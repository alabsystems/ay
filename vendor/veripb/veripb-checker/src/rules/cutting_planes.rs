use std::rc::Rc;

use colored::Colorize;
use veripb_formula::prelude::*;
use veripb_rules::{Instruction, PolRule};

use crate::prelude::*;

use super::Checkable;

impl Checkable for PolRule {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if context.trace_enabled && context.config.trace_pol {
            trace_derivation(self, context, database);
        }
        let result = execute_pol_instructions(&mut self.instructions, context.only_core, database)?;
        crate::kernel_bridge::consume_pol(
            context,
            database,
            &self.instructions,
            &result[0].constraint,
        )?;
        Ok(result)
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}

/// Compute the result of the cutting planes derivation by executing the instructions
/// via stack-based evaluation.
pub fn execute_pol_instructions(
    instructions: &mut [Instruction],
    only_core: bool,
    database: &mut Database,
) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
    let mut stack: Vec<PBConstraintEnum> = Vec::new();

    // We optimize cutting planes derivations by accumulating successive additions of literal axioms
    // and adding them to the base constraint in one go.
    // Boolean tracking whether the top of the stack is a literal axiom (possibly multiplied with a constant).
    let mut top_is_literal_axiom = false;
    // Vector of terms keeping track of the literal axioms that still need to be added.
    let mut literal_axiom_stash = Vec::new();
    // Vector keeping track of variables that still need to be weakened.
    let mut weakening_stash = Vec::new();

    for instruction in instructions.iter_mut() {
        if !literal_axiom_stash.is_empty() {
            // We need to process the literal axiom stash if we encounter an operation that does not extend the
            // current sequence of literal axiom additions.
            let need_to_process_stash = if top_is_literal_axiom {
                // Multiplying the literal axiom on the top of the stack or adding it extends the current sequence.
                !matches!(instruction, Instruction::Multiply(_) | Instruction::Add)
            } else {
                // Only pushing a new literal axiom on the stack extend the current sequence.
                !matches!(instruction, Instruction::LiteralAxiom(_))
            };
            if need_to_process_stash {
                let last = if top_is_literal_axiom {
                    // If there is still a literal axiom on top of the stack, we remove it temporarily
                    // in order to carry out the addition on the correct constraint.
                    stack.pop()
                } else {
                    None
                };
                if let Some(first) = stack.last_mut() {
                    // Construct constraint from literal axioms to be added.
                    let second =
                        constraint_from_terms(std::mem::take(&mut literal_axiom_stash), 0.into());
                    // Add constraint containing literal axioms.
                    if let Some(replacement) = first.add(&second) {
                        stack.pop();
                        stack.push(replacement);
                    }
                    // Restore temporarily removed literal axiom.
                    if let Some(last) = last {
                        stack.push(last);
                    }
                } else {
                    return Err(CheckingError::NotEnoughConstraintsOnStack);
                }
            }
        }

        if !weakening_stash.is_empty() {
            // We need to process the weakening stash if we have no additional weakening step.
            if !matches!(instruction, Instruction::Weaken(_)) {
                if let Some(constraint) = stack.last_mut() {
                    if let Some(replacement) =
                        constraint.weaken_all(std::mem::take(&mut weakening_stash))
                    {
                        stack.pop();
                        stack.push(replacement);
                    }
                } else {
                    return Err(CheckingError::NotEnoughConstraintsOnStack);
                }
            }
        }

        match instruction {
            Instruction::ConstraintId(index) => {
                *index = database.normalize_id(*index);
                let constraint = database.get_entry_usize(*index as usize)?;
                if only_core && !constraint.is_core_constraint_id(*index as usize) {
                    return Err(CheckingError::CoreSubproofUsingNonCoreConstraint(*index));
                }
                stack.push(constraint.constraint.clone());
                top_is_literal_axiom = false;
            }
            Instruction::LiteralAxiom(lit) => {
                stack.push(Cardinality::from_lits(vec![*lit], 0).into());
                top_is_literal_axiom = true;
            }
            Instruction::Saturate => {
                match stack.last_mut() {
                    Some(constraint) => constraint.saturate(),
                    None => return Err(CheckingError::NotEnoughConstraintsOnStack),
                }
                top_is_literal_axiom = false;
            }
            Instruction::Weaken(var_idx) => {
                weakening_stash.push(*var_idx);
                top_is_literal_axiom = false;
            }
            Instruction::NormalizedFormDivide(divisor) => {
                match stack.last_mut() {
                    Some(constraint) => constraint.normalized_form_div(divisor),
                    None => return Err(CheckingError::NotEnoughConstraintsOnStack),
                }
                top_is_literal_axiom = false;
            }
            Instruction::VariableFormDivide(divisor) => {
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.variable_form_div(divisor) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => return Err(CheckingError::NotEnoughConstraintsOnStack),
                }
                top_is_literal_axiom = false;
            }
            Instruction::NormalizedFormMIR(divisor) => {
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.normalized_form_mir(divisor) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => return Err(CheckingError::NotEnoughConstraintsOnStack),
                }
                top_is_literal_axiom = false;
            }
            Instruction::VariableFormMIR(divisor) => {
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.variable_form_mir(divisor) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => return Err(CheckingError::NotEnoughConstraintsOnStack),
                }
                top_is_literal_axiom = false;
            }
            Instruction::Multiply(factor) => match stack.last_mut() {
                Some(constraint) => {
                    if let Some(replacement) = constraint.multiply(factor) {
                        stack.pop();
                        stack.push(replacement);
                    }
                }
                None => return Err(CheckingError::NotEnoughConstraintsOnStack),
            },
            Instruction::Add => {
                if let Some(second) = stack.pop() {
                    if !top_is_literal_axiom {
                        // The top is not a literal axiom, so we just add it.
                        if let Some(first) = stack.last_mut() {
                            if let Some(replacement) = first.add(&second) {
                                stack.pop();
                                stack.push(replacement);
                            }
                        } else {
                            return Err(CheckingError::NotEnoughConstraintsOnStack);
                        }
                    } else {
                        // Store the literal axiom for adding it later.
                        if let Some(term) = second.get_term(0) {
                            literal_axiom_stash.push(term);
                        }
                        top_is_literal_axiom = false;
                    }
                } else {
                    return Err(CheckingError::NotEnoughConstraintsOnStack);
                }
            }
            Instruction::LowerRHS(amount) => {
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.lower_rhs(amount) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => return Err(CheckingError::NotEnoughConstraintsOnStack),
                }
                // A lowered literal axiom is no longer the plain `l >= 0`
                // the literal-axiom stash assumes: leaving the flag set made
                // a following `+` stash only the term and silently drop the
                // lowered degree (deriving `C + (l >= 0)` where the proof
                // said `C + (l >= -a)`). Sound but not what the derivation
                // stated; found by the proved-kernel shadow replay.
                top_is_literal_axiom = false;
            }
        }
    }

    if !literal_axiom_stash.is_empty() {
        // Process the remaining literal axioms that still need to be added.
        if let Some(first) = stack.last_mut() {
            let second = constraint_from_terms(std::mem::take(&mut literal_axiom_stash), 0.into());
            if let Some(replacement) = first.add(&second) {
                stack.pop();
                stack.push(replacement);
            }
        } else {
            return Err(CheckingError::NotEnoughConstraintsOnStack);
        }
    }

    if !weakening_stash.is_empty() {
        // Process remaining weakening steps.
        if let Some(constraint) = stack.last_mut() {
            if let Some(replacement) = constraint.weaken_all(std::mem::take(&mut weakening_stash)) {
                stack.pop();
                stack.push(replacement);
            }
        } else {
            return Err(CheckingError::NotEnoughConstraintsOnStack);
        }
    }

    if stack.len() != 1 {
        return Err(CheckingError::StackNotOne(stack.len()));
    }

    Ok(vec![Rc::new(DBConstraint::from(
        stack.pop().unwrap().into_smallest_type(),
    ))])
}

/// Print a verbose, step-by-step trace of this pol derivation that mirrors the
/// raw pol line: the operand column reads top-to-bottom like the source tokens.
///
/// The [`compute`](PolRule::compute) hot path batches successive literal-axiom
/// additions and weakenings, so its live stack does not always reflect the
/// logical state between operations. This re-evaluates the instructions in a
/// simple, non-optimized way purely for display; it is only ever run for the
/// few rules selected for tracing.
///
/// Each row shows the stack depth, one source token (a constraint id, a
/// literal, a scalar/variable, or an operator such as `+`, `*` or `d`), and
/// the resulting top of the stack. Scalars and weakening variables sit
/// transiently on the stack before the operator that consumes them, exactly
/// as they appear on the pol line.
fn trace_derivation(rule: &PolRule, context: &Context, database: &Database) {
    let var_names = &context.var_names;

    /// The pretty-printed top of the constraint stack, or empty if the stack is bare.
    fn top_of(stack: &[PBConstraintEnum], var_names: &VarNameManager) -> String {
        stack
            .last()
            .map(|constraint| constraint.to_pretty_string(var_names))
            .unwrap_or_default()
    }

    let mut stack: Vec<PBConstraintEnum> = Vec::new();
    // Each row is (stack depth, source token, top-of-stack, top-is-constraint).
    // Scalars/variables are not real constraints, so they are flagged to be
    // shown without constraint colouring.
    let mut rows: Vec<(usize, String, String, bool)> = Vec::new();

    for instruction in rule.instructions.iter() {
        match instruction {
            Instruction::ConstraintId(index) => {
                let normalized = database.normalize_id(*index);
                match database.get_entry_usize(normalized as usize) {
                    // Mirror compute(): a core-only context rejects non-core
                    // constraints, so stop the trace where the real check fails.
                    Ok(constraint)
                        if context.only_core
                            && !constraint.is_core_constraint_id(normalized as usize) =>
                    {
                        rows.push((
                            stack.len(),
                            index.to_string(),
                            "(non-core)".to_string(),
                            false,
                        ));
                        break;
                    }
                    Ok(constraint) => stack.push(constraint.constraint.clone()),
                    // The real computation reports the error with proper
                    // context; here we simply stop the trace at this operand.
                    Err(_) => {
                        rows.push((
                            stack.len(),
                            index.to_string(),
                            "(unavailable)".to_string(),
                            false,
                        ));
                        break;
                    }
                }
                rows.push((
                    stack.len(),
                    index.to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::LiteralAxiom(lit) => {
                stack.push(Cardinality::from_lits(vec![*lit], 0).into());
                rows.push((
                    stack.len(),
                    lit.to_pretty_string(var_names),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::Add => {
                let Some(second) = stack.pop() else { break };
                match stack.last_mut() {
                    Some(first) => {
                        if let Some(replacement) = first.add(&second) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "+".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::Saturate => {
                match stack.last_mut() {
                    Some(constraint) => constraint.saturate(),
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "s".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            // The remaining operators each consume a scalar (or, for weakening, a
            // variable) that precedes them on the pol line. Show that operand as a
            // transient stack entry, then the operator and its result.
            Instruction::Multiply(factor) => {
                rows.push((
                    stack.len() + 1,
                    factor.to_string(),
                    factor.to_string(),
                    false,
                ));
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.multiply(factor) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "*".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::NormalizedFormDivide(divisor) => {
                rows.push((
                    stack.len() + 1,
                    divisor.to_string(),
                    divisor.to_string(),
                    false,
                ));
                match stack.last_mut() {
                    Some(constraint) => constraint.normalized_form_div(divisor),
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "d".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::VariableFormDivide(divisor) => {
                rows.push((
                    stack.len() + 1,
                    divisor.to_string(),
                    divisor.to_string(),
                    false,
                ));
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.variable_form_div(divisor) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "c".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::NormalizedFormMIR(divisor) => {
                rows.push((
                    stack.len() + 1,
                    divisor.to_string(),
                    divisor.to_string(),
                    false,
                ));
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.normalized_form_mir(divisor) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "n".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::VariableFormMIR(divisor) => {
                rows.push((
                    stack.len() + 1,
                    divisor.to_string(),
                    divisor.to_string(),
                    false,
                ));
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.variable_form_mir(divisor) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "m".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::LowerRHS(amount) => {
                rows.push((
                    stack.len() + 1,
                    amount.to_string(),
                    amount.to_string(),
                    false,
                ));
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.lower_rhs(amount) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "-".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
            Instruction::Weaken(var_idx) => {
                let variable = Lit::from_var(*var_idx, false).to_pretty_string(var_names);
                rows.push((stack.len() + 1, variable.clone(), variable, false));
                match stack.last_mut() {
                    Some(constraint) => {
                        if let Some(replacement) = constraint.weaken_all(vec![*var_idx]) {
                            stack.pop();
                            stack.push(replacement);
                        }
                    }
                    None => break,
                }
                rows.push((
                    stack.len(),
                    "w".to_string(),
                    top_of(&stack, var_names),
                    true,
                ));
            }
        }
    }

    let depth_w = rows
        .iter()
        .map(|(depth, _, _, _)| depth.to_string().len())
        .chain(std::iter::once("depth".len()))
        .max()
        .unwrap_or(0);
    let operand_w = rows
        .iter()
        .map(|(_, operand, _, _)| operand.len())
        .chain(std::iter::once("operand".len()))
        .max()
        .unwrap_or(0);

    println!(
        "    {:<depth_w$}  {:<operand_w$}  top of stack",
        "depth", "operand"
    );
    for (depth, operand, top, top_is_constraint) in rows {
        let top = if top_is_constraint {
            top.blue()
        } else {
            top.normal()
        };
        println!("    {:<depth_w$}  {:<operand_w$}  {}", depth, operand, top);
    }
}
