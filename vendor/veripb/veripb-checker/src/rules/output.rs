use std::rc::Rc;

use ahash::AHashSet;
use itertools::Itertools;
use veripb_formula::prelude::*;
use veripb_parser::{
    opb_parser::parse_opb_from_file_given_var_manager,
    wcnf_parser::parse_wcnf_from_file_given_var_manager,
};
use veripb_rules::{OutputGuarantee, OutputRule, OutputType};

use crate::prelude::*;

#[inline]
fn parse_output_file(
    context: &mut Context,
) -> Result<(Formula, Option<AHashSet<VarIdx>>), CheckingError> {
    if let Some(output_formula_path) = &context.config.output_formula {
        match FormulaFormat::resolve(context.config.formula_format_override, output_formula_path) {
            // A checking error, not `unimplemented!`. `veripb f.opb p.pbp
            // out.cnf` with an `output ... FILE` rule is an ordinary command
            // line, and under the release profile's `panic = "abort"` the
            // macro turned it into a process abort with no verdict. The
            // `NotImplemented` variant already exists for exactly this and is
            // what the version-3 parser routes `output ... PERMUTATION` to.
            FormulaFormat::CNF => Err(CheckingError::not_implemented(
                "output with a DIMACS CNF output formula (use OPB or WCNF)",
            )),
            FormulaFormat::WCNF => Ok((
                parse_wcnf_from_file_given_var_manager(
                    output_formula_path,
                    &mut context.var_names,
                )?,
                None,
            )),
            FormulaFormat::OPB => {
                let (formula, _, preserved_vars) = parse_opb_from_file_given_var_manager(
                    output_formula_path,
                    &mut context.var_names,
                )?;
                Ok((formula, preserved_vars))
            }
        }
    } else {
        Err(CheckingError::NoOutputFormulaGiven)
    }
}

#[inline]
fn check_file(
    context: &mut Context,
    database: &mut Database,
    check_preserved_vars: bool,
) -> Result<Vec<(usize, usize)>, CheckingError> {
    // Parse the output formula.
    let (output_formula, preserved_vars) = parse_output_file(context)?;

    // Check that the objectives are equivalent.
    match (&context.objective, output_formula.objective) {
        (None, None) => {}
        (Some(current_objective), Some(output_objective)) => {
            if *current_objective != output_objective {
                if current_objective.constant != output_objective.constant {
                    return Err(CheckingError::OutputObjectiveConstantMismatch(
                        current_objective.constant.clone(),
                        output_objective.constant,
                    ));
                }
                let (current_extra, output_extra) = current_objective.difference(&output_objective);
                return Err(CheckingError::OutputObjectiveMismatch(
                    current_extra
                        .iter()
                        .map(|t| t.to_pretty_string(&context.var_names))
                        .join(", "),
                    output_extra
                        .iter()
                        .map(|t| t.to_pretty_string(&context.var_names))
                        .join(", "),
                ));
            }
        }
        (None, Some(_)) => return Err(CheckingError::OutputObjectiveButNoProofObjective),
        (Some(_), None) => return Err(CheckingError::OutputNoObjectiveButProofObjective),
    }

    // Check if every constraint in output formula is in core constraints.
    database.update_unique_index(&mut context.propagation_engine)?;

    // Converted up front, because the constraints are cross-checked against an
    // independent reading of the output file BEFORE any of them is looked up.
    // The verdict this rule reaches is about that file, and the lookup loop
    // below can only ever confirm the checker's own parse against the
    // database — it has no way to notice that the parse and the file disagree.
    let output_constraints: Vec<Rc<veripb_formula::prelude::DBConstraint>> = output_formula
        .constraints
        .into_iter()
        .map(|c| Rc::new(c.into()))
        .collect();
    let for_cross_check: Vec<_> = output_constraints.iter().map(|c| &c.constraint).collect();
    crate::kernel_bridge::output_formula_cross_check(context, &for_cross_check)?;

    // The pairing the kernel's `output_unsat_of_unsat` needs, recorded as the
    // checker computes it anyway: which database id each output constraint was
    // found at. Nothing here changes what is accepted; it only keeps the
    // correspondence the lookup establishes instead of discarding it.
    let mut pairs: Vec<(usize, usize)> = Vec::with_capacity(output_constraints.len());
    for (out_pos, output_constraint) in output_constraints.into_iter().enumerate() {
        if let Some(database_constraint) = database.lookup(&output_constraint) {
            if database_constraint.is_core_constraint() {
                pairs.push((database_constraint.get_some_id(), out_pos));
                // The lookup accepted this output constraint because it is
                // syntactically a database constraint — the same acceptance
                // shape as the `e`/`ea` rule and the proofgoal `DBLookup`, so
                // it is re-judged through the same entry point rather than
                // trusted on the live hash/`Eq`.
                crate::kernel_bridge::consume_db_lookup(
                    context,
                    &output_constraint.constraint,
                    &database_constraint.constraint,
                )?;
                // Mark constraints for check that every core constraint is in output formula.
                database_constraint.header.borrow_mut().is_in_output_formula = true;
            } else {
                return Err(CheckingError::OutputConstraintNotInCore(
                    database_constraint.get_some_id(),
                ));
            }
        } else {
            return Err(CheckingError::OutputConstraintNotInDatabase(
                output_constraint.to_pretty_string(&context.var_names),
            ));
        }
    }

    // Check if every core constraint was marked by a output formula constraint.
    for constraint in database.unique_constraints.iter() {
        if constraint.is_core_and_not_in_output_constraint() {
            return Err(CheckingError::OutputCoreConstraintNotInOutput(
                constraint.get_some_id(),
            ));
        }
    }

    // Check if preserved sets are equal when guarantee is `EQUIENUMERABLE`.
    if check_preserved_vars {
        match (&context.preserved_variables, preserved_vars) {
            (None, None) => {}
            (Some(current_vars), Some(output_vars)) => {
                if *current_vars != output_vars {
                    // Both lists are sorted by `missing_vars_message`; taking
                    // either set in hash order made this refusal name its
                    // variables in a different order on every run.
                    let missing_vars = crate::utils::missing_vars_message(
                        current_vars,
                        &output_vars,
                        &context.var_names,
                    );
                    let additional_vars = crate::utils::missing_vars_message(
                        &output_vars,
                        current_vars,
                        &context.var_names,
                    );
                    return Err(CheckingError::OutputPreservedVarsMismatch(
                        missing_vars,
                        additional_vars,
                    ));
                }
            }
            (None, Some(_)) => return Err(CheckingError::OutputCurrentHasNoPreservedVars),
            (Some(_), None) => return Err(CheckingError::OutputFormulaHasNoPreservedVars),
        }
    }

    Ok(pairs)
}

impl Checkable for OutputRule {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if context.has_output {
            return Err(CheckingError::DoubleOutput);
        }
        if context.has_conclusion || context.has_end_proof {
            return Err(CheckingError::WrongFooterOrder("output"));
        }
        if !context.subcontexts.is_empty() {
            return Err(CheckingError::OutputWhileOpenSubcontext);
        }

        // Check for checked deletion condition.
        if !context.strong_solution_guarantees
            && (self.guarantee == OutputGuarantee::Equioptimal
                || self.guarantee == OutputGuarantee::Equisatisfiable
                || self.guarantee == OutputGuarantee::Equienumerable)
        {
            return Err(CheckingError::ExpectedStrongerGuarantees);
        }

        // Check conditions for `EQUIENUMERABLE`.
        if self.guarantee == OutputGuarantee::Equienumerable {
            if context.preserved_variables.is_none() && context.witnesses_used {
                return Err(CheckingError::OutputEquienumWitnessUsed);
            }
            if context.solution_logged {
                return Err(CheckingError::OutputEquienumSolutionLogged);
            }
            // The guard above tests "a solution was logged", which is a PROXY
            // for the hazard — "a solution-restricting constraint has been
            // stored" — and the proxy misses one route: `obji v` stores the
            // same objective-improving constraint an improving `sol`/`soli`
            // does WITHOUT logging a solution. So `sol …; obji v;` used to
            // slip past this arm while the semantically identical single rule
            // `soli … : v;` was refused, and six proof lines certified a
            // 3-solution formula EQUIENUMERABLE to an output with none.
            // `EQUIOPTIMAL` tolerates the same constraint because its verdict
            // is explicitly qualified (`FOR obj < v`, with `v` capped by
            // `Context::objective_guarantee_ceiling` at the infimum of
            // everything removed); an enumeration count has no such qualifier.
            // Ported from the ay repo's patch
            // 0002-ay-post-fork-soundness-fixes (defect 20 there); see
            // tests/instances/incorrect/version3/output_equienumerable_sol_then_obji.pbp.
            if context.objective_improving_used {
                return Err(CheckingError::OutputEquienumObjectiveRestricting);
            }
        }

        // Check that right guarantee was used.
        match self.guarantee {
            OutputGuarantee::Equioptimal if context.objective.is_none() => {
                return Err(CheckingError::OutputEquioptimalWithoutObjective);
            }
            OutputGuarantee::Equioptimal => {}
            OutputGuarantee::Equisatisfiable if context.objective.is_some() => {
                return Err(CheckingError::OutputEquisatisfiableWithObjective);
            }
            _ => {}
        }

        // `EQUISATISFIABLE` is an unqualified claim, so a rule that deletes
        // solutions outright breaks it: `solx` on the only solution class of a
        // satisfiable input leaves a database — and hence an output formula —
        // that is unsatisfiable. `EQUIENUMERABLE` already refuses for the same
        // reason a few lines above; `EQUIOPTIMAL` does not need to, because it
        // prints the objective value below which nothing was removed.
        //
        // `context.solution_logged` is exactly the right flag here even though
        // an improving `soli` also sets it: `soli`/`obji` require an objective,
        // and an objective has already been rejected for this guarantee above.
        if self.guarantee == OutputGuarantee::Equisatisfiable && context.solution_logged {
            return Err(CheckingError::OutputEquisatSolutionExcluded);
        }

        // `DERIVABLE` claims every model of the input is a model of the output,
        // and `check_file` establishes it by matching the output against the
        // *core set* constraint for constraint. That is sound only while every
        // core constraint is entailed by the input — and `solx`/`soli`/`obji`
        // break exactly that: each stores a satisfiability-preserving but
        // *not* input-entailed constraint into core (its own kernel taint is
        // `solution-exclusion-unmodelled`). So after solution logging the core
        // set can be unsatisfiable while the input is not, and the DERIVABLE
        // check would then certify a satisfiable input as entailing an
        // unsatisfiable output — a false claim, disprovable on one variable:
        // input `x1 >= 1` (SAT at x1=1) &ldquo;derives&rdquo; `{x1 >= 1, ~x1 >= 1}` (UNSAT).
        //
        // This is defect 15's failure mode at the one guarantee its fix did not
        // reach: `EQUISATISFIABLE` (just above) and `EQUIENUMERABLE` (further
        // up) already carry this guard, and the earlier reasoning that DERIVABLE
        // was "implication-based, so unaffected by weakened solution
        // guarantees" is precisely the step that fails — it silently assumes an
        // input-entailed core. Nothing exercised it because no corpus proof
        // ever wrote `DERIVABLE`.
        //
        // `solution_logged` alone is the same PROXY the `EQUIENUMERABLE` arm
        // used to test, with the same evasion: `obji v` stores the identical
        // non-entailed constraint into core without logging a solution, so
        // `f 1; obji 1; output DERIVABLE FILE;` certified
        // `min: x2; x1 ∨ x2` as deriving `{x1 ∨ x2, ~x2}` — false at
        // x1=0, x2=1. Both flags together cover every rule that stores a
        // solution-restricting constraint (`soli`/`solx` set the first,
        // `soli`/`obji` the second; plain `sol` stores nothing). Ported from
        // the ay repo's patch 0002-ay-post-fork-soundness-fixes (defect 20
        // there), which established the proxy-vs-hazard failure mode; see
        // tests/instances/incorrect/version3/output_derivable_obji.pbp.
        //
        // AND `red`/`dom`, which the two flags above do NOT cover. The comment
        // above says "both flags together cover every rule that stores a
        // solution-restricting constraint", and that is true -- but
        // solution-restricting was the wrong category. What DERIVABLE needs is
        // that every core constraint is input-ENTAILED, and redundance- and
        // dominance-based strengthening store non-entailed constraints by a
        // licence that has nothing to do with solutions. Disprovable on two
        // variables, with no solution logged and no objective at all:
        //
        //     input   1 x1 1 x2 >= 1
        //     proof   red 1 x1 >= 1 : x1 1 ;  core id -1 ;
        //             output DERIVABLE FILE
        //     output  { 1 x1 1 x2 >= 1,  1 x1 >= 1 }
        //
        // certified `s VERIFIED OUTPUT DERIVABLE` at exit 0, and x1=0 x2=1
        // satisfies the input while falsifying the output. Same failure mode
        // as defects 15 and 20, at the third route their fixes did not reach.
        // See tests/instances/incorrect/version3/output_derivable_red.pbp.
        if self.guarantee == OutputGuarantee::Derivable
            && (context.solution_logged
                || context.objective_improving_used
                || context.witnessed_strengthening_used)
        {
            return Err(CheckingError::OutputDerivableSolutionRestricting);
        }

        // Only an `OutputType::File` run compares against a formula, so only
        // it can produce the pairing the kernel transfer needs. `IMPLICIT`
        // deliberately leaves this empty: its claim is about the core set
        // itself, there is no second formula, and an empty pairing declines
        // the transfer rather than vacuously granting it.
        let mut output_pairs: Vec<(usize, usize)> = Vec::new();
        // Check that the output is equivalent to the current problem.
        match self.output_type {
            OutputType::None => {}
            OutputType::Implicit => {
                // `IMPLICIT` means "the output formula is the current core
                // set", so there is nothing to compare against and the proof's
                // own claim is true. But if the user *named* an output file on
                // the command line, it is never opened -- and a verdict with
                // the word OUTPUT in it is then printed about a file nobody
                // read. Measured: an `output EQUISATISFIABLE IMPLICIT;` proof
                // over a satisfiable formula prints
                // `s VERIFIED OUTPUT EQUISATISFIABLE` at exit 0 while the named
                // file is `{x1 >= 1, ~x1 >= 1}`, unsatisfiable. Nothing false is
                // claimed; the user is simply liable to read the verdict as
                // being about their file. Say so.
                if context.config.output_formula.is_some() {
                    log::warn!(
                        "The proof's `output` rule says IMPLICIT, so the output formula is this \
                         proof's core set and the output file given on the command line was not \
                         read. The verdict below is about the core set, not about that file."
                    );
                }
            }
            OutputType::File => {
                output_pairs = check_file(
                    context,
                    database,
                    self.guarantee == OutputGuarantee::Equienumerable,
                )?;
            }
            // `output <guarantee> PERMUTATION` is a legal lexeme that no
            // checker path implements. The version-3 parser turns it into an
            // `UnimplementedRule` and never reaches here, but the version-2
            // parser does, and `unimplemented!()` made
            // `output EQUISATISFIABLE PERMUTATION` in a 2.0 proof abort the
            // process instead of reporting the same refusal the 3.0 spelling
            // gets. Same message, same variant, both spellings.
            OutputType::Permutation => {
                return Err(CheckingError::not_implemented("output.PERMUTATION"));
            }
        }

        // The `output` rule's claim — "this output formula is <guarantee> with
        // the input formula" — is a formula-level equivalence resting on the
        // core-set discipline and on objective equality. The proved kernel
        // models neither (the development design notes section 5, item 5: no objective
        // model, no core/derived distinction, no two-formula equivalence), so
        // the licence itself is counted here; the per-constraint database
        // lookups of `check_file` are kernel-re-judged where they happen.
        // Gated on the guarantee rather than the output type, because
        // `IMPLICIT` reaches the same verdict line with no check at all, and
        // not on `print_verification_result`, so the in-process harness and
        // the binary report the same statistics.
        if context.config.kernel_verify && self.guarantee != OutputGuarantee::None {
            // The BACKWARD half of the claim -- a model of the emitted formula
            // is a model of the given one -- is what
            // `VeriPbCore.output_unsat_of_unsat` proves, and the bridge can
            // now discharge its hypotheses for a run that never deleted a core
            // constraint. What is still NOT modelled is the rest of the
            // guarantee: the forward half needs the companion model, and
            // `EQUIOPTIMAL`/`EQUIENUMERABLE` add an objective and a counting
            // claim the kernel has no model for. So a justified backward
            // transfer narrows the skip rather than removing it.
            use crate::kernel_bridge::OutputTransfer;
            match crate::kernel_bridge::offer_output_equivalence(context, database, &output_pairs) {
                OutputTransfer::Equivalence => {
                    context.kernel_stats.output_backward_transfers += 1;
                    context.kernel_stats.output_equivalences += 1;
                    // `EQUISATISFIABLE` claims exactly "these two formulas are
                    // satisfiable together", and with both halves the kernel
                    // has that outright -- so this run reports NOTHING outside
                    // the proved fragment for its `output`. The other
                    // guarantees claim strictly more than equisatisfiability:
                    // `EQUIOPTIMAL` an objective the kernel has no model for,
                    // `EQUIENUMERABLE` a counting claim it has no model for,
                    // and `DERIVABLE` a derivability claim that is not an
                    // equivalence at all. Those keep a skip naming the part
                    // that is still theirs alone.
                    if self.guarantee != OutputGuarantee::Equisatisfiable {
                        context
                            .kernel_stats
                            .skip("output-guarantee-beyond-equisatisfiability");
                    }
                }
                OutputTransfer::Backward(reason) => {
                    context.kernel_stats.output_backward_transfers += 1;
                    context.kernel_stats.skip(reason);
                }
                OutputTransfer::None(reason) => context.kernel_stats.skip(reason),
            }
        }

        // Warn the user that proof used unchecked assertions before printing `s` status lines.
        if context.assertion_used {
            log::warn!("The proof used unchecked assertions.");
            if context.elaborator.is_some() {
                log::warn!(
                    "Unchecked assertions (unsupported in the kernel format) have been written to the elaborated proof."
                );
            }
        }

        if self.guarantee != OutputGuarantee::None {
            // The bound is the checked guarantee ceiling, not the best logged
            // objective. Preserve it as typed data for in-process consumers.
            context.pending_verification_results.push(
                crate::checked_result::CheckedStatement::output(
                    self.guarantee,
                    self.output_type,
                    context.objective_guarantee_ceiling().cloned(),
                    context.assertion_used,
                    context.config.print_verification_result,
                ),
            );
        }

        context.has_output = true;
        Ok(vec![])
    }
}
