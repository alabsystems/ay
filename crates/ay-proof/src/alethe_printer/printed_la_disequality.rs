// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `la_disequality` judged over the bytes it ships.
//!
//! Pinned carcara 1.1.0 (`checker/rules/linear_arithmetic.rs`) accepts
//! exactly `(cl (or (= t1 t2) (not (<= t1 t2)) (not (<= t2 t1))))` and compares
//! the three copies of `t1`, and of `t2`, with `assert_eq`: identity of the
//! parsed terms, not equality up to symmetry. Three printer sites emit the
//! rule (the guarded disequality split, the equality-adapter triangle and the
//! `bvult` zero lowering), and each builds that clause from text that some
//! rendering channel chose. At c57bd8481 (and until this change) nothing
//! judged the result, and the split shipped
//! `(or (= 1 x) (not (<= x 1)) (not (<= 1 x)))` for an authored `(= 1 x)`
//! stored as `(= x 1)` (see `arith_disequality_split.rs`),
//! which pinned carcara refused and which made the whole document `invalid`.
//!
//! This is the chokepoint for that rule, like `judge_printed_la_generic` for
//! `la_generic`: every `:rule la_disequality` command a step ships must be
//! that shape with byte-identical operand copies, or the step declines to the
//! honest hole over its own clause. Identical bytes parse to identical terms,
//! so an accepted command is an instance of the rule; a spelling difference
//! that happens to denote the same term is refused, which costs a hole and
//! never validity.

use super::printed_command::{printed_commands, rendered_rule_field_names, PrintedCommandRead};
use super::surface_tokens::split_alethe_application_bounded;
use super::*;

const LA_DISEQUALITY: &str = "la_disequality";

/// The arguments of the printed application `(op a1 .. an)`, or `None`.
fn application<'t>(text: &'t str, op: &str) -> Option<Vec<&'t str>> {
    split_alethe_application_bounded(text, op, usize::MAX, usize::MAX).ok()
}

/// The operands `(a, b)` of the printed literal `(not (<= a b))`, or `None`.
fn negated_le(literal: &str) -> Option<(&str, &str)> {
    let negated = application(literal, "not")?;
    let [inner] = negated.as_slice() else {
        return None;
    };
    let operands = application(inner, "<=")?;
    let [a, b] = operands.as_slice() else {
        return None;
    };
    Some((*a, *b))
}

/// Whether a printed `la_disequality` conclusion is an instance of the rule
/// as pinned carcara checks it.
pub(super) fn printed_la_disequality_holds(conclusion: &[&str]) -> bool {
    let [packed] = conclusion else {
        return false;
    };
    let Some(disjuncts) = application(packed, "or") else {
        return false;
    };
    let [equality, forward, reverse] = disjuncts.as_slice() else {
        return false;
    };
    let Some(operands) = application(equality, "=") else {
        return false;
    };
    let [t1, t2] = operands.as_slice() else {
        return false;
    };
    negated_le(forward) == Some((*t1, *t2)) && negated_le(reverse) == Some((*t2, *t1))
}

impl AlethePrinter<'_> {
    /// Judge every `:rule la_disequality` command in one rendered step
    /// ([`printed_la_disequality_holds`]); a refusal declines the step to the
    /// honest hole over its own clause, or declines the export where the step
    /// has no clause to hole.
    pub(super) fn judge_printed_la_disequality(
        &self,
        step: &ProofStep,
        id: ProofId,
        rendered: String,
    ) -> Result<String, AlethePrintError> {
        // A pre-filter only; the decision below reads commands.
        if !rendered.contains(LA_DISEQUALITY) {
            return Ok(rendered);
        }
        let refused = match printed_commands(&rendered) {
            Ok(commands) => commands.iter().find_map(|command| match command {
                PrintedCommandRead::Command(command) if command.rule() == Some(LA_DISEQUALITY) => {
                    let holds = command
                        .conclusion()
                        .is_some_and(|conclusion| printed_la_disequality_holds(&conclusion));
                    (!holds).then(|| command.name().unwrap_or("?").to_string())
                }
                PrintedCommandRead::Command(_) => None,
                PrintedCommandRead::Unsplittable(text) => {
                    rendered_rule_field_names(text, &[LA_DISEQUALITY]).then(|| id.to_string())
                }
            }),
            Err(_) => {
                rendered_rule_field_names(&rendered, &[LA_DISEQUALITY]).then(|| id.to_string())
            }
        };
        let Some(refused_name) = refused else {
            return Ok(rendered);
        };
        let clause: Option<&[TermId]> = match step {
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::FiniteFieldLinear { clause, .. }
            | ProofStep::NraSos { clause, .. }
            | ProofStep::Step { clause, .. } => Some(clause),
            _ => None,
        };
        let Some(clause) = clause else {
            return Err(AlethePrintError::InvalidSurfaceStep {
                id,
                reason: format!(
                    "printed step `{refused_name}` is not an instance of la_disequality over the text it ships"
                ),
            });
        };
        Ok(format!(
            "(step {id} {} :rule {})",
            self.format_clause(clause),
            ay_core::UNPROVED_STEP_RULE
        ))
    }
}
