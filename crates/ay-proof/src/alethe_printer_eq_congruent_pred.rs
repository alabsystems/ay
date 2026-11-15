// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface admissibility for Alethe `eq_congruent_pred` steps.
//!
//! The 2026-09-11 rule audit — which rules AY prints whose validity is a
//! relation over their printed operands, and which of those have no
//! printed-surface judgement — left exactly one member open:
//! `eq_congruent_pred`. Measured 2026-09-20: the printer shipped
//! `(cl (not (= (ite (not (= a b)) 1 0) 0)) (not (p a)) (p b))
//! :rule eq_congruent_pred` over a re-spelled hypothesis, the sixth false
//! green's mechanism at the predicate rule. The rule is now judged over the
//! text the step ships, replaying pinned carcara 1.1.0's own decision
//! procedure, at both sites that print it; a failure declines to the honest
//! `hole`, unless the step is over the EQUALITY predicate, where it is the
//! transitivity chain [`AlethePrinter::eq_congruent_pred_chain_or_hole`]
//! spells.

use ay_core::{ProofId, TermId, UNPROVED_STEP_RULE};

use super::surface_literal::equal_modulo_bitvec_literal_spelling;
use super::surface_tokens::split_smt_term_slices_bounded;
use super::{split_alethe_application_bounded, AlethePrinter};

/// Literal count above which the replay declines rather than scanning.
const MAX_CONGRUENCE_LITERALS: usize = 1_024;

/// Byte cap on one rendered literal handed to the balanced tokenizer.
const MAX_CONGRUENCE_TERM_BYTES: usize = 1024 * 1024;

impl AlethePrinter<'_> {
    /// Whether the active surface is accepted by Alethe `eq_congruent_pred`.
    ///
    /// Judged over the PRINTED clause, never over the term DAG.
    pub(super) fn eq_congruent_pred_prints_spec_valid(&self, clause: &[TermId]) -> bool {
        if clause.len() > MAX_CONGRUENCE_LITERALS {
            return false;
        }
        let printed: Vec<String> = clause.iter().map(|&lit| self.format_term(lit)).collect();
        let borrowed: Vec<&str> = printed.iter().map(String::as_str).collect();
        printed_eq_congruent_pred_holds(&borrowed)
    }

    /// An `eq_congruent_pred` the printed text does not instantiate: the
    /// equality chain it states over the `=` predicate, else the honest
    /// decline (the clause still ships, named as unproved).
    ///
    /// Congruence of `=` itself, `(cl (not (= a1 b1)) (not (= a2 b2))
    /// (not (= a1 a2)) (= b1 b2))`, is the chain `b1 = a1 = a2 = b2`. The
    /// strict validator pairs argument positions over the TERM STORE; the
    /// authored-surface channel then prints an assumed equality in the
    /// problem's operand order (`mk_eq` interned `(not (= (select d i) v))`'s
    /// atom as `(= v (select d i))`), so the printed positions no longer pair
    /// and carcara's `eq_congruent_pred` refuses the text. Its `eq_transitive`
    /// orients every hypothesis itself and re-derives the chain over exactly
    /// the same literals. MEASURED (QF_AX `three_store_chain`, QF_AUFLIA
    /// `array_swap_arith`): `(cl (not (= v v)) (not (= (select d i) (select c
    /// i))) (not (= v (select c i))) (= (select d i) v))` shipped as each
    /// document's only hole, and that step as `eq_transitive` checks `valid`.
    ///
    /// Read off the printed clause, which the shared chain step must prove
    /// exactly as printed ([`Self::printed_chain_step`]: carcara's own
    /// `find_chain` replay, or the closed-spelling bridge). That is only ever
    /// the equality predicate: `eq_transitive` reads every literal but the
    /// last as a `(not (= ..))` and the last as an `(= ..)`, and the strict
    /// validator puts the asserted application last.
    pub(super) fn eq_congruent_pred_chain_or_hole(&self, id: ProofId, clause: &[TermId]) -> String {
        let printed = self.format_clause(clause);
        if !self.work_budget_exhausted() {
            let literals = split_alethe_application_bounded(
                &printed,
                "cl",
                MAX_CONGRUENCE_LITERALS,
                MAX_CONGRUENCE_TERM_BYTES,
            );
            if let Some(chain) = literals
                .ok()
                .and_then(|literals| self.printed_chain_step(&id.to_string(), &literals))
            {
                return chain;
            }
        }
        format!("(step {id} {printed} :rule {UNPROVED_STEP_RULE})")
    }
}

/// Replay pinned carcara 1.1.0's `eq_congruent_pred` decision procedure over
/// the exact literal text a step is about to ship.
///
/// Mirrors `carcara/src/checker/rules/congruence.rs::eq_congruent_pred`:
///
/// * at least three literals (`assert_clause_len(conclusion, 3..)`);
/// * every literal but the last two is a `(not (= t u))` hypothesis;
/// * of the last two, ONE is negated: `(not (p t_1 .. t_n))` then
///   `(p u_1 .. u_n)`, or `(p t_1 .. t_n)` then `(not (p u_1 .. u_n))`
///   (carcara strips the negation from the first if it has one, else from
///   the second);
/// * both are applications of the SAME head with the SAME arity, and there
///   is EXACTLY one hypothesis per argument position;
/// * hypothesis `i` equates argument pair `i` in either orientation.
///
/// Heads and operands are compared with
/// [`equal_modulo_bitvec_literal_spelling`], carcara's term identity on the
/// two ways the printed surface can spell one term differently. A head the
/// tokenizer cannot read as one field, or two heads that differ as text,
/// decline — carcara compares its parsed function/operator terms, and a
/// distinct spelling this replay cannot prove equal is refused rather than
/// guessed.
pub(super) fn printed_eq_congruent_pred_holds(literals: &[&str]) -> bool {
    if !(3..=MAX_CONGRUENCE_LITERALS).contains(&literals.len()) {
        return false;
    }
    let (hypotheses, applications) = literals.split_at(literals.len() - 2);
    let [first, second] = applications else {
        return false;
    };
    let (left, right) = match split_printed_negation(first) {
        Some(left) => (left, *second),
        None => match split_printed_negation(second) {
            Some(right) => (*first, right),
            None => return false,
        },
    };
    let Some((left_head, left_args)) = split_printed_application(left) else {
        return false;
    };
    let Some((right_head, right_args)) = split_printed_application(right) else {
        return false;
    };
    if !equal_modulo_bitvec_literal_spelling(left_head, right_head)
        || left_args.len() != right_args.len()
        || hypotheses.len() != left_args.len()
    {
        return false;
    }
    hypotheses
        .iter()
        .zip(left_args.iter().zip(right_args.iter()))
        .all(|(hypothesis, (&left_arg, &right_arg))| {
            let Some(negated) = split_printed_negation(hypothesis) else {
                return false;
            };
            let Some((t, u)) = split_printed_equality(negated) else {
                return false;
            };
            (equal_modulo_bitvec_literal_spelling(t, left_arg)
                && equal_modulo_bitvec_literal_spelling(u, right_arg))
                || (equal_modulo_bitvec_literal_spelling(u, left_arg)
                    && equal_modulo_bitvec_literal_spelling(t, right_arg))
        })
}

/// One rendered application `(head a_1 .. a_n)` split into its head field and
/// its operand renderings. A bare symbol has no arguments to pair and is not
/// an application to carcara's rule, so it declines.
fn split_printed_application(term: &str) -> Option<(&str, Vec<&str>)> {
    let inner = term.strip_prefix('(')?.strip_suffix(')')?;
    let fields = split_smt_term_slices_bounded(
        inner,
        MAX_CONGRUENCE_LITERALS.saturating_add(1),
        MAX_CONGRUENCE_TERM_BYTES,
    )
    .ok()?;
    let (head, args) = fields.split_first()?;
    if args.is_empty() {
        return None;
    }
    Some((head, args.to_vec()))
}

/// One rendered binary `(= a b)` split into its two operand renderings.
fn split_printed_equality(term: &str) -> Option<(&str, &str)> {
    let operands =
        split_alethe_application_bounded(term, "=", 2, MAX_CONGRUENCE_TERM_BYTES).ok()?;
    match operands.as_slice() {
        [left, right] => Some((left, right)),
        _ => None,
    }
}

/// One rendered `(not X)` split into `X`.
fn split_printed_negation(term: &str) -> Option<&str> {
    let operands =
        split_alethe_application_bounded(term, "not", 1, MAX_CONGRUENCE_TERM_BYTES).ok()?;
    match operands.as_slice() {
        [only] => Some(only),
        _ => None,
    }
}

#[cfg(test)]
#[path = "alethe_printer_eq_congruent_pred_chain_tests.rs"]
mod chain_tests;

#[cfg(test)]
mod tests {
    use super::printed_eq_congruent_pred_holds;

    #[test]
    fn a_canonical_predicate_congruence_holds_in_both_polarity_orders() {
        assert!(printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not (= c d))",
            "(not (p a c))",
            "(p b d)",
        ]));
        assert!(printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not (= c d))",
            "(p a c)",
            "(not (p b d))",
        ]));
    }

    #[test]
    fn hypotheses_may_be_flipped_but_not_reordered() {
        // carcara pairs hypothesis `i` with argument position `i` and accepts
        // either orientation of that one equality.
        assert!(printed_eq_congruent_pred_holds(&[
            "(not (= b a))",
            "(not (= d c))",
            "(not (p a c))",
            "(p b d)",
        ]));
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= c d))",
            "(not (= a b))",
            "(not (p a c))",
            "(p b d)",
        ]));
    }

    #[test]
    fn the_hypothesis_count_must_equal_the_arity() {
        // `MissingPremise` and `TooManyPremises`: carcara does not let a
        // syntactically equal argument pair go without its hypothesis.
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not (p a c))",
            "(p b c)",
        ]));
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not (= c c))",
            "(not (= x y))",
            "(not (p a c))",
            "(p b c)",
        ]));
    }

    #[test]
    fn the_re_spelled_hypothesis_of_the_measured_shape_does_not_hold() {
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= (ite (not (= a b)) 1 0) 0))",
            "(not (p a))",
            "(p b)",
        ]));
    }

    #[test]
    fn different_heads_two_negations_or_no_negation_do_not_hold() {
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not (p a))",
            "(q b)",
        ]));
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not (p a))",
            "(not (p b))",
        ]));
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(p a)",
            "(p b)",
        ]));
        assert!(!printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not p)",
            "p",
        ]));
    }

    #[test]
    fn builtin_operators_are_applications_too() {
        // carcara's `Term::Op` arm: `(< a c)` and `(< b d)` share the operator.
        assert!(printed_eq_congruent_pred_holds(&[
            "(not (= a b))",
            "(not (= c d))",
            "(not (< a c))",
            "(< b d)",
        ]));
    }

    #[test]
    fn operand_spelling_differences_carcara_parses_to_one_term_still_hold() {
        assert!(printed_eq_congruent_pred_holds(&[
            "(not (= x #xAA))",
            "(not (p x))",
            "(p (_ bv170 8))",
        ]));
        assert!(printed_eq_congruent_pred_holds(&[
            "(not (= (f  a) b))",
            "(not (p (f a)))",
            "(p b)",
        ]));
    }
}
