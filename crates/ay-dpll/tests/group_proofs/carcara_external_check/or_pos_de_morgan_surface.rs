// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An `or_pos` gate whose PRINTED surface is `(not (and ...))`, not `(or ...)`.
//!
//! AY rewrites an authored `(not (and A1 .. An))` into an internal `or` node and
//! registers the authored spelling as that node's surface override, so the
//! `assume` keeps matching the problem premise. Tseitin then annotates the gate
//! clause `or_pos` — correctly, over the TERM — and the printer renders the
//! rule name from the internal classification and the term text from the
//! override. The two disagree, and Carcara refuses the step:
//!
//! ```text
//! [ERROR] checking failed on step 't240' with rule 'or_pos': term
//! '(not (not (and ...)))' is of the wrong form, expected '(not(or ...))'
//! ```
//!
//! That is an `invalid` document, not a holey one: a step claiming a rule it
//! does not instantiate, which no internal signal caught because AY's own
//! strict checker validates `or_pos` against the term DAG, where the node
//! really is an `or`. Measured on QF_UF/QG-classification, 14 of 120 sampled
//! files shipped it.
//!
//! Both fixtures below are the two spellings that made the existing De Morgan
//! bridge decline, and the second carries both at once:
//!
//! * the printed `and` is a NESTED binary spine, so one `and_neg` yields two
//!   negated operands instead of n;
//! * a conjunct is spelled with its equality arguments in the opposite order
//!   from the traced literal (`(= b (f a a))` in the override against
//!   `(= (f a a) b)` in the clause).

use super::{require_carcara_or_skip, run_carcara_trust_free, solve_unsat_and_get_proof};
use ntest::timeout;

/// Authored `(not (and (and A B) C))`: the printed conjunction is a nested
/// binary spine while the internal node is a flat n-ary `or`.
const NESTED_NEGATED_CONJUNCTION: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U U) U)
(assert (= (f a a) b))
(assert (= (f a b) c))
(assert (= (f b a) c))
(assert (not (and (and (= (f a a) b) (= (f a b) c)) (= (f b a) c))))
(check-sat)
"#;

/// The same shape, with two conjuncts authored in the opposite equality
/// orientation from the canonical term the clause literal carries.
const NESTED_NEGATED_CONJUNCTION_REVERSED_EQUALITIES: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun f (U U) U)
(assert (= (f a a) b))
(assert (= (f a b) c))
(assert (= (f b a) c))
(assert (not (and (and (= b (f a a)) (= (f a b) c)) (= c (f b a)))))
(check-sat)
"#;

/// Every `or_pos` step in `proof` must have `(not (or ...))` as its first
/// clause literal — the shape the Alethe rule is defined over.
fn or_pos_steps_are_well_formed(proof: &str) -> Result<(), String> {
    for line in proof.lines() {
        let line = line.trim();
        if !line.ends_with(":rule or_pos)") || !line.starts_with("(step ") {
            continue;
        }
        if !line.contains("(cl (not (or ") {
            return Err(line.to_string());
        }
    }
    Ok(())
}

#[test]
fn well_formed_gate_detector_reads_the_gate_literal() {
    assert!(or_pos_steps_are_well_formed("(step t1 (cl (not (or a b)) a b) :rule or_pos)").is_ok());
    assert!(or_pos_steps_are_well_formed(
        "(step t1 (cl (not (not (and a b))) (not a)) :rule or_pos)"
    )
    .is_err());
    // Other rules over the same shape are none of this detector's business.
    assert!(or_pos_steps_are_well_formed(
        "(step t1 (cl (not (not (and a b))) (not a)) :rule resolution)"
    )
    .is_ok());
}

#[test]
#[timeout(60_000)]
fn nested_negated_conjunction_or_pos_is_bridged_not_mislabelled() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "or_pos_de_morgan_nested";
    let proof = solve_unsat_and_get_proof(NESTED_NEGATED_CONJUNCTION, label);
    if let Err(step) = or_pos_steps_are_well_formed(&proof) {
        panic!("or_pos claimed over a non-disjunction:\n{step}\n\nfull proof:\n{proof}");
    }
    // The honest bridge, not a relabelling: the double negation is discharged
    // by `not_simplify`, and the nested spine by one `and_neg` per printed node.
    assert!(
        proof.contains(":rule not_simplify"),
        "the De Morgan bridge must discharge the double negation:\n{proof}"
    );
    assert!(
        proof.matches(":rule and_neg").count() >= 2,
        "a two-node printed spine needs one and_neg per node:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, label, NESTED_NEGATED_CONJUNCTION, &proof),
        "the bridged De Morgan gate must replay in Carcara without trust"
    );
}

#[test]
#[timeout(60_000)]
fn reversed_conjunct_equalities_are_bridged_by_eq_symmetric() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "or_pos_de_morgan_reversed";
    let proof = solve_unsat_and_get_proof(NESTED_NEGATED_CONJUNCTION_REVERSED_EQUALITIES, label);
    if let Err(step) = or_pos_steps_are_well_formed(&proof) {
        panic!("or_pos claimed over a non-disjunction:\n{step}\n\nfull proof:\n{proof}");
    }
    assert!(
        proof.contains(":rule eq_symmetric"),
        "a conjunct spelled in the reverse equality orientation must be \
         re-oriented by a real inference, not silently accepted:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(
            &carcara,
            label,
            NESTED_NEGATED_CONJUNCTION_REVERSED_EQUALITIES,
            &proof
        ),
        "the re-oriented De Morgan gate must replay in Carcara without trust"
    );
}
