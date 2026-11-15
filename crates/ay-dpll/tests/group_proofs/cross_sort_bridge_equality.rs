// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A proof rebuild must not leave an equality across two sorts in the shared
//! term store (`plan_eq`, `executor/proof_original_rebuild.rs`).
//!
//! On the one-element-list refutation below, the substitution bridge pairs an
//! authored `=` over the list sort `L` with a leaf `=` over the cell sort `U`
//! (one head, one arity), and `plan_eq` used to intern `(= a u)` before it
//! tried any leg. A same-context consequence-replay probe later collected
//! datatype axioms from the whole store, read that dead ill-sorted term as an
//! atom, and its variable substitution panicked rebuilding it
//! (`mk_eq_coerce_no_ite_expand cannot coerce Uninterpreted("L") =
//! Uninterpreted("U")`), so the `:produce-proofs` solve died. The fixture is
//! the Carcara corpus row `wrong-verdict_unsat_ufdt_forall_field_sort_list_cells`,
//! which panicked this way from f1a718aed (which first sent its proof through
//! the bridge) through 9fce3bc73. Without proofs it was always `unsat`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `|U| = 1` by the universal, so two one-element lists are equal.
const ONE_ELEMENT_LISTS: &str = "(set-option :produce-proofs true)
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((L 0)) (((nil) (cons (hd U) (tl L)))))
(declare-const a L)
(declare-const b L)
(declare-const u U)
(assert (distinct a b))
(assert ((_ is cons) a))
(assert ((_ is cons) b))
(assert (= (tl a) nil))
(assert (= (tl b) nil))
(assert (forall ((x U)) (= x u)))
(check-sat)
(get-proof)
";

#[test]
#[timeout(30_000)]
fn a_cross_sort_bridge_pairing_leaves_the_proof_mode_refutation_intact() {
    let commands = parse(ONE_ELEMENT_LISTS).expect("parse the fixture");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute the fixture");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.last().map(String::as_str).unwrap_or_default();
    assert!(
        proof.contains("(assume ") && proof.contains("(step "),
        "the refutation must still publish an Alethe document: {proof}"
    );
}
