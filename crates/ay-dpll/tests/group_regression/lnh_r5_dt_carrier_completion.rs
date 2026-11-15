// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model completion's step 1b (the lnh-r5 repair of `lv9`/`lv10`) gathers the
//! solve's own committed equality atoms of a GENUINELY uninterpreted sort
//! (`model/completion.rs`, `is_genuinely_uninterpreted_sort`). The term store
//! spells a datatype `Uninterpreted` too, and the step admitted those atoms:
//! on the eager DT+BV lane they are opaque Booleans no theory closes (the
//! ite-lifted constructor biconditionals, atoms over extensionality
//! witnesses), and merging classes on their SAT values gave
//! `(mkInner 0 0 0 K)` and `(mkInner 0 65 65 K)` one element. The strict
//! `ite_uf_definition` oracle refuted that model and the satisfiable query
//! below answered `unknown`: ay-chc's nested-vector counterexample
//! (`quantified::counterexample::tests::nested`) lost its checked witness.
//!
//! The query is ay-chc's rendered replay obligation, verbatim. `lv9`/`lv10`
//! in `lnh_r5_regression` keep the genuinely uninterpreted half of the step.

use std::time::Duration;

use ay_dpll::api::{Logic, Solver};

use super::lnh_symmetry_domain_soundness::{
    solve, verdicts, Posture, DECIDED_BUDGET, NEVER_WRONG_BUDGET, POSTURES,
};

/// Satisfiable (z3 5.1.0: `sat`): row 33 of the outer vector has length 65,
/// so cell (33, 64) exists and holds 7, which is distinct from 8.
const NESTED_VEC_SAT: &str = r#"(set-logic ALL)
(declare-datatypes ((Inner 0) (Outer 0)) (((mkInner (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))) ((mkOuter (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner))))))
(declare-const ay_qcex_0 Outer)
(declare-const ay_qcex_1 Outer)
(declare-const ay_qcex_2 (_ BitVec 64))
(declare-const ay_qcex_3 (_ BitVec 64))
(assert true)
(assert (let ((ay!source!0 ay_qcex_0)) (= ay!source!0 ((as mkOuter Outer) (_ bv0 64) (_ bv34 64) (_ bv34 64) (store ((as const (Array (_ BitVec 64) Inner)) ((as mkInner Inner) (_ bv0 64) (_ bv0 64) (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8)))) (_ bv33 64) ((as mkInner Inner) (_ bv0 64) (_ bv65 64) (_ bv65 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))))))))
(assert (let ((ay!source!0 ay_qcex_0)) (forall ((ay!source!1 (_ BitVec 64))(ay!source!2 (_ BitVec 64))) (=> (and (bvult ay!source!1 (fld_len ay!source!0)) (bvult ay!source!2 (fld_len (select (fld_data ay!source!0) ay!source!1)))) (= (select (fld_data (select (fld_data ay!source!0) ay!source!1)) ay!source!2) (_ bv7 8))))))
(assert (let ((ay!source!3 ay_qcex_1)(ay!source!4 ay_qcex_2)(ay!source!5 ay_qcex_3)) (and (= ay!source!4 (_ bv33 64)) (= ay!source!5 (_ bv64 64)) (bvult ay!source!4 (fld_len ay!source!3)) (bvult ay!source!5 (fld_len (select (fld_data ay!source!3) ay!source!4))) (distinct (select (fld_data (select (fld_data ay!source!3) ay!source!4)) ay!source!5) (_ bv8 8)))))
(assert (= (let ((ay!source!3 ay_qcex_1)(ay!source!4 ay_qcex_2)(ay!source!5 ay_qcex_3)) ay!source!3) (let ((ay!source!0 ay_qcex_0)) ay!source!0)))
(check-sat)
"#;

/// The negative twin (z3 5.1.0: `unsat`): the same query asking the cell to
/// differ from 7, which the quantified premise pins it to.
fn nested_vec_unsat() -> String {
    let twin = NESTED_VEC_SAT.replace("ay!source!5) (_ bv8 8))", "ay!source!5) (_ bv7 8))");
    assert_ne!(twin, NESTED_VEC_SAT, "the twin must change the query");
    twin
}

/// ay-chc's replay path (`quantified/counterexample/replay.rs`): a fresh
/// `Logic::All` solver, the rendered body, the interruptible internal query.
/// `Some(true)`: checked SAT (model validated, emission witness); `Some(false)`:
/// `unsat`; `None`: neither.
fn chc_replay_verdict(script: &str, budget: Duration) -> Option<bool> {
    let body = script
        .strip_prefix("(set-logic ALL)\n")
        .expect("the renderer's header");
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let assertions = solver.parse_smtlib2(body).expect("parse");
    assert!(!assertions.is_empty());
    drop(assertions);
    solver.set_timeout(Some(budget));
    let verdict = solver.check_sat_interruptible_internal_query(|| false);
    if verdict.is_sat() {
        assert!(
            verdict.was_model_validated() && verdict.has_sat_emission_witness(),
            "a `sat` on the replay path must carry its checked witness"
        );
        Some(true)
    } else if verdict.is_unsat() {
        Some(false)
    } else {
        None
    }
}

#[test]
fn nested_vec_witness_is_checked_sat_on_the_chc_replay_path() {
    assert_eq!(
        chc_replay_verdict(NESTED_VEC_SAT, DECIDED_BUDGET),
        Some(true),
        "z3 5.1.0 says sat; the replay path must decide it with a checked model"
    );
}

#[test]
fn nested_vec_twins_are_never_wrong() {
    let unsat = nested_vec_unsat();
    assert_ne!(
        chc_replay_verdict(&unsat, NEVER_WRONG_BUDGET),
        Some(true),
        "WRONG VERDICT: the negative twin is unsat (z3 5.1.0) but the replay path minted sat"
    );
    for posture in POSTURES {
        for (smt, wrong) in [(NESTED_VEC_SAT, "unsat"), (unsat.as_str(), "sat")] {
            let results = solve(smt, posture, NEVER_WRONG_BUDGET);
            assert!(
                !verdicts(&results).contains(&wrong),
                "WRONG VERDICT ({posture:?}): z3 5.1.0 never says `{wrong}` here; got {results:?}"
            );
        }
    }
}

#[test]
fn nested_vec_witness_is_decided_by_the_executor() {
    for posture in [Posture::Plain, Posture::Authored, Posture::Z3Mode] {
        let results = solve(NESTED_VEC_SAT, posture, DECIDED_BUDGET);
        assert_eq!(
            verdicts(&results),
            vec!["sat"],
            "nested vector ({posture:?}): z3 5.1.0 says sat; got {results:?}"
        );
    }
}
