// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The combined DT+X routes re-solve an `unknown` round one depth deeper
//! (`solve_with_dt_axioms`) and stop when a round would solve the previous
//! round's assertion window again. The read-over-equality pass minted a fresh
//! extensionality witness every round (`theories/ext_read_witness.rs`), so
//! each round was a renamed copy of the last, plus axioms over the reads of
//! the discarded witnesses, and that exit never fired. Inside the finite-model
//! refinement of ay-chc's nested-vector replay obligation (below, verbatim) 62
//! rounds repeated one `unknown`: about 10 s of the 11.25 s counterexample
//! slice on a slow core, which made
//! `quantified::counterexample::tests::nested::concrete_nested_vec_*` flaky
//! there.

use std::time::Duration;

use ay_dpll::api::{Logic, Solver};

use crate::common::solve_vec;

/// Satisfiable (z3 5.1.0: `sat`).
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

/// ay-chc's authored metamorphic control
/// `tests/fixtures/quantified_nested_cells/missing_outer_frame.smt2`, verbatim
/// below its comment header (z3 5.1.0: `sat`). Its deciding round is a later
/// round whose axioms cover datatype-valued reads an earlier round's solve
/// minted, so it is solved only while a round that adds axioms is re-solved.
const MISSING_OUTER_FRAME_SAT: &str = "(set-logic ALL)
(declare-datatypes ((Inner 0) (Outer 0))
  (((mk_inner (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8)))))
   ((mk_outer (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                   (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner))))))
(declare-const before Outer)
(declare-const after Outer)
(declare-const old_cell Inner)
(declare-const new_cell Inner)
(declare-const after_cells (Array (_ BitVec 64) Inner))
(assert (= old_cell (select (fld_data before) (_ bv33 64))))
(assert (= new_cell
  (mk_inner (fld_ptr old_cell) (fld_len old_cell) (fld_cap old_cell)
            (store (fld_data old_cell) (_ bv64 64) #x09))))
(assert (= (select after_cells (_ bv33 64)) new_cell))
(assert (= after (mk_outer (fld_ptr before) (fld_len before) (fld_cap before) after_cells)))
(assert (= (select (fld_data (select (fld_data before) (_ bv64 64))) (_ bv33 64)) #x07))
(assert (not (= (select (fld_data (select (fld_data after) (_ bv64 64))) (_ bv33 64)) #x07)))
(check-sat)
";

/// One session, four public queries over two datatype-element arrays that
/// are equal (z3 5.1.0: `sat unsat sat unsat`). The second query's clash sits
/// at an index nothing reads, so only that query's read witness refutes it.
const UNREAD_CLASH_SESSION: &str = "(set-logic ALL)
(declare-datatype S ((mk (f Int) (g Int))))
(declare-const a (Array Int S))
(declare-const b (Array Int S))
(assert (= a b))
(check-sat)
(push 1)
(assert (= a ((as const (Array Int S)) (mk 0 0))))
(assert (= b ((as const (Array Int S)) (mk 1 0))))
(check-sat)
(pop 1)
(push 1)
(assert (= a ((as const (Array Int S)) (mk 5 0))))
(assert (= b ((as const (Array Int S)) (mk 5 0))))
(check-sat)
(pop 1)
(push 1)
(assert (= a ((as const (Array Int S)) (mk 0 0))))
(assert (= b (store ((as const (Array Int S)) (mk 0 0)) 7 (mk 0 1))))
(check-sat)
(pop 1)
";

/// Term-store size after the nested-vector replay. Measured on a fresh
/// solver: 2,793 terms with one witness per query, 46,991 when every round
/// re-solved up to the depth ceiling.
const NESTED_VEC_REPLAY_TERM_CEILING: u64 = 12_000;

/// ay-chc's replay path (`quantified/counterexample/replay.rs`): a fresh
/// `Logic::All` solver, the rendered body, the interruptible internal query.
/// Returns `Some(true)` for checked SAT, `Some(false)` for `unsat`, and the
/// solver's final term count.
fn replay(script: &str) -> (Option<bool>, u64) {
    let body = script
        .strip_prefix("(set-logic ALL)\n")
        .expect("the renderer's header");
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let assertions = solver.parse_smtlib2(body).expect("parse");
    assert!(!assertions.is_empty());
    drop(assertions);
    // A wall backstop only; the assertions below are on verdicts and counted
    // work.
    solver.set_timeout(Some(Duration::from_secs(30)));
    let verdict = solver.check_sat_interruptible_internal_query(|| false);
    let decided = if verdict.is_sat() {
        assert!(
            verdict.was_model_validated() && verdict.has_sat_emission_witness(),
            "a `sat` on the replay path must carry its checked witness"
        );
        Some(true)
    } else if verdict.is_unsat() {
        Some(false)
    } else {
        None
    };
    (decided, solver.statistics().term_count)
}

#[test]
fn nested_vec_replay_stops_at_the_repeated_round() {
    let (verdict, terms) = replay(NESTED_VEC_SAT);
    assert_eq!(
        verdict,
        Some(true),
        "z3 5.1.0 says sat; the replay path must decide it with a checked model"
    );
    assert!(
        terms <= NESTED_VEC_REPLAY_TERM_CEILING,
        "the replay minted {terms} terms (ceiling {NESTED_VEC_REPLAY_TERM_CEILING}): \
         the deepening loop is re-solving repeated rounds again"
    );
}

/// The negative twin: with one witness the window repeats only when no
/// axiom changed, so a round that adds axioms is still solved. Stopping this
/// flat vocabulary after its first round, or stopping all deepening, leaves
/// it `unknown`.
#[test]
fn a_round_that_adds_axioms_is_still_solved() {
    let (verdict, _) = replay(MISSING_OUTER_FRAME_SAT);
    assert_eq!(
        verdict,
        Some(true),
        "z3 5.1.0 says sat; its deciding round adds axioms over reads the \
         previous round's solve minted"
    );
}

/// The soundness twin of the reuse: a later query of a session still
/// refutes its unread clash, with a witness of its own, and never refutes
/// the satisfiable one.
#[test]
fn a_later_query_refutes_an_unread_clash_with_its_own_witness() {
    let verdicts = solve_vec(UNREAD_CLASH_SESSION);
    assert_eq!(verdicts.len(), 4, "{verdicts:?}");
    assert_eq!(verdicts[0], "sat", "{verdicts:?}");
    assert_eq!(verdicts[1], "unsat", "the fills differ: {verdicts:?}");
    assert_ne!(
        verdicts[2], "unsat",
        "WRONG VERDICT: equal fills satisfy (= a b): {verdicts:?}"
    );
    assert_eq!(verdicts[3], "unsat", "the arrays differ at 7: {verdicts:?}");
}
