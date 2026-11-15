// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! LNH symmetry clauses outliving their check (2026-10-02 audit of the
//! domain repair, `k00`..`k11`, `M3*`, `M8b`, `L*`; on main since the pass
//! landed).
//!
//! The pass appends its clauses `B` (the least-index pin `e = c0`, the
//! lex-leader chains) to the solve-time assertion vector, which `check_sat`
//! restores. But the persistent incremental lanes (the DT, Seq, LIA/LRA
//! persist-SAT pipelines on the theory lane, the BV lane) activate every
//! non-root term they encode at the current push depth and never retract it
//! when the check ends — forever at depth 0. A later check that the pass
//! correctly declines (its problem is asymmetric) was solved under the stale
//! pin: wrong `unsat` in `--z3-mode`, `unknown` in the default posture. The
//! pass now stays out of incremental sessions (`lnh_admissible_for_check`),
//! and a check that does carry `B` runs on none of the session's lanes.
//!
//! The same harness and postures as `lnh_symmetry_domain_soundness`.

use super::lnh_symmetry_domain_soundness::{
    solve, verdicts, Posture, DECIDED_BUDGET, NEVER_WRONG_BUDGET, POSTURES,
};

/// Lane leak (2026-10-02 audit k08): the least-index pin `e = c0` of the
/// first check was encoded by the persistent DATATYPE lane at push depth 1 and
/// stayed active for the second check, which the pass correctly declines:
/// wrong `unsat` in `--z3-mode`, `unknown` in the default posture.
const LEAK_DT_SAME_DEPTH: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((N 0)) (((z) (s (p N)))))
(declare-const e N) (declare-const c0 N) (declare-const c1 N) (declare-const c2 N) (declare-const c3 N) (declare-const c4 N)
(push 1)
(assert (or (= e c0) (= e c1) (= e c2) (= e c3) (= e c4)))
(check-sat)
(assert (not (= e c0)))
(check-sat)
"#;

/// k02: depth 0 after a `(push 1)(pop 1)` — the leaked pin was permanent.
const LEAK_DT_DEPTH0: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((U 0)) (((zz) (ss (pp U)))))
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U)
(declare-const e U)
(push 1)(pop 1)
(assert (distinct c0 c1 c2 c3 c4))
(assert (or (= e c0) (= e c1) (= e c2) (= e c3) (= e c4)))
(check-sat)
(assert (= e c4))
(check-sat)
"#;

/// k09: the pure-UF shape routed to the persistent BV lane by its logic.
const LEAK_UFBV_LOGIC: &str = r#"
(set-logic QF_UFBV)
(declare-sort U 0)
(declare-const e U) (declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U)
(push 1)
(assert (or (= e c0) (= e c1) (= e c2) (= e c3) (= e c4)))
(check-sat)
(assert (not (= e c0)))
(check-sat)
"#;

/// M8b: the persistent sequence lane.
const LEAK_SEQ: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(declare-const x U)
(declare-const sq (Seq Int))
(push 1)
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (or (= x c0) (= x c1) (= x c2) (= x c3) (= x c4) (= x c5)))
(assert (= (seq.len sq) 2))
(check-sat)
(assert (not (= x c0)))
(check-sat)
(pop 1)
"#;

/// k04: the lex-leader chain leaked the same way (`p c0`, not `p c1`).
const LEAK_LEXLEADER_UFDT: &str = r#"
(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ((Nat 0)) (((zz) (ss (pp Nat)))))
(declare-const n Nat)
(declare-fun p (U) Bool)
(declare-const b Bool)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(declare-const e U)
(push 1)
(assert ((_ is ss) n))
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (= b (or (= e c0) (= e c1) (= e c2) (= e c3) (= e c4) (= e c5))))
(assert (or (p c0) (p c1) (p c2) (p c3) (p c4) (p c5)))
(check-sat)
(assert (p c0))
(assert (not (p c1)))
(check-sat)
"#;

/// k11: the leak survived an intervening `check-sat-assuming`.
const LEAK_AFTER_CHECK_SAT_ASSUMING: &str = r#"
(set-logic QF_DT)
(declare-datatypes ((U 0)) (((zz) (ss (pp U)))))
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U)
(declare-const e U)
(push 1)
(assert (distinct c0 c1 c2 c3 c4))
(assert (or (= e c0) (= e c1) (= e c2) (= e c3) (= e c4)))
(check-sat)
(check-sat-assuming ((not (= e c0))))
(assert (not (= e c0)))
(check-sat)
"#;

/// V1: one check, no push. With the pin `x = c0`, `VariableSubstitution`
/// eliminated `x` and the BV lane committed `(p c0)` only; the evaluator had
/// no congruence fallback for a Bool application, so `(p x)` evaluated to
/// Unknown and a satisfiable QF_UFBV problem came back `unknown`.
const UFBV_PREDICATE_OVER_SUBSTITUTED_ARG: &str = r#"
(set-logic QF_UFBV)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(declare-const x U)
(declare-fun p (U) Bool)
(declare-fun g (U) (_ BitVec 8))
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (or (= x c0) (= x c1) (= x c2) (= x c3) (= x c4) (= x c5)))
(assert (p x))
(assert (bvugt (g x) #x05))
(check-sat)
"#;

/// Fixtures with z3 5.1.0's answers, and how many leading checks `--z3-mode`
/// must decide.
const FIXTURES: [(&str, &str, &[&str], usize); 7] = [
    ("lane leak, DT", LEAK_DT_SAME_DEPTH, &["sat", "sat"], 2),
    ("lane leak, DT depth 0", LEAK_DT_DEPTH0, &["sat", "sat"], 2),
    (
        "lane leak, QF_UFBV logic",
        LEAK_UFBV_LOGIC,
        &["sat", "sat"],
        2,
    ),
    ("lane leak, Seq", LEAK_SEQ, &["sat", "sat"], 2),
    (
        "lane leak, lex-leader UFDT",
        LEAK_LEXLEADER_UFDT,
        &["sat", "sat"],
        2,
    ),
    (
        "lane leak after check-sat-assuming",
        LEAK_AFTER_CHECK_SAT_ASSUMING,
        &["sat", "sat", "sat"],
        3,
    ),
    (
        "UFBV predicate over a substituted argument",
        UFBV_PREDICATE_OVER_SUBSTITUTED_ARG,
        &["sat"],
        1,
    ),
];

/// A definite answer that contradicts z3 is wrong; `unknown` is not.
#[test]
fn lnh_clauses_never_outlive_their_check() {
    for (name, smt, expect, _) in FIXTURES {
        for posture in POSTURES {
            let results = solve(smt, posture, NEVER_WRONG_BUDGET);
            let got = verdicts(&results);
            assert_eq!(
                got.len(),
                expect.len(),
                "{name} ({posture:?}): one verdict per check expected; got {results:?}"
            );
            for (index, (&got, &want)) in got.iter().zip(expect).enumerate() {
                assert!(
                    got == want || got == "unknown",
                    "WRONG VERDICT ({name}, {posture:?}, check {index}): z3 5.1.0 says \
                     `{want}`, got `{got}`; all answers {all:?}",
                    all = verdicts(&results)
                );
            }
        }
    }
}

/// `--z3-mode` decides every check (z3 5.1.0 decides each in milliseconds).
#[test]
fn lnh_lane_leak_fixtures_are_decided_in_z3_mode() {
    for (name, smt, expect, decided) in FIXTURES {
        let results = solve(smt, Posture::Z3Mode, DECIDED_BUDGET);
        assert_eq!(
            verdicts(&results).get(..decided),
            expect.get(..decided),
            "{name} (Z3Mode): z3 5.1.0's answers expected; got {results:?}"
        );
    }
}

/// The native API turns incremental mode on when an assertion follows a
/// check, with no `push` (`note_api_assertion_mutation`), so the persistent BV
/// lane kept the first check's pin `e = c0` the same way.
#[test]
fn lnh_pin_does_not_outlive_its_check_through_the_native_api() {
    use ay_dpll::api::{Logic, Solver, Sort};
    let mut solver = Solver::try_new(Logic::QfUfbv).expect("solver");
    let u = Sort::Uninterpreted("U".to_string());
    let e = solver.declare_const("e", u.clone());
    let cs: Vec<_> = (0..6)
        .map(|i| solver.declare_const(&format!("c{i}"), u.clone()))
        .collect();
    let distinct = solver.distinct(&cs);
    solver.assert_term(distinct);
    let eqs: Vec<_> = cs.iter().map(|&c| solver.eq(e, c)).collect();
    let totality = solver.or_many(&eqs);
    solver.assert_term(totality);
    let first = solver.check_sat();
    assert!(first.is_sat(), "z3 5.1.0: sat; got {:?}", first.result());
    let pinned = solver.eq(e, cs[0]);
    let not_pinned = solver.not(pinned);
    solver.assert_term(not_pinned);
    let second = solver.check_sat();
    assert!(
        !second.is_unsat(),
        "z3 5.1.0: sat (e = c1); the first check's pin must not survive it"
    );
    assert!(second.is_sat(), "z3 5.1.0: sat; got {:?}", second.result());
}
