// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The parity discovery routines read only self-loop clauses, and skip a
//! self-loop whose update they cannot read. Their candidates are admitted as
//! `algebraically_verified` (no SMT self-inductiveness check) only when
//! `is_parity_preserved_by_transitions` accepts every transition into the
//! predicate. Ported from the pre-publication history (663b1ed34f,
//! 2026-05-17), which never reached the published tree.

#![allow(clippy::unwrap_used)]

use crate::pdr::solver::test_helpers::solver_from_str;
use crate::{ChcExpr, ChcVar};

fn x_mod_2_is_0(x: ChcVar) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::Int(2)),
        ChcExpr::Int(0),
    )
}

/// `x' = x + 2` and `x' = x + n`: the second self-loop's increment is not a
/// constant, so discovery sees only `+2` and proposes `x mod 2 = 0`, which is
/// false (n = 5 reaches x = 5). Before the gate it went into frame 1 as an
/// algebraically verified lemma with no check at all.
#[test]
fn increment_divisibility_candidate_with_unread_self_loop_is_not_admitted() {
    let mut solver = solver_from_str(
        r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int) (n Int)) (=> (= x 0) (P x n))))
(assert (forall ((x Int) (y Int) (n Int)) (=> (and (P x n) (= y (+ x 2))) (P y n))))
(assert (forall ((x Int) (y Int) (n Int)) (=> (and (P x n) (= y (+ x n))) (P y n))))
(assert (forall ((x Int) (n Int)) (=> (and (P x n) (= x 5)) false)))
(check-sat)
"#,
    );
    let p = solver.problem.lookup_predicate("P").unwrap();
    let x = solver.canonical_vars(p).unwrap()[0].clone();
    let candidate = x_mod_2_is_0(x);

    solver.discover_increment_divisibility_invariants();

    assert!(
        !solver.frames[1].contains_lemma(p, &candidate),
        "the non-inductive x mod 2 = 0 must not reach frame 1"
    );
}

/// Positive control: with `x' = x + 2` the only transition, `x mod 2 = 0` is
/// inductive and is still admitted on the algebraic path.
#[test]
fn increment_divisibility_candidate_preserved_by_every_transition_stays_algebraic() {
    let mut solver = solver_from_str(
        r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 2))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (= x 5)) false)))
(check-sat)
"#,
    );
    let p = solver.problem.lookup_predicate("P").unwrap();
    let x = solver.canonical_vars(p).unwrap()[0].clone();
    let candidate = x_mod_2_is_0(x);

    solver.discover_increment_divisibility_invariants();

    let lemma = solver.frames[1]
        .lemmas
        .iter()
        .find(|lemma| lemma.predicate == p && lemma.formula == candidate)
        .expect("x mod 2 = 0 is inductive here and must be admitted");
    assert!(
        lemma.algebraically_verified,
        "a candidate every transition preserves keeps the algebraic admission"
    );
}
