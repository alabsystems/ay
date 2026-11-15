// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
#![allow(clippy::panic)]

//! LEAKAGE and COST guards for admitting `no_mbqi` into the constant-
//! interpretation SAT certificate. Blast radius, not soundness-by-argument:
//! leakage across queries in one solver, perturbation of the shared term
//! store, and the wall-clock the admission now spends on snapshots that used
//! to decline on the first line.

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};
use std::time::Instant;

#[derive(Debug, PartialEq, Eq)]
enum V {
    Sat,
    Unsat,
    Unknown,
}

fn verdict(solver: &mut Solver) -> V {
    let details = solver.check_sat_with_details();
    match details.accept_for_consumer() {
        Ok(SolveResult::Sat) => V::Sat,
        Ok(SolveResult::Unsat(_)) => V::Unsat,
        Ok(SolveResult::Unknown) => V::Unknown,
        other => panic!("unexpected solve outcome: {other:?}"),
    }
}

/// R1. GRANT THEN A DIFFERENT UNSAT QUERY IN THE SAME SOLVER.
/// Query 1 is the witnessless choose (grants on the branch). Query 2, pushed
/// on top, is an ARITHMETIC contradiction that has nothing to do with the
/// certificate. A leaked grant / stale witness would answer anything but
/// `unsat`.
fn grant_then_unrelated_unsat() -> (V, V) {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let px = s.try_apply(&p, &[x]).unwrap();
    let pc = s.try_apply(&p, &[c]).unwrap();
    let body = s.try_implies(px, pc).unwrap();
    let q = s.try_forall(&[x], body).unwrap();
    s.mark_no_mbqi(q);
    s.try_assert_term(q).unwrap();
    let npc = s.try_not(pc).unwrap();
    s.try_assert_term(npc).unwrap();
    let first = verdict(&mut s);
    s.push();
    let n = s.declare_const("n", Sort::Int);
    let zero = s.int_const(0);
    let one = s.int_const(1);
    let lt = s.try_lt(n, zero).unwrap();
    let gt = s.try_gt(n, one).unwrap();
    let both = s.try_and(lt, gt).unwrap();
    s.try_assert_term(both).unwrap();
    let second = verdict(&mut s);
    s.pop();
    (first, second)
}

/// R2. THE SAME UNSAT QUERY, WITH AND WITHOUT A PRIOR GRANT IN THE SAME
/// SOLVER. Both must be `unsat`; a difference is leakage.
fn unsat_after_grant_vs_alone() -> (V, V) {
    fn unsat_query(s: &mut Solver) -> V {
        let f = s.declare_fun("f", &[Sort::Int], Sort::Int);
        let a = s.declare_const("a", Sort::Int);
        let y = s.fresh_var("y", Sort::Int);
        let fy = s.try_apply(&f, &[y]).unwrap();
        let zero = s.int_const(0);
        let ge = s.try_ge(fy, zero).unwrap();
        let all = s.try_forall(&[y], ge).unwrap();
        s.try_assert_term(all).unwrap();
        let fa = s.try_apply(&f, &[a]).unwrap();
        let neg = s.int_const(-1);
        let eq = s.try_eq(fa, neg).unwrap();
        s.try_assert_term(eq).unwrap();
        verdict(s)
    }
    let mut alone = Solver::try_new(Logic::All).expect("logic");
    let v_alone = unsat_query(&mut alone);

    let mut after = Solver::try_new(Logic::All).expect("logic");
    {
        let p = after.declare_fun("P", &[Sort::Int], Sort::Bool);
        let c = after.declare_const("c", Sort::Int);
        let x = after.fresh_var("x", Sort::Int);
        let px = after.try_apply(&p, &[x]).unwrap();
        let pc = after.try_apply(&p, &[c]).unwrap();
        let body = after.try_implies(px, pc).unwrap();
        let q = after.try_forall(&[x], body).unwrap();
        after.mark_no_mbqi(q);
        after.push();
        after.try_assert_term(q).unwrap();
        let npc = after.try_not(pc).unwrap();
        after.try_assert_term(npc).unwrap();
        let _ = verdict(&mut after);
        after.pop();
    }
    let v_after = unsat_query(&mut after);
    (v_alone, v_after)
}

/// R3. THE COST OF A DECLINE THAT USED TO BE FREE.
/// `forall u:U. h(u) > g(u) + 5` is SAT but no CONSTANT interpretation
/// satisfies it, so the certificate enumerates its whole combination space and
/// declines. Before the change a marked snapshot returned `None` on the
/// certificate's FIRST line; now it pays the full budget. Verdict is `unknown`
/// on both sides — this measures only the wall clock the admission added.
fn decline_cost(mark: bool) -> (V, u128) {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let u = Sort::Uninterpreted("U".to_string());
    let h = s.declare_fun("h", &[u.clone()], Sort::Int);
    let g = s.declare_fun("g", &[u.clone()], Sort::Int);
    let v = s.fresh_var("v", u);
    let hv = s.try_apply(&h, &[v]).unwrap();
    let gv = s.try_apply(&g, &[v]).unwrap();
    let five = s.int_const(5);
    let sum = s.try_add(gv, five).unwrap();
    let gtt = s.try_gt(hv, sum).unwrap();
    let q = s.try_forall(&[v], gtt).unwrap();
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).unwrap();
    let start = Instant::now();
    let out = verdict(&mut s);
    (out, start.elapsed().as_millis())
}

/// R4. DETERMINISM. The witnessless choose, marked, solved five times in five
/// fresh solvers: every verdict must agree.
fn determinism() -> Vec<V> {
    (0..5)
        .map(|_| {
            let mut s = Solver::try_new(Logic::All).expect("logic");
            let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
            let c = s.declare_const("c", Sort::Int);
            let x = s.fresh_var("x", Sort::Int);
            let px = s.try_apply(&p, &[x]).unwrap();
            let pc = s.try_apply(&p, &[c]).unwrap();
            let body = s.try_implies(px, pc).unwrap();
            let q = s.try_forall(&[x], body).unwrap();
            s.mark_no_mbqi(q);
            s.try_assert_term(q).unwrap();
            let npc = s.try_not(pc).unwrap();
            s.try_assert_term(npc).unwrap();
            verdict(&mut s)
        })
        .collect()
}

/// R5. AN UNSAT SNAPSHOT THAT NEEDS THE MARKED AXIOM TO CLOSE.
/// `forall x. P(x) => P(c)`, marked, beside ground `P(3)` and `not P(c)`.
/// Truth: UNSAT. The mark tells ay to reach it by E-matching the ground
/// witness; the certificate must not answer `sat`.
fn ground_witness_unsat(mark: bool) -> V {
    let mut s = Solver::try_new(Logic::All).expect("logic");
    let p = s.declare_fun("P", &[Sort::Int], Sort::Bool);
    let c = s.declare_const("c", Sort::Int);
    let x = s.fresh_var("x", Sort::Int);
    let px = s.try_apply(&p, &[x]).unwrap();
    let pc = s.try_apply(&p, &[c]).unwrap();
    let body = s.try_implies(px, pc).unwrap();
    let q = s.try_forall(&[x], body).unwrap();
    if mark {
        s.mark_no_mbqi(q);
    }
    s.try_assert_term(q).unwrap();
    let three = s.int_const(3);
    let p3 = s.try_apply(&p, &[three]).unwrap();
    s.try_assert_term(p3).unwrap();
    let npc = s.try_not(pc).unwrap();
    s.try_assert_term(npc).unwrap();
    verdict(&mut s)
}

#[test]
fn regression_probes() {
    let (first, second) = grant_then_unrelated_unsat();
    println!("REGR R1 grant={first:?} unrelated_unsat={second:?}");
    assert_eq!(
        second,
        V::Unsat,
        "R1: leaked grant changed an unrelated UNSAT"
    );

    let (alone, after) = unsat_after_grant_vs_alone();
    println!("REGR R2 unsat_alone={alone:?} unsat_after_grant={after:?}");
    assert_eq!(alone, after, "R2: a prior grant changed a later verdict");

    for mark in [false, true] {
        let (v, ms) = decline_cost(mark);
        println!("REGR R3 decline_cost mark={mark} verdict={v:?} ms={ms}");
    }

    let d = determinism();
    println!("REGR R4 determinism={d:?}");
    assert!(
        d.windows(2).all(|w| w[0] == w[1]),
        "R4: nondeterministic verdict"
    );

    for mark in [false, true] {
        let v = ground_witness_unsat(mark);
        println!("REGR R5 ground_witness_unsat mark={mark} verdict={v:?}");
        assert_eq!(v, V::Unsat, "R5: a ground-witness refutation was lost");
    }
    println!("REGR-DONE");
}
