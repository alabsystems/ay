// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #8530: QF_ABV egt-3096.smt2 false UNSAT with 0 theory conflicts.
//!
//! Root cause: kitten's solve() did not reset assumptions when returning
//! unknown (status==0, e.g. ticks limit hit). The next assume() call saw
//! status==0 and skipped reset_incremental(), appending new assumptions on
//! top of stale ones from the previous timed-out solve. During sweep's
//! backbone probing, this created assumption stacks of 100+ unrelated
//! literals, causing false UNSAT in equivalence probes.
//!
//! Fix: d619dfb10 — add reset_assumptions() and call it in solve() when
//! the result is 0 with non-empty assumptions.

use ntest::timeout;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// Exact reproduction of egt-3096.smt2 from SMT-LIB QF_ABV benchmarks.
/// This formula is SAT; the bug caused it to return UNSAT due to sweep
/// preprocessing corrupting kitten assumptions.
#[test]
#[timeout(30_000)]
fn test_abv_sweep_false_unsat_8530() {
    let smt = r#"
(set-info :smt-lib-version 2.6)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.
|)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun packet () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= (concat (_ bv0 24) (select packet (_ bv240 32))) (_ bv53 32))))
(assert (not (= (concat (_ bv0 24) (select packet (_ bv240 32))) (_ bv0 32))))
(assert (= (concat (_ bv0 24) (select packet (_ bv240 32))) (_ bv52 32)))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv242 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv53 32))))
(assert (= (concat (_ bv0 24) (select packet (bvadd (_ bv242 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv0 32)))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv243 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv53 32))))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv243 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv0 32))))
(assert (= (concat (_ bv0 24) (select packet (bvadd (_ bv243 32) (concat (_ bv0 24) (select packet (_ bv241 32)))))) (_ bv52 32)))
(assert (let ((?v_0 (concat (_ bv0 24) (select packet (_ bv241 32))))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (bvadd (_ bv0 32) (bvadd ?v_0 (_ bv2 32))) (_ bv1 32)) (_ bv1 32)) (concat (_ bv0 24) (select packet (bvadd (_ bv244 32) ?v_0))))))))
(assert (let ((?v_0 (bvadd (concat (_ bv0 24) (select packet (_ bv241 32))) (_ bv2 32)))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (_ bv0 32) ?v_0) (_ bv1 32)) ?v_0)))))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv245 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv53 32))))
(assert (not (= (concat (_ bv0 24) (select packet (bvadd (_ bv245 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv0 32))))
(assert (= (concat (_ bv0 24) (select packet (bvadd (_ bv245 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv52 32)))
(assert (let ((?v_0 (bvadd (_ bv246 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv547 32)))))
(assert (let ((?v_1 (concat (_ bv0 24) (select packet (_ bv241 32))))) (let ((?v_0 (bvadd ?v_1 (_ bv2 32)))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (bvadd (bvadd (_ bv0 32) ?v_0) (_ bv1 32)) ?v_0) (_ bv1 32)) (concat (_ bv0 24) (select packet (bvadd (_ bv246 32) (bvmul (_ bv2 32) ?v_1))))))))))
(assert (let ((?v_0 (bvadd (_ bv248 32) (bvmul (_ bv2 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (and (bvule (_ bv0 32) ?v_0) (bvule ?v_0 (_ bv547 32)))))
(assert (let ((?v_0 (bvadd (concat (_ bv0 24) (select packet (_ bv241 32))) (_ bv2 32)))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (bvadd (_ bv0 32) ?v_0) (_ bv1 32)) ?v_0) ?v_0)))))
(assert (= (concat (_ bv0 24) (select packet (bvadd (_ bv247 32) (bvmul (_ bv3 32) (concat (_ bv0 24) (select packet (_ bv241 32))))))) (_ bv53 32)))
(assert (let ((?v_0 (bvadd (concat (_ bv0 24) (select packet (_ bv241 32))) (_ bv2 32)))) (not (bvsle (_ bv308 32) (bvadd (bvadd (bvadd (bvadd (bvadd (bvadd (_ bv0 32) ?v_0) (_ bv1 32)) ?v_0) ?v_0) (_ bv1 32)) (concat (_ bv0 24) (_ bv83 8)))))))
(assert (not (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv28 32)))))))
(assert (not (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv29 32)))))))
(assert (not (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv30 32)))))))
(assert (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv31 32))))))
(assert (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select packet (_ bv29 32)))))
(check-sat)
(exit)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        results(&output),
        vec!["sat"],
        "Bug #8530: QF_ABV egt-3096 must be SAT (was false UNSAT due to kitten assumption accumulation in sweep)"
    );
}

/// Minimal QF_ABV formula that exercises the same code path: array select
/// with bitvector concat and arithmetic, enough complexity to trigger sweep
/// preprocessing with kitten backbone probing.
#[test]
#[timeout(15_000)]
fn test_abv_array_select_concat_bvadd_sat_8530() {
    let smt = r#"
(set-logic QF_ABV)
(declare-fun arr () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (concat (_ bv0 24) (select arr (_ bv240 32))) (_ bv52 32)))
(assert (not (= (concat (_ bv0 24) (select arr (_ bv240 32))) (_ bv53 32))))
(assert (= (concat (_ bv0 24) (select arr (bvadd (_ bv242 32) (concat (_ bv0 24) (select arr (_ bv241 32)))))) (_ bv0 32)))
(assert (not (= (concat (_ bv0 24) (_ bv0 8)) (concat (_ bv0 24) (select arr (_ bv31 32))))))
(check-sat)
(exit)
    "#;
    let output = crate::common::solve(smt);
    assert_eq!(
        results(&output),
        vec!["sat"],
        "QF_ABV array-select-concat-bvadd must be SAT"
    );
}
