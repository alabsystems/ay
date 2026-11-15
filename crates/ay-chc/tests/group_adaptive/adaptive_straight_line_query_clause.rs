// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! A straight-line BV program over a validity array (two steps, two error
//! rules): the BV-native probe refutes the collapsed query, and the Safe
//! answer stands once the back-translated model validates on the original
//! clauses. The query clause's body under that model pins the validity array
//! to a store chain; checked raw it stays an array query for the
//! proof-carrying executor (unknown within the per-rule cap), so query-clause
//! validation must substitute the definitions away as transition validation
//! does.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const STRAIGHT_LINE: &str = r#"(set-logic HORN)
(declare-fun p0 ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 32) Bool) (Array (_ BitVec 64) (_ BitVec 64))) Bool)
(declare-fun p1 ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 32) Bool) (Array (_ BitVec 64) (_ BitVec 64))) Bool)
(declare-fun p2 ((_ BitVec 64) (_ BitVec 64) (Array (_ BitVec 32) Bool) (Array (_ BitVec 64) (_ BitVec 64))) Bool)
(assert (forall ((x0 (_ BitVec 64)) (x1 (_ BitVec 64)) (va (Array (_ BitVec 32) Bool)) (ma (Array (_ BitVec 64) (_ BitVec 64)))) (=> (and (= x0 #x5f58d8c050c05c5b) (= x1 #x0000000000000000) (= va ((as const (Array (_ BitVec 32) Bool)) true)) (= ma ((as const (Array (_ BitVec 64) (_ BitVec 64))) #x0000000000000000))) (p0 x0 x1 va ma))))
(assert (forall ((x0 (_ BitVec 64)) (x1 (_ BitVec 64)) (y0 (_ BitVec 64)) (y1 (_ BitVec 64)) (t0 (_ BitVec 64)) (t1 (_ BitVec 64)) (t2 (_ BitVec 64)) (t3 (_ BitVec 64)) (t4 (_ BitVec 64)) (t5 (_ BitVec 64)) (t6 (_ BitVec 64)) (t7 (_ BitVec 64)) (t8 (_ BitVec 64)) (t9 (_ BitVec 64)) (t10 (_ BitVec 64)) (t11 (_ BitVec 64)) (va (Array (_ BitVec 32) Bool)) (vb (Array (_ BitVec 32) Bool)) (lv (Array (_ BitVec 32) Bool)) (ma (Array (_ BitVec 64) (_ BitVec 64))) (mb (Array (_ BitVec 64) (_ BitVec 64))) (rd (_ BitVec 64)) (ok Bool)) (=> (and (p0 x0 x1 va ma) (= (bvsub (bvlshr (ite (= x1 #x0000000000000003) x0 #x0000000000000003) (ite (bvult x0 x0) #x0000000000000004 x0)) (bvsub (concat ((_ extract 63 32) x0) ((_ extract 31 0) #x0000000000000001)) (bvlshr x0 x1))) t0) (= ok (select vb #x00000044)) (= y1 t1) (= t6 t11) (= t9 #x0000004200000000) (= rd (select mb x0)) (= mb (store ma t8 x1)) (= y0 t6) (= lv (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000042 true)) (= vb (store (store va ((_ extract 63 32) t3) false) #x00000044 true)) (= t1 (bvmul x1 x1)) (= (bvshl ((_ zero_extend 32) ((_ extract 31 0) t0)) #x0000004200000000) t3) (= t10 (bvlshr (ite (bvslt t5 t2) t4 t2) (bvadd x1 t2))) (= t8 t0) (= t5 (bvmul (bvshl t3 t2) (bvurem x0 t3))) (= t2 (bvlshr t1 t1)) (= t6 x1) (= (bvshl (concat ((_ extract 63 32) (bvneg t3)) ((_ extract 31 0) t0)) (ite (bvslt (bvmul t0 t4) (concat ((_ extract 63 32) #x0000000000000063) ((_ extract 31 0) #x00000000000000ff))) ((_ zero_extend 32) ((_ extract 31 0) #x00000000000000ff)) (concat ((_ extract 63 32) #x0000000000000063) ((_ extract 31 0) #x00000000000000ff)))) t7) (= t4 t0) ok) (p1 y0 y1 vb mb))))
(assert (forall ((x0 (_ BitVec 64)) (x1 (_ BitVec 64)) (y0 (_ BitVec 64)) (y1 (_ BitVec 64)) (t0 (_ BitVec 64)) (t1 (_ BitVec 64)) (t2 (_ BitVec 64)) (t3 (_ BitVec 64)) (t4 (_ BitVec 64)) (t5 (_ BitVec 64)) (t6 (_ BitVec 64)) (t7 (_ BitVec 64)) (t8 (_ BitVec 64)) (t9 (_ BitVec 64)) (t10 (_ BitVec 64)) (t11 (_ BitVec 64)) (va (Array (_ BitVec 32) Bool)) (vb (Array (_ BitVec 32) Bool)) (lv (Array (_ BitVec 32) Bool)) (ma (Array (_ BitVec 64) (_ BitVec 64))) (mb (Array (_ BitVec 64) (_ BitVec 64))) (rd (_ BitVec 64)) (ok Bool)) (=> (and (p1 x0 x1 va ma) (= t6 (bvand t3 ((_ zero_extend 32) ((_ extract 31 0) #x0000000000000001)))) (= t2 (ite (bvslt (bvashr t0 #xb1ae512acfe697b6) (bvurem t0 x0)) t1 (bvurem t0 x0))) (= rd (select mb t2)) (= y1 t0) (= t10 t7) (= x0 t0) (= t3 t0) (= t8 (bvadd ((_ zero_extend 32) ((_ extract 31 0) t1)) (bvor t0 #x0000000000000007))) (= t4 (bvlshr (bvneg (bvashr t0 t0)) x1)) (= ok (select vb #x00000044)) (= lv (store ((as const (Array (_ BitVec 32) Bool)) true) #x0aac1493 true)) (= y0 t2) (= t5 (bvudiv t3 #x0000000000000000)) (= vb (store (store va ((_ extract 63 32) t1) false) #x00000044 true)) (= t9 x1) (= t11 (bvlshr t6 (bvand x1 t1))) (= t3 t7) (= mb (store ma t10 x0)) (= t1 (bvsub (bvxor x0 t0) x1)) ok) (p2 y0 y1 vb mb))))
(assert (forall ((x0 (_ BitVec 64)) (x1 (_ BitVec 64)) (va (Array (_ BitVec 32) Bool)) (ma (Array (_ BitVec 64) (_ BitVec 64)))) (=> (and (p1 x0 x1 va ma) (not (= (select va #x00000000) false))) false)))
(assert (forall ((x0 (_ BitVec 64)) (x1 (_ BitVec 64)) (va (Array (_ BitVec 32) Bool)) (ma (Array (_ BitVec 64) (_ BitVec 64)))) (=> (and (p2 x0 x1 va ma) (not (= (select va #x00000042) true))) false)))
(check-sat)
"#;

/// The second error rule asserts allocation 66 live after the last step.
const LIVE_66: &str = "(not (= (select va #x00000042) true))";
const DEAD_66: &str = "(not (= (select va #x00000042) false))";

fn solve(source: &str, release_budget: Duration) -> VerifiedChcResult {
    let problem = ChcParser::parse(source).unwrap_or_else(|err| panic!("fixture parses: {err}"));
    let budget = if cfg!(debug_assertions) {
        release_budget * 4
    } else {
        release_budget
    };
    AdaptivePortfolio::new(problem, AdaptiveConfig::default().with_time_budget(budget)).solve()
}

#[test]
#[timeout(120_000)]
fn straight_line_validity_array_query_is_safe() {
    let result = solve(STRAIGHT_LINE, Duration::from_secs(5));
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "both error rules are unreachable (z3: sat, an interpretation exists); got {result:?}"
    );
}

/// Negative twin: asserting allocation 66 dead after the last step is
/// violated, and the answer is a validated counterexample.
#[test]
#[timeout(120_000)]
fn straight_line_validity_array_query_asserting_dead_is_unsafe() {
    assert_eq!(STRAIGHT_LINE.matches(LIVE_66).count(), 1);
    let unsafe_twin = STRAIGHT_LINE.replace(LIVE_66, DEAD_66);
    let result = solve(&unsafe_twin, Duration::from_secs(5));
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "allocation 66 is live after the last step (z3: unsat, no interpretation); got {result:?}"
    );
}
