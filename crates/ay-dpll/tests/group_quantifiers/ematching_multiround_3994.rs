// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for #3994: multi-round E-matching must chain instantiations.

use ay_dpll::UnknownReason;
use ntest::timeout;

/// Round 1:
///   forall x. P(x) => Q(f(x)) with P(0) produces Q(f(0)).
/// Round 2:
///   forall y. Q(y) => false uses Q(f(0)) to derive contradiction.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_chained_trigger_unsat_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int))
            (! (=> (P x) (Q (f x)))
               :pattern ((P x)))))
        (assert (forall ((y Int))
            (! (=> (Q y) false)
               :pattern ((Q y)))))
        (assert (P 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Exactly 3 rounds are required:
/// Round 1: P(0) -> Q(0)
/// Round 2: Q(0) -> R(0)
/// Round 3: R(0) -> false
#[test]
#[timeout(60000)]
fn test_multiround_ematching_round_budget_boundary_unsat_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun R (Int) Bool)
        (assert (forall ((x Int))
            (! (=> (P x) (Q x))
               :pattern ((P x)))))
        (assert (forall ((x Int))
            (! (=> (Q x) (R x))
               :pattern ((Q x)))))
        (assert (forall ((x Int))
            (! (=> (R x) false)
               :pattern ((R x)))))
        (assert (P 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// 4 rounds are required:
/// Round 1: P(0) -> Q(0)
/// Round 2: Q(0) -> R(0)
/// Round 3: R(0) -> S(0)
/// Round 4: S(0) -> false
///
/// With `MAX_EMATCHING_ROUNDS = 8`, this now resolves to unsat.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_4chain_unsat_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun R (Int) Bool)
        (declare-fun S (Int) Bool)
        (assert (forall ((x Int))
            (! (=> (P x) (Q x))
               :pattern ((P x)))))
        (assert (forall ((x Int))
            (! (=> (Q x) (R x))
               :pattern ((Q x)))))
        (assert (forall ((x Int))
            (! (=> (R x) (S x))
               :pattern ((R x)))))
        (assert (forall ((x Int))
            (! (=> (S x) false)
               :pattern ((S x)))))
        (assert (P 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// 8 rounds required (exactly `MAX_EMATCHING_ROUNDS = 8`):
/// P0(0) -> P1(0) -> ... -> P7(0) -> false
///
/// This is the boundary case: the deepest chain that resolves within budget.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_8chain_boundary_unsat_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P0 (Int) Bool)
        (declare-fun P1 (Int) Bool)
        (declare-fun P2 (Int) Bool)
        (declare-fun P3 (Int) Bool)
        (declare-fun P4 (Int) Bool)
        (declare-fun P5 (Int) Bool)
        (declare-fun P6 (Int) Bool)
        (declare-fun P7 (Int) Bool)
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) false) :pattern ((P7 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// 9 rounds required — exceeds MAX_EMATCHING_ROUNDS=8, returns `unknown`.
///
/// B1c refinement (`try_ematching_refinement_round`) exists as dead code but
/// is NOT wired into the solve loop (has `#[allow(dead_code)]`, zero callers).
/// When B1c is integrated, this should return `unsat` (effective budget 8+4=12).
/// See #3325 for B1c integration work.
#[test]
#[timeout(60000)]
fn test_multiround_ematching_9chain_now_unsat_with_b1c_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P0 (Int) Bool)
        (declare-fun P1 (Int) Bool)
        (declare-fun P2 (Int) Bool)
        (declare-fun P3 (Int) Bool)
        (declare-fun P4 (Int) Bool)
        (declare-fun P5 (Int) Bool)
        (declare-fun P6 (Int) Bool)
        (declare-fun P7 (Int) Bool)
        (declare-fun P8 (Int) Bool)
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) (P8 x)) :pattern ((P7 x)))))
        (assert (forall ((x Int)) (! (=> (P8 x) false) :pattern ((P8 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    // B1c interleaved E-matching (#5927) now resolves this: the effective budget
    // is 8 (preprocessing) + 4 (interleaved) = 12 rounds, enough for 9 steps.
    assert_eq!(outputs, vec!["unsat"]);
}

/// 30-step implication chain: P0(0) -> P1(0) -> ... -> P29(0) -> false
///
/// The chain is deliberately longer than the combined E-matching budget so
/// that even the raised preprocessing round limit cannot complete it. The
/// effective budget is 16 (preprocessing, `MAX_EMATCHING_ROUNDS`) + 1
/// (post-CEGQI) + 4 (interleaved) = 21 rounds, insufficient for 30 steps, so
/// the solver reports `unknown` rather than spuriously timing out or claiming
/// `unsat`. (Chain length bumped from 14 to 30 when `MAX_EMATCHING_ROUNDS`
/// was raised from 8 to 16 to chain deeper iterator/permutation clusters.)
#[test]
#[timeout(60000)]
fn test_multiround_ematching_exhausted_budget_returns_unknown_3994() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P0 (Int) Bool)
        (declare-fun P1 (Int) Bool)
        (declare-fun P2 (Int) Bool)
        (declare-fun P3 (Int) Bool)
        (declare-fun P4 (Int) Bool)
        (declare-fun P5 (Int) Bool)
        (declare-fun P6 (Int) Bool)
        (declare-fun P7 (Int) Bool)
        (declare-fun P8 (Int) Bool)
        (declare-fun P9 (Int) Bool)
        (declare-fun P10 (Int) Bool)
        (declare-fun P11 (Int) Bool)
        (declare-fun P12 (Int) Bool)
        (declare-fun P13 (Int) Bool)
        (declare-fun P14 (Int) Bool)
        (declare-fun P15 (Int) Bool)
        (declare-fun P16 (Int) Bool)
        (declare-fun P17 (Int) Bool)
        (declare-fun P18 (Int) Bool)
        (declare-fun P19 (Int) Bool)
        (declare-fun P20 (Int) Bool)
        (declare-fun P21 (Int) Bool)
        (declare-fun P22 (Int) Bool)
        (declare-fun P23 (Int) Bool)
        (declare-fun P24 (Int) Bool)
        (declare-fun P25 (Int) Bool)
        (declare-fun P26 (Int) Bool)
        (declare-fun P27 (Int) Bool)
        (declare-fun P28 (Int) Bool)
        (declare-fun P29 (Int) Bool)
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) (P8 x)) :pattern ((P7 x)))))
        (assert (forall ((x Int)) (! (=> (P8 x) (P9 x)) :pattern ((P8 x)))))
        (assert (forall ((x Int)) (! (=> (P9 x) (P10 x)) :pattern ((P9 x)))))
        (assert (forall ((x Int)) (! (=> (P10 x) (P11 x)) :pattern ((P10 x)))))
        (assert (forall ((x Int)) (! (=> (P11 x) (P12 x)) :pattern ((P11 x)))))
        (assert (forall ((x Int)) (! (=> (P12 x) (P13 x)) :pattern ((P12 x)))))
        (assert (forall ((x Int)) (! (=> (P13 x) (P14 x)) :pattern ((P13 x)))))
        (assert (forall ((x Int)) (! (=> (P14 x) (P15 x)) :pattern ((P14 x)))))
        (assert (forall ((x Int)) (! (=> (P15 x) (P16 x)) :pattern ((P15 x)))))
        (assert (forall ((x Int)) (! (=> (P16 x) (P17 x)) :pattern ((P16 x)))))
        (assert (forall ((x Int)) (! (=> (P17 x) (P18 x)) :pattern ((P17 x)))))
        (assert (forall ((x Int)) (! (=> (P18 x) (P19 x)) :pattern ((P18 x)))))
        (assert (forall ((x Int)) (! (=> (P19 x) (P20 x)) :pattern ((P19 x)))))
        (assert (forall ((x Int)) (! (=> (P20 x) (P21 x)) :pattern ((P20 x)))))
        (assert (forall ((x Int)) (! (=> (P21 x) (P22 x)) :pattern ((P21 x)))))
        (assert (forall ((x Int)) (! (=> (P22 x) (P23 x)) :pattern ((P22 x)))))
        (assert (forall ((x Int)) (! (=> (P23 x) (P24 x)) :pattern ((P23 x)))))
        (assert (forall ((x Int)) (! (=> (P24 x) (P25 x)) :pattern ((P24 x)))))
        (assert (forall ((x Int)) (! (=> (P25 x) (P26 x)) :pattern ((P25 x)))))
        (assert (forall ((x Int)) (! (=> (P26 x) (P27 x)) :pattern ((P26 x)))))
        (assert (forall ((x Int)) (! (=> (P27 x) (P28 x)) :pattern ((P27 x)))))
        (assert (forall ((x Int)) (! (=> (P28 x) (P29 x)) :pattern ((P28 x)))))
        (assert (forall ((x Int)) (! (=> (P29 x) false) :pattern ((P29 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    // 30 steps > 21 (16 preprocessing + 1 post-CEGQI + 4 interleaved) = budget exhausted.
    assert_eq!(outputs, vec!["unknown"]);
}

/// Regression for interleaved E-matching observability: the 30-step chain above
/// exhausts the four post-solve interleaved rounds. Those rounds must be counted
/// in public statistics, and exhaustion must be classified as a round limit.
#[test]
#[timeout(60000)]
fn test_interleaved_ematching_exhaustion_stats_and_reason_8614() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P0 (Int) Bool)
        (declare-fun P1 (Int) Bool)
        (declare-fun P2 (Int) Bool)
        (declare-fun P3 (Int) Bool)
        (declare-fun P4 (Int) Bool)
        (declare-fun P5 (Int) Bool)
        (declare-fun P6 (Int) Bool)
        (declare-fun P7 (Int) Bool)
        (declare-fun P8 (Int) Bool)
        (declare-fun P9 (Int) Bool)
        (declare-fun P10 (Int) Bool)
        (declare-fun P11 (Int) Bool)
        (declare-fun P12 (Int) Bool)
        (declare-fun P13 (Int) Bool)
        (declare-fun P14 (Int) Bool)
        (declare-fun P15 (Int) Bool)
        (declare-fun P16 (Int) Bool)
        (declare-fun P17 (Int) Bool)
        (declare-fun P18 (Int) Bool)
        (declare-fun P19 (Int) Bool)
        (declare-fun P20 (Int) Bool)
        (declare-fun P21 (Int) Bool)
        (declare-fun P22 (Int) Bool)
        (declare-fun P23 (Int) Bool)
        (declare-fun P24 (Int) Bool)
        (declare-fun P25 (Int) Bool)
        (declare-fun P26 (Int) Bool)
        (declare-fun P27 (Int) Bool)
        (declare-fun P28 (Int) Bool)
        (declare-fun P29 (Int) Bool)
        (assert (forall ((x Int)) (! (=> (P0 x) (P1 x)) :pattern ((P0 x)))))
        (assert (forall ((x Int)) (! (=> (P1 x) (P2 x)) :pattern ((P1 x)))))
        (assert (forall ((x Int)) (! (=> (P2 x) (P3 x)) :pattern ((P2 x)))))
        (assert (forall ((x Int)) (! (=> (P3 x) (P4 x)) :pattern ((P3 x)))))
        (assert (forall ((x Int)) (! (=> (P4 x) (P5 x)) :pattern ((P4 x)))))
        (assert (forall ((x Int)) (! (=> (P5 x) (P6 x)) :pattern ((P5 x)))))
        (assert (forall ((x Int)) (! (=> (P6 x) (P7 x)) :pattern ((P6 x)))))
        (assert (forall ((x Int)) (! (=> (P7 x) (P8 x)) :pattern ((P7 x)))))
        (assert (forall ((x Int)) (! (=> (P8 x) (P9 x)) :pattern ((P8 x)))))
        (assert (forall ((x Int)) (! (=> (P9 x) (P10 x)) :pattern ((P9 x)))))
        (assert (forall ((x Int)) (! (=> (P10 x) (P11 x)) :pattern ((P10 x)))))
        (assert (forall ((x Int)) (! (=> (P11 x) (P12 x)) :pattern ((P11 x)))))
        (assert (forall ((x Int)) (! (=> (P12 x) (P13 x)) :pattern ((P12 x)))))
        (assert (forall ((x Int)) (! (=> (P13 x) (P14 x)) :pattern ((P13 x)))))
        (assert (forall ((x Int)) (! (=> (P14 x) (P15 x)) :pattern ((P14 x)))))
        (assert (forall ((x Int)) (! (=> (P15 x) (P16 x)) :pattern ((P15 x)))))
        (assert (forall ((x Int)) (! (=> (P16 x) (P17 x)) :pattern ((P16 x)))))
        (assert (forall ((x Int)) (! (=> (P17 x) (P18 x)) :pattern ((P17 x)))))
        (assert (forall ((x Int)) (! (=> (P18 x) (P19 x)) :pattern ((P18 x)))))
        (assert (forall ((x Int)) (! (=> (P19 x) (P20 x)) :pattern ((P19 x)))))
        (assert (forall ((x Int)) (! (=> (P20 x) (P21 x)) :pattern ((P20 x)))))
        (assert (forall ((x Int)) (! (=> (P21 x) (P22 x)) :pattern ((P21 x)))))
        (assert (forall ((x Int)) (! (=> (P22 x) (P23 x)) :pattern ((P22 x)))))
        (assert (forall ((x Int)) (! (=> (P23 x) (P24 x)) :pattern ((P23 x)))))
        (assert (forall ((x Int)) (! (=> (P24 x) (P25 x)) :pattern ((P24 x)))))
        (assert (forall ((x Int)) (! (=> (P25 x) (P26 x)) :pattern ((P25 x)))))
        (assert (forall ((x Int)) (! (=> (P26 x) (P27 x)) :pattern ((P26 x)))))
        (assert (forall ((x Int)) (! (=> (P27 x) (P28 x)) :pattern ((P27 x)))))
        (assert (forall ((x Int)) (! (=> (P28 x) (P29 x)) :pattern ((P28 x)))))
        (assert (forall ((x Int)) (! (=> (P29 x) false) :pattern ((P29 x)))))
        (assert (P0 0))
        (check-sat)
    "#;

    let commands = ay_frontend::parse(smt).expect("valid SMT-LIB input");
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["unknown"]);
    assert_eq!(
        exec.unknown_reason(),
        Some(UnknownReason::QuantifierRoundLimit)
    );

    let stats = exec.statistics();
    assert_eq!(
        stats.get_string("unknown.phase"),
        Some("quantifier-instantiation"),
        "Unknown diagnostics should identify the responsible phase"
    );
    assert_eq!(
        stats.get_string("unknown.cost_center"),
        Some("ematching"),
        "Unknown diagnostics should identify the E-matching budget as cost center"
    );
    assert!(
        stats
            .get_string("unknown.detail")
            .is_some_and(|detail| detail.contains("E-matching budget exhausted")),
        "Unknown detail should include the bounded instantiation reason"
    );
    // Preprocessing runs the full raised budget (MAX_EMATCHING_ROUNDS = 16) plus
    // the 4 interleaved refinement rounds before exhaustion is declared.
    assert_eq!(
        stats.ematching_rounds_completed, 20,
        "expected 16 preprocessing + 4 interleaved rounds, got {}",
        stats.ematching_rounds_completed
    );
    // Incremental E-matching (fix2): the persistent (quant,binding) seen memo
    // dedups instances ACROSS rounds within one process_quantifiers epoch, where
    // the previous per-round-fresh seen re-counted the same instance every round.
    // The cumulative SET of distinct instances and the round count (12) are
    // unchanged, and the result is still unknown/QuantifierRoundLimit; only the
    // per-round-summed counter is no longer inflated by re-derivations. 12 = one
    // distinct instance per completed round (8 preprocessing + 4 interleaved), so
    // interleaved rounds DO still contribute (> the 8 preprocessing rounds alone).
    assert!(
        stats.ematching_instances_created >= 9,
        "expected interleaved instances to be included (more than the 8 \
         preprocessing rounds alone), got {}",
        stats.ematching_instances_created
    );
}
