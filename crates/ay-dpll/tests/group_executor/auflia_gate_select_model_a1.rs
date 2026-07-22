// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the #A1 AUFLIA model-construction fix (#8373 class).
//!
//! Pattern: Bool variables defined by gate equalities over array-select
//! terms (`(= I (<= F (select Q G)))`) where preprocessing substitutes the
//! definitional equalities away. The solved constraints mention the
//! POST-substitution select form (`(select Q (+ B1 (* R 4)))`) while the
//! original assertions mention the PRE-substitution form (`(select Q G)`).
//! Both reach LIA as independent opaque variables; before the fix the final
//! model carried inconsistent values for the two forms of the same array
//! read, model completion replayed the stale value, validation flagged the
//! solver's own model (`(not I) evaluates to false`) and the answer degraded
//! to Unknown (#8373). The fix reconciles the LIA model (composite index
//! recomputation + opaque-select read congruence) BEFORE array-model
//! extraction, so the store-row-congruence and multiple-gates members now
//! answer `sat`. The original chain repro (formerly a red-by-ignore pin) is
//! covered since the 2026-07-19 follow-up: EUF-view read grouping, witness
//! non-authority, and post-class-merge re-reconciliation — see the chain
//! member's doc comment for the full mechanism.
//!
//! Follow-up (post-0bd4fda960 audit hardening): the same class regressed
//! through the cross-theory UF-table normalization (congruent duplicated
//! `store` rows conflict-marked -> whole model discarded -> `Sat` fail-closed
//! to Unknown with "No model available") and through the class-merge pass-2
//! fresh-shift trusting a stale EUF disequality edge over a holding original
//! equality. See `combiner_models.rs`: the Array-token congruence repair and
//! the holding-equality move guard, plus the recompute/reconcile/recover
//! fixpoint in `solve_auf_lia`'s model-extraction closure.

use ntest::timeout;

/// The original llreve/hcai diagnosis repro (aufquery5 shape).
///
/// FIXED (2026-07-19, formerly a red-by-ignore pin): the chain shape (store
/// at composite index `B1 + 4P`, read at `B1 + 4R`, `B1 > 0`, `P != R`) is
/// z3-adjudicated SAT (`P != R` leaves `select Q G` unconstrained) but
/// answered Sat->timeout. Root cause was NOT the array conflict check
/// itself: the first (small) AUFLIA split-loop pass FOUND the sat model,
/// but read-congruence materialization kept being re-broken after the
/// class-merge repairs — (a) the pre-substitution read `(select Q G)`
/// reaches the model only as an EUF class string, so the LIA-only
/// `reconcile_lia_select_congruence` grouping never saw it; (b) the
/// class-merge reunify/fresh-shift passes run AFTER the reconciliation
/// fixpoint and moved reconciled select values again; (c) a stale internal
/// extensionality-witness read (`select Q __ay_arr2lia_wit_*`) vetoed the
/// reconciliation as a fake solved-form authority. The committed reads then
/// disagreed on one `(Q, idx)` cell, the materialization pass failed closed
/// (`Sat` with no model -> unknown), and the 16x axiom-expanded re-solve
/// diverged in `check_store_permutation_select_conflicts`'s per-pair
/// explanation BFS over the blown-up equality graph. Fixed by: EUF-view
/// select grouping + witness-read non-authority in
/// `reconcile_lia_select_congruence`, re-running the recovery fixpoint
/// after the class-merge passes (`extract_all_models_auflia_with_lia_fixup`),
/// and window-memoizing the final-check explanation queries (frozen-graph
/// `eq_paths_cache` + asserted-path predecessor forests). All candidate-
/// model repairs; the strict + independent gates still decide acceptance
/// (this run: model-check-gate confirmed-sat, 0.6s).
#[test]
#[timeout(30_000)]
fn test_auflia_bool_gate_over_select_chain_sat_a1() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-const D (Array Int Int))
(declare-const Q (Array Int Int))
(declare-const E Int)
(declare-const F Int)
(declare-const G Int)
(declare-const H Int)
(declare-const B1 Int)
(declare-const P Int)
(declare-const R Int)
(declare-const I Bool)
(declare-const B Bool)
(assert (= Q (store D E F)))
(assert (= E (+ B1 (* 4 P))))
(assert (= G (+ B1 (* 4 R))))
(assert (= H (select Q G)))
(assert (not (<= B1 0)))
(assert (= B (= P 0)))
(assert (= I (<= F H)))
(assert (not (= P R)))
(assert (not I))
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "bool gate over substituted select chain must be SAT (was unknown via #8373 degrade)"
    );
}

/// Regression for the congruent-`store`-rows model discard (#A1 follow-up).
///
/// AUFLIA preprocessing duplicates `(store A x v)` in pre- and post-
/// substitution form; under the FINAL arithmetic assignment the two rows of
/// the `store` UF table carry identical argument keys but distinct opaque
/// Array-sorted e-class tokens. The 0bd4fda960 cross-theory table
/// normalization treated Array results as not-directly-repairable, marked the
/// table conflicted, and the outer witness sweep
/// (`complete_unconstrained_constants_for_output`) then DISCARDED the whole
/// candidate model — so the emission funnel saw `Sat` with no model and
/// fail-closed a genuine SAT to `unknown` ("No model available").
///
/// The repair unifies the congruent rows' Array tokens (guarded on no hard
/// pins and no known-disequal pair), so one array interpretation is extracted
/// and the strict + independent gates can CONFIRM the model. The `get-value`
/// exercises the printer path over the unified interpretation end-to-end.
#[test]
#[timeout(30_000)]
fn test_auflia_congruent_store_rows_model_survives_a1() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const A1 (Array Int Int))
(declare-const base Int)
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)
(declare-const y Int)
(declare-const v Int)
(declare-const gate1 Bool)
(declare-const gate2 Bool)
(assert (= A1 (store A x v)))
(assert (= x (+ base (* 8 i))))
(assert (= y (+ base (* 8 j))))
(assert (= gate1 (<= v (select A1 y))))
(assert (= gate2 (= i 0)))
(assert (not (<= base 0)))
(assert (not (= i j)))
(assert (not gate1))
(assert gate2)
(check-sat)
(get-value (v (select A1 y) (select A1 x)))
"#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        !outputs.is_empty() && outputs[0] == "sat",
        "congruent duplicated store rows must not discard the model: {outputs:?}"
    );
    assert!(
        outputs.len() >= 2 && outputs[1].contains("select"),
        "sat must come with a printable model (get-value): {outputs:?}"
    );
}

/// Same class with two gates and a select-equality gate.
#[test]
#[timeout(30_000)]
fn test_auflia_multiple_gates_over_select_sat_a1() {
    let smt = r#"
(set-logic QF_AUFLIA)
(declare-const A (Array Int Int))
(declare-const A1 (Array Int Int))
(declare-const base Int)
(declare-const i Int)
(declare-const j Int)
(declare-const x Int)
(declare-const y Int)
(declare-const v Int)
(declare-const gate1 Bool)
(declare-const gate2 Bool)
(declare-const gate3 Bool)
(assert (= A1 (store A x v)))
(assert (= x (+ base (* 8 i))))
(assert (= y (+ base (* 8 j))))
(assert (= gate1 (<= v (select A1 y))))
(assert (= gate2 (= i 0)))
(assert (= gate3 (= (select A1 y) (select A y))))
(assert (not (<= base 0)))
(assert (not (= i j)))
(assert (not gate1))
(assert gate2)
(check-sat)
"#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "multiple bool gates over substituted selects must be SAT"
    );
}
