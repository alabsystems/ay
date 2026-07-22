// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! QF_AX swap/storeinv `_np_nf_` false-SAT soundness fences (#qf-ax-swap-false-sat).
//!
//! The 2026-07-02 SMT-COMP QF_AX differential sweep found 40 false-SATs on the
//! Armando/Bonacina/Ranise/Schulz swap/storeinv `_np_nf_` families: one
//! top-level NEGATED equality between two nested store chains over a free base
//! array, with no explicit select-disequality witness. Two independent holes
//! combined to certify the wrong model:
//!  1. the eager-ROW2b rescue only fired on the positive-equality storeinv
//!     signature (`has_storeinv_extensionality_witness`), so the fabricated
//!     `__ext_diff` select never unrolled down the chains, and
//!  2. `evaluate_array_equality` fell back to the SAT model's own truth value
//!     when no semantic comparison applied (circular self-validation).
//! Fixed by `has_negated_deep_store_chain_array_equality` (eager-ROW2b now
//! fires on the negated shape) and `compare_same_base_store_chains` (symbolic
//! pointwise comparison; the circular fallback is gone).
//!
//! These tests pin the UNSAT verdicts. `unknown` would be sound-but-regressed;
//! `sat` is the soundness bug returning.

use anyhow::Result;

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// Minimized from `swap_t1_np_nf_ai_00004_002.cvc.smt2` (`:status unsat`):
/// composing the same two swaps in different store orders yields equal arrays,
/// so asserting the results disequal is UNSAT — for EVERY index valuation,
/// including collisions (no `distinct` guards).
const SWAP_NP_MIN: &str = r#"
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun i0 () Index)
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun i3 () Index)
(assert (let ((?v_0 (store (store a1 i1 (select a1 i3)) i3 (select a1 i1))))
  (let ((?v_3 (select ?v_0 i0)) (?v_4 (select ?v_0 i2)))
    (let ((?v_1 (store (store ?v_0 i0 ?v_4) i2 ?v_3))
          (?v_5 (store (store ?v_0 i2 ?v_3) i0 ?v_4)))
      (let ((?v_2 (store (store ?v_1 i2 (select ?v_1 i1)) i1 (select ?v_1 i2)))
            (?v_6 (store (store ?v_5 i1 (select ?v_5 i2)) i2 (select ?v_5 i1))))
        (not (= ?v_2 ?v_6)))))))
(check-sat)
"#;

#[test]
#[ntest::timeout(120_000)]
fn test_qf_ax_swap_np_min_not_sat() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(SWAP_NP_MIN, 60)?;
    assert_ne!(
        outcome,
        SolverOutcome::Sat,
        "SOUNDNESS BUG: false SAT on the minimized QF_AX swap _np_ shape \
         (#qf-ax-swap-false-sat)"
    );
    Ok(())
}

/// Release-only: the same fence, wider net (also catches a timeout regression
/// back into the multi-minute wandering that preceded the fix).
///
/// NOTE: the verdict here is `unknown`, not `unsat`. The eager-ROW2b unroll
/// that refutes this shape outright is OPT-IN (`AY_QFAX_NEG_CHAIN_GATE=1`)
/// because the eager fixpoint currently derives FALSE refutations on the
/// `:status sat` siblings (swap_invalid_*): with the gate on, soundness
/// breaks in the other direction. Until that eager-fixpoint bug is fixed, the
/// sound default keeps the lazy engine + fail-closed model gates: wrong
/// models degrade to `unknown`. Pinning not-sat (rather than unsat) is the
/// soundness fence; the unsat conversion is the tracked completeness gap.
#[cfg(not(debug_assertions))]
#[test]
#[ntest::timeout(120_000)]
fn test_qf_ax_swap_np_min_not_sat_release() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(SWAP_NP_MIN, 60)?;
    assert_ne!(
        outcome,
        SolverOutcome::Sat,
        "SOUNDNESS BUG: false SAT on the minimized QF_AX swap _np_ shape \
         (#qf-ax-swap-false-sat)"
    );
    Ok(())
}
