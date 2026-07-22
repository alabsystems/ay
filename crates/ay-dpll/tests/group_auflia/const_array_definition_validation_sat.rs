// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Definitional const-array equality must stay SAT-certifiable
//! (#qf-ax-swap-false-sat completeness residue).
//!
//! `(= m (const-array d))` with `m` otherwise unconstrained is the shape
//! deductive-checks emits for every `Map::empty()` / `Set::empty()` ghost-collection
//! constructor. The lazy ArraySolver never materializes an `array_model`
//! entry for `m` (no select touches it), so after the #qf-ax-swap-false-sat
//! removal of the circular SAT-model fallback, `evaluate_array_equality`
//! returned `Unknown` and the unconditional model gate downgraded a
//! trivially-SAT query to `unknown` — flipping downstream counterexample
//! detection (deductive-checks set_and_map: expected Counterexample, got Unknown).
//!
//! Fixed by resolving array variables through their definitional equalities
//! (`compare_array_var_definitions`) in the POSITIVE evaluation direction —
//! EQUAL verdict only — with the same Unknown-component abort as
//! `normalize_array_to_stores`, and by scanning the active
//! `check-sat-assuming` assumptions (where `produce-unsat-cores` redirects
//! named assertions) in addition to `ctx.assertions`.
//!
//! These pins are completeness fences: `unknown` here is the regression.
//! The negated-equality soundness fences live in `qf_ax_swap_np_soundness`.

use anyhow::Result;

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// Bare definitional equality: no cores, no names.
const CONST_ARRAY_DEF_PLAIN: &str = r#"
(set-logic ALL)
(declare-const dom (Array (_ BitVec 32) Bool))
(assert (= dom ((as const (Array (_ BitVec 32) Bool)) false)))
(check-sat)
"#;

/// The deductive-checks shape: `produce-unsat-cores` + a named assertion redirects
/// the definition through `check_sat_assuming` as an ASSUMPTION, so the
/// definitional scan must look beyond `ctx.assertions`.
const CONST_ARRAY_DEF_NAMED_CORES: &str = r#"
(set-option :produce-unsat-cores true)
(set-logic ALL)
(declare-const dom (Array (_ BitVec 32) Bool))
(assert (! (= dom ((as const (Array (_ BitVec 32) Bool)) false)) :named dn2))
(check-sat)
"#;

#[test]
#[ntest::timeout(60_000)]
fn test_const_array_definitional_equality_is_sat() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(CONST_ARRAY_DEF_PLAIN, 30)?;
    assert_eq!(
        outcome,
        SolverOutcome::Sat,
        "COMPLETENESS REGRESSION: trivially-SAT `(= m (const-array d))` \
         definitional equality no longer SAT-certifiable"
    );
    Ok(())
}

#[test]
#[ntest::timeout(60_000)]
fn test_const_array_definitional_equality_named_cores_is_sat() -> Result<()> {
    let outcome = run_executor_smt_with_timeout(CONST_ARRAY_DEF_NAMED_CORES, 30)?;
    assert_eq!(
        outcome,
        SolverOutcome::Sat,
        "COMPLETENESS REGRESSION: named+produce-unsat-cores definitional \
         const-array equality no longer SAT-certifiable (assumption-redirect \
         path; deductive-checks Map/Set empty() shape)"
    );
    Ok(())
}
