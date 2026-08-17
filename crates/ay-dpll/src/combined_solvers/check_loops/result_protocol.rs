// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sub-solver result forwarding, triage, and terminal consistency checks.

use ay_core::{TheoryLit, TheoryResult, TheorySolver};

/// Forward a non-Sat sub-solver result, exhaustively matching all variants.
///
/// Returns `Some(result)` for any variant other than `Sat`, ensuring that
/// new `TheoryResult` variants added in the future cause a compile error
/// instead of being silently treated as `Sat`.
pub(in crate::combined_solvers) fn forward_non_sat(result: TheoryResult) -> Option<TheoryResult> {
    match result {
        TheoryResult::Sat => None,
        TheoryResult::Unsat(reasons) => {
            // A theory claiming UNSAT must provide at least one reason term;
            // an empty reason vector cannot form a valid conflict clause.
            // Downgrade to Unknown in release to prevent false-UNSAT from an
            // empty/tautological conflict clause. (#6849)
            debug_assert!(
                !reasons.is_empty(),
                "BUG: sub-theory returned Unsat with empty reasons"
            );
            if reasons.is_empty() {
                Some(TheoryResult::Unknown)
            } else {
                Some(TheoryResult::Unsat(reasons))
            }
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            debug_assert!(
                !conflict.literals.is_empty(),
                "BUG: sub-theory returned UnsatWithFarkas with empty literals"
            );
            if conflict.literals.is_empty() {
                Some(TheoryResult::Unknown)
            } else {
                Some(TheoryResult::UnsatWithFarkas(conflict))
            }
        }
        TheoryResult::Unknown => Some(TheoryResult::Unknown),
        TheoryResult::NeedSplit(split) => Some(TheoryResult::NeedSplit(split)),
        TheoryResult::NeedDisequalitySplit(split) => {
            Some(TheoryResult::NeedDisequalitySplit(split))
        }
        TheoryResult::NeedExpressionSplit(split) => Some(TheoryResult::NeedExpressionSplit(split)),
        // #8707 / #8765: batch variant of NeedExpressionSplit emitted by LRA's
        // buffered expression-split path. Forward through the combined-solver
        // plumbing just like the singleton variant.
        TheoryResult::NeedExpressionSplits(splits) => {
            Some(TheoryResult::NeedExpressionSplits(splits))
        }
        TheoryResult::NeedStringLemma(lemma) => Some(TheoryResult::NeedStringLemma(lemma)),
        TheoryResult::NeedLemmas(lemmas) => Some(TheoryResult::NeedLemmas(lemmas)),
        TheoryResult::NeedModelEquality(eq) => Some(TheoryResult::NeedModelEquality(eq)),
        TheoryResult::NeedModelEqualities(eqs) => Some(TheoryResult::NeedModelEqualities(eqs)),
        // All current TheoryResult variants handled above (#4906, #6149, #8707).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}

/// Narrow a full sub-solver result to what is safe and cheap during BCP-time
/// eager callbacks.
///
/// Combined solvers use this to defer splits, lemmas, and model-equality work
/// until the final post-SAT full `check()`. Only local conflicts and Unknown
/// results propagate during BCP.
pub(in crate::combined_solvers) fn defer_non_local_result(result: TheoryResult) -> TheoryResult {
    match result {
        TheoryResult::Sat => TheoryResult::Sat,
        TheoryResult::Unsat(reasons) => {
            debug_assert!(
                !reasons.is_empty(),
                "BUG: sub-theory returned Unsat with empty reasons"
            );
            TheoryResult::Unsat(reasons)
        }
        TheoryResult::UnsatWithFarkas(conflict) => {
            debug_assert!(
                !conflict.literals.is_empty(),
                "BUG: sub-theory returned UnsatWithFarkas with empty literals"
            );
            TheoryResult::UnsatWithFarkas(conflict)
        }
        TheoryResult::Unknown => TheoryResult::Unknown,
        // #6546 Packet 5: pass NeedLemmas through so the TheoryExtension
        // can inject array axioms inline during BCP instead of deferring to
        // a full SAT re-solve cycle via pending_split.
        TheoryResult::NeedLemmas(lemmas) => TheoryResult::NeedLemmas(lemmas),
        TheoryResult::NeedSplit(_)
        | TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_)
        | TheoryResult::NeedExpressionSplits(_)
        | TheoryResult::NeedStringLemma(_)
        | TheoryResult::NeedModelEquality(_)
        | TheoryResult::NeedModelEqualities(_) => TheoryResult::Sat,
        // All current TheoryResult variants handled above (#4906, #6149, #8707).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}

/// Triage a LIA check result: Unsat returns early, splits are deferred (#5081).
///
/// Returns `(deferred_split, early_return)`. If `early_return` is `Some`, the
/// caller should return it immediately. Otherwise, `deferred_split` holds a
/// split request to return at fixpoint if no new equalities are discovered.
pub(in crate::combined_solvers) fn triage_lia_result(
    result: TheoryResult,
) -> (Option<TheoryResult>, Option<TheoryResult>) {
    match result {
        TheoryResult::Sat | TheoryResult::Unknown => (None, None),
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => (None, Some(result)),
        TheoryResult::NeedSplit(_)
        | TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_)
        | TheoryResult::NeedExpressionSplits(_)
        | TheoryResult::NeedStringLemma(_)
        | TheoryResult::NeedLemmas(_)
        | TheoryResult::NeedModelEquality(_)
        | TheoryResult::NeedModelEqualities(_) => (Some(result), None),
        // All current TheoryResult variants handled above (#4906, #6149, #6303, #8707).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}

/// Triage an LRA check result with split deferral for combined solvers (#6129).
///
/// Like [`triage_lra_result`], but defers `NeedDisequalitySplit` and
/// `NeedExpressionSplit` instead of early-returning them. This allows the
/// Nelson-Oppen loop to continue through the interface bridge, which may
/// propagate equalities that resolve the disequality without needing a split.
///
/// Returns `(deferred_split, early_return)`. If `early_return` is `Some`,
/// the caller should return it immediately. Otherwise, `deferred_split` holds
/// a split request to return at fixpoint if no new equalities are discovered.
pub(in crate::combined_solvers) fn triage_lra_result_deferred(
    result: TheoryResult,
) -> (Option<TheoryResult>, Option<TheoryResult>) {
    match result {
        TheoryResult::Sat | TheoryResult::Unknown => (None, None),
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => (None, Some(result)),
        // Defer splits so the N-O interface bridge can try to resolve the
        // disequality before escalating to the outer split loop (#6129).
        // #8707 / #8765: NeedExpressionSplits (batch) follows the same deferral
        // policy as the singleton NeedExpressionSplit.
        TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_)
        | TheoryResult::NeedExpressionSplits(_) => (Some(result), None),
        TheoryResult::NeedSplit(_) => {
            unreachable!("BUG: LRA solver returned NeedSplit (should only come from LIA)");
        }
        TheoryResult::NeedStringLemma(_) => {
            unreachable!("BUG: LRA solver returned NeedStringLemma");
        }
        TheoryResult::NeedLemmas(_) => {
            unreachable!("BUG: LRA solver returned NeedLemmas");
        }
        // LRA returns NeedModelEquality/NeedModelEqualities when fixed-term
        // equalities are discovered (lib.rs:7182-7194). Defer them so the N-O
        // bridge can try to resolve them before escalating (#6812).
        TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
            (Some(result), None)
        }
        // All current TheoryResult variants handled above (#4906, #6149, #6303, #8707).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}

/// Fixpoint convergence postcondition (#4714): after the N-O loop decides Sat,
/// verify that no sub-theory has undrained equalities. A non-empty result means
/// the fixpoint check exited prematurely — equalities were discovered between
/// the last `propagate_equalities()` call and the Sat return.
///
/// This drains pending equalities, so it must only be called at the terminal
/// Sat return point (not mid-loop). Always-on: a fixpoint violation is a
/// soundness bug that must not be masked by build profile (#4998).
pub(in crate::combined_solvers) fn assert_fixpoint_convergence(
    label: &str,
    solvers: &mut [&mut dyn TheorySolver],
) {
    for solver in solvers {
        let post = solver.propagate_equalities();
        assert!(
            post.equalities.is_empty() && post.conflict.is_none(),
            "BUG: {label} fixpoint violation — sub-theory has {} undrained equalities and {} after Sat",
            post.equalities.len(),
            if post.conflict.is_some() {
                "an undrained conflict"
            } else {
                "no conflict"
            },
        );
    }
}

pub(super) fn array_equality_propagation_conflict_result(conflict: Vec<TheoryLit>) -> TheoryResult {
    if !conflict.is_empty() {
        return TheoryResult::Unsat(conflict);
    }

    // Array solver reported a conflict with zero reasons — this is a theory
    // solver bug (#4666). Return Unknown so DPLL(T) can backtrack safely,
    // matching the established combined-solver fallback (#6211, #6496).
    tracing::warn!(
        "BUG: array propagate_equalities returned conflict with 0 reasons — \
         returning Unknown instead of silently dropping"
    );
    TheoryResult::Unknown
}
