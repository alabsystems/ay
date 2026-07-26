// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_arrays::ArraySolver;
use ay_core::term::TermStore;
use ay_core::{EqualityPropagationResult, TermId, TheoryLit, TheoryResult, TheorySolver};
use ay_euf::EufSolver;
use std::collections::BTreeMap;

use self::affine::{affine_euf_equality_reasons, distinct_by_affine_offset};

mod affine;

/// Forward a non-Sat sub-solver result, exhaustively matching all variants.
///
/// Returns `Some(result)` for any variant other than `Sat`, ensuring that
/// new `TheoryResult` variants added in the future cause a compile error
/// instead of being silently treated as `Sat`.
pub(super) fn forward_non_sat(result: TheoryResult) -> Option<TheoryResult> {
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
pub(super) fn defer_non_local_result(result: TheoryResult) -> TheoryResult {
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
pub(super) fn triage_lia_result(
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
pub(super) fn triage_lra_result_deferred(
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

/// Result of draining equalities and disequalities from a theory solver (#8455).
pub(super) struct PropagationCounts {
    /// Number of equalities propagated.
    pub(super) equalities: usize,
    /// Number of disequalities propagated.
    pub(super) disequalities: usize,
}

/// Propagate discovered equalities and disequalities from `source` to `target`
/// solver (#8455).
///
/// Returns `Ok(counts)` with the number of shared equalities and disequalities,
/// or `Err(Unsat(...))` if the propagation reveals a conflict.
///
/// Both equalities and disequalities must be exchanged for Nelson-Oppen
/// completeness. Prior to #8455, the `disequalities` field of
/// `EqualityPropagationResult` was silently dropped.
#[allow(clippy::result_large_err)] // TheoryResult is inherently large; boxing adds overhead on the hot path
pub(super) fn propagate_equalities_to(
    source: &mut dyn TheorySolver,
    target: &mut dyn TheorySolver,
    debug: bool,
    label: &str,
    iteration: usize,
) -> Result<usize, TheoryResult> {
    let counts = propagate_all_to(source, target, debug, label, iteration)?;
    Ok(counts.equalities)
}

/// Full equality + disequality propagation from `source` to `target` (#8455).
///
/// Like `propagate_equalities_to` but returns both equality and disequality
/// counts so callers can include disequality flow in their fixpoint
/// convergence check.
#[allow(clippy::result_large_err)]
pub(super) fn propagate_all_to(
    source: &mut dyn TheorySolver,
    target: &mut dyn TheorySolver,
    debug: bool,
    label: &str,
    iteration: usize,
) -> Result<PropagationCounts, TheoryResult> {
    let eq_result = drain_equalities_for_propagation(source, debug, label, iteration)?;
    let eq_count = eq_result.equalities.len();
    for eq in eq_result.equalities {
        target.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
    }

    let diseq_count = eq_result.disequalities.len();
    for diseq in eq_result.disequalities {
        target.assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
    }

    Ok(PropagationCounts {
        equalities: eq_count,
        disequalities: diseq_count,
    })
}

#[allow(clippy::result_large_err)]
pub(super) fn drain_equalities_for_propagation(
    source: &mut dyn TheorySolver,
    debug: bool,
    label: &str,
    iteration: usize,
) -> Result<EqualityPropagationResult, TheoryResult> {
    let eq_result = source.propagate_equalities();
    if let Some(conflict) = eq_result.conflict {
        // Guard: empty reasons cannot form a valid conflict (#4666)
        if !conflict.is_empty() {
            return Err(TheoryResult::Unsat(conflict));
        }
        // A theory reported a conflict but with zero reasons — this is
        // a theory solver bug (#4666). Rather than crash consumers with
        // a panic, return Unknown so the DPLL(T) layer can backtrack
        // safely (#6197).
        tracing::warn!(
            "BUG: {label} propagate_equalities returned conflict with 0 reasons — \
             returning Unknown instead of crashing"
        );
        return Err(TheoryResult::Unknown);
    }
    let eq_count = eq_result.equalities.len();
    if debug && eq_count > 0 {
        safe_eprintln!(
            "[N-O {}] Iteration {}: discovered {} equalities",
            label,
            iteration,
            eq_count
        );
    }
    for eq in &eq_result.equalities {
        // Nelson-Oppen symmetry: both sides of a propagated equality must be
        // distinct terms (self-equality is trivial and wastes fixpoint iterations).
        debug_assert!(
            eq.lhs != eq.rhs,
            "BUG: {label} propagated trivial self-equality ({:?} = {:?})",
            eq.lhs,
            eq.rhs
        );
    }
    let diseq_count = eq_result.disequalities.len();
    if debug && diseq_count > 0 {
        safe_eprintln!(
            "[N-O {}] Iteration {}: discovered {} disequalities",
            label,
            iteration,
            diseq_count
        );
    }
    for diseq in &eq_result.disequalities {
        debug_assert!(
            diseq.lhs != diseq.rhs,
            "BUG: {label} propagated trivial self-disequality ({:?} != {:?})",
            diseq.lhs,
            diseq.rhs
        );
    }
    Ok(eq_result)
}

/// Fixpoint convergence postcondition (#4714): after the N-O loop decides Sat,
/// verify that no sub-theory has undrained equalities. A non-empty result means
/// the fixpoint check exited prematurely — equalities were discovered between
/// the last `propagate_equalities()` call and the Sat return.
///
/// This drains pending equalities, so it must only be called at the terminal
/// Sat return point (not mid-loop). Always-on: a fixpoint violation is a
/// soundness bug that must not be masked by build profile (#4998).
pub(super) fn assert_fixpoint_convergence(label: &str, solvers: &mut [&mut dyn TheorySolver]) {
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

/// Cached `AY_DEBUG_NELSON_OPPEN` env var (checked once per process).
pub(super) fn debug_nelson_oppen() -> bool {
    crate::theory_debug_flags::debug_nelson_oppen()
}

fn array_equality_propagation_conflict_result(conflict: Vec<TheoryLit>) -> TheoryResult {
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

/// Propagate arithmetic-derived index (dis)equalities to the array solver,
/// discover ROW1/ROW2 equalities, and forward them to EUF (#4665).
///
/// `get_value_with_reasons` evaluates an index term to an optional `(value, reasons)`
/// pair using the arithmetic solver (LIA or LRA). The reasons are `TheoryLit`s from
/// tight bounds that justify the value. When disequalities are found, the merged
/// reasons from both indices are stored in the array solver so that
/// `explain_distinct_if_provable()` can justify ROW2 conflicts (#6546).
///
/// Returns `Some(result)` if a conflict was found or new equalities were propagated
/// (caller should continue the N-O loop), or `None` if no undecided pairs exist.
///
/// `act_on_read_congruence_pairs` gates the store-carrying READ-CONGRUENCE
/// pair obligations (`UndecidedIndexPair::sels`, #seed-1213-case-187). It is
/// `true` for ground solves (the wrong-model fix those pairs exist for);
/// the executor passes `false` for (re-)solves inside the
/// quantifier-instantiation pipeline — see #read-congruence-quantified-scope
/// on `TheoryCombiner::set_read_congruence_pairs_enabled`.
pub(super) fn propagate_array_index_info<V: PartialEq>(
    terms: &TermStore,
    arrays: &mut ArraySolver<'_>,
    euf: &mut EufSolver<'_>,
    get_value_with_reasons: impl Fn(TermId) -> Option<(V, Vec<TheoryLit>)>,
    act_on_read_congruence_pairs: bool,
) -> Option<TheoryResult> {
    let undecided = arrays.undecided_index_pairs();
    let mut propagated_new = false;
    // Track pairs where the arithmetic model couldn't determine the relationship:
    // either both values are equal (trivial model) or one/both have no value
    // (e.g., Skolem functions not tracked by LIA). These need SAT-level case
    // splits via NeedModelEquality (#6282).
    let mut unresolved_pairs: Vec<(TermId, TermId)> = Vec::new();
    for pair in &undecided {
        // Array index pairs must be distinct terms — comparing a term to itself
        // is always equal and should never appear as "undecided".
        debug_assert!(
            pair.idx1 != pair.idx2,
            "BUG: undecided array index pair contains self-pair ({:?}, {:?})",
            pair.idx1,
            pair.idx2
        );
        // Value-filtered READ-CONGRUENCE pair (store-carrying problems, QF_ALIA
        // seed-1213 case 187): `sels` carries the two select terms over the
        // same array whose index pair this is. Only act when the arithmetic
        // model assigns the selects DISTINCT values — read congruence
        // (`idx1 = idx2 => sel1 = sel2`) then genuinely forces `idx1 != idx2`.
        // Pairs whose select values coincide (congruence satisfiable either
        // way) or are unknown to arithmetic are skipped, so store-heavy unsat
        // families don't multiply split-loop atoms (pointer-safe-5 livelock
        // guard); unknown-value residuals are fail-closed by the independent
        // model gate's printed-witness check.
        // #read-congruence-quantified-scope (#7956 tseitin regression): inside
        // the quantifier-instantiation pipeline these obligations are skipped
        // wholesale. Instantiated select terms routinely carry symbolic
        // offsets the arithmetic solver has no value for, so under the
        // fail-closed keep below every such pair became a model-equality
        // split over UNBOUNDED Int index terms and the ground search wandered
        // (10M+ decisions, conflict-free) instead of converging; quantified
        // SAT answers still pass full model validation plus the independent
        // model gate downstream.
        if pair.sels.is_some() && !act_on_read_congruence_pairs {
            continue;
        }
        if let Some((sel1, sel2)) = pair.sels {
            // Skip ONLY when both select values are known and EQUAL — read
            // congruence is then satisfiable regardless of the index
            // relationship, so the pair creates no obligation. A select the
            // arithmetic solver has NO value for stays reported (fail-closed):
            // dropping it is exactly how the seed-1213/187 wrong model shipped
            // (the violated read had no LIA value at reporting time).
            let keep = match (get_value_with_reasons(sel1), get_value_with_reasons(sel2)) {
                (Some((sv1, _)), Some((sv2, _))) => sv1 != sv2,
                _ => true,
            };
            if !keep {
                continue;
            }
        }
        // #7956: an asserted EUF equality between opaque Int leaves induces
        // equality of their affine contexts.  Example:
        //
        //   seq_offset(final) = seq_offset(current)
        //   seq_offset(final) + 1 = seq_offset(current) + 1
        //
        // Neither leaf needs a concrete LIA value, so the model-value path
        // below cannot discover this relationship.  Preserve EUF's
        // SAT-visible explanation on the external array edge; a ROW conflict
        // can then backtrack the responsible equality branch instead of
        // repeatedly producing a conflicted `select` function table that the
        // final model funnel must discard.  The helper fails closed when a
        // representative substitution has no SAT premise; that pair falls
        // through to the ordinary equality/disequality split below rather
        // than installing an unconditional array edge.
        if let Some(reasons) = affine_euf_equality_reasons(terms, euf, pair.idx1, pair.idx2) {
            arrays.assert_external_equality_with_reasons(pair.idx1, pair.idx2, &reasons);
            // `undecided_index_pairs` excludes relationships already present
            // in the array equality graph, so this snapshot entry witnesses a
            // newly inserted edge.  Restart once to let ROW checks consume it;
            // the next snapshot omits the now-known pair, preventing thrash.
            propagated_new = true;
            continue;
        }
        if let (Some((v1, r1)), Some((v2, r2))) = (
            get_value_with_reasons(pair.idx1),
            get_value_with_reasons(pair.idx2),
        ) {
            if v1 != v2 {
                // The model assigns distinct values to the two indices. Merge the
                // reasons from both evaluations (#6546).
                let mut reasons = r1;
                reasons.extend(r2);
                reasons.sort_by_key(|lit| (lit.term.0, lit.value));
                reasons.dedup_by_key(|lit| (lit.term, lit.value));
                if reasons.is_empty() {
                    // Model-only distinctness is NOT provable distinctness: the
                    // arithmetic solver assigns ARBITRARY distinct values to
                    // unconstrained indices (e.g. two free vars get 0 and 1).
                    // Asserting `idx1 != idx2` with no premises lets the array
                    // solver fire a ROW2 conflict (select(store(a,i,v),k)=select(a,k))
                    // whose explanation carries no `(= idx1 idx2)=false` literal, so
                    // SAT can never backtrack into the `idx1 = idx2` branch → false
                    // UNSAT. This is the disequality-direction mirror of the
                    // `v1 == v2` guard below (#5086); defer to a SAT case split.
                    unresolved_pairs.push((pair.idx1, pair.idx2));
                } else if arrays
                    .assert_external_disequality_with_reasons(pair.idx1, pair.idx2, reasons)
                {
                    // Only count as new propagation if the disequality was not
                    // already known (#6546 Packet 4). Without this, re-asserting
                    // known disequalities returns Some(Sat) which restarts the N-O
                    // loop indefinitely — the root cause of storeinv 3+ index
                    // timeouts.
                    propagated_new = true;
                }
            } else {
                // Do NOT assert equality when v1 == v2 (#5086). Model-based value
                // equality does not imply provable equality: LIA may assign all
                // unconstrained variables to 0 (the trivial model). Asserting
                // external equality in that case makes the array solver believe
                // indices are provably equal, which generates unsound conflicts
                // (false UNSAT on storecomm/swap benchmarks).
                //
                // Instead, track as unresolved for model equality case split (#6282).
                unresolved_pairs.push((pair.idx1, pair.idx2));
            }
        } else if distinct_by_affine_offset(terms, pair.idx1, pair.idx2) {
            // Syntactic affine offset — tautological, no reasons needed.
            if arrays.assert_external_disequality(pair.idx1, pair.idx2) {
                propagated_new = true;
            }
        } else {
            // Neither arithmetic model nor syntactic analysis could determine
            // the relationship. Track for model equality case split (#6282).
            unresolved_pairs.push((pair.idx1, pair.idx2));
        }
    }
    let arr_eq = arrays.propagate_equalities();
    if let Some(conflict) = arr_eq.conflict {
        return Some(array_equality_propagation_conflict_result(conflict));
    }
    for eq in &arr_eq.equalities {
        // Self-equality guard: array ROW equalities should have distinct terms.
        debug_assert!(
            eq.lhs != eq.rhs,
            "BUG: array ROW propagated trivial self-equality ({:?} = {:?})",
            eq.lhs,
            eq.rhs
        );
        euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
    }
    if !arr_eq.equalities.is_empty() {
        if let Some(result) = forward_non_sat(euf.check()) {
            return Some(result);
        }
        // Array equalities were forwarded to EUF — signal the N-O loop to
        // continue so that EUF→LIA propagation can discover new consequences
        // (#5086). Previously returned None here which caused premature
        // fixpoint termination on storeinv/swap benchmarks.
        return Some(TheoryResult::Sat);
    }
    // If there are undecided index pairs that the arithmetic model couldn't
    // resolve (same value or no value), request SAT-level case split(s) via
    // NeedModelEquality/NeedModelEqualities. This forces the SAT solver to
    // decide (= idx1 idx2), which enables array store chain resolution:
    // - If decided true: ROW1 applies (select(store(a,i,v),i) = v)
    // - If decided false: ROW2 applies (select(store(a,i,v),j) = select(a,j))
    //
    // Without this, storeinv benchmarks with Skolem index functions timeout
    // because the array solver can never resolve the store chain (#6282).
    //
    // Batch all same-sort unresolved pairs into one NeedModelEqualities to
    // avoid O(N) pipeline restarts — each restart is expensive in debug mode
    // and the pairs are typically discovered simultaneously (#6303).
    //
    // Filter out pairs that are already tracked by the array solver's
    // requested_model_eqs dedup set (#6546 Packet 4). Without this filter,
    // the trivial LIA model (all indices = 0) causes the same unresolved
    // pairs to be re-requested every N-O fixpoint, spinning the pipeline
    // through MAX_DEDUP_RETRIES * MAX_ITERATIONS iterations.
    if !unresolved_pairs.is_empty() {
        // Only request same-sort pairs — model equality creates (= lhs rhs)
        // which requires matching sorts. Also skip pairs already requested.
        let new_pairs: Vec<(TermId, TermId)> = unresolved_pairs
            .iter()
            .filter(|&&(idx1, idx2)| terms.sort(idx1) == terms.sort(idx2))
            .filter(|&&(idx1, idx2)| !arrays.model_equality_already_requested(idx1, idx2))
            .copied()
            .collect();
        for &(idx1, idx2) in &new_pairs {
            arrays.mark_model_equality_requested(idx1, idx2);
        }
        let requests: Vec<ay_core::ModelEqualityRequest> = new_pairs
            .into_iter()
            .map(|(idx1, idx2)| ay_core::ModelEqualityRequest {
                lhs: idx1,
                rhs: idx2,
                reason: Vec::new(),
                implied: false,
            })
            .collect();
        if requests.len() == 1 {
            return Some(TheoryResult::NeedModelEquality(
                requests
                    .into_iter()
                    .next()
                    .expect("invariant: requests.len() == 1"),
            ));
        } else if requests.len() > 1 {
            return Some(TheoryResult::NeedModelEqualities(requests));
        }
    }
    if !propagated_new {
        return None;
    }
    Some(TheoryResult::Sat)
}

/// Discover model equalities for Nelson-Oppen with non-convex theories (#4906).
///
/// At fixpoint, when the N-O loop would return Sat, check if there are shared
/// interface terms that have equal values in the arithmetic model but are NOT
/// yet in the same EUF equivalence class. If such pairs exist, return
/// `NeedModelEquality` or `NeedModelEqualities` so the DPLL layer creates the
/// speculative `(= lhs rhs)` decisions (Z3's `assume_eq` + `try_true_first`
/// pattern, smt_context.cpp:4576).
///
/// Returns `None` if all equal-valued terms are already EUF-equivalent (no
/// model equality needed), `Some(NeedModelEquality(...))` for a single
/// unresolved pair, or `Some(NeedModelEqualities(...))` when multiple
/// same-value groups can be unified in one restart.
pub(super) fn discover_model_equality<V: Eq + Ord + std::fmt::Display>(
    interface_arith_terms: impl Iterator<Item = TermId>,
    terms: &TermStore,
    euf: &EufSolver<'_>,
    get_value: &impl Fn(TermId) -> Option<V>,
    allowed_sorts: &[ay_core::Sort],
    debug: bool,
    label: &str,
) -> Option<TheoryResult> {
    // Collect terms with their model values. Group by value.
    // Filter to allowed sorts only — the interface set may contain
    // non-arithmetic terms (e.g., Array-sorted variables) if tracking
    // was imprecise. Creating (= Int Array) would panic in mk_eq.
    let mut value_groups: BTreeMap<V, Vec<TermId>> = BTreeMap::new();
    for term in interface_arith_terms {
        let sort = terms.sort(term);
        if !allowed_sorts.iter().any(|s| s == sort) {
            continue;
        }
        if let Some(val) = get_value(term) {
            value_groups.entry(val).or_default().push(term);
        }
    }
    // #6846: Collect ALL non-EUF-equivalent pairs into a batch instead of
    // returning only the first one. This avoids O(N) pipeline restarts when
    // many interface terms share a value (e.g., QF_AUFLIA with free UF variables).
    //
    // Within each value group, we only need ONE representative pair to unify
    // all terms: pick the first term as anchor and pair it with each non-equivalent
    // term. This gives O(N) pairs per group instead of O(N^2).
    let mut batch = Vec::new();
    for (val, group_terms) in &value_groups {
        if group_terms.len() < 2 {
            continue;
        }
        let anchor = group_terms[0];
        for &other in &group_terms[1..] {
            if anchor == other {
                continue;
            }
            // #9701: Skip pairs that EUF already knows are DISEQUAL (an
            // asserted `(not (= anchor other))`). Proposing a model equality
            // there is futile — the SAT solver can never set the equality true —
            // and it MASKS the disequality/expression split that actually forces
            // the arithmetic theory to separate the two values. Without this,
            // pigeonhole-over-bounded-UF-results formulas (e.g. three terms each
            // in {0,1}, pairwise distinct) accept a wrong-SAT all-equal model:
            // the LIA values coincide, discover_model_equality keeps requesting
            // the already-false equality, the dedup set exhausts, and the loop
            // falls through to accept the (invalid) model. Letting these pairs
            // through to the expression-split path makes LIA enforce
            // `anchor <= other-1 OR anchor >= other+1`, recovering soundness.
            if euf.are_known_disequal(anchor, other) {
                if debug {
                    safe_eprintln!(
                        "[N-O {label}] Skipping model equality for known-disequal pair: {:?} != {:?} (both = {})",
                        anchor,
                        other,
                        val,
                    );
                }
                continue;
            }
            if !euf.are_equal(anchor, other) {
                if debug {
                    safe_eprintln!(
                        "[N-O {label}] Model equality: {:?} = {:?} (both = {}, not EUF-equal)",
                        anchor,
                        other,
                        val,
                    );
                }
                batch.push(ay_core::ModelEqualityRequest {
                    lhs: anchor,
                    rhs: other,
                    reason: Vec::new(),
                    implied: false,
                });
            }
        }
    }
    match batch.len() {
        0 => None,
        1 => Some(TheoryResult::NeedModelEquality(batch.pop().unwrap())),
        _ => Some(TheoryResult::NeedModelEqualities(batch)),
    }
}

#[cfg(test)]
mod tests;
