// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Native pseudo-Boolean propagation using RoundingSat watched slack.
//!
//! Implements the watched-slack scheme from Elffers & Nordstrom, "Divide and
//! Conquer: Towards Faster Pseudo-Boolean Solving" (IJCAI 2018), also described
//! by Chai & Kuehlmann (2005).
//!
//! Constraints are normalized into `sum(a_i * l_i) >= degree` with positive
//! coefficients. For each constraint, the propagator maintains a *watched set*
//! of terms whose coefficient sum satisfies:
//!
//!   `watchedSum >= degree + maxUnwatchedCoeff`
//!
//! This invariant guarantees that no propagation is missed: if the watched sum
//! drops below the threshold after a literal becomes false, either a swap is
//! found (restoring the invariant) or propagations/conflicts are detected.
//!
//! The slack for propagation checks is:
//!
//!   `slack = sum(coeff of non-false watched terms) - degree`
//!
//! When slack < 0: conflict.
//! When slack < coeff of some watched unassigned literal: propagate that literal.
//!
//! Watch lists are maintained incrementally: when a watched literal becomes
//! false and is swapped out, only the two affected watch list entries change.
//! This avoids the O(n*m) global rebuild of the previous implementation.
//!
//! Reason clauses are returned in clause style: each literal in the reason is
//! itself false under the current assignment, except for the propagated literal.

use std::cell::Cell;

use crate::types::{PbConstraint, PbLit, PbRel, PbTerm};

mod check;
mod notify;

/// DIMACS-style SAT literal.
pub type Lit = i32;

/// The value of a literal under the current partial assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum LitValue {
    True,
    False,
    Unassigned,
}

/// Result of pseudo-Boolean propagation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PropResult {
    /// No conflict or new implication.
    Ok,
    /// Propagation was interrupted before reaching a fixpoint.
    Interrupted,
    /// The current assignment violates a constraint.
    /// Contains the conflicting literals and the internal constraint index.
    Conflict(Vec<Lit>, usize),
    /// The literal must be assigned true, with a clause-style reason.
    /// Contains the propagated literal, reason literals, and the internal
    /// constraint index that caused the propagation.
    Propagated(Lit, Vec<Lit>, usize),
}

const PB_UNIT_CARDINALITY_NATIVE_OK: i32 = 0;
const PB_UNIT_CARDINALITY_NATIVE_CONFLICT: i32 = 1;
const PB_UNIT_CARDINALITY_NATIVE_PROPAGATE: i32 = 2;
const PB_UNIT_CARDINALITY_NATIVE_INVALID: i32 = -1;

// The ExternalCodegenIr helper ABI is intentionally i64 even though the solver's
// coefficient arithmetic is i128. These mirrors contain only {-1, 0, 1},
// literal ids (i32), and a term index, so widening them with the coefficient
// migration would only make the Rust/native ABI disagree.
const PB_NATIVE_VALUE_FALSE: i64 = -1;
const PB_NATIVE_VALUE_UNASSIGNED: i64 = 0;
const PB_NATIVE_VALUE_TRUE: i64 = 1;
const PB_NATIVE_FIRST_UNASSIGNED_SENTINEL: i64 = -1;

#[repr(C)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct PbUnitCardinalityNativeOutput {
    status: i32,
    first_unassigned_index: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeHelperSource {
    NativeAbi,
    ScalarShadow,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum NativeHelperAttempt {
    Evaluated {
        result: PropResult,
        source: NativeHelperSource,
    },
    TrustedNativeOk,
    Fallback,
    Interrupted,
}

/// Counters for PB native-helper compilation, evaluation, and fail-closed use.
///
/// The first external code generation slice keeps useful native applications distinct from
/// the older scalar-shadow validation path. A useful native application is only
/// counted after a native ABI result has been accepted by scalar confirmation
/// or by the exact-mirror trusted-`Ok` guard; scalar-shadow evaluations are
/// exposed separately.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PbNativeHelperStats {
    /// Helper compile requests submitted to the backend.
    pub compile_attempts: u64,
    /// Helper compile requests that produced a callable native artifact.
    pub compile_successes: u64,
    /// Helper compile requests that failed or produced no callable artifact.
    pub compile_failures: u64,
    /// Helper evaluations considered on the solve path.
    pub evaluation_attempts: u64,
    /// Calls into a true native helper ABI.
    pub native_apply_attempts: u64,
    /// Scalar fallback checks used to confirm helper output.
    pub scalar_confirmation_checks: u64,
    /// True native helper applications accepted after scalar confirmation or a
    /// trusted exact-mirror native `Ok`.
    pub native_apply_confirmations: u64,
    /// Per-call fills of the retired packed value buffer.
    pub native_value_buffer_fills: u64,
    /// Legacy scalar-shadow helper evaluations accepted by scalar validation.
    pub scalar_shadow_applications: u64,
    /// Fail-closed deoptimizations after helper/scalar mismatch.
    pub deopts: u64,
    /// Scalar fallback applications after unsupported helper use or deopt.
    pub scalar_fallbacks: u64,
}

impl PbNativeHelperStats {
    /// Useful native applications, excluding scalar-shadow validation.
    #[must_use]
    pub const fn useful_native_applications(self) -> u64 {
        self.native_apply_confirmations
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AssignOutcome {
    NewlyAssigned,
    AlreadyAssigned,
    Conflict,
}

enum TernaryNotify {
    Advance,
    Stay,
    /// A constraint handler produced a non-`Ok` result while servicing the
    /// falsified literal. `result` is the propagation/conflict/interrupt; the
    /// constraint's cached slack has ALREADY been updated for this falsification.
    ///
    /// `advance` records whether this watch entry was retained at `cursor`
    /// (`true` → the dispatch loop must step `cursor`) or swap-removed (`false`
    /// → a different entry now occupies `cursor`, so it must be re-examined).
    /// This distinction lets the dispatch loop CONTINUE past propagations
    /// (keeping every watching constraint's slack consistent, RoundingSat
    /// `runPropagation` semantics) instead of returning early and leaving stale
    /// cached slack on the unvisited tail of the watch list.
    Return {
        result: PropResult,
        advance: bool,
    },
}

/// Processes a non-`Ok` per-constraint watch result inside the `notify_falsified`
/// dispatch loop, returning `Some(result)` when the watch-list scan must stop
/// NOW (conflict or interrupt) and `None` when it should continue.
///
/// On a propagation the first one is stashed in `first_propagation` (to surface
/// to the caller after the scan completes) and the `cursor` is stepped per
/// `advance`, so the remaining watches are still visited and their cached slack
/// stays consistent with the assignment. A conflict/interrupt is returned
/// verbatim; the partial slack decrements already applied are repaired on the
/// subsequent backtrack via the recorded falsified-watch events.
///
/// IMPORTANT (counting soundness): a conflict stops the scan, leaving the tail
/// of the watch list unprocessed. Counting constraints in that tail would then
/// miss this falsification's slack decrement while the literal stays false,
/// making their trusted-exact slack stale. The caller MUST therefore call
/// `decrement_remaining_counting_watches` before surfacing a conflict to bring
/// every tail counting constraint's slack back in sync. Non-counting
/// constraints tolerate a stale cached slack (their checks fall back to an exact
/// rescan), so they are intentionally left unprocessed — preserving the
/// well-tuned early-abort behavior of the watched scheme.
fn handle_watch_result(
    result: PropResult,
    advance: bool,
    cursor: &mut usize,
    first_propagation: &mut Option<PropResult>,
) -> Option<PropResult> {
    match result {
        PropResult::Ok => {
            if advance {
                *cursor += 1;
            }
            None
        }
        PropResult::Propagated(..) => {
            if first_propagation.is_none() {
                *first_propagation = Some(result);
            }
            if advance {
                *cursor += 1;
            }
            None
        }
        PropResult::Conflict(..) | PropResult::Interrupted => Some(result),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WeightedReplacement {
    Swap(usize),
    InsufficientNonFalse,
    NoNonFalse,
}

/// Partial SAT assignment plus decision levels.
#[derive(Debug, Default, Clone)]
pub(crate) struct Assignment {
    values: Vec<Option<bool>>,
    decision_levels: Vec<Option<u32>>,
    native_values: Vec<i64>,
}

impl Assignment {
    fn ensure_var(&mut self, var: u32) {
        let target_len =
            usize::try_from(var).expect("u32 variable index must fit in usize on this platform");
        if self.values.len() < target_len {
            self.values.resize(target_len, None);
            self.decision_levels.resize(target_len, None);
            self.native_values
                .resize(target_len, PB_NATIVE_VALUE_UNASSIGNED);
        }
    }

    fn assign_literal(&mut self, lit: Lit, decision_level: u32) -> AssignOutcome {
        let Some(var) = lit_var(lit) else {
            return AssignOutcome::Conflict;
        };

        self.ensure_var(var);
        let idx = usize::try_from(var - 1).expect("1-based variable index must fit in usize");
        let value = lit > 0;

        match self.values[idx] {
            Some(existing) if existing == value => {
                // The packed `native_values` mirror is only ever READ by the
                // unit-cardinality JIT helper (compiled solely under the
                // `native-code-backend` feature) and by the mirror unit tests. In the
                // default/competition build neither reader is compiled, so this is
                // a write-only i64 store on the hottest path; skip it there.
                #[cfg(test)]
                {
                    self.native_values[idx] = native_value_from_bool(value);
                }
                AssignOutcome::AlreadyAssigned
            }
            Some(_) => AssignOutcome::Conflict,
            None => {
                self.values[idx] = Some(value);
                self.decision_levels[idx] = Some(decision_level);
                #[cfg(test)]
                {
                    self.native_values[idx] = native_value_from_bool(value);
                }
                AssignOutcome::NewlyAssigned
            }
        }
    }

    fn unassign_literal(&mut self, lit: Lit) -> bool {
        let Some(var) = lit_var(lit) else {
            return false;
        };

        let idx = usize::try_from(var - 1).expect("1-based variable index must fit in usize");
        if idx < self.values.len() {
            let changed = self.values[idx].is_some() || self.decision_levels[idx].is_some();
            self.values[idx] = None;
            self.decision_levels[idx] = None;
            // See `assign_literal`: the `native_values` mirror is read only by the
            // `native-code-backend` JIT helper and the mirror unit tests, so skip the
            // unassign store in the default/competition build.
            #[cfg(test)]
            {
                self.native_values[idx] = PB_NATIVE_VALUE_UNASSIGNED;
            }
            changed
        } else {
            false
        }
    }

    fn value(&self, lit: Lit) -> LitValue {
        let Some(var) = lit_var(lit) else {
            return LitValue::Unassigned;
        };

        let idx = usize::try_from(var - 1).expect("1-based variable index must fit in usize");
        let Some(&stored) = self.values.get(idx) else {
            return LitValue::Unassigned;
        };

        match stored {
            Some(value) if (lit > 0) == value => LitValue::True,
            Some(_) => LitValue::False,
            None => LitValue::Unassigned,
        }
    }

    fn native_value(&self, lit: Lit) -> i64 {
        let Some(var) = lit_var(lit) else {
            return PB_NATIVE_VALUE_UNASSIGNED;
        };

        let idx = usize::try_from(var - 1).expect("1-based variable index must fit in usize");
        let Some(&value) = self.native_values.get(idx) else {
            return PB_NATIVE_VALUE_UNASSIGNED;
        };

        if lit > 0 {
            value
        } else {
            value.saturating_neg()
        }
    }

    fn native_value_mirrors_assignment(&self, lit: Lit) -> bool {
        self.native_value(lit) == native_value_from_lit_value(self.value(lit))
    }

    fn native_values(&self) -> &[i64] {
        &self.native_values
    }

    #[allow(dead_code)]
    fn decision_level(&self, lit: Lit) -> Option<u32> {
        let var = lit_var(lit)?;
        let idx = usize::try_from(var - 1).expect("1-based variable index must fit in usize");
        self.decision_levels.get(idx).copied().flatten()
    }
}

// Only the `native_values` mirror writes (gated to test/`native-code-backend`)
// call this; gate it identically so the default/competition build does not
// compile a now-unused helper.
#[cfg(test)]
fn native_value_from_bool(value: bool) -> i64 {
    if value {
        PB_NATIVE_VALUE_TRUE
    } else {
        PB_NATIVE_VALUE_FALSE
    }
}

fn native_value_from_lit_value(value: LitValue) -> i64 {
    match value {
        LitValue::True => PB_NATIVE_VALUE_TRUE,
        LitValue::False => PB_NATIVE_VALUE_FALSE,
        LitValue::Unassigned => PB_NATIVE_VALUE_UNASSIGNED,
    }
}

/// A normalized weighted literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct PropTerm {
    pub(crate) lit: Lit,
    pub(crate) coeff: i128,
}

/// Normalized propagation shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstraintShape {
    /// A unit-weight disjunction: `l_1 + ... + l_n >= 1`.
    Clause,
    /// A three-literal unit-weight disjunction with distinct literals.
    TernaryClause,
    /// A unit-weight at-least-k constraint.
    UnitCardinality,
    /// General weighted pseudo-Boolean constraint.
    Weighted,
}

/// Internal watched-slack representation of one `>=` constraint.
///
/// Terms are partitioned into watched (indices `0..watch_end`) and unwatched
/// (`watch_end..terms.len()`). Within each partition, terms are sorted by
/// descending coefficient. The invariant maintained is:
///
///   `watched_sum >= degree + max_unwatched_coeff`
///
/// where `watched_sum` is the sum of all watched term coefficients (regardless
/// of assignment), and `max_unwatched_coeff` is the largest coefficient among
/// unwatched terms (0 if none).
///
/// This invariant guarantees that when ANY watched literal becomes false, the
/// remaining watched sum still exceeds the degree by at least
/// `max_unwatched_coeff - a_false`. This means either:
/// 1. A swap can be found (the new watched literal has coeff <= max_unwatched),
///    restoring the invariant, OR
/// 2. Propagation/conflict is correctly detected.
///
/// Reference: Elffers & Nordstrom, "Divide and Conquer: Towards Faster
/// Pseudo-Boolean Solving" (IJCAI 2018), Section 3.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PropConstraint {
    terms: Vec<PropTerm>,
    native_lits: Vec<i64>,
    degree: i128,
    shape: ConstraintShape,
    /// End of the watched region: terms[0..watch_end] are watched.
    watch_end: usize,
    /// Sum of coefficients of non-false watched terms minus degree.
    slack: i128,
    /// Whether this constraint is active.
    active: bool,
    /// Sum of all watched coefficients (regardless of assignment).
    watched_sum: i128,
    /// Maximum coefficient among watched terms.
    max_watched_coeff: i128,
    /// Maximum coefficient among unwatched terms.
    max_unwatched_coeff: i128,
    /// Preferred replacement-scan start inside the unwatched region.
    weighted_replacement_scan_hint: usize,
    /// Counting (RoundingSat-style) propagation flag for `Weighted` constraints.
    ///
    /// When `true`, every term is permanently watched (`watch_end == terms.len()`,
    /// empty unwatched region, no swaps), so `slack` is the *exact* slack
    /// `sum(coeff of non-false terms) - degree` maintained incrementally in O(1)
    /// per falsify/unfalsify. This avoids the O(terms) `exact_weighted_slack`
    /// rescan that the watched-slack shortcut (`slack >= max_watched_coeff`)
    /// cannot prevent on big-M / large-coefficient rows, where the largest
    /// coefficient swamps the shortcut threshold.
    ///
    /// Because there are no swaps, terms stay in their initial descending-
    /// coefficient order, which the counting propagation scan relies on for the
    /// `coeff <= slack` early stop. Clause / cardinality / ternary shapes never
    /// set this flag; their fast paths are unchanged.
    counting: bool,
    /// For counting constraints only: `(lit, summed_coeff)` pairs sorted by
    /// `lit`, aggregating duplicate occurrences of the same literal. Lets
    /// `notify_falsified` recover a falsified literal's total coefficient in
    /// O(log n) without scanning all terms — the lookup that keeps counting
    /// propagation O(log n) per touch instead of O(terms). Empty for
    /// non-counting constraints.
    counting_lit_coeffs: Vec<(Lit, i128)>,
    /// Full-visibility mode (P2d event-driven completeness): the constraint
    /// is watched on EVERY distinct literal, and falsifications of literals
    /// OUTSIDE the watched region trigger a full (exact) propagation check
    /// without touching cached slack.
    ///
    /// Armed when a FALSE literal gets stuck in the watched region — no
    /// invariant-preserving replacement existed at falsification time, or the
    /// region was born with a false literal (constraints added mid-search,
    /// e.g. objective bounds and learned rows). In that state the watched
    /// slack under-approximates the exact slack, so falsifications (and
    /// backtrack un-falsifications) of UNWATCHED literals can flip the
    /// constraint between Ok/propagating/conflicting with no watched event.
    /// The historical full rescan per `propagate_all` call re-checked every
    /// constraint and hid this blindness; the event-driven fixpoint instead
    /// arms full visibility exactly for the affected rows. Never disarmed
    /// (conservative: extra checks only), survives rebuilds.
    watch_all: bool,
    /// Falsified-watch-event validity epoch (P2e per-literal event buckets).
    ///
    /// Every falsified-watch event recorded for this row carries the epoch at
    /// record time; the unassign repair pass only honors events whose epoch
    /// still matches. Bumped exactly when the row's event semantics are
    /// rewritten wholesale (`convert_to_counting` re-records aggregated
    /// per-literal events), which lazily invalidates the watched-mode events
    /// still sitting in per-literal buckets without an O(total events) sweep.
    event_epoch: u32,
}

/// Native PB watched-slack propagator implementing the RoundingSat algorithm.
///
/// Watch lists map each literal to the set of constraint indices that watch it.
/// When a literal becomes false, only constraints watching that literal are
/// examined, making propagation event-driven rather than scanning all
/// constraints.
#[derive(Debug, Default)]
pub struct PbPropagator {
    constraints: Vec<PropConstraint>,
    assignment: Assignment,
    /// Watch lists: indexed by `lit_index(lit)`, each entry is a list of
    /// constraint indices that currently watch that literal.
    watches: Vec<Vec<usize>>,
    /// Reused scratch storage for constructor-time watch-list insertion.
    watch_build_scratch: Vec<usize>,
    /// Falsified-watch-event buckets, indexed by `lit_index(lit)` like
    /// `watches`: constraints whose slack was decremented for that active
    /// false watched literal, each entry stamped with the row's `event_epoch`
    /// at record time (stale-epoch entries are skipped and discarded on
    /// consumption). Bucketing keys the unassign repair pass by the literals
    /// actually unassigned, making backtrack O(events of those literals)
    /// instead of a full scan of every outstanding event (P2e: the full scan
    /// dominated UNSAT-grind profiles at ~100k outstanding events).
    falsified_watch_events: Vec<Vec<(usize, u32)>>,
    /// Scratch literal set used when rebuilding false-watch event records.
    falsified_watch_event_lits: Vec<Lit>,
    #[cfg(test)]
    rebuild_count: u64,
    #[cfg(test)]
    stats: PropagationStats,
    /// Some interruptible maintenance paths leave watch/slack state dirty and
    /// require a full rebuild before the next propagation step.
    needs_rebuild: bool,
    /// Event-driven propagation work queue (P2d): constraint indices whose
    /// last check reported a propagation that the caller did not consume
    /// (`notify_falsified` keeps only the FIRST propagation per event), plus
    /// newly added constraints. Draining this queue lets the CDCL fixpoint
    /// driver skip the historical O(constraints) full rescan per decision.
    /// Deduplicated via `in_pending_check`; stale entries are harmless (a
    /// recheck of a non-propagating or inactive constraint returns `Ok`).
    /// A min-heap on the constraint index: the historical full scan always
    /// serviced the LOWEST-cid propagating constraint first, and keeping that
    /// bias keeps the search trajectory close to the scan-based engine's.
    pending_check_cids: std::collections::BinaryHeap<std::cmp::Reverse<usize>>,
    /// Per-constraint "already queued in `pending_check_cids`" flag.
    in_pending_check: Vec<bool>,
    /// Whether one full constraint scan has reached a propagation fixpoint
    /// since construction / the last full rebuild. Until then, event-driven
    /// draining alone is not sufficient and callers must scan.
    full_scan_done: bool,
    /// Incremented on every `invalidate_full_scan`. Fixpoint drivers capture
    /// this before scanning and refuse to `mark_full_scan_complete` if a
    /// rebuild invalidated constraint state mid-drive (the completed scan
    /// prefix would no longer certify the rebuilt constraints).
    full_scan_generation: u64,
    /// Test-only escape: disables the P2d blind-row full-visibility arming
    /// so propagator-level tests can pin the pure watched-scheme behaviors
    /// (counting-selection policy, reason paths, watch bounds) without rows
    /// converting to counting/watch-all mid-test. The CDCL fixpoint drivers
    /// REQUIRE arming for event completeness (their debug oracle would
    /// fail), so this exists only for direct-propagator tests.
    #[cfg(test)]
    blind_arming_disabled: bool,
    /// Enables external code generation native-helper validation against the scalar fallback.
    native_code_helper_validation_enabled: bool,
    /// Fail-closed deopt flag set after any helper/scalar mismatch.
    native_code_helper_deopted: Cell<bool>,
    /// Native-helper and scalar-shadow counters.
    native_helper_stats: Cell<PbNativeHelperStats>,
    #[cfg(test)]
    force_next_native_code_helper_mismatch: Cell<bool>,
    #[cfg(test)]
    force_next_native_code_helper_invalid: Cell<bool>,
}

#[cfg(test)]
#[derive(Debug, Default)]
struct PropagationStats {
    clause_checks: Cell<u64>,
    unit_cardinality_checks: Cell<u64>,
    weighted_checks: Cell<u64>,
    clause_watch_shortcuts: Cell<u64>,
    unit_cardinality_watch_shortcuts: Cell<u64>,
    unit_cardinality_slack_shortcuts: Cell<u64>,
    unit_cardinality_full_scans: Cell<u64>,
    unit_cardinality_scan_terms: Cell<u64>,
    weighted_slack_shortcuts: Cell<u64>,
    weighted_no_replacement_shortcuts: Cell<u64>,
    weighted_exact_slack_scans: Cell<u64>,
    slack_recalculations: Cell<u64>,
    coefficient_bound_recomputations: Cell<u64>,
    unwatched_replacement_candidates: Cell<u64>,
    unwatched_replacement_value_checks: Cell<u64>,
    deactivation_watch_lists_visited: Cell<u64>,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct PropagationStatsSnapshot {
    pub(crate) clause_checks: u64,
    pub(crate) unit_cardinality_checks: u64,
    pub(crate) weighted_checks: u64,
    pub(crate) clause_watch_shortcuts: u64,
    pub(crate) unit_cardinality_watch_shortcuts: u64,
    pub(crate) unit_cardinality_slack_shortcuts: u64,
    pub(crate) unit_cardinality_full_scans: u64,
    pub(crate) unit_cardinality_scan_terms: u64,
    pub(crate) weighted_slack_shortcuts: u64,
    pub(crate) weighted_no_replacement_shortcuts: u64,
    pub(crate) weighted_exact_slack_scans: u64,
    pub(crate) slack_recalculations: u64,
    pub(crate) coefficient_bound_recomputations: u64,
    pub(crate) unwatched_replacement_candidates: u64,
    pub(crate) unwatched_replacement_value_checks: u64,
    pub(crate) deactivation_watch_lists_visited: u64,
}

const STOP_POLL_INTERVAL: usize = 256;
const WATCH_LIST_MIN_GROWTH: usize = 8;
const WATCH_LIST_MAX_GROWTH: usize = 1024;

impl PbPropagator {
    /// Creates an empty propagator.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Pre-sizes the propagator for a bulk import of `num_constraints` rows over
    /// variables `1..=num_vars`.
    ///
    /// Purely an allocation hint for the solver-construction import path: the
    /// per-row `add_*_constraint` calls otherwise grow `constraints` /
    /// `in_pending_check` / the dense assignment and watch arrays through
    /// amortized doubling, whose final step overshoots the needed capacity by
    /// up to ~30% — over-allocation that is RETAINED for the whole solve on a
    /// multi-million-row instance (measured ~86MB max-RSS on the 6.4M-row
    /// lopes-172; see the call site in `cdcl.rs`). `Eq` rows import as two
    /// internal rows, so `num_constraints` is a floor — any excess simply
    /// falls back to the normal amortized growth. Semantics are unchanged:
    /// capacity only.
    pub(crate) fn reserve_for_bulk_import(&mut self, num_vars: u32, num_constraints: usize) {
        self.constraints.reserve_exact(num_constraints);
        self.in_pending_check.reserve_exact(num_constraints);
        self.assignment.ensure_var(num_vars);
        self.ensure_watch_capacity(num_vars);
    }

    /// Adds a pseudo-Boolean constraint.
    ///
    /// `PbRel::Eq` is represented internally as two normalized `>=`
    /// constraints. The returned identifier is the first internal constraint
    /// added for this call. `None` means the whole constraint was trivially
    /// satisfied.
    pub fn add_constraint(&mut self, terms: &[PbTerm], rel: PbRel, rhs: i128) -> Option<usize> {
        let mut first_id = self.add_ge_constraint(terms, rhs);

        if rel == PbRel::Eq {
            let mut negated_terms = Vec::with_capacity(terms.len());
            negated_terms.extend(terms.iter().map(|term| PbTerm {
                coeff: -term.coeff,
                lits: term.lits.clone(),
            }));

            let second_id = self.add_ge_constraint(&negated_terms, -rhs);
            if first_id.is_none() {
                first_id = second_id;
            }
        }

        first_id
    }

    /// Adds a constraint from the crate's public `PbConstraint` type.
    pub fn add_from_pb_constraint(&mut self, constraint: &PbConstraint) -> Option<usize> {
        self.add_constraint(&constraint.terms, constraint.rel, constraint.rhs)
    }

    /// Returns whether constraint `cid` uses counting propagation.
    #[cfg(test)]
    pub(crate) fn is_counting_for_test(&self, cid: usize) -> bool {
        self.constraints.get(cid).is_some_and(|c| c.counting)
    }

    /// Returns the cached slack of constraint `cid` (test introspection).
    #[cfg(test)]
    pub(crate) fn slack_for_test(&self, cid: usize) -> i128 {
        self.constraints[cid].slack
    }

    /// Recomputes the exact slack of weighted constraint `cid` from scratch.
    #[cfg(test)]
    pub(crate) fn exact_weighted_slack_for_test(&self, cid: usize) -> i128 {
        self.exact_weighted_slack(cid)
    }

    /// Disables the P2d blind-row arming for this propagator (test-only; see
    /// the `blind_arming_disabled` field).
    #[cfg(test)]
    pub(crate) fn disable_blind_arming_for_test(&mut self) {
        self.blind_arming_disabled = true;
        // Undo any arming that construction-time adds already performed:
        // rebuilding re-derives regions/watches, and the disabled flag keeps
        // them on the pure watched scheme afterwards.
        for constraint in &mut self.constraints {
            constraint.watch_all = false;
        }
        self.needs_rebuild = true;
        self.rebuild_all_constraint_state();
    }

    /// Forces constraint `cid` into (or out of) counting mode and rebuilds its
    /// watched/slack state at the current assignment. Used by the differential
    /// fuzz test to compare counting vs watched propagation on identical input.
    #[cfg(test)]
    pub(crate) fn set_constraint_counting_for_test(&mut self, cid: usize, counting: bool) {
        if self.constraints[cid].shape != ConstraintShape::Weighted {
            return;
        }
        self.constraints[cid].counting = counting;
        if !counting {
            self.constraints[cid].counting_lit_coeffs = Vec::new();
        }
        // Re-initialize watch/slack state for the new mode and rebuild all watch
        // lists so the watched literals match `watch_end`.
        self.needs_rebuild = true;
        self.rebuild_all_constraint_state();
    }

    /// Adds a constraint from the crate's public `PbConstraint` type, polling
    /// during the constructor work used by timeout-sensitive prechecks.
    ///
    /// If this returns `Err(())`, the caller should discard this propagator
    /// before further use. Timeout prechecks do that naturally by returning
    /// `Unknown`.
    pub(crate) fn add_from_pb_constraint_interruptible<F>(
        &mut self,
        constraint: &PbConstraint,
        should_stop: &mut F,
    ) -> Result<Option<usize>, ()>
    where
        F: FnMut() -> bool,
    {
        self.add_constraint_interruptible(
            &constraint.terms,
            constraint.rel,
            constraint.rhs,
            should_stop,
        )
    }

    /// Assigns a literal to true and performs event-driven propagation.
    ///
    /// Only constraints watching the negation of `lit` are examined. This is
    /// the core of the RoundingSat efficiency: most constraints are untouched
    /// per assignment.
    pub fn assign_literal(&mut self, lit: Lit, decision_level: u32) -> PropResult {
        self.ensure_rebuilt();

        match self.assignment.assign_literal(lit, decision_level) {
            AssignOutcome::AlreadyAssigned => return PropResult::Ok,
            AssignOutcome::Conflict => return PropResult::Conflict(Vec::new(), usize::MAX),
            AssignOutcome::NewlyAssigned => {}
        }

        self.notify_falsified(-lit)
    }

    /// Assigns a literal to true and performs event-driven propagation with
    /// cooperative interruption checks.
    pub fn assign_literal_interruptible<F>(
        &mut self,
        lit: Lit,
        decision_level: u32,
        mut should_stop: F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return PropResult::Interrupted;
        }
        if self.ensure_rebuilt_interruptible(&mut should_stop) {
            return PropResult::Interrupted;
        }

        match self.assignment.assign_literal(lit, decision_level) {
            AssignOutcome::AlreadyAssigned => return PropResult::Ok,
            AssignOutcome::Conflict => return PropResult::Conflict(Vec::new(), usize::MAX),
            AssignOutcome::NewlyAssigned => {}
        }

        self.notify_falsified_interruptible(-lit, &mut should_stop)
    }

    /// Removes any assignment to the variable referenced by `lit`.
    ///
    /// On backtrack, we unassign the literal and repair watched-prefix slack.
    pub fn unassign_literal(&mut self, lit: Lit) {
        self.unassign_literals(&[lit]);
    }

    /// Removes multiple assignments, then repairs watched-prefix slack.
    ///
    /// This is the preferred backtrack path for CDCL. Clean watch state only
    /// needs slack for formerly false watched literals restored; dirty state
    /// still falls back to a full rebuild.
    pub(crate) fn unassign_literals(&mut self, lits: &[Lit]) {
        if lits.is_empty() {
            return;
        }
        let repair_incrementally = !self.needs_rebuild;
        let mut formerly_false_lits = Vec::new();
        let mut changed = false;
        for &lit in lits {
            if repair_incrementally {
                match self.assignment.value(lit) {
                    LitValue::True => formerly_false_lits.push(-lit),
                    LitValue::False => formerly_false_lits.push(lit),
                    LitValue::Unassigned => {}
                }
            }
            changed |= self.assignment.unassign_literal(lit);
        }
        if !changed && !self.needs_rebuild {
            return;
        }
        if self.needs_rebuild {
            self.rebuild_all_constraint_state();
            return;
        }

        self.repair_slack_after_unassign(&formerly_false_lits);
        self.queue_rechecks_for_unassigned_true_lits(&formerly_false_lits);
    }

    /// Removes multiple assignments and attempts to rebuild watch/slack state,
    /// returning `true` if the rebuild was interrupted.
    pub(crate) fn unassign_literals_interruptible<F>(
        &mut self,
        lits: &[Lit],
        mut should_stop: F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        if lits.is_empty() {
            return false;
        }
        let repair_incrementally = !self.needs_rebuild;
        let mut formerly_false_lits = Vec::new();
        let mut changed = false;
        for &lit in lits {
            if repair_incrementally {
                match self.assignment.value(lit) {
                    LitValue::True => formerly_false_lits.push(-lit),
                    LitValue::False => formerly_false_lits.push(lit),
                    LitValue::Unassigned => {}
                }
            }
            changed |= self.assignment.unassign_literal(lit);
        }
        if !changed && !self.needs_rebuild {
            return false;
        }
        if self.needs_rebuild {
            return self.rebuild_all_constraint_state_interruptible(&mut should_stop);
        }

        if self.repair_slack_after_unassign_interruptible(&formerly_false_lits, &mut should_stop) {
            return true;
        }
        self.queue_rechecks_for_unassigned_true_lits_interruptible(
            &formerly_false_lits,
            &mut should_stop,
        )
    }

    /// Scans all constraints for a conflict or one implication.
    ///
    /// This is the fallback full-scan propagation used after backtracking or
    /// when the caller wants to ensure all propagations are found. In normal
    /// CDCL operation, `assign_literal` handles event-driven propagation.
    pub fn propagate(&mut self) -> PropResult {
        self.propagate_from(0)
    }

    /// Queues constraint `cid` for a later propagation re-check (deduplicated).
    ///
    /// Called for every constraint whose check reports a propagation during
    /// watch notification (including ones whose result the caller consumes —
    /// rechecking a satisfied-fixpoint constraint is an `Ok` no-op) and for
    /// every newly added constraint. See `pending_check_cids`.
    pub(crate) fn queue_pending_check(&mut self, cid: usize) {
        if let Some(flag) = self.in_pending_check.get_mut(cid) {
            if !*flag {
                *flag = true;
                self.pending_check_cids.push(std::cmp::Reverse(cid));
            }
        }
    }

    /// Arms full visibility for `cid` iff its cached watched slack leaves
    /// room for a watched-literal propagation (`slack < max_watched_coeff`).
    ///
    /// This is the precise blindness condition for the exact-slack checks:
    /// unwatched falsifications can silently drive the exact slack down to
    /// the watched slack, so any watched literal with `coeff > slack` may
    /// become propagating with no watched event. When `slack >=
    /// max_watched_coeff` no literal can propagate even at that minimum
    /// (unwatched literals never propagate while the region invariant
    /// holds), so the row is safe until its next WATCHED falsification —
    /// which is evented and re-runs this check.
    fn arm_watch_all_if_blind(&mut self, cid: usize) {
        let Some(constraint) = self.constraints.get(cid) else {
            return;
        };
        if constraint.watch_all || constraint.counting || !constraint.active {
            return;
        }
        if constraint.slack < constraint.max_watched_coeff {
            self.arm_watch_all(cid);
        }
    }

    /// Whether the watched region of `cid` currently contains a false literal.
    fn watched_region_has_false_lit(&self, cid: usize) -> bool {
        let constraint = &self.constraints[cid];
        constraint.terms[..constraint.watch_end]
            .iter()
            .any(|term| self.assignment.value(term.lit) == LitValue::False)
    }

    /// Arms full-visibility mode for `cid` so falsifications (and backtrack
    /// un-falsifications) of every literal notify the constraint. Idempotent;
    /// never adds a watch entry for a literal that already has one (in
    /// particular, never for the falsified literal being processed by an
    /// in-flight notification, whose watch list is being iterated).
    ///
    /// Weighted rows are upgraded to COUNTING mode (all terms watched, exact
    /// slack maintained incrementally): profiling showed the plain
    /// `watch_all` fallback re-running the O(terms) exact rescan on every
    /// falsification of an armed row, while counting pays O(log terms) per
    /// touch. Unit-coefficient shapes (Clause/UnitCardinality/TernaryClause)
    /// keep their value-based checks and only gain the extra watch entries
    /// plus the `watch_all` re-check paths in `notify_falsified`; their
    /// cached slack and falsified-watch events are untouched.
    fn arm_watch_all(&mut self, cid: usize) {
        #[cfg(test)]
        if self.blind_arming_disabled {
            return;
        }
        let Some(constraint) = self.constraints.get(cid) else {
            return;
        };
        if constraint.watch_all || constraint.counting || !constraint.active {
            return;
        }
        // Weighted rows convert to counting unless the counting kill switch
        // is set for A/B measurement — then they fall back to the plain
        // full-visibility mode (equally exact, rescan per touch).
        if constraint.shape == ConstraintShape::Weighted && !counting_disabled_by_env() {
            self.convert_to_counting(cid);
            return;
        }
        self.constraints[cid].watch_all = true;
        let n = self.constraints[cid].terms.len();
        for idx in self.constraints[cid].watch_end..n {
            let lit = self.constraints[cid].terms[idx].lit;
            // `add_watch` dedupes against existing entries (the watched
            // region's lists and duplicate unwatched occurrences).
            self.add_watch(lit, cid);
        }
    }

    /// Converts a Weighted watched-slack row to counting mode mid-search
    /// (P2d full visibility for blind rows).
    ///
    /// Counting rows watch every term and trust `slack` as the EXACT slack,
    /// so the conversion must re-establish every counting invariant at the
    /// current assignment:
    /// 1. restore the descending-coefficient term order the counting
    ///    early-break scan relies on (swaps perturbed it);
    /// 2. rebuild the counting region (`watch_end == terms.len()`, aggregated
    ///    `counting_lit_coeffs`) and recompute `slack` exactly;
    /// 3. watch every distinct literal (deduplicated);
    /// 4. rewrite this row's falsified-watch events so backtrack repair
    ///    restores exactly one aggregated coefficient per false literal —
    ///    the pre-conversion events reflected watched-region semantics and
    ///    would otherwise double- or under-restore.
    fn convert_to_counting(&mut self, cid: usize) {
        debug_assert_eq!(self.constraints[cid].shape, ConstraintShape::Weighted);
        debug_assert!(!self.constraints[cid].counting);
        // Weighted rows carry no native-helper literal mirror (only
        // UnitCardinality does), so sorting terms alone is safe.
        debug_assert!(self.constraints[cid].native_lits.is_empty());

        // (1) Restore the descending order used at construction.
        self.constraints[cid].terms.sort_by(|lhs, rhs| {
            rhs.coeff
                .cmp(&lhs.coeff)
                .then_with(|| lhs.lit.unsigned_abs().cmp(&rhs.lit.unsigned_abs()))
                .then_with(|| lhs.lit.cmp(&rhs.lit))
        });

        // (2) Counting region + exact slack.
        self.constraints[cid].counting = true;
        self.initialize_counting_watched_region(cid);
        self.recalculate_slack(cid);

        // (3) Watch everything (deduplicated; existing entries survive).
        let n = self.constraints[cid].terms.len();
        for idx in 0..n {
            let lit = self.constraints[cid].terms[idx].lit;
            self.add_watch(lit, cid);
        }

        // (4) Rewrite the repair events for this row. Bumping the row's event
        // epoch lazily invalidates every event recorded under watched-mode
        // semantics (stale-epoch entries are skipped when their literal's
        // bucket is consumed); the re-record below then stores exactly one
        // aggregated event per currently-false literal at the new epoch.
        self.constraints[cid].event_epoch = self.constraints[cid].event_epoch.wrapping_add(1);
        self.record_constraint_falsified_watch_events(cid);
    }

    /// Queues `cid` for re-checking iff its cached watched slack leaves room
    /// for a propagation or conflict (`slack < max_watched_coeff`).
    ///
    /// This is the conservative-inclusive "might fire" test shared by every
    /// shape: Weighted uses exactly this shortcut
    /// (`weighted_has_sufficient_watched_slack`), Clause/UnitCardinality
    /// propagate only when `slack <= 0` (unit coefficients, so `< 1`), and
    /// TernaryClause pins `slack = 0` at initialization (always re-checked —
    /// its value-based check is three literal reads). Counting rows keep
    /// their exact slack in `slack` and their maximum coefficient in
    /// `max_watched_coeff`.
    fn queue_pending_check_if_tight(&mut self, cid: usize) {
        let Some(constraint) = self.constraints.get(cid) else {
            return;
        };
        if constraint.active && constraint.slack < constraint.max_watched_coeff {
            self.queue_pending_check(cid);
        }
    }

    /// Re-queues constraints whose propagation may have been RE-ENABLED by
    /// unassignments (P2d event-driven completeness).
    ///
    /// Falsified-side slack restoration is handled by
    /// `repair_slack_after_unassign`; this covers the other polarity: a
    /// watched literal that was TRUE and becomes UNASSIGNED re-enters the
    /// `coeff > slack && unassigned` propagation test with the slack
    /// UNCHANGED (a true watched literal already counted as non-false). Any
    /// watcher of the formerly-true literal with tight slack must therefore
    /// be re-checked — the historical full rescan per `propagate_all` call
    /// found these implicitly. `formerly_false_lits` holds the FALSIFIED
    /// polarity per unassigned variable (see `unassign_literals`), so the
    /// formerly-true literal is its negation.
    fn queue_rechecks_for_unassigned_true_lits(&mut self, formerly_false_lits: &[Lit]) {
        for &falsified in formerly_false_lits {
            let Some(watch_idx) = lit_index(-falsified) else {
                continue;
            };
            if watch_idx >= self.watches.len() {
                continue;
            }
            let mut i = 0usize;
            while i < self.watches[watch_idx].len() {
                let cid = self.watches[watch_idx][i];
                i += 1;
                self.queue_pending_check_if_tight(cid);
            }
        }
    }

    /// Interruptible variant of `queue_rechecks_for_unassigned_true_lits`.
    /// On interruption the propagator is marked for a full rebuild (which
    /// re-arms the full scan), so a partial walk can never silently drop a
    /// re-enabled propagation.
    fn queue_rechecks_for_unassigned_true_lits_interruptible<F>(
        &mut self,
        formerly_false_lits: &[Lit],
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        let mut poll_budget = STOP_POLL_INTERVAL;
        for &falsified in formerly_false_lits {
            let Some(watch_idx) = lit_index(-falsified) else {
                continue;
            };
            if watch_idx >= self.watches.len() {
                continue;
            }
            let mut i = 0usize;
            while i < self.watches[watch_idx].len() {
                if should_interrupt(should_stop, &mut poll_budget) {
                    self.needs_rebuild = true;
                    return true;
                }
                let cid = self.watches[watch_idx][i];
                i += 1;
                self.queue_pending_check_if_tight(cid);
            }
        }
        false
    }

    /// Pops one queued constraint index for re-checking, if any.
    pub(crate) fn pop_pending_check(&mut self) -> Option<usize> {
        let std::cmp::Reverse(cid) = self.pending_check_cids.pop()?;
        if let Some(flag) = self.in_pending_check.get_mut(cid) {
            *flag = false;
        }
        Some(cid)
    }

    /// Whether a fixpoint driver must still run one full constraint scan
    /// before trusting event-driven queue draining alone.
    ///
    /// A PENDING rebuild also demands a scan (D3): an interrupted
    /// notification abandons its watch-list walk mid-way and only marks
    /// `needs_rebuild` — the dropped propagations are re-discoverable solely
    /// by rebuild + rescan. Without this clause a drive whose queue happens
    /// to be empty would skip both (the rebuild only runs lazily inside
    /// scan/recheck calls) and return a false fixpoint. The scan this forces
    /// runs `ensure_rebuilt` first; the rebuild bumps the scan generation, so
    /// the drive's completion claim is refused and one redundant (fail-safe)
    /// scan follows on the next drive.
    pub(crate) fn needs_full_scan(&self) -> bool {
        !self.full_scan_done || self.needs_rebuild
    }

    /// Opaque token for `mark_full_scan_complete`: captures the current
    /// rebuild generation so a completion claim is refused when constraint
    /// state was rebuilt wholesale during the drive.
    pub(crate) fn full_scan_token(&self) -> u64 {
        self.full_scan_generation
    }

    /// Records that a full constraint scan reached a propagation fixpoint.
    /// Only fixpoint drivers (CDCL `propagate_all`, preprocessing
    /// `drive_to_fixpoint`) may call this, and only after a scan over every
    /// constraint returned no conflict/propagation and the pending queue was
    /// drained. `token` must come from `full_scan_token()` taken before the
    /// scan began; a stale token (mid-drive rebuild) makes this a no-op, so
    /// the next drive scans again.
    pub(crate) fn mark_full_scan_complete(&mut self, token: u64) {
        if token == self.full_scan_generation {
            self.full_scan_done = true;
        }
    }

    /// Invalidates the event-driven shortcut: the next fixpoint drive must
    /// perform a full constraint scan (used after full watch/slack rebuilds,
    /// which recompute constraint state wholesale).
    fn invalidate_full_scan(&mut self) {
        self.full_scan_done = false;
        self.full_scan_generation = self.full_scan_generation.wrapping_add(1);
    }

    /// Scans active constraints from `start_cid` for a conflict or one
    /// implication.
    pub(crate) fn propagate_from(&mut self, start_cid: usize) -> PropResult {
        self.ensure_rebuilt();

        for cid in start_cid..self.constraints.len() {
            let result = self.propagate_constraint(cid);
            if !matches!(result, PropResult::Ok) {
                return result;
            }
        }

        PropResult::Ok
    }

    /// Rechecks one constraint for conflict or propagation.
    pub(crate) fn propagate_constraint(&mut self, cid: usize) -> PropResult {
        self.ensure_rebuilt();

        if self
            .constraints
            .get(cid)
            .map_or(true, |constraint| !constraint.active)
        {
            return PropResult::Ok;
        }

        self.check_propagation(cid)
    }

    /// Scans all constraints for a conflict or one implication, with
    /// cooperative interruption checks.
    pub fn propagate_interruptible<F>(&mut self, mut should_stop: F) -> PropResult
    where
        F: FnMut() -> bool,
    {
        self.propagate_from_interruptible(0, &mut should_stop)
    }

    pub(crate) fn propagate_from_interruptible<F>(
        &mut self,
        start_cid: usize,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return PropResult::Interrupted;
        }
        if self.ensure_rebuilt_interruptible(should_stop) {
            return PropResult::Interrupted;
        }

        let mut poll_budget = STOP_POLL_INTERVAL;
        for cid in start_cid..self.constraints.len() {
            if should_interrupt(should_stop, &mut poll_budget) {
                return PropResult::Interrupted;
            }
            let result = self.propagate_constraint_interruptible(cid, should_stop);
            if !matches!(result, PropResult::Ok) {
                return result;
            }
        }

        PropResult::Ok
    }

    pub(crate) fn propagate_constraint_interruptible<F>(
        &mut self,
        cid: usize,
        should_stop: &mut F,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return PropResult::Interrupted;
        }
        if self.ensure_rebuilt_interruptible(should_stop) {
            return PropResult::Interrupted;
        }
        if self
            .constraints
            .get(cid)
            .map_or(true, |constraint| !constraint.active)
        {
            return PropResult::Ok;
        }

        self.check_propagation_interruptible(cid, should_stop)
    }

    /// Returns the current value of `lit`.
    #[must_use]
    pub fn value(&self, lit: Lit) -> LitValue {
        self.assignment.value(lit)
    }

    /// Returns the number of internal `>=` constraints.
    #[must_use]
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Diagnostic: total falsified-watch-event entries currently outstanding
    /// across all per-literal buckets (stale-epoch entries included).
    #[must_use]
    pub(crate) fn falsified_watch_events_len(&self) -> usize {
        self.falsified_watch_events.iter().map(Vec::len).sum()
    }

    /// Enables or disables validated external code generation native-helper execution.
    pub(crate) fn set_native_code_helper_validation_enabled(&mut self, enabled: bool) {
        self.native_code_helper_validation_enabled = enabled;
        if enabled {
            self.native_code_helper_deopted.set(false);
        }
    }

    /// Returns useful solve-path external code generation native-helper applications.
    ///
    /// Scalar-shadow validations are intentionally excluded; use
    /// `native_helper_stats` for those counters.
    #[must_use]
    pub(crate) fn native_code_helper_applications(&self) -> u64 {
        self.native_helper_stats().useful_native_applications()
    }

    /// Returns native-helper and scalar-shadow solve-path counters.
    #[must_use]
    pub fn native_helper_stats(&self) -> PbNativeHelperStats {
        self.native_helper_stats.get()
    }

    #[cfg(test)]
    fn force_next_native_code_helper_mismatch_for_test(&self) {
        self.force_next_native_code_helper_mismatch.set(true);
    }

    /// Returns the normalized PB constraint for the given internal index.
    ///
    /// This is used by cutting-planes conflict analysis to retrieve the
    /// original constraint for resolution. Returns `None` if `cid` is out of
    /// range.
    #[must_use]
    pub fn get_constraint_pb(&self, cid: usize) -> Option<PbConstraint> {
        let constraint = self.constraints.get(cid)?;
        let terms = constraint
            .terms
            .iter()
            .map(|t| {
                let var = t.lit.unsigned_abs();
                let negated = t.lit < 0;
                PbTerm {
                    coeff: t.coeff,
                    lits: vec![PbLit { var, negated }],
                }
            })
            .collect();
        Some(PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: constraint.degree,
        })
    }

    /// Returns the decision level at which a literal was assigned, if any.
    #[must_use]
    pub fn decision_level(&self, lit: Lit) -> Option<u32> {
        self.assignment.decision_level(lit)
    }

    /// Deactivates a constraint so it is skipped during propagation.
    ///
    /// The constraint remains in the array to preserve index stability, but
    /// propagation skips it. Watch list entries for this constraint are removed
    /// only from the buckets matching its current watched literals.
    pub fn deactivate_constraint(&mut self, cid: usize) {
        let Some(constraint) = self.constraints.get_mut(cid) else {
            return;
        };

        if !constraint.active {
            return;
        }
        constraint.active = false;

        if self.needs_rebuild {
            return;
        }

        let mut watch_indices = std::mem::take(&mut self.watch_build_scratch);
        self.collect_unique_watched_indices(cid, &mut watch_indices);

        for watch_idx in watch_indices.iter().copied() {
            #[cfg(test)]
            self.stats.deactivation_watch_lists_visited.set(
                self.stats
                    .deactivation_watch_lists_visited
                    .get()
                    .saturating_add(1),
            );

            if let Some(watch_list) = self.watches.get_mut(watch_idx) {
                watch_list.retain(|&c| c != cid);
            }
        }

        watch_indices.clear();
        self.watch_build_scratch = watch_indices;
    }

    /// Deactivates a constraint without removing its watch-list entries.
    ///
    /// Event-driven propagation skips inactive constraints, and the next watch
    /// rebuild drops the stale entries. This is only for bulk-retired bounds
    /// where removing each watch eagerly is the hot path.
    pub(crate) fn deactivate_constraint_lazy(&mut self, cid: usize) {
        if let Some(constraint) = self.constraints.get_mut(cid) {
            constraint.active = false;
        }
    }

    /// Deactivates a batch of constraints and removes their watch-list
    /// entries with ONE retain per affected watch list.
    ///
    /// EXACTLY equivalent to calling [`Self::deactivate_constraint`] per cid
    /// — including the subtlety that only entries in the buckets of each
    /// row's CURRENTLY WATCHED literals are removed, while stale entries
    /// (left by counting conversions / lazy retirement) survive to be
    /// `swap_remove`d organically during later notifications. Preserving
    /// that end state keeps the propagation visit order — and therefore the
    /// search trajectory — bit-identical to the per-row path (verified by a
    /// trajectory bisect on tsp DEC-LIN rows, P2e).
    ///
    /// The win is purely algorithmic: each affected bucket is scanned ONCE
    /// for the whole batch instead of once per retiring row. `reduce_db`
    /// retires hundreds of dense counting rows at a time (every literal
    /// watched, watch lists thousands long), where the per-row retain loop
    /// dominated UNSAT-grind profiles (P2e).
    pub fn deactivate_constraints_bulk(&mut self, cids: &[usize]) {
        if cids.is_empty() {
            return;
        }
        // Mark rows inactive first (idempotent; skips already-inactive
        // rows), collecting per-bucket removal lists from each row's
        // currently watched literals — the same buckets the per-row path
        // would have visited.
        let mut removals_by_bucket: std::collections::HashMap<usize, Vec<usize>> =
            std::collections::HashMap::new();
        let mut watch_indices = std::mem::take(&mut self.watch_build_scratch);
        let mut any_newly_deactivated = false;
        for &cid in cids {
            let Some(constraint) = self.constraints.get_mut(cid) else {
                continue;
            };
            if !constraint.active {
                continue;
            }
            constraint.active = false;
            any_newly_deactivated = true;
            if self.needs_rebuild {
                // Dirty state is rebuilt wholesale later (watch lists
                // included), exactly like the single-row eager path.
                continue;
            }
            watch_indices.clear();
            self.collect_unique_watched_indices(cid, &mut watch_indices);
            for &watch_idx in &watch_indices {
                removals_by_bucket.entry(watch_idx).or_default().push(cid);
            }
        }
        watch_indices.clear();
        self.watch_build_scratch = watch_indices;
        if !any_newly_deactivated || self.needs_rebuild {
            return;
        }

        // One retain per affected bucket. Membership is tested via a scratch
        // mark vector (set, retain, clear) — O(1) per entry, no hashing.
        let mut removal_marks = vec![false; self.constraints.len()];
        for (watch_idx, bucket_cids) in removals_by_bucket {
            for &cid in &bucket_cids {
                removal_marks[cid] = true;
            }
            if let Some(watch_list) = self.watches.get_mut(watch_idx) {
                watch_list.retain(|&c| !removal_marks.get(c).copied().unwrap_or(false));
            }
            for &cid in &bucket_cids {
                removal_marks[cid] = false;
            }
        }
    }

    /// Returns whether the constraint at `cid` is active.
    #[must_use]
    pub fn is_constraint_active(&self, cid: usize) -> bool {
        self.constraints.get(cid).is_some_and(|c| c.active)
    }

    // -----------------------------------------------------------------------
    // Internal: constraint addition
    // -----------------------------------------------------------------------

    fn add_ge_constraint(&mut self, terms: &[PbTerm], rhs: i128) -> Option<usize> {
        let (mut normalized_terms, adjusted_rhs) = normalize_ge_terms(terms, rhs);

        if adjusted_rhs <= 0 {
            return None;
        }

        // Sort by descending coefficient (largest first) for watch selection.
        normalized_terms.sort_by(|lhs, rhs| {
            rhs.coeff
                .cmp(&lhs.coeff)
                .then_with(|| lhs.lit.unsigned_abs().cmp(&rhs.lit.unsigned_abs()))
                .then_with(|| lhs.lit.cmp(&rhs.lit))
        });

        // Ensure assignment and watch capacity once. Every smaller variable is
        // covered by the max variable's dense assignment/watch arrays.
        if let Some(max_var) = normalized_terms
            .iter()
            .filter_map(|term| lit_var(term.lit))
            .max()
        {
            self.assignment.ensure_var(max_var);
            self.ensure_watch_capacity(max_var);
        }

        let cid = self.constraints.len();
        let shape = classify_constraint_shape(&normalized_terms, adjusted_rhs);
        let counting = should_use_counting(shape, &normalized_terms, adjusted_rhs);
        let native_lits = native_lits_for_shape(shape, &normalized_terms);
        self.constraints.push(PropConstraint {
            terms: normalized_terms,
            native_lits,
            degree: adjusted_rhs,
            shape,
            watch_end: 0,
            slack: 0,
            active: true,
            watched_sum: 0,
            max_watched_coeff: 0,
            max_unwatched_coeff: 0,
            weighted_replacement_scan_hint: 0,
            counting,
            counting_lit_coeffs: Vec::new(),
            watch_all: false,
            event_epoch: 0,
        });

        // Initialize watched region and add to watch lists.
        if shape == ConstraintShape::TernaryClause {
            self.initialize_ternary_clause_watched_region(cid);
        } else {
            self.initialize_sorted_watched_region(cid);
            self.recalculate_slack(cid);
        }
        self.add_constraint_watches(cid);
        self.record_constraint_falsified_watch_events(cid);
        // A region born blind (constraints added mid-search: learned rows,
        // objective bounds) arms full visibility (P2d). TernaryClause skips
        // `recalculate_slack` (slack pinned 0), so it uses the false-watched
        // test instead of the slack rule.
        if shape == ConstraintShape::TernaryClause {
            if self.watched_region_has_false_lit(cid) {
                self.arm_watch_all(cid);
            }
        } else {
            self.arm_watch_all_if_blind(cid);
        }
        self.in_pending_check.push(false);
        debug_assert_eq!(self.in_pending_check.len(), self.constraints.len());
        // A newly added constraint may already propagate (or conflict) under
        // the current assignment; queue it so event-driven fixpoint drivers
        // check it without a full rescan. While a full scan is still pending
        // (construction / post-rebuild) the scan itself covers this cid, so
        // skip the redundant queue entry.
        if self.full_scan_done {
            self.queue_pending_check(cid);
        }
        Some(cid)
    }

    fn add_constraint_interruptible<F>(
        &mut self,
        terms: &[PbTerm],
        rel: PbRel,
        rhs: i128,
        should_stop: &mut F,
    ) -> Result<Option<usize>, ()>
    where
        F: FnMut() -> bool,
    {
        let mut first_id = self.add_ge_constraint_interruptible(terms, rhs, should_stop)?;

        if rel == PbRel::Eq {
            let mut negated_terms = Vec::with_capacity(terms.len());
            let mut poll_budget = STOP_POLL_INTERVAL;
            for term in terms {
                if should_interrupt(should_stop, &mut poll_budget) {
                    return Err(());
                }
                negated_terms.push(PbTerm {
                    coeff: -term.coeff,
                    lits: term.lits.clone(),
                });
            }

            let second_id =
                self.add_ge_constraint_interruptible(&negated_terms, -rhs, should_stop)?;
            if first_id.is_none() {
                first_id = second_id;
            }
        }

        Ok(first_id)
    }

    fn add_ge_constraint_interruptible<F>(
        &mut self,
        terms: &[PbTerm],
        rhs: i128,
        should_stop: &mut F,
    ) -> Result<Option<usize>, ()>
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return Err(());
        }

        let (mut normalized_terms, adjusted_rhs) =
            normalize_ge_terms_interruptible(terms, rhs, should_stop)?;

        if adjusted_rhs <= 0 {
            return Ok(None);
        }

        sort_prop_terms_interruptible(&mut normalized_terms, should_stop)?;

        let mut max_var = None;
        let mut poll_budget = STOP_POLL_INTERVAL;
        for term in &normalized_terms {
            if should_interrupt(should_stop, &mut poll_budget) {
                return Err(());
            }
            if let Some(var) = lit_var(term.lit) {
                max_var = Some(max_var.map_or(var, |existing: u32| existing.max(var)));
            }
        }

        if let Some(max_var) = max_var {
            if should_stop() {
                return Err(());
            }
            self.assignment.ensure_var(max_var);
            if should_stop() {
                return Err(());
            }
            self.ensure_watch_capacity(max_var);
        }

        let cid = self.constraints.len();
        let shape =
            classify_constraint_shape_interruptible(&normalized_terms, adjusted_rhs, should_stop)?;
        let counting = should_use_counting(shape, &normalized_terms, adjusted_rhs);
        let native_lits = native_lits_for_shape(shape, &normalized_terms);
        self.constraints.push(PropConstraint {
            terms: normalized_terms,
            native_lits,
            degree: adjusted_rhs,
            shape,
            watch_end: 0,
            slack: 0,
            active: true,
            watched_sum: 0,
            max_watched_coeff: 0,
            max_unwatched_coeff: 0,
            weighted_replacement_scan_hint: 0,
            counting,
            counting_lit_coeffs: Vec::new(),
            watch_all: false,
            event_epoch: 0,
        });

        if shape == ConstraintShape::TernaryClause {
            if should_stop() {
                return Err(());
            }
            self.initialize_ternary_clause_watched_region(cid);
        } else {
            if self.initialize_sorted_watched_region_interruptible(cid, should_stop) {
                return Err(());
            }
            if self.recalculate_slack_interruptible(cid, should_stop) {
                return Err(());
            }
        }
        if self.add_constraint_watches_interruptible(cid, should_stop) {
            return Err(());
        }
        self.record_constraint_falsified_watch_events(cid);
        // See `add_ge_constraint`: a region born blind arms full visibility
        // (P2d).
        if shape == ConstraintShape::TernaryClause {
            if self.watched_region_has_false_lit(cid) {
                self.arm_watch_all(cid);
            }
        } else {
            self.arm_watch_all_if_blind(cid);
        }
        self.in_pending_check.push(false);
        debug_assert_eq!(self.in_pending_check.len(), self.constraints.len());
        // See `add_ge_constraint`: a new constraint may already propagate, and
        // a still-pending full scan covers it without a queue entry.
        if self.full_scan_done {
            self.queue_pending_check(cid);
        }
        Ok(Some(cid))
    }

    fn swap_constraint_terms(&mut self, cid: usize, lhs: usize, rhs: usize) {
        let constraint = &mut self.constraints[cid];
        constraint.terms.swap(lhs, rhs);
        if !constraint.native_lits.is_empty() {
            debug_assert_eq!(constraint.native_lits.len(), constraint.terms.len());
            constraint.native_lits.swap(lhs, rhs);
        }
    }

    fn ensure_rebuilt(&mut self) {
        if !self.needs_rebuild {
            return;
        }
        self.rebuild_all_constraint_state();
    }

    fn ensure_rebuilt_interruptible<F>(&mut self, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        if !self.needs_rebuild {
            return false;
        }
        self.rebuild_all_constraint_state_interruptible(should_stop)
    }

    // -----------------------------------------------------------------------
    // Internal: watched region initialization and maintenance
    // -----------------------------------------------------------------------

    /// Initializes the watched region for constraint `cid`.
    ///
    /// The RoundingSat invariant requires:
    ///   `watched_sum >= degree + max_unwatched_coeff`
    ///
    /// Initial addition sorts terms by descending coefficient, but incremental
    /// watch swaps can perturb that order before a later rebuild. Compute
    /// suffix maxima over the current order so the invariant is restored even
    /// when the largest unwatched coefficient is not the first unwatched term.
    fn initialize_watched_region(&mut self, cid: usize) {
        if self.constraints[cid].counting {
            self.initialize_counting_watched_region(cid);
            return;
        }
        let constraint = &mut self.constraints[cid];
        let degree = constraint.degree;
        let n = constraint.terms.len();
        let mut suffix_max_coeff = vec![0i128; n + 1];
        for idx in (0..n).rev() {
            suffix_max_coeff[idx] = suffix_max_coeff[idx + 1].max(constraint.terms[idx].coeff);
        }

        let mut watch_end = 0usize;
        let mut watched_sum = 0i128;

        // Add terms until watched_sum >= degree + max_unwatched_coeff.
        loop {
            let max_unwatched = suffix_max_coeff[watch_end];
            let threshold = degree.saturating_add(max_unwatched);

            if watched_sum >= threshold || watch_end >= n {
                break;
            }

            watched_sum = watched_sum.saturating_add(constraint.terms[watch_end].coeff);
            watch_end += 1;
        }

        constraint.watch_end = watch_end;
        constraint.watched_sum = watched_sum;
        constraint.max_watched_coeff = constraint.terms[..watch_end]
            .iter()
            .map(|term| term.coeff)
            .max()
            .unwrap_or(0);
        constraint.max_unwatched_coeff = suffix_max_coeff[watch_end];
        constraint.weighted_replacement_scan_hint = watch_end;
    }

    /// Initializes the watched region for a freshly added constraint.
    ///
    /// Fresh constraints are sorted by descending coefficient, so the strongest
    /// unwatched coefficient is simply the first unwatched term. Rebuilds use
    /// `initialize_watched_region`, which tolerates swap-perturbed term order.
    fn initialize_sorted_watched_region(&mut self, cid: usize) {
        if self.constraints[cid].counting {
            self.initialize_counting_watched_region(cid);
            return;
        }
        let constraint = &mut self.constraints[cid];
        let degree = constraint.degree;
        let n = constraint.terms.len();
        let mut watch_end = 0usize;
        let mut watched_sum = 0i128;

        loop {
            let max_unwatched = constraint.terms.get(watch_end).map_or(0, |term| term.coeff);
            let threshold = degree.saturating_add(max_unwatched);

            if watched_sum >= threshold || watch_end >= n {
                break;
            }

            watched_sum = watched_sum.saturating_add(constraint.terms[watch_end].coeff);
            watch_end += 1;
        }

        constraint.watch_end = watch_end;
        constraint.watched_sum = watched_sum;
        constraint.max_watched_coeff = if watch_end == 0 {
            0
        } else {
            constraint.terms[0].coeff
        };
        constraint.max_unwatched_coeff =
            constraint.terms.get(watch_end).map_or(0, |term| term.coeff);
        constraint.weighted_replacement_scan_hint = watch_end;
    }

    /// Watches every term of a counting constraint (`watch_end == terms.len()`).
    ///
    /// With all terms watched there is no unwatched region, so no swaps ever
    /// occur and the descending-coefficient order is preserved for the lifetime
    /// of the constraint. `slack` (recomputed by the caller via
    /// `recalculate_slack`) then equals the exact slack over all terms.
    fn initialize_counting_watched_region(&mut self, cid: usize) {
        let constraint = &mut self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        debug_assert!(constraint.counting);
        let n = constraint.terms.len();
        constraint.watch_end = n;
        constraint.watched_sum = constraint.terms[..n]
            .iter()
            .map(|term| term.coeff)
            .fold(0i128, i128::saturating_add);
        constraint.max_watched_coeff = constraint.terms.first().map_or(0, |term| term.coeff);
        constraint.max_unwatched_coeff = 0;
        constraint.weighted_replacement_scan_hint = n;

        // Build the lit -> summed-coeff lookup (sorted by lit), aggregating any
        // duplicate occurrences of the same literal so a falsification decrements
        // slack by the literal's total coefficient in one step.
        let mut lit_coeffs = std::mem::take(&mut constraint.counting_lit_coeffs);
        lit_coeffs.clear();
        lit_coeffs.reserve(n);
        for term in &constraint.terms {
            lit_coeffs.push((term.lit, term.coeff));
        }
        lit_coeffs.sort_unstable_by_key(|&(lit, _)| lit);
        // Merge duplicate literals into a single entry holding the coeff sum.
        let mut write = 0usize;
        let mut read = 0usize;
        while read < lit_coeffs.len() {
            let lit = lit_coeffs[read].0;
            let mut sum = 0i128;
            while read < lit_coeffs.len() && lit_coeffs[read].0 == lit {
                sum = sum.saturating_add(lit_coeffs[read].1);
                read += 1;
            }
            lit_coeffs[write] = (lit, sum);
            write += 1;
        }
        lit_coeffs.truncate(write);
        self.constraints[cid].counting_lit_coeffs = lit_coeffs;
    }

    /// Returns the total coefficient with which counting constraint `cid`
    /// contains `lit`, or 0 if `lit` does not appear. O(log n) via the
    /// `counting_lit_coeffs` lookup.
    fn counting_lit_coeff(&self, cid: usize, lit: Lit) -> i128 {
        let table = &self.constraints[cid].counting_lit_coeffs;
        match table.binary_search_by_key(&lit, |&(entry_lit, _)| entry_lit) {
            Ok(idx) => table[idx].1,
            Err(_) => 0,
        }
    }

    fn initialize_sorted_watched_region_interruptible<F>(
        &mut self,
        cid: usize,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return true;
        }

        if self.constraints[cid].counting {
            self.initialize_counting_watched_region(cid);
            return false;
        }

        let constraint = &mut self.constraints[cid];
        let degree = constraint.degree;
        let n = constraint.terms.len();
        let mut watch_end = 0usize;
        let mut watched_sum = 0i128;
        let mut poll_budget = STOP_POLL_INTERVAL;

        loop {
            if should_interrupt(should_stop, &mut poll_budget) {
                return true;
            }

            let max_unwatched = constraint.terms.get(watch_end).map_or(0, |term| term.coeff);
            let threshold = degree.saturating_add(max_unwatched);

            if watched_sum >= threshold || watch_end >= n {
                break;
            }

            watched_sum = watched_sum.saturating_add(constraint.terms[watch_end].coeff);
            watch_end += 1;
        }

        constraint.watch_end = watch_end;
        constraint.watched_sum = watched_sum;
        constraint.max_watched_coeff = if watch_end == 0 {
            0
        } else {
            constraint.terms[0].coeff
        };
        constraint.max_unwatched_coeff =
            constraint.terms.get(watch_end).map_or(0, |term| term.coeff);
        constraint.weighted_replacement_scan_hint = watch_end;
        false
    }

    fn initialize_ternary_clause_watched_region(&mut self, cid: usize) {
        let constraint = &mut self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::TernaryClause);
        debug_assert_eq!(constraint.terms.len(), 3);
        debug_assert_eq!(constraint.degree, 1);
        debug_assert!(constraint.terms.iter().all(|term| term.coeff == 1));

        constraint.watch_end = 2;
        constraint.slack = 0;
        constraint.watched_sum = 2;
        constraint.max_watched_coeff = 1;
        constraint.max_unwatched_coeff = 1;
        constraint.weighted_replacement_scan_hint = constraint.watch_end;
    }

    #[cfg(test)]
    fn record_clause_check(&self) {
        self.stats
            .clause_checks
            .set(self.stats.clause_checks.get().saturating_add(1));
    }

    #[cfg(test)]
    fn record_unit_cardinality_check(&self) {
        self.stats
            .unit_cardinality_checks
            .set(self.stats.unit_cardinality_checks.get().saturating_add(1));
    }

    #[cfg(test)]
    fn record_weighted_check(&self) {
        self.stats
            .weighted_checks
            .set(self.stats.weighted_checks.get().saturating_add(1));
    }

    #[cfg(test)]
    fn record_clause_watch_shortcut(&self) {
        self.stats
            .clause_watch_shortcuts
            .set(self.stats.clause_watch_shortcuts.get().saturating_add(1));
    }

    #[cfg(test)]
    fn record_unit_cardinality_watch_shortcut(&self) {
        self.stats.unit_cardinality_watch_shortcuts.set(
            self.stats
                .unit_cardinality_watch_shortcuts
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_unit_cardinality_slack_shortcut(&self) {
        self.stats.unit_cardinality_slack_shortcuts.set(
            self.stats
                .unit_cardinality_slack_shortcuts
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_unit_cardinality_full_scan(&self) {
        self.stats.unit_cardinality_full_scans.set(
            self.stats
                .unit_cardinality_full_scans
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_unit_cardinality_scan_term(&self) {
        self.stats.unit_cardinality_scan_terms.set(
            self.stats
                .unit_cardinality_scan_terms
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_weighted_slack_shortcut(&self) {
        self.stats
            .weighted_slack_shortcuts
            .set(self.stats.weighted_slack_shortcuts.get().saturating_add(1));
    }

    #[cfg(test)]
    fn record_weighted_no_replacement_shortcut(&self) {
        self.stats.weighted_no_replacement_shortcuts.set(
            self.stats
                .weighted_no_replacement_shortcuts
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_weighted_exact_slack_scan(&self) {
        self.stats.weighted_exact_slack_scans.set(
            self.stats
                .weighted_exact_slack_scans
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_slack_recalculation(&self) {
        self.stats
            .slack_recalculations
            .set(self.stats.slack_recalculations.get().saturating_add(1));
    }

    #[cfg(test)]
    fn record_coefficient_bound_recomputation(&self) {
        self.stats.coefficient_bound_recomputations.set(
            self.stats
                .coefficient_bound_recomputations
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_unwatched_replacement_candidate(&self) {
        self.stats.unwatched_replacement_candidates.set(
            self.stats
                .unwatched_replacement_candidates
                .get()
                .saturating_add(1),
        );
    }

    #[cfg(test)]
    fn record_unwatched_replacement_value_check(&self) {
        self.stats.unwatched_replacement_value_checks.set(
            self.stats
                .unwatched_replacement_value_checks
                .get()
                .saturating_add(1),
        );
    }

    fn update_native_helper_stats(&self, update: impl FnOnce(&mut PbNativeHelperStats)) {
        let mut stats = self.native_helper_stats.get();
        update(&mut stats);
        self.native_helper_stats.set(stats);
    }

    fn record_native_helper_evaluation(&self) {
        self.update_native_helper_stats(|stats| {
            stats.evaluation_attempts = stats.evaluation_attempts.saturating_add(1);
        });
    }

    fn record_native_helper_native_apply_attempt(&self) {
        self.update_native_helper_stats(|stats| {
            stats.native_apply_attempts = stats.native_apply_attempts.saturating_add(1);
        });
    }

    fn record_native_helper_scalar_confirmation(&self) {
        self.update_native_helper_stats(|stats| {
            stats.scalar_confirmation_checks = stats.scalar_confirmation_checks.saturating_add(1);
        });
    }

    fn record_native_helper_native_apply_confirmation(&self) {
        self.update_native_helper_stats(|stats| {
            stats.native_apply_confirmations = stats.native_apply_confirmations.saturating_add(1);
        });
    }

    fn record_native_helper_scalar_shadow_application(&self) {
        self.update_native_helper_stats(|stats| {
            stats.scalar_shadow_applications = stats.scalar_shadow_applications.saturating_add(1);
        });
    }

    fn record_native_helper_deopt(&self) {
        self.update_native_helper_stats(|stats| {
            stats.deopts = stats.deopts.saturating_add(1);
        });
    }

    fn record_native_helper_scalar_fallback(&self) {
        self.update_native_helper_stats(|stats| {
            stats.scalar_fallbacks = stats.scalar_fallbacks.saturating_add(1);
        });
    }

    fn should_try_native_code_helper(&self) -> bool {
        self.native_code_helper_validation_enabled && !self.native_code_helper_deopted.get()
    }

    fn validated_native_code_helper_result(
        &self,
        helper: PropResult,
        scalar: PropResult,
        source: NativeHelperSource,
    ) -> PropResult {
        self.record_native_helper_scalar_confirmation();

        #[cfg(test)]
        let helper = if self.force_next_native_code_helper_mismatch.replace(false) {
            PropResult::Ok
        } else {
            helper
        };

        if helper == scalar {
            match source {
                NativeHelperSource::NativeAbi => {
                    self.record_native_helper_native_apply_confirmation();
                }
                NativeHelperSource::ScalarShadow => {
                    self.record_native_helper_scalar_shadow_application();
                }
            }
            return helper;
        }

        self.native_code_helper_deopted.set(true);
        self.record_native_helper_deopt();
        self.record_native_helper_scalar_fallback();
        scalar
    }

    fn unit_cardinality_native_code_helper(&self, cid: usize) -> NativeHelperAttempt {
        if self.unit_cardinality_has_sufficient_watched_slack(cid) {
            return NativeHelperAttempt::Evaluated {
                result: PropResult::Ok,
                source: NativeHelperSource::ScalarShadow,
            };
        }

        self.apply_unit_cardinality_native_or_shadow(cid, None::<&mut fn() -> bool>)
    }

    fn unit_cardinality_native_code_helper_interruptible<F>(
        &self,
        cid: usize,
        should_stop: &mut F,
    ) -> NativeHelperAttempt
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return NativeHelperAttempt::Interrupted;
        }
        if self.unit_cardinality_has_sufficient_watched_slack(cid) {
            return NativeHelperAttempt::Evaluated {
                result: PropResult::Ok,
                source: NativeHelperSource::ScalarShadow,
            };
        }

        self.apply_unit_cardinality_native_or_shadow(cid, Some(should_stop))
    }

    fn apply_unit_cardinality_native_or_shadow<F>(
        &self,
        cid: usize,
        should_stop: Option<&mut F>,
    ) -> NativeHelperAttempt
    where
        F: FnMut() -> bool,
    {
        {
            NativeHelperAttempt::Evaluated {
                result: self.unit_cardinality_native_code_helper_scan(cid, should_stop),
                source: NativeHelperSource::ScalarShadow,
            }
        }
    }

    fn apply_unit_cardinality_native_abi(&self, cid: usize) -> NativeHelperAttempt {
        if !self.ensure_unit_cardinality_native_helper() {
            return NativeHelperAttempt::Fallback;
        }

        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::UnitCardinality);
        if constraint.native_lits.len() != constraint.terms.len() {
            self.native_code_helper_deopted.set(true);
            self.record_native_helper_deopt();
            return NativeHelperAttempt::Fallback;
        }
        debug_assert!(self.unit_cardinality_native_abi_mirrors_constraint_and_assignment(cid));

        #[cfg(test)]
        let forced_invalid_lits = [i64::MIN, 1, 2];
        #[cfg(test)]
        let native_lits = if self.force_next_native_code_helper_invalid.replace(false) {
            forced_invalid_lits.as_slice()
        } else {
            constraint.native_lits.as_slice()
        };
        #[cfg(not(test))]
        let native_lits = constraint.native_lits.as_slice();

        self.record_native_helper_native_apply_attempt();
        let Some(output) = self.apply_compiled_unit_cardinality_native_helper(
            self.assignment.native_values(),
            native_lits,
            constraint.degree,
        ) else {
            self.native_code_helper_deopted.set(true);
            self.record_native_helper_deopt();
            return NativeHelperAttempt::Fallback;
        };

        if output.status == PB_UNIT_CARDINALITY_NATIVE_OK
            && output.first_unassigned_index == PB_NATIVE_FIRST_UNASSIGNED_SENTINEL
            && self.can_trust_unit_cardinality_native_ok(output)
        {
            return NativeHelperAttempt::TrustedNativeOk;
        }

        let Some(result) = self.unit_cardinality_result_from_native_output(cid, output) else {
            self.native_code_helper_deopted.set(true);
            self.record_native_helper_deopt();
            return NativeHelperAttempt::Fallback;
        };

        NativeHelperAttempt::Evaluated {
            result,
            source: NativeHelperSource::NativeAbi,
        }
    }

    fn can_trust_unit_cardinality_native_ok(&self, output: PbUnitCardinalityNativeOutput) -> bool {
        output.status == PB_UNIT_CARDINALITY_NATIVE_OK
            && output.first_unassigned_index == PB_NATIVE_FIRST_UNASSIGNED_SENTINEL
            && !self.native_code_helper_mismatch_for_test_is_armed()
    }

    fn unit_cardinality_native_abi_mirrors_constraint_and_assignment(&self, cid: usize) -> bool {
        let constraint = &self.constraints[cid];
        constraint.native_lits.len() == constraint.terms.len()
            && constraint
                .native_lits
                .iter()
                .zip(constraint.terms.iter())
                .all(|(&native_lit, term)| {
                    native_lit == i64::from(term.lit)
                        && self.assignment.native_value_mirrors_assignment(term.lit)
                })
    }

    #[cfg(test)]
    fn native_code_helper_mismatch_for_test_is_armed(&self) -> bool {
        self.force_next_native_code_helper_mismatch.get()
    }

    #[cfg(not(test))]
    fn native_code_helper_mismatch_for_test_is_armed(&self) -> bool {
        false
    }

    fn ensure_unit_cardinality_native_helper(&self) -> bool {
        false
    }

    fn apply_compiled_unit_cardinality_native_helper(
        &self,
        _assignment_values: &[i64],
        _lits: &[i64],
        _degree: i128,
    ) -> Option<PbUnitCardinalityNativeOutput> {
        None
    }

    fn unit_cardinality_result_from_native_output(
        &self,
        cid: usize,
        output: PbUnitCardinalityNativeOutput,
    ) -> Option<PropResult> {
        match output.status {
            PB_UNIT_CARDINALITY_NATIVE_OK => Some(PropResult::Ok),
            PB_UNIT_CARDINALITY_NATIVE_CONFLICT => {
                Some(PropResult::Conflict(self.conflict_reason(cid), cid))
            }
            PB_UNIT_CARDINALITY_NATIVE_PROPAGATE => {
                let first_unassigned_index = usize::try_from(output.first_unassigned_index).ok()?;
                let term = self.constraints[cid].terms.get(first_unassigned_index)?;
                if self.assignment.value(term.lit) != LitValue::Unassigned {
                    return None;
                }
                Some(PropResult::Propagated(
                    term.lit,
                    self.propagation_reason(cid, term.lit),
                    cid,
                ))
            }
            PB_UNIT_CARDINALITY_NATIVE_INVALID => None,
            _ => None,
        }
    }

    fn unit_cardinality_native_code_helper_scan<F>(
        &self,
        cid: usize,
        mut should_stop: Option<&mut F>,
    ) -> PropResult
    where
        F: FnMut() -> bool,
    {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::UnitCardinality);

        let mut non_false_count = 0i128;
        let mut first_unassigned = None;
        let mut false_lits = ReasonBuf::new();
        let mut poll_budget = STOP_POLL_INTERVAL;

        for term in &constraint.terms {
            if let Some(stop) = should_stop.as_mut() {
                if should_interrupt(*stop, &mut poll_budget) {
                    return PropResult::Interrupted;
                }
            }

            match self.assignment.value(term.lit) {
                LitValue::True => {
                    non_false_count = non_false_count.saturating_add(1);
                    if non_false_count > constraint.degree {
                        return PropResult::Ok;
                    }
                }
                LitValue::Unassigned => {
                    non_false_count = non_false_count.saturating_add(1);
                    if non_false_count > constraint.degree {
                        return PropResult::Ok;
                    }
                    if first_unassigned.is_none() {
                        first_unassigned = Some(term.lit);
                    }
                }
                LitValue::False => false_lits.push_false(term.lit),
            }
        }

        if non_false_count < constraint.degree {
            return PropResult::Conflict(false_lits.into_reason(), cid);
        }

        if non_false_count == constraint.degree {
            if let Some(lit) = first_unassigned {
                return PropResult::Propagated(lit, false_lits.into_propagation_reason(lit), cid);
            }
        }

        PropResult::Ok
    }

    fn check_unit_cardinality_no_unwatched_non_false(&self, cid: usize) -> PropResult {
        debug_assert_eq!(
            self.constraints[cid].shape,
            ConstraintShape::UnitCardinality
        );

        #[cfg(test)]
        self.record_unit_cardinality_check();

        let constraint = &self.constraints[cid];
        let watched_non_false_count = constraint.degree.saturating_add(constraint.slack);

        if watched_non_false_count < constraint.degree {
            #[cfg(test)]
            self.record_unit_cardinality_watch_shortcut();
            return PropResult::Conflict(self.conflict_reason(cid), cid);
        }

        if watched_non_false_count == constraint.degree {
            #[cfg(test)]
            self.record_unit_cardinality_watch_shortcut();
            for term in &constraint.terms[..constraint.watch_end] {
                if self.assignment.value(term.lit) == LitValue::Unassigned {
                    return PropResult::Propagated(
                        term.lit,
                        self.propagation_reason(cid, term.lit),
                        cid,
                    );
                }
            }
            return PropResult::Ok;
        }

        #[cfg(test)]
        self.record_unit_cardinality_watch_shortcut();
        PropResult::Ok
    }

    fn unit_cardinality_has_sufficient_watched_slack(&self, cid: usize) -> bool {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::UnitCardinality);
        constraint.slack > 0
    }

    fn weighted_has_sufficient_watched_slack(&self, cid: usize) -> bool {
        let constraint = &self.constraints[cid];
        debug_assert_eq!(constraint.shape, ConstraintShape::Weighted);
        constraint.slack >= constraint.max_watched_coeff
    }

    // -----------------------------------------------------------------------
    // Internal: slack calculation
    // -----------------------------------------------------------------------

    /// Recalculates the slack for constraint `cid`.
    ///
    /// slack = sum(coeff of non-false watched terms) - degree
    fn recalculate_slack(&mut self, cid: usize) {
        #[cfg(test)]
        self.record_slack_recalculation();

        let degree = self.constraints[cid].degree;
        let mut slack = -degree;

        for term in &self.constraints[cid].terms[..self.constraints[cid].watch_end] {
            if self.assignment.value(term.lit) != LitValue::False {
                slack = slack.saturating_add(term.coeff);
            }
        }

        self.constraints[cid].slack = slack;
    }

    fn recalculate_slack_interruptible<F>(&mut self, cid: usize, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        #[cfg(test)]
        self.record_slack_recalculation();

        if should_stop() {
            return true;
        }

        let degree = self.constraints[cid].degree;
        let mut slack = -degree;
        let mut poll_budget = STOP_POLL_INTERVAL;

        for term in &self.constraints[cid].terms[..self.constraints[cid].watch_end] {
            if should_interrupt(should_stop, &mut poll_budget) {
                return true;
            }
            if self.assignment.value(term.lit) != LitValue::False {
                slack = slack.saturating_add(term.coeff);
            }
        }

        self.constraints[cid].slack = slack;
        false
    }

    fn adjust_slack_for_falsified_watch(&mut self, cid: usize, lit: Lit, coeff: i128) {
        self.constraints[cid].slack = self.constraints[cid].slack.saturating_sub(coeff);
        self.add_falsified_watch_event(lit, cid);
    }

    fn adjust_slack_for_non_false_watch(&mut self, cid: usize, coeff: i128) {
        self.constraints[cid].slack = self.constraints[cid].slack.saturating_add(coeff);
    }

    fn add_falsified_watch_event(&mut self, lit: Lit, cid: usize) {
        let Some(lit_idx) = lit_index(lit) else {
            return;
        };
        if self.falsified_watch_events.len() <= lit_idx {
            self.falsified_watch_events
                .resize_with(lit_idx + 1, Vec::new);
        }
        let epoch = self
            .constraints
            .get(cid)
            .map_or(0, |constraint| constraint.event_epoch);
        #[cfg(debug_assertions)]
        debug_assert!(
            !self.falsified_watch_events[lit_idx]
                .iter()
                .any(|&(event_cid, event_epoch)| event_cid == cid && event_epoch == epoch),
            "falsified watch event already recorded for literal {lit} and constraint {cid}"
        );
        self.falsified_watch_events[lit_idx].push((cid, epoch));
    }

    fn exact_weighted_slack(&self, cid: usize) -> i128 {
        debug_assert_eq!(self.constraints[cid].shape, ConstraintShape::Weighted);
        #[cfg(test)]
        self.record_weighted_exact_slack_scan();

        self.constraints[cid]
            .terms
            .iter()
            .filter(|term| self.assignment.value(term.lit) != LitValue::False)
            .fold(-self.constraints[cid].degree, |slack, term| {
                slack.saturating_add(term.coeff)
            })
    }

    fn exact_weighted_slack_interruptible<F>(&self, cid: usize, should_stop: &mut F) -> Option<i128>
    where
        F: FnMut() -> bool,
    {
        debug_assert_eq!(self.constraints[cid].shape, ConstraintShape::Weighted);
        #[cfg(test)]
        self.record_weighted_exact_slack_scan();

        let mut slack = -self.constraints[cid].degree;
        let mut poll_budget = STOP_POLL_INTERVAL;
        for term in &self.constraints[cid].terms {
            if should_interrupt(should_stop, &mut poll_budget) {
                return None;
            }
            if self.assignment.value(term.lit) != LitValue::False {
                slack = slack.saturating_add(term.coeff);
            }
        }
        Some(slack)
    }

    fn update_weighted_swap_coefficient_bounds(
        &mut self,
        cid: usize,
        watched_idx: usize,
        old_max_watched_coeff: i128,
        old_max_unwatched_coeff: i128,
        falsified_coeff: i128,
        candidate_coeff: i128,
    ) {
        debug_assert_eq!(self.constraints[cid].shape, ConstraintShape::Weighted);
        self.update_weighted_swap_max_watched(
            cid,
            watched_idx,
            old_max_watched_coeff,
            falsified_coeff,
            candidate_coeff,
        );
        self.update_weighted_swap_max_unwatched(
            cid,
            old_max_unwatched_coeff,
            falsified_coeff,
            candidate_coeff,
        );
    }

    fn update_weighted_swap_max_watched(
        &mut self,
        cid: usize,
        watched_idx: usize,
        old_max_watched_coeff: i128,
        falsified_coeff: i128,
        candidate_coeff: i128,
    ) {
        let watch_end = self.constraints[cid].watch_end;

        if watch_end <= 2 {
            let mut max_coeff = 0i128;
            for term in &self.constraints[cid].terms[..watch_end] {
                if term.coeff > max_coeff {
                    max_coeff = term.coeff;
                }
            }
            self.constraints[cid].max_watched_coeff = max_coeff;
            return;
        }

        if falsified_coeff < old_max_watched_coeff {
            self.constraints[cid].max_watched_coeff = old_max_watched_coeff.max(candidate_coeff);
        } else if candidate_coeff >= old_max_watched_coeff {
            self.constraints[cid].max_watched_coeff = candidate_coeff;
        } else {
            debug_assert!(watched_idx < watch_end);
            self.recompute_max_watched(cid);
        }
    }

    fn update_weighted_swap_max_unwatched(
        &mut self,
        cid: usize,
        old_max_unwatched_coeff: i128,
        falsified_coeff: i128,
        candidate_coeff: i128,
    ) {
        let watch_end = self.constraints[cid].watch_end;
        let unwatched_len = self.constraints[cid].terms.len() - watch_end;

        if unwatched_len <= 2 {
            let mut max_coeff = 0i128;
            for term in &self.constraints[cid].terms[watch_end..] {
                if term.coeff > max_coeff {
                    max_coeff = term.coeff;
                }
            }
            self.constraints[cid].max_unwatched_coeff = max_coeff;
            return;
        }

        if candidate_coeff < old_max_unwatched_coeff {
            self.constraints[cid].max_unwatched_coeff =
                old_max_unwatched_coeff.max(falsified_coeff);
        } else if falsified_coeff >= old_max_unwatched_coeff {
            self.constraints[cid].max_unwatched_coeff = falsified_coeff;
        } else {
            self.recompute_max_unwatched(cid);
        }
    }

    /// Recomputes max_watched_coeff by scanning the watched region.
    fn recompute_max_watched(&mut self, cid: usize) {
        #[cfg(test)]
        self.record_coefficient_bound_recomputation();

        let watch_end = self.constraints[cid].watch_end;
        let mut max_coeff = 0i128;
        for term in &self.constraints[cid].terms[..watch_end] {
            if term.coeff > max_coeff {
                max_coeff = term.coeff;
            }
        }
        self.constraints[cid].max_watched_coeff = max_coeff;
    }

    /// Recomputes max_unwatched_coeff by scanning the unwatched region.
    fn recompute_max_unwatched(&mut self, cid: usize) {
        #[cfg(test)]
        self.record_coefficient_bound_recomputation();

        let watch_end = self.constraints[cid].watch_end;
        let mut max_coeff = 0i128;
        for term in &self.constraints[cid].terms[watch_end..] {
            if term.coeff > max_coeff {
                max_coeff = term.coeff;
            }
        }
        self.constraints[cid].max_unwatched_coeff = max_coeff;
    }

    // -----------------------------------------------------------------------
    // Internal: rebuild (used after backtrack)
    // -----------------------------------------------------------------------

    fn rebuild_all_constraint_state(&mut self) {
        #[cfg(test)]
        {
            self.rebuild_count += 1;
        }
        // Watch/slack state is recomputed wholesale: any propagation the event
        // queue was tracking may be re-discoverable only by a fresh full scan.
        self.invalidate_full_scan();
        for cid in 0..self.constraints.len() {
            if !self.constraints[cid].active {
                continue;
            }
            if self.constraints[cid].shape == ConstraintShape::TernaryClause {
                self.initialize_ternary_clause_watched_region(cid);
                self.repair_watched_region(cid);
                if self.watched_region_has_false_lit(cid) {
                    self.arm_watch_all(cid);
                }
                continue;
            }
            self.initialize_watched_region(cid);
            self.repair_watched_region(cid);
            self.recalculate_slack(cid);
            // Blind after repair (see `arm_watch_all_if_blind`): arm full
            // visibility (P2d). `rebuild_all_watches` below honors the flag.
            self.arm_watch_all_if_blind(cid);
        }
        self.rebuild_all_watches();
        self.rebuild_falsified_watch_events();
        self.needs_rebuild = false;
    }

    fn repair_slack_after_unassign(&mut self, formerly_false_lits: &[Lit]) {
        if formerly_false_lits.is_empty() {
            return;
        }

        // Consume exactly the unassigned literals' event buckets: backtrack
        // cost is O(events of those literals), not O(all outstanding events)
        // (P2e). Entries whose row epoch moved on (counting conversion
        // re-recorded the row's events) are stale and dropped unconsumed.
        for &lit in formerly_false_lits {
            let Some(lit_idx) = lit_index(lit) else {
                continue;
            };
            let Some(bucket) = self.falsified_watch_events.get_mut(lit_idx) else {
                continue;
            };
            let mut events = std::mem::take(bucket);
            for &(cid, event_epoch) in &events {
                let constraint = self.constraints.get(cid);
                if constraint.is_none_or(|c| c.event_epoch != event_epoch) {
                    continue;
                }
                if let Some(restored_slack) = restored_slack_for_event(constraint, lit) {
                    if restored_slack != 0 {
                        self.adjust_slack_for_non_false_watch(cid, restored_slack);
                        // Late-added rows (objective bounds, imports) can stay
                        // conflicting or propagating across a backtrack; with
                        // the event-driven fixpoint (no per-call rescan) they
                        // must be re-queued here (P2d).
                        self.queue_pending_check_if_tight(cid);
                    }
                }
            }
            // Return the (cleared) bucket to keep its capacity.
            events.clear();
            self.falsified_watch_events[lit_idx] = events;
        }
    }

    fn repair_slack_after_unassign_interruptible<F>(
        &mut self,
        formerly_false_lits: &[Lit],
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        if formerly_false_lits.is_empty() {
            return false;
        }
        if should_stop() {
            self.needs_rebuild = true;
            return true;
        }

        // Bucketed consumption; see `repair_slack_after_unassign`. On
        // interrupt the partially consumed state is left dirty and
        // `needs_rebuild` forces the wholesale recompute before the next
        // propagation step, exactly like the historical list variant.
        let mut poll_budget = STOP_POLL_INTERVAL;
        for &lit in formerly_false_lits {
            let Some(lit_idx) = lit_index(lit) else {
                continue;
            };
            let Some(bucket) = self.falsified_watch_events.get_mut(lit_idx) else {
                continue;
            };
            let mut events = std::mem::take(bucket);
            for &(cid, event_epoch) in &events {
                if should_interrupt(should_stop, &mut poll_budget) {
                    self.needs_rebuild = true;
                    return true;
                }
                let constraint = self.constraints.get(cid);
                if constraint.is_none_or(|c| c.event_epoch != event_epoch) {
                    continue;
                }
                if let Some(restored_slack) = restored_slack_for_event(constraint, lit) {
                    if restored_slack != 0 {
                        self.adjust_slack_for_non_false_watch(cid, restored_slack);
                        // See `repair_slack_after_unassign`: re-queue rows that
                        // stay tight across the backtrack (P2d event-driven
                        // completeness).
                        self.queue_pending_check_if_tight(cid);
                    }
                }
            }
            // Return the (cleared) bucket to keep its capacity.
            events.clear();
            self.falsified_watch_events[lit_idx] = events;
        }
        false
    }

    fn rebuild_falsified_watch_events(&mut self) {
        self.falsified_watch_events.iter_mut().for_each(Vec::clear);
        self.falsified_watch_event_lits.clear();

        for cid in 0..self.constraints.len() {
            self.record_constraint_falsified_watch_events(cid);
        }
    }

    fn record_constraint_falsified_watch_events(&mut self, cid: usize) {
        let mut event_lits = std::mem::take(&mut self.falsified_watch_event_lits);
        event_lits.clear();

        if let Some(constraint) = self.constraints.get(cid) {
            if constraint.active && constraint.shape != ConstraintShape::TernaryClause {
                for term in &constraint.terms[..constraint.watch_end] {
                    if self.assignment.value(term.lit) == LitValue::False
                        && !event_lits.contains(&term.lit)
                    {
                        event_lits.push(term.lit);
                    }
                }
            }
        }

        for lit in event_lits.iter().copied() {
            self.add_falsified_watch_event(lit, cid);
        }
        event_lits.clear();
        self.falsified_watch_event_lits = event_lits;
    }

    fn rebuild_all_constraint_state_interruptible<F>(&mut self, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            self.needs_rebuild = true;
            return true;
        }

        #[cfg(test)]
        {
            self.rebuild_count += 1;
        }
        // See `rebuild_all_constraint_state`: force the next full scan.
        self.invalidate_full_scan();

        self.watches.iter_mut().for_each(Vec::clear);

        let mut constraint_budget = STOP_POLL_INTERVAL;
        for cid in 0..self.constraints.len() {
            if should_interrupt(should_stop, &mut constraint_budget) {
                self.needs_rebuild = true;
                return true;
            }
            if !self.constraints[cid].active {
                continue;
            }
            // ORDERING CONSTRAINT (D1): `add_constraint_watches` MUST run
            // BEFORE any arming / counting conversion. It uses UNCHECKED
            // watch inserts, which are only safe while this row's freshly
            // cleared lists hold no entry for it; `arm_watch_all_if_blind`
            // may convert the row to counting and add one entry per literal
            // via the deduplicating `add_watch`. In the reversed order the
            // unchecked inserts land ON TOP of the conversion's entries,
            // every literal holds `cid` twice, and the counting pre-pass
            // double-decrements the trusted exact slack — a spurious
            // conflict on a satisfiable row (wrong UNSAT at level 0 in
            // release). Arming AFTER is safe: it only ever adds via the
            // deduplicating `add_watch` against the now-populated lists.
            if self.constraints[cid].shape == ConstraintShape::TernaryClause {
                self.initialize_ternary_clause_watched_region(cid);
                if self.repair_watched_region_interruptible(cid, should_stop) {
                    self.needs_rebuild = true;
                    return true;
                }
                self.add_constraint_watches(cid);
                if self.watched_region_has_false_lit(cid) {
                    self.arm_watch_all(cid);
                }
                continue;
            }
            self.initialize_watched_region(cid);
            if self.repair_watched_region_interruptible(cid, should_stop) {
                self.needs_rebuild = true;
                return true;
            }
            self.recalculate_slack(cid);
            self.add_constraint_watches(cid);
            // See `rebuild_all_constraint_state`: blind after repair arms
            // full visibility (P2d).
            self.arm_watch_all_if_blind(cid);
        }

        self.rebuild_falsified_watch_events();
        self.needs_rebuild = false;
        false
    }

    /// Tries to swap false watched literals with non-false unwatched ones.
    ///
    /// This is used during rebuild after backtrack to restore the watched
    /// region to a good state.
    fn repair_watched_region(&mut self, cid: usize) {
        let watch_end = self.constraints[cid].watch_end;

        for watched_idx in 0..watch_end {
            let watched_lit = self.constraints[cid].terms[watched_idx].lit;
            if self.assignment.value(watched_lit) != LitValue::False {
                continue;
            }

            let replacement_idx = self.strongest_non_false_unwatched_replacement(cid);

            if let Some(candidate_idx) = replacement_idx {
                self.swap_constraint_terms(cid, watched_idx, candidate_idx);
            }
        }

        // Update watched_sum and max_unwatched after repairs.
        let constraint = &mut self.constraints[cid];
        constraint.watched_sum = constraint.terms[..constraint.watch_end]
            .iter()
            .map(|t| t.coeff)
            .fold(0i128, i128::saturating_add);
        constraint.max_watched_coeff = constraint.terms[..constraint.watch_end]
            .iter()
            .map(|t| t.coeff)
            .max()
            .unwrap_or(0);
        constraint.max_unwatched_coeff = constraint.terms[constraint.watch_end..]
            .iter()
            .map(|t| t.coeff)
            .max()
            .unwrap_or(0);
        constraint.weighted_replacement_scan_hint = constraint.watch_end;
    }

    fn repair_watched_region_interruptible<F>(&mut self, cid: usize, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        let watch_end = self.constraints[cid].watch_end;
        let mut watched_budget = STOP_POLL_INTERVAL;

        for watched_idx in 0..watch_end {
            if should_interrupt(should_stop, &mut watched_budget) {
                return true;
            }

            let watched_lit = self.constraints[cid].terms[watched_idx].lit;
            if self.assignment.value(watched_lit) != LitValue::False {
                continue;
            }

            let replacement_idx = match self
                .strongest_non_false_unwatched_replacement_interruptible(cid, should_stop)
            {
                Ok(replacement_idx) => replacement_idx,
                Err(()) => return true,
            };

            if let Some(candidate_idx) = replacement_idx {
                self.swap_constraint_terms(cid, watched_idx, candidate_idx);
            }
        }

        let constraint = &mut self.constraints[cid];
        constraint.watched_sum = constraint.terms[..constraint.watch_end]
            .iter()
            .map(|t| t.coeff)
            .fold(0i128, i128::saturating_add);
        constraint.max_watched_coeff = constraint.terms[..constraint.watch_end]
            .iter()
            .map(|t| t.coeff)
            .max()
            .unwrap_or(0);
        constraint.max_unwatched_coeff = constraint.terms[constraint.watch_end..]
            .iter()
            .map(|t| t.coeff)
            .max()
            .unwrap_or(0);
        constraint.weighted_replacement_scan_hint = constraint.watch_end;

        false
    }

    /// Rebuilds all watch lists from scratch.
    ///
    /// Used after backtrack when many constraints may have changed their
    /// watched sets. This is O(sum of all watched terms) which is bounded
    /// by the total number of terms across all constraints.
    fn rebuild_all_watches(&mut self) {
        self.watches.iter_mut().for_each(Vec::clear);

        for (cid, constraint) in self.constraints.iter().enumerate() {
            if !constraint.active {
                continue;
            }
            // Full-visibility rows watch every literal (P2d).
            let watched_len = if constraint.watch_all {
                constraint.terms.len()
            } else {
                constraint.watch_end
            };
            for term in &constraint.terms[..watched_len] {
                let watch_idx =
                    lit_index(term.lit).expect("watched literals must be non-zero DIMACS literals");
                if !self.watches[watch_idx].contains(&cid) {
                    self.watches[watch_idx].push(cid);
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // Internal: incremental watch list operations
    // -----------------------------------------------------------------------

    /// Adds constraint `cid` to all watch lists for its watched literals.
    /// Full-visibility rows (`watch_all`) watch every distinct literal (P2d).
    fn add_constraint_watches(&mut self, cid: usize) {
        if self.constraints[cid].watch_all {
            let n = self.constraints[cid].terms.len();
            for idx in 0..n {
                let lit = self.constraints[cid].terms[idx].lit;
                self.add_watch(lit, cid);
            }
            return;
        }
        match self.constraints[cid].watch_end {
            0 => return,
            1 => {
                let watch_idx = lit_index(self.constraints[cid].terms[0].lit)
                    .expect("watched literals must be non-zero DIMACS literals");
                self.add_watch_index_unchecked(watch_idx, cid);
                return;
            }
            2 => {
                let first_idx = lit_index(self.constraints[cid].terms[0].lit)
                    .expect("watched literals must be non-zero DIMACS literals");
                let second_idx = lit_index(self.constraints[cid].terms[1].lit)
                    .expect("watched literals must be non-zero DIMACS literals");
                self.add_watch_index_unchecked(first_idx, cid);
                if second_idx != first_idx {
                    self.add_watch_index_unchecked(second_idx, cid);
                }
                return;
            }
            _ => {}
        }

        let mut watch_indices = std::mem::take(&mut self.watch_build_scratch);
        self.collect_unique_watched_indices(cid, &mut watch_indices);

        for watch_idx in watch_indices.iter().copied() {
            self.add_watch_index_unchecked(watch_idx, cid);
        }

        watch_indices.clear();
        self.watch_build_scratch = watch_indices;
    }

    fn add_constraint_watches_interruptible<F>(&mut self, cid: usize, should_stop: &mut F) -> bool
    where
        F: FnMut() -> bool,
    {
        if should_stop() {
            return true;
        }

        match self.constraints[cid].watch_end {
            0 => return false,
            1 => {
                let watch_idx = lit_index(self.constraints[cid].terms[0].lit)
                    .expect("watched literals must be non-zero DIMACS literals");
                self.add_watch_index_unchecked(watch_idx, cid);
                return false;
            }
            2 => {
                let first_idx = lit_index(self.constraints[cid].terms[0].lit)
                    .expect("watched literals must be non-zero DIMACS literals");
                let second_idx = lit_index(self.constraints[cid].terms[1].lit)
                    .expect("watched literals must be non-zero DIMACS literals");
                self.add_watch_index_unchecked(first_idx, cid);
                if second_idx != first_idx {
                    self.add_watch_index_unchecked(second_idx, cid);
                }
                return false;
            }
            _ => {}
        }

        let mut watch_indices = std::mem::take(&mut self.watch_build_scratch);
        if self.collect_unique_watched_indices_interruptible(cid, &mut watch_indices, should_stop) {
            watch_indices.clear();
            self.watch_build_scratch = watch_indices;
            return true;
        }

        let mut poll_budget = STOP_POLL_INTERVAL;
        for watch_idx in watch_indices.iter().copied() {
            if should_interrupt(should_stop, &mut poll_budget) {
                watch_indices.clear();
                self.watch_build_scratch = watch_indices;
                return true;
            }
            self.add_watch_index_unchecked(watch_idx, cid);
        }

        watch_indices.clear();
        self.watch_build_scratch = watch_indices;
        false
    }

    /// Adds a single watch: constraint `cid` watches `lit`.
    fn add_watch(&mut self, lit: Lit, cid: usize) {
        if let Some(idx) = lit_index(lit) {
            if idx < self.watches.len() && !self.watches[idx].contains(&cid) {
                self.add_watch_index_unchecked(idx, cid);
            }
        }
    }

    fn replace_watch_after_swap(
        &mut self,
        watch_idx: usize,
        cursor: usize,
        cid: usize,
        old_lit: Lit,
        candidate_lit: Lit,
    ) -> bool {
        // Full-visibility rows keep a watch entry on EVERY literal — the
        // swapped-out literal's entry must survive so its future
        // falsifications stay observable (P2d).
        if self.constraints[cid].watch_all {
            self.add_watch(candidate_lit, cid);
            return true;
        }
        let old_lit_still_watched = self.constraints[cid].terms[..self.constraints[cid].watch_end]
            .iter()
            .any(|term| term.lit == old_lit);

        if !old_lit_still_watched {
            self.watches[watch_idx].swap_remove(cursor);
        }
        self.add_watch(candidate_lit, cid);
        old_lit_still_watched
    }

    fn add_watch_index_unchecked(&mut self, watch_idx: usize, cid: usize) {
        reserve_watch_slot(&mut self.watches[watch_idx]);
        self.watches[watch_idx].push(cid);
    }

    /// Grows the dense assignment and watch-list arrays so they cover `var`.
    ///
    /// Used by the solver's runtime var-pool (`PbCdclSolver::new_var`) to make a
    /// freshly allocated variable addressable for `value()`/`assign_literal()`
    /// lookups even before any constraint references it. Growing never touches an
    /// existing slot: the assignment array resizes with `None`/unassigned and the
    /// watch array resizes with empty lists, so no prior state is invalidated.
    pub fn ensure_var_capacity(&mut self, var: u32) {
        self.assignment.ensure_var(var);
        self.ensure_watch_capacity(var);
    }

    fn ensure_watch_capacity(&mut self, var: u32) {
        let target_len =
            usize::try_from(var).expect("u32 variable index must fit in usize on this platform");
        let required = target_len
            .checked_mul(2)
            .expect("watch vector size overflowed usize");
        if self.watches.len() < required {
            self.watches.resize_with(required, Vec::new);
        }
    }

    fn collect_unique_watched_indices(&self, cid: usize, out: &mut Vec<usize>) {
        out.clear();
        let constraint = &self.constraints[cid];
        out.reserve(constraint.watch_end);
        for term in &constraint.terms[..constraint.watch_end] {
            out.push(
                lit_index(term.lit).expect("watched literals must be non-zero DIMACS literals"),
            );
        }
        out.sort_unstable();
        out.dedup();
    }

    fn collect_unique_watched_indices_interruptible<F>(
        &self,
        cid: usize,
        out: &mut Vec<usize>,
        should_stop: &mut F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        out.clear();
        let constraint = &self.constraints[cid];
        out.reserve(constraint.watch_end);
        let mut poll_budget = STOP_POLL_INTERVAL;
        for term in &constraint.terms[..constraint.watch_end] {
            if should_interrupt(should_stop, &mut poll_budget) {
                return true;
            }
            out.push(
                lit_index(term.lit).expect("watched literals must be non-zero DIMACS literals"),
            );
        }
        if sort_usizes_interruptible(out, should_stop).is_err() {
            return true;
        }
        out.dedup();
        false
    }

    // -----------------------------------------------------------------------
    // Internal: reason extraction
    // -----------------------------------------------------------------------

    fn conflict_reason(&self, cid: usize) -> Vec<Lit> {
        // In the shipped build `ReasonBuf` is a no-op and these scans are skipped
        // entirely (the loop body and `value` lookups have no observable effect),
        // so the dead reason is produced with zero allocation. Tests still see the
        // exact same vector.
        #[cfg(not(test))]
        {
            let _ = cid;
            Vec::new()
        }
        #[cfg(test)]
        {
            let mut reason = ReasonBuf::new();
            for term in &self.constraints[cid].terms {
                if self.assignment.value(term.lit) == LitValue::False {
                    reason.push_false(term.lit);
                }
            }
            reason.into_reason()
        }
    }

    fn propagation_reason(&self, cid: usize, propagated_lit: Lit) -> Vec<Lit> {
        #[cfg(not(test))]
        {
            let _ = (cid, propagated_lit);
            Vec::new()
        }
        #[cfg(test)]
        {
            let mut reason = ReasonBuf::with_propagated(propagated_lit);
            for term in &self.constraints[cid].terms {
                if term.lit == propagated_lit {
                    continue;
                }
                if self.assignment.value(term.lit) == LitValue::False {
                    reason.push_false(term.lit);
                }
            }
            reason.into_reason()
        }
    }

    #[cfg(test)]
    pub(crate) fn rebuild_count(&self) -> u64 {
        self.rebuild_count
    }

    #[cfg(test)]
    pub(crate) fn propagation_stats(&self) -> PropagationStatsSnapshot {
        PropagationStatsSnapshot {
            clause_checks: self.stats.clause_checks.get(),
            unit_cardinality_checks: self.stats.unit_cardinality_checks.get(),
            weighted_checks: self.stats.weighted_checks.get(),
            clause_watch_shortcuts: self.stats.clause_watch_shortcuts.get(),
            unit_cardinality_watch_shortcuts: self.stats.unit_cardinality_watch_shortcuts.get(),
            unit_cardinality_slack_shortcuts: self.stats.unit_cardinality_slack_shortcuts.get(),
            unit_cardinality_full_scans: self.stats.unit_cardinality_full_scans.get(),
            unit_cardinality_scan_terms: self.stats.unit_cardinality_scan_terms.get(),
            weighted_slack_shortcuts: self.stats.weighted_slack_shortcuts.get(),
            weighted_no_replacement_shortcuts: self.stats.weighted_no_replacement_shortcuts.get(),
            weighted_exact_slack_scans: self.stats.weighted_exact_slack_scans.get(),
            slack_recalculations: self.stats.slack_recalculations.get(),
            coefficient_bound_recomputations: self.stats.coefficient_bound_recomputations.get(),
            unwatched_replacement_candidates: self.stats.unwatched_replacement_candidates.get(),
            unwatched_replacement_value_checks: self.stats.unwatched_replacement_value_checks.get(),
            deactivation_watch_lists_visited: self.stats.deactivation_watch_lists_visited.get(),
        }
    }
}

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

fn lit_var(lit: Lit) -> Option<u32> {
    let var = lit.unsigned_abs();
    if var == 0 {
        None
    } else {
        Some(var)
    }
}

fn lit_index(lit: Lit) -> Option<usize> {
    let var = lit_var(lit)?;
    let base = usize::try_from(var - 1).expect("1-based variable index must fit in usize") * 2;
    Some(if lit > 0 { base } else { base + 1 })
}

fn restored_slack_for_event(constraint: Option<&PropConstraint>, lit: Lit) -> Option<i128> {
    let constraint = constraint?;
    if !constraint.active || constraint.shape == ConstraintShape::TernaryClause {
        return None;
    }

    // Counting constraints watch every term; recover the literal's total
    // coefficient in O(log n) from the pre-aggregated lookup instead of an
    // O(terms) scan of the (full-length) watched region.
    if constraint.counting {
        return Some(
            constraint
                .counting_lit_coeffs
                .binary_search_by_key(&lit, |&(entry_lit, _)| entry_lit)
                .map_or(0, |idx| constraint.counting_lit_coeffs[idx].1),
        );
    }

    Some(
        constraint.terms[..constraint.watch_end]
            .iter()
            .filter(|term| term.lit == lit)
            .map(|term| term.coeff)
            .fold(0i128, i128::saturating_add),
    )
}

/// Minimum number of terms before counting propagation is considered.
///
/// On small/medium constraints the O(terms) exact-slack rescan is cheap, so the
/// watched scheme's lower per-assignment watch-list cost wins; counting also
/// touches a constraint on EVERY literal falsification (not just the watched
/// prefix), which can perturb propagation order enough to slow an instance that
/// the watched scheme happened to solve quickly. Counting only earns its keep
/// when an exact rescan would scan many terms, so we require a comfortably large
/// term count. This keeps big-M rows (knapsack/Aardal/bnn have tens-to-hundreds
/// of terms) on the counting path while leaving smaller weighted constraints —
/// which the watched scheme already handles well — untouched.
const COUNTING_MIN_TERMS: usize = 48;

/// Process-wide kill switch for counting propagation, read once from the
/// `AY_PB_DISABLE_COUNTING` environment variable. Lets A/B benchmarks compare
/// counting vs the legacy watched-slack path with the same binary; defaults to
/// counting enabled. Soundness does not depend on this — both paths are sound.
fn counting_disabled_by_env() -> bool {
    // B14: typed A/B switch (`ab_switches`); the never-set env read is gone.
    // (Name kept: callers say "disabled", the switch stores the positive.)
    !crate::ab_switches::get().counting
}

/// A coefficient counts as "big" for `big_count` when it is at least a quarter
/// of the degree (the same threshold the big-M gate uses). Centralized so the
/// gate and the long-tail test stay consistent.
fn coeff_is_big(coeff: i128, degree: i128) -> bool {
    coeff.saturating_mul(4) >= degree
}

/// Decides whether a `Weighted` constraint should use counting (RoundingSat-
/// style) propagation instead of the watched-slack scheme.
///
/// The watched-slack shortcut `slack >= max_watched_coeff` is the only thing
/// that lets the watched scheme avoid an O(terms) `exact_weighted_slack` rescan
/// per touch. That shortcut is structurally defeated when the largest
/// coefficient (`terms[0].coeff` after the descending sort) is large relative to
/// the degree: the slack must reach that huge coefficient to short-circuit,
/// which almost never happens on big-M rows. In that regime every touch falls
/// into the O(terms) rescan, and counting — which maintains the exact slack
/// incrementally in O(1) — is strictly better.
///
/// A large top coefficient alone is *not* sufficient, though: several
/// large-coefficient families are already fast on the watched scheme and only
/// pay counting's per-touch bookkeeping overhead near the time boundary. The
/// shape counting genuinely accelerates is a *dominated long tail*: one (or a
/// few) big-M terms over a long tail of much smaller coefficients, so almost
/// every touch rescans the whole tail. We isolate it with three gates applied to
/// the descending-sorted terms:
///
///   1. Big-M gate — the largest coefficient is >= degree/4 (the watched
///      shortcut is effectively dead).
///   2. Long tail — the count of "big" coefficients (>= degree/4) is at most
///      ~n/6, so the big mass is concentrated and a long tail remains to rescan.
///      This excludes knapsack / subset-sum rows (Aardal prob*/cuww) and the
///      random-regular even-colouring / rand6reg rows, whose terms are *mostly*
///      big (so there is no tail and the watched scheme is already fast).
///   3. Dominant top — the largest coefficient clears the second largest by
///      >= ~1.8x. This excludes the remaining near-equal-top families: knapsack
///      > rows with comparable top weights and bitvector-equality rows (array_diag
///      > `sum 2^i (x_a - x_b)`), whose paired +/- powers of two leave the two
///      > largest coefficients (near-)equal. The watched scheme handles both well.
///
/// NOTE (known limitation): some optimization-proof rows — notably the WBO/
/// PARTIAL weighted-queens objective-aggregation rows — share this exact
/// near-equal-top / long-tail-ish region with the hurt DEC rows above, and
/// counting genuinely *helps* prove their optimum. There is no per-constraint
/// structural property that keeps those while excluding the DEC families; this
/// predicate favors recovering the DEC families. See the module-level discussion
/// and the tuning notes for the empirical trade-off.
///
/// All other shapes and structures keep their existing fast paths untouched.
fn should_use_counting(shape: ConstraintShape, terms: &[PropTerm], degree: i128) -> bool {
    if shape != ConstraintShape::Weighted {
        return false;
    }
    if counting_disabled_by_env() {
        return false;
    }
    let n = terms.len();
    if n < COUNTING_MIN_TERMS {
        // FORGONE COST: the terms this refusal hands back to the non-counting
        // propagator, every time it is asked.
        ay_core::forgone::charge(ay_core::forgone::PB_COUNTING, n as u64);
        return false;
    }
    // Terms are sorted descending by coefficient at construction, so the first
    // term carries the largest coefficient and `terms[1]` the second largest.
    let Some(max_coeff) = terms.first().map(|term| term.coeff) else {
        return false;
    };
    if degree <= 0 || max_coeff <= 0 {
        return false;
    }
    // (1) Big-M gate (necessary condition): the largest coefficient is at least a
    // quarter of the degree, so the watched shortcut `slack >= max_coeff` is
    // rarely satisfiable and the watched scheme keeps falling into the O(terms)
    // exact rescan. Use i128 throughout to avoid overflow on large coeffs.
    if !coeff_is_big(max_coeff, degree) {
        return false;
    }

    // (2) Long-tail signature: the big-M mass must be concentrated in a small
    // fraction of the terms, leaving a long tail of much smaller coefficients
    // for every touch to rescan. That long tail is exactly where the exact-slack
    // rescan dominates and counting's O(1) incremental slack wins. We require the
    // count of "big" coefficients (>= degree/4) to be at most ~n/6.
    //
    // This is the gate that excludes the families where the watched scheme is
    // already fast despite a large top coefficient: knapsack / subset-sum rows
    // (Aardal prob*/cuww) and the random-regular even-colouring / rand6reg rows
    // have *many* comparable big coefficients — most of their terms are big, so
    // there is no tail to rescan and counting is pure overhead near the boundary.
    let big_count = terms
        .iter()
        .filter(|term| coeff_is_big(term.coeff, degree))
        .count();
    if big_count.saturating_mul(6) > n {
        return false;
    }

    // (3) Dominant top coefficient: the largest coefficient must clear the second
    // largest by a comfortable margin (>= ~1.8x). Counting helps when one (or a
    // few) terms dominate a long tail; when the two largest coefficients are
    // close the row behaves like a cardinality/knapsack row (or a bitvector
    // equality whose +/- power-of-two pair leaves the top two coefficients
    // identical), and the watched scheme already handles it well. The 1.8x margin
    // is what separates the dominant big-M / factor rows (top coefficient 2x+ the
    // next) from those near-equal-top families. A single dominant term (no second
    // term) trivially satisfies this.
    let Some(second_coeff) = terms.get(1).map(|term| term.coeff) else {
        return true;
    };
    if second_coeff <= 0 {
        return true;
    }
    // max_coeff >= 1.8 * second_coeff, cross-multiplied as `5*max >= 9*second`
    // and widened to i128 so large coefficients cannot overflow.
    max_coeff.saturating_mul(5) >= second_coeff.saturating_mul(9)
}

fn classify_constraint_shape(terms: &[PropTerm], degree: i128) -> ConstraintShape {
    // These tags are internal dispatch hints; all constraints keep their
    // normalized PB form for reason extraction and cutting-planes consumers.
    if terms.iter().all(|term| term.coeff == 1) {
        if degree == 1 {
            if is_distinct_ternary_clause(terms) {
                ConstraintShape::TernaryClause
            } else if has_adjacent_duplicate_lit(terms) {
                ConstraintShape::Weighted
            } else {
                ConstraintShape::Clause
            }
        } else {
            ConstraintShape::UnitCardinality
        }
    } else {
        ConstraintShape::Weighted
    }
}

fn classify_constraint_shape_interruptible<F>(
    terms: &[PropTerm],
    degree: i128,
    should_stop: &mut F,
) -> Result<ConstraintShape, ()>
where
    F: FnMut() -> bool,
{
    if should_stop() {
        return Err(());
    }

    let mut all_unit = true;
    let mut poll_budget = STOP_POLL_INTERVAL;
    for term in terms {
        if should_interrupt(should_stop, &mut poll_budget) {
            return Err(());
        }
        if term.coeff != 1 {
            all_unit = false;
            break;
        }
    }

    if all_unit {
        if degree == 1 {
            if is_distinct_ternary_clause(terms) {
                Ok(ConstraintShape::TernaryClause)
            } else if has_adjacent_duplicate_lit(terms) {
                Ok(ConstraintShape::Weighted)
            } else {
                Ok(ConstraintShape::Clause)
            }
        } else {
            Ok(ConstraintShape::UnitCardinality)
        }
    } else {
        Ok(ConstraintShape::Weighted)
    }
}

fn native_lits_for_shape(_shape: ConstraintShape, _terms: &[PropTerm]) -> Vec<i64> {
    Vec::new()
}

fn is_distinct_ternary_clause(terms: &[PropTerm]) -> bool {
    terms.len() == 3
        && terms[0].lit != terms[1].lit
        && terms[0].lit != terms[2].lit
        && terms[1].lit != terms[2].lit
}

fn has_adjacent_duplicate_lit(terms: &[PropTerm]) -> bool {
    terms.windows(2).any(|pair| pair[0].lit == pair[1].lit)
}

fn normalize_ge_terms(terms: &[PbTerm], rhs: i128) -> (Vec<PropTerm>, i128) {
    let mut adjusted_rhs = rhs;
    let mut normalized = Vec::with_capacity(terms.len());

    for term in terms {
        if term.coeff == 0 {
            continue;
        }

        match term.lits.as_slice() {
            [] => {
                adjusted_rhs = adjusted_rhs.saturating_sub(term.coeff);
            }
            [lit] => {
                let dimacs_lit = pb_lit_to_dimacs(*lit);
                if term.coeff > 0 {
                    normalized.push(PropTerm {
                        lit: dimacs_lit,
                        coeff: term.coeff,
                    });
                } else {
                    normalized.push(PropTerm {
                        lit: -dimacs_lit,
                        coeff: -term.coeff,
                    });
                    adjusted_rhs = adjusted_rhs.saturating_sub(term.coeff);
                }
            }
            _ => {
                // Watched-slack propagation is defined over linear PB terms.
                // Keep the module self-contained and conservative by skipping
                // unsupported non-linear terms here.
            }
        }
    }

    (normalized, adjusted_rhs)
}

fn normalize_ge_terms_interruptible<F>(
    terms: &[PbTerm],
    rhs: i128,
    should_stop: &mut F,
) -> Result<(Vec<PropTerm>, i128), ()>
where
    F: FnMut() -> bool,
{
    let mut adjusted_rhs = rhs;
    let mut normalized = Vec::with_capacity(terms.len());
    let mut poll_budget = STOP_POLL_INTERVAL;

    for term in terms {
        if should_interrupt(should_stop, &mut poll_budget) {
            return Err(());
        }

        if term.coeff == 0 {
            continue;
        }

        match term.lits.as_slice() {
            [] => {
                adjusted_rhs = adjusted_rhs.saturating_sub(term.coeff);
            }
            [lit] => {
                let dimacs_lit = pb_lit_to_dimacs(*lit);
                if term.coeff > 0 {
                    normalized.push(PropTerm {
                        lit: dimacs_lit,
                        coeff: term.coeff,
                    });
                } else {
                    normalized.push(PropTerm {
                        lit: -dimacs_lit,
                        coeff: -term.coeff,
                    });
                    adjusted_rhs = adjusted_rhs.saturating_sub(term.coeff);
                }
            }
            _ => {}
        }
    }

    Ok((normalized, adjusted_rhs))
}

fn prop_term_import_order(lhs: &PropTerm, rhs: &PropTerm) -> std::cmp::Ordering {
    rhs.coeff
        .cmp(&lhs.coeff)
        .then_with(|| lhs.lit.unsigned_abs().cmp(&rhs.lit.unsigned_abs()))
        .then_with(|| lhs.lit.cmp(&rhs.lit))
}

fn sort_prop_terms_interruptible<F>(terms: &mut [PropTerm], should_stop: &mut F) -> Result<(), ()>
where
    F: FnMut() -> bool,
{
    sort_by_interruptible(terms, should_stop, prop_term_import_order)
}

fn sort_usizes_interruptible<F>(values: &mut [usize], should_stop: &mut F) -> Result<(), ()>
where
    F: FnMut() -> bool,
{
    sort_by_interruptible(values, should_stop, usize::cmp)
}

fn sort_by_interruptible<T, F, C>(
    values: &mut [T],
    should_stop: &mut F,
    mut compare: C,
) -> Result<(), ()>
where
    F: FnMut() -> bool,
    C: FnMut(&T, &T) -> std::cmp::Ordering,
{
    if values.len() < 2 {
        return Ok(());
    }
    if should_stop() {
        return Err(());
    }

    let mut sorted = true;
    let mut poll_budget = STOP_POLL_INTERVAL;
    for idx in 1..values.len() {
        if should_interrupt(should_stop, &mut poll_budget) {
            return Err(());
        }
        if compare(&values[idx - 1], &values[idx]).is_gt() {
            sorted = false;
            break;
        }
    }
    if sorted {
        return Ok(());
    }

    if values.len() <= STOP_POLL_INTERVAL {
        values.sort_by(compare);
        if should_stop() {
            return Err(());
        }
        return Ok(());
    }

    let len = values.len();
    let mut poll_budget = STOP_POLL_INTERVAL;
    for start in (0..(len / 2)).rev() {
        sift_down_interruptible(
            values,
            start,
            len,
            should_stop,
            &mut poll_budget,
            &mut compare,
        )?;
    }

    for end in (1..len).rev() {
        if should_interrupt(should_stop, &mut poll_budget) {
            return Err(());
        }
        values.swap(0, end);
        sift_down_interruptible(values, 0, end, should_stop, &mut poll_budget, &mut compare)?;
    }

    Ok(())
}

fn sift_down_interruptible<T, F, C>(
    values: &mut [T],
    start: usize,
    end: usize,
    should_stop: &mut F,
    poll_budget: &mut usize,
    compare: &mut C,
) -> Result<(), ()>
where
    F: FnMut() -> bool,
    C: FnMut(&T, &T) -> std::cmp::Ordering,
{
    let mut root = start;

    loop {
        let child = root.saturating_mul(2).saturating_add(1);
        if child >= end {
            return Ok(());
        }

        let mut swap_idx = root;
        if compare(&values[swap_idx], &values[child]).is_lt() {
            swap_idx = child;
        }
        if child + 1 < end && compare(&values[swap_idx], &values[child + 1]).is_lt() {
            swap_idx = child + 1;
        }
        if swap_idx == root {
            return Ok(());
        }

        values.swap(root, swap_idx);
        root = swap_idx;
        if should_interrupt(should_stop, poll_budget) {
            return Err(());
        }
    }
}

fn pb_lit_to_dimacs(lit: PbLit) -> Lit {
    let var = i32::try_from(lit.var).expect("PbLit variable must fit in i32 for DIMACS encoding");
    if lit.negated {
        -var
    } else {
        var
    }
}

#[cfg(test)]
fn push_unique(lits: &mut Vec<Lit>, lit: Lit) {
    if !lits.contains(&lit) {
        lits.push(lit);
    }
}

/// Accumulator for clause-style reason literals on the propagate/conflict path.
///
/// Every production CDCL consumer of [`PropResult`] binds the reason vector to
/// `_` and rebuilds the reason from the stored constraint id during conflict
/// analysis (`analyze_conflict_dense` -> `constraint_by_index`); the trail stores
/// only `reason: Option<cid>`, never the literal vector. The reason vector is
/// therefore dead weight outside the reason-asserting unit tests, yet the old
/// builders heap-allocated and filled it (an O(n) `push_unique` `.contains` scan)
/// on *every* propagation/conflict.
///
/// In test builds this records the literals so the reason-asserting tests
/// (`propagation/tests.rs`) observe the exact same vectors as before. In the
/// shipped (non-test) build it is a zero-sized no-op and [`Self::into_reason`]
/// yields an empty `Vec`, which performs no heap allocation. This is a pure
/// performance change: the populated vector was never read on the production
/// path, so search behavior (verdicts, conflicts, decisions, propagations) is
/// unchanged.
#[derive(Default)]
struct ReasonBuf {
    #[cfg(test)]
    lits: Vec<Lit>,
}

impl ReasonBuf {
    fn new() -> Self {
        Self::default()
    }

    /// Seeds the reason with the propagated literal (first entry, as before).
    /// Used only by the test-only `propagation_reason` body.
    #[cfg(test)]
    fn with_propagated(propagated_lit: Lit) -> Self {
        let mut buf = Self::new();
        buf.lits.push(propagated_lit);
        buf
    }

    /// Records a false literal, preserving the de-duplicated insertion order of
    /// the original `push_unique` builders. Compiles to a no-op in release.
    #[inline]
    #[cfg_attr(not(test), allow(unused_variables))]
    fn push_false(&mut self, lit: Lit) {
        #[cfg(test)]
        push_unique(&mut self.lits, lit);
    }

    fn into_reason(self) -> Vec<Lit> {
        #[cfg(test)]
        {
            self.lits
        }
        #[cfg(not(test))]
        {
            Vec::new()
        }
    }

    /// Builds a propagation reason `[propagated_lit, ..accumulated false lits]`,
    /// matching the old `propagation_reason_from_false_lits` ordering. No-op
    /// (empty `Vec`) in release.
    #[cfg_attr(not(test), allow(unused_variables))]
    fn into_propagation_reason(self, propagated_lit: Lit) -> Vec<Lit> {
        #[cfg(test)]
        {
            let mut reason = vec![propagated_lit];
            for lit in self.lits {
                push_unique(&mut reason, lit);
            }
            reason
        }
        #[cfg(not(test))]
        {
            Vec::new()
        }
    }
}

fn reserve_watch_slot(watch_list: &mut Vec<usize>) {
    if watch_list.len() < watch_list.capacity() {
        return;
    }

    let additional = if watch_list.capacity() == 0 {
        WATCH_LIST_MIN_GROWTH
    } else {
        watch_list.capacity().min(WATCH_LIST_MAX_GROWTH)
    };
    watch_list.reserve(additional);
}

fn should_interrupt<F>(should_stop: &mut F, poll_budget: &mut usize) -> bool
where
    F: FnMut() -> bool,
{
    *poll_budget -= 1;
    if *poll_budget == 0 {
        *poll_budget = STOP_POLL_INTERVAL;
        should_stop()
    } else {
        false
    }
}

#[cfg(test)]
mod tests;
