// Copyright 2026 Andrew Yates
// Core DRAT/DRUP proof checker with two-watched-literal BCP engine.
// Originally extracted from ay-sat/src/forward_checker.rs (Biere 2021, CaDiCaL checker parity).

mod adapter_api;
pub mod backward;
mod clause_db;
mod construct;
mod propagation;
mod rat;
mod rup_deps;
pub mod sr;
mod sr_reduct_core;
mod steps;
mod types;

pub use construct::CheckerConstructionError;
pub use sr::SrChecker;
pub use types::{ConcludeFailure, ConcludeResult, Stats};
pub(crate) use types::{Visit, Watch};

use crate::error::DratCheckError;
use crate::literal::Literal;
use rustc_hash::FxHashMap;
use std::collections::TryReserveError;

const INITIAL_HASH_CAPACITY: usize = 1024;

/// Largest clause hash table, in buckets. Beyond it the table stops doubling
/// and chains grow longer instead: bucket count affects lookup speed only,
/// never which clause a lookup finds. 2^27 buckets (a 3 GiB bucket array)
/// keep the load factor at most one up to 134M live clauses.
const MAX_HASH_CAPACITY: usize = 1 << 27;

/// Why the dense per-variable arrays could not be grown to cover a variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum DenseRefusal {
    /// The variable index lies beyond [`MAX_DENSE_VARS`].
    OutOfEnvelope,
    /// The variable lies inside the envelope, but the allocator refused the
    /// growth of the dense arrays (or the requested universe).
    AllocationFailed,
}

impl DenseRefusal {
    /// The step error for a clause mentioning `variable` that was refused.
    pub(super) fn step_error(self, variable: usize, step: u64) -> DratCheckError {
        match self {
            Self::OutOfEnvelope => DratCheckError::VariableOutOfRange {
                variable,
                maximum: MAX_DENSE_VARS,
                step,
            },
            Self::AllocationFailed => DratCheckError::DenseAllocationFailed { variable, step },
        }
    }

    /// The conclusion failure once a clause could not be stored.
    fn conclude_failure(self) -> ConcludeFailure {
        match self {
            Self::OutOfEnvelope => ConcludeFailure::VariableOutOfRange,
            Self::AllocationFailed => ConcludeFailure::DenseAllocationFailed,
        }
    }
}

/// Largest dense variable universe accepted by the checker frontends.
///
/// Each variable owns two polarity slots in both `watches` and `occ_lists`.
/// The ceiling matches AY's supported 58.6M-variable competition giant while
/// rejecting the former 268M-variable worst-case envelope before allocation.
pub const MAX_DENSE_VARS: usize = 1 << 26;

/// The dense arrays indexed by variable or by literal code, allocated
/// together by [`DratChecker::new`].
#[derive(Default)]
struct DenseArrays {
    assigns: Vec<Option<bool>>,
    watches: Vec<Vec<Watch>>,
    occ_lists: Vec<Vec<usize>>,
    marks: Vec<bool>,
    reasons: Vec<Option<usize>>,
    conflict_marked: Vec<bool>,
}

impl DenseArrays {
    /// Allocate every array for `num_vars` variables (`2 * num_vars` literal
    /// slots), or `None` if the literal count overflows or the allocator
    /// refuses any of them.
    fn try_alloc(num_vars: usize) -> Option<Self> {
        let num_lits = num_vars.checked_mul(2)?;
        Some(Self {
            assigns: try_filled(None, num_vars)?,
            watches: try_filled(Vec::new(), num_lits)?,
            occ_lists: try_filled(Vec::new(), num_lits)?,
            marks: try_filled(false, num_lits)?,
            reasons: try_filled(None, num_vars)?,
            conflict_marked: try_filled(false, num_vars)?,
        })
    }
}

/// Reserve room for `v` to reach length `len` without reallocating, or
/// report the allocator's refusal. A vector already that long is left as is.
///
/// The reservation is amortized (`try_reserve`, not `try_reserve_exact`):
/// proofs that introduce extension variables grow the universe one variable
/// at a time, and exact reservations would reallocate every array on every
/// new variable (quadratic copying on an allocator that cannot grow in
/// place). Peak capacity is what the former infallible `resize` reserved.
fn try_reserve_to<T>(v: &mut Vec<T>, len: usize) -> Result<(), TryReserveError> {
    match len.checked_sub(v.len()) {
        Some(additional) => v.try_reserve(additional),
        None => Ok(()),
    }
}

/// Pad `v` with copies of `elem` up to length `len` (no-op when already that
/// long). After [`try_reserve_to`] for the same `len` this never reallocates.
fn fill_to<T: Clone>(v: &mut Vec<T>, len: usize, elem: T) {
    if let Some(additional) = len.checked_sub(v.len()) {
        v.extend(std::iter::repeat_n(elem, additional));
    }
}

/// `len` copies of `elem`, or `None` if the allocator refuses the buffer.
///
/// The buffer is reserved up front with `try_reserve_exact`, so filling it
/// never reallocates: this is `vec![elem; len]` with a fallible allocation.
pub(super) fn try_filled<T: Clone>(elem: T, len: usize) -> Option<Vec<T>> {
    let mut filled = Vec::new();
    filled.try_reserve_exact(len).ok()?;
    filled.extend(std::iter::repeat_n(elem, len));
    Some(filled)
}

/// Forward DRAT checker.
///
/// Verifies each added clause is either RUP (Reverse Unit Propagation) implied
/// or RAT (Resolution Asymmetric Tautology) with respect to the current clause
/// database. Uses a self-contained 2WL BCP engine.
pub struct DratChecker {
    pub(super) num_vars: usize,
    pub(super) assigns: Vec<Option<bool>>,
    pub(super) trail: Vec<Literal>,
    pub(super) propagate_cursor: usize,
    pub(super) watches: Vec<Vec<Watch>>,
    /// Per-literal live-clause occurrences for RAT candidate lookup.
    pub(super) occ_lists: Vec<Vec<usize>>,
    pub(super) clauses: Vec<Option<Vec<Literal>>>,
    /// Fully unlinked tombstone slots available for reuse.
    pub(super) free_clause_slots: Vec<usize>,
    pub(super) hash_buckets: Vec<Vec<usize>>,
    pub(super) live_clauses: usize,
    pub(super) inconsistent: bool,
    /// Set permanently after any unchecked cross-crate adapter mutation.
    /// Diagnostic clients may keep using the clause database, but an
    /// authoritative proof conclusion must then fail closed.
    authority_tainted: bool,
    /// Set permanently (to the first refusal) when a clause could not be
    /// stored because the dense arrays could not cover one of its variables:
    /// it lies outside the dense envelope ([`MAX_DENSE_VARS`]), or the
    /// allocator refused the growth. The database then lacks a clause of the
    /// formula or derivation, so an authoritative proof conclusion must fail
    /// closed. Also set by [`Self::new`] when the allocator refuses the
    /// requested variable universe.
    dense_refusal: Option<DenseRefusal>,
    /// Test-only fault injection: the number of further dense-array
    /// reservations [`Self::ensure_capacity`] may make before the next one is
    /// refused as if by the allocator. `None` (the default) never refuses.
    #[cfg(test)]
    reservations_before_refusal: Option<usize>,
    /// The bulk `verify` API is intentionally one-shot. Reusing a checker would
    /// otherwise carry clauses or an earlier contradiction into a new problem.
    bulk_verify_started: bool,
    pub(crate) stats: Stats,
    check_rat: bool,
    /// Marker array indexed by literal code for O(n) tautology/duplicate detection.
    /// Size = 2 * num_vars. Avoids O(n^2) nested loops per drat-trim pattern.
    marks: Vec<bool>,
    /// Per-variable reason clause index. Set during BCP when a literal is
    /// propagated by a clause. Used by `rup_deps::collect_conflict_deps` and
    /// `backward::mark_active` for dependency tracking.
    pub(super) reasons: Vec<Option<usize>>,
    /// Clause index of the last BCP conflict. Set by `propagate_watches`
    /// when a conflict is detected. Used by `collect_conflict_deps`.
    pub(super) bcp_conflict_cidx: Option<usize>,
    /// Persistent marker array for conflict analysis (avoids allocation per call).
    pub(super) conflict_marked: Vec<bool>,
    /// Dirty list for `conflict_marked` cleanup.
    pub(super) conflict_marked_dirty: Vec<usize>,
    /// Reusable buffer for RAT resolvent construction.
    pub(super) scratch_resolvent: Vec<Literal>,
    /// Retained scratch for exact, order-independent O(k) clause matching.
    clause_match_counts: FxHashMap<Literal, usize>,
    clause_match_consumed: Vec<Literal>,
    /// Core-first BCP mode. When enabled, `propagate()` processes ACTIVE
    /// watch entries before non-ACTIVE ones (drat-trim.c:196-230).
    /// Toggled by the backward checker.
    pub(super) core_first: bool,
    /// Adaptive prep mode toggle (drat-trim.c:647-652). Turns core-first
    /// on when RUP checks have low indegree (<=2 resolution steps),
    /// off when high (>2). Automatically managed during backward checking.
    pub(super) prep: bool,
    /// Reusable scratch buffer for clause simplification in `add_clause_internal`.
    /// Avoids per-call heap allocation when filtering falsified literals (#5626).
    simplify_buf: Vec<Literal>,
}

impl DratChecker {
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// Conclude the current formula and derivation as UNSAT.
    ///
    /// This requires no failed derivation steps, no unchecked adapter
    /// mutations, and a derived contradiction. Contradictory original clauses
    /// therefore need no separate proof step.
    ///
    /// Unlike LRAT, DRAT has no finalization coverage check.
    /// The reference implementation (CaDiCaL checker.cpp) has no explicit
    /// conclusion API -- it relies on the `inconsistent` flag. This method
    /// provides a structured alternative for API parity with ay-lrat-check.
    pub fn conclude_unsat(&self) -> ConcludeResult {
        if self.stats.failures > 0 {
            return ConcludeResult::Failed(ConcludeFailure::StepFailures);
        }
        if let Some(refusal) = self.dense_refusal {
            return ConcludeResult::Failed(refusal.conclude_failure());
        }
        if self.authority_tainted {
            return ConcludeResult::Failed(ConcludeFailure::UncheckedAdapterMutation);
        }
        if !self.inconsistent {
            return ConcludeResult::Failed(ConcludeFailure::NoEmptyClause);
        }
        ConcludeResult::Verified
    }

    /// Create a checker for variables `0..num_vars`.
    ///
    /// The dense per-variable and per-literal arrays are allocated fallibly.
    /// If the allocator refuses them (or `2 * num_vars` overflows), the
    /// checker starts with an empty universe and fails every conclusion
    /// closed instead of aborting the process or panicking with a capacity
    /// overflow: [`ConcludeFailure::VariableOutOfRange`] for a universe
    /// beyond [`MAX_DENSE_VARS`], [`ConcludeFailure::DenseAllocationFailed`]
    /// for one inside it.
    pub fn new(num_vars: usize, check_rat: bool) -> Self {
        let (num_vars, dense, dense_refusal) = match DenseArrays::try_alloc(num_vars) {
            Some(dense) => (num_vars, dense, None),
            None if num_vars > MAX_DENSE_VARS => {
                (0, DenseArrays::default(), Some(DenseRefusal::OutOfEnvelope))
            }
            None => (
                0,
                DenseArrays::default(),
                Some(DenseRefusal::AllocationFailed),
            ),
        };
        Self::from_arrays(
            num_vars,
            dense,
            vec![Vec::new(); INITIAL_HASH_CAPACITY],
            if check_rat {
                construct::CheckMode::Rat
            } else {
                construct::CheckMode::Drup
            },
            dense_refusal,
        )
    }

    /// Start one authoritative bulk verification on pristine checker state.
    pub(super) fn begin_bulk_verify(&mut self) -> Result<(), DratCheckError> {
        if self.bulk_verify_started
            || self.authority_tainted
            || self.dense_refusal.is_some()
            || !self.clauses.is_empty()
            || !self.trail.is_empty()
            || self.inconsistent
            || self.stats != Stats::default()
        {
            return Err(DratCheckError::CheckerNotFresh);
        }
        self.bulk_verify_started = true;
        Ok(())
    }

    /// Grow the dense per-variable arrays to cover variable index `var_idx`.
    ///
    /// Returns [`DenseRefusal::OutOfEnvelope`], leaving the checker's
    /// contents unchanged, when `var_idx` lies beyond both the current
    /// universe and [`MAX_DENSE_VARS`]. The frontends refuse such variables
    /// before parsing a proof; this refusal covers the library API, where one
    /// literal of variable `Variable::MAX_ID` would otherwise demand two
    /// 2^32-entry watch arrays (~200GB) and abort.
    ///
    /// Inside the envelope the growth is still up to 2^27 slots of 24 bytes
    /// per literal array (~3 GiB each), so it is fallible: every array is
    /// reserved before any is filled, and an allocator refusal returns
    /// [`DenseRefusal::AllocationFailed`] with every array length (and the
    /// universe) unchanged, instead of aborting the process with the arrays
    /// out of step. Callers record the refusal and fail closed.
    pub(super) fn ensure_capacity(&mut self, var_idx: usize) -> Result<(), DenseRefusal> {
        if var_idx < self.num_vars {
            return Ok(());
        }
        if var_idx >= MAX_DENSE_VARS {
            return Err(DenseRefusal::OutOfEnvelope);
        }
        // `var_idx < MAX_DENSE_VARS = 2^26`, so neither step can overflow and
        // every array stays below 2^27 entries.
        let new_num_vars = var_idx + 1;
        let new_num_lits = new_num_vars * 2;
        if self.try_reserve_dense(new_num_vars, new_num_lits).is_err() {
            return Err(DenseRefusal::AllocationFailed);
        }
        fill_to(&mut self.assigns, new_num_vars, None);
        fill_to(&mut self.watches, new_num_lits, Vec::new());
        fill_to(&mut self.occ_lists, new_num_lits, Vec::new());
        fill_to(&mut self.marks, new_num_lits, false);
        fill_to(&mut self.reasons, new_num_vars, None);
        fill_to(&mut self.conflict_marked, new_num_vars, false);
        self.num_vars = new_num_vars;
        Ok(())
    }

    /// Record that a clause could not be stored because of `refusal`. The
    /// first refusal sticks and fails every later conclusion closed.
    pub(super) fn record_dense_refusal(&mut self, refusal: DenseRefusal) {
        self.dense_refusal.get_or_insert(refusal);
    }

    /// Reserve every dense array for `num_vars` variables and `num_lits`
    /// literal slots, stopping at the first allocator refusal. Lengths (and
    /// so the checker's observable state) are untouched either way.
    fn try_reserve_dense(
        &mut self,
        num_vars: usize,
        num_lits: usize,
    ) -> Result<(), TryReserveError> {
        let len = self.reservation_len(num_vars);
        try_reserve_to(&mut self.assigns, len)?;
        let len = self.reservation_len(num_lits);
        try_reserve_to(&mut self.watches, len)?;
        let len = self.reservation_len(num_lits);
        try_reserve_to(&mut self.occ_lists, len)?;
        let len = self.reservation_len(num_lits);
        try_reserve_to(&mut self.marks, len)?;
        let len = self.reservation_len(num_vars);
        try_reserve_to(&mut self.reasons, len)?;
        let len = self.reservation_len(num_vars);
        try_reserve_to(&mut self.conflict_marked, len)
    }

    /// The length one dense-array reservation asks for: `len` itself.
    #[cfg(not(test))]
    #[inline]
    fn reservation_len(&mut self, len: usize) -> usize {
        len
    }

    /// The length one dense-array reservation asks for. Under test fault
    /// injection ([`Self::reservations_before_refusal`]) an exhausted budget
    /// asks for `usize::MAX` elements, which the real `try_reserve` refuses
    /// without touching the vector: the same error path an allocator refusal
    /// takes.
    #[cfg(test)]
    fn reservation_len(&mut self, len: usize) -> usize {
        match self.reservations_before_refusal.as_mut() {
            None => len,
            Some(0) => usize::MAX,
            Some(budget) => {
                *budget -= 1;
                len
            }
        }
    }

    #[inline]
    pub(super) fn value(&self, lit: Literal) -> Option<bool> {
        let vi = lit.variable().index();
        if vi >= self.num_vars {
            return None;
        }
        self.assigns[vi].map(|v| v == lit.is_positive())
    }

    /// Assign a literal without a reason (used for assumptions in RUP checks).
    ///
    /// Silently skips if the variable is already assigned (robustness against
    /// malformed proofs -- drat-trim does not crash on double-assignment).
    #[inline]
    pub(super) fn assign(&mut self, lit: Literal) {
        let vi = lit.variable().index();
        if self.assigns[vi].is_some() {
            return; // Already assigned -- skip (malformed proof robustness).
        }
        self.assigns[vi] = Some(lit.is_positive());
        self.reasons[vi] = None;
        self.trail.push(lit);
    }

    /// Assign a literal with a reason clause (used during BCP propagation).
    ///
    /// Silently skips if the variable is already assigned (robustness against
    /// malformed proofs -- drat-trim does not crash on double-assignment).
    #[inline]
    pub(super) fn assign_with_reason(&mut self, lit: Literal, reason_cidx: usize) {
        let vi = lit.variable().index();
        if self.assigns[vi].is_some() {
            return; // Already assigned -- skip (malformed proof robustness).
        }
        self.assigns[vi] = Some(lit.is_positive());
        self.reasons[vi] = Some(reason_cidx);
        self.trail.push(lit);
    }

    pub(super) fn backtrack(&mut self, saved_trail_len: usize) {
        while self.trail.len() > saved_trail_len {
            let Some(lit) = self.trail.pop() else {
                break; // Structurally unreachable but safe.
            };
            let vi = lit.variable().index();
            self.assigns[vi] = None;
            self.reasons[vi] = None;
        }
        self.propagate_cursor = saved_trail_len;
    }

    /// Check if `clause` is RUP (Reverse Unit Propagation) implied:
    /// assume the negation of each literal, propagate, check for conflict.
    pub(super) fn check_rup(&mut self, clause: &[Literal]) -> bool {
        self.stats.checks = self.stats.checks.saturating_add(1);
        self.bcp_conflict_cidx = None;
        if self.inconsistent {
            return true;
        }
        let saved = self.trail.len();
        if clause.iter().any(|&lit| self.value(lit) == Some(true)) {
            return true;
        }
        for &lit in clause {
            let neg = lit.negated();
            match self.value(neg) {
                Some(true) => {}
                Some(false) => {
                    self.backtrack(saved);
                    return true;
                }
                None => self.assign(neg),
            }
        }
        let no_conflict = self.propagate();
        self.backtrack(saved);
        !no_conflict
    }
}

#[cfg(test)]
mod adapter_api_tests;
#[cfg(test)]
mod binary_format_tests;
#[cfg(test)]
mod test_helpers;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_algorithm_audit;
#[cfg(test)]
mod tests_coverage;
#[cfg(test)]
mod tests_dense_envelope;
#[cfg(test)]
mod tests_performance;
#[cfg(test)]
mod tests_proptest;
