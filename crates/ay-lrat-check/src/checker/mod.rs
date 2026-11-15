// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core LRAT verification: RUP checking with explicit hint clauses.
//!
//! Stronger than DRUP (requires certificate). For `add_derived(id, clause, hints)`:
//! assume ¬clause, walk hints, propagate units until conflict or exhaustion.
//! Reference: CaDiCaL `lratchecker.cpp` (Biere 2021). Originally extracted from ay-sat.

use crate::dimacs::Literal;
use crate::lrat_parser::LratStep;
use ay_core::kani_compat::{det_hash_map_new, DetHashMap as HashMap};
use std::collections::TryReserveError;
use std::io::Write;

#[cfg(test)]
use dense::try_filled;
use dense::DenseArrays;

/// Largest dense variable universe accepted by checker frontends.
///
/// LRAT keeps two polarity occurrence-list Vecs plus dense assignment/mark
/// arrays per variable. The ceiling matches AY's supported 58.6M-variable
/// competition giant while rejecting the former 268M-variable envelope.
pub const MAX_DENSE_VARS: usize = 1 << 26;

/// Literal-index ceiling implied by [`MAX_DENSE_VARS`]: two polarity slots
/// per variable. Every per-literal array (`marks`, `checked_lits`,
/// `occ_lists`) stays strictly below this length.
pub(crate) const MAX_DENSE_LITS: usize = 2 * MAX_DENSE_VARS;

#[cfg(test)]
pub(super) use types::{is_tautological, lit};
pub(crate) use types::{ClauseEntry, HintAction};
pub use types::{ConcludeFailure, ConcludeResult, Stats};

/// LRAT proof checker with arena-indexed clause database.
///
/// Clause literals live in a flat `Vec<Literal>` arena; the index map stores
/// `(start, len)` ranges. Copying a `ClauseEntry` (16 bytes) releases the
/// borrow on `clause_index` without cloning literal data (#5267).
pub struct LratChecker {
    /// Flat arena storing all clause literals contiguously.
    pub(crate) clause_arena: Vec<Literal>,
    /// Maps clause ID to `(start, len)` range in `clause_arena`.
    pub(crate) clause_index: HashMap<u64, ClauseEntry>,
    /// Saved clause content for weaken/restore (CaDiCaL `clauses_to_reconstruct`).
    /// Tuple: (sorted literals, was_original, was_tautological).
    weakened_clauses: HashMap<u64, (Vec<Literal>, bool, bool)>,
    /// `assigns[var.index()] = Some(polarity)` where `true` = positive.
    pub(crate) assigns: Vec<Option<bool>>,
    /// Trail of assigned variable indices for backtracking.
    pub(crate) trail: Vec<usize>,
    pub(crate) stats: Stats,
    /// Whether an empty clause was derived.
    has_empty_clause: bool,
    /// DIMACS variable count. Derived clauses may use extension variables beyond this.
    num_vars: usize,
    /// Scratch space: literal marks for deletion content verification and
    /// blocked clause checking (ER proofs).
    /// Indexed by `Literal::index()` (which is `2*var_id + polarity_bit`).
    /// CaDiCaL lratchecker.cpp:634-649 (delete_verified), :384-444 (check_blocked).
    marks: Vec<bool>,
    /// Per-literal scratch for resolution and blocked clause checks.
    checked_lits: Vec<bool>,
    /// Generation counter for O(1) duplicate hint detection (#5267).
    hint_generation: u32,
    /// Stack of `checked_lits` indices that were set to `true`.
    /// Used for O(touched) cleanup instead of O(num_vars) full scan
    /// after each resolution check. Without this, resolution checking
    /// is O(n × num_vars) on long proof chains (#5263 perf regression).
    checked_stack: Vec<usize>,
    /// Per-literal occurrence lists: `occ_lists[lit.index()]` contains clause IDs
    /// that include `lit`. Used by RAT completeness check for O(occ) lookup instead
    /// of O(n) full-database scan. Lazy deletion: deleted clause IDs are skipped
    /// during iteration. Reference: drat-trim `intro` array, ay-drat-check #5309.
    occ_lists: Vec<Vec<u64>>,
    /// Strict (fail-fast) mode: first failure prevents subsequent operations.
    strict: bool,
    /// Set by any failing operation when `strict` is `true`, and by the
    /// constructor when the requested universe exceeds [`MAX_DENSE_VARS`].
    /// Once set, all further `add_derived`, `add_original`, `delete`, and
    /// `delete_verified` calls return `false` without processing.
    pub(crate) failed: bool,
    /// Prevents double-conclusion in `conclude_unsat()`.
    concluded: bool,
    /// Last derived clause ID for monotonicity debug checks.
    last_derived_id: u64,
}

impl LratChecker {
    /// Borrow verification statistics (#5319).
    pub fn stats(&self) -> &Stats {
        &self.stats
    }

    /// Create a new LRAT checker sized for `num_vars` variables.
    /// Default: strict (fail-fast) mode. Use `new_lenient()` for soft-failure.
    pub fn new(num_vars: usize) -> Self {
        Self::with_strict(num_vars, true)
    }

    /// Create a new LRAT checker with lenient (soft-failure) mode.
    pub fn new_lenient(num_vars: usize) -> Self {
        Self::with_strict(num_vars, false)
    }

    /// Build a checker for variables `0..num_vars`.
    ///
    /// A universe beyond [`MAX_DENSE_VARS`] is refused rather than allocated:
    /// every frontend rejects such a formula before constructing a checker,
    /// and on the library API it used to demand dense arrays of up to
    /// `2 * usize::MAX` slots (a capacity-overflow panic, or an abort from
    /// the allocator). A universe inside the envelope is still up to 2^27
    /// literal slots (3 GiB for `occ_lists`), so its arrays are allocated
    /// fallibly, and an allocator refusal is refused the same way instead of
    /// aborting the process. A refused checker starts with an empty
    /// universe, already failed (`stats.failures == 1`), so every operation
    /// returns `false` and no proof can conclude [`ConcludeResult::Verified`].
    fn with_strict(num_vars: usize, strict: bool) -> Self {
        if num_vars > MAX_DENSE_VARS {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: num_vars={num_vars} exceeds the dense variable envelope \
                 {MAX_DENSE_VARS}; refusing to allocate"
            );
            return Self::from_dense(None, strict);
        }
        // `num_vars <= 2^26` here, so `2 * num_vars` cannot overflow and
        // every dense array stays below 2^27 entries.
        Self::from_allocation(
            num_vars,
            DenseArrays::try_alloc(num_vars, num_vars * 2),
            strict,
        )
    }

    /// Build a checker for `num_vars` variables from the outcome of
    /// allocating its dense arrays: an allocator refusal yields a refused
    /// checker (see [`Self::with_strict`]).
    fn from_allocation(
        num_vars: usize,
        allocation: Result<DenseArrays, TryReserveError>,
        strict: bool,
    ) -> Self {
        match allocation {
            Ok(dense) => Self::from_dense(Some((num_vars, dense)), strict),
            Err(error) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: cannot allocate the dense arrays for \
                     num_vars={num_vars}: {error}; refusing"
                );
                Self::from_dense(None, strict)
            }
        }
    }

    /// Build a checker over already allocated dense arrays for a universe of
    /// `universe` variables, or a refused checker when `dense` is `None`.
    fn from_dense(dense: Option<(usize, DenseArrays)>, strict: bool) -> Self {
        let (universe, dense, refused) = match dense {
            Some((universe, dense)) => (universe, dense, false),
            None => (0, DenseArrays::default(), true),
        };
        let mut stats = Stats::default();
        if refused {
            stats.failures = 1;
        }
        Self {
            clause_arena: Vec::new(),
            clause_index: det_hash_map_new(),
            weakened_clauses: det_hash_map_new(),
            assigns: dense.assigns,
            trail: Vec::new(),
            stats,
            has_empty_clause: false,
            num_vars: universe,
            // 2 slots per variable (positive and negative polarity).
            marks: dense.marks,
            checked_lits: dense.checked_lits,
            hint_generation: 0,
            checked_stack: Vec::new(),
            occ_lists: dense.occ_lists,
            strict,
            failed: refused,
            concluded: false,
            last_derived_id: 0,
        }
    }

    /// Check whether a clause is tautological using the `marks` array.
    /// Allocation-free O(clause_len) with O(clause_len) cleanup (#5267).
    fn check_tautological(&mut self, clause: &[Literal]) -> bool {
        let mut found = false;
        for &lit in clause {
            self.ensure_mark_capacity(lit);
            self.ensure_mark_capacity(lit.negated());
            if self.marks[lit.negated().index()] {
                found = true;
                break;
            }
            self.marks[lit.index()] = true;
        }
        for &lit in clause {
            let idx = lit.index();
            if idx < self.marks.len() {
                self.marks[idx] = false;
            }
        }
        found
    }

    /// Record a failure. In strict mode, blocks all subsequent operations.
    #[inline]
    fn record_failure(&mut self) {
        self.stats.failures = self.stats.failures.saturating_add(1);
        if self.strict {
            self.failed = true;
        }
    }

    /// Set strict (fail-fast) mode. When enabled, any verification failure
    /// causes all subsequent operations to return false immediately.
    /// Default: true (CaDiCaL-compatible behavior).
    pub fn set_strict(&mut self, strict: bool) {
        self.strict = strict;
    }

    /// Add an original (input) clause. No chain check.
    pub fn add_original(&mut self, clause_id: u64, clause: &[Literal]) -> bool {
        if self.failed || self.concluded {
            return false;
        }
        if clause_id == 0 {
            let _ = writeln!(std::io::stderr(), "LRAT FAIL: clause ID 0 is reserved");
            self.record_failure();
            return false;
        }
        if self.clause_index.contains_key(&clause_id) {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT: duplicate clause ID {clause_id} in original clauses"
            );
            self.record_failure();
            return false;
        }
        for &lit in clause {
            if !self.ensure_var_strict(lit) {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT: literal {lit} exceeds declared num_vars={}",
                    self.num_vars
                );
                self.record_failure();
                return false;
            }
        }
        let taut = self.check_tautological(clause);
        if self.insert_clause(clause_id, clause, taut, true).is_none() {
            self.record_failure();
            return false;
        }
        self.stats.originals = self.stats.originals.saturating_add(1);
        true
    }

    /// Add a trusted clause (e.g., TrustedTransform from inprocessing).
    ///
    /// No chain verification — the clause is accepted as an axiom.
    /// Unlike `add_original`, this allows extension variables beyond
    /// the initial `num_vars` (inprocessing may introduce new variables).
    /// Maintains the strictly-monotonic derived-ID sequence so the clause
    /// can be referenced by later LRAT hints (#7108).
    pub fn add_trusted(&mut self, clause_id: u64, clause: &[Literal]) -> bool {
        if self.failed || self.concluded {
            return false;
        }
        if self.clause_index.contains_key(&clause_id) {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: duplicate clause ID {clause_id} in trusted clause"
            );
            self.record_failure();
            return false;
        }
        if clause_id <= self.last_derived_id {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: non-monotonic trusted clause ID: {clause_id} after {}",
                self.last_derived_id
            );
            self.record_failure();
            return false;
        }
        self.last_derived_id = clause_id;
        if !self.admit_extended(clause, "trusted") {
            return false;
        }
        let taut = self.check_tautological(clause);
        if self.insert_clause(clause_id, clause, taut, false).is_none() {
            self.record_failure();
            return false;
        }
        self.stats.derived = self.stats.derived.saturating_add(1);
        true
    }

    /// Grow the assignment array for every literal of a trusted or derived
    /// `clause`, which may use extension variables beyond `num_vars`.
    ///
    /// Returns `false`, recording a failure, when a literal lies outside the
    /// dense envelope ([`MAX_DENSE_VARS`]). The LRAT frontends refuse such
    /// literals while parsing; this covers the library API, where one literal
    /// of variable `Variable::MAX_ID` would otherwise size the dense arrays
    /// to 2^31 entries.
    fn admit_extended(&mut self, clause: &[Literal], kind: &str) -> bool {
        for &lit in clause {
            if !self.ensure_var_extended(lit) {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: {kind} clause literal {lit} exceeds the dense variable \
                     envelope {MAX_DENSE_VARS}"
                );
                self.record_failure();
                return false;
            }
        }
        true
    }

    /// Verify an entire LRAT proof. Returns true if all steps verify
    /// and `conclude_unsat()` confirms the proof is complete.
    pub fn verify_proof(&mut self, steps: &[LratStep]) -> bool {
        for step in steps {
            match step {
                LratStep::Add { id, clause, hints } => {
                    // Every addition read from an LRAT proof is untrusted and
                    // must pass RUP, RAT, or blocked-clause verification.  In
                    // particular, an empty hint list is also how valid ER
                    // definition clauses are encoded; `add_derived` checks
                    // those with `check_blocked`.  Treating an arbitrary
                    // non-empty, empty-hint addition as `add_trusted` would
                    // incorrectly validate a proof containing an unsupported
                    // axiom.
                    if !self.add_derived(*id, clause, hints) {
                        let lits: Vec<_> = clause.iter().map(ToString::to_string).collect();
                        let _ = writeln!(
                            std::io::stderr(),
                            "LRAT: clause {id} = {lits:?} not implied by hints {hints:?}"
                        );
                        return false;
                    }
                }
                LratStep::Delete { ids } => {
                    for &id in ids {
                        if !self.delete(id) {
                            return false;
                        }
                    }
                }
            }
        }
        self.conclude_unsat() == ConcludeResult::Verified
    }

    /// Add a derived clause and verify its LRAT chain.
    ///
    /// Hints are signed: positive IDs are RUP chain references, negative IDs
    /// mark RAT witness boundaries. See [`LratStep::Add`] for format details.
    pub fn add_derived(&mut self, clause_id: u64, clause: &[Literal], hints: &[i64]) -> bool {
        if self.failed || self.concluded {
            return false;
        }
        if self.clause_index.contains_key(&clause_id) {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: duplicate clause ID {clause_id} in derived clause"
            );
            self.record_failure();
            return false;
        }
        // CaDiCaL lratchecker.cpp:489 requires strictly monotonic clause IDs.
        // Converted from debug_assert to runtime guard for release safety.
        if clause_id <= self.last_derived_id {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: non-monotonic derived clause ID: {clause_id} after {}",
                self.last_derived_id
            );
            self.record_failure();
            return false;
        }
        self.last_derived_id = clause_id;
        if !self.admit_extended(clause, "derived") {
            return false;
        }
        self.stats.derived = self.stats.derived.saturating_add(1);

        // Zero is the hint-list terminator, never a clause reference. Reject
        // it in the direct API as well as i64::MIN, whose negation overflows.
        if hints.iter().any(|&hint| hint == 0 || hint == i64::MIN) {
            self.record_failure();
            return false;
        }

        let ok = self.verify_chain(clause, hints);
        if !ok {
            let failure_num = self.stats.failures.saturating_add(1);
            if failure_num <= 10 {
                let missing: Vec<i64> = hints
                    .iter()
                    .filter(|&&h| h > 0 && !self.clause_index.contains_key(&(h as u64)))
                    .copied()
                    .collect();
                let lits: Vec<_> = clause.iter().map(ToString::to_string).collect();
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL #{failure_num}: clause_id={clause_id} clause={lits:?} \
                     hints={hints:?} missing_hints={missing:?}",
                );
            }
            self.record_failure();
        }

        // Only insert on success (CaDiCaL lratchecker.cpp:525, #5200).
        if ok {
            if clause.is_empty() {
                self.has_empty_clause = true;
            }
            let taut = self.check_tautological(clause);
            if self.insert_clause(clause_id, clause, taut, false).is_none() {
                self.record_failure();
                return false;
            }
        }
        ok
    }

    // clause_lits(), insert_clause(), compact_arena() are in arena.rs
    // delete(), delete_verified(), finalize_clause() are in deletion.rs
    // derived_empty_clause(), conclude_unsat(), stats_summary() are in conclude.rs
}

mod arena;
mod assigns;
mod blocked;
mod chain;
mod conclude;
mod deletion;
mod dense;
mod rat;
mod resolution;
mod types;

#[cfg(test)]
mod proof_coverage_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_algorithm_audit;
#[cfg(test)]
mod tests_algorithm_audit_deletion;
#[cfg(test)]
mod tests_blocked;
#[cfg(test)]
mod tests_cadical_parity;
#[cfg(test)]
mod tests_conclude;
#[cfg(test)]
mod tests_coverage;
#[cfg(test)]
mod tests_dense_envelope;
#[cfg(test)]
mod tests_e2e;
#[cfg(test)]
mod tests_er;
#[cfg(test)]
mod tests_finalization;
#[cfg(test)]
mod tests_fmla_guarded_equiv;
#[cfg(test)]
mod tests_performance;
#[cfg(test)]
mod tests_proptest;
#[cfg(test)]
mod tests_rat;
#[cfg(test)]
mod tests_resolution;
#[cfg(test)]
mod tests_strict_and_throughput;
#[cfg(test)]
mod tests_weaken_restore;
