// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY LIA - Linear Integer Arithmetic theory solver
//!
//! Implements branch-and-bound over LRA for integer arithmetic,
//! following the DPLL(T) approach where the SAT solver handles branching.
//!
//! ## Algorithm Overview
//!
//! The solver uses lazy branch-and-bound with cutting planes:
//!
//! 1. Solve the LRA (Linear Real Arithmetic) relaxation
//! 2. If UNSAT, return UNSAT (integers can't satisfy it either)
//! 3. If SAT, check if all integer variables have integer values
//! 4. If all integers are satisfied, return SAT
//! 5. Otherwise, try cutting planes (Gomory, then HNF)
//! 6. If no cuts, return a split request for branch-and-bound
//!
//! ## Cutting Planes
//!
//! - **Gomory cuts**: Derived from the simplex tableau. Fast but limited when
//!   the tableau involves slack variables (internal to simplex).
//! - **HNF cuts**: Derived from the original constraint matrix using Hermite
//!   Normal Form. Works even when Gomory cuts fail due to slack variables.
//!
//! The DPLL(T) framework handles the branching by backtracking on the conflict
//! and trying alternative Boolean assignments.

#![warn(missing_docs)]
#![warn(clippy::all)]
// Gaussian-elimination echelon loops index parallel `work` rows by position;
// the index form is the natural expression (mirrors the workspace lint policy).
#![allow(clippy::needless_range_loop)]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

mod affine_implication;
mod assertion_view;
mod bounds;
mod branching;
mod check;
mod cuts;
mod dioph;
mod dioph_bridge;
mod dioph_joint_case_split;
mod dioph_joint_case_split_support;
mod dioph_substitution;
mod dioph_tighten;
mod enumeration;
mod gcd;
mod gcd_accumulative;
mod gcd_tableau;
mod hnf;
pub mod instrument;
mod intsat_bridge;
mod linear_cache;
mod linear_collect;
mod modular;
mod modular_bounds;
mod nelson_oppen;
mod parsing;
mod poly_residual;
mod state;
mod theory_impl;
mod two_var;
mod types;

pub use check::{
    reset_probe_subset_hint, restore_probe_state, save_probe_state, ProbeStateSnapshot,
};
pub(crate) use types::{
    gcd_of_abs, lia_debug_flags, positive_mod, AlgebraicDetectStamp, CutScopeState,
    DirectEnumResult, EnumMatrix, EnumRrefCache, EnumRrefOutcome, IneqOp, LinearCoeffs,
    SubstitutionMap, SubstitutionTriple,
};
pub use types::{DiophState, HnfCutKey, LiaModel, LiaSolver, LiaTimings, StoredCut};

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::FarkasAnnotation;
use ay_core::{
    propagate_tight_bound_equalities, unwrap_not, DiscoveredDisequality, DiscoveredEquality,
    DisequalitySplitRequest, EqualityPropagationResult, Sort, SplitRequest, TheoryConflict,
    TheoryLit, TheoryPropagation, TheoryResult, TheorySolver,
};
use ay_lra::{Bound, GcdRowInfo, LraSolver};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

impl<'a> LiaSolver<'a> {
    /// M-A2 lazy-persistent-combiner: rebind the borrowed term store to a
    /// SUPERSET (append-extended) store (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2).
    ///
    /// SOUNDNESS: `terms` is the only `&'a`-bound field; all else is owned and
    /// `TermId`-keyed. The inner `LraSolver` reads terms through a re-pointable
    /// raw pointer (`set_terms`), which we also re-point here so it tracks the
    /// same store. Because the store is append-only, every previously-resolved
    /// `TermId` maps to identical `TermData`/`Sort` in `new_terms`, so every
    /// cache stays valid. Only sound when `new_terms` is a superset of the
    /// store this solver was built on. Debug-only (shadow arm).
    #[cfg(debug_assertions)]
    pub fn rebind_terms(&mut self, new_terms: &'a TermStore) {
        self.terms = new_terms;
        self.lra.set_terms(new_terms);
    }

    /// Create a new LIA solver
    #[must_use]
    pub fn new(terms: &'a TermStore) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_integer_mode(true);
        LiaSolver {
            terms,
            lra,
            integer_vars: HashSet::default(),
            sorted_integer_vars: Vec::new(),
            int_bounds_dirty: HashSet::default(),
            // Conservative start (#C4): the first bounds-conflict check
            // always scans every integer variable.
            int_bounds_all_dirty: true,
            int_constant_terms: HashMap::default(),
            asserted: Vec::new(),
            const_bool_conflicts: Vec::new(),
            in_search_phase: false,
            dioph_bcp_unproductive_streak: 0,
            scopes: Vec::new(),
            cut_scopes: Vec::new(),
            cut_state_scopes: Vec::new(),
            gomory_iterations: 0,
            // Keep Gomory as a quick first pass; avoid burning entire checks on cycling cuts.
            max_gomory_iterations: 8,
            hnf_iterations: 0,
            hnf_barren_fingerprint: None,
            max_hnf_iterations: 50, // HNF is more expensive, limit more
            seen_hnf_cuts: HashSet::default(),
            seen_hnf_cuts_trail: Vec::new(),
            learned_cuts: Vec::new(),
            dioph_equality_key: Vec::new(),
            dioph_needs_full_check: false,
            dioph_needs_revalidation: false,
            dioph_safe_dependent_vars: HashSet::default(),
            dioph_cached_substitutions: Vec::new(),
            dioph_cached_modular_gcds: Vec::new(),
            dioph_cached_reasons: Vec::new(),
            dioph_modified_bounds: false,
            dioph_bound_term_ids: HashSet::default(),
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::default(),
            propagated_disequality_pairs: HashSet::default(),
            shared_equalities: Vec::new(),
            hidden_interface: false,
            shared_eq_seen: HashSet::default(),
            conflict_probe: false,
            probe_subset_cache: false,
            verify_only: false,
            shared_eq_revision: 0,
            detect_algebraic_cache: None,
            detect_algebraic_calls: 0,
            detect_algebraic_cache_hits: 0,
            probe_alg_incr: None,
            shared_disequalities: Vec::new(),
            pending_shared_eq_conflict: None,
            skip_shared_algebraic: false,
            timeout_callback: None,
            deadline: None,
            direct_enum_witness: None,
            enum_rref_cache: None,
            // #6359: Use process-level cached env vars (OnceLock) to avoid
            // syscalls on every DPLL(T) iteration.
            debug_lia: lia_debug_flags().debug_lia,
            debug_lia_branch: lia_debug_flags().debug_lia_branch,
            debug_lia_check: lia_debug_flags().debug_lia_check,
            debug_lia_nelson_oppen: lia_debug_flags().debug_lia_nelson_oppen,
            debug_patch: lia_debug_flags().debug_patch,
            debug_gcd: lia_debug_flags().debug_gcd,
            debug_gcd_tab: lia_debug_flags().debug_gcd_tab,
            debug_dioph: lia_debug_flags().debug_dioph,
            debug_hnf: lia_debug_flags().debug_hnf,
            debug_mod: lia_debug_flags().debug_mod,
            debug_enum: lia_debug_flags().debug_enum,
            assertion_view_cache: assertion_view::AssertionViewCache::default(),
            linear_cache: Default::default(),
            affine_cache: Default::default(),
            dioph_parse_cache: Default::default(),
            var_index_epoch: 0,
            // Per-theory runtime statistics (#4706)
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            affine_min_core_attempts: 0,
            affine_min_core_successes: 0,
            // Persistent buffers for augment_farkas (#8599)
            reachable_vars_buf: HashSet::default(),
            conflict_vars_buf: HashSet::default(),
            // Real per-phase timings (#8823). Populated during check().
            timings: LiaTimings::default(),
        }
    }

    /// Number of learned HNF cuts stored across soft resets.
    /// Used by combined solver tests to verify cut preservation (#3510).
    pub fn learned_cut_count(&self) -> usize {
        self.learned_cuts.len()
    }

    /// Number of seen HNF cut keys (deduplication set).
    /// Used by combined solver tests to verify cut preservation (#3510).
    pub fn seen_hnf_cut_count(&self) -> usize {
        self.seen_hnf_cuts.len()
    }

    /// Enable combined theory mode on the inner LRA solver.
    /// See `LraSolver::set_combined_theory_mode` for details.
    pub fn set_combined_theory_mode(&mut self, enabled: bool) {
        self.lra.set_combined_theory_mode(enabled);
    }

    /// #uflia-eager-sweep: opt the inner LRA solver into the eager
    /// re-propagation pop semantics. See
    /// `LraSolver::set_eager_repropagate_on_pop`.
    pub fn set_eager_repropagate_on_pop(&mut self, enabled: bool) {
        self.lra.set_eager_repropagate_on_pop(enabled);
    }

    /// Number of Nelson-Oppen shared equalities currently asserted
    /// (diagnostic accessor; see the combiner-check telemetry).
    pub fn shared_equalities_len(&self) -> usize {
        self.shared_equalities.len()
    }

    /// INTERFACE-DIET: mark that the combiner withheld a pure-UF=UF Int equality
    /// from this solver's N-O interface. Sticky until `reset` — an empty
    /// `shared_equalities` can no longer be trusted as a complete interface, so
    /// the finite-domain / enumeration Sat-unlock sites fail-closed.
    pub fn mark_interface_hidden(&mut self) {
        self.hidden_interface = true;
    }

    /// INTERFACE-DIET: whether any pure-UF=UF Int equality was withheld this solve.
    pub fn interface_is_hidden(&self) -> bool {
        self.hidden_interface
    }

    /// INTERFACE-DIET certifier: snapshot the Int terms resident in the LIA
    /// integer-variable registry (the residency source for value-certification).
    pub fn integer_var_terms(&self) -> Vec<TermId> {
        self.integer_vars.iter().copied().collect()
    }

    /// INTERFACE-DIET certifier: RAW LIA candidate-model value of `term` (the
    /// LRA solver's own `get_value`, NEVER the EUF-preferring fallback — #6930:
    /// a certifier that consulted an EUF-agrees-with-EUF value would rubber-stamp
    /// the very arrangement it is meant to check). `None` ⇒ LIA leaves it free.
    pub fn raw_lia_value(&self, term: TermId) -> Option<BigInt> {
        // Int-sorted terms carry integer LRA values; take the numerator (the
        // denominator is 1 for a satisfiable integer assignment). A non-integral
        // rational here means LIA has not yet integer-fixed the column ⇒ treat as
        // free (None), which the certifier handles by materializing.
        let v = self.lra.get_value(term)?;
        if v.is_integer() {
            Some(v.to_integer())
        } else {
            None
        }
    }

    /// INTERFACE-DIET model-identity invariant: whether a finite-domain /
    /// enumeration witness is currently installed (its arrangement was built
    /// from the possibly-incomplete shared-eq set and must not stand under a
    /// hidden interface).
    pub fn has_direct_enum_witness(&self) -> bool {
        self.direct_enum_witness.is_some()
    }

    /// Enable the cached-subset-first farkas probe (#probe-subset-cache) on
    /// this solver. Default OFF; see the field doc in `types.rs` — the batch
    /// guess changes learned-clause content and thus SAT trajectories, so
    /// only trajectory-owning callers (the UFLIA hybrid's bounded lazy
    /// detour) opt in. `AY_PROBE_SUBSET_CACHE=0|1` force-overrides globally.
    pub fn set_probe_subset_cache(&mut self, enabled: bool) {
        self.probe_subset_cache = enabled;
    }

    /// Mark this solver as a verdict-only VERIFICATION instance
    /// (#uflia-verify-only).
    ///
    /// Verification callers (`make_verification_combiner` users) inspect only
    /// the `TheoryResult` variant and discard conflict payloads, so the
    /// post-verdict shared-reason augmentation — including its
    /// full-check-per-equality probe loop — is skipped. The verdict itself is
    /// unchanged: augmentation runs strictly after `check_inner` has decided
    /// `Unsat`/`UnsatWithFarkas` and never flips the variant.
    pub fn set_verify_only(&mut self, verify_only: bool) {
        self.verify_only = verify_only;
    }

    /// Whether combined theory mode is enabled on the inner LRA solver.
    pub fn combined_theory_mode(&self) -> bool {
        self.lra.combined_theory_mode()
    }

    /// Skip shared equalities in `detect_algebraic_equalities` (#6282).
    ///
    /// In AUFLIA mode, array store axioms create dense shared equality systems
    /// (e.g., `select(store(a,i,v),i) = v` for every store). Gaussian elimination
    /// on these produces O(n²) derived equalities that flood EUF with conflicts,
    /// preventing N-O convergence. Disabling shared equality processing in the
    /// algebraic detection lets the array solver handle these relationships directly.
    pub fn set_skip_shared_algebraic(&mut self, skip: bool) {
        self.skip_shared_algebraic = skip;
    }

    /// Seed Nelson-Oppen equality propagation deduplication for a replayed pair.
    ///
    /// AUFLIA creates fresh theory instances across model-equality refinements.
    /// When the previous instance already propagated a reason-validated equality,
    /// the next instance can import that fact and avoid reporting it as fresh
    /// propagation work again.
    pub fn seed_propagated_equality_pair(&mut self, lhs: TermId, rhs: TermId) {
        if lhs == rhs {
            return;
        }
        let pair = if lhs.0 < rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        self.propagated_equality_pairs.insert(pair);
    }

    /// The always-valid incremental assertion view (#C1).
    ///
    /// O(1): maintained in `assert_literal` and truncated via per-scope marks
    /// in `push`/`pop` instead of being rebuilt with an O(asserted) scan +
    /// sort on every access (the pre-#C1 behavior, which dominated BCP-time
    /// checks on boolean-heavy QF_LIA).
    fn assertion_view(&self) -> &assertion_view::AssertionView {
        self.assertion_view_cache.view()
    }

    /// Get timing breakdown for LIA solving phases (#4794, #8823).
    ///
    /// Returns the real accumulated wall-clock time spent in each phase
    /// (`simplex`, `gomory`, `hnf`, `dioph`) measured via `Instant::now()`
    /// inside `check_inner` and `check_during_propagate_inner`. Before #8823
    /// this returned a static zero stub that silently fed dispatch
    /// decisions fake telemetry.
    pub fn timings(&self) -> &LiaTimings {
        &self.timings
    }

    /// Reset accumulated phase timings (#8823).
    ///
    /// Useful for tests and for dispatchers that want to measure a single
    /// query's cost rather than the solver's cumulative lifetime.
    pub fn reset_timings(&mut self) {
        self.timings = LiaTimings::default();
    }

    /// Set a timeout callback for cooperative interruption.
    ///
    /// The callback is checked periodically during the branch-and-bound loop.
    /// When it returns `true`, the theory check returns `ay_core::TheoryResult::Unknown` at the
    /// next checkpoint.
    ///
    /// # Example
    /// ```
    /// # use ay_core::term::TermStore;
    /// # use ay_lia::LiaSolver;
    /// # let terms = TermStore::new();
    /// # let mut solver = LiaSolver::new(&terms);
    /// let start = ay_core::time::Instant::now();
    /// let timeout = std::time::Duration::from_secs(5);
    /// # let timeout = std::time::Duration::from_secs(0);
    /// solver.set_timeout_callback(move || start.elapsed() >= timeout);
    /// # assert!(matches!(
    /// #     ay_core::TheorySolver::check(&mut solver),
    /// #     ay_core::TheoryResult::Unknown
    /// # ));
    /// ```
    pub fn set_timeout_callback<F: Fn() -> bool + 'static>(&mut self, callback: F) {
        self.timeout_callback = Some(Box::new(callback));
    }

    /// Install a hard wall-clock deadline on the LIA solver (#8749).
    ///
    /// Unlike [`Self::set_timeout_callback`] the deadline is also propagated
    /// down into the IntSat probe so its BigInt-heavy conflict loop honours
    /// `--timeout` instead of running until its conflict budget is exhausted.
    /// The two mechanisms are complementary: the callback is checked at LIA
    /// cascade iteration boundaries, while the deadline is checked inside the
    /// IntSat propagation loop.
    pub fn set_deadline(&mut self, deadline: ay_core::time::Instant) {
        self.deadline = Some(deadline);
    }

    /// Deadline to propagate into sub-solvers (currently only the IntSat
    /// probe). Returns `None` when no deadline was installed.
    pub(crate) fn deadline_for_intsat(&self) -> Option<ay_core::time::Instant> {
        self.deadline
    }

    /// Check if the solver should abort due to timeout.
    fn should_timeout(&self) -> bool {
        self.timeout_callback.as_ref().is_some_and(|cb| cb())
            || self
                .deadline
                .is_some_and(|dl| ay_core::time::Instant::now() >= dl)
    }

    /// Return whether this check-iteration may attempt Gomory cuts.
    ///
    /// This intentionally blocks Gomory once cube testing has been attempted.
    /// Even when cube testing fails and bounds are popped, prior relaxations of
    /// this guard caused false UNSAT regressions on modular workloads (#3073).
    fn should_try_gomory(&self, cube_tried: bool) -> bool {
        self.gomory_iterations < self.max_gomory_iterations && !cube_tried
    }

    /// Build a deterministic mapping between integer variable TermIds and
    /// contiguous indices. Sorted by TermId for reproducible behavior.
    fn build_var_index(&self) -> (HashMap<TermId, usize>, Vec<TermId>) {
        let mut term_to_idx = HashMap::default();
        let mut idx_to_term = Vec::new();
        let mut int_vars: Vec<TermId> = self.integer_vars.iter().copied().collect();
        int_vars.sort_by_key(|t| t.0);
        for (idx, term) in int_vars.into_iter().enumerate() {
            term_to_idx.insert(term, idx);
            idx_to_term.push(term);
        }
        debug_assert_eq!(
            term_to_idx.len(),
            idx_to_term.len(),
            "BUG: build_var_index bijection violated: term_to_idx has {} entries, idx_to_term has {}",
            term_to_idx.len(),
            idx_to_term.len()
        );
        debug_assert_eq!(
            idx_to_term.len(),
            self.integer_vars.len(),
            "BUG: build_var_index lost variables: {} indexed vs {} registered",
            idx_to_term.len(),
            self.integer_vars.len()
        );
        (term_to_idx, idx_to_term)
    }

    /// Register a term as an integer variable
    ///
    /// Should be called for all variables declared with Int sort.
    pub fn register_integer_var(&mut self, term: TermId) {
        // A var entering `integer_vars` may already carry LRA bounds — it
        // must be (re)scanned by the next bounds-conflict check (#C4).
        self.mark_int_bound_dirty(term);
        if self.integer_vars.insert(term) {
            // Variable index changed → dioph parse cache rows are stale (#C2).
            self.var_index_epoch += 1;
            Self::insert_sorted_integer_var(&mut self.sorted_integer_vars, term);
        }
    }

    /// Binary-insert `term` into the sorted integer-var mirror (#C4).
    /// Caller guarantees freshness (`integer_vars.insert` returned true).
    fn insert_sorted_integer_var(sorted: &mut Vec<TermId>, term: TermId) {
        match sorted.binary_search_by_key(&term.0, |t| t.0) {
            Err(pos) => sorted.insert(pos, term),
            Ok(_) => debug_assert!(
                false,
                "BUG: sorted_integer_vars already contains fresh var {}",
                term.0
            ),
        }
    }

    /// Record that `term`'s LRA bounds may have been tightened since the last
    /// conflict-free integer-bounds scan (#C4).
    ///
    /// No-op while `int_bounds_all_dirty` is set: the next scan covers every
    /// integer variable anyway, and the flag is only cleared by that scan.
    pub(crate) fn mark_int_bound_dirty(&mut self, term: TermId) {
        if !self.int_bounds_all_dirty {
            self.int_bounds_dirty.insert(term);
        }
    }

    /// Conservative escape hatch (#C4): force the next
    /// `check_integer_bounds_conflict` to scan every integer variable.
    /// Used by paths whose touched-variable set is not precisely known
    /// (Gomory/HNF cut insertion, cube test, learned-cut replay, external
    /// `lra_solver_mut` access, resets).
    pub(crate) fn mark_int_bounds_all_dirty(&mut self) {
        self.int_bounds_all_dirty = true;
        self.int_bounds_dirty.clear();
    }

    /// Check if a rational value is an integer
    fn is_integer(val: &BigRational) -> bool {
        val.denom().is_one()
    }

    /// Detect immediate integer infeasibility from bounds alone.
    ///
    /// For integer variables, strict/real bounds can imply a tightened integer interval.
    /// Example: `x > 5` and `x < 6` with `x : Int` is immediately UNSAT.
    ///
    /// Returns a `TheoryConflict` with Farkas coefficients for interpolation.
    /// For simple bounds conflicts on a single variable, both bounds get coefficient 1.
    ///
    /// #C4 (lia-hot-loop-plan §C4): instead of collecting + sorting every
    /// integer var and converting each bound through `to_big()` per call,
    /// this
    /// - short-circuits to the `int_bounds_dirty` set of vars whose bounds
    ///   may have tightened since the last conflict-free scan (sound because
    ///   LRA bound slots only tighten within a scope and `pop()` only widens
    ///   — a *new* gap requires a tracked tightening; see `types.rs` field
    ///   docs),
    /// - iterates the cached `sorted_integer_vars` for full scans,
    /// - borrows bounds via `get_bounds_ref` (no `Bound` reason-vec clones)
    ///   and compares effective integer bounds through the exact i64
    ///   floor/ceil fast path, falling back to the BigInt path whenever
    ///   either bound is not inline-representable.
    ///
    /// The common (conflict-free) path allocates nothing.
    ///
    /// Determinism: any var with a gap is necessarily dirty, so scanning the
    /// sorted dirty subset returns the same smallest-TermId conflict (with
    /// identical literals and coefficients) as the historical full scan.
    fn check_integer_bounds_conflict(&mut self) -> Option<TheoryConflict> {
        use num_rational::Rational64;

        let mut dirty_scratch: Vec<TermId>;
        let scan: &[TermId] = if self.int_bounds_all_dirty {
            &self.sorted_integer_vars
        } else {
            if self.int_bounds_dirty.is_empty() {
                return None;
            }
            dirty_scratch = self
                .int_bounds_dirty
                .iter()
                .copied()
                .filter(|t| self.integer_vars.contains(t))
                .collect();
            // Sort for deterministic iteration order (matches the historical
            // full-scan order restricted to the dirty subset).
            dirty_scratch.sort_unstable_by_key(|t| t.0);
            &dirty_scratch
        };

        let mut found: Option<TheoryConflict> = None;
        for &term in scan {
            let Some((lower, upper)) = self.lra.get_bounds_ref(term) else {
                continue;
            };
            let (Some(lb), Some(ub)) = (lower, upper) else {
                continue;
            };

            // i64 fast path; exact-BigInt fallback when either bound is Big
            // or the ±1 strict adjustment would overflow (soundness §3:
            // checked i64, Big fallback — both compute the same integers).
            let gap = match (
                Self::effective_int_lower_i64(lb),
                Self::effective_int_upper_i64(ub),
            ) {
                (Some(li), Some(ui)) => li > ui,
                _ => Self::effective_int_lower(lb) > Self::effective_int_upper(ub),
            };
            if !gap {
                continue;
            }

            let mut literals = Vec::new();
            let mut coefficients = Vec::new();

            // Add ALL reasons from both bounds.
            for (reason, reason_value) in lb.reasons.iter().zip(&lb.reason_values) {
                if !reason.is_sentinel() {
                    literals.push(TheoryLit::new(*reason, *reason_value));
                    coefficients.push(Rational64::from(1));
                }
            }
            for (reason, reason_value) in ub.reasons.iter().zip(&ub.reason_values) {
                if !reason.is_sentinel() {
                    literals.push(TheoryLit::new(*reason, *reason_value));
                    coefficients.push(Rational64::from(1));
                }
            }

            debug_assert!(
                !literals.is_empty(),
                "BUG: check_integer_bounds_conflict: empty conflict literals for term {term:?} \
                 with integer bound gap"
            );
            let farkas = FarkasAnnotation::new(coefficients);
            found = Some(TheoryConflict::with_farkas(literals, farkas));
            break;
        }

        if found.is_none() {
            // Conflict-free: certify the current bounds. Conflicts keep the
            // dirty state — the impending pop re-runs through tracked paths.
            self.int_bounds_dirty.clear();
            self.int_bounds_all_dirty = false;
        }
        found
    }

    /// Register terms from a UF-int equality for Nelson-Oppen tracking (#3581).
    ///
    /// This collects integer variables and constants from both sides of the
    /// equality without adding any constraints. Used when a negated UF-int
    /// equality is asserted (value=false) so that constants like 80 in
    /// `(not (= (inv 2) 80))` are available for tight-bound pairing.
    pub fn register_nelson_oppen_terms(&mut self, lhs: TermId, rhs: TermId) {
        self.collect_integer_vars(lhs);
        self.collect_integer_vars(rhs);
    }

    /// Extract integer variables from a term and its subterms.
    /// Also collects integer constant terms for N-O propagation (#3581).
    fn collect_integer_vars(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                // Track integer constants for Nelson-Oppen propagation (#3581).
                // These allow propagate_equalities to pair derived tight bounds
                // (e.g., f(1) = 0) with existing constant terms (TermId for 0).
                self.int_constant_terms.entry(n.clone()).or_insert(term);
            }
            TermData::Var(_, _) => {
                // Check the sort of this term to see if it's an integer
                if matches!(self.terms.sort(term), Sort::Int) {
                    // The enclosing literal/equality may (re)tighten this
                    // var's LRA bounds — mark for the next bounds scan (#C4).
                    self.mark_int_bound_dirty(term);
                    if self.integer_vars.insert(term) {
                        // Variable index changed → dioph parse rows stale (#C2).
                        self.var_index_epoch += 1;
                        Self::insert_sorted_integer_var(&mut self.sorted_integer_vars, term);
                    }
                }
            }
            TermData::App(sym, args) => {
                // Treat Int-sorted "opaque" arithmetic terms as integer variables.
                //
                // In AUFLIA/Nelson-Oppen, terms like (f x) : Int appear inside arithmetic
                // constraints (e.g., (< (f x) y)). The linear parser treats these terms as
                // atomic variables, so they must be tracked as integer vars for:
                // - direct enumeration (must not treat them as 0)
                // - integrality checks / branch-and-bound
                if matches!(self.terms.sort(term), Sort::Int) {
                    let is_atomic_var = match sym.name() {
                        // Linear arithmetic ops are decomposed into their arguments.
                        "+" | "-" => false,
                        "*" => {
                            // Match collect_linear_coeffs(): treat non-linear multiplication as
                            // an opaque variable; otherwise decompose.
                            let non_const_args = args
                                .iter()
                                .filter(|&&arg| {
                                    !matches!(
                                        self.terms.get(arg),
                                        TermData::Const(Constant::Int(_) | Constant::Rational(_))
                                    )
                                })
                                .count();
                            non_const_args > 1
                        }
                        // Everything else (UF apps, select, div/mod, etc) is opaque to linear LIA.
                        _ => true,
                    };
                    if is_atomic_var {
                        // Same dirty marking as the Var case above (#C4).
                        self.mark_int_bound_dirty(term);
                        if self.integer_vars.insert(term) {
                            // Variable index changed → dioph parse rows stale (#C2).
                            self.var_index_epoch += 1;
                            Self::insert_sorted_integer_var(&mut self.sorted_integer_vars, term);
                        }
                    }
                }
                for &arg in args {
                    self.collect_integer_vars(arg);
                }
            }
            TermData::Let(_, body) => {
                self.collect_integer_vars(*body);
            }
            TermData::Not(inner) => {
                self.collect_integer_vars(*inner);
            }
            TermData::Ite(cond, then_branch, else_branch) => {
                self.collect_integer_vars(*cond);
                self.collect_integer_vars(*then_branch);
                self.collect_integer_vars(*else_branch);
            }
            _ => {}
        }
    }

    /// Equality-dense systems benefit from deeper HNF exploration.
    /// We treat a system as dense once equalities cover at least half of variables.
    fn is_equality_dense(num_equalities: usize, num_vars: usize) -> bool {
        num_vars > 0 && num_equalities.saturating_mul(2) >= num_vars
    }

    fn hnf_iteration_budget(num_equalities: usize, num_vars: usize) -> usize {
        if Self::is_equality_dense(num_equalities, num_vars) {
            20
        } else {
            2
        }
    }

    /// Extract the current model if satisfiable
    ///
    /// Returns None if the last check was not SAT or if integer constraints
    /// are not satisfied.
    /// Terms that appear in a CROSS-THEORY equality LIA was told about
    /// (`assert_shared_equality`). LIA is the authority for these: the
    /// equality is a hard constraint the LRA relaxation of a sibling solver
    /// may never have received (Int-only equalities are routed to LIA
    /// alone). See `reconcile_lia_lra_values` (#reconcile-lia-authority).
    #[must_use]
    pub fn shared_equality_terms(&self) -> HashSet<TermId> {
        let mut out: HashSet<TermId> = HashSet::default();
        for (lhs, rhs, _) in &self.shared_equalities {
            out.insert(*lhs);
            out.insert(*rhs);
        }
        out
    }

    /// Extract an integer model for the current satisfiable state, preferring
    /// a direct enumeration witness when one was found.
    pub fn extract_model(&self) -> Option<LiaModel> {
        let debug = self.debug_lia;

        if let Some(model) = &self.direct_enum_witness {
            return Some(model.clone());
        }

        let lra_model = self.lra.extract_model();
        let mut values = HashMap::default();

        if debug {
            safe_eprintln!(
                "[LIA] extract_model: lra_model has {} values, integer_vars has {} entries",
                lra_model.values.len(),
                self.integer_vars.len()
            );
            for &term in &self.integer_vars {
                safe_eprintln!("[LIA] integer_var: term {}", term.0);
            }
        }

        // Convert rational values to integers, checking constraints
        for (&term, val) in &lra_model.values {
            if debug {
                safe_eprintln!(
                    "[LIA] checking term {}: in integer_vars={}",
                    term.0,
                    self.integer_vars.contains(&term)
                );
            }
            if self.integer_vars.contains(&term) {
                if Self::is_integer(val) {
                    if debug {
                        safe_eprintln!("[LIA] term {} -> int value {}", term.0, val.numer());
                    }
                    values.insert(term, val.numer().clone());
                } else {
                    // Integer constraint violated
                    if debug {
                        safe_eprintln!("[LIA] term {} has non-integer value {}", term.0, val);
                    }
                    return None;
                }
            }
        }

        if debug {
            safe_eprintln!("[LIA] final model has {} values", values.len());
        }
        // Every registered integer variable that appears in the LRA model should
        // have an integer value in our extracted model. Missing variables indicate
        // a term registration or model extraction bug.
        debug_assert!(
            self.integer_vars
                .iter()
                .all(|v| !lra_model.values.contains_key(v) || values.contains_key(v)),
            "BUG: extract_model: integer variable present in LRA model but missing from LIA model"
        );
        Some(LiaModel { values })
    }

    /// Get the underlying LRA solver
    pub fn lra_solver(&self) -> &LraSolver {
        &self.lra
    }

    /// Collect bound conflicts from the underlying LRA relaxation.
    pub fn collect_all_bound_conflicts(&self, skip_first: bool) -> Vec<TheoryConflict> {
        self.lra.collect_all_bound_conflicts(skip_first)
    }

    /// Get mutable access to the underlying LRA solver
    ///
    /// Used by NIA to add tangent plane constraints directly.
    pub fn lra_solver_mut(&mut self) -> &mut LraSolver {
        // External `&mut` access can tighten arbitrary bounds (e.g. NIA
        // tangent planes) — conservatively rescan everything (#C4).
        self.mark_int_bounds_all_dirty();
        &mut self.lra
    }

    /// Count integer variables that are currently fixed (lower bound == upper bound).
    ///
    /// Used by the iterative Dioph tightening loop to detect when tightening
    /// has fixed new variables, which signals that re-running the Dioph solver
    /// may discover new substitutions (Z3's continue_with_check pattern).
    fn count_fixed_integer_vars(&self) -> usize {
        let mut count = 0;
        for &term_id in &self.integer_vars {
            if let Some((Some(lb), Some(ub))) = self.lra.get_bounds(term_id) {
                if lb.value == ub.value {
                    count += 1;
                }
            }
        }
        count
    }

    /// Count the number of equality constraints in the asserted literals.
    ///
    /// Used to detect equality-dense problems where more aggressive HNF
    /// cut generation is beneficial. Served from the incremental view (#C1):
    /// `positive_equalities` contains exactly the `(= a b)` atoms asserted
    /// true (including repeats), matching the previous O(asserted) scan.
    fn count_equalities(&self) -> usize {
        self.assertion_view().positive_equalities.len()
    }

    /// Count asserted arithmetic relational atoms (any polarity): `=`, `<=`,
    /// `>=`, `<`, `>`. Used to recognize the "single isolated constraint" shape
    /// where pinning a concrete Diophantine witness is provably sound: when the
    /// only arithmetic atom in the system is one equality over exactly the free
    /// variables, no other constraint can rule the witness out.
    pub(crate) fn count_arith_atoms(&self) -> usize {
        let mut count = 0;
        for &(literal, _value) in &self.asserted {
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if matches!(name.as_str(), "=" | "<=" | ">=" | "<" | ">") && args.len() == 2 {
                    count += 1;
                }
            }
        }
        count
    }

    /// Stable, sorted, deduplicated key for the currently asserted equality
    /// atoms (#C5). Served from the incrementally maintained view instead of
    /// re-scanning and re-sorting `asserted` on every BCP-time check.
    ///
    /// Used to avoid re-running Diophantine solving when only inequalities
    /// change (common during branch-and-bound).
    fn equality_key(&self) -> &[TermId] {
        &self.assertion_view().equality_key
    }
}

#[cfg(kani)]
mod verification;

#[cfg(test)]
mod dioph_conflict_tests;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
