// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver configuration, shared-state accessors, and integer-bound support.

use crate::assertion_view;
use crate::{LiaSolver, LiaTimings};
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermId;
use ay_core::{FarkasAnnotation, TheoryConflict, TheoryLit};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

impl<'a> LiaSolver<'a> {
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
    pub(super) fn assertion_view(&self) -> &assertion_view::AssertionView {
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
    pub(super) fn should_timeout(&self) -> bool {
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
    pub(super) fn should_try_gomory(&self, cube_tried: bool) -> bool {
        self.gomory_iterations < self.max_gomory_iterations && !cube_tried
    }

    /// Build a deterministic mapping between integer variable TermIds and
    /// contiguous indices. Sorted by TermId for reproducible behavior.
    pub(super) fn build_var_index(&self) -> (HashMap<TermId, usize>, Vec<TermId>) {
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
    pub(super) fn insert_sorted_integer_var(sorted: &mut Vec<TermId>, term: TermId) {
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
    pub(super) fn is_integer(val: &BigRational) -> bool {
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
    pub(super) fn check_integer_bounds_conflict(&mut self) -> Option<TheoryConflict> {
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
}
