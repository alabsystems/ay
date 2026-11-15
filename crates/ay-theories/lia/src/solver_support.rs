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

impl LiaSolver<'_> {
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

    /// Enable the lattice-closure refutation before unbounded splits
    /// (`lattice_refute_bridge`). Default ON. The NIA turns it off: its check
    /// loop steers its own refinement (bounded enumeration, capped search) from
    /// the inner LIA's split requests. Measured 2026-09-29: on 280 SMT-COMP 2025
    /// QF_NIA/QF_UFNIA files the closure decided nothing new, and it moved the
    /// search of `d10a_the_same_window_solved_twice_continues_its_lanes` off the
    /// path that decides it (into an NIA state the loop answers `unknown`).
    pub fn set_lattice_closure(&mut self, enabled: bool) {
        self.lattice_closure = enabled;
    }

    /// Push a scope for an enclosing NIA's model GUESSES (sign cuts, rounding /
    /// patch pins, factor-split pins). Identical to `TheorySolver::push`,
    /// except that while any such scope is open the placeholder reason of a
    /// reasonless shared equality is not accepted as a premise
    /// (`bound_is_justified`): a guess on the same variable cites the same
    /// term (#nonlinear-shared-reasons).
    pub fn push_tentative(&mut self) {
        self.tentative_scope_marks.push(self.scopes.len());
        ay_core::TheorySolver::push(self);
    }

    /// Whether a scope opened by [`Self::push_tentative`] is still open.
    pub(crate) fn in_tentative_scope(&self) -> bool {
        !self.tentative_scope_marks.is_empty()
    }

    /// Pop a scope the NIA opened for its tentative sign cuts / patches
    /// (#nia-sign-cut-soundness). Identical to `TheorySolver::pop` except
    /// that the Nelson-Oppen sent-equality dedup and the pending equalities
    /// are preserved: EUF has not backtracked, so nothing needs re-sending.
    pub fn pop_tentative(&mut self) {
        self.pop_inner(true);
    }

    /// Shared body of `TheorySolver::pop` and [`Self::pop_tentative`].
    pub(crate) fn pop_inner(&mut self, tentative: bool) {
        if let Some(mark) = self.scopes.pop() {
            let depth = self.scopes.len();
            while self
                .tentative_scope_marks
                .last()
                .is_some_and(|&opened_at| opened_at >= depth)
            {
                self.tentative_scope_marks.pop();
            }
            debug_assert!(
                mark <= self.asserted.len(),
                "BUG: LIA pop: scope mark {} exceeds asserted length {}",
                mark,
                self.asserted.len()
            );
            self.asserted.truncate(mark);
            // #C3: drop const-bool conflicts whose literal was just popped, so a
            // reported conflict reason is always a live literal (#8784). The Vec
            // is empty in the overwhelmingly common case, so retain is O(1).
            if !self.const_bool_conflicts.is_empty() {
                self.const_bool_conflicts.retain(|(idx, _)| *idx < mark);
            }
            // Truncate the incremental view in the SAME transaction as the
            // asserted-trail truncation (#C1, plan §3.4): otherwise
            // `conflict_reasons_all_live` could see stale view-derived
            // literals and publish a false-UNSAT conflict.
            self.assertion_view_cache.on_pop();
            ay_core::TheorySolver::pop(&mut self.lra);
            self.direct_enum_witness = None;
            let cut_mark = self.cut_scopes.pop().unwrap_or(0);
            self.learned_cuts.truncate(cut_mark);
            // Restore cut state from the outer scope (#3685).
            // Previously these were hard-reset to 0/empty, losing the outer
            // scope's iteration progress and seen-cut deduplication set.
            let saved = self.cut_state_scopes.pop().unwrap_or_default();
            self.gomory_iterations = saved.gomory_iterations;
            self.hnf_iterations = saved.hnf_iterations;
            // #C7: undo only the HNF-cut keys inserted in this scope, restoring
            // the exact pre-push `seen_hnf_cuts` (#3685) without a per-push clone.
            while self.seen_hnf_cuts_trail.len() > saved.seen_hnf_cuts_mark {
                if let Some(key) = self.seen_hnf_cuts_trail.pop() {
                    self.seen_hnf_cuts.remove(&key);
                }
            }
            // #shared-eq-idempotent: drop exactly the keys whose trail entries
            // this pop removes, keeping `shared_eq_seen` in lockstep with the
            // trail. Insertion is deduped, so each key occurs at most once on
            // the trail and this undo is exact (same discipline as #C7's
            // `seen_hnf_cuts_trail`).
            while self.shared_equalities.len() > saved.shared_eq_mark {
                if let Some((lhs, rhs, _)) = self.shared_equalities.pop() {
                    let key = if lhs.0 <= rhs.0 {
                        (lhs, rhs)
                    } else {
                        (rhs, lhs)
                    };
                    self.shared_eq_seen.remove(&key);
                }
            }
            // Truncation changes the algebraic-detection input set; bump the
            // revision so the memo cannot alias a pop+push of equal length.
            self.shared_eq_revision += 1;
            self.shared_disequalities.truncate(saved.shared_diseq_mark);
            // #8124: Clear pending shared equality conflict on pop — the conflict
            // may have been derived from literals that are no longer asserted.
            self.pending_shared_eq_conflict = None;
            // #C8: Preserve the equality-derived Diophantine caches across pop.
            // They depend only on the asserted equality SET (captured by
            // `dioph_equality_key`), not on the inequality bounds that
            // branch-and-bound and BMC backtracking churn. Re-solving the full
            // Diophantine system after EVERY backtrack was a dominant per-check
            // cost on deep (depth>=2) BMC counterexamples. Instead, mark the
            // caches for re-validation; the unconditional `dioph_equality_key`
            // comparison in check()/check_during_propagate() reuses them when the
            // equality set is unchanged and drops+rebuilds them when it changed —
            // the exact staleness gate #3736 references. This mirrors what
            // `soft_reset` already does across a (more drastic) LRA reset
            // (parsing.rs:437-453).
            self.dioph_needs_revalidation = true;
            // The bound-tracking state records bounds Dioph ADDED to LRA; those
            // bounds were just popped, so it is stale. Clear it conservatively;
            // propagate_bounds_through_substitutions repopulates it in the new
            // scope (#8147).
            self.dioph_modified_bounds = false;
            self.dioph_bound_term_ids.clear();

            // AUDIT FIX [P]90: Clear propagated_equality_pairs on pop().
            // Without this, after backtracking, equalities that were previously propagated
            // won't be re-propagated even if they get re-established. This could cause
            // the N-O combination to miss conflicts in alternate search branches.
            //
            // NOT on a TENTATIVE pop (#nia-sign-cut-soundness): the NIA pops
            // its sign-cut / patch scope at the start of every `check()`, in
            // the middle of a Nelson-Oppen round in which EUF has NOT
            // backtracked. Clearing the dedup there made LIA re-send every
            // tight-bound equality on every round, the combiner counted them
            // as new, and the interface fixpoint ran to its 100-iteration
            // limit and answered `unknown` on decided QF_UFNIA inputs. An
            // equality's validity is a function of its (live, asserted)
            // reasons, not of the LIA scope it was discovered in, so the
            // sent-set and the pending list stay.
            if !tentative {
                self.propagated_equality_pairs.clear();
                self.propagated_disequality_pairs.clear();
                self.pending_equalities.clear();
            }
        }
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
    pub fn set_timeout_callback<F: Fn() -> bool + Send + 'static>(&mut self, callback: F) {
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
    /// Blocked once this check has tried the cube test. This is search order,
    /// not a soundness guard. #3073 (2026-02-10) added the block after
    /// relaxing it to "after a successful cube" (z4 9208a5cf) made
    /// `(distinct (mod x 3) (mod (+ x 1) 3)) /\ 0 <= x < 10` answer UNSAT.
    /// Rebuilt at 9208a5cf (2026-11-08), that false UNSAT persists with the
    /// cube test disabled. The slack rows of the time were written over basic
    /// variables, and a later pivot left two rows owning one basic variable.
    /// `get_or_create_slack` substitutes basic variables since #4842. The
    /// Sat path runs Gomory before the cube test since 20cf3eea8, which wins
    /// `v20_problem__019`. the development design notes 2026-11-08 has the
    /// measurements.
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
            // JUSTIFIED bounds only (#nia-sign-cut-soundness). Checked after
            // the cheap presence test so the conflict-free hot path pays
            // nothing extra beyond two trail lookups per bounded var.
            if !self.bound_is_justified(lb) || !self.bound_is_justified(ub) {
                continue;
            }

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
