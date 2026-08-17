// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen fixpoint check loop for TheoryCombiner.
//!
//! Separated from `combiner.rs` for file-size compliance (#6332 Wave 0).

// Wave 1: TheoryCombiner now used in production dispatch (#6332).
#![allow(clippy::result_large_err)]

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{
    DiscoveredEquality, Sort, Symbol, TermData, TermId, TermStore, TheoryLit, TheoryResult,
    TheorySolver,
};
use ay_euf::EufSolver;
use ay_lia::LiaSolver;
use num_bigint::BigInt;

use super::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, discover_model_equality,
    drain_equalities_for_propagation, forward_non_sat, propagate_array_index_info,
    propagate_equalities_to, triage_lia_result, triage_lra_result_deferred,
};
use super::combiner::TheoryCombiner;
use super::interface_bridge::{
    evaluate_arith_term_with_reasons, evaluate_real_arith_term_with_reasons,
    has_unjustified_int_leaf, lia_get_int_value_with_reasons, lra_get_real_value_with_reasons,
};
use super::theory_stats;

/// Result of the arithmetic check + propagation step.
pub(super) struct ArithStepResult {
    pub(super) is_unknown: bool,
    pub(super) deferred: Option<TheoryResult>,
    pub(super) new_equalities: bool,
    /// #8469: Whether new disequalities were propagated from arith to EUF.
    pub(super) new_disequalities: bool,
}

/// Outcome of the INTERFACE-DIET pre-Sat arrangement certifier (C3/R1).
enum DietCertifyOutcome {
    /// Arrangement value-certified against RAW LIA values ⇒ accept Sat.
    Ok,
    /// A withheld equality was materialized on demand ⇒ re-run the fixpoint.
    Rerun,
    /// Fail-closed (witness under hidden interface / unexplainable pair / budget).
    Unknown,
}

/// Result of EUF-to-arithmetic propagation step (#8163).
struct EufPropResult {
    /// Number of equalities propagated from EUF to arithmetic.
    eq_count: usize,
    /// Number of disequalities propagated from EUF to arithmetic.
    diseq_count: usize,
}

fn remember_deferred_arith_result(slot: &mut Option<TheoryResult>, result: Option<TheoryResult>) {
    let Some(result) = result else {
        return;
    };
    match result {
        TheoryResult::NeedSplit(_)
        | TheoryResult::NeedDisequalitySplit(_)
        | TheoryResult::NeedExpressionSplit(_)
        | TheoryResult::NeedExpressionSplits(_)
            if deferred_result_priority(&result)
                >= slot.as_ref().map_or(0, deferred_result_priority) =>
        {
            *slot = Some(result);
        }
        _ => {}
    }
}

fn deferred_result_priority(result: &TheoryResult) -> usize {
    match result {
        TheoryResult::NeedExpressionSplits(splits) if splits.len() > 1 => 4,
        TheoryResult::NeedExpressionSplit(_) | TheoryResult::NeedExpressionSplits(_) => 3,
        TheoryResult::NeedSplit(_) | TheoryResult::NeedDisequalitySplit(_) => 2,
        _ => 0,
    }
}

fn take_deferred_before_later_conflict(
    slot: &mut Option<TheoryResult>,
    later_result: &TheoryResult,
) -> Option<TheoryResult> {
    if !matches!(
        later_result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ) {
        return None;
    }
    let should_preempt = matches!(
        slot.as_ref(),
        Some(TheoryResult::NeedExpressionSplits(splits)) if splits.len() > 1
    );
    if should_preempt {
        return slot.take();
    }
    None
}

impl TheoryCombiner<'_> {
    /// The full N-O fixpoint check loop.
    pub(super) fn nelson_oppen_check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();
        // Inc0-0c: combiner-check vs fixpoint-iteration attribution
        // (--lia-instrument-gated, write-only).
        ay_lia::instrument::bump_no_check();
        const MAX_ITERATIONS: usize = 100;
        let mut deferred_arith_result: Option<TheoryResult> = None;
        // INTERFACE-DIET: fresh materialization-round budget per combiner check.
        self.diet_certify_rounds = 0;
        // #8319: AY_MAX_FIXPOINT_ROUNDS caps the N-O loop for debugging.
        let max_iters = crate::theory_debug_flags::max_fixpoint_rounds()
            .unwrap_or(MAX_ITERATIONS)
            .min(MAX_ITERATIONS);

        // #8469: Configure EUF with shared arithmetic terms so
        // propagate_equalities() can collect disequalities through
        // the unified path instead of a separate call.
        if self.lia.is_some() || self.lra.is_some() {
            let shared_terms = match &self.interface {
                Some(ib) => ib.sorted_arith_terms(),
                None => Vec::new(),
            };
            self.euf.set_shared_arith_terms(shared_terms);
        }

        for iteration in 0..max_iters {
            // Inc0-0c: fixpoint-iteration count (write-only telemetry).
            ay_lia::instrument::bump_no_fixpoint_iter();
            // #8637: Check interrupt flag at the top of each N-O iteration.
            // Without this check, the loop runs up to 100 iterations with no
            // opportunity for the caller to cancel.
            if self.is_interrupted() {
                theory_stats::inc_unknown_returns();
                theory_stats::inc_no_rounds(iteration as u64);
                return TheoryResult::Unknown;
            }

            let arith = match self.check_arith_step(debug, iteration) {
                Ok(a) => a,
                Err(result) => {
                    // #8596: When arithmetic finds UNSAT and we have arrays,
                    // give the array theory a chance to contribute lemmas or
                    // model equalities before accepting the conflict. The
                    // arithmetic conflict may be conditional on array index
                    // disequalities that haven't been case-split yet.
                    //
                    // Example: select(a,y)=1 with a=store(const(0),x,1)
                    // requires x=y. Without this, LIA finds UNSAT (select
                    // value is 0 when x!=y) before arrays can request the
                    // model equality x=y.
                    // #7956: Only invoke the array rescue when the arithmetic
                    // conflict actually references array-theory terms (select /
                    // store / Array-sorted literals). If the conflict lives
                    // entirely in the pure arithmetic / EUF fragment, the
                    // array theory cannot contribute a lemma or model equality
                    // that resolves it, and swallowing the conflict blocks SAT
                    // from backtracking over flippable literals (e.g. spurious
                    // EUF-propagated `(= 0 seq_len(vec)) = true`). Forwarding
                    // conflicts without array terms preserves completeness.
                    let gate_ok = self.arrays.is_some()
                        && match &result {
                            TheoryResult::Unsat(lits) => {
                                conflict_involves_array_theory(self.terms, lits)
                            }
                            TheoryResult::UnsatWithFarkas(conflict) => {
                                conflict_involves_array_theory(self.terms, &conflict.literals)
                            }
                            _ => false,
                        };
                    if gate_ok {
                        if let Some(array_result) =
                            self.try_array_rescue_on_arith_conflict(debug, iteration)
                        {
                            if debug {
                                safe_eprintln!(
                                    "[N-O {}] Arithmetic UNSAT rescued by array theory: {:?}",
                                    self.label,
                                    std::mem::discriminant(&array_result),
                                );
                            }
                            theory_stats::inc_no_rounds((iteration + 1) as u64);
                            return array_result;
                        }
                    } else if debug
                        && self.arrays.is_some()
                        && matches!(
                            &result,
                            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                        )
                    {
                        safe_eprintln!(
                            "[N-O {}] Arithmetic UNSAT forwarded to SAT (no array-theory terms in conflict)",
                            self.label,
                        );
                    }
                    if let Some(deferred) =
                        take_deferred_before_later_conflict(&mut deferred_arith_result, &result)
                    {
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] Returning deferred arithmetic split batch before later conflict",
                                self.label,
                            );
                        }
                        theory_stats::inc_no_rounds((iteration + 1) as u64);
                        return deferred;
                    }
                    // #8165: record rounds completed before early return
                    theory_stats::inc_no_rounds((iteration + 1) as u64);
                    return result;
                }
            };
            remember_deferred_arith_result(&mut deferred_arith_result, arith.deferred);
            let mut has_new_eqs = arith.new_equalities;

            let (bridge_eqs, bridge_speculative) = self.evaluate_bridge(debug);
            self.record_cross_theory_equalities(&bridge_eqs);
            for eq in &bridge_eqs {
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                if let Some(lia) = &mut self.lia {
                    lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                }
            }
            has_new_eqs |= !bridge_eqs.is_empty();

            theory_stats::inc_check_euf();
            let euf_check = self.euf.check();
            if let Some(result) = forward_non_sat(euf_check) {
                if let Some(deferred) =
                    take_deferred_before_later_conflict(&mut deferred_arith_result, &result)
                {
                    if debug {
                        safe_eprintln!(
                            "[N-O {}] Returning deferred arithmetic split batch before EUF conflict",
                            self.label,
                        );
                    }
                    theory_stats::inc_no_rounds((iteration + 1) as u64);
                    return deferred;
                }
                // #8165: EUF conflict — record domain and rounds
                if matches!(
                    &result,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                ) {
                    theory_stats::inc_conflict_euf();
                }
                if matches!(&result, TheoryResult::Unknown) {
                    theory_stats::inc_unknown_returns();
                }
                theory_stats::inc_no_rounds((iteration + 1) as u64);
                return result;
            }

            let euf_prop = match self.propagate_euf_to_arith(debug, iteration) {
                Ok(r) => r,
                Err(conflict) => {
                    if let Some(deferred) =
                        take_deferred_before_later_conflict(&mut deferred_arith_result, &conflict)
                    {
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] Returning deferred arithmetic split batch before propagation conflict",
                                self.label,
                            );
                        }
                        theory_stats::inc_no_rounds((iteration + 1) as u64);
                        return deferred;
                    }
                    // #8165: propagation conflict — record rounds
                    theory_stats::inc_no_rounds((iteration + 1) as u64);
                    return conflict;
                }
            };

            match self.check_arrays_step(debug, iteration) {
                Ok(arr_new) => {
                    has_new_eqs |= arr_new;
                }
                Err(result) => {
                    if let Some(deferred) =
                        take_deferred_before_later_conflict(&mut deferred_arith_result, &result)
                    {
                        if debug {
                            safe_eprintln!(
                                "[N-O {}] Returning deferred arithmetic split batch before array conflict",
                                self.label,
                            );
                        }
                        theory_stats::inc_no_rounds((iteration + 1) as u64);
                        return deferred;
                    }
                    // #8165: array conflict — record domain and rounds
                    if matches!(
                        &result,
                        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                    ) {
                        theory_stats::inc_conflict_arrays();
                    }
                    theory_stats::inc_no_rounds((iteration + 1) as u64);
                    return result;
                }
            }

            // #8163, #8469: Include disequality propagations in fixpoint convergence.
            // When theories propagate new disequalities in either direction
            // (EUF->arith or arith->EUF), the receiving solver may discover new
            // equalities or conflicts in response. The loop must continue until
            // no new information flows in any direction.
            if !has_new_eqs
                && !arith.new_disequalities
                && euf_prop.eq_count == 0
                && euf_prop.diseq_count == 0
            {
                if debug && iteration > 0 {
                    safe_eprintln!(
                        "[N-O {}] Fixpoint reached after {} iterations",
                        self.label,
                        iteration + 1
                    );
                }
                match self.handle_fixpoint(
                    debug,
                    arith.is_unknown,
                    deferred_arith_result.take(),
                    &bridge_speculative,
                ) {
                    Some(result) => {
                        // #8165: record rounds at fixpoint
                        if matches!(&result, TheoryResult::Unknown) {
                            theory_stats::inc_unknown_returns();
                        }
                        theory_stats::inc_no_rounds((iteration + 1) as u64);
                        return result;
                    }
                    None => continue,
                }
            }

            // Non-convergence is a SOUND fallback, never a crash. Historically
            // the final iteration asserted (panicked) with "Nelson-Oppen loop
            // did not converge" — but a theory-combination fixpoint that fails
            // to settle within the bound must return `Unknown`, not abort the
            // whole solver: `unknown` is always a sound verdict, whereas the
            // panic turned a legitimate (if pathological) AUFLIA instance into a
            // process crash. The loop simply ends and falls through to the
            // `TheoryResult::Unknown` return below. (#8319: a user-capped
            // `AY_MAX_FIXPOINT_ROUNDS` reaches the same fallback.)
            if debug && iteration == max_iters - 1 {
                safe_eprintln!(
                    "[N-O {}] did not converge in {} iterations; returning Unknown (sound fallback)",
                    self.label,
                    max_iters,
                );
            }
        }

        // #8165: Unknown from non-convergence (or #8319 capped rounds)
        theory_stats::inc_unknown_returns();
        theory_stats::inc_no_rounds(max_iters as u64);
        TheoryResult::Unknown
    }

    // --- Per-step helpers ---

    fn check_arith_step(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Result<ArithStepResult, TheoryResult> {
        if let Some(lia) = &mut self.lia {
            theory_stats::inc_check_lia();
            let result = lia.check();
            let is_unknown = matches!(&result, TheoryResult::Unknown);
            let (deferred, early) = triage_lia_result(result);
            if let Some(ref early) = early {
                // #8165: track LIA domain conflicts
                if matches!(
                    early,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                ) {
                    theory_stats::inc_conflict_lia();
                }
            }
            if let Some(early) = early {
                return Err(early);
            }
            // #8469: Capture both equality and disequality counts for
            // bidirectional N-O propagation. #8785: retain the equality payload
            // so AUFLIA can persist reason-validated replays across fresh
            // combiner instances.
            let eq_result =
                drain_equalities_for_propagation(lia, debug, self.arith_prop_label, iteration)?;
            let counts = super::check_loops::PropagationCounts {
                equalities: eq_result.equalities.len(),
                disequalities: eq_result.disequalities.len(),
            };
            self.record_cross_theory_equalities(&eq_result.equalities);
            for eq in eq_result.equalities {
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }
            for diseq in eq_result.disequalities {
                self.euf
                    .assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
            }
            // #8165: track per-theory propagation counts
            if counts.equalities > 0 {
                theory_stats::inc_props_lia(counts.equalities as u64);
            }
            Ok(ArithStepResult {
                is_unknown,
                deferred,
                new_equalities: counts.equalities > 0,
                new_disequalities: counts.disequalities > 0,
            })
        } else if let Some(lra) = &mut self.lra {
            theory_stats::inc_check_lra();
            let result = lra.check();
            let is_unknown = matches!(&result, TheoryResult::Unknown);
            let (deferred, early) = triage_lra_result_deferred(result);
            if let Some(ref early) = early {
                // #8165: track LRA domain conflicts
                if matches!(
                    early,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                ) {
                    theory_stats::inc_conflict_lra();
                }
            }
            if let Some(early) = early {
                return Err(early);
            }
            // #8469/#8785: retain equality payload for fresh-combiner replay.
            let eq_result =
                drain_equalities_for_propagation(lra, debug, self.arith_prop_label, iteration)?;
            let counts = super::check_loops::PropagationCounts {
                equalities: eq_result.equalities.len(),
                disequalities: eq_result.disequalities.len(),
            };
            self.record_cross_theory_equalities(&eq_result.equalities);
            for eq in eq_result.equalities {
                self.euf.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }
            for diseq in eq_result.disequalities {
                self.euf
                    .assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
            }
            // #8165: track per-theory propagation counts
            if counts.equalities > 0 {
                theory_stats::inc_props_lra(counts.equalities as u64);
            }
            // #G1-uflra completeness: propagate ENTAILED interface equalities
            // that the LRA individual-tight-bound Nelson-Oppen grouping misses —
            // pairs `a, b` whose DIFFERENCE `a - b` is simplex-pinned to exactly
            // [0,0] while neither `a` nor `b` is individually pinned (e.g.
            // `(+ x 1) = (+ y 1)` ⟹ x=y, or `x<=y ∧ y<=x`). See
            // `propagate_lra_entailed_interface_equalities`.
            let entailed_new = self.propagate_lra_entailed_interface_equalities(debug);
            Ok(ArithStepResult {
                is_unknown,
                deferred,
                new_equalities: counts.equalities > 0 || entailed_new > 0,
                new_disequalities: counts.disequalities > 0,
            })
        } else {
            Ok(ArithStepResult {
                is_unknown: false,
                deferred: None,
                new_equalities: false,
                new_disequalities: false,
            })
        }
    }

    /// Nelson-Oppen completeness: assert into EUF every interface equality
    /// `a = b` that the LRA relaxation ENTAILS because it pins the difference
    /// `a - b` to exactly `[0,0]`, even when neither `a` nor `b` is individually
    /// simplex-pinned. Returns the number of newly-asserted equalities.
    ///
    /// WHY THIS EXISTS (gap #G1-uflra, the analog of the QF_UFLIA fix in
    /// `lia/theory_impl.rs`): LRA's tight-bound N-O grouping only emits `a = b`
    /// when a variable is INDIVIDUALLY pinned (`lb == ub`). From
    /// `(+ x 1) = (+ y 1)` the tableau holds a row pinning `x - y` to 0, but the
    /// simplex is free to place `x, y` anywhere on that line (e.g. `x=y=0` with
    /// EMPTY bound reasons), so neither is individually pinned and `x = y` is
    /// never shared. EUF congruence then never fires on `f(x), f(y)` and
    /// `QF_UFLRA` returns `unknown` (spurious model rejected by the soundness
    /// gate) instead of `unsat`. Note this runs from the COMBINED check loop
    /// only; pure standalone QF_LRA never reaches here.
    ///
    /// SOUNDNESS (Lean invariant (ENT)): `find_entailed_difference_equalities`
    /// returns `(a, b, reasons)` ONLY when the currently-asserted arithmetic
    /// atoms genuinely ENTAIL `a - b == 0` (a `=` atom over `a - b`, or a matched
    /// pair of non-strict `<=`/`>=` atoms pinning it to a closed `[0,0]`) WITH a
    /// NON-EMPTY reason set drawn from those asserted atom literals. Every T-model
    /// of the asserted formula already satisfies `a = b`, so sharing it is
    /// equisatisfiable — never a wrong-UNSAT — and the reasons are real SAT
    /// literals, so EUF's conflict clause stays valid under backtracking. A
    /// COINCIDENTAL model-value match on genuinely-unconstrained `a, b` is NOT
    /// entailed, so nothing is emitted and the formula stays SAT.
    ///
    /// TERMINATION / no fixpoint thrash: we skip any pair EUF already merged
    /// (`are_equal`), so each entailed equality is asserted at most once per EUF
    /// state; after it merges, later rounds emit nothing and the N-O loop
    /// converges.
    ///
    /// CANDIDATES: every Real *leaf* term the LRA relaxation knows (declared
    /// vars, UF applications — NOT compound `+ - * /` sub-expressions). This
    /// mirrors the LIA precedent (`lia/theory_impl.rs` passes all `integer_vars`,
    /// not just interface terms) and is required for TRANSITIVE chains: from
    /// `x=y ∧ y=z ∧ f(x)!=f(z)` the intermediate `y` is not itself a UF argument,
    /// yet `x=y` and `y=z` must both be shared so EUF derives `x=z`. The LRA
    /// helper restricts to pairs COUPLED by a common tableau row, so this is
    /// never an O(n^2) scan over unrelated variables. Gated on an interface
    /// existing (UF and LRA actually share terms) so pure combinations without UF
    /// do no work.
    fn propagate_lra_entailed_interface_equalities(&mut self, debug: bool) -> usize {
        if self.interface.is_none() {
            return 0;
        }
        let terms = self.terms;
        let candidates: Vec<TermId> = match &self.lra {
            Some(lra) => {
                let mut cs: Vec<TermId> = lra
                    .term_to_var()
                    .keys()
                    .copied()
                    .filter(|&t| {
                        *terms.sort(t) == Sort::Real
                            && !matches!(
                                terms.get(t),
                                TermData::App(Symbol::Named(op), args)
                                    if !args.is_empty()
                                        && matches!(op.as_str(), "+" | "-" | "*" | "/")
                            )
                    })
                    .collect();
                cs.sort_unstable(); // Deterministic order (#2681).
                cs
            }
            None => return 0,
        };
        if candidates.len() < 2 {
            return 0;
        }
        let entailed = match &self.lra {
            Some(lra) => lra.find_entailed_difference_equalities(&candidates),
            None => return 0,
        };
        let mut count = 0usize;
        for (lhs, rhs, reasons) in entailed {
            // Defensive: the helper guarantees non-empty reasons; a zero-reason
            // "entailment" would be a model artifact and must never be shared.
            if reasons.is_empty() {
                continue;
            }
            // Natural dedup: if EUF already knows `a = b`, re-asserting only
            // wastes a fixpoint round. (Known-DISEQUAL pairs are intentionally
            // NOT skipped: an entailed equality between EUF-disequal terms is a
            // genuine conflict we want EUF to surface.)
            if self.euf.are_equal(lhs, rhs) {
                continue;
            }
            if debug {
                safe_eprintln!(
                    "[N-O {}] LRA entailed interface equality: {:?} = {:?} ({} reasons)",
                    self.label,
                    lhs,
                    rhs,
                    reasons.len(),
                );
            }
            self.record_cross_theory_equalities(&[DiscoveredEquality::new(
                lhs,
                rhs,
                reasons.clone(),
            )]);
            self.euf.assert_shared_equality(lhs, rhs, &reasons);
            count += 1;
        }
        count
    }

    fn propagate_euf_to_arith(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Result<EufPropResult, TheoryResult> {
        // Drain EUF equalities once and forward to both arithmetic AND arrays.
        // The array solver's `notify_equality` uses these to eagerly queue ROW2
        // axioms before `check()` runs — Z3's merge_eh equivalent (#6546).
        let eq_result =
            drain_equalities_for_propagation(&mut self.euf, debug, self.euf_prop_label, iteration)?;
        let count = eq_result.equalities.len();

        // Nelson-Oppen sharing restriction for the ARITH cross-theory channel
        // (#no-cross-flood). An `Array`-sorted congruence equality is never an
        // arithmetic shared equality — EUF never merges terms of different
        // sorts, so an Array=Array edge sits in a graph component that no
        // Int/Real interface term can reach, and LIA/LRA cannot consume an
        // Array-sorted `assert_shared_equality`. On the QF_ALIA cs_lazy family
        // the 637-atom ITE-definitional array encoding makes EUF discover
        // ~244K Array=Array congruence pairs per N-O round; re-inserting them
        // all into `record_cross_theory_equalities` (per-eq reason sort + BFS
        // over the retained replay graph) is the entire solve budget. Routing
        // ONLY the arith-relevant equalities to the arith channel drops that
        // flood. This is sort-keyed (never interface-membership-keyed), so it
        // has NO Nelson-Oppen "become-shared" completeness gap: a term's sort
        // never changes, so an equality dropped here can never later become an
        // arith shared equality. The array theory still receives EVERY EUF
        // equality below via `notify_arrays_of_euf_equalities` — arrays are the
        // sole consumer of the Array=Array pairs and are NOT restricted.
        let arith_eqs: Vec<DiscoveredEquality> = eq_result
            .equalities
            .iter()
            .filter(|eq| {
                !matches!(self.terms.sort(eq.lhs), Sort::Array(_))
                    && !matches!(self.terms.sort(eq.rhs), Sort::Array(_))
            })
            .cloned()
            .collect();
        self.record_cross_theory_equalities(&arith_eqs);
        // #8165: track EUF propagation count
        if count > 0 {
            theory_stats::inc_props_euf(count as u64);
        }
        if debug && count > 0 {
            safe_eprintln!(
                "[N-O {}] Iteration {}: discovered {} equalities (→arith+arrays)",
                self.euf_prop_label,
                iteration,
                count
            );
        }
        for eq in &eq_result.equalities {
            debug_assert!(
                eq.lhs != eq.rhs,
                "BUG: {} propagated trivial self-equality ({:?} = {:?})",
                self.euf_prop_label,
                eq.lhs,
                eq.rhs
            );
        }
        // Forward to arithmetic solver. Same N-O restriction as above: only
        // arith-relevant (non-Array) equalities are shared with LIA/LRA.
        //
        // INTERFACE-DIET C2: drain diet — the EUF→LIA forward is the channel one
        // N-O round LATER that re-admits withheld pure-UF=UF Int equalities (the
        // channel that defeated the native-DT attempt). Apply the SAME withhold
        // test here, LIA-only; EUF-internal state and LRA forwarding are
        // untouched (M1 is LIA-only; LRA is the separately-pinned M4b lever).
        let diet_withholds = self.interface_diet.withholds();
        for eq in &arith_eqs {
            if let Some(lia) = &mut self.lia {
                if diet_withholds
                    && crate::term_helpers::is_pure_uf_uf_int_equality(self.terms, eq.lhs, eq.rhs)
                {
                    lia.mark_interface_hidden();
                } else {
                    lia.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
                }
            } else if let Some(lra) = &mut self.lra {
                lra.assert_shared_equality(eq.lhs, eq.rhs, &eq.reason);
            }
        }
        let array_notifications = self.notify_arrays_of_euf_equalities(&eq_result.equalities);
        if array_notifications > 0 {
            self.mark_arrays_dirty();
        }

        // #8469: Disequalities are now collected by propagate_equalities()
        // through the unified path. No separate collect_implied_disequalities()
        // call needed — EUF populates the result internally.
        let diseq_count = eq_result.disequalities.len();
        // #8165: track disequality propagations
        if diseq_count > 0 {
            theory_stats::inc_diseq_propagations(diseq_count as u64);
        }
        if debug && diseq_count > 0 {
            safe_eprintln!(
                "[N-O {}] Iteration {}: propagating {} disequalities (->arith)",
                self.euf_prop_label,
                iteration,
                diseq_count
            );
        }
        for diseq in &eq_result.disequalities {
            debug_assert!(
                diseq.lhs != diseq.rhs,
                "BUG: {} propagated trivial self-disequality ({:?} != {:?})",
                self.euf_prop_label,
                diseq.lhs,
                diseq.rhs
            );
        }
        for diseq in eq_result.disequalities {
            if let Some(lia) = &mut self.lia {
                lia.assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
            } else if let Some(lra) = &mut self.lra {
                lra.assert_shared_disequality(diseq.lhs, diseq.rhs, &diseq.reason);
            }
        }

        Ok(EufPropResult {
            eq_count: count,
            diseq_count,
        })
    }

    pub(super) fn array_notify_find(parent: &mut HashMap<TermId, TermId>, term: TermId) -> TermId {
        let current = match parent.get(&term).copied() {
            Some(current) => current,
            None => {
                parent.insert(term, term);
                return term;
            }
        };
        if current == term {
            return term;
        }
        let root = Self::array_notify_find(parent, current);
        parent.insert(term, root);
        root
    }

    fn notify_arrays_of_euf_equalities(&mut self, equalities: &[DiscoveredEquality]) -> usize {
        if self.arrays.is_none() || equalities.is_empty() {
            return 0;
        }

        let mut batch_parent: HashMap<TermId, TermId> = HashMap::default();
        let mut batch_edges: Vec<(TermId, TermId, Vec<TheoryLit>)> = Vec::new();
        let mut notifications = Vec::new();
        for eq in equalities {
            if !matches!(self.terms.sort(eq.lhs), Sort::Array(_))
                || !matches!(self.terms.sort(eq.rhs), Sort::Array(_))
            {
                continue;
            }

            let lhs_root = Self::array_notify_find(&mut self.euf_array_notify_parent, eq.lhs);
            let rhs_root = Self::array_notify_find(&mut self.euf_array_notify_parent, eq.rhs);
            if lhs_root == rhs_root {
                continue;
            }

            let batch_lhs = Self::array_notify_find(&mut batch_parent, lhs_root);
            let batch_rhs = Self::array_notify_find(&mut batch_parent, rhs_root);
            if batch_lhs == batch_rhs {
                continue;
            }
            let (target, source) = if batch_lhs.0 <= batch_rhs.0 {
                (batch_lhs, batch_rhs)
            } else {
                (batch_rhs, batch_lhs)
            };
            batch_parent.insert(source, target);
            let mut reason = eq.reason.clone();
            reason.sort_by_key(|lit| (lit.term.0, lit.value));
            reason.dedup_by_key(|lit| (lit.term, lit.value));
            if reason.is_empty() {
                if let Some(structural_reason) =
                    self.current_structural_congruence_reason(eq.lhs, eq.rhs)
                {
                    reason = structural_reason;
                }
            }
            batch_edges.push((lhs_root, rhs_root, reason));
        }

        let mut component_members: HashMap<TermId, Vec<TermId>> = HashMap::default();
        let batch_nodes: Vec<TermId> = batch_parent.keys().copied().collect();
        for node in batch_nodes {
            let root = Self::array_notify_find(&mut batch_parent, node);
            component_members.entry(root).or_default().push(node);
        }

        // Build a single adjacency map over the batch's spanning-forest edges
        // (#no-cross-flood). `batch_edges` only ever contains edges that JOINED
        // two previously-separate batch components (see the union guard above),
        // so it is a forest: the path between any two nodes of a component is
        // UNIQUE. The former `array_notify_path_reason` re-ran an O(edges) DFS
        // for EVERY (target, source) pair — O(members × edges) per component,
        // which on QF_ALIA cs_lazy (tens of thousands of internal ITE-array
        // congruence nodes per batch) was the entire post-flood solve budget.
        // A single traversal per component computes every member's path-reason
        // in O(edges + members). Empty-reason edges stay non-traversable exactly
        // as before, so an unreachable member yields no replay edge (identical
        // to the old `None` return); the notification itself is unconditional.
        let mut adjacency: HashMap<TermId, Vec<(TermId, &Vec<TheoryLit>)>> = HashMap::default();
        for (lhs, rhs, edge_reason) in &batch_edges {
            if edge_reason.is_empty() {
                continue;
            }
            adjacency.entry(*lhs).or_default().push((*rhs, edge_reason));
            adjacency.entry(*rhs).or_default().push((*lhs, edge_reason));
        }

        for members in component_members.values_mut() {
            if members.len() < 2 {
                continue;
            }
            members.sort_unstable_by_key(|term| term.0);
            let target = members[0];
            // One traversal from `target` accumulating the unique tree-path
            // reason to every reachable node in this component (see the
            // adjacency-forest note above): O(edges + members) versus the former
            // O(members × edges) per-pair DFS.
            let mut path_reason: HashMap<TermId, Vec<TheoryLit>> = HashMap::default();
            path_reason.insert(target, Vec::new());
            let mut stack = vec![target];
            while let Some(node) = stack.pop() {
                let base = path_reason
                    .get(&node)
                    .expect("visited node has a path reason")
                    .clone();
                if let Some(neighbors) = adjacency.get(&node) {
                    for (next, edge_reason) in neighbors {
                        if path_reason.contains_key(next) {
                            continue;
                        }
                        let mut next_reason = base.clone();
                        next_reason.extend(edge_reason.iter().copied());
                        next_reason.sort_by_key(|lit| (lit.term.0, lit.value));
                        next_reason.dedup_by_key(|lit| (lit.term, lit.value));
                        path_reason.insert(*next, next_reason);
                        stack.push(*next);
                    }
                }
            }
            for &source in &members[1..] {
                self.euf_array_notify_parent.insert(source, target);
                if let Some(reason) = path_reason.get(&source) {
                    self.record_euf_array_notify_replay_edge(target, source, reason.clone());
                }
                notifications.push((target, source));
            }
        }

        if let Some(arrays) = &mut self.arrays {
            for &(target, source) in &notifications {
                arrays.notify_equality(target, source);
            }
        }

        notifications.len()
    }

    fn check_arrays_step(&mut self, debug: bool, iteration: usize) -> Result<bool, TheoryResult> {
        if self.array_quiescent_epoch == Some(self.array_epoch) {
            return Ok(false);
        }

        let mut new_eqs = false;
        if let Some(arrays) = &mut self.arrays {
            theory_stats::inc_check_arrays();
            if let Some(result) = forward_non_sat(arrays.check()) {
                return Err(result);
            }
            let arr_eq_count = propagate_equalities_to(
                arrays,
                &mut self.euf,
                debug,
                self.arr_prop_label,
                iteration,
            )?;
            // #no-replay-quadratic: consume the sent-replay DELTA via the
            // discovery-order log cursor instead of cloning the whole
            // reason-carrying set and `Vec::contains`-scanning it per element
            // — that export+scan pair was quadratic in retained replays per
            // Nelson-Oppen iteration (dominant cost on QF_ALIA cs_lazy.i_*
            // after ITE naming, 2026-07-11 sample profile). Replays whose
            // reasons do not hold yet stay in a pending queue re-validated
            // each step — exactly the semantics of the former full rescan.
            let log = arrays.sent_equality_replay_log();
            if self.array_replay_export_cursor > log.len() {
                // The array solver cleared its log (pop); restart.
                self.array_replay_export_cursor = 0;
            }
            for replay in &log[self.array_replay_export_cursor..] {
                if !self.array_equality_replays_seen.contains(replay)
                    && self.array_replay_pending_set.insert(replay.clone())
                {
                    self.array_replay_pending.push(replay.clone());
                }
            }
            self.array_replay_export_cursor = log.len();
            new_eqs = arr_eq_count > 0;
        }
        let pending = std::mem::take(&mut self.array_replay_pending);
        for replay in pending {
            if self.array_equality_replay_is_valid(&replay) {
                self.array_replay_pending_set.remove(&replay);
                if self.array_equality_replays_seen.insert(replay.clone()) {
                    self.array_equality_replays.push(replay);
                }
            } else {
                self.array_replay_pending.push(replay);
            }
        }
        if self.lia.is_none() && self.lra.is_none() {
            let mut arrays_changed = false;
            if let Some(arrays) = &mut self.arrays {
                let euf_to_arr = propagate_equalities_to(
                    &mut self.euf,
                    arrays,
                    debug,
                    self.euf_prop_label,
                    iteration,
                )?;
                arrays_changed = euf_to_arr > 0;
                new_eqs |= euf_to_arr > 0;
            }
            if arrays_changed {
                self.mark_arrays_dirty();
            }
        }
        if new_eqs {
            self.array_quiescent_epoch = None;
        } else {
            self.array_quiescent_epoch = Some(self.array_epoch);
        }
        Ok(new_eqs)
    }

    // --- Bridge and fixpoint helpers ---

    pub(super) fn evaluate_bridge(
        &mut self,
        debug: bool,
    ) -> (Vec<DiscoveredEquality>, Vec<(TermId, TermId)>) {
        let interface = match &mut self.interface {
            Some(i) => i,
            None => return (Vec::new(), Vec::new()),
        };
        if let Some(lia) = &self.lia {
            let euf_int_values = build_euf_int_value_map(&mut self.euf);
            interface.evaluate_and_propagate(
                self.terms,
                &|t| get_value_with_euf_fallback(lia, &euf_int_values, t),
                debug,
                self.label,
            )
        } else if let Some(lra) = &self.lra {
            interface.evaluate_and_propagate_real(
                self.terms,
                &|t| lra_get_real_value_with_reasons(lra, t),
                debug,
                self.label,
            )
        } else {
            (Vec::new(), Vec::new())
        }
    }

    pub(super) fn handle_fixpoint(
        &mut self,
        debug: bool,
        arith_is_unknown: bool,
        deferred_arith_result: Option<TheoryResult>,
        bridge_speculative: &[(TermId, TermId)],
    ) -> Option<TheoryResult> {
        if self.arrays.is_some() {
            match self.propagate_array_indices() {
                Some(TheoryResult::Sat) => {
                    self.mark_arrays_dirty();
                    return None;
                }
                Some(r) => return Some(r),
                None => {}
            }
        }
        if arith_is_unknown {
            if debug {
                safe_eprintln!(
                    "[N-O {}] fixpoint: arith is UNKNOWN — returning Unknown",
                    self.label
                );
            }
            return Some(TheoryResult::Unknown);
        }
        // #uflia-eq-value-mismatch: Nelson-Oppen completeness pass. An asserted
        // Int (dis)equality atom whose two sides BOTH evaluate — with full
        // arithmetic/EUF justification — to values contradicting the asserted
        // polarity is a genuine combined-theory conflict that neither sub-solver
        // sees alone: LIA treats a UF application (or an unregistered mixed
        // compound) as an opaque variable it may value freely, while EUF cannot
        // interpret `+`/`ite`. On the mathsat EufLaArithmetic hard* family the
        // fixpoint otherwise converges to a per-theory-consistent state whose
        // joint valuation violates the final `distinct` (e.g. both sides of an
        // atom asserted FALSE evaluate to 4), and the strict ite_uf_definition
        // gate demotes the accepted model — degrading a provable UNSAT to
        // unknown. SOUNDNESS: fires only when every evaluation leaf is
        // justified (LIA tight-bound reasons or an EUF `explain`ed class
        // constant; `has_unjustified_int_leaf` rejects model artifacts), so the
        // returned conflict literals ENTAIL both values; together with the
        // violated atom they form a genuinely UNSAT set. The same check runs
        // inside the isolated verification combiner, so the conflict is also
        // independently confirmable (#8123 gate).
        if let Some(conflict) = self.check_int_equality_value_mismatches(debug) {
            return Some(conflict);
        }
        let deferred_after_interface = if let Some(result) = deferred_arith_result {
            match result {
                // A concrete disequality split is already the refinement that
                // explores a previously encoded model-equality false branch.
                // Let it through; otherwise stale model equalities can mask the
                // split and the outer loop accepts an invalid model (#7884).
                TheoryResult::NeedDisequalitySplit(_) => return Some(result),
                TheoryResult::NeedExpressionSplit(_)
                | TheoryResult::NeedExpressionSplits(_)
                | TheoryResult::NeedModelEquality(_)
                | TheoryResult::NeedModelEqualities(_) => Some(result),
                other => return Some(other),
            }
        } else {
            None
        };
        // A deferred arithmetic disequality split is often a symptom of the
        // current arithmetic model, not the best next refinement. Give the
        // Nelson-Oppen interface one last chance to request model equalities
        // first; otherwise UFLIA can split on UF-containing arithmetic
        // expressions and degrade to Unknown instead of forcing the EUF
        // equality/disequality conflict (#7884).
        //
        // #6846: discover_model_eq returns non-EUF-equivalent pairs with proven
        // arithmetic reasons. Terms with zero LIA reasons (UF applications with
        // arbitrary model values) are excluded to prevent the split loop from
        // diverging on constantly-shifting value groupings.
        if let Some(model_eq) = self.discover_model_eq(debug) {
            return Some(model_eq);
        }
        // #6846: Bridge speculative pairs are zero-reason equalities from LIA
        // model evaluation of UF applications. These terms have coincidentally
        // matching LIA values but no arithmetic proof of equality. Route them
        // through NeedModelEqualities so the split loop encodes them as SAT
        // decisions with triangle axioms. The split loop's global model-eq
        // iteration counter prevents divergence.
        let mut batch = Vec::new();
        for &(lhs, rhs) in bridge_speculative {
            // #9701: Never propose a speculative model equality for a pair the
            // EUF theory has already pinned DISEQUAL (e.g. an asserted
            // `(not (= (f x) (f y)))`). The equality can never be satisfied, so
            // proposing it is futile AND it masks the deferred disequality /
            // expression split that actually forces the arithmetic theory to
            // separate the two coincident model values. Without this skip,
            // pigeonhole-over-bounded-UF-results formulas accept a wrong-SAT
            // all-equal model (uflia_deep family): the bridge keeps proposing
            // the already-false equality until the split loop's model-eq dedup
            // exhausts, then accepts the invalid model. Letting the pair fall
            // through to `deferred_after_interface` (the expression split)
            // restores soundness.
            if self.euf.are_known_disequal(lhs, rhs) {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] Skipping bridge speculative model equality for known-disequal pair: {:?} != {:?}",
                        self.label,
                        lhs,
                        rhs,
                    );
                }
                continue;
            }
            if !self.euf.are_equal(lhs, rhs) {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] Bridge speculative model equality: {:?} = {:?} (no arithmetic reasons, not EUF-equal)",
                        self.label,
                        lhs,
                        rhs,
                    );
                }
                batch.push(ay_core::ModelEqualityRequest {
                    lhs,
                    rhs,
                    reason: Vec::new(),
                    implied: false,
                });
            }
        }
        match batch.len() {
            0 => {}
            1 => return Some(TheoryResult::NeedModelEquality(batch.pop().unwrap())),
            _ => return Some(TheoryResult::NeedModelEqualities(batch)),
        }
        if let Some(deferred) = deferred_after_interface {
            return Some(deferred);
        }
        // #uflia-cong-repair-arm: LAST gate before accepting Sat on the pure
        // UF+LIA lane — scan the candidate model for UF function-graph
        // violations (two applications of the same symbol whose argument
        // VALUES coincide but whose own values differ) and case-split the
        // first unresolved argument pair. This is exactly the class of model
        // the independent soundness gate would reject post-hoc (observed on
        // the SMT-COMP Hash SAT family: `hash_6(ite(c, x1+x4, x1))` colliding
        // with `hash_6(x3)` through an ite-lifted argument whose value
        // coincidence was never proposed as an interface equality).
        //
        // REACTIVE ARMING: the scan runs ONLY when the Executor has armed it
        // for a re-solve (`arm_uflia_congruence_repair`), i.e. AFTER the
        // independent model gate refuted the first-pass model. The first pass
        // stays on the fast accept and lets the model reach that gate: a
        // latent-consistent collision (the group's app values are invisible
        // and materialize to ONE value per argument tuple) is gate-ACCEPTED
        // and stays SAT with zero wasteful splits (hash_sat_07_03); a real
        // violation is gate-REJECTED (`ModelViolates`), arms this flag, and
        // the armed re-solve's scan drives the arg-split refinement to a
        // correct verdict (the +12 Hash SAT family). An earlier UNCONDITIONAL
        // variant admitted the latent case eagerly and pushed 07_03 past its
        // budget. SOUND either way: the scan only ADDS `implied: false`
        // case-split atoms (never removes a model), and every re-solve is
        // re-validated by the same gate — worst case is a fail-closed Unknown.
        if self.arm_uflia_congruence_repair {
            // #uflia-fd-rescue: on the armed re-solve, FIRST try a finite-domain
            // model of the CURRENT assignment with UF congruence Ackermannized
            // IN (equal argument values => equal application values). This is a
            // whole congruence-consistent candidate model in ONE shot, which
            // sidesteps the split loop's divergence on the Hash SAT family
            // (dense ite-lifted argument collisions the arg-split refinement
            // cannot separate within budget). On success the witness is
            // installed as LIA's `direct_enum_witness`, so the fall-through
            // `Sat` materializes THAT model (via `extract_model`) instead of the
            // class-based arrangement; it is re-validated by the SAME
            // independent gate (worst case a fail-closed `unknown`, exactly as
            // today) and NEVER emits Unsat. Only when no witness is found do we
            // fall back to the split-based congruence repair (the landed +12
            // path), so that path is never weakened.
            let rescued = self
                .lia
                .as_mut()
                .is_some_and(|lia| lia.try_finite_domain_uflia());
            if rescued {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] uflia finite-domain rescue installed a congruence-consistent witness",
                        self.label
                    );
                }
            } else if let Some(repair) = self.discover_congruence_repair_eqs(debug) {
                return Some(repair);
            }
        }
        if let Some(arrays) = &mut self.arrays {
            if let Some(result) = forward_non_sat(arrays.final_check()) {
                return Some(result);
            }
        }
        // Diagnostic-only: --debug-no-terms="242,30,..." dumps the EUF/LIA
        // view of the listed term ids at every Sat-accepting fixpoint.
        if let Some(list) = ay_core::misc_cli_flags().debug_no_terms.as_deref() {
            let ids: Vec<u32> = list
                .split(',')
                .filter_map(|tok| tok.trim().parse::<u32>().ok())
                .collect();
            if let Some(lia) = &self.lia {
                for &raw in &ids {
                    let t = TermId(raw);
                    let lia_val = lia
                        .lra_solver()
                        .get_value_with_reasons(t)
                        .map(|(v, rs)| format!("{} ({} reasons)", v, rs.len()));
                    safe_eprintln!(
                        "[N-O {} fixpoint-sat] T{} lia={:?}",
                        self.label,
                        raw,
                        lia_val,
                    );
                }
            }
            let euf_vals = build_euf_int_value_map(&mut self.euf);
            for &raw in &ids {
                let t = TermId(raw);
                safe_eprintln!(
                    "[N-O {} fixpoint-sat] T{} euf_int={:?}",
                    self.label,
                    raw,
                    euf_vals
                        .get(&t)
                        .map(|(v, rs)| format!("{} ({} reasons)", v, rs.len())),
                );
            }
        }
        // D0 datatype clash/acyclicity pass over the settled e-graph
        // (`DESIGN_lazy_dt.md` stage D0). Runs only when the executor
        // registered datatypes, and only at the point the fixpoint would
        // otherwise accept `Sat`. Conflict-only: a detected clash/cycle is
        // emitted as an entailed datatype tautology clause via `NeedLemmas`
        // (the ROW2 permanent-clause conduit, #6546) after independent
        // fresh-EUF re-derivation inside the pass; an unemittable conflict
        // degrades to a sound `Unknown` (fail-closed) — this hook can never
        // move a verdict toward `Sat`.
        if let Some(dt) = &mut self.dt_pass {
            match dt.check(self.terms, &mut self.euf) {
                ay_dt::DtPassOutcome::Ok => {}
                ay_dt::DtPassOutcome::Lemmas(lemmas) => {
                    if debug {
                        safe_eprintln!(
                            "[N-O {}] DT e-graph pass: emitting {} tautology lemma(s)",
                            self.label,
                            lemmas.len(),
                        );
                    }
                    return Some(TheoryResult::NeedLemmas(lemmas));
                }
                ay_dt::DtPassOutcome::Inconclusive => {
                    if debug {
                        safe_eprintln!(
                            "[N-O {}] DT e-graph pass: unemittable datatype conflict; \
                             degrading Sat to Unknown (fail-closed)",
                            self.label,
                        );
                    }
                    return Some(TheoryResult::Unknown);
                }
            }
        }
        // D1 lazy DT tester/selector propagation at the fixpoint
        // (`DESIGN_lazy_dt.md` stage D1). Forced (no merge gate): the loop is
        // about to accept a candidate model, so any not-yet-emitted entailed
        // tester/selector implication must be materialized NOW — a model
        // violating one is pruned by the injected tautology clause instead of
        // surviving to the (still authoritative) model gates. Dedup inside
        // the propagator bounds re-runs; clauses are permanent.
        if self.dt_d1.is_some() {
            let lemmas = self.dt_d1_lemmas(true);
            if !lemmas.is_empty() {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] DT D1 pass: emitting {} propagation lemma(s) at fixpoint",
                        self.label,
                        lemmas.len(),
                    );
                }
                return Some(TheoryResult::NeedLemmas(lemmas));
            }
        }
        // D2 splitting on demand over finite (all-nullary) datatype sorts
        // (`DESIGN_lazy_dt.md` stage D2; lazy lane only). The loop is about
        // to accept a candidate model: any registered enum split base whose
        // class is still uncommitted and whose domain-closure clause the
        // candidate does not already satisfy gets its exhaustiveness clause
        // now, turning the constructor choice into an ordinary SAT decision.
        // Clauses are unconditional datatype tautologies (validated at
        // registration), so they can only prune models that violate
        // datatype semantics — never manufacture a false-UNSAT; Sat still
        // goes through the always-on model gates.
        if self.dt_d2.is_some() {
            let lemmas = self.dt_d2_lemmas();
            if !lemmas.is_empty() {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] DT D2 pass: emitting {} split clause(s) at fixpoint",
                        self.label,
                        lemmas.len(),
                    );
                }
                return Some(TheoryResult::NeedLemmas(lemmas));
            }
        }
        // INTERFACE-DIET C3 + R1/R3: the arrangement certifier runs immediately
        // before the ONLY terminal `Sat` return of the fixpoint — AFTER every
        // in-invocation mutation (D0 &mut euf, D1/D2, the FD-rescue witness
        // replacement). Because the diet withheld pure-UF=UF Int equalities from
        // LIA, the accepted arrangement was never checked against them; the
        // certifier re-derives the arrangement from the LIVE e-graph + LIVE LIA
        // registry and value-certifies every EUF-equal resident Int pair against
        // RAW LIA values. A verified-consistent arrangement is CERTIFIED Sat; a
        // value mismatch (or a pinned-vs-free asymmetry) is materialized
        // demand-driven and the fixpoint re-runs so LIA builds the conflict with
        // its own sound machinery; an unexplainable / runaway case is Unknown.
        if self.interface_diet.withholds() {
            match self.certify_diet_arrangement(debug) {
                DietCertifyOutcome::Ok => {}
                DietCertifyOutcome::Rerun => return None,
                DietCertifyOutcome::Unknown => return Some(TheoryResult::Unknown),
            }
        }
        self.assert_convergence();
        Some(TheoryResult::Sat)
    }

    /// INTERFACE-DIET arrangement certifier (C3 + R1). See the call site in
    /// [`Self::handle_fixpoint`]. Returns:
    /// * `Ok` — every EUF-equal resident Int pair has matching RAW LIA values
    ///   (or both sides free): the withheld interface hides no conflict, Sat is
    ///   genuinely certified.
    /// * `Rerun` — a mismatch / pinned-vs-free pair was materialized into LIA;
    ///   the caller re-runs the fixpoint (LIA now surfaces the conflict, or
    ///   propagates the value, on its next `check_arith_step`).
    /// * `Unknown` — a witness stands under a hidden interface, an EUF class
    ///   could not be explained, or the per-check materialization budget is
    ///   exhausted (fail-closed; never a wrong verdict).
    fn certify_diet_arrangement(&mut self, debug: bool) -> DietCertifyOutcome {
        // Phase 0 — cheap guards + RAW-value snapshot (immutable LIA borrow,
        // released before any EUF query). Residency from LIA's own integer-var
        // registry; values are LraSolver::get_value (never the EUF fallback).
        let resident_valued: Vec<(TermId, Option<BigInt>)> = {
            let Some(lia) = self.lia.as_ref() else {
                return DietCertifyOutcome::Ok;
            };
            // Nothing withheld this solve ⇒ interface complete ⇒ stock accept
            // path already sound (byte-identical decision).
            if !lia.interface_is_hidden() {
                return DietCertifyOutcome::Ok;
            }
            // Model-identity invariant (R2): a finite-domain / enumeration witness
            // built from the possibly-incomplete shared-eq set cannot stand under
            // a hidden interface.
            if lia.has_direct_enum_witness() {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] diet-certify: direct_enum_witness under hidden interface ⇒ Unknown",
                        self.label
                    );
                }
                return DietCertifyOutcome::Unknown;
            }
            lia.integer_var_terms()
                .into_iter()
                .map(|t| (t, lia.raw_lia_value(t)))
                .collect()
        };
        // Runaway guard (fail-closed): bound the certify↔materialize ping-pong.
        const MAX_DIET_CERTIFY_ROUNDS: u32 = 256;
        if self.diet_certify_rounds >= MAX_DIET_CERTIFY_ROUNDS {
            if debug {
                safe_eprintln!(
                    "[N-O {}] diet-certify: materialization budget exhausted ⇒ Unknown",
                    self.label
                );
            }
            return DietCertifyOutcome::Unknown;
        }

        // Phase 1 — value-certify EUF-equal resident pairs. Greedy class grouping
        // over the public `are_equal` (≤|R|² find-queries, the M3-sanctioned
        // bound); most classes are singletons so the practical cost is near-linear.
        let mut reps: Vec<(TermId, Option<BigInt>)> = Vec::new();
        let mut to_materialize: Vec<(TermId, TermId)> = Vec::new();
        for (t, vt) in &resident_valued {
            let mut matched = false;
            for (rep, vrep) in &reps {
                if self.euf.are_equal(*rep, *t) {
                    matched = true;
                    match (vrep, vt) {
                        // Both pinned and DISAGREE: a real combined conflict the
                        // withheld equality hid — materialize so LIA refutes it.
                        (Some(x), Some(y)) if x != y => to_materialize.push((*rep, *t)),
                        // Pinned vs free (missing column): materialize to
                        // propagate the pinned value into the free side (R1).
                        (Some(_), None) | (None, Some(_)) => to_materialize.push((*rep, *t)),
                        // Both free, or pinned+equal: no hidden violation.
                        _ => {}
                    }
                    break;
                }
            }
            if !matched {
                reps.push((*t, vt.clone()));
            }
        }

        if to_materialize.is_empty() {
            if debug || ay_core::misc_cli_flags().phase_trace {
                safe_eprintln!(
                    "c phase-trace diet-certify CERTIFIED-SAT resident={} euf_classes={} label={}",
                    resident_valued.len(),
                    reps.len(),
                    self.label,
                );
            }
            return DietCertifyOutcome::Ok;
        }

        // Materialize each mismatching / missing-column pair with the EUF proof
        // of its equality. An unexplainable pair (should not happen for an
        // are_equal pair) fails closed to Unknown rather than assert a
        // reason-less shared equality.
        self.diet_certify_rounds += 1;
        let mut materialized = 0usize;
        for (a, b) in to_materialize {
            let reason = self.euf.explain(a, b);
            if reason.is_empty() {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] diet-certify: unexplainable EUF-equal pair {:?}={:?} ⇒ Unknown",
                        self.label,
                        a,
                        b
                    );
                }
                return DietCertifyOutcome::Unknown;
            }
            if let Some(lia) = self.lia.as_mut() {
                lia.assert_shared_equality(a, b, &reason);
                materialized += 1;
            }
        }
        if debug || ay_core::misc_cli_flags().phase_trace {
            safe_eprintln!(
                "c phase-trace diet-certify MATERIALIZED n={} round={} label={}",
                materialized,
                self.diet_certify_rounds,
                self.label,
            );
        }
        DietCertifyOutcome::Rerun
    }

    /// #uflia-cong-repair: accept-point UF function-graph consistency scan.
    ///
    /// Groups every Int-sorted uninterpreted application with Int-sorted
    /// arguments by `(symbol, argument model values)`. Two members of a group
    /// that are NOT in the same EUF class are a (possibly latent) function-
    /// graph violation: model materialization assigns one value per argument
    /// tuple, so if their classes materialize to different values the model
    /// falsifies functionality and the independent model gate demotes it to
    /// `unknown`. A pair is skipped only when BOTH application values are
    /// already visible to LIA/EUF and coincide (then materialization is
    /// consistent for that point). Crucially, an application whose own value
    /// is invisible at accept time (e.g. `hash_6(ite(c, x1+x4, x1))` — the
    /// app is registered nowhere in LIA and its EUF class carries no int
    /// constant) still participates: the observed Hash-family gate rejections
    /// come exactly from such ite-lifted arguments whose value coincidence
    /// was never proposed as an interface equality. For each violating pair,
    /// propose a `ModelEqualityRequest` on the first argument position whose
    /// terms are neither EUF-equal nor EUF-disequal (deciding it TRUE merges
    /// the applications by congruence; deciding it FALSE forces LIA to
    /// separate the argument values, dissolving the group). When every
    /// argument pair is already pinned, fall back to proposing the
    /// application pair itself.
    ///
    /// SOUNDNESS: requests are `implied: false` with empty reasons — pure SAT
    /// case-splits that can only add decisions, never remove a model. An
    /// unproposable violation (all pairs pinned) falls through to Sat and the
    /// independent gate still fail-closes, exactly as before this scan.
    ///
    /// Scoped to the UFLIA lane: array-carrying combiners own their index
    /// coincidences via the array rescue machinery (#6367/#7956), and the
    /// LRA lanes have no observed instances of this failure class.
    fn discover_congruence_repair_eqs(&mut self, debug: bool) -> Option<TheoryResult> {
        if self.label != "UFLIA" {
            return None;
        }
        let lia = self.lia.as_ref()?;
        // Cap the per-round batch: each pair is one SAT-visible atom; a giant
        // batch on a dense-collision model floods the split loop's round
        // budget. 16 keeps convergence brisk (one round usually repairs the
        // whole graph because a single argument split separates many groups).
        const MAX_REPAIR_PAIRS: usize = 16;
        let euf_int_values = build_euf_int_value_map(&mut self.euf);
        let terms = self.terms;
        let eval = |t: TermId| -> Option<BigInt> {
            let mut reasons = Vec::new();
            evaluate_arith_term_with_reasons(
                terms,
                &|var| get_value_with_euf_fallback(lia, &euf_int_values, var),
                t,
                &mut reasons,
            )
        };
        // Phase 1: group applications by (symbol, argument values). TermId
        // order makes group membership order deterministic (DetHashMap).
        // The application's own value is `None` when neither LIA nor the EUF
        // int-value fallback can see it yet — such members still group (their
        // materialized value is unconstrained, so a collision is possible).
        type GroupKey = (String, Vec<BigInt>);
        let mut groups: HashMap<GroupKey, Vec<(TermId, Option<BigInt>)>> = HashMap::default();
        for raw in 0..u32::try_from(terms.len()).unwrap_or(u32::MAX) {
            let tid = TermId(raw);
            let TermData::App(Symbol::Named(name), args) = terms.get(tid) else {
                continue;
            };
            if args.is_empty() {
                continue;
            }
            // Interpreted arithmetic/logical operators evaluate as functions
            // of their arguments inside `evaluate_arith_term_with_reasons`,
            // so they can never exhibit a graph violation; skip them. Opaque
            // ops the evaluator does not interpret behave exactly like UF
            // applications here and are deliberately kept.
            let n = name.as_str();
            if matches!(
                n,
                "+" | "-"
                    | "*"
                    | "="
                    | "<="
                    | "<"
                    | ">"
                    | ">="
                    | "distinct"
                    | "and"
                    | "or"
                    | "not"
                    | "=>"
                    | "ite"
                    | "select"
                    | "store"
            ) {
                continue;
            }
            if !matches!(terms.sort(tid), Sort::Int) {
                continue;
            }
            if !args.iter().all(|&a| matches!(terms.sort(a), Sort::Int)) {
                continue;
            }
            let app_val = eval(tid);
            let mut arg_vals = Vec::with_capacity(args.len());
            let mut all_known = true;
            for &a in args {
                match eval(a) {
                    Some(v) => arg_vals.push(v),
                    None => {
                        all_known = false;
                        break;
                    }
                }
            }
            if !all_known {
                continue;
            }
            groups
                .entry((name.to_string(), arg_vals))
                .or_default()
                .push((tid, app_val));
        }
        // Phase 2: emit repair requests for violating pairs.
        let mut batch: Vec<ay_core::ModelEqualityRequest> = Vec::new();
        let mut proposed_pairs: std::collections::BTreeSet<(TermId, TermId)> =
            std::collections::BTreeSet::new();
        let propose = |batch: &mut Vec<ay_core::ModelEqualityRequest>,
                       proposed: &mut std::collections::BTreeSet<(TermId, TermId)>,
                       lhs: TermId,
                       rhs: TermId|
         -> bool {
            let key = if lhs.0 <= rhs.0 {
                (lhs, rhs)
            } else {
                (rhs, lhs)
            };
            if !proposed.insert(key) {
                return false;
            }
            batch.push(ay_core::ModelEqualityRequest {
                lhs,
                rhs,
                reason: Vec::new(),
                implied: false,
            });
            true
        };
        'groups: for ((name, _), apps) in &groups {
            if apps.len() < 2 {
                continue;
            }
            for i in 0..apps.len() {
                for j in (i + 1)..apps.len() {
                    let (a_app, a_val) = &apps[i];
                    let (b_app, b_val) = &apps[j];
                    if let (Some(av), Some(bv)) = (a_val, b_val) {
                        // Both values visible and coincident: materialization
                        // is consistent at this argument point regardless of
                        // EUF class structure. Only a visible DIVERGENCE (or
                        // an invisible value, which materializes arbitrarily)
                        // can break functionality.
                        if av == bv {
                            continue;
                        }
                    }
                    if self.euf.are_equal(*a_app, *b_app) {
                        // EUF already merged them; the value divergence is a
                        // LIA-model artifact that class-based materialization
                        // resolves (one value per class).
                        continue;
                    }
                    let (TermData::App(_, a_args), TermData::App(_, b_args)) =
                        (terms.get(*a_app), terms.get(*b_app))
                    else {
                        continue;
                    };
                    let mut proposed_any = false;
                    for (&ai, &bi) in a_args.iter().zip(b_args.iter()) {
                        if ai == bi || self.euf.are_equal(ai, bi) {
                            continue;
                        }
                        if self.euf.are_known_disequal(ai, bi) {
                            continue;
                        }
                        if propose(&mut batch, &mut proposed_pairs, ai, bi) {
                            if debug {
                                safe_eprintln!(
                                    "[N-O {}] Congruence repair ({}): arg split {:?} = {:?} (apps {:?}/{:?} values {:?} vs {:?})",
                                    self.label, name, ai, bi, a_app, b_app, a_val, b_val,
                                );
                            }
                            proposed_any = true;
                        }
                        break;
                    }
                    if !proposed_any
                        && !self.euf.are_known_disequal(*a_app, *b_app)
                        && propose(&mut batch, &mut proposed_pairs, *a_app, *b_app)
                        && debug
                    {
                        safe_eprintln!(
                            "[N-O {}] Congruence repair ({}): app split {:?} = {:?} (values {:?} vs {:?})",
                            self.label, name, a_app, b_app, a_val, b_val,
                        );
                    }
                    if batch.len() >= MAX_REPAIR_PAIRS {
                        break 'groups;
                    }
                }
            }
        }
        match batch.len() {
            0 => None,
            1 => Some(TheoryResult::NeedModelEquality(
                batch.pop().expect("len checked"),
            )),
            _ => Some(TheoryResult::NeedModelEqualities(batch)),
        }
    }

    fn propagate_array_indices(&mut self) -> Option<TheoryResult> {
        // #read-congruence-quantified-scope: threaded from the executor via
        // `set_read_congruence_pairs_enabled` (default `true`).
        let act_on_read_congruence_pairs = self.read_congruence_pairs_enabled;
        let arrays = self.arrays.as_mut()?;
        let terms = self.terms;
        if let Some(lia) = &self.lia {
            propagate_array_index_info(
                terms,
                arrays,
                &mut self.euf,
                |t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_arith_term_with_reasons(
                        terms,
                        &|var| lia_get_int_value_with_reasons(lia, var),
                        t,
                        &mut reasons,
                    )?;
                    Some((value, reasons))
                },
                act_on_read_congruence_pairs,
            )
        } else if let Some(lra) = &self.lra {
            propagate_array_index_info(
                terms,
                arrays,
                &mut self.euf,
                |t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_real_arith_term_with_reasons(
                        terms,
                        &|var| lra_get_real_value_with_reasons(lra, var),
                        t,
                        &mut reasons,
                    )?;
                    Some((value, reasons))
                },
                act_on_read_congruence_pairs,
            )
        } else {
            None
        }
    }

    /// #uflia-eq-value-mismatch: scan asserted Int (dis)equality atoms for a
    /// justified joint-valuation violation (see the call site in
    /// [`Self::handle_fixpoint`] for the full rationale). Returns
    /// `Some(TheoryResult::Unsat(..))` with a fully-asserted reason set on the
    /// first violation found, `None` otherwise.
    fn check_int_equality_value_mismatches(&mut self, debug: bool) -> Option<TheoryResult> {
        use crate::term_helpers::decode_non_bool_eq;
        self.lia.as_ref()?;
        let terms = self.terms;
        let euf_int_values = build_euf_int_value_map(&mut self.euf);
        let lia = self.lia.as_ref()?;
        // Shared-term value clash: a term with a JUSTIFIED (tight-bound) LIA
        // value AND a justified EUF class-constant value that DIFFER is a
        // direct cross-theory conflict — the reason union is unsat. Observed
        // on EufLaArithmetic hard*: LIA holds `x = 3` (tight) while EUF holds
        // `x ~ 1` (asserted equality atom the arithmetic side never
        // materialized), and the N-O fixpoint otherwise converges around the
        // contradiction. Each side's reasons entail ITS value, so together
        // they are UNSAT; empty EUF reasons mean a level-0 (unit-entailed)
        // merge and the LIA reasons alone are already inconsistent with the
        // problem. LIA-side empty reasons are skipped (#6930: a bare simplex
        // model value is a free choice, not an entailment).
        let mut euf_valued: Vec<(&TermId, &(BigInt, Vec<TheoryLit>))> =
            euf_int_values.iter().collect();
        euf_valued.sort_unstable_by_key(|(t, _)| **t);
        for (&t, (euf_val, euf_reasons)) in euf_valued {
            let Some((lia_val, lia_reasons)) = lia_get_int_value_with_reasons(lia, t) else {
                continue;
            };
            if lia_reasons.is_empty() || &lia_val == euf_val {
                continue;
            }
            let mut conflict = lia_reasons;
            conflict.extend(euf_reasons.iter().copied());
            conflict.sort_by_key(|r| r.term);
            conflict.dedup_by_key(|r| r.term);
            if debug {
                safe_eprintln!(
                    "[N-O {}] shared-term value clash: {:?} lia={} euf={} ({} reason lits)",
                    self.label,
                    t,
                    lia_val,
                    euf_val,
                    conflict.len(),
                );
            }
            return Some(TheoryResult::Unsat(conflict));
        }
        let get = |t: TermId| get_value_with_euf_fallback(lia, &euf_int_values, t);
        // Diagnostic-only: --debug-no-terms="4,30,..." dumps the LIA/EUF view
        // of the listed term ids at every fixpoint mismatch scan.
        if let Some(list) = ay_core::misc_cli_flags().debug_no_terms.as_deref() {
            for raw in list.split(',') {
                let Ok(id) = raw.trim().parse::<u32>() else {
                    continue;
                };
                let t = TermId(id);
                safe_eprintln!(
                    "[N-O {} scan] T{} lia={:?} euf={:?}",
                    self.label,
                    id,
                    lia_get_int_value_with_reasons(lia, t)
                        .map(|(v, r)| format!("{v} ({} r)", r.len())),
                    euf_int_values
                        .get(&t)
                        .map(|(v, r)| format!("{v} ({} r)", r.len())),
                );
            }
        }
        // Deterministic iteration order (#3041).
        let mut assignments: Vec<(TermId, bool)> = self
            .current_assignments
            .iter()
            .map(|(&t, &v)| (t, v))
            .collect();
        assignments.sort_unstable_by_key(|&(t, _)| t);
        // Per-scan memo: equality operands repeat across many atoms (a UF
        // application is compared against every branch variant), so cache
        // each side's evaluation for the duration of the scan.
        let mut eval_memo: HashMap<TermId, Option<(BigInt, Vec<TheoryLit>)>> = HashMap::default();
        let mut eval_side = |side: TermId| -> Option<(BigInt, Vec<TheoryLit>)> {
            eval_memo
                .entry(side)
                .or_insert_with(|| {
                    let mut side_reasons = Vec::new();
                    evaluate_arith_term_with_reasons(terms, &get, side, &mut side_reasons)
                        .map(|v| (v, side_reasons))
                })
                .clone()
        };
        for (atom, value) in assignments {
            let Some((lhs, rhs)) = decode_non_bool_eq(terms, atom) else {
                continue;
            };
            if !matches!(terms.sort(lhs), Sort::Int) || !matches!(terms.sort(rhs), Sort::Int) {
                continue;
            }
            let mut reasons = Vec::new();
            let lhs_eval = eval_side(lhs).map(|(v, r)| {
                reasons.extend(r);
                v
            });
            let rhs_eval = eval_side(rhs).map(|(v, r)| {
                reasons.extend(r);
                v
            });
            if debug && !value {
                safe_eprintln!(
                    "[N-O {}] eq-value scan: atom {:?}=false lhs {:?}={:?} rhs {:?}={:?}",
                    self.label,
                    atom,
                    lhs,
                    lhs_eval,
                    rhs,
                    rhs_eval,
                );
            }
            let (Some(lhs_val), Some(rhs_val)) = (lhs_eval, rhs_eval) else {
                continue;
            };
            if (lhs_val == rhs_val) == value {
                continue;
            }
            // Model-artifact guard (#8147): only justified values entail the
            // violation. A leaf valued without reasons (a free simplex choice)
            // makes the mismatch circumstantial, not a theory conflict.
            if has_unjustified_int_leaf(terms, &get, lhs)
                || has_unjustified_int_leaf(terms, &get, rhs)
            {
                if debug {
                    safe_eprintln!(
                        "[N-O {}] eq-value mismatch on {:?} SKIPPED: unjustified leaf",
                        self.label,
                        atom,
                    );
                }
                continue;
            }
            reasons.push(TheoryLit::new(atom, value));
            reasons.sort_by_key(|r| r.term);
            reasons.dedup_by_key(|r| r.term);
            if debug {
                safe_eprintln!(
                    "[N-O {}] eq-value mismatch: atom {:?}={} but lhs {:?}={} rhs {:?}={} ({} reason lits)",
                    self.label,
                    atom,
                    value,
                    lhs,
                    lhs_val,
                    rhs,
                    rhs_val,
                    reasons.len(),
                );
            }
            return Some(TheoryResult::Unsat(reasons));
        }
        None
    }

    fn discover_model_eq(&mut self, debug: bool) -> Option<TheoryResult> {
        let sorted_terms = self.interface.as_ref()?.sorted_arith_terms();
        if let Some(lia) = &self.lia {
            // #6846: Evaluation-based model equality discovery.
            // Groups Int-sorted interface terms by model value, batches all
            // non-EUF-equal pairs.
            //
            // EUF-fallback (#take_first_mut / N-O completeness): use the SAME
            // value closure as the bridge path (mod.rs:761-764) — when LIA has
            // no tight bound for a term, fall back to its EUF-class Int value.
            // This lets two interface seq-element selects forced equal by EUF
            // array-select congruence (whose shared value is an EUF union-find
            // value with no LIA reasons) be grouped into a model equality.
            // SOUNDNESS: the request stays `implied:false` with empty `reason`
            // (a SAT case-split, not a theory lemma — euf.explain reasons are
            // used only as the group key and discarded), so a wrong grouping
            // can only waste a decision, never remove a model. The empty-reasons
            // drop is KEPT so a bare LIA trivial-model value (no justification)
            // still never groups; only EUF- or LIA-justified values are admitted.
            // (An A/B that admitted unjustified values here flooded the accept
            // path with value-group case-splits and pushed previously-solving
            // Hash greens past the 20s budget; the targeted accept-point scan
            // in `discover_congruence_repair_eqs` replaced it. #uflia-cong-repair)
            let euf_int_values = build_euf_int_value_map(&mut self.euf);
            discover_model_equality(
                sorted_terms.into_iter(),
                self.terms,
                &self.euf,
                &|t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_arith_term_with_reasons(
                        self.terms,
                        &|var| get_value_with_euf_fallback(lia, &euf_int_values, var),
                        t,
                        &mut reasons,
                    )?;
                    if reasons.is_empty() {
                        None
                    } else {
                        Some(value)
                    }
                },
                &[Sort::Int],
                debug,
                self.label,
            )
        } else if let Some(lra) = &self.lra {
            // #7462: Use evaluate_real_arith_term_with_reasons (recursive
            // expression evaluation) instead of direct variable lookup.
            // Without recursive evaluation, compound UF arguments like
            // (+ x 0.5) cannot be evaluated, so two UF args that simplify
            // to the same value are never grouped together.
            let terms = self.terms;
            discover_model_equality(
                sorted_terms.into_iter(),
                self.terms,
                &self.euf,
                &|t| {
                    let mut reasons = Vec::new();
                    let value = evaluate_real_arith_term_with_reasons(
                        terms,
                        &|var| lra_get_real_value_with_reasons(lra, var),
                        t,
                        &mut reasons,
                    )?;
                    if reasons.is_empty() {
                        None
                    } else {
                        Some(value)
                    }
                },
                &[Sort::Real],
                debug,
                self.label,
            )
        } else {
            None
        }
    }

    /// #8596: When arithmetic finds UNSAT and we have arrays, give the array
    /// theory a chance to contribute before accepting the conflict.
    ///
    /// The arithmetic conflict may be conditional on array index disequalities
    /// that haven't been case-split yet. For example, with:
    ///   a = store(const(0), x, 1) AND select(a, y) = 1
    /// the LIA relaxation finds UNSAT when x != y (select value would be 0),
    /// but the formula is SAT when x = y. The array solver can discover this
    /// via model equalities.
    ///
    /// Returns `Some(result)` if arrays produced a non-conflict result (lemmas
    /// or model equalities) that should be returned instead of the arithmetic
    /// conflict. Returns `None` if the arithmetic conflict should be accepted.
    fn try_array_rescue_on_arith_conflict(
        &mut self,
        debug: bool,
        iteration: usize,
    ) -> Option<TheoryResult> {
        // #6367: Check presence without holding a mutable borrow of self.arrays
        // so that self.gate_rescue_on_counter / self.euf / self.propagate_...
        // can re-borrow self in the NeedModelEquality branches below.
        self.arrays.as_ref()?;

        // Run array check to process pending axioms.
        theory_stats::inc_check_arrays();
        let arr_result = self
            .arrays
            .as_mut()
            .expect("arrays presence checked above")
            .check();
        match arr_result {
            TheoryResult::Sat => {}
            TheoryResult::NeedLemmas(_) => {
                // Arrays have pending work — return this instead of the
                // arithmetic conflict. The lemmas will add new constraints
                // that may resolve the conflict.
                return Some(arr_result);
            }
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
                // #6367: Gate model-equality rescues on the pipeline-owned
                // per-pair counter. When the same pair has been rescued more
                // than the budget, drop it so the arithmetic UnsatWithFarkas
                // stands instead of looping.
                if let Some(gated) = self.gate_rescue_on_counter(arr_result, debug) {
                    return Some(gated);
                }
                // else: all pairs exhausted — fall through to let the
                // arithmetic conflict stand.
            }
            // Array conflict or other result — don't rescue, let the
            // arithmetic conflict stand.
            _ => {}
        }

        // Propagate array equalities to EUF. Scoped so the &mut borrow
        // on self.arrays drops before subsequent self method calls.
        {
            let arrays = self.arrays.as_mut().expect("arrays presence checked above");
            if let Ok(arr_eq_count) = propagate_equalities_to(
                arrays,
                &mut self.euf,
                debug,
                self.arr_prop_label,
                iteration,
            ) {
                if arr_eq_count > 0 {
                    // New equalities discovered — the arithmetic conflict may
                    // be resolvable. Return None to let the conflict stand but
                    // the caller could re-check. Actually, the new equalities
                    // won't help in this iteration since arith already returned
                    // UNSAT. The key is the final_check below.
                }
            }
        }

        // Try array final_check — this is where model equalities and
        // extensionality lemmas are generated.
        let arrays = self.arrays.as_mut()?;
        let fc_result = arrays.final_check();
        match fc_result {
            TheoryResult::Sat => {}
            TheoryResult::NeedLemmas(_) => {
                // Array final_check produced lemmas. Return instead of the
                // arithmetic conflict.
                if debug {
                    safe_eprintln!(
                        "[N-O {}] Array final_check rescued arithmetic conflict with {:?}",
                        self.label,
                        std::mem::discriminant(&fc_result),
                    );
                }
                return Some(fc_result);
            }
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
                // Array final_check produced model equalities. Apply the
                // same per-pair rescue budget (#6367).
                if let Some(gated) = self.gate_rescue_on_counter(fc_result, debug) {
                    if debug {
                        safe_eprintln!(
                            "[N-O {}] Array final_check rescued arithmetic conflict \
                             with model-eq (after budget gate)",
                            self.label,
                        );
                    }
                    return Some(gated);
                }
                // else: all pairs exhausted — fall through.
            }
            _ => {}
        }

        // Try propagate_array_indices — this discovers index equalities
        // from the arithmetic model.
        match self.propagate_array_indices() {
            Some(TheoryResult::Sat) => {
                // New index info propagated — mark arrays dirty and
                // let the conflict stand (it will be retried).
                self.mark_arrays_dirty();
            }
            Some(result) => {
                // #6367: Apply the same per-pair budget if this is a
                // model-equality. Lemmas and other results pass through.
                match result {
                    TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
                        if let Some(gated) = self.gate_rescue_on_counter(result, debug) {
                            return Some(gated);
                        }
                        // else: all pairs exhausted — fall through.
                    }
                    other => return Some(other),
                }
            }
            None => {}
        }

        // No rescue available — the arithmetic conflict stands.
        None
    }

    /// Gate a model-equality rescue on the pipeline-owned per-pair counter (#6367).
    ///
    /// For `NeedModelEquality`: if the single pair has exhausted its budget,
    /// returns `None` so the caller falls back to the arithmetic conflict.
    ///
    /// For `NeedModelEqualities`: filters out every pair that has exhausted
    /// its budget. When the batch becomes empty, returns `None`. When only
    /// one pair survives, returns it as `NeedModelEquality` (matching the
    /// canonical batch-to-single reduction used elsewhere in this module).
    ///
    /// When no counter is wired (legacy callers), all rescues are allowed.
    /// Non-model-equality inputs are returned unchanged.
    fn gate_rescue_on_counter(
        &mut self,
        result: TheoryResult,
        debug: bool,
    ) -> Option<TheoryResult> {
        let Some(counter_arc) = self.rescue_pair_counter.as_ref() else {
            // No counter configured — preserve legacy unbudgeted behaviour.
            return Some(result);
        };
        let counter_arc = counter_arc.clone();
        let budget = crate::executor::DEFAULT_RESCUE_PAIR_BUDGET;

        match result {
            TheoryResult::NeedModelEquality(req) => {
                let exhausted = {
                    let mut guard = match counter_arc.lock() {
                        Ok(g) => g,
                        Err(poisoned) => poisoned.into_inner(),
                    };
                    guard.record_and_check_exhausted(req.lhs, req.rhs, budget)
                };
                if exhausted {
                    if debug {
                        safe_eprintln!(
                            "[N-O {}] rescue pair budget exhausted for ({:?},{:?}); \
                             dropping rescue and accepting arith conflict",
                            self.label,
                            req.lhs,
                            req.rhs,
                        );
                    }
                    None
                } else {
                    Some(TheoryResult::NeedModelEquality(req))
                }
            }
            TheoryResult::NeedModelEqualities(batch) => {
                let mut retained: Vec<_> = Vec::with_capacity(batch.len());
                let mut dropped = 0usize;
                {
                    let mut guard = match counter_arc.lock() {
                        Ok(g) => g,
                        Err(poisoned) => poisoned.into_inner(),
                    };
                    for req in batch {
                        if guard.record_and_check_exhausted(req.lhs, req.rhs, budget) {
                            dropped += 1;
                        } else {
                            retained.push(req);
                        }
                    }
                }
                if debug && dropped > 0 {
                    safe_eprintln!(
                        "[N-O {}] rescue pair budget dropped {} / {} model eqs",
                        self.label,
                        dropped,
                        dropped + retained.len(),
                    );
                }
                match retained.len() {
                    0 => None,
                    1 => Some(TheoryResult::NeedModelEquality(retained.pop().unwrap())),
                    _ => Some(TheoryResult::NeedModelEqualities(retained)),
                }
            }
            other => Some(other),
        }
    }

    fn assert_convergence(&mut self) {
        let mut solvers: Vec<&mut dyn TheorySolver> = Vec::new();
        if let Some(lia) = &mut self.lia {
            solvers.push(lia);
        }
        if let Some(lra) = &mut self.lra {
            solvers.push(lra);
        }
        solvers.push(&mut self.euf);
        if let Some(arrays) = &mut self.arrays {
            solvers.push(arrays);
        }
        assert_fixpoint_convergence(self.label, &mut solvers);
    }
}

/// Build EUF int-value lookup with pre-computed explain reasons (#5081).
pub(super) fn build_euf_int_value_map(
    euf: &mut EufSolver<'_>,
) -> HashMap<TermId, (BigInt, Vec<TheoryLit>)> {
    let raw_map = euf.build_int_value_map();
    let mut explained: HashMap<TermId, (BigInt, Vec<TheoryLit>)> = Default::default();
    for (tid, (val, const_tid)) in raw_map {
        let reasons = euf.explain(tid, const_tid);
        explained.insert(tid, (val, reasons));
    }
    explained
}

/// Get integer value for a term, trying LIA first then EUF fallback (#5081).
///
/// CRITICAL: When falling back to EUF reasons, we MUST use EUF's value too.
/// LIA's model value and EUF's reasons may be inconsistent — LIA can assign
/// `v = 0` (trivial model) while EUF's equality chain justifies `v = 42`.
/// Mixing LIA's value with EUF's reasons produces an unsound (value, reasons)
/// pair that causes false-UNSAT (#6930).
pub(super) fn get_value_with_euf_fallback(
    lia: &LiaSolver<'_>,
    euf_int_values: &HashMap<TermId, (BigInt, Vec<TheoryLit>)>,
    t: TermId,
) -> Option<(BigInt, Vec<TheoryLit>)> {
    if let Some((val, lia_reasons)) = lia_get_int_value_with_reasons(lia, t) {
        if !lia_reasons.is_empty() {
            // TL27 #8742 trace: dump full reason set to spot unsound bridge
            // propagations where reasons don't actually justify the value.
            if ay_core::debug_channel_active(ay_core::DebugChannel::EufFallback) {
                if let Some((euf_val, euf_reasons)) = euf_int_values.get(&t) {
                    if &val != euf_val {
                        eprintln!(
                            "[EUF_FALLBACK] MISMATCH t={t:?} lia_val={val} lia_reasons={lia_reasons:?} euf_val={euf_val} euf_reasons={euf_reasons:?}"
                        );
                    } else {
                        eprintln!(
                            "[EUF_FALLBACK] match t={t:?} val={val} lia_reasons={lia_reasons:?} euf_reasons={euf_reasons:?}"
                        );
                    }
                } else {
                    eprintln!(
                        "[EUF_FALLBACK] lia-only t={t:?} val={val} lia_reasons={lia_reasons:?}"
                    );
                }
            }
            return Some((val, lia_reasons));
        }
        // LIA returned a value with no reasons (unconstrained variable).
        // If EUF has a justified value for this term, prefer EUF's (value, reasons)
        // pair — they are guaranteed consistent since EUF's value comes from its
        // own equivalence class and the reasons justify that specific value.
        if let Some((euf_val, euf_reasons)) = euf_int_values.get(&t) {
            if !euf_reasons.is_empty() {
                return Some((euf_val.clone(), euf_reasons.clone()));
            }
        }
        return Some((val, lia_reasons));
    }
    euf_int_values
        .get(&t)
        .map(|(val, reasons)| (val.clone(), reasons.clone()))
}

/// #7956: Recursively check if a term mentions an array-theory constructor
/// (`select` or `store`) or an Array-sorted subterm.
///
/// Used by `conflict_involves_array_theory` to decide whether an
/// arithmetic UNSAT conflict is plausibly rescuable by the array theory.
/// A conflict whose reasons are purely arithmetic/equality atoms with
/// no connection to arrays cannot be resolved by array-theory model
/// equalities — forwarding it to SAT is the correct behaviour.
fn term_mentions_array(terms: &TermStore, term: TermId) -> bool {
    // Unwrap top-level negation.
    let inner = match terms.get(term) {
        TermData::Not(inner) => *inner,
        _ => term,
    };
    if matches!(terms.sort(inner), Sort::Array(_)) {
        return true;
    }
    mentions_array_rec(terms, inner)
}

fn mentions_array_rec(terms: &TermStore, term: TermId) -> bool {
    if matches!(terms.sort(term), Sort::Array(_)) {
        return true;
    }
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "select" | "store" => true,
            _ => args.iter().any(|&arg| mentions_array_rec(terms, arg)),
        },
        TermData::Not(inner) => mentions_array_rec(terms, *inner),
        TermData::Ite(c, t, e) => {
            mentions_array_rec(terms, *c)
                || mentions_array_rec(terms, *t)
                || mentions_array_rec(terms, *e)
        }
        TermData::App(_, args) => args.iter().any(|&arg| mentions_array_rec(terms, arg)),
        _ => false,
    }
}

/// #7956: Determine whether an arithmetic conflict's reason literals touch
/// any array-theory constructor.
///
/// The AUFLIA rescue path (`try_array_rescue_on_arith_conflict`) exists so
/// that LIA UNSAT conflicts conditional on array index (dis)equalities can
/// be resolved by a speculative `NeedModelEquality`. For the rescue to be
/// logically relevant, at least one conflict reason must involve arrays.
///
/// If no reason mentions `select`/`store` or an Array-sorted subterm, the
/// conflict is purely arithmetic/equality and array model equalities cannot
/// invalidate it. In that case the conflict must be forwarded back to SAT
/// so SAT can flip a decision (or, at level 0, conclude UNSAT globally).
///
/// Swallowing such a conflict causes false-UNSAT / incompleteness (#7956):
/// the rescue returns a `NeedModelEquality` that does not address the
/// conflict, the SAT-asserted atoms in the conflict reasons are never
/// revisited, and the solver either loops (until the per-pair budget is
/// hit) or terminates with the wrong answer.
pub(super) fn conflict_involves_array_theory(terms: &TermStore, literals: &[TheoryLit]) -> bool {
    literals
        .iter()
        .any(|lit| term_mentions_array(terms, lit.term))
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
