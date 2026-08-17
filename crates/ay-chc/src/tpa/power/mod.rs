// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Power abstraction management for TPA.
//!
//! Manages the exact (T^{=n}) and less-than (T^{<n}) power abstractions,
//! including composition, strengthening via interpolation, Houdini filtering,
//! and fixed-point detection.
//!
//! Reference: Golem TPA.cc power management (357-396),
//!            Golem TPA.cc fixed point checks (975-1140)

mod bool_partition;

use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::transition_system::TransitionSystem;
use crate::ChcExpr;

use super::solver::{flatten_to_constraints, PowerKind, SafetyExplanation, TpaSolver};

use bool_partition::{bool_partition_branch_count, classify_bool_partition};

/// Maximum total Bool branch combinations before we refuse to even try
/// the partitioned path.
const BOOL_PARTITION_BRANCH_LIMIT: usize = 65536;

/// Cap on Houdini candidate conjuncts before pairwise squashing kicks in.
///
/// Mirrors Golem's `squashInvariants` limit (TPA.cc:894): keeps each
/// inductiveness SMT query bounded even when a power abstraction has an
/// unusually large conjunction.
const HOUDINI_CANDIDATE_CAP: usize = 128;

/// Hard cap on Houdini refinement passes. Houdini converges in at most
/// `#candidates` passes; the cap bounds worst-case SMT calls when the squashed
/// candidate set is large. Hitting the cap only forgoes committing survivors
/// this round (a completeness concession), never soundness.
const HOUDINI_MAX_PASSES: usize = 24;

/// Kill switch: `AY_TPA_NO_FIXPOINT=1` disables the repaired less-than
/// fixed-point safety detection (reverts TPA to power-deepening only).
fn fixpoint_disabled() -> bool {
    use std::sync::OnceLock;
    static OFF: OnceLock<bool> = OnceLock::new();
    *OFF.get_or_init(|| !crate::ab_switches::get().tpa_fixpoint)
}

impl TpaSolver {
    /// Get exact power abstraction at the given level.
    ///
    /// Returns the stored pure transition summary. Exact powers are learned
    /// through interpolation (not computed by explicit composition), so they
    /// mention only current-state and next-state variables — never intermediate
    /// midpoint layers. This prevents the geometric formula blowup that
    /// occurred when powers were built by explicit conjunction.
    ///
    /// Level 0 is always the base transition T (set in `init_powers`).
    /// Higher levels are populated by `strengthen_power_with_interpolant`.
    ///
    /// Reference: Golem TPA.cc:getExactPower (line 352-355)
    pub(super) fn get_exact_power(&self, power: u32, _ts: &TransitionSystem) -> Option<ChcExpr> {
        let idx = power as usize;
        if idx < self.exact_powers.len() {
            self.exact_powers[idx].clone()
        } else {
            None
        }
    }

    /// Get less-than power abstraction at the given level.
    ///
    /// Returns the stored pure transition summary. Less-than powers are learned
    /// through interpolation, not computed by explicit composition.
    /// Level 0 is always the identity (0 transition steps, set in `init_powers`).
    ///
    /// Reference: Golem TPA.cc:getLessThanPower (line 381-384)
    pub(super) fn get_less_than_power(
        &self,
        power: u32,
        _ts: &TransitionSystem,
    ) -> Option<ChcExpr> {
        let idx = power as usize;
        if idx < self.less_than_powers.len() {
            self.less_than_powers[idx].clone()
        } else {
            None
        }
    }

    /// Get power abstraction for the given kind (exact or less-than).
    pub(super) fn get_power(
        &self,
        kind: PowerKind,
        power: u32,
        ts: &TransitionSystem,
    ) -> Option<ChcExpr> {
        match kind {
            PowerKind::Exact => self.get_exact_power(power, ts),
            PowerKind::LessThan => self.get_less_than_power(power, ts),
        }
    }

    /// Strengthen power abstraction with a learned interpolant.
    ///
    /// Stores the interpolant at level `power + 1`, conjoining with any
    /// existing value. If the slot is empty, stores the interpolant directly.
    /// This matches Golem's storeExactPower/storeLessThanPower semantics
    /// (TPA.cc:357-396): exact powers are pure learned summaries, not
    /// compositions of lower levels.
    ///
    /// Reference: Golem TPA.cc:storeExactPower (line 357-378),
    ///            Golem TPA.cc:storeLessThanPower (line 386-396)
    fn strengthen_power_with_interpolant(
        &mut self,
        kind: PowerKind,
        power: u32,
        interpolant: ChcExpr,
    ) {
        if self.config.verbose_level > 0 {
            let kind_name = match kind {
                PowerKind::Exact => "Exact",
                PowerKind::LessThan => "Less-than",
            };
            safe_eprintln!(
                "TPA: strengthening {} power {} with interpolant ({} conjuncts)",
                kind_name,
                power,
                interpolant.collect_conjuncts().len()
            );
        }

        let idx = (power + 1) as usize;
        let powers = match kind {
            PowerKind::Exact => &mut self.exact_powers,
            PowerKind::LessThan => &mut self.less_than_powers,
        };
        if powers.len() <= idx {
            powers.resize_with(idx + 1, || None);
        }
        let new_val = match powers[idx].take() {
            Some(existing) => ChcExpr::and(existing, interpolant),
            None => interpolant,
        };
        powers[idx] = Some(new_val);
    }

    /// Compute interpolant from an UNSAT reachability query and strengthen.
    ///
    /// For exact: query was from(v) ∧ T^{=n}(v,v_1) ∧ T^{=n}(v_1,v_2) ∧ to(v_2)
    /// For less-than: learns from the composed case:
    ///   from(v) ∧ T^{<n}(v,v_1) ∧ T^{=n}(v_1,v_2) ∧ to(v_2)
    ///
    /// Partitions at intermediate state v_1:
    /// - A: from(v) ∧ T^{kind}(v, v_1)
    /// - B: T^{=n}(v_1, v_2) ∧ to(v_2)
    ///
    /// The interpolant constrains intermediate states at time 1 and strengthens
    /// the power abstraction at `power + 1`.
    pub(super) fn strengthen_power_from_unsat(
        &mut self,
        kind: PowerKind,
        power: u32,
        from: &ChcExpr,
        to: &ChcExpr,
        ts: &TransitionSystem,
    ) {
        let a_power = match self.get_power(kind, power, ts) {
            Some(p) => p,
            None => return, // Level not learned yet, skip strengthening
        };

        // B-partition always uses the exact power shifted to time 1→2
        let exact_power = match self.get_exact_power(power, ts) {
            Some(ep) => ep,
            None => return, // Level not learned yet, skip strengthening
        };
        let shifted_exact = self.shift_and_freshen(&exact_power, 1, ts);

        // A-partition: from(v) ∧ T^{kind}(v, v_1)
        let a_constraints = {
            let mut constraints = flatten_to_constraints(from);
            constraints.extend(flatten_to_constraints(&a_power));
            constraints
        };

        // B-partition: T^{=n}(v_1, v_2) ∧ to(v_2)
        let shifted_to = self.shift_expr(to, 2, ts);
        let b_constraints = {
            let mut constraints = flatten_to_constraints(&shifted_exact);
            constraints.extend(flatten_to_constraints(&shifted_to));
            constraints
        };

        // Shared variables are at time 1 (the intermediate state)
        let shared_vars = ts.state_var_names_at(1);

        let kind_name = match kind {
            PowerKind::Exact => "Exact",
            PowerKind::LessThan => "Less-than",
        };

        let bool_partition = classify_bool_partition(&a_constraints, &b_constraints);
        let bool_var_count = bool_partition.a_local.len()
            + bool_partition.shared.len()
            + bool_partition.b_local.len();
        if bool_var_count > 0 {
            let branch_count = bool_partition_branch_count(&bool_partition);
            if branch_count.is_some_and(|count| count <= BOOL_PARTITION_BRANCH_LIMIT) {
                if let Some(interpolant) = self.interpolate_with_full_bool_partitioning(
                    &a_constraints,
                    &b_constraints,
                    &shared_vars,
                    &bool_partition,
                ) {
                    if self.config.verbose_level > 0 {
                        safe_eprintln!(
                            "TPA: full Bool partition interpolation succeeded at power {} ({} kind), {} conjuncts, {}/{}/{} Bool vars, {} branch pairs",
                            power,
                            kind_name,
                            interpolant.collect_conjuncts().len(),
                            bool_partition.a_local.len(),
                            bool_partition.shared.len(),
                            bool_partition.b_local.len(),
                            branch_count.expect("checked above")
                        );
                    }
                    self.strengthen_power_with_interpolant(kind, power, interpolant);
                    return;
                }
                if self.config.verbose_level > 0 {
                    safe_eprintln!(
                        "TPA: full Bool partition interpolation failed at power {} ({} kind), falling back",
                        power, kind_name
                    );
                }
            } else if self.config.verbose_level > 0 {
                safe_eprintln!(
                    "TPA: skipping full Bool partition interpolation at power {} ({} kind): {} Bool vars exceed {} branch pairs",
                    power,
                    kind_name,
                    bool_var_count,
                    BOOL_PARTITION_BRANCH_LIMIT
                );
            }
        }

        // Standard interpolation (no Bool partitioning)
        match interpolating_sat_constraints(&a_constraints, &b_constraints, &shared_vars) {
            InterpolatingSatResult::Unsat(interpolant) => {
                if self.config.verbose_level > 0 {
                    safe_eprintln!(
                        "TPA: interpolation succeeded at power {} ({} kind), {} conjuncts",
                        power,
                        kind_name,
                        interpolant.collect_conjuncts().len()
                    );
                }
                self.strengthen_power_with_interpolant(kind, power, interpolant);
            }
            InterpolatingSatResult::Unknown => {
                if self.config.verbose_level > 0 {
                    safe_eprintln!(
                        "TPA: interpolation FAILED at power {} ({} kind), {} shared vars",
                        power,
                        kind_name,
                        shared_vars.len()
                    );
                }
            }
        }
    }

    /// Check if a power abstraction reached a safe fixed point.
    ///
    /// Only the less-than hierarchy is currently used for safety; the exact
    /// (k-inductive) fixed point is deferred (see below). For less-than this
    /// dispatches to [`Self::check_less_than_fixed_point`], which runs the
    /// Houdini-strengthened fixed-point exits from Golem's
    /// `checkLessThanFixedPoint` (TPA.cc:975-1078).
    ///
    /// SOUNDNESS (#7467): Exact fixed-point acceptance stays disabled here. A
    /// bare exact fixed point (`T^{=n} ∘ T^{=n} ⊆ T^{=n}`) only proves closure
    /// of the `2^n`-step relation under self-composition, not closure under one
    /// step, so it does not by itself certify safety. Golem builds a separate
    /// `safeTransitionInvariant` from `T^{<i}` and `T^{=i}` plus a k→1-inductive
    /// conversion; that port is a later increment.
    pub(super) fn check_fixed_point(
        &mut self,
        kind: PowerKind,
        power: u32,
        ts: &TransitionSystem,
    ) -> bool {
        if power == 0 {
            return false;
        }
        // Kill switch (#chc25-split-tpa): AY_TPA_NO_FIXPOINT=1 disables the
        // repaired less-than fixed-point safety detection, reverting TPA to its
        // prior behavior (deepen powers until Unsafe/Unknown). The result is
        // never wrong either way — the portfolio re-verifies every Safe — so this
        // is a performance/behavior escape hatch, not a soundness control.
        if fixpoint_disabled() {
            return false;
        }
        match kind {
            PowerKind::Exact => false,
            PowerKind::LessThan => self.check_less_than_fixed_point(power, ts),
        }
    }

    /// Less-than fixed-point detection via a Houdini-strengthened 1-inductive
    /// state-invariant check.
    ///
    /// AY's less-than powers `lt[i]` are Craig interpolants over the reached
    /// state variables (time index 1) — *state sets* over-approximating the
    /// states reachable from init in `< 2^i` steps, not the two-copy transition
    /// relations of Golem's `TPASplit`. So the analogue of Golem's
    /// `checkLessThanFixedPoint` is a standard inductive-invariant test: for each
    /// learned level `i ≤ power`, interpret `lt[i]` as a state predicate `S(x)`
    /// (renaming the reached vars back to the base copy), then
    ///
    /// 1. grow the persistent inductive state-invariant set via a Houdini pass
    ///    over `S`'s conjuncts, and
    /// 2. try the accumulated invariants — alone and conjoined with `S` — as a
    ///    1-inductive safe invariant through [`Self::record_safe_state_invariant`].
    ///
    /// SOUNDNESS: [`Self::record_safe_state_invariant`] verifies the *definition*
    /// of a safe inductive invariant directly (`init ⇒ Inv`, `Inv ∧ Tr ⇒ Inv'`,
    /// `Inv ∧ query` UNSAT). These three conditions alone certify safety
    /// regardless of where the candidate came from, so no over-approximation
    /// argument about the powers is required. The portfolio's
    /// `verify_model_per_rule` gate re-checks the emitted invariant on the
    /// ORIGINAL clauses as a second, independent authority.
    fn check_less_than_fixed_point(&mut self, power: u32, ts: &TransitionSystem) -> bool {
        for i in 1..=power {
            if self.is_cancelled() {
                return false;
            }
            let Some(lt_i) = self.get_less_than_power(i, ts) else {
                continue;
            };
            // Interpret the reached-state formula as a state predicate over the
            // base copy (rename time-1 vars → time-0).
            let s_state = ts.rename_state_vars_at(&lt_i, 1, 0);
            let candidates_i = s_state.collect_conjuncts();

            // Grow the persistent inductive invariant set from this level.
            self.houdini_filter_state(&candidates_i, ts);

            let acc = ChcExpr::and_all(self.state_invariants.iter().cloned());
            let attempts = [ChcExpr::and(acc.clone(), s_state.clone()), acc, s_state];
            for inv in attempts {
                if matches!(inv, ChcExpr::Bool(true)) {
                    continue;
                }
                if self.record_safe_state_invariant(inv, i, ts) {
                    return true;
                }
            }
        }
        false
    }

    /// Verify a candidate state predicate is a safe 1-inductive invariant and,
    /// on success, record it for extraction.
    ///
    /// Returns `true` iff all three inductive-invariant conditions hold
    /// (each requiring a definite UNSAT; a solver `Unknown` fails closed):
    /// 1. **Initiation**  `init(x) ∧ ¬Inv(x)` UNSAT,
    /// 2. **Consecution** `Inv(x) ∧ Tr(x, x') ∧ ¬Inv(x')` UNSAT,
    /// 3. **Safety**      `Inv(x) ∧ query(x)` UNSAT.
    fn record_safe_state_invariant(
        &mut self,
        inv: ChcExpr,
        level: u32,
        ts: &TransitionSystem,
    ) -> bool {
        // 1. Initiation.
        let initiation = ChcExpr::and(ts.init.clone(), ChcExpr::not(inv.clone()));
        if !self
            .smt
            .check_sat_with_timeout(&initiation, self.config.timeout_per_power)
            .is_unsat()
        {
            return false;
        }

        // 2. Consecution: Inv(x) ∧ Tr(x, x_1) ∧ ¬Inv(x_1).
        let inv_next = ts.send_through_time(&inv, 1);
        let consecution =
            ChcExpr::and_all([inv.clone(), ts.transition_at(0), ChcExpr::not(inv_next)]);
        if !self
            .smt
            .check_sat_with_timeout(&consecution, self.config.timeout_per_power)
            .is_unsat()
        {
            return false;
        }

        // 3. Safety: Inv(x) ∧ query(x).
        let safety = ChcExpr::and(inv.clone(), ts.query.clone());
        if !self
            .smt
            .check_sat_with_timeout(&safety, self.config.timeout_per_power)
            .is_unsat()
        {
            return false;
        }

        if self.config.verbose_level > 0 {
            safe_eprintln!(
                "TPA: less-than fixed point verified safe at level {} ({} conjuncts)",
                level,
                inv.collect_conjuncts().len()
            );
        }
        self.explanation = Some(SafetyExplanation {
            state_invariant: inv,
        });
        true
    }

    /// Houdini pass: grow the persistent inductive state-invariant set with the
    /// self-inductive subset of `candidates`.
    ///
    /// Analogue of Golem's `houdiniCheck` (TPA.cc:906-973) over a single state
    /// copy. Starting from the candidate conjuncts (squashed to at most
    /// [`HOUDINI_CANDIDATE_CAP`]), repeatedly drops any candidate `c` that the
    /// current candidate conjunction does not re-derive after one transition
    /// (`⋀survivors(x) ∧ Tr(x, x') ⇒ c(x')`), until a fixed point. A *converged*
    /// survivor set is jointly self-inductive and is appended (deduplicated) to
    /// the persistent invariants.
    fn houdini_filter_state(&mut self, candidates: &[ChcExpr], ts: &TransitionSystem) {
        let mut candidates: Vec<ChcExpr> = candidates
            .iter()
            .filter(|c| !matches!(c, ChcExpr::Bool(true)))
            .cloned()
            .collect();
        squash_invariants(&mut candidates);
        if candidates.is_empty() {
            return;
        }

        // Iterate to a fixed point: at most one candidate is guaranteed to drop
        // per pass, so `candidates.len()` passes suffice. Cap the pass count so a
        // pathologically large (squashed) candidate set cannot make a single
        // fixed-point check dominate the power budget; a premature stop only
        // yields a possibly-smaller (still sound) inductive set.
        let mut converged = false;
        let max_passes = (candidates.len() + 1).min(HOUDINI_MAX_PASSES);
        for _ in 0..max_passes {
            if self.is_cancelled() {
                return;
            }
            // ⋀survivors(x) ∧ Tr(x, x_1); each goal is c(x_1).
            let conj = ChcExpr::and_all(candidates.iter().cloned());
            let lhs = ChcExpr::and(conj, ts.transition_at(0));

            let mut survivors = Vec::with_capacity(candidates.len());
            let mut dropped_any = false;
            for cand in &candidates {
                let goal = ts.send_through_time(cand, 1); // c(x_1)
                let query = ChcExpr::and(lhs.clone(), ChcExpr::not(goal));
                let implied = self
                    .smt
                    .check_sat_with_timeout(&query, self.config.timeout_per_power)
                    .is_unsat();
                if implied {
                    survivors.push(cand.clone());
                } else {
                    dropped_any = true;
                }
                if self.is_cancelled() {
                    return;
                }
            }
            candidates = survivors;
            if !dropped_any || candidates.is_empty() {
                converged = true;
                break;
            }
        }

        // Only commit a *converged* (jointly self-inductive) survivor set to the
        // persistent invariants. A pass-capped, not-yet-converged set could still
        // contain a non-inductive conjunct; adding it would pollute future
        // fixed-point candidates (a completeness loss). Soundness never depends on
        // this — `record_safe_state_invariant` re-verifies the full candidate.
        if !converged {
            return;
        }
        for cand in candidates {
            if !self.state_invariants.contains(&cand) {
                self.state_invariants.push(cand);
            }
        }
    }
}

/// Squash a candidate list down to at most [`HOUDINI_CANDIDATE_CAP`] entries by
/// pairwise conjunction, mirroring Golem's `squashInvariants` (TPA.cc:894-904).
///
/// Conjoining two candidates cannot turn a jointly-inductive set unsound: the
/// Houdini closure check and `record_safe_state_invariant` re-verify whatever
/// survives, so squashing only trades granularity for a bounded candidate count.
fn squash_invariants(candidates: &mut Vec<ChcExpr>) {
    while candidates.len() > HOUDINI_CANDIDATE_CAP {
        let mut j = 0;
        let mut i = candidates.len() - 1;
        while i >= 1 && i > j {
            let merged = ChcExpr::and(candidates[j].clone(), candidates[i].clone());
            candidates.pop();
            candidates[j] = merged;
            if candidates.len() <= HOUDINI_CANDIDATE_CAP {
                break;
            }
            j += 1;
            i -= 1;
        }
    }
}

#[cfg(test)]
mod tests;
