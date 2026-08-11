// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Product-native primal stochastic local search (SLS) for *non-linear*
//! pseudo-Boolean optimization (the OPT-NLC track) — a WalkSAT /
//! min-conflicts-style flip search that, unlike [`crate::optimize::sls`], tracks
//! PRODUCT terms exactly so it can find a *feasible* assignment and drive the
//! objective down on instances whose constraints and/or objective contain
//! `coeff · (l_1 ∧ l_2 ∧ …)` terms (a term is true iff ALL its literals are
//! true). This is the missing first-class primal for OPT-NLC: on the local QPLIB
//! family AY's complete engine returns UNKNOWN with no `o` line, and the linear
//! SLS *declines* (it defensively rejects any non-linear term), so AY emits no
//! incumbent at all. This module lets AY stream a verified feasible incumbent
//! there — a strict no-incumbent → incumbent gain.
//!
//! # Incremental product tracker
//! For each constraint (and the objective, treated as a pseudo-constraint) we
//! maintain the exact left-hand side `Σ coeff_t · [term_t true]`. For each
//! product term we maintain `false_count` = how many of its literals are
//! currently FALSE; the term is true iff `false_count == 0`. A variable flip only
//! touches the terms it occurs in: each touched term's `false_count` moves by ±1,
//! and a term toggles exactly when its `false_count` crosses `0 ↔ 1`, changing
//! the owning constraint's LHS by `±coeff`. Flip deltas are therefore computed in
//! `O(touched terms)`, never `O(all terms)`.
//!
//! # Soundness (NON-NEGOTIABLE — identical posture to [`crate::optimize::sls`])
//! This module is ADVISORY ONLY. It can only ever PROPOSE feasible incumbents; it
//! can NEVER claim a global OPTIMUM or UNSAT.
//!
//! 1. The incremental tracker steers the search; it never decides what is
//!    reported. A bug in it can only waste cycles, never emit a wrong answer.
//! 2. Every candidate the search wants to report is re-verified with
//!    `verify_all_constraints` against ALL original constraints (which evaluates
//!    PRODUCT terms exactly via `eval_term`) and its objective recomputed exactly
//!    with `eval_objective` before `on_improve` is called, and only a
//!    strictly-improving feasible point is ever reported. The portfolio caller
//!    re-verifies a SECOND time via `sanitize_optimization_incumbent`.
//! 3. The function returns at most an improved feasible assignment plus its exact
//!    objective; never a "proven optimum" / "infeasible" verdict.
//! 4. The PRNG is seeded deterministically from instance *structure* only
//!    (reusing [`crate::optimize::lns::structural_seed`]), so runs are
//!    bit-for-bit reproducible.

use crate::eval::verify_all_constraints;
use crate::optimize::lns::{structural_seed, SplitMix64};
use crate::solver::eval_objective;
use crate::types::{PbInstance, PbObjective, PbRel};

/// Maximum number of variables a product-SLS run will accept (mirrors the linear
/// `MAX_SLS_VARS`). Above this the per-flip bookkeeping is too coarse to help in
/// a time slice; decline.
const MAX_NLC_VARS: usize = 200_000;

/// Maximum total number of literal occurrences (Σ over all terms of the term's
/// literal count, across every constraint and the objective) the inverse index
/// will build. Declining above this keeps the index from blowing up.
const MAX_NLC_OCCURRENCES: usize = 16_000_000;

/// Hard cap on flips per call so an absent deadline still terminates (tests).
const MAX_FLIPS: u64 = 200_000_000;

/// How often (in flips) to poll the stop signal / deadline.
const STOP_POLL_INTERVAL: u64 = 1024;

/// WalkSAT random-walk probability (in 1/1000): with this probability the
/// feasibility phase picks a random variable from the chosen violated constraint
/// rather than the greedy best one.
const WALK_NOISE_PERMILLE: u64 = 200;

/// Consecutive non-improving feasibility flips after which the PAWS-style weights
/// of currently-violated constraints are bumped (to escape plateaus).
const PAWS_BUMP_INTERVAL: u64 = 1;

/// Objective-descent random-walk probability (in 1/1000): occasionally skip the
/// greedy objective step to diversify.
const OBJ_NOISE_PERMILLE: u64 = 50;

/// Sentinel "constraint index" used by occurrences that belong to the objective
/// pseudo-constraint rather than a real hard constraint.
const OBJECTIVE_OWNER: u32 = u32::MAX;

/// Outcome of a product-SLS run: the best feasible incumbent found, or `None`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NlcResult {
    pub(crate) assignment: Vec<bool>,
    pub(crate) objective: i128,
}

/// Tuning knobs for one product-native SLS trajectory. [`Default`] reproduces the
/// historical `search` / `search_with_seed_xor` behaviour BYTE-FOR-BYTE (no
/// seed diversifier, current-anchored perturbation), so every existing caller is
/// unaffected. A diversified parallel worker overrides these to explore a
/// deterministically different trajectory (the mirror of the linear SLS's
/// `SlsOptions`); soundness is UNAFFECTED either way — every reported incumbent is
/// still re-verified and exactly valued.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct NlcSearchOptions {
    /// XOR diversifier folded into the structural RNG seed (see
    /// `search_with_seed_xor`). `0` reproduces the unmodified [`structural_seed`].
    pub(crate) seed_xor: u64,
    /// When the objective descent gets STUCK (no strictly-improving objective flip
    /// and no feasibility-preserving sideways flip), re-anchor the diversifying
    /// perturbation on the BEST feasible incumbent found so far (intensification)
    /// instead of kicking from the current, possibly-drifted point. Anytime-safe:
    /// the best incumbent is always retained and every reported point is
    /// independently re-verified, so this only changes WHICH region the search
    /// re-explores, never what may be reported.
    pub(crate) intensify_from_best: bool,
}

/// Per (product) term cached state.
struct TermState {
    /// Coefficient contribution when the term is true.
    coeff: i128,
    /// How many of this term's literals are currently FALSE. The term is true iff
    /// this is 0.
    false_count: u32,
}

impl TermState {
    #[inline]
    fn is_true(&self) -> bool {
        self.false_count == 0
    }
}

/// Per-constraint cached state for the product tracker.
struct ConstraintState {
    /// Exact LHS = Σ coeff_t over currently-true terms.
    lhs: i128,
    rhs: i128,
    rel: PbRel,
    /// PAWS-style penalty weight (>= 1). Raised on plateaus.
    weight: i128,
}

impl ConstraintState {
    /// Non-negative "amount short" (0 when satisfied). Saturating so it cannot
    /// panic on pathological coefficients.
    fn shortfall(&self) -> i128 {
        shortfall_for(self.rel, self.lhs, self.rhs)
    }
}

/// Shortfall for a relation given LHS / RHS (free function so look-ahead code can
/// use it without borrowing a [`ConstraintState`]).
fn shortfall_for(rel: PbRel, lhs: i128, rhs: i128) -> i128 {
    match rel {
        PbRel::Ge => (rhs.saturating_sub(lhs)).max(0),
        PbRel::Eq => lhs.saturating_sub(rhs).saturating_abs(),
    }
}

/// One occurrence of a variable inside a term: identifies which constraint owns
/// the term, the term's global index, and whether the literal there is positive
/// (so the literal is true when the variable is true) or negated.
struct Occurrence {
    /// Owning constraint index, or [`OBJECTIVE_OWNER`] for the objective.
    owner: u32,
    /// Global index into the flat `terms` (or `obj_terms`) vector.
    term: u32,
    /// `true` if the literal is negated (`~v`): then the literal is true when the
    /// variable is FALSE.
    negated: bool,
}

/// Product-native incremental tracker over all hard constraints plus the
/// objective. Maintains every constraint's exact product LHS and the objective
/// value so that a single variable flip costs `O(occ(v))`.
struct ProductTracker {
    /// Flat term states for hard constraints, pushed in constraint order (each
    /// constraint's terms form a contiguous slice by construction; the flip path
    /// addresses terms through per-variable occurrence lists, not per constraint).
    terms: Vec<TermState>,
    states: Vec<ConstraintState>,
    /// Flat objective term states.
    obj_terms: Vec<TermState>,
    /// Exact current objective value (Σ coeff over true objective terms).
    objective_value: i128,
    /// For each variable, the (constraint/objective, term) occurrences it appears
    /// in.
    occurrences: Vec<Vec<Occurrence>>,
    /// Total weighted violation (Σ over violated constraints of weight·shortfall).
    weighted_violation: i128,
    /// Currently-violated constraint indices (incrementally maintained, O(1)
    /// swap-remove).
    violated_list: Vec<usize>,
    /// Position of constraint `c` in `violated_list`, or `usize::MAX` if not
    /// violated.
    violated_pos: Vec<usize>,
}

impl ProductTracker {
    /// Builds the tracker for `instance` / `objective` under `assignment`.
    /// Returns `None` if too large or a coefficient/index computation overflows.
    fn new(
        instance: &PbInstance,
        objective: &PbObjective,
        num_vars: usize,
        assignment: &[bool],
    ) -> Option<Self> {
        let mut occurrences: Vec<Vec<Occurrence>> = Vec::new();
        occurrences.resize_with(num_vars, Vec::new);
        let mut terms: Vec<TermState> = Vec::new();
        let mut states: Vec<ConstraintState> = Vec::with_capacity(instance.constraints.len());
        let mut total_occ = 0usize;

        for (ci, constraint) in instance.constraints.iter().enumerate() {
            let owner = u32::try_from(ci).ok()?;
            let mut lhs: i128 = 0;
            for term in &constraint.terms {
                if term.lits.is_empty() {
                    // An empty product is conventionally "true" (empty AND); it
                    // contributes its coefficient unconditionally and depends on
                    // no variable. Track it as a constant true term.
                    lhs = lhs.checked_add(term.coeff)?;
                    let term_index = u32::try_from(terms.len()).ok()?;
                    let _ = term_index;
                    terms.push(TermState {
                        coeff: term.coeff,
                        false_count: 0,
                    });
                    continue;
                }
                let term_index = u32::try_from(terms.len()).ok()?;
                let mut false_count: u32 = 0;
                for lit in &term.lits {
                    let var_index = (lit.var as usize).checked_sub(1)?;
                    if var_index >= num_vars {
                        return None;
                    }
                    let value = assignment.get(var_index).copied().unwrap_or(false);
                    let literal_true = if lit.negated { !value } else { value };
                    if !literal_true {
                        false_count = false_count.checked_add(1)?;
                    }
                    total_occ = total_occ.checked_add(1)?;
                    if total_occ > MAX_NLC_OCCURRENCES {
                        return None;
                    }
                    occurrences[var_index].push(Occurrence {
                        owner,
                        term: term_index,
                        negated: lit.negated,
                    });
                }
                if false_count == 0 {
                    lhs = lhs.checked_add(term.coeff)?;
                }
                terms.push(TermState {
                    coeff: term.coeff,
                    false_count,
                });
            }
            states.push(ConstraintState {
                lhs,
                rhs: constraint.rhs,
                rel: constraint.rel,
                weight: 1,
            });
        }

        // Objective pseudo-constraint.
        let mut obj_terms: Vec<TermState> = Vec::with_capacity(objective.terms.len());
        let mut objective_value: i128 = 0;
        for term in &objective.terms {
            if term.lits.is_empty() {
                objective_value = objective_value.checked_add(term.coeff)?;
                obj_terms.push(TermState {
                    coeff: term.coeff,
                    false_count: 0,
                });
                continue;
            }
            let term_index = u32::try_from(obj_terms.len()).ok()?;
            let mut false_count: u32 = 0;
            for lit in &term.lits {
                let var_index = (lit.var as usize).checked_sub(1)?;
                if var_index >= num_vars {
                    return None;
                }
                let value = assignment.get(var_index).copied().unwrap_or(false);
                let literal_true = if lit.negated { !value } else { value };
                if !literal_true {
                    false_count = false_count.checked_add(1)?;
                }
                total_occ = total_occ.checked_add(1)?;
                if total_occ > MAX_NLC_OCCURRENCES {
                    return None;
                }
                occurrences[var_index].push(Occurrence {
                    owner: OBJECTIVE_OWNER,
                    term: term_index,
                    negated: lit.negated,
                });
            }
            if false_count == 0 {
                objective_value = objective_value.checked_add(term.coeff)?;
            }
            obj_terms.push(TermState {
                coeff: term.coeff,
                false_count,
            });
        }

        let constraint_count = states.len();
        let mut tracker = ProductTracker {
            terms,
            states,
            obj_terms,
            objective_value,
            occurrences,
            weighted_violation: 0,
            violated_list: Vec::new(),
            violated_pos: vec![usize::MAX; constraint_count],
        };
        tracker.recompute_violation();
        Some(tracker)
    }

    fn num_violated(&self) -> usize {
        self.violated_list.len()
    }

    fn mark_violated(&mut self, c: usize) {
        if self.violated_pos[c] == usize::MAX {
            self.violated_pos[c] = self.violated_list.len();
            self.violated_list.push(c);
        }
    }

    fn mark_satisfied(&mut self, c: usize) {
        let pos = self.violated_pos[c];
        if pos == usize::MAX {
            return;
        }
        let last = self.violated_list.len() - 1;
        let moved = self.violated_list[last];
        self.violated_list.swap(pos, last);
        self.violated_list.pop();
        self.violated_pos[moved] = pos;
        self.violated_pos[c] = usize::MAX;
    }

    /// Recomputes `weighted_violation` and the violated-set from scratch.
    fn recompute_violation(&mut self) {
        let mut total: i128 = 0;
        self.violated_list.clear();
        for pos in self.violated_pos.iter_mut() {
            *pos = usize::MAX;
        }
        for ci in 0..self.states.len() {
            let short = self.states[ci].shortfall();
            if short > 0 {
                total = total.saturating_add(self.states[ci].weight.saturating_mul(short));
                self.violated_pos[ci] = self.violated_list.len();
                self.violated_list.push(ci);
            }
        }
        self.weighted_violation = total;
    }

    /// Applies a flip of `var` (0-indexed): updates every touched term's
    /// `false_count`, the owning constraint LHS (and objective value), and the
    /// aggregate violation counters. `new_value` is the value AFTER the flip.
    fn apply_flip(&mut self, var: usize, new_value: bool) {
        let occ_len = self.occurrences[var].len();
        for i in 0..occ_len {
            // Copy the small occurrence record so we can mutate term/constraint
            // state without holding a borrow of `self.occurrences[var]`.
            let (owner, term_idx, negated) = {
                let o = &self.occurrences[var][i];
                (o.owner, o.term as usize, o.negated)
            };
            // The literal is true when (var == !negated). After the flip the
            // literal's truth is `new_value != negated`. We need the DIRECTION the
            // false_count moves: literal becoming false => +1; becoming true => -1.
            let literal_true_after = new_value != negated;

            if owner == OBJECTIVE_OWNER {
                let was_true = self.obj_terms[term_idx].is_true();
                if literal_true_after {
                    self.obj_terms[term_idx].false_count -= 1;
                } else {
                    self.obj_terms[term_idx].false_count += 1;
                }
                let now_true = self.obj_terms[term_idx].is_true();
                if !was_true && now_true {
                    self.objective_value = self
                        .objective_value
                        .saturating_add(self.obj_terms[term_idx].coeff);
                } else if was_true && !now_true {
                    self.objective_value = self
                        .objective_value
                        .saturating_sub(self.obj_terms[term_idx].coeff);
                }
                continue;
            }

            let c = owner as usize;
            let was_true = self.terms[term_idx].is_true();
            if literal_true_after {
                self.terms[term_idx].false_count -= 1;
            } else {
                self.terms[term_idx].false_count += 1;
            }
            let now_true = self.terms[term_idx].is_true();
            if was_true == now_true {
                continue;
            }
            let coeff = self.terms[term_idx].coeff;
            let state = &mut self.states[c];
            let before_short = state.shortfall();
            let before_weighted = weighted(state.weight, before_short);
            if now_true {
                state.lhs = state.lhs.saturating_add(coeff);
            } else {
                state.lhs = state.lhs.saturating_sub(coeff);
            }
            let after_short = state.shortfall();
            let after_weighted = weighted(state.weight, after_short);
            if before_short == 0 && after_short > 0 {
                self.mark_violated(c);
            } else if before_short > 0 && after_short == 0 {
                self.mark_satisfied(c);
            }
            self.weighted_violation = self
                .weighted_violation
                .saturating_sub(before_weighted)
                .saturating_add(after_weighted);
        }
    }

    /// Weighted-violation delta that flipping `var` to `new_value` would produce,
    /// WITHOUT mutating state. Lower (more negative) is better in the feasibility
    /// phase.
    ///
    /// A product term can have multiple literals of the SAME variable; flipping
    /// the variable moves each such literal independently, so we accumulate the
    /// net `false_count` change per touched term before deciding whether the term
    /// toggles. Multiple touched terms can also belong to the same constraint, so
    /// we then coalesce per-constraint LHS deltas. Both use the generation-stamped
    /// [`FlipScratch`] so the work stays `O(touched)`.
    fn flip_violation_delta_for(
        &self,
        var: usize,
        new_value: bool,
        scratch: &mut FlipScratch,
    ) -> i128 {
        self.fold_flip_into_constraints(var, new_value, scratch);
        let mut delta: i128 = 0;
        for ci in scratch.touched_constraints() {
            let lhs_delta = scratch.constraint_delta(ci);
            let state = &self.states[ci];
            let before_short = state.shortfall();
            let before_weighted = weighted(state.weight, before_short);
            let new_lhs = state.lhs.saturating_add(lhs_delta);
            let after_short = shortfall_for(state.rel, new_lhs, state.rhs);
            let after_weighted = weighted(state.weight, after_short);
            delta = delta
                .saturating_sub(before_weighted)
                .saturating_add(after_weighted);
        }
        delta
    }

    /// Populates `scratch`'s constraint accumulator with the per-constraint LHS
    /// deltas that flipping `var` to `new_value` would cause. Coalesces literals
    /// of the same variable within a term and multiple toggled terms within a
    /// constraint, all in `O(touched)` via the generation-stamped scratch.
    fn fold_flip_into_constraints(&self, var: usize, new_value: bool, scratch: &mut FlipScratch) {
        scratch.begin();
        for o in &self.occurrences[var] {
            if o.owner == OBJECTIVE_OWNER {
                continue;
            }
            let literal_true_after = new_value != o.negated;
            let step: i32 = if literal_true_after { -1 } else { 1 };
            scratch.bump(o.term, o.owner, step);
        }
        // Snapshot the touched-term ids so we can read term state and write the
        // constraint accumulator without aliasing the scratch's touched-term Vec.
        let touched_terms = std::mem::take(&mut scratch.term_touched);
        for &t in &touched_terms {
            let term_idx = t as usize;
            let term = &self.terms[term_idx];
            let was_true = term.false_count == 0;
            let new_false = (term.false_count as i64) + scratch.term_delta[term_idx] as i64;
            let now_true = new_false == 0;
            if was_true == now_true {
                continue;
            }
            let c = scratch.term_owner[term_idx] as usize;
            let lhs_delta = if now_true { term.coeff } else { -term.coeff };
            scratch.bump_constraint(c, lhs_delta);
        }
        scratch.term_touched = touched_terms;
    }

    /// Whether flipping `var` to `new_value` keeps EVERY constraint satisfied
    /// (objective-descent phase). Assumes the current assignment is feasible.
    fn flip_preserves_feasibility(
        &self,
        var: usize,
        new_value: bool,
        scratch: &mut FlipScratch,
    ) -> bool {
        self.fold_flip_into_constraints(var, new_value, scratch);
        for ci in scratch.touched_constraints() {
            let lhs_delta = scratch.constraint_delta(ci);
            let state = &self.states[ci];
            let new_lhs = state.lhs.saturating_add(lhs_delta);
            if shortfall_for(state.rel, new_lhs, state.rhs) > 0 {
                return false;
            }
        }
        true
    }

    /// Change in the objective value from flipping `var` to `new_value`. Negative
    /// means the objective decreases (good — we minimize).
    fn flip_objective_delta(&self, var: usize, new_value: bool, scratch: &mut FlipScratch) -> i128 {
        scratch.begin();
        for o in &self.occurrences[var] {
            if o.owner != OBJECTIVE_OWNER {
                continue;
            }
            let literal_true_after = new_value != o.negated;
            let step: i32 = if literal_true_after { -1 } else { 1 };
            scratch.bump_obj(o.term, step);
        }
        let mut delta: i128 = 0;
        for entry in scratch.obj_entries() {
            let term = &self.obj_terms[entry.term as usize];
            let was_true = term.false_count == 0;
            let new_false = (term.false_count as i64) + entry.delta as i64;
            let now_true = new_false == 0;
            if was_true == now_true {
                continue;
            }
            if now_true {
                delta = delta.saturating_add(term.coeff);
            } else {
                delta = delta.saturating_sub(term.coeff);
            }
        }
        delta
    }

    /// Raises the penalty weight of every currently-violated constraint by 1
    /// (PAWS additive bump). O(violated): each +1 weight adds that constraint's
    /// shortfall to the aggregate; the violated-set itself is unchanged (a weight
    /// bump cannot change any shortfall).
    fn bump_violated_weights(&mut self) {
        let mut added: i128 = 0;
        for i in 0..self.violated_list.len() {
            let c = self.violated_list[i];
            let short = self.states[c].shortfall(); // > 0 by invariant
            self.states[c].weight = self.states[c].weight.saturating_add(1);
            added = added.saturating_add(short);
        }
        self.weighted_violation = self.weighted_violation.saturating_add(added);
    }

    /// The incrementally-maintained exact LHS of constraint `c` (test-only
    /// accessor for the differential fuzz against a from-scratch recompute).
    #[cfg(test)]
    fn constraint_lhs(&self, c: usize) -> i128 {
        self.states[c].lhs
    }

    /// The incrementally-maintained exact objective value (test-only).
    #[cfg(test)]
    fn objective_value(&self) -> i128 {
        self.objective_value
    }

    /// The incrementally-maintained total weighted violation (test-only).
    #[cfg(test)]
    fn weighted_violation(&self) -> i128 {
        self.weighted_violation
    }

    /// Count of currently-violated constraints, computed from the incremental
    /// per-constraint LHS (test-only).
    #[cfg(test)]
    fn unweighted_num_violated(&self) -> usize {
        (0..self.states.len())
            .filter(|&c| self.states[c].shortfall() > 0)
            .count()
    }
}

#[inline]
fn weighted(weight: i128, short: i128) -> i128 {
    if short > 0 {
        weight.saturating_mul(short)
    } else {
        0
    }
}

/// A small reusable scratch buffer for accumulating per-term and per-constraint
/// net effects of a single variable flip without per-call heap churn. Because a
/// variable may appear multiple times in one term (and multiple terms may belong
/// to one constraint), we must coalesce by term index then by constraint index.
/// We use generation-stamped dense maps so `begin()` is O(1).
struct FlipScratch {
    // Term coalescing (hard-constraint terms).
    term_gen: Vec<u32>,
    term_delta: Vec<i32>,
    term_owner: Vec<u32>,
    term_touched: Vec<u32>,
    // Objective-term coalescing.
    obj_gen: Vec<u32>,
    obj_delta: Vec<i32>,
    obj_touched: Vec<u32>,
    // Constraint coalescing.
    con_gen: Vec<u32>,
    con_delta: Vec<i128>,
    con_touched: Vec<usize>,
    generation: u32,
}

struct ObjEntry {
    term: u32,
    delta: i32,
}

impl FlipScratch {
    fn new(num_terms: usize, num_obj_terms: usize, num_constraints: usize) -> Self {
        FlipScratch {
            term_gen: vec![0; num_terms],
            term_delta: vec![0; num_terms],
            term_owner: vec![0; num_terms],
            term_touched: Vec::new(),
            obj_gen: vec![0; num_obj_terms],
            obj_delta: vec![0; num_obj_terms],
            obj_touched: Vec::new(),
            con_gen: vec![0; num_constraints],
            con_delta: vec![0; num_constraints],
            con_touched: Vec::new(),
            generation: 0,
        }
    }

    fn begin(&mut self) {
        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 {
            // Generation wrapped; reset all stamps to avoid stale matches.
            for g in self.term_gen.iter_mut() {
                *g = 0;
            }
            for g in self.obj_gen.iter_mut() {
                *g = 0;
            }
            for g in self.con_gen.iter_mut() {
                *g = 0;
            }
            self.generation = 1;
        }
        self.term_touched.clear();
        self.obj_touched.clear();
        self.con_touched.clear();
    }

    fn bump(&mut self, term: u32, owner: u32, step: i32) {
        let t = term as usize;
        if self.term_gen[t] != self.generation {
            self.term_gen[t] = self.generation;
            self.term_delta[t] = 0;
            self.term_owner[t] = owner;
            self.term_touched.push(term);
        }
        self.term_delta[t] += step;
    }

    fn bump_obj(&mut self, term: u32, step: i32) {
        let t = term as usize;
        if self.obj_gen[t] != self.generation {
            self.obj_gen[t] = self.generation;
            self.obj_delta[t] = 0;
            self.obj_touched.push(term);
        }
        self.obj_delta[t] += step;
    }

    fn bump_constraint(&mut self, constraint: usize, lhs_delta: i128) {
        if self.con_gen[constraint] != self.generation {
            self.con_gen[constraint] = self.generation;
            self.con_delta[constraint] = 0;
            self.con_touched.push(constraint);
        }
        self.con_delta[constraint] = self.con_delta[constraint].saturating_add(lhs_delta);
    }

    fn obj_entries(&self) -> impl Iterator<Item = ObjEntry> + '_ {
        self.obj_touched.iter().map(move |&term| ObjEntry {
            term,
            delta: self.obj_delta[term as usize],
        })
    }

    /// The constraint indices touched by the last `fold_flip_into_constraints`.
    /// Returns an owned snapshot so the caller can read `constraint_delta` for
    /// each while iterating.
    fn touched_constraints(&self) -> Vec<usize> {
        self.con_touched.clone()
    }

    /// The accumulated LHS delta for a touched constraint.
    fn constraint_delta(&self, constraint: usize) -> i128 {
        self.con_delta[constraint]
    }
}

/// Runs product-native SLS to find (and improve) a feasible incumbent for
/// `instance` / `objective`, starting from all-false. Reports every adopted,
/// re-verified improvement through `on_improve` and returns the best feasible
/// incumbent found, or `None`. See the module docs for the soundness argument.
///
/// Test-only baseline wrapper: production callers go through
/// [`search_with_options`] directly (default options reproduce this
/// byte-for-byte).
#[cfg(test)]
pub(crate) fn search(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> Option<NlcResult> {
    search_with_options(
        instance,
        objective,
        deadline,
        should_stop,
        on_improve,
        NlcSearchOptions::default(),
    )
}

/// As [`search`], but with an XOR-diversifier folded into the structural RNG
/// seed (the product-native mirror of `SlsOptions::seed_xor`, design §2.3): a
/// diversified parallel worker passes its own fixed nonzero constant so its
/// trajectory deterministically differs from the default's on the same
/// instance. Still structure-only — no entropy, no instance identity — so
/// every run stays bit-for-bit reproducible. `0` reproduces the unmodified
/// [`structural_seed`] exactly ([`search`] delegates with `0`, so existing
/// callers are byte-identical).
///
/// Test-only wrapper (as [`search`]): production callers use
/// [`search_with_options`].
#[cfg(test)]
pub(crate) fn search_with_seed_xor(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    seed_xor: u64,
) -> Option<NlcResult> {
    search_with_options(
        instance,
        objective,
        deadline,
        should_stop,
        on_improve,
        NlcSearchOptions {
            seed_xor,
            intensify_from_best: false,
        },
    )
}

/// As `search_with_seed_xor`, but takes the full [`NlcSearchOptions`] knob set
/// (the product-native mirror of the linear SLS's `search_with_options`, design
/// §2.3). The default options reproduce `search` byte-for-byte; a diversified
/// parallel worker overrides them (a distinct `seed_xor` and/or
/// `intensify_from_best`) to explore a deterministically different trajectory.
/// Soundness is identical regardless of the options: every reported incumbent is
/// re-verified with `verify_all_constraints` and exactly valued with
/// `eval_objective` inside [`try_record_incumbent`], and the caller re-verifies a
/// second time.
pub(crate) fn search_with_options(
    instance: &PbInstance,
    objective: &PbObjective,
    deadline: Option<std::time::Instant>,
    should_stop: &dyn Fn() -> bool,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    options: NlcSearchOptions,
) -> Option<NlcResult> {
    let seed_xor = options.seed_xor;
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > MAX_NLC_VARS {
        return None;
    }
    if objective.terms.is_empty() {
        return None;
    }

    let stop = || should_stop() || deadline.is_some_and(|dl| std::time::Instant::now() >= dl);
    if stop() {
        return None;
    }

    let mut rng = SplitMix64::new(structural_seed(instance, objective) ^ seed_xor);

    // Deterministic, structure-free start. The feasibility phase finds a feasible
    // point from here; the start choice affects trajectory only, never soundness.
    let mut assignment = vec![false; num_vars];
    let mut tracker = ProductTracker::new(instance, objective, num_vars, &assignment)?;
    let mut scratch = FlipScratch::new(
        tracker.terms.len(),
        tracker.obj_terms.len(),
        tracker.states.len(),
    );

    let mut best: Option<NlcResult> = None;
    let mut flips: u64 = 0;
    let mut stale: u64 = 0;

    while flips < MAX_FLIPS {
        if flips.is_multiple_of(STOP_POLL_INTERVAL) && stop() {
            break;
        }

        if tracker.num_violated() > 0 {
            feasibility_step(
                instance,
                &mut assignment,
                &mut tracker,
                &mut scratch,
                &mut rng,
                &mut stale,
            );
        } else {
            try_record_incumbent(
                instance,
                objective,
                &assignment,
                &mut best,
                on_improve,
                &stop,
            );
            let made_progress = objective_step(
                num_vars,
                &mut assignment,
                &mut tracker,
                &mut scratch,
                &mut rng,
            );
            if !made_progress
                && !random_feasible_flip(
                    num_vars,
                    &mut assignment,
                    &mut tracker,
                    &mut scratch,
                    &mut rng,
                )
            {
                // STUCK: no strictly-improving objective flip and no
                // feasibility-preserving sideways flip. The intensifying
                // trajectory re-anchors on the best feasible incumbent (so the
                // diversifying kick re-explores the incumbent's basin instead of
                // drifting away from it); the default trajectory perturbs from the
                // current point exactly as before. Anytime-safe either way — `best`
                // is retained and every reported point is re-verified.
                if options.intensify_from_best {
                    if let Some(incumbent) = best.as_ref() {
                        reseat_to(&incumbent.assignment, &mut assignment, &mut tracker);
                    }
                }
                perturb(num_vars, &mut assignment, &mut tracker, &mut rng);
            }
        }

        flips += 1;
    }

    if tracker.num_violated() == 0 {
        try_record_incumbent(
            instance,
            objective,
            &assignment,
            &mut best,
            on_improve,
            &stop,
        );
    }

    best
}

/// One feasibility-phase flip: pick a random violated constraint, then flip the
/// variable in it that most reduces weighted violation (WalkSAT noise: sometimes
/// a random variable from that constraint). PAWS-bump on non-improving moves.
fn feasibility_step(
    instance: &PbInstance,
    assignment: &mut [bool],
    tracker: &mut ProductTracker,
    scratch: &mut FlipScratch,
    rng: &mut SplitMix64,
    stale: &mut u64,
) {
    if tracker.violated_list.is_empty() {
        return;
    }
    let pick = tracker.violated_list[rng.below(tracker.violated_list.len())];
    let constraint = &instance.constraints[pick];

    // Candidate variables: every variable appearing in any term of the chosen
    // violated constraint (deduplicated cheaply via a small vector; constraints
    // are typically modest in arity).
    let mut candidate_vars: Vec<usize> = Vec::new();
    for term in &constraint.terms {
        for lit in &term.lits {
            if let Some(idx) = (lit.var as usize).checked_sub(1) {
                if idx < assignment.len() && !candidate_vars.contains(&idx) {
                    candidate_vars.push(idx);
                }
            }
        }
    }
    if candidate_vars.is_empty() {
        return;
    }

    let chosen = if rng.below(1000) < WALK_NOISE_PERMILLE as usize {
        candidate_vars[rng.below(candidate_vars.len())]
    } else {
        let mut best_var = candidate_vars[0];
        let mut best_delta =
            tracker.flip_violation_delta_for(best_var, !assignment[best_var], scratch);
        for &v in &candidate_vars[1..] {
            let d = tracker.flip_violation_delta_for(v, !assignment[v], scratch);
            if d < best_delta {
                best_delta = d;
                best_var = v;
            }
        }
        best_var
    };

    let improving = tracker.flip_violation_delta_for(chosen, !assignment[chosen], scratch) < 0;
    let new_value = !assignment[chosen];
    assignment[chosen] = new_value;
    tracker.apply_flip(chosen, new_value);

    if improving {
        *stale = 0;
    } else {
        *stale += 1;
        if *stale >= PAWS_BUMP_INTERVAL {
            tracker.bump_violated_weights();
            *stale = 0;
        }
    }
}

/// One objective-descent flip while staying feasible. Scans variables that occur
/// in the objective for a feasibility-preserving flip that strictly lowers the
/// objective, takes the best one. Returns `true` if such a flip was made.
fn objective_step(
    num_vars: usize,
    assignment: &mut [bool],
    tracker: &mut ProductTracker,
    scratch: &mut FlipScratch,
    rng: &mut SplitMix64,
) -> bool {
    if rng.below(1000) < OBJ_NOISE_PERMILLE as usize {
        return false;
    }

    let mut best_var: Option<usize> = None;
    let mut best_gain: i128 = 0; // require strictly negative objective delta
    for var in 0..num_vars {
        let new_value = !assignment[var];
        let delta = tracker.flip_objective_delta(var, new_value, scratch);
        if delta >= 0 {
            continue;
        }
        if delta < best_gain && tracker.flip_preserves_feasibility(var, new_value, scratch) {
            best_gain = delta;
            best_var = Some(var);
        }
    }

    if let Some(var) = best_var {
        let new_value = !assignment[var];
        assignment[var] = new_value;
        tracker.apply_flip(var, new_value);
        true
    } else {
        false
    }
}

/// Takes one random feasibility-preserving flip (any variable). Returns `true` if
/// found and applied. Used to diversify when objective descent is stuck.
fn random_feasible_flip(
    num_vars: usize,
    assignment: &mut [bool],
    tracker: &mut ProductTracker,
    scratch: &mut FlipScratch,
    rng: &mut SplitMix64,
) -> bool {
    let attempts = 32usize.min(num_vars);
    for _ in 0..attempts {
        let var = rng.below(num_vars);
        let new_value = !assignment[var];
        if tracker.flip_preserves_feasibility(var, new_value, scratch) {
            assignment[var] = new_value;
            tracker.apply_flip(var, new_value);
            return true;
        }
    }
    false
}

/// Re-anchors the working assignment (and the incremental tracker) on `target` by
/// flipping exactly the variables that differ — the product-native mirror of the
/// linear SLS's best-incumbent reseat. Cost is `O(diff × occ)` (each differing
/// variable is a single `apply_flip`), so a re-anchor onto the best incumbent is
/// bounded by the same per-flip accounting as ordinary search. Used by the
/// intensifying trajectory to pull a drifted search back into the incumbent's
/// basin before the diversifying kick; never changes what may be reported (the
/// caller re-records only re-verified improvements).
fn reseat_to(target: &[bool], assignment: &mut [bool], tracker: &mut ProductTracker) {
    let n = assignment.len().min(target.len());
    for var in 0..n {
        if assignment[var] != target[var] {
            let new_value = target[var];
            assignment[var] = new_value;
            tracker.apply_flip(var, new_value);
        }
    }
}

/// Perturbs by flipping a few random variables (may break feasibility; the
/// feasibility phase repairs it). The best incumbent is already recorded, so this
/// can only help explore.
fn perturb(
    num_vars: usize,
    assignment: &mut [bool],
    tracker: &mut ProductTracker,
    rng: &mut SplitMix64,
) {
    let kicks = 1 + rng.below(3);
    for _ in 0..kicks {
        let var = rng.below(num_vars);
        let new_value = !assignment[var];
        assignment[var] = new_value;
        tracker.apply_flip(var, new_value);
    }
}

/// Re-verifies `assignment` against ALL original constraints (exact, products via
/// `eval_term`) and recomputes the objective exactly. If feasible AND strictly
/// better than the current best, records it and streams via `on_improve`.
///
/// Module-local soundness gate: nothing is reported that does not pass
/// `verify_all_constraints` with an exactly-recomputed objective.
fn try_record_incumbent(
    instance: &PbInstance,
    objective: &PbObjective,
    assignment: &[bool],
    best: &mut Option<NlcResult>,
    on_improve: &mut dyn FnMut(i128, &[bool]),
    stop: &dyn Fn() -> bool,
) {
    if stop() {
        return;
    }
    if !verify_all_constraints(&instance.constraints, assignment) {
        return;
    }
    let objective_value = eval_objective(objective, assignment);
    let is_improvement = match best {
        Some(current) => objective_value < current.objective,
        None => true,
    };
    if !is_improvement {
        return;
    }
    let assignment_vec = assignment.to_vec();
    on_improve(objective_value, &assignment_vec);
    *best = Some(NlcResult {
        assignment: assignment_vec,
        objective: objective_value,
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::eval_constraint;
    use crate::types::{PbConstraint, PbLit, PbTerm};

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn neg(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn prod(coeff: i128, lits: Vec<PbLit>) -> PbTerm {
        PbTerm { coeff, lits }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    fn no_stop() -> impl Fn() -> bool {
        || false
    }

    /// From-scratch LHS of a constraint, matching `eval_constraint`'s exact term
    /// semantics (products via all-literals-true), used as the differential
    /// oracle for the incremental tracker.
    fn scratch_lhs(c: &PbConstraint, assignment: &[bool]) -> i128 {
        let mut lhs = 0i128;
        for term in &c.terms {
            let all_true = term.lits.iter().all(|l| {
                let v = (l.var as usize)
                    .checked_sub(1)
                    .and_then(|i| assignment.get(i))
                    .copied()
                    .unwrap_or(false);
                if l.negated {
                    !v
                } else {
                    v
                }
            });
            if all_true {
                lhs += term.coeff;
            }
        }
        lhs
    }

    fn scratch_objective(obj: &PbObjective, assignment: &[bool]) -> i128 {
        eval_objective(obj, assignment)
    }

    fn scratch_num_violated(constraints: &[PbConstraint], assignment: &[bool]) -> usize {
        constraints
            .iter()
            .filter(|c| !eval_constraint(c, assignment))
            .count()
    }

    /// Builds a random instance WITH product terms, negated literals, Ge and Eq
    /// rows, plus a product objective.
    fn random_product_instance(rng: &mut SplitMix64) -> (PbInstance, PbObjective) {
        let num_vars = 3 + rng.below(8) as u32;
        let mut constraints = Vec::new();
        let rows = 2 + rng.below(6);
        for _ in 0..rows {
            let term_count = 1 + rng.below(4);
            let mut terms = Vec::new();
            for _ in 0..term_count {
                let arity = 1 + rng.below(3);
                let mut lits = Vec::new();
                for _ in 0..arity {
                    let v = 1 + rng.below(num_vars as usize) as u32;
                    if rng.below(2) == 0 {
                        lits.push(lit(v));
                    } else {
                        lits.push(neg(v));
                    }
                }
                let coeff = (rng.below(7) as i128) - 3; // in [-3, 3]
                terms.push(prod(coeff, lits));
            }
            let rhs = (rng.below(5) as i128) - 2; // in [-2, 2]
            if rng.below(3) == 0 {
                constraints.push(eq(terms, rhs));
            } else {
                constraints.push(ge(terms, rhs));
            }
        }
        // Product objective (some single-literal, some products, some negated).
        let mut obj_terms = Vec::new();
        let obj_count = 1 + rng.below(5);
        for _ in 0..obj_count {
            let arity = 1 + rng.below(3);
            let mut lits = Vec::new();
            for _ in 0..arity {
                let v = 1 + rng.below(num_vars as usize) as u32;
                if rng.below(2) == 0 {
                    lits.push(lit(v));
                } else {
                    lits.push(neg(v));
                }
            }
            let coeff = (rng.below(9) as i128) - 4; // in [-4, 4]
            obj_terms.push(prod(coeff, lits));
        }
        let objective = PbObjective { terms: obj_terms };
        let instance = PbInstance {
            num_vars,
            num_constraints: constraints.len() as u32,
            constraints,
            objective: Some(objective.clone()),
        };
        (instance, objective)
    }

    /// SELF-CHECK of the advisory scorer: after every flip on random
    /// product/negated/Eq instances, the incremental LHS/violation/objective must
    /// equal a from-scratch recompute (the soundness-of-the-scorer differential
    /// fuzz). This is what guarantees the steering signal is exact; the reported
    /// incumbent is independently re-verified regardless.
    #[test]
    fn product_tracker_incremental_matches_scratch_fuzz() {
        let mut rng = SplitMix64::new(0xD1FF_FACE_1234_5678);
        for _ in 0..200 {
            let (instance, objective) = random_product_instance(&mut rng);
            let num_vars = instance.num_vars as usize;
            let mut assignment = vec![false; num_vars];
            // Randomize the start so we exercise non-trivial false_counts.
            for a in assignment.iter_mut() {
                *a = rng.below(2) == 0;
            }
            let mut tracker =
                ProductTracker::new(&instance, &objective, num_vars, &assignment).unwrap();
            let mut scratch = FlipScratch::new(
                tracker.terms.len(),
                tracker.obj_terms.len(),
                tracker.states.len(),
            );

            // Verify the initial build matches scratch.
            check_against_scratch(&tracker, &instance, &objective, &assignment);

            for _ in 0..60 {
                let var = rng.below(num_vars);
                let new_value = !assignment[var];

                // Look-ahead deltas must match the realized change.
                let predicted_viol_delta =
                    tracker.flip_violation_delta_for(var, new_value, &mut scratch);
                let predicted_obj_delta =
                    tracker.flip_objective_delta(var, new_value, &mut scratch);
                let predicted_preserves =
                    tracker.flip_preserves_feasibility(var, new_value, &mut scratch);

                let viol_before = tracker.weighted_violation();
                let obj_before = tracker.objective_value();

                assignment[var] = new_value;
                tracker.apply_flip(var, new_value);

                let viol_after = tracker.weighted_violation();
                let obj_after = tracker.objective_value();

                assert_eq!(
                    viol_after - viol_before,
                    predicted_viol_delta,
                    "violation-delta look-ahead mismatch"
                );
                assert_eq!(
                    obj_after - obj_before,
                    predicted_obj_delta,
                    "objective-delta look-ahead mismatch"
                );
                // `flip_preserves_feasibility(var)` is defined under the
                // precondition that the CURRENT state is feasible (its only call
                // sites). Under that precondition the post-flip state is feasible
                // iff every touched constraint stays satisfied; validate that
                // against a full from-scratch feasibility recompute. (`viol_before`
                // is the weighted violation BEFORE the flip; 0 ⇔ feasible.)
                if viol_before == 0 {
                    let now_feasible = verify_all_constraints(&instance.constraints, &assignment);
                    assert_eq!(
                        predicted_preserves, now_feasible,
                        "flip_preserves_feasibility disagreed with scratch feasibility"
                    );
                }

                check_against_scratch(&tracker, &instance, &objective, &assignment);
            }
        }
    }

    fn check_against_scratch(
        tracker: &ProductTracker,
        instance: &PbInstance,
        objective: &PbObjective,
        assignment: &[bool],
    ) {
        for (c, constraint) in instance.constraints.iter().enumerate() {
            assert_eq!(
                tracker.constraint_lhs(c),
                scratch_lhs(constraint, assignment),
                "incremental LHS != scratch LHS for constraint {c}"
            );
        }
        assert_eq!(
            tracker.objective_value(),
            scratch_objective(objective, assignment),
            "incremental objective != scratch objective"
        );
        assert_eq!(
            tracker.unweighted_num_violated(),
            scratch_num_violated(&instance.constraints, assignment),
            "incremental violated-count != scratch"
        );
        // The maintained violated-set must list exactly the violated constraints.
        let listed: std::collections::BTreeSet<usize> =
            tracker.violated_list.iter().copied().collect();
        let expected: std::collections::BTreeSet<usize> = instance
            .constraints
            .iter()
            .enumerate()
            .filter(|(_, c)| !eval_constraint(c, assignment))
            .map(|(i, _)| i)
            .collect();
        assert_eq!(listed, expected, "violated-set membership mismatch");
    }

    /// End-to-end: a product constraint that the all-false start violates must be
    /// repaired, and a product objective driven down — with every reported
    /// incumbent verified.
    #[test]
    fn product_sls_finds_and_improves_feasible() {
        // Constraint: x1 x2 + x3 >= 1  (all-false violates it).
        // Objective:  min -2 x1 x2 - x3  (reward making the product true).
        let constraints = vec![ge(
            vec![prod(1, vec![lit(1), lit(2)]), prod(1, vec![lit(3)])],
            1,
        )];
        let objective = PbObjective {
            terms: vec![prod(-2, vec![lit(1), lit(2)]), prod(-1, vec![lit(3)])],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints,
            objective: Some(objective.clone()),
        };
        let stop = no_stop();
        let mut reported = Vec::new();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
            reported.push(obj);
        };
        let result = search(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(400)),
            &stop,
            &mut on_improve,
        )
        .expect("should find a feasible incumbent");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &result.assignment),
            result.objective
        );
        // Optimum is x1=x2=x3=true: objective -3. Should reach it (small).
        assert_eq!(result.objective, -3);
        for window in reported.windows(2) {
            assert!(
                window[1] < window[0],
                "reported values must strictly improve"
            );
        }
    }

    /// Negated literals + Eq row: ~x1 ~x2 = 1 means both x1,x2 false. Objective
    /// min x3. SLS must satisfy the product-Eq and only report verified points.
    #[test]
    fn product_sls_handles_negated_and_eq() {
        let constraints = vec![eq(vec![prod(1, vec![neg(1), neg(2)])], 1)];
        let objective = PbObjective {
            terms: vec![prod(1, vec![lit(3)])],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints,
            objective: Some(objective.clone()),
        };
        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(400)),
            &stop,
            &mut on_improve,
        )
        .expect("should satisfy the negated product Eq");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        // ~x1 ~x2 = 1 forces x1=x2=false; x3 free, minimized to false -> obj 0.
        assert_eq!(result.objective, 0);
        assert!(!result.assignment[0] && !result.assignment[1]);
    }

    /// The seed-XOR diversifier (the parallel `nlc-sls-opt` worker's knob)
    /// only changes the TRAJECTORY: a nonzero xor still satisfies the
    /// instance and every reported incumbent stays verified and exactly
    /// valued — the same invariants as the unXORed search.
    #[test]
    fn product_sls_seed_xor_diversified_run_stays_sound() {
        let constraints = vec![eq(vec![prod(1, vec![neg(1), neg(2)])], 1)];
        let objective = PbObjective {
            terms: vec![prod(1, vec![lit(3)])],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints,
            objective: Some(objective.clone()),
        };
        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search_with_seed_xor(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(400)),
            &stop,
            &mut on_improve,
            0x27A9_F1D8_5EED_000E,
        )
        .expect("diversified run should still satisfy the product Eq");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(result.objective, 0);
    }

    /// The intensifying trajectory (`intensify_from_best`, the `nlc-sls-focused-opt`
    /// worker's knob) re-anchors the stuck-point kick on the best incumbent. It
    /// stays SOUND — every reported point is feasible and exactly valued, values
    /// strictly improve — and still reaches the optimum on this small shape.
    #[test]
    fn product_sls_intensify_from_best_stays_sound() {
        // Constraint: x1 x2 + x3 >= 1  (all-false violates it).
        // Objective:  min -2 x1 x2 - x3.  Optimum x1=x2=x3=true -> -3.
        let constraints = vec![ge(
            vec![prod(1, vec![lit(1), lit(2)]), prod(1, vec![lit(3)])],
            1,
        )];
        let objective = PbObjective {
            terms: vec![prod(-2, vec![lit(1), lit(2)]), prod(-1, vec![lit(3)])],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints,
            objective: Some(objective.clone()),
        };
        let stop = no_stop();
        let mut prev: Option<i128> = None;
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert!(verify_all_constraints(&instance.constraints, model));
            assert_eq!(eval_objective(&objective, model), obj);
            if let Some(p) = prev {
                assert!(obj < p, "reported values must strictly improve");
            }
            prev = Some(obj);
        };
        let result = search_with_options(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(400)),
            &stop,
            &mut on_improve,
            NlcSearchOptions {
                seed_xor: 0x1357_9BDF_2468_ACE0,
                intensify_from_best: true,
            },
        )
        .expect("intensifying run should find a feasible incumbent");
        assert!(verify_all_constraints(
            &instance.constraints,
            &result.assignment
        ));
        assert_eq!(
            eval_objective(&objective, &result.assignment),
            result.objective
        );
        assert_eq!(result.objective, -3);
    }

    /// Across many random product/negated/Eq instances, the intensifying trajectory
    /// (`intensify_from_best`) must — exactly like the default — never report an
    /// infeasible or mis-valued incumbent, and reported values must strictly
    /// improve. Guards the `reseat_to` re-anchor path against soundness slips.
    #[test]
    fn product_sls_intensify_never_reports_bad_incumbent_fuzz() {
        let mut rng = SplitMix64::new(0x00DE_C0DE_1234_5678);
        for _ in 0..40 {
            let (instance, objective) = random_product_instance(&mut rng);
            let stop = no_stop();
            let mut violations = 0usize;
            let mut prev: Option<i128> = None;
            let mut on_improve = |obj: i128, model: &[bool]| {
                if !verify_all_constraints(&instance.constraints, model) {
                    violations += 1;
                }
                if eval_objective(&objective, model) != obj {
                    violations += 1;
                }
                if let Some(p) = prev {
                    if obj >= p {
                        violations += 1;
                    }
                }
                prev = Some(obj);
            };
            let result = search_with_options(
                &instance,
                &objective,
                Some(std::time::Instant::now() + std::time::Duration::from_millis(40)),
                &stop,
                &mut on_improve,
                NlcSearchOptions {
                    seed_xor: 0x0A0B_0C0D_0E0F_1011,
                    intensify_from_best: true,
                },
            );
            assert_eq!(violations, 0, "intensifying SLS reported a bad incumbent");
            if let Some(r) = result {
                assert!(verify_all_constraints(&instance.constraints, &r.assignment));
                assert_eq!(eval_objective(&objective, &r.assignment), r.objective);
            }
        }
    }

    /// No-constraint instance (the QPLIB_3877/5881 shape): all-false is feasible;
    /// the search must drive the product objective below zero and report verified
    /// incumbents.
    #[test]
    fn product_sls_unconstrained_descent() {
        let objective = PbObjective {
            terms: vec![
                prod(-5, vec![lit(1), lit(2)]),
                prod(-3, vec![lit(2), lit(3)]),
                prod(2, vec![lit(1)]),
            ],
        };
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 0,
            constraints: vec![],
            objective: Some(objective.clone()),
        };
        let stop = no_stop();
        let mut on_improve = |obj: i128, model: &[bool]| {
            assert_eq!(eval_objective(&objective, model), obj);
        };
        let result = search(
            &instance,
            &objective,
            Some(std::time::Instant::now() + std::time::Duration::from_millis(400)),
            &stop,
            &mut on_improve,
        )
        .expect("unconstrained -> always feasible");
        assert_eq!(
            eval_objective(&objective, &result.assignment),
            result.objective
        );
        // Best: x1=x2=x3=true -> -5 -3 +2 = -6. Should reach the negative region.
        assert!(result.objective < 0);
    }

    /// Across many random product/negated/Eq instances, every reported incumbent
    /// (and the returned best) must be feasible and exactly valued, and reported
    /// values must strictly improve. The advisory scorer must never cause a bad
    /// incumbent to be emitted.
    #[test]
    fn product_sls_never_reports_bad_incumbent_fuzz() {
        let mut rng = SplitMix64::new(0x0FEE_1DEA_DBEE_F001);
        for _ in 0..40 {
            let (instance, objective) = random_product_instance(&mut rng);
            let stop = no_stop();
            let mut violations = 0usize;
            let mut prev: Option<i128> = None;
            let mut on_improve = |obj: i128, model: &[bool]| {
                if !verify_all_constraints(&instance.constraints, model) {
                    violations += 1;
                }
                if eval_objective(&objective, model) != obj {
                    violations += 1;
                }
                if let Some(p) = prev {
                    if obj >= p {
                        violations += 1;
                    }
                }
                prev = Some(obj);
            };
            let result = search(
                &instance,
                &objective,
                Some(std::time::Instant::now() + std::time::Duration::from_millis(40)),
                &stop,
                &mut on_improve,
            );
            assert_eq!(violations, 0, "product SLS reported a bad incumbent");
            if let Some(r) = result {
                assert!(verify_all_constraints(&instance.constraints, &r.assignment));
                assert_eq!(eval_objective(&objective, &r.assignment), r.objective);
            }
        }
    }

    #[test]
    fn product_sls_respects_should_stop() {
        let objective = PbObjective {
            terms: vec![prod(-1, vec![lit(1), lit(2)])],
        };
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 0,
            constraints: vec![],
            objective: Some(objective.clone()),
        };
        let stop = || true;
        let mut called = false;
        let mut on_improve = |_obj: i128, _model: &[bool]| called = true;
        let result = search(&instance, &objective, None, &stop, &mut on_improve);
        assert!(result.is_none());
        assert!(!called);
    }
}
