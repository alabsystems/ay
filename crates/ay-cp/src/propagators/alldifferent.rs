// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// This file implements the bounds-consistency AllDifferent algorithm of
// Lopez-Ortiz, Quimper, Tromp, and van Beek ("A fast and simple algorithm for
// bounds consistency of the alldifferent constraint", IJCAI 2003). The
// implementation is derived from Choco-solver's `AlgoAllDiffBC.java`, which is
// distributed under the BSD 4-Clause license by IMT Atlantique. As required by
// that license, its notice is reproduced here:
//
// ---------------------------------------------------------------------------
// Copyright (c) 1999-2026, IMT Atlantique (the choco-solver project)
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//   1. Redistributions of source code must retain the above copyright notice,
//      this list of conditions and the following disclaimer.
//   2. Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimer in the
//      documentation and/or other materials provided with the distribution.
//   3. All advertising materials mentioning features or use of this software
//      must display the following acknowledgement: This product includes
//      software developed by IMT Atlantique and the choco-solver project.
//   4. Neither the name of the copyright holder nor the names of its
//      contributors may be used to endorse or promote products derived from
//      this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.
// ---------------------------------------------------------------------------

//! AllDifferent constraint propagator.
//!
//! Implements bounds-consistent propagation for the all-different constraint:
//! all variables must take distinct values.
//!
//! # Algorithm
//!
//! Uses the O(n log n) bounds-consistency algorithm from:
//! - Lopez-Ortiz, Quimper, Tromp, van Beek. "A fast and simple algorithm for
//!   bounds consistency of the alldifferent constraint" (IJCAI 2003)
//!
//! Ported from Choco-solver's AlgoAllDiffBC.java (BSD 4-clause license,
//! IMT Atlantique). The algorithm uses a union-find structure with path
//! compression to detect Hall intervals in O(n) per sweep after O(n log n)
//! sorting.
//!
//! Two sweeps per propagation:
//! - `filter_lower`: processes variables by ascending ub, propagates lb raises
//! - `filter_upper`: processes variables by descending lb, propagates ub reductions
//!
//! # Explanation
//!
//! When propagating `x >= v` because variables {y1, ..., yk} form a Hall
//! interval [a, b] with b < v, the explanation is:
//!   `[y1 >= a] ∧ [y1 <= b] ∧ ... ∧ [yk >= a] ∧ [yk <= b] ∧ [x >= x.lb] → [x >= v]`

use ay_sat::Literal;

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// AllDifferent bounds-consistency propagator using the O(n log n) Lopez-Ortiz
/// algorithm with union-find path compression.
#[derive(Debug)]
pub struct AllDifferentBounds {
    vars: Vec<IntVarId>,
    // Per-variable workspace
    ws_lb: Vec<i64>,
    ws_ub_excl: Vec<i64>, // ub + 1 (half-open, matching Choco convention)
    ws_minrank: Vec<usize>,
    ws_maxrank: Vec<usize>,
    ws_minsorted: Vec<usize>,
    ws_maxsorted: Vec<usize>,
    // Per-bounds workspace (capacity: 2*n + 2)
    ws_bounds: Vec<i64>,
    ws_t: Vec<usize>, // tree / union-find parent
    ws_d: Vec<i64>,   // capacity diffs
    ws_h: Vec<usize>, // Hall interval links
    nb_bounds: usize,
}

impl AllDifferentBounds {
    pub fn new(vars: Vec<IntVarId>) -> Self {
        assert!(vars.len() >= 2, "alldiff needs at least 2 variables");
        let n = vars.len();
        let cap = 2 * n + 2;
        Self {
            vars,
            ws_lb: vec![0; n],
            ws_ub_excl: vec![0; n],
            ws_minrank: vec![0; n],
            ws_maxrank: vec![0; n],
            ws_minsorted: (0..n).collect(),
            ws_maxsorted: (0..n).collect(),
            ws_bounds: vec![0; cap],
            ws_t: vec![0; cap],
            ws_d: vec![0; cap],
            ws_h: vec![0; cap],
            nb_bounds: 0,
        }
    }

    /// Build the sorted bounds array and compute per-variable ranks.
    ///
    /// Creates a merged sorted array of all distinct lb and ub+1 values,
    /// then assigns each variable's `minrank` (position of its lb in bounds)
    /// and `maxrank` (position of its ub+1 in bounds).
    fn sort_it(&mut self, trail: &IntegerTrail) {
        let n = self.vars.len();

        // Read current bounds from trail
        for i in 0..n {
            let var = self.vars[i];
            self.ws_lb[i] = trail.lb(var);
            self.ws_ub_excl[i] = trail.ub(var) + 1; // half-open
        }

        // Reset sort indices
        for i in 0..n {
            self.ws_minsorted[i] = i;
            self.ws_maxsorted[i] = i;
        }

        // Sort by lb and ub respectively
        self.ws_minsorted.sort_unstable_by_key(|&i| self.ws_lb[i]);
        self.ws_maxsorted
            .sort_unstable_by_key(|&i| self.ws_ub_excl[i]);

        // Merge lb and ub+1 values into sorted bounds array (like merge step of merge sort)
        let min_lb = self.ws_lb[self.ws_minsorted[0]];
        let mut last = min_lb - 2;
        let mut nb = 0usize;
        self.ws_bounds[0] = last;

        let mut i = 0usize;
        let mut j = 0usize;
        loop {
            if i < n && self.ws_lb[self.ws_minsorted[i]] <= self.ws_ub_excl[self.ws_maxsorted[j]] {
                let val = self.ws_lb[self.ws_minsorted[i]];
                if val != last {
                    nb += 1;
                    self.ws_bounds[nb] = val;
                    last = val;
                }
                self.ws_minrank[self.ws_minsorted[i]] = nb;
                i += 1;
            } else {
                let val = self.ws_ub_excl[self.ws_maxsorted[j]];
                if val != last {
                    nb += 1;
                    self.ws_bounds[nb] = val;
                    last = val;
                }
                self.ws_maxrank[self.ws_maxsorted[j]] = nb;
                j += 1;
                if j == n {
                    break;
                }
            }
        }

        self.nb_bounds = nb;
        self.ws_bounds[nb + 1] = self.ws_bounds[nb] + 2;
    }

    /// Follow parent pointers upward until reaching a root (where t[i] <= i).
    #[inline]
    fn pathmax(t: &[usize], mut i: usize) -> usize {
        while t[i] > i {
            i = t[i];
        }
        i
    }

    /// Follow parent pointers downward until reaching a root (where t[i] >= i).
    #[inline]
    fn pathmin(t: &[usize], mut i: usize) -> usize {
        while t[i] < i {
            i = t[i];
        }
        i
    }

    /// Path compression: set all nodes from `start` to `end` to point to `to`.
    #[inline]
    fn pathset(t: &mut [usize], mut cur: usize, end: usize, to: usize) {
        while cur != end {
            let next = t[cur];
            t[cur] = to;
            cur = next;
        }
    }

    /// FilterLower: detect Hall intervals and propagate lower bound raises.
    ///
    /// Processes variables in ascending ub order. For each variable, "consumes"
    /// one capacity slot at its lower bound position. When capacity reaches zero,
    /// the interval is full → union-find merge. Hall intervals discovered this
    /// way force lower bound raises on variables whose lb falls inside the Hall
    /// interval.
    fn filter_lower(&mut self, encoder: &IntegerEncoder) -> PropagationResult {
        let nb = self.nb_bounds;
        let n = self.vars.len();

        // Initialize for the lower-bound sweep
        for i in 1..=nb + 1 {
            self.ws_t[i] = i - 1;
            self.ws_h[i] = i - 1;
            self.ws_d[i] = self.ws_bounds[i] - self.ws_bounds[i - 1];
        }
        // Sentinel: h[0] = 0 ensures pathmax(h, 0) = 0
        self.ws_h[0] = 0;

        let mut clauses = Vec::new();

        // Process variables in ascending ub order
        for idx in 0..n {
            let var_idx = self.ws_maxsorted[idx];
            let minrank = self.ws_minrank[var_idx];
            let maxrank = self.ws_maxrank[var_idx];

            let mut z = Self::pathmax(&self.ws_t, minrank + 1);
            let j = self.ws_t[z];

            self.ws_d[z] -= 1;

            if self.ws_d[z] == 0 {
                self.ws_t[z] = z + 1;
                z = Self::pathmax(&self.ws_t, z + 1);
                self.ws_t[z] = j;
            }

            Self::pathset(&mut self.ws_t, minrank + 1, z, z);

            // Conflict: more variables than available values
            if self.ws_d[z] < self.ws_bounds[z] - self.ws_bounds[maxrank] {
                if let Some(clause) = self.explain_conflict(encoder) {
                    return PropagationResult::Conflict(clause);
                }
                return PropagationResult::NoChange;
            }

            // Propagate: raise lb if a Hall interval forces it
            if self.ws_h[minrank] > minrank {
                let w = Self::pathmax(&self.ws_h, self.ws_h[minrank]);
                let hall_max = self.ws_bounds[w];
                let current_lb = self.ws_lb[var_idx];

                if hall_max > current_lb {
                    if let Some(clause) = self.explain_lower_prop(var_idx, hall_max, w, encoder) {
                        clauses.push(clause);
                    }
                }

                Self::pathset(&mut self.ws_h, minrank, w, w);
            }

            // Mark new Hall interval
            if self.ws_d[z] == self.ws_bounds[z] - self.ws_bounds[maxrank] {
                let target = j - 1; // safe: j >= 1 proven by algorithm invariant
                let start = self.ws_h[maxrank];
                Self::pathset(&mut self.ws_h, start, target, maxrank);
                self.ws_h[maxrank] = target;
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    /// FilterUpper: detect Hall intervals and propagate upper bound reductions.
    ///
    /// Symmetric to filter_lower. Processes variables in descending lb order.
    fn filter_upper(&mut self, encoder: &IntegerEncoder) -> PropagationResult {
        let nb = self.nb_bounds;
        let n = self.vars.len();

        // Initialize for the upper-bound sweep
        for i in 0..=nb {
            self.ws_t[i] = i + 1;
            self.ws_h[i] = i + 1;
            self.ws_d[i] = self.ws_bounds[i + 1] - self.ws_bounds[i];
        }
        // Sentinel: h[nb+1] = nb+1 ensures pathmin(h, nb+1) = nb+1
        self.ws_h[nb + 1] = nb + 1;

        let mut clauses = Vec::new();

        // Process variables in descending lb order
        for idx in (0..n).rev() {
            let var_idx = self.ws_minsorted[idx];
            let maxrank = self.ws_maxrank[var_idx];
            let minrank = self.ws_minrank[var_idx];

            let mut z = Self::pathmin(&self.ws_t, maxrank - 1);
            let j = self.ws_t[z];
            self.ws_d[z] -= 1;

            if self.ws_d[z] == 0 {
                self.ws_t[z] = z - 1;
                z = Self::pathmin(&self.ws_t, z - 1);
                self.ws_t[z] = j;
            }

            Self::pathset(&mut self.ws_t, maxrank - 1, z, z);

            // Conflict: more variables than available values
            if self.ws_d[z] < self.ws_bounds[minrank] - self.ws_bounds[z] {
                if let Some(clause) = self.explain_conflict(encoder) {
                    return PropagationResult::Conflict(clause);
                }
                return PropagationResult::NoChange;
            }

            // Propagate: reduce ub if a Hall interval forces it
            if self.ws_h[maxrank] < maxrank {
                let w = Self::pathmin(&self.ws_h, self.ws_h[maxrank]);
                let hall_min = self.ws_bounds[w];
                let current_ub_excl = self.ws_ub_excl[var_idx];

                if hall_min < current_ub_excl {
                    if let Some(clause) = self.explain_upper_prop(var_idx, hall_min, w, encoder) {
                        clauses.push(clause);
                    }
                }

                Self::pathset(&mut self.ws_h, maxrank, w, w);
            }

            // Mark new Hall interval
            if self.ws_d[z] == self.ws_bounds[minrank] - self.ws_bounds[z] {
                let target = j + 1;
                let start = self.ws_h[minrank];
                Self::pathset(&mut self.ws_h, start, target, minrank);
                self.ws_h[minrank] = target;
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    /// Generate a conflict explanation: all variables' bounds are contradictory.
    ///
    /// Over-approximate but always sound — the CDCL solver will minimize via
    /// conflict analysis. The union-find bucket chains don't reliably contain
    /// the complete conflict set after merging.
    fn explain_conflict(&self, encoder: &IntegerEncoder) -> Option<Vec<Literal>> {
        let mut reasons = Vec::new();
        for (i, &var) in self.vars.iter().enumerate() {
            reasons.push(encoder.lookup_ge(var, self.ws_lb[i])?);
            reasons.push(encoder.lookup_le(var, self.ws_ub_excl[i] - 1)?);
        }
        Some(Explanation::new(reasons).into_conflict_clause())
    }

    /// Generate explanation for a lower bound raise.
    ///
    /// Hall set identification: variables (other than the propagated one) with
    /// `ub_excl <= hall_max` are "trapped" inside the Hall interval — their
    /// bounds form a sufficient reason for the lb raise. This is tighter than
    /// all-variables (O(k) vs O(n) reasons) while remaining sound: including
    /// extra variables only weakens the clause. The outsider's current lb is
    /// also required for soundness after CDCL backtracking (#5986).
    fn explain_lower_prop(
        &self,
        var_idx: usize,
        hall_max: i64,
        _w: usize,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<Literal>> {
        let var = self.vars[var_idx];
        let conclusion = encoder.lookup_ge(var, hall_max)?;
        let mut reasons = Vec::new();
        for (i, &v) in self.vars.iter().enumerate() {
            if i == var_idx {
                continue;
            }
            if self.ws_ub_excl[i] <= hall_max {
                reasons.push(encoder.lookup_ge(v, self.ws_lb[i])?);
                reasons.push(encoder.lookup_le(v, self.ws_ub_excl[i] - 1)?);
            }
        }
        // Outsider's current lb: soundness after backtracking (#5986).
        reasons.push(encoder.lookup_ge(var, self.ws_lb[var_idx])?);
        Some(Explanation::new(reasons).into_clause(conclusion))
    }

    /// Generate explanation for an upper bound reduction.
    ///
    /// Symmetric to explain_lower_prop. Hall set: variables with `lb >= hall_min`.
    fn explain_upper_prop(
        &self,
        var_idx: usize,
        hall_min: i64,
        _w: usize,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<Literal>> {
        let var = self.vars[var_idx];
        let conclusion = encoder.lookup_le(var, hall_min - 1)?;
        let mut reasons = Vec::new();
        for (i, &v) in self.vars.iter().enumerate() {
            if i == var_idx {
                continue;
            }
            if self.ws_lb[i] >= hall_min {
                reasons.push(encoder.lookup_ge(v, self.ws_lb[i])?);
                reasons.push(encoder.lookup_le(v, self.ws_ub_excl[i] - 1)?);
            }
        }
        // Outsider's current ub: soundness after backtracking (#5986).
        reasons.push(encoder.lookup_le(var, self.ws_ub_excl[var_idx] - 1)?);
        Some(Explanation::new(reasons).into_clause(conclusion))
    }
}

impl Propagator for AllDifferentBounds {
    fn variables(&self) -> &[IntVarId] {
        &self.vars
    }

    fn priority(&self) -> PropagatorPriority {
        // O(n log n) bounds-consistency via Lopez-Ortiz union-find sweep.
        // Much cheaper than AC's O(n·d) matching + SCC.
        PropagatorPriority::Linear
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        self.sort_it(trail);

        // Run both sweeps on the same bound snapshot. Each produces clauses
        // independently; the SAT solver processes them and re-invokes the
        // propagator if any bounds change.
        let lower = self.filter_lower(encoder);
        if matches!(lower, PropagationResult::Conflict(_)) {
            return lower;
        }
        let upper = self.filter_upper(encoder);
        if matches!(upper, PropagationResult::Conflict(_)) {
            return upper;
        }

        match (lower, upper) {
            (PropagationResult::Propagated(mut lc), PropagationResult::Propagated(uc)) => {
                lc.extend(uc);
                PropagationResult::Propagated(lc)
            }
            (PropagationResult::Propagated(c), _) | (_, PropagationResult::Propagated(c)) => {
                PropagationResult::Propagated(c)
            }
            _ => PropagationResult::NoChange,
        }
    }

    fn name(&self) -> &'static str {
        "alldifferent_bounds"
    }
}

#[cfg(test)]
#[path = "alldifferent_tests.rs"]
mod tests;
