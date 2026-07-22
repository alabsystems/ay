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

//! Shifted AllDifferent propagator: `alldiff(vars[k] + shifts[k])`.
//!
//! Used for diagonal constraints in queens-style problems:
//! `alldiff(q[i] + i)` and `alldiff(q[i] - i)` where shifts encode the
//! column/row offsets. Propagation works in "shifted space" where the
//! Hall interval algorithm applies directly.
//!
//! # Algorithm
//!
//! Uses the O(n log n) bounds-consistency algorithm from:
//! - Lopez-Ortiz, Quimper, Tromp, van Beek. "A fast and simple algorithm for
//!   bounds consistency of the alldifferent constraint" (IJCAI 2003)
//!
//! Same union-find structure as [`AllDifferentBounds`](super::alldifferent::AllDifferentBounds),
//! ported from Choco-solver's AlgoAllDiffBC.java (BSD 4-clause, IMT Atlantique),
//! but operating on shifted bounds:
//!   `shifted_lb[k] = trail.lb(vars[k]) + shifts[k]`
//!   `shifted_ub[k] = trail.ub(vars[k]) + shifts[k]`
//!
//! Explanation literals are converted back to original (unshifted) space.

use ay_sat::Literal;

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// AllDifferent with per-variable shifts: `alldiff(vars[k] + shifts[k])`.
/// Uses O(n log n) Lopez-Ortiz union-find algorithm in shifted space.
#[derive(Debug)]
pub struct ShiftedAllDifferentBounds {
    vars: Vec<IntVarId>,
    shifts: Vec<i64>,
    // Per-variable workspace (shifted-space bounds)
    ws_lb: Vec<i64>,      // shifted lb
    ws_ub_excl: Vec<i64>, // shifted ub + 1 (half-open)
    ws_minrank: Vec<usize>,
    ws_maxrank: Vec<usize>,
    ws_minsorted: Vec<usize>,
    ws_maxsorted: Vec<usize>,
    // Per-bounds workspace (capacity: 2*n + 2)
    ws_bounds: Vec<i64>,
    ws_t: Vec<usize>,
    ws_d: Vec<i64>,
    ws_h: Vec<usize>,
    nb_bounds: usize,
}

impl ShiftedAllDifferentBounds {
    pub fn new(vars: Vec<IntVarId>, shifts: Vec<i64>) -> Self {
        assert_eq!(vars.len(), shifts.len());
        assert!(
            vars.len() >= 2,
            "shifted alldiff needs at least 2 variables"
        );
        let n = vars.len();
        let cap = 2 * n + 2;
        Self {
            vars,
            shifts,
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

    /// Build sorted bounds array and compute per-variable ranks in shifted space.
    fn sort_it(&mut self, trail: &IntegerTrail) {
        let n = self.vars.len();
        for i in 0..n {
            let var = self.vars[i];
            let shift = self.shifts[i];
            self.ws_lb[i] = trail.lb(var) + shift;
            self.ws_ub_excl[i] = trail.ub(var) + shift + 1;
        }
        for i in 0..n {
            self.ws_minsorted[i] = i;
            self.ws_maxsorted[i] = i;
        }
        self.ws_minsorted.sort_unstable_by_key(|&i| self.ws_lb[i]);
        self.ws_maxsorted
            .sort_unstable_by_key(|&i| self.ws_ub_excl[i]);

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

    #[inline]
    fn pathmax(t: &[usize], mut i: usize) -> usize {
        while t[i] > i {
            i = t[i];
        }
        i
    }

    #[inline]
    fn pathmin(t: &[usize], mut i: usize) -> usize {
        while t[i] < i {
            i = t[i];
        }
        i
    }

    #[inline]
    fn pathset(t: &mut [usize], mut cur: usize, end: usize, to: usize) {
        while cur != end {
            let next = t[cur];
            t[cur] = to;
            cur = next;
        }
    }

    /// FilterLower in shifted space: propagate lb raises.
    fn filter_lower(&mut self, encoder: &IntegerEncoder) -> PropagationResult {
        let nb = self.nb_bounds;
        let n = self.vars.len();

        for i in 1..=nb + 1 {
            self.ws_t[i] = i - 1;
            self.ws_h[i] = i - 1;
            self.ws_d[i] = self.ws_bounds[i] - self.ws_bounds[i - 1];
        }
        self.ws_h[0] = 0;

        let mut clauses = Vec::new();

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

            if self.ws_d[z] < self.ws_bounds[z] - self.ws_bounds[maxrank] {
                if let Some(clause) = self.explain_conflict(encoder) {
                    return PropagationResult::Conflict(clause);
                }
                return PropagationResult::NoChange;
            }

            if self.ws_h[minrank] > minrank {
                let w = Self::pathmax(&self.ws_h, self.ws_h[minrank]);
                let hall_max = self.ws_bounds[w]; // shifted space
                let current_slb = self.ws_lb[var_idx];

                if hall_max > current_slb {
                    if let Some(clause) = self.explain_lower_prop(var_idx, hall_max, encoder) {
                        clauses.push(clause);
                    }
                }

                Self::pathset(&mut self.ws_h, minrank, w, w);
            }

            if self.ws_d[z] == self.ws_bounds[z] - self.ws_bounds[maxrank] {
                let target = j - 1;
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

    /// FilterUpper in shifted space: propagate ub reductions.
    fn filter_upper(&mut self, encoder: &IntegerEncoder) -> PropagationResult {
        let nb = self.nb_bounds;
        let n = self.vars.len();

        for i in 0..=nb {
            self.ws_t[i] = i + 1;
            self.ws_h[i] = i + 1;
            self.ws_d[i] = self.ws_bounds[i + 1] - self.ws_bounds[i];
        }
        self.ws_h[nb + 1] = nb + 1;

        let mut clauses = Vec::new();

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

            if self.ws_d[z] < self.ws_bounds[minrank] - self.ws_bounds[z] {
                if let Some(clause) = self.explain_conflict(encoder) {
                    return PropagationResult::Conflict(clause);
                }
                return PropagationResult::NoChange;
            }

            if self.ws_h[maxrank] < maxrank {
                let w = Self::pathmin(&self.ws_h, self.ws_h[maxrank]);
                let hall_min = self.ws_bounds[w]; // shifted space
                let current_sub_excl = self.ws_ub_excl[var_idx];

                if hall_min < current_sub_excl {
                    if let Some(clause) = self.explain_upper_prop(var_idx, hall_min, encoder) {
                        clauses.push(clause);
                    }
                }

                Self::pathset(&mut self.ws_h, maxrank, w, w);
            }

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

    /// Conflict explanation: all variables' shifted bounds are contradictory.
    fn explain_conflict(&self, encoder: &IntegerEncoder) -> Option<Vec<Literal>> {
        let mut reasons = Vec::new();
        for (i, &var) in self.vars.iter().enumerate() {
            let shift = self.shifts[i];
            let orig_lb = self.ws_lb[i] - shift;
            let orig_ub = self.ws_ub_excl[i] - 1 - shift;
            reasons.push(encoder.lookup_ge(var, orig_lb)?);
            reasons.push(encoder.lookup_le(var, orig_ub)?);
        }
        Some(Explanation::new(reasons).into_conflict_clause())
    }

    /// Explanation for lb raise in shifted space. Hall set: variables with
    /// shifted ub_excl <= hall_max. Converts back to original space.
    fn explain_lower_prop(
        &self,
        var_idx: usize,
        hall_max: i64, // shifted space
        encoder: &IntegerEncoder,
    ) -> Option<Vec<Literal>> {
        let var = self.vars[var_idx];
        let shift = self.shifts[var_idx];
        // Conclusion: original lb >= hall_max - shift
        let new_orig_lb = hall_max - shift;
        let conclusion = encoder.lookup_ge(var, new_orig_lb)?;
        let mut reasons = Vec::new();
        for (i, &v) in self.vars.iter().enumerate() {
            if i == var_idx {
                continue;
            }
            if self.ws_ub_excl[i] <= hall_max {
                let s = self.shifts[i];
                reasons.push(encoder.lookup_ge(v, self.ws_lb[i] - s)?);
                reasons.push(encoder.lookup_le(v, self.ws_ub_excl[i] - 1 - s)?);
            }
        }
        // Outsider's current lb (original space)
        let orig_lb = self.ws_lb[var_idx] - shift;
        reasons.push(encoder.lookup_ge(var, orig_lb)?);
        Some(Explanation::new(reasons).into_clause(conclusion))
    }

    /// Explanation for ub reduction in shifted space. Hall set: variables with
    /// shifted lb >= hall_min. Converts back to original space.
    fn explain_upper_prop(
        &self,
        var_idx: usize,
        hall_min: i64, // shifted space
        encoder: &IntegerEncoder,
    ) -> Option<Vec<Literal>> {
        let var = self.vars[var_idx];
        let shift = self.shifts[var_idx];
        // Conclusion: original ub <= hall_min - 1 - shift
        let new_orig_ub = hall_min - 1 - shift;
        let conclusion = encoder.lookup_le(var, new_orig_ub)?;
        let mut reasons = Vec::new();
        for (i, &v) in self.vars.iter().enumerate() {
            if i == var_idx {
                continue;
            }
            if self.ws_lb[i] >= hall_min {
                let s = self.shifts[i];
                reasons.push(encoder.lookup_ge(v, self.ws_lb[i] - s)?);
                reasons.push(encoder.lookup_le(v, self.ws_ub_excl[i] - 1 - s)?);
            }
        }
        // Outsider's current ub (original space)
        let orig_ub = self.ws_ub_excl[var_idx] - 1 - shift;
        reasons.push(encoder.lookup_le(var, orig_ub)?);
        Some(Explanation::new(reasons).into_clause(conclusion))
    }
}

impl Propagator for ShiftedAllDifferentBounds {
    fn variables(&self) -> &[IntVarId] {
        &self.vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Linear
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        self.sort_it(trail);

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
        "shifted_alldifferent_bounds"
    }
}
