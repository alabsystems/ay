// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA diving heuristic: SAT-only witness search from the LP point.
//!
//! Split out of `lia_support.rs` to keep both files under the quality
//! gate's line budget. The cube test and rounding helpers stay there.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermId;
use ay_core::{TheoryResult, TheorySolver};

use crate::rational::Rational;
use crate::{BoundType, LraSolver};

impl LraSolver {
    /// Diving heuristic (#split-walk-sat-fallback, LIA dive lane): starting
    /// from the current LP point, dive toward an integer point — fix one
    /// fractional integer variable to an integer (both bounds), re-solve the
    /// LP, and repeat until every integer variable is integral.
    ///
    /// The dive backtracks: each fixing is a binary choice (nearest integer
    /// first, the other neighbour on failure) explored depth-first under a
    /// total LP-solve budget (`max_nodes`), each choice in its own `push`
    /// scope. A re-solve that is not `Sat` (infeasible, or `Unknown` because
    /// a conflict would need the reason-free fixing bounds) fails the choice
    /// point. The whole search runs inside one outer scope: on success the
    /// integral point is read out as `(term, value)` pairs and every scope
    /// is popped, so the solver state is exactly as before the call either
    /// way. The fixing bounds carry no reason literals (multi-reason "axiom"
    /// form, as the cube test intended): they never escape their scope, and
    /// a conflict produced under them is discarded with the pop.
    ///
    /// Returns `None` when the budget is exhausted, when every explored
    /// path fails, or when some integer variable has no tableau column / no
    /// integral read-out. This is a SAT-only witness search: `None` carries
    /// no verdict.
    ///
    /// Variable choice is deterministic: smallest distance to the nearest
    /// integer, ties broken by the smaller `TermId`.
    pub fn try_integer_dive(
        &mut self,
        integer_vars: &HashSet<TermId>,
        max_nodes: usize,
    ) -> Option<Vec<(TermId, num_bigint::BigInt)>> {
        self.try_integer_dive_prefixed(integer_vars, &[], max_nodes)
    }

    /// As [`Self::try_integer_dive`], but with variables pre-fixed to
    /// integer values before the search (each in the dive's outer
    /// scope, so no state escapes). The LIA dive-repair loop uses
    /// this to steer a re-dive off an asserted disequality the
    /// previous witness violated — disequalities are invisible to
    /// the LP, so an unsteered dive can land exactly on one
    /// (#lia-dive-repair). A pre-fixed variable without a tableau
    /// column, or an LP made infeasible by the fixings, declines
    /// the whole dive.
    pub fn try_integer_dive_prefixed(
        &mut self,
        integer_vars: &HashSet<TermId>,
        prefixed: &[(TermId, num_bigint::BigInt)],
        max_nodes: usize,
    ) -> Option<Vec<(TermId, num_bigint::BigInt)>> {
        if integer_vars.is_empty() || max_nodes == 0 {
            return None;
        }
        let mut ordered: Vec<TermId> = integer_vars.iter().copied().collect();
        ordered.sort_by_key(|t| t.0);
        // Fail closed up front when some integer variable cannot be read
        // out of the tableau: its value would be missing from the witness.
        if ordered.iter().any(|t| !self.term_to_var.contains_key(t)) {
            return None;
        }

        self.push();
        let mut nodes_left = max_nodes;
        let mut fixed: Vec<TermId> = Vec::new();
        let outcome = self
            .apply_prefixed(prefixed, &mut fixed, &mut nodes_left)
            .and_then(|()| self.dive_search(&ordered, &mut fixed, &mut nodes_left));
        self.pop();
        outcome
    }

    /// Assert the pre-fixings inside the dive's outer scope and
    /// re-solve once; `None` declines the dive.
    fn apply_prefixed(
        &mut self,
        prefixed: &[(TermId, num_bigint::BigInt)],
        fixed: &mut Vec<TermId>,
        nodes_left: &mut usize,
    ) -> Option<()> {
        if prefixed.is_empty() {
            return Some(());
        }
        if *nodes_left == 0 {
            return None;
        }
        *nodes_left -= 1;
        for &(term, ref value) in prefixed {
            let var = *self.term_to_var.get(&term)?;
            let rounded = Rational::from(value.clone());
            self.assert_var_bound_with_reasons(
                var,
                rounded.clone(),
                BoundType::Lower,
                false,
                &[],
                &[],
            );
            self.assert_var_bound_with_reasons(var, rounded, BoundType::Upper, false, &[], &[]);
            fixed.push(term);
        }
        self.dirty = true;
        matches!(self.dual_simplex(), TheoryResult::Sat).then_some(())
    }

    /// One level of the backtracking dive: `fixed` holds the variables
    /// already fixed on the current path (each under one more `push` scope
    /// than its parent, all still open). Each level pops its own choice
    /// scope before returning — on success the witness has already been
    /// copied out of the tableau, so no scope needs to outlive its level.
    fn dive_search(
        &mut self,
        ordered: &[TermId],
        fixed: &mut Vec<TermId>,
        nodes_left: &mut usize,
    ) -> Option<Vec<(TermId, num_bigint::BigInt)>> {
        // Pick the fractional integer variable closest to integral.
        let mut pick: Option<(TermId, u32, Rational, Rational)> = None;
        let mut pick_dist: Option<Rational> = None;
        for &term in ordered {
            if fixed.contains(&term) {
                continue;
            }
            let var = *self.term_to_var.get(&term)?;
            let info = self.vars.get(var as usize)?;
            let val = info.value.x_rational();
            if val.is_integer() {
                continue;
            }
            let floor_rat = Rational::from(val.floor());
            let ceil_rat = Rational::from(val.ceil());
            let dist_floor = (&val - &floor_rat).abs();
            let dist_ceil = (&ceil_rat - &val).abs();
            let (first, second, dist) = if dist_floor <= dist_ceil {
                (floor_rat, ceil_rat, dist_floor)
            } else {
                (ceil_rat, floor_rat, dist_ceil)
            };
            let better = match &pick_dist {
                None => true,
                Some(d) => dist < *d,
            };
            if better {
                pick = Some((term, var, first, second));
                pick_dist = Some(dist);
            }
        }
        let Some((term, var, first, second)) = pick else {
            // Every integer variable is integral at a feasible LP point.
            let model = self.extract_model();
            let mut witness = Vec::with_capacity(ordered.len());
            for &term in ordered {
                let val = model.values.get(&term)?;
                if !val.is_integer() {
                    return None;
                }
                witness.push((term, val.numer().clone()));
            }
            return Some(witness);
        };

        for rounded in [first, second] {
            if *nodes_left == 0 {
                return None;
            }
            *nodes_left -= 1;
            self.push();
            self.assert_var_bound_with_reasons(
                var,
                rounded.clone(),
                BoundType::Lower,
                false,
                &[],
                &[],
            );
            self.assert_var_bound_with_reasons(var, rounded, BoundType::Upper, false, &[], &[]);
            self.dirty = true;
            let mut found = None;
            if matches!(self.dual_simplex(), TheoryResult::Sat) {
                fixed.push(term);
                found = self.dive_search(ordered, fixed, nodes_left);
                fixed.pop();
            }
            self.pop();
            if found.is_some() {
                return found;
            }
        }
        None
    }
}
