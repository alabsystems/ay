// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer-to-SAT encoder using order encoding.
//!
//! Maps integer variable bounds to SAT literals lazily.
//! For variable `x ∈ [lb..ub]`, creates SAT variables representing:
//!   `[x >= lb+1], [x >= lb+2], ..., [x >= ub]`
//!
//! The value of x is the largest v such that `[x >= v]` is true, or lb
//! if no such literal is true.
//!
//! Literals are created lazily: only when a propagator actually needs
//! to reason about a specific bound. This keeps the SAT formula small.
//!
//! The encoder also maintains the ordering clauses:
//!   `[x >= v+1] → [x >= v]`  (encoded as `¬[x >= v+1] ∨ [x >= v]`)
//!
//! These ensure consistency between bounds.
//!
//! # Design Reference
//!
//! OR-Tools CP-SAT `IntegerEncoder` (ortools/sat/integer.h, lines ~200-400)
//! Chuffed `IntVar` (chuffed/vars/int-var.h)

use std::collections::BTreeMap;

use ay_sat::{Literal, Solver as SatSolver, Variable as SatVariable};
use rustc_hash::FxHashMap;

use crate::variable::IntVarId;

/// Maps between integer variable bounds and SAT literals.
#[derive(Debug)]
pub struct IntegerEncoder {
    /// For each (IntVarId, value v), the SAT literal meaning `[x >= v]`.
    /// Only populated for values where a literal has been requested.
    ge_literals: FxHashMap<(IntVarId, i64), Literal>,

    /// Reverse map: SAT variable → (IntVarId, bound value, is_ge).
    /// Used to decode SAT assignments back to integer values.
    sat_to_int: BTreeMap<SatVariable, BoundLiteral>,

    /// For each IntVarId, the initial lower and upper bounds.
    var_bounds: Vec<(i64, i64)>,

    /// Dense lookup table for `[x >= v]` literals, built by `pre_allocate_all()`.
    /// `ge_array[var_id]` contains literals for values `[lb, lb+1, ..., ub+1]`.
    /// When `ub == i64::MAX`, the impossible `ub+1` sentinel is omitted and the
    /// array ends at `ub`.
    /// Index into inner vec: `(value - lb) as usize`.
    /// Empty until `pre_allocate_all()` is called.
    ge_array: Vec<Vec<Literal>>,

    /// Dense reverse map: SAT variable index → BoundLiteral.
    /// Built by `pre_allocate_all()`. `None` for SAT variables that don't
    /// correspond to any integer bound literal.
    decode_array: Vec<Option<BoundLiteral>>,
}

/// What a SAT literal means in terms of integer bounds.
#[derive(Debug, Clone, Copy)]
pub struct BoundLiteral {
    /// The integer variable this literal refers to
    pub var: IntVarId,
    /// The bound value
    pub value: i64,
    /// If true, the positive literal means `x >= value`.
    /// The negative literal means `x < value` (i.e., `x <= value - 1`).
    pub is_ge: bool,
}

impl IntegerEncoder {
    /// Create a new encoder.
    pub fn new() -> Self {
        Self {
            ge_literals: FxHashMap::default(),
            sat_to_int: BTreeMap::new(),
            var_bounds: Vec::new(),
            ge_array: Vec::new(),
            decode_array: Vec::new(),
        }
    }

    /// Register a new integer variable with bounds [lb, ub].
    /// Returns the `IntVarId`.
    pub fn register_var(&mut self, lb: i64, ub: i64) -> IntVarId {
        let id = IntVarId(self.var_bounds.len() as u32);
        self.var_bounds.push((lb, ub));
        id
    }

    /// Get or create the SAT literal for `[x >= value]`.
    ///
    /// If the literal doesn't exist yet, allocates a new SAT variable
    /// and adds the ordering clause `[x >= value] → [x >= value - 1]`
    /// if the literal for `value - 1` also exists.
    pub fn get_or_create_ge(&mut self, sat: &mut SatSolver, var: IntVarId, value: i64) -> Literal {
        let key = (var, value);
        // Consult the dense array FIRST (falls back to the hash map before
        // `pre_allocate_all()` runs). `pre_allocate_all()` clears `ge_literals`
        // after building `ge_array`, so the hash lookup alone would MISS every
        // pre-allocated bound and mint a fresh, unchannelled duplicate SAT
        // variable. Such a duplicate is invisible to the ordering clauses and
        // to propagator explanations (which use `lookup_ge`), silently
        // decoupling callers like `solve_under_assumptions` from the order
        // encoding: assumptions were not enforced in extracted models, and the
        // CP extension livelocked re-emitting the same satisfied conflict
        // clause forever (#LNS rebuild-free assumption solving).
        if let Some(lit) = self.lookup_ge(var, value) {
            return lit;
        }

        let (lb, ub) = self.var_bounds[var.index()];

        // [x >= lb] is always true (tautology) — represent as a fixed true literal
        if value <= lb {
            // We still need a SAT variable, but it's forced true
            let sat_var = sat.new_var();
            let lit = Literal::positive(sat_var);
            // Force it true
            sat.add_clause(vec![lit]);
            self.ge_literals.insert(key, lit);
            self.sat_to_int.insert(
                sat_var,
                BoundLiteral {
                    var,
                    value,
                    is_ge: true,
                },
            );
            return lit;
        }

        // [x >= ub+1] is always false — represent as a forced false literal
        if value > ub {
            let sat_var = sat.new_var();
            let lit = Literal::positive(sat_var);
            // Force it false
            sat.add_clause(vec![lit.negated()]);
            self.ge_literals.insert(key, lit);
            self.sat_to_int.insert(
                sat_var,
                BoundLiteral {
                    var,
                    value,
                    is_ge: true,
                },
            );
            return lit;
        }

        // Normal case: create a new SAT variable
        let sat_var = sat.new_var();
        let lit = Literal::positive(sat_var);
        self.ge_literals.insert(key, lit);
        self.sat_to_int.insert(
            sat_var,
            BoundLiteral {
                var,
                value,
                is_ge: true,
            },
        );

        // Add ordering clause: [x >= value] → [x >= value - 1]
        // Encoded as: ¬[x >= value] ∨ [x >= value - 1]
        if value - 1 > lb {
            if let Some(&prev_lit) = self.ge_literals.get(&(var, value - 1)) {
                sat.add_clause(vec![lit.negated(), prev_lit]);
            }
        }

        // Add ordering clause: [x >= value + 1] → [x >= value]
        // If the next literal already exists
        if let Some(next_value) = value.checked_add(1) {
            if let Some(&next_lit) = self.ge_literals.get(&(var, next_value)) {
                sat.add_clause(vec![next_lit.negated(), lit]);
            }
        }

        lit
    }

    /// Get the SAT literal for `[x <= value]`, which is `¬[x >= value + 1]`.
    pub fn get_or_create_le(&mut self, sat: &mut SatSolver, var: IntVarId, value: i64) -> Literal {
        if let Some(next_value) = value.checked_add(1) {
            self.get_or_create_ge(sat, var, next_value).negated()
        } else {
            let (lb, _) = self.var_bounds[var.index()];
            self.get_or_create_ge(sat, var, lb)
        }
    }

    /// Get the SAT literal for `[x = value]`.
    /// This is `[x >= value] ∧ [x <= value]`, i.e., `[x >= value] ∧ ¬[x >= value + 1]`.
    pub fn get_or_create_eq(
        &mut self,
        sat: &mut SatSolver,
        var: IntVarId,
        value: i64,
    ) -> (Literal, Literal) {
        let ge = self.get_or_create_ge(sat, var, value);
        let le = self.get_or_create_le(sat, var, value);
        (ge, le)
    }

    /// Forbid a single value using the standard order-encoding `x != value`
    /// clause: `¬[x >= value] ∨ [x >= value + 1]`.
    pub fn forbid_value(&mut self, sat: &mut SatSolver, var: IntVarId, value: i64) {
        let ge = self.get_or_create_ge(sat, var, value);
        let mut clause = vec![ge.negated()];
        if let Some(next_value) = value.checked_add(1) {
            clause.push(self.get_or_create_ge(sat, var, next_value));
        }
        sat.add_clause(clause);
    }

    /// Look up what integer bound a SAT variable represents.
    /// After `pre_allocate_all()`, uses O(1) array indexing.
    #[inline]
    pub fn decode(&self, sat_var: SatVariable) -> Option<&BoundLiteral> {
        let idx = sat_var.index();
        if idx < self.decode_array.len() {
            self.decode_array[idx].as_ref()
        } else {
            // Fallback to hash map for SAT variables created after pre_allocate_all
            self.sat_to_int.get(&sat_var)
        }
    }

    /// Get bounds for a variable.
    #[inline]
    pub fn var_bounds(&self, var: IntVarId) -> (i64, i64) {
        self.var_bounds[var.index()]
    }

    /// Number of registered variables.
    pub fn num_vars(&self) -> usize {
        self.var_bounds.len()
    }

    /// Number of SAT literals created so far.
    pub fn num_literals(&self) -> usize {
        self.ge_literals.len()
    }

    /// Look up an existing `[x >= value]` literal without creating one.
    /// After `pre_allocate_all()`, uses O(1) array indexing.
    /// Returns `None` if the literal hasn't been pre-allocated.
    #[inline]
    pub fn lookup_ge(&self, var: IntVarId, value: i64) -> Option<Literal> {
        let idx = var.index();
        if idx < self.ge_array.len() {
            let (lb, _) = self.var_bounds[idx];
            if let Some(offset) = value
                .checked_sub(lb)
                .and_then(|delta| usize::try_from(delta).ok())
            {
                let arr = &self.ge_array[idx];
                if offset < arr.len() {
                    return Some(arr[offset]);
                }
            }
        }
        // Fallback: hash map (for literals created outside pre_allocate_all)
        self.ge_literals.get(&(var, value)).copied()
    }

    /// Look up an existing `[x <= value]` literal, i.e. `¬[x >= value + 1]`.
    /// Returns `None` if the literal hasn't been pre-allocated.
    #[inline]
    pub fn lookup_le(&self, var: IntVarId, value: i64) -> Option<Literal> {
        if let Some(next_value) = value.checked_add(1) {
            self.lookup_ge(var, next_value).map(Literal::negated)
        } else {
            let (lb, _) = self.var_bounds[var.index()];
            self.lookup_ge(var, lb)
        }
    }

    /// Pre-allocate all order-encoding literals for every registered variable.
    /// For variable `x ∈ [lb, ub]`, creates `[x >= v]` for all v in [lb, ub+1].
    /// Also builds dense lookup arrays for O(1) `lookup_ge()` and `decode()`.
    pub fn pre_allocate_all(&mut self, sat: &mut SatSolver) {
        if !self.ge_array.is_empty() {
            debug_assert_eq!(
                self.ge_array.len(),
                self.var_bounds.len(),
                "registering new CP variables after order pre-allocation is unsupported",
            );
            return;
        }

        for var_idx in 0..self.var_bounds.len() {
            let var = IntVarId(var_idx as u32);
            let (lb, ub) = self.var_bounds[var_idx];
            let end = ub.saturating_add(1);
            // Create [x >= v] for every v from lb to ub+1
            // (ub+1 is "always false", but useful for [x <= ub] = ¬[x >= ub+1])
            for v in lb..=end {
                self.get_or_create_ge(sat, var, v);
            }
        }

        // Build dense ge_array for O(1) lookup_ge().
        self.ge_array = Vec::with_capacity(self.var_bounds.len());
        for var_idx in 0..self.var_bounds.len() {
            let var = IntVarId(var_idx as u32);
            let (lb, ub) = self.var_bounds[var_idx];
            let end = ub.saturating_add(1);
            let size = end
                .checked_sub(lb)
                .and_then(|width| width.checked_add(1))
                .and_then(|width| usize::try_from(width).ok())
                .expect("order-encoding domain too large to pre-allocate");
            let mut arr = Vec::with_capacity(size);
            for v in lb..=end {
                // All literals were just created above, so unwrap is safe
                arr.push(self.ge_literals[&(var, v)]);
            }
            self.ge_array.push(arr);
        }

        // Build dense decode_array for O(1) decode().
        let max_sat_var = self.sat_to_int.keys().map(|v| v.index()).max().unwrap_or(0);
        self.decode_array = vec![None; max_sat_var + 1];
        for (&sat_var, &bound_lit) in &self.sat_to_int {
            self.decode_array[sat_var.index()] = Some(bound_lit);
        }

        // Free the map memory now that dense arrays handle all lookups.
        // No new literals are created after pre_allocate_all() — all
        // get_or_create_* calls happen during model construction before this point.
        // The fallback paths in lookup_ge/decode handle the (impossible in practice)
        // case of post-allocation creation by returning None from the empty maps.
        self.ge_literals.clear();
        self.ge_literals.shrink_to_fit();
        self.sat_to_int.clear();
    }
}

impl Default for IntegerEncoder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[path = "encoder_tests.rs"]
mod tests;
