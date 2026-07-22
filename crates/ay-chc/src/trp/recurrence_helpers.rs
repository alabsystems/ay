// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recurrence bound and exponential pattern handlers for TRP.
//!
//! Extracted from `mod.rs` for code health (#5970).
//! Contains LoAT-style recurrence handlers:
//! - `recurrent_bounds`: delta bounds scaled by iteration count
//! - `recurrent_exps`: exponential growth/decay patterns

use super::Trp;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl Trp {
    /// Handle delta bounds (x' - x patterns) from LoAT.
    ///
    /// Introduces delta variables: d = x' - x
    /// Projects out non-delta variables, emits bounds scaled by n.
    pub(super) fn recurrent_bounds(
        &self,
        loop_body: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        result: &mut Vec<ChcExpr>,
        handled_vars: &FxHashSet<String>,
    ) {
        // For each state variable, compute delta = x_next - x
        for var in &self.state_vars {
            // Skip variables already handled by closed-form analysis to avoid duplicates
            if handled_vars.contains(&var.name) {
                continue;
            }
            if var.sort != ChcSort::Int {
                continue;
            }

            let next_var = ChcVar::new(format!("{}_next", var.name), var.sort.clone());

            // Get model values
            let pre_val = model
                .get(&var.name)
                .and_then(|v| match v {
                    SmtValue::Int(n) => Some(*n),
                    _ => None,
                })
                .unwrap_or(0);

            let post_val = model
                .get(&next_var.name)
                .and_then(|v| match v {
                    SmtValue::Int(n) => Some(*n),
                    _ => None,
                })
                .unwrap_or(0);

            // i128-lockstep: checked i128 subtraction; skip the variable on
            // overflow instead of wrapping.
            let Some(delta) = post_val.checked_sub(pre_val) else {
                continue;
            };

            // If delta is non-zero, emit constraint
            if delta != 0 {
                // For constant delta, emit: (x_next - x) * n accounts for n iterations
                // This is a simple bound - more sophisticated analysis would be needed
                // for variable deltas

                // Check if this matches a constant delta pattern in the loop body
                if self.is_constant_delta_pattern(loop_body, var, delta) {
                    // Emit: total change = delta * n
                    // x_next@n - x@0 = delta * n
                    let total_delta = if delta == 1 {
                        ChcExpr::var(self.n_var.clone())
                    } else {
                        ChcExpr::mul(ChcExpr::int(delta), ChcExpr::var(self.n_var.clone()))
                    };

                    // The post-state after n iterations should satisfy bounds based on n
                    if delta > 0 {
                        // x' >= x + delta for each step, so x_n >= x_0 + delta*n
                        result.push(ChcExpr::ge(
                            ChcExpr::var(next_var.clone()),
                            ChcExpr::add(ChcExpr::var(var.clone()), total_delta),
                        ));
                    } else {
                        // x' <= x + delta (where delta < 0)
                        result.push(ChcExpr::le(
                            ChcExpr::var(next_var.clone()),
                            ChcExpr::add(ChcExpr::var(var.clone()), total_delta),
                        ));
                    }
                }
            }
        }
    }

    /// Check if the loop body contains a constant delta pattern for var.
    pub(super) fn is_constant_delta_pattern(
        &self,
        loop_body: &ChcExpr,
        var: &ChcVar,
        expected_delta: i128,
    ) -> bool {
        // Look for x_next = x + c pattern in conjuncts
        for conjunct in loop_body.conjuncts() {
            if let ChcExpr::Op(ChcOp::Eq, args) = conjunct {
                if args.len() == 2 {
                    // Check for x_next = x + c
                    if let ChcExpr::Var(lhs_var) = args[0].as_ref() {
                        let expected_next = format!("{}_next", var.name);
                        if lhs_var.name == expected_next {
                            // Check RHS for x + c pattern
                            if let Some(delta) = self.extract_delta(&args[1], var) {
                                return delta == expected_delta;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Extract delta from an expression x + c or x - c.
    pub(super) fn extract_delta(&self, expr: &ChcExpr, var: &ChcVar) -> Option<i128> {
        match expr {
            ChcExpr::Var(v) if v.name == var.name => Some(0),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == var.name => Some(*c),
                    (ChcExpr::Int(c), ChcExpr::Var(v)) if v.name == var.name => Some(*c),
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == var.name => c.checked_neg(),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Handle exponential patterns (x' = c*x where c != 1) from LoAT.
    ///
    /// For c > 1 and x >= 0: emit x >= 0 (sign preserved) and x_next >= x (growth)
    /// For c > 1 and x < 0: emit x < 0 (sign preserved) and x_next <= x (more negative)
    pub(super) fn recurrent_exps(
        &self,
        loop_body: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        result: &mut Vec<ChcExpr>,
    ) {
        // Look for x_next = c * x patterns
        for conjunct in loop_body.conjuncts() {
            if let ChcExpr::Op(ChcOp::Eq, args) = conjunct {
                if args.len() == 2 {
                    // Check for x_next = c * x
                    if let ChcExpr::Var(lhs_var) = args[0].as_ref() {
                        if let Some(base) = lhs_var.name.strip_suffix("_next") {
                            if let Some(var) = self.state_vars.iter().find(|v| v.name == base) {
                                if let Some(coeff) = self.extract_linear_coeff(&args[1], var) {
                                    if coeff != 1 && coeff != 0 {
                                        // Found x' = c*x pattern
                                        let val = model
                                            .get(&var.name)
                                            .and_then(|v| match v {
                                                SmtValue::Int(n) => Some(*n),
                                                _ => None,
                                            })
                                            .unwrap_or(0);

                                        let next_var = ChcVar::new(
                                            format!("{}_next", var.name),
                                            var.sort.clone(),
                                        );

                                        // Emit bounds based on sign and coefficient
                                        if coeff > 1 {
                                            if val >= 0 {
                                                // x >= 0: sign preserved, exponential growth
                                                result.push(ChcExpr::ge(
                                                    ChcExpr::var(var.clone()),
                                                    ChcExpr::int(0),
                                                ));
                                                // x_next >= x (growth bound)
                                                result.push(ChcExpr::ge(
                                                    ChcExpr::var(next_var),
                                                    ChcExpr::var(var.clone()),
                                                ));
                                            } else {
                                                // x < 0: sign preserved, becomes more negative
                                                result.push(ChcExpr::lt(
                                                    ChcExpr::var(var.clone()),
                                                    ChcExpr::int(0),
                                                ));
                                                // x_next <= x (more negative bound)
                                                result.push(ChcExpr::le(
                                                    ChcExpr::var(next_var),
                                                    ChcExpr::var(var.clone()),
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Extract linear coefficient from c * x expression.
    pub(super) fn extract_linear_coeff(&self, expr: &ChcExpr, var: &ChcVar) -> Option<i128> {
        match expr {
            ChcExpr::Var(v) if v.name == var.name => Some(1),
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(c), ChcExpr::Var(v)) if v.name == var.name => Some(*c),
                    (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == var.name => Some(*c),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}
