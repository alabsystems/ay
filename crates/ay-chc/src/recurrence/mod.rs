// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed-form recurrence solver for loop acceleration.
//!
//! This module computes closed-form solutions for linear recurrences,
//! enabling loop acceleration in CHC engines (TPA, TRL, TRP).
//!
//! # Supported Recurrence Types
//!
//! 1. **Constant delta**: `x' = x + c` -> `x_n = x_0 + c*n`
//! 2. **Triangular systems**: Multiple variables with acyclic dependencies
//!
//! # Algorithm Source
//!
//! Based on CAV'19 "Termination of Triangular Integer Loops is Decidable"
//! (Frohn & Giesl), Algorithm 3.

use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_rational::Rational64;
use std::sync::Arc;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;

/// A closed-form expression for a recurrence solution.
#[derive(Debug, Clone)]
pub(crate) enum ClosedForm {
    /// Constant delta: x_n = x_0 + c*n
    ConstantDelta {
        /// Delta per iteration
        delta: i64,
    },

    /// Polynomial in iteration count n, with coefficients that may depend
    /// on initial variable values.
    ///
    /// Represents: sum_{i=0}^{degree} coeffs\[i\] * n^i
    /// where each coefficient is a linear combination of initial values.
    /// Empty string key "" represents the constant term.
    Polynomial {
        /// Polynomial coefficients indexed by power of n.
        coeffs: Vec<FxHashMap<String, Rational64>>,
    },
}

impl ClosedForm {
    /// Create a polynomial for quadratic accumulation.
    ///
    /// For s' = s + i where i grows linearly: i_n = i_0 + n
    /// s_n = s_0 + n*i_0 + n*(n-1)/2
    fn quadratic_sum(
        sum_var: impl Into<String>,
        counter_var: impl Into<String>,
        counter_delta: i64,
    ) -> Self {
        let sum_var = sum_var.into();
        let counter_var = counter_var.into();

        // s_n = s_0 + sum_{k=0}^{n-1} (i_0 + delta*k)
        //     = s_0 + n*i_0 + delta * n*(n-1)/2
        //     = s_0 + n*i_0 + (delta/2)*n^2 - (delta/2)*n
        //     = s_0 + (i_0 - delta/2)*n + (delta/2)*n^2

        let mut coeff_0 = FxHashMap::default();
        coeff_0.insert(sum_var, Rational64::from_integer(1));

        let delta_half = Rational64::new(counter_delta, 2);
        let mut coeff_1 = FxHashMap::default();
        coeff_1.insert(counter_var, Rational64::from_integer(1));
        coeff_1.insert(String::new(), -delta_half);

        let mut coeff_2 = FxHashMap::default();
        coeff_2.insert(String::new(), delta_half);

        Self::Polynomial {
            coeffs: vec![coeff_0, coeff_1, coeff_2],
        }
    }
}

/// A system of recurrence relations with triangular (acyclic) dependencies.
///
/// Variables are ordered such that each variable's update depends only on
/// variables that appear earlier in the order.
#[derive(Debug, Clone)]
pub(crate) struct TriangularSystem {
    /// Variables in dependency order (earlier vars are solved first).
    pub order: Vec<String>,

    /// Closed-form solution for each variable.
    pub solutions: FxHashMap<String, ClosedForm>,
}

impl TriangularSystem {
    fn new() -> Self {
        Self {
            order: Vec::new(),
            solutions: FxHashMap::default(),
        }
    }

    /// Get the closed-form solution for a variable.
    pub(crate) fn get_solution(&self, var: &str) -> Option<&ClosedForm> {
        self.solutions.get(var)
    }
}

impl Default for TriangularSystem {
    fn default() -> Self {
        Self::new()
    }
}

/// Analyze a transition relation and attempt to build a closed-form recurrence.
///
/// Given a transition as a conjunction of equalities like `v' = f(v)`, attempts
/// to compute closed-form solutions.
pub(crate) fn analyze_transition(
    transition: &ChcExpr,
    state_vars: &[String],
) -> Option<TriangularSystem> {
    let updates = extract_updates(transition, state_vars)?;
    let order = topological_order(&updates)?;

    let mut system = TriangularSystem::new();

    for var in order {
        if let Some(update) = updates.get(&var) {
            match analyze_update(update, &var, &system) {
                Some(cf) => {
                    system.order.push(var.clone());
                    system.solutions.insert(var, cf);
                }
                None => return None,
            }
        }
    }

    if system.solutions.is_empty() {
        None
    } else {
        Some(system)
    }
}

/// Extract update expressions from a transition.
fn extract_updates(
    transition: &ChcExpr,
    state_vars: &[String],
) -> Option<FxHashMap<String, ChcExpr>> {
    let mut updates = FxHashMap::default();
    let conjuncts = transition.conjuncts();

    for conjunct in conjuncts {
        if let ChcExpr::Op(ChcOp::Eq, args) = conjunct {
            if args.len() == 2 {
                if let ChcExpr::Var(v) = &*args[0] {
                    let base_name = v.base_name();
                    if v.is_primed() && state_vars.contains(&base_name.to_string()) {
                        // Strip BvToInt ITE/mod wrappers (#7931) so recurrence
                        // analysis sees the underlying linear structure.
                        let rhs = strip_bv_wrapping(&args[1]);
                        updates.insert(base_name.to_string(), rhs);
                        continue;
                    }
                }
                if let ChcExpr::Var(v) = &*args[0] {
                    if let Some(base) = v.name.strip_suffix("_next") {
                        if state_vars.contains(&base.to_string()) {
                            let rhs = strip_bv_wrapping(&args[1]);
                            updates.insert(base.to_string(), rhs);
                        }
                    }
                }
            }
        }
    }

    if updates.is_empty() {
        None
    } else {
        Some(updates)
    }
}

/// Compute topological order for solving variables.
fn topological_order(updates: &FxHashMap<String, ChcExpr>) -> Option<Vec<String>> {
    let mut vars: Vec<_> = updates.keys().cloned().collect();
    vars.sort_unstable(); // Deterministic variable ordering (#3060)

    let mut deps: FxHashMap<String, Vec<String>> = FxHashMap::default();
    for (var, update) in updates {
        let mut var_deps = Vec::new();
        collect_variable_refs(update, &vars, &mut var_deps);
        var_deps.retain(|d| d != var);
        deps.insert(var.clone(), var_deps);
    }

    let mut dependents: FxHashMap<String, Vec<String>> = FxHashMap::default();
    for var in &vars {
        dependents.insert(var.clone(), Vec::new());
    }
    for (var, dep_list) in &deps {
        for dep in dep_list {
            dependents.entry(dep.clone()).or_default().push(var.clone());
        }
    }

    let mut in_degree: FxHashMap<String, usize> = FxHashMap::default();
    for (var, dep_list) in &deps {
        in_degree.insert(var.clone(), dep_list.len());
    }

    let mut queue: Vec<String> = vars
        .iter()
        .filter(|v| *in_degree.get(*v).unwrap_or(&0) == 0)
        .cloned()
        .collect();
    // Sort descending so pop() yields smallest first (#3060)
    queue.sort_unstable_by(|a, b| b.cmp(a));

    let mut result = Vec::new();

    while let Some(var) = queue.pop() {
        result.push(var.clone());
        if let Some(dependent_list) = dependents.get(&var) {
            for dependent in dependent_list {
                if let Some(count) = in_degree.get_mut(dependent) {
                    *count -= 1;
                    if *count == 0 {
                        queue.push(dependent.clone());
                    }
                }
            }
            // Re-sort entire queue to maintain global descending order (#3060)
            queue.sort_unstable_by(|a, b| b.cmp(a));
        }
    }

    if result.len() == vars.len() {
        Some(result)
    } else {
        None
    }
}

fn collect_variable_refs(expr: &ChcExpr, candidates: &[String], result: &mut Vec<String>) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(v) => {
            let base = v.base_name();
            if candidates.contains(&base.to_string()) && !result.contains(&base.to_string()) {
                result.push(base.to_string());
            }
        }
        ChcExpr::Op(_, args) => {
            for arg in args {
                collect_variable_refs(arg, candidates, result);
            }
        }
        _ => {}
    });
}

/// Check whether a positive integer is a power of two.
fn is_power_of_2(n: i128) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

/// Strip BvToInt modular arithmetic wrappers from an expression (#7931).
///
/// BvToInt transforms BV operations into integer arithmetic with ITE/mod
/// guards that enforce modular semantics. These wrappers hide the underlying
/// linear structure from recurrence analysis. This function recognizes and
/// strips the common BvToInt patterns:
///
/// - `ite(sum < 2^w, sum, sum - 2^w)` -> `sum` (bvadd)
/// - `ite(diff >= 0, diff, diff + 2^w)` -> `diff` (bvsub)
/// - `mod(expr, 2^w)` -> `expr` (bvmul, large-width ops)
///
/// The stripping is conservative: only recognized patterns with power-of-2
/// bounds are stripped. This is sound for accumulator analysis when values
/// are bounded by loop iterations (no overflow).
pub(crate) fn strip_bv_wrapping(expr: &ChcExpr) -> ChcExpr {
    match expr {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            // Pattern: ite(sum < 2^w, sum, sum - 2^w) -- bvadd wrapping
            if let ChcExpr::Op(ChcOp::Lt, cond_args) = &*args[0] {
                if cond_args.len() == 2 {
                    if let ChcExpr::Int(bound) = &*cond_args[1] {
                        if is_power_of_2(*bound) && *cond_args[0] == *args[1] {
                            // Verify else-branch is sum - 2^w
                            if let ChcExpr::Op(ChcOp::Sub, sub_args) = &*args[2] {
                                if sub_args.len() == 2
                                    && *cond_args[0] == *sub_args[0]
                                    && *sub_args[1] == ChcExpr::Int(*bound)
                                {
                                    return strip_bv_wrapping(&cond_args[0]);
                                }
                            }
                        }
                    }
                }
            }
            // Pattern: ite(diff >= 0, diff, diff + 2^w) -- bvsub wrapping
            if let ChcExpr::Op(ChcOp::Ge, cond_args) = &*args[0] {
                if cond_args.len() == 2 && *cond_args[1] == ChcExpr::Int(0) {
                    if *cond_args[0] == *args[1] {
                        if let ChcExpr::Op(ChcOp::Add, add_args) = &*args[2] {
                            if add_args.len() == 2 && *cond_args[0] == *add_args[0] {
                                if let ChcExpr::Int(bound) = &*add_args[1] {
                                    if is_power_of_2(*bound) {
                                        return strip_bv_wrapping(&cond_args[0]);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // Not a recognized BvToInt pattern -- still recurse into sub-expressions
            let new_args: Vec<Arc<ChcExpr>> = args
                .iter()
                .map(|a| Arc::new(strip_bv_wrapping(a)))
                .collect();
            ChcExpr::Op(ChcOp::Ite, new_args)
        }
        // Pattern: mod(expr, 2^w) -- bvmul, large-width bvadd/bvsub
        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
            if let ChcExpr::Int(bound) = &*args[1] {
                if is_power_of_2(*bound) {
                    return strip_bv_wrapping(&args[0]);
                }
            }
            expr.clone()
        }
        // Recurse into other operations
        ChcExpr::Op(op, args) => {
            let new_args: Vec<Arc<ChcExpr>> = args
                .iter()
                .map(|a| Arc::new(strip_bv_wrapping(a)))
                .collect();
            if new_args.iter().zip(args.iter()).all(|(a, b)| **a == **b) {
                expr.clone()
            } else {
                ChcExpr::Op(*op, new_args)
            }
        }
        _ => expr.clone(),
    }
}

/// Analyze a single variable update and produce a closed form.
fn analyze_update(update: &ChcExpr, var: &str, system: &TriangularSystem) -> Option<ClosedForm> {
    // Pattern: v (unchanged, delta = 0)
    if let ChcExpr::Var(v) = update {
        if v.base_name() == var || v.name == var {
            return Some(ClosedForm::ConstantDelta { delta: 0 });
        }
    }

    // Pattern: v + c or c + v (constant delta)
    if let ChcExpr::Op(ChcOp::Add, args) = update {
        if args.len() == 2 {
            match (&*args[0], &*args[1]) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if v.base_name() == var || v.name == var => {
                    // i128-lockstep: ClosedForm is Rational64(i64)-based; abstain
                    // (no closed form) when the delta does not fit i64.
                    return Some(ClosedForm::ConstantDelta {
                        delta: i64::try_from(*c).ok()?,
                    });
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if v.base_name() == var || v.name == var => {
                    // i128-lockstep: abstain when the delta does not fit i64.
                    return Some(ClosedForm::ConstantDelta {
                        delta: i64::try_from(*c).ok()?,
                    });
                }
                (ChcExpr::Var(v), ChcExpr::Var(other))
                    if (v.base_name() == var || v.name == var) =>
                {
                    let other_base = other.base_name();
                    if let Some(ClosedForm::ConstantDelta { delta, .. }) =
                        system.solutions.get(other_base)
                    {
                        return Some(ClosedForm::quadratic_sum(var, other_base, *delta));
                    }
                }
                (ChcExpr::Var(other), ChcExpr::Var(v))
                    if (v.base_name() == var || v.name == var) =>
                {
                    let other_base = other.base_name();
                    if let Some(ClosedForm::ConstantDelta { delta, .. }) =
                        system.solutions.get(other_base)
                    {
                        return Some(ClosedForm::quadratic_sum(var, other_base, *delta));
                    }
                }
                // Pattern: v + (c + other) or v + (other + c) where other has ConstantDelta
                // This handles forward-substituted transitions like B + (1 + A)
                // which is B + A_next where A_next = A + 1. The effective update
                // is B' = B + (A + constant), producing a quadratic sum with an
                // offset that is absorbed by the constant in coeff[1].
                (ChcExpr::Var(v), ChcExpr::Op(ChcOp::Add, inner_args))
                    if (v.base_name() == var || v.name == var) && inner_args.len() == 2 =>
                {
                    let (other_var, _constant) = match (&*inner_args[0], &*inner_args[1]) {
                        (ChcExpr::Int(_c), ChcExpr::Var(other)) => (Some(other), Some(*_c)),
                        (ChcExpr::Var(other), ChcExpr::Int(_c)) => (Some(other), Some(*_c)),
                        _ => (None, None),
                    };
                    if let (Some(other), Some(_const_offset)) = (other_var, _constant) {
                        let other_base = other.base_name();
                        if let Some(ClosedForm::ConstantDelta { delta }) =
                            system.solutions.get(other_base)
                        {
                            // The sum accumulates (other + const_offset) per iteration.
                            // other has delta d, so at step k: other_k = other_0 + d*k.
                            // We accumulate: sum_{k=0}^{n-1} (other_k + const_offset)
                            //              = sum_{k=0}^{n-1} (other_0 + d*k + const_offset)
                            //              = n*(other_0 + const_offset) + d*n*(n-1)/2
                            // This is a quadratic sum with effective counter_init
                            // shifted by const_offset. We express it as:
                            // s_n = s_0 + n*(other_0 + const_offset) + (d/2)*n^2 - (d/2)*n
                            let sum_var_str: String = var.to_string();
                            let other_base_str: String = other_base.to_string();
                            let delta_half = Rational64::new(*delta, 2);

                            let mut coeff_0 = FxHashMap::default();
                            coeff_0.insert(sum_var_str, Rational64::from_integer(1));

                            let mut coeff_1 = FxHashMap::default();
                            coeff_1.insert(other_base_str, Rational64::from_integer(1));
                            // constant term: const_offset - delta/2
                            coeff_1.insert(
                                String::new(),
                                // i128-lockstep: Rational64 numerator is i64; abstain
                                // when the offset does not fit.
                                Rational64::from_integer(i64::try_from(_const_offset).ok()?)
                                    - delta_half,
                            );

                            let mut coeff_2 = FxHashMap::default();
                            coeff_2.insert(String::new(), delta_half);

                            return Some(ClosedForm::Polynomial {
                                coeffs: vec![coeff_0, coeff_1, coeff_2],
                            });
                        }
                    }
                }
                // Symmetric: (c + other) + v or (other + c) + v
                (ChcExpr::Op(ChcOp::Add, inner_args), ChcExpr::Var(v))
                    if (v.base_name() == var || v.name == var) && inner_args.len() == 2 =>
                {
                    let (other_var, _constant) = match (&*inner_args[0], &*inner_args[1]) {
                        (ChcExpr::Int(_c), ChcExpr::Var(other)) => (Some(other), Some(*_c)),
                        (ChcExpr::Var(other), ChcExpr::Int(_c)) => (Some(other), Some(*_c)),
                        _ => (None, None),
                    };
                    if let (Some(other), Some(_const_offset)) = (other_var, _constant) {
                        let other_base = other.base_name();
                        if let Some(ClosedForm::ConstantDelta { delta }) =
                            system.solutions.get(other_base)
                        {
                            let sum_var_str: String = var.to_string();
                            let other_base_str: String = other_base.to_string();
                            let delta_half = Rational64::new(*delta, 2);

                            let mut coeff_0 = FxHashMap::default();
                            coeff_0.insert(sum_var_str, Rational64::from_integer(1));

                            let mut coeff_1 = FxHashMap::default();
                            coeff_1.insert(other_base_str, Rational64::from_integer(1));
                            coeff_1.insert(
                                String::new(),
                                // i128-lockstep: Rational64 numerator is i64; abstain
                                // when the offset does not fit.
                                Rational64::from_integer(i64::try_from(_const_offset).ok()?)
                                    - delta_half,
                            );

                            let mut coeff_2 = FxHashMap::default();
                            coeff_2.insert(String::new(), delta_half);

                            return Some(ClosedForm::Polynomial {
                                coeffs: vec![coeff_0, coeff_1, coeff_2],
                            });
                        }
                    }
                }
                // Pattern: v + (scalar * (c + other)) or v + (scalar * (other + c))
                // where other has ConstantDelta. Handles cases like B + (-1 * (-1 + A)).
                // The per-step increment is scalar*(c + other_k), forming a quadratic sum.
                (ChcExpr::Var(v), ChcExpr::Op(ChcOp::Mul, mul_args))
                    if (v.base_name() == var || v.name == var) && mul_args.len() == 2 =>
                {
                    let (scalar, inner) = match (&*mul_args[0], &*mul_args[1]) {
                        (ChcExpr::Int(s), inner) => (Some(*s), Some(inner)),
                        (inner, ChcExpr::Int(s)) => (Some(*s), Some(inner)),
                        _ => (None, None),
                    };
                    if let (Some(s), Some(ChcExpr::Op(ChcOp::Add, inner_args))) = (scalar, inner) {
                        if inner_args.len() == 2 {
                            let (other_var, const_val) = match (&*inner_args[0], &*inner_args[1]) {
                                (ChcExpr::Int(c), ChcExpr::Var(other)) => (Some(other), Some(*c)),
                                (ChcExpr::Var(other), ChcExpr::Int(c)) => (Some(other), Some(*c)),
                                _ => (None, None),
                            };
                            if let (Some(other), Some(c)) = (other_var, const_val) {
                                let other_base = other.base_name();
                                if let Some(ClosedForm::ConstantDelta { delta }) =
                                    system.solutions.get(other_base)
                                {
                                    // s_n = s_0 + n*s*(c + other_0) + (s*d/2)*n^2 - (s*d/2)*n
                                    // i128-lockstep: Rational64 numerator is i64;
                                    // abstain when scalar/constant do not fit.
                                    let s_rat = Rational64::from_integer(i64::try_from(s).ok()?);
                                    let sd_half = s_rat * Rational64::new(*delta, 2);
                                    let sc =
                                        s_rat * Rational64::from_integer(i64::try_from(c).ok()?);

                                    let sum_var_str: String = var.to_string();
                                    let other_base_str: String = other_base.to_string();

                                    let mut coeff_0 = FxHashMap::default();
                                    coeff_0.insert(sum_var_str, Rational64::from_integer(1));

                                    let mut coeff_1 = FxHashMap::default();
                                    coeff_1.insert(other_base_str, s_rat);
                                    coeff_1.insert(String::new(), sc - sd_half);

                                    let mut coeff_2 = FxHashMap::default();
                                    coeff_2.insert(String::new(), sd_half);

                                    return Some(ClosedForm::Polynomial {
                                        coeffs: vec![coeff_0, coeff_1, coeff_2],
                                    });
                                }
                            }
                        }
                    }
                }
                // Symmetric: (scalar * (c + other)) + v
                (ChcExpr::Op(ChcOp::Mul, mul_args), ChcExpr::Var(v))
                    if (v.base_name() == var || v.name == var) && mul_args.len() == 2 =>
                {
                    let (scalar, inner) = match (&*mul_args[0], &*mul_args[1]) {
                        (ChcExpr::Int(s), inner) => (Some(*s), Some(inner)),
                        (inner, ChcExpr::Int(s)) => (Some(*s), Some(inner)),
                        _ => (None, None),
                    };
                    if let (Some(s), Some(ChcExpr::Op(ChcOp::Add, inner_args))) = (scalar, inner) {
                        if inner_args.len() == 2 {
                            let (other_var, const_val) = match (&*inner_args[0], &*inner_args[1]) {
                                (ChcExpr::Int(c), ChcExpr::Var(other)) => (Some(other), Some(*c)),
                                (ChcExpr::Var(other), ChcExpr::Int(c)) => (Some(other), Some(*c)),
                                _ => (None, None),
                            };
                            if let (Some(other), Some(c)) = (other_var, const_val) {
                                let other_base = other.base_name();
                                if let Some(ClosedForm::ConstantDelta { delta }) =
                                    system.solutions.get(other_base)
                                {
                                    // i128-lockstep: Rational64 numerator is i64;
                                    // abstain when scalar/constant do not fit.
                                    let s_rat = Rational64::from_integer(i64::try_from(s).ok()?);
                                    let sd_half = s_rat * Rational64::new(*delta, 2);
                                    let sc =
                                        s_rat * Rational64::from_integer(i64::try_from(c).ok()?);

                                    let sum_var_str: String = var.to_string();
                                    let other_base_str: String = other_base.to_string();

                                    let mut coeff_0 = FxHashMap::default();
                                    coeff_0.insert(sum_var_str, Rational64::from_integer(1));

                                    let mut coeff_1 = FxHashMap::default();
                                    coeff_1.insert(other_base_str, s_rat);
                                    coeff_1.insert(String::new(), sc - sd_half);

                                    let mut coeff_2 = FxHashMap::default();
                                    coeff_2.insert(String::new(), sd_half);

                                    return Some(ClosedForm::Polynomial {
                                        coeffs: vec![coeff_0, coeff_1, coeff_2],
                                    });
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // Pattern: v - c (negative constant delta)
    if let ChcExpr::Op(ChcOp::Sub, args) = update {
        if args.len() == 2 {
            if let (ChcExpr::Var(v), ChcExpr::Int(c)) = (&*args[0], &*args[1]) {
                if v.base_name() == var || v.name == var {
                    // i128-lockstep: checked negate + i64 narrow; abstain on overflow.
                    return Some(ClosedForm::ConstantDelta {
                        delta: i64::try_from(c.checked_neg()?).ok()?,
                    });
                }
            }
        }
    }

    // Pattern: c (constant reset)
    if let ChcExpr::Int(c) = update {
        let mut coeffs = vec![FxHashMap::default()];
        // i128-lockstep: Rational64 numerator is i64; abstain when the reset
        // constant does not fit.
        coeffs[0].insert(
            String::new(),
            Rational64::from_integer(i64::try_from(*c).ok()?),
        );
        return Some(ClosedForm::Polynomial { coeffs });
    }

    None
}
