// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Problem-derived qualifier extraction for template-guided generalization.
//!
//! Qualifiers are atomic predicates (typically linear arithmetic comparisons) extracted from the
//! input CHC problem and later instantiated over predicate variables.

use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// A set of problem-derived qualifier templates.
#[derive(Debug, Clone)]
pub(crate) struct QualifierSet {
    /// Integer constants appearing in the problem.
    pub constants: FxHashSet<i128>,

    /// Multiplication coefficients appearing in the problem (e.g., `* 5 C` yields 5).
    /// Used for scaled-difference qualifiers `v1 - k*v2 {=, <=, >=} c`.
    pub coefficients: FxHashSet<i128>,
}

impl QualifierSet {
    /// Extract qualifiers from a CHC problem.
    pub(crate) fn from_problem(problem: &ChcProblem) -> Self {
        let mut comparisons: FxHashSet<ChcExpr> = FxHashSet::default();
        let mut constants: FxHashSet<i128> = FxHashSet::default();
        let mut coefficients: FxHashSet<i128> = FxHashSet::default();

        for clause in problem.clauses() {
            Self::collect_from_clause(clause, &mut comparisons, &mut constants);
        }

        // Extract multiplication coefficients from all clauses.
        for clause in problem.clauses() {
            if let Some(ref c) = clause.body.constraint {
                Self::collect_coefficients(c, &mut coefficients);
            }
            if let ClauseHead::Predicate(_, ref args) = clause.head {
                for arg in args {
                    Self::collect_coefficients(arg, &mut coefficients);
                }
            }
        }
        // Remove trivial coefficients (0, 1, -1 are already handled by difference qualifiers).
        coefficients.remove(&0);
        coefficients.remove(&1);
        coefficients.remove(&-1);

        // Seed small default coefficients {2, -2, 3, -3} so that scaled-difference
        // qualifiers (v1 - k*v2) are available even when the problem uses additive
        // step sizes rather than explicit (* k var) patterns (e.g., s_multipl_23
        // has B' = B + 2 which makes B = 2*A, but 2 only appears as an additive
        // constant, not as a multiplication coefficient).
        for k in [2i128, -2, 3, -3] {
            coefficients.insert(k);
        }

        // Avoid uncontrolled blow-ups from large constant sets. Keep a small, stable slice.
        let constants = Self::cap_constants(constants, 64);

        Self {
            constants,
            coefficients,
        }
    }

    /// Instantiate a set of candidate qualifiers over the given variables.
    ///
    /// This produces a conservative template family over integer variables:
    /// - `v ∘ c`, where ∘ ∈ {=, ≤, ≥}
    /// - `v1 ∘ v2`, where ∘ ∈ {=, ≤, ≥}
    pub(crate) fn instantiate(&self, vars: &[ChcVar]) -> Vec<ChcExpr> {
        let mut candidates: FxHashSet<ChcExpr> = FxHashSet::default();

        let mut int_vars: Vec<ChcVar> = vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .cloned()
            .collect();
        int_vars.sort_by(|a, b| a.name.cmp(&b.name));

        let mut constants: Vec<i128> = self.constants.iter().copied().collect();
        constants.sort_unstable();

        for v in &int_vars {
            for c in &constants {
                candidates.insert(ChcExpr::eq(ChcExpr::var(v.clone()), ChcExpr::int(*c)));
                candidates.insert(ChcExpr::le(ChcExpr::var(v.clone()), ChcExpr::int(*c)));
                candidates.insert(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(*c)));
            }
        }

        for (i, v1) in int_vars.iter().enumerate() {
            for v2 in int_vars.iter().skip(i + 1) {
                let a = ChcExpr::var(v1.clone());
                let b = ChcExpr::var(v2.clone());
                candidates.insert(ChcExpr::eq(a.clone(), b.clone()));
                candidates.insert(ChcExpr::le(a.clone(), b.clone()));
                candidates.insert(ChcExpr::ge(a.clone(), b.clone()));
                candidates.insert(ChcExpr::le(b.clone(), a.clone()));
                candidates.insert(ChcExpr::ge(b, a));
            }
        }

        // Sum-relation qualifiers: v1 + v2 {=, <=, >=} v3
        // These capture relational invariants like A + B = C which are
        // common in multi-phase counting loops (gj2007_m_1, dillig02_m).
        if int_vars.len() >= 3 {
            for (i, v1) in int_vars.iter().enumerate() {
                for (j, v2) in int_vars.iter().enumerate().skip(i + 1) {
                    let sum = ChcExpr::add(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone()));
                    for (k, v3) in int_vars.iter().enumerate() {
                        if k == i || k == j {
                            continue;
                        }
                        let rhs = ChcExpr::var(v3.clone());
                        candidates.insert(ChcExpr::eq(sum.clone(), rhs.clone()));
                        candidates.insert(ChcExpr::le(sum.clone(), rhs.clone()));
                        candidates.insert(ChcExpr::ge(sum.clone(), rhs.clone()));
                    }
                }
            }
        }

        // Sum-constant qualifiers: v1 + v2 {=, <=, >=} c
        // Captures conservation invariants like x0 + x1 = 0 (s_multipl_25).
        for (i, v1) in int_vars.iter().enumerate() {
            for v2 in int_vars.iter().skip(i + 1) {
                let sum = ChcExpr::add(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone()));
                for c in &constants {
                    candidates.insert(ChcExpr::eq(sum.clone(), ChcExpr::int(*c)));
                    candidates.insert(ChcExpr::le(sum.clone(), ChcExpr::int(*c)));
                    candidates.insert(ChcExpr::ge(sum.clone(), ChcExpr::int(*c)));
                }
            }
        }

        // Difference-relation qualifiers: v1 - v2 {=, <=, >=} c
        // for constants in the problem, capturing difference invariants.
        for (i, v1) in int_vars.iter().enumerate() {
            for v2 in int_vars.iter().skip(i + 1) {
                let diff = ChcExpr::sub(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone()));
                for c in &constants {
                    candidates.insert(ChcExpr::eq(diff.clone(), ChcExpr::int(*c)));
                    candidates.insert(ChcExpr::le(diff.clone(), ChcExpr::int(*c)));
                    candidates.insert(ChcExpr::ge(diff.clone(), ChcExpr::int(*c)));
                }
            }
        }

        // Scaled-difference qualifiers: v1 - k*v2 {=, <=, >=} c
        // for multiplication coefficients k found in the problem.
        // Critical for multi-phase loop invariants (gj2007_m_1: A - 5*C >= -6).
        let mut sorted_coeffs: Vec<i128> = self.coefficients.iter().copied().collect();
        sorted_coeffs.sort_unstable();
        for &k in &sorted_coeffs {
            for (i, v1) in int_vars.iter().enumerate() {
                for (j, v2) in int_vars.iter().enumerate() {
                    if i == j {
                        continue;
                    }
                    // v1 - k*v2
                    let scaled = ChcExpr::mul(ChcExpr::int(k), ChcExpr::var(v2.clone()));
                    let diff = ChcExpr::sub(ChcExpr::var(v1.clone()), scaled);
                    for c in &constants {
                        candidates.insert(ChcExpr::eq(diff.clone(), ChcExpr::int(*c)));
                        candidates.insert(ChcExpr::le(diff.clone(), ChcExpr::int(*c)));
                        candidates.insert(ChcExpr::ge(diff.clone(), ChcExpr::int(*c)));
                    }
                }
            }
        }

        // NOTE: Self-product (v*v) and cross-product (v1*v2) qualifiers are NOT
        // included here. They are injected unconditionally via
        // `instantiate_product_predicates()` in CEGAR's refinement path,
        // bypassing the MIN/MAX template budget. Including them here would
        // displace linear qualifiers in the budget-limited fallback because
        // `(* ...)` sorts lexicographically before `(+ ...)` and `(= ...)`.

        let mut out: Vec<ChcExpr> = candidates.into_iter().collect();
        out.sort_by_cached_key(ToString::to_string);
        out
    }

    /// Instantiate product/quadratic qualifiers over the given variables.
    ///
    /// These capture nonlinear invariants that the linear qualifier fallback
    /// misses due to the template budget cap. Injected unconditionally by CEGAR
    /// (like modular predicates) to ensure product invariants are available for
    /// benchmarks like s_multipl_22 (triangular: 2*B = A*(A+1)), s_multipl_08
    /// (A * B = C), and accumulator patterns (A * B + C = N).
    pub(crate) fn instantiate_product_predicates(&self, vars: &[ChcVar]) -> Vec<ChcExpr> {
        let mut candidates: FxHashSet<ChcExpr> = FxHashSet::default();
        let mut int_vars: Vec<ChcVar> = vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .cloned()
            .collect();
        int_vars.sort_by(|a, b| a.name.cmp(&b.name));

        let mut constants: Vec<i128> = self.constants.iter().copied().collect();
        constants.sort_unstable();

        // Self-product qualifiers: v*v {=,<=,>=} w, v*v {=,<=,>=} 2*w, v*v+v = 2*w
        if int_vars.len() >= 2 && int_vars.len() <= 10 {
            for (i, v1) in int_vars.iter().enumerate() {
                let sq = ChcExpr::mul(ChcExpr::var(v1.clone()), ChcExpr::var(v1.clone()));
                for (j, v2) in int_vars.iter().enumerate() {
                    if j == i {
                        continue;
                    }
                    candidates.insert(ChcExpr::eq(sq.clone(), ChcExpr::var(v2.clone())));
                    candidates.insert(ChcExpr::le(sq.clone(), ChcExpr::var(v2.clone())));
                    candidates.insert(ChcExpr::ge(sq.clone(), ChcExpr::var(v2.clone())));
                    let dbl_v2 = ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(v2.clone()));
                    candidates.insert(ChcExpr::eq(sq.clone(), dbl_v2.clone()));
                    candidates.insert(ChcExpr::le(sq.clone(), dbl_v2.clone()));
                    candidates.insert(ChcExpr::ge(sq.clone(), dbl_v2.clone()));
                    let sq_plus_v1 = ChcExpr::add(sq.clone(), ChcExpr::var(v1.clone()));
                    candidates.insert(ChcExpr::eq(sq_plus_v1.clone(), dbl_v2));
                    let dbl_v2_2 = ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(v2.clone()));
                    candidates.insert(ChcExpr::le(sq_plus_v1.clone(), dbl_v2_2.clone()));
                    candidates.insert(ChcExpr::ge(sq_plus_v1, dbl_v2_2));
                }
            }
        }

        // Cross-product qualifiers: v1*v2 {=,<=,>=} v3, v1*v2+v3 = c
        if int_vars.len() >= 3 && int_vars.len() <= 10 {
            for (i, v1) in int_vars.iter().enumerate() {
                for (j, v2) in int_vars.iter().enumerate().skip(i + 1) {
                    let product = ChcExpr::mul(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone()));
                    for (k, v3) in int_vars.iter().enumerate() {
                        if k == i || k == j {
                            continue;
                        }
                        candidates.insert(ChcExpr::eq(product.clone(), ChcExpr::var(v3.clone())));
                        candidates.insert(ChcExpr::le(product.clone(), ChcExpr::var(v3.clone())));
                        candidates.insert(ChcExpr::ge(product.clone(), ChcExpr::var(v3.clone())));
                        let accum = ChcExpr::add(product.clone(), ChcExpr::var(v3.clone()));
                        for &c in &[0i128, 1, -1] {
                            candidates.insert(ChcExpr::eq(accum.clone(), ChcExpr::int(c)));
                        }
                        for c in constants.iter().take(8) {
                            candidates.insert(ChcExpr::eq(accum.clone(), ChcExpr::int(*c)));
                        }
                    }
                }
            }
        }

        // Sum-relation qualifiers: v1+v2 {=,<=,>=} v3
        if int_vars.len() >= 3 {
            for (i, v1) in int_vars.iter().enumerate() {
                for (j, v2) in int_vars.iter().enumerate().skip(i + 1) {
                    let sum = ChcExpr::add(ChcExpr::var(v1.clone()), ChcExpr::var(v2.clone()));
                    for (k, v3) in int_vars.iter().enumerate() {
                        if k == i || k == j {
                            continue;
                        }
                        let rhs = ChcExpr::var(v3.clone());
                        candidates.insert(ChcExpr::eq(sum.clone(), rhs.clone()));
                        candidates.insert(ChcExpr::le(sum.clone(), rhs.clone()));
                        candidates.insert(ChcExpr::ge(sum.clone(), rhs.clone()));
                    }
                }
            }
        }

        let mut out: Vec<ChcExpr> = candidates.into_iter().collect();
        out.sort_by_cached_key(ToString::to_string);
        out
    }

    /// Instantiate problem-derived modular qualifiers over the given variables.
    ///
    /// These are used by the main qualifier fallback and by CEGAR's direct
    /// template injection path when non-modular atoms already fill the budget.
    pub(crate) fn instantiate_modular_predicates(&self, vars: &[ChcVar]) -> Vec<ChcExpr> {
        let mut candidates: FxHashSet<ChcExpr> = FxHashSet::default();
        let mut int_vars: Vec<ChcVar> = vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .cloned()
            .collect();
        int_vars.sort_by(|a, b| a.name.cmp(&b.name));

        for k in self.modular_divisors() {
            for v in &int_vars {
                let mod_expr = ChcExpr::mod_op(ChcExpr::var(v.clone()), ChcExpr::int(k));
                for c in 0..k {
                    candidates.insert(ChcExpr::eq(mod_expr.clone(), ChcExpr::int(c)));
                }
            }
        }

        let mut out: Vec<ChcExpr> = candidates.into_iter().collect();
        out.sort_by_cached_key(ToString::to_string);
        out
    }

    fn modular_divisors(&self) -> Vec<i128> {
        let mut mod_divisors: FxHashSet<i128> = FxHashSet::default();
        mod_divisors.insert(2);
        mod_divisors.insert(3);

        for &k in &self.coefficients {
            if let Some(abs_k) = Self::bounded_modulus(k) {
                mod_divisors.insert(abs_k);
            }
        }

        for &c in &self.constants {
            if let Some(abs_c) = Self::bounded_modulus(c) {
                mod_divisors.insert(abs_c);
            }
        }

        let mut sorted_divisors: Vec<i128> = mod_divisors.into_iter().collect();
        sorted_divisors.sort_unstable();
        sorted_divisors
    }

    fn bounded_modulus(value: i128) -> Option<i128> {
        const MAX_MODULUS: i128 = 16;

        let abs_value = value.checked_abs()?;
        (abs_value > 1 && abs_value <= MAX_MODULUS).then_some(abs_value)
    }

    fn collect_from_clause(
        clause: &HornClause,
        comparisons: &mut FxHashSet<ChcExpr>,
        constants: &mut FxHashSet<i128>,
    ) {
        for (_, args) in &clause.body.predicates {
            for arg in args {
                Self::collect_constants_from_expr(arg, constants);
            }
        }

        if let Some(c) = &clause.body.constraint {
            Self::collect_from_constraint_expr(c, comparisons, constants);
        }

        match &clause.head {
            ClauseHead::Predicate(_, args) => {
                for arg in args {
                    Self::collect_constants_from_expr(arg, constants);
                }
            }
            ClauseHead::False => {}
        }
    }

    fn collect_from_constraint_expr(
        expr: &ChcExpr,
        comparisons: &mut FxHashSet<ChcExpr>,
        constants: &mut FxHashSet<i128>,
    ) {
        let normalized = expr
            .normalize_negations()
            .normalize_strict_int_comparisons()
            .simplify_constants();
        Self::walk_expr(&normalized, comparisons, constants);
    }

    fn walk_expr(
        expr: &ChcExpr,
        comparisons: &mut FxHashSet<ChcExpr>,
        constants: &mut FxHashSet<i128>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(_) => {}
            ChcExpr::Int(n) => {
                constants.insert(*n);
            }
            ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {}
            ChcExpr::Var(_) => {}
            ChcExpr::Op(op, args) => {
                if matches!(
                    op,
                    ChcOp::Eq | ChcOp::Ne | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                ) {
                    comparisons.insert(expr.clone());
                }
                for a in args {
                    Self::walk_expr(a.as_ref(), comparisons, constants);
                }
            }
            ChcExpr::PredicateApp(_, _, args) => {
                for a in args {
                    Self::walk_expr(a.as_ref(), comparisons, constants);
                }
            }
            ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    Self::walk_expr(a.as_ref(), comparisons, constants);
                }
            }
            ChcExpr::ConstArrayMarker(_) => {}
            ChcExpr::IsTesterMarker(_) => {}
            ChcExpr::ConstArray(_ks, v) => Self::walk_expr(v.as_ref(), comparisons, constants),
        });
    }

    /// Extract multiplication coefficients from expressions.
    /// E.g., `(* 5 C)` yields coefficient 5, `(* (- 1) B)` yields -1.
    fn collect_coefficients(expr: &ChcExpr, coefficients: &mut FxHashSet<i128>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                // Check for (int * var) or (var * int)
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Int(k), ChcExpr::Var(_)) | (ChcExpr::Var(_), ChcExpr::Int(k)) => {
                        coefficients.insert(*k);
                        // Also insert the negation for flexibility
                        coefficients.insert(-*k);
                    }
                    _ => {}
                }
                // Recurse into subexpressions
                for a in args {
                    Self::collect_coefficients(a, coefficients);
                }
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_coefficients(a, coefficients);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    Self::collect_coefficients(a, coefficients);
                }
            }
            _ => {}
        });
    }

    fn collect_constants_from_expr(expr: &ChcExpr, constants: &mut FxHashSet<i128>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => {
                constants.insert(*n);
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    Self::collect_constants_from_expr(a.as_ref(), constants);
                }
            }
            ChcExpr::PredicateApp(_, _, args) => {
                for a in args {
                    Self::collect_constants_from_expr(a.as_ref(), constants);
                }
            }
            ChcExpr::FuncApp(_, _, args) => {
                for a in args {
                    Self::collect_constants_from_expr(a.as_ref(), constants);
                }
            }
            ChcExpr::ConstArray(_ks, v) => Self::collect_constants_from_expr(v.as_ref(), constants),
            ChcExpr::Bool(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        });
    }

    fn cap_constants(mut constants: FxHashSet<i128>, max: usize) -> FxHashSet<i128> {
        if constants.len() <= max {
            return constants;
        }

        // Always keep these if present.
        let must_keep = [0i128, 1, -1, 2, -2];
        let mut keep: FxHashSet<i128> = FxHashSet::default();
        for c in must_keep {
            if keep.len() >= max {
                break;
            }
            if constants.contains(&c) {
                keep.insert(c);
            }
        }

        let mut rest: Vec<i128> = constants.drain().collect();
        rest.sort_by_key(|c| (c.unsigned_abs(), *c));

        for c in rest {
            if keep.len() >= max {
                break;
            }
            keep.insert(c);
        }

        keep
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "qualifier_tests.rs"]
mod tests;
