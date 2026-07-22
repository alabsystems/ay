// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear constraint types and parsing for Farkas combination.
//!
//! Provides `LinearConstraint`, parsing from `ChcExpr`, checked Rational64
//! arithmetic, integer bound extraction, and floor/ceil rounding.

use crate::expr::walk_linear_expr;
use crate::{ChcExpr, ChcOp, ChcSort};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_rational::Rational64;

/// Checked addition for Rational64 that returns None on i64 overflow.
///
/// Rational64 operations internally cross-multiply numerators and
/// denominators, which can overflow i64. With `panic = "abort"` in
/// release, this causes a hard crash. This function detects overflow
/// via i128 intermediates before performing the operation.
pub(crate) fn checked_r64_add(a: Rational64, b: Rational64) -> Option<Rational64> {
    let an = i128::from(*a.numer());
    let ad = i128::from(*a.denom());
    let bn = i128::from(*b.numer());
    let bd = i128::from(*b.denom());
    // a/ad + b/bd = (an*bd + bn*ad) / (ad*bd)
    let num = an.checked_mul(bd)?.checked_add(bn.checked_mul(ad)?)?;
    let den = ad.checked_mul(bd)?;
    let num_i64 = i64::try_from(num).ok()?;
    let den_i64 = i64::try_from(den).ok()?;
    if den_i64 == 0 {
        return None;
    }
    Some(Rational64::new(num_i64, den_i64))
}

/// Checked multiplication for Rational64 that returns None on i64 overflow.
pub(crate) fn checked_r64_mul(a: Rational64, b: Rational64) -> Option<Rational64> {
    let an = i128::from(*a.numer());
    let ad = i128::from(*a.denom());
    let bn = i128::from(*b.numer());
    let bd = i128::from(*b.denom());
    let num = an.checked_mul(bn)?;
    let den = ad.checked_mul(bd)?;
    let num_i64 = i64::try_from(num).ok()?;
    let den_i64 = i64::try_from(den).ok()?;
    if den_i64 == 0 {
        return None;
    }
    Some(Rational64::new(num_i64, den_i64))
}

/// Checked negation for Rational64 that returns None on i64::MIN.
pub(super) fn checked_r64_neg(a: Rational64) -> Option<Rational64> {
    let n = (*a.numer()).checked_neg()?;
    Some(Rational64::new(n, *a.denom()))
}

/// Checked division for Rational64 that returns None on i64 overflow or division by zero.
pub(super) fn checked_r64_div(a: Rational64, b: Rational64) -> Option<Rational64> {
    let an = i128::from(*a.numer());
    let ad = i128::from(*a.denom());
    let bn = i128::from(*b.numer());
    let bd = i128::from(*b.denom());
    if bn == 0 {
        return None;
    }
    let num = an.checked_mul(bd)?;
    let den = ad.checked_mul(bn)?;
    let num_i64 = i64::try_from(num).ok()?;
    let den_i64 = i64::try_from(den).ok()?;
    if den_i64 == 0 {
        return None;
    }
    Some(Rational64::new(num_i64, den_i64))
}

/// A linear constraint in the form: Σᵢ aᵢ·xᵢ ≤ b (or < for strict)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LinearConstraint {
    /// Variable name -> coefficient
    pub(crate) coeffs: FxHashMap<String, Rational64>,
    /// Constant bound (RHS)
    pub(crate) bound: Rational64,
    /// Whether this is strict (< vs ≤)
    pub(crate) strict: bool,
    /// Arithmetic sort of the variables in this constraint (`Int` or `Real`).
    ///
    /// LRA-Lin unlock (#chc25-lra-convergence): the exact-rational Farkas
    /// machinery is sort-agnostic, but the emitted interpolant atom must carry
    /// the ORIGINAL variable sort — emitting an `Int`-sorted atom over `Real`
    /// state variables mis-types the Craig-validation query and the candidate
    /// is silently rejected. This field records the domain observed during
    /// parsing (defaults to `Int` for byte-identical LIA behaviour) and is
    /// propagated through Fourier-Motzkin / pairwise elimination so
    /// `build_linear_inequality_sorted` reconstructs `Real` atoms for LRA.
    pub(crate) var_sort: ChcSort,
}

impl LinearConstraint {
    pub(super) fn new(bound: Rational64, strict: bool) -> Self {
        Self {
            coeffs: FxHashMap::default(),
            bound,
            strict,
            var_sort: ChcSort::Int,
        }
    }

    /// The sort to use when emitting a constraint derived by combining `a` and
    /// `b`: `Real` if either operand is over the reals, else `Int`. Both
    /// operands share the same arithmetic domain in every live caller
    /// (a single interpolation query is over one theory), so this is just a
    /// defensive `Real`-dominates merge.
    pub(super) fn merged_sort(a: &Self, b: &Self) -> ChcSort {
        if matches!(a.var_sort, ChcSort::Real) || matches!(b.var_sort, ChcSort::Real) {
            ChcSort::Real
        } else {
            ChcSort::Int
        }
    }

    pub(super) fn set_coeff(&mut self, var: &str, coeff: Rational64) {
        if coeff == Rational64::from_integer(0) {
            self.coeffs.remove(var);
        } else {
            self.coeffs.insert(var.to_string(), coeff);
        }
    }

    pub(crate) fn get_coeff(&self, var: &str) -> Rational64 {
        self.coeffs
            .get(var)
            .copied()
            .unwrap_or(Rational64::from_integer(0))
    }
}

/// Try to parse a ChcExpr as a linear constraint.
/// Returns None if the expression is not a linear inequality.
pub(crate) fn parse_linear_constraint(expr: &ChcExpr) -> Option<LinearConstraint> {
    match expr {
        // a ≤ b  =>  a - b ≤ 0
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
            add_linear_expr(&args[0], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[1], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a < b  =>  a - b < 0
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
            add_linear_expr(&args[0], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[1], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a ≥ b  =>  b - a ≤ 0
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
            add_linear_expr(&args[1], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[0], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a > b  =>  b - a < 0
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
            add_linear_expr(&args[1], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[0], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a = b  =>  a - b ≤ 0 AND b - a ≤ 0 (we return one direction)
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            // For equalities, we treat as a <= b (caller may want both directions)
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
            add_linear_expr(&args[0], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[1], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // Handle negated comparisons
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            match args[0].as_ref() {
                // NOT(a ≤ b)  =>  a > b  =>  b - a < 0
                ChcExpr::Op(ChcOp::Le, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
                    add_linear_expr(&inner_args[1], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[0],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                // NOT(a < b)  =>  a ≥ b  =>  b - a ≤ 0
                ChcExpr::Op(ChcOp::Lt, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
                    add_linear_expr(&inner_args[1], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[0],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                // NOT(a ≥ b)  =>  a < b  =>  a - b < 0
                ChcExpr::Op(ChcOp::Ge, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
                    add_linear_expr(&inner_args[0], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[1],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                // NOT(a > b)  =>  a ≤ b  =>  a - b ≤ 0
                ChcExpr::Op(ChcOp::Gt, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
                    add_linear_expr(&inner_args[0], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[1],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Parse a ChcExpr as zero or more linear constraints.
/// Recursively flattens conjunctions and returns every parseable member.
///
/// Production callers moved to the sort-generic `parse_linear_constraints_flat_any`;
/// this `Rational64` form is kept only for the pinned tests in `farkas/tests.rs`
/// (see the `#[cfg(test)]` re-export in `farkas/mod.rs`).
#[cfg(test)]
pub(crate) fn parse_linear_constraints_flat(expr: &ChcExpr) -> Vec<LinearConstraint> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .flat_map(|arg| parse_linear_constraints_flat(arg))
            .collect(),
        _ => parse_linear_constraint(expr).into_iter().collect(),
    }
}

/// Parse a linear constraint, splitting equalities into both directions.
/// `a = b` becomes `[a - b <= 0, b - a <= 0]`.
/// Non-equalities return a single constraint (or empty if not parseable).
pub(crate) fn parse_linear_constraints_split_eq(expr: &ChcExpr) -> Vec<LinearConstraint> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .flat_map(|arg| parse_linear_constraints_split_eq(arg))
            .collect(),
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            let mut results = Vec::new();
            // Direction 1: a - b <= 0
            let mut c1 = LinearConstraint::new(Rational64::from_integer(0), false);
            if add_linear_expr(&args[0], Rational64::from_integer(1), &mut c1).is_some()
                && add_linear_expr(&args[1], Rational64::from_integer(-1), &mut c1).is_some()
            {
                results.push(c1);
            }
            // Direction 2: b - a <= 0
            let mut c2 = LinearConstraint::new(Rational64::from_integer(0), false);
            if add_linear_expr(&args[1], Rational64::from_integer(1), &mut c2).is_some()
                && add_linear_expr(&args[0], Rational64::from_integer(-1), &mut c2).is_some()
            {
                results.push(c2);
            }
            results
        }
        _ => parse_linear_constraint(expr).into_iter().collect(),
    }
}

/// Add a linear expression to a constraint with a multiplier.
/// Returns None if the expression is not linear.
fn add_linear_expr(
    expr: &ChcExpr,
    mult: Rational64,
    constraint: &mut LinearConstraint,
) -> Option<()> {
    // Split borrows so both closures can access disjoint fields.
    let bound = &mut constraint.bound;
    let coeffs = &mut constraint.coeffs;
    walk_linear_expr(
        expr,
        mult,
        &mut |m, n| {
            // i128-lockstep: Rational64 is i64-backed; constants beyond i64
            // decline linear-constraint parsing (fail-closed), never truncate.
            let term = checked_r64_mul(m, Rational64::from_integer(i64::try_from(n).ok()?))?;
            *bound = checked_r64_add(*bound, checked_r64_neg(term)?)?;
            Some(())
        },
        &mut |m, v| {
            if !matches!(v.sort, ChcSort::Int) {
                return None;
            }
            let zero = Rational64::from_integer(0);
            let current = coeffs.get(&v.name).copied().unwrap_or(zero);
            let new_val = checked_r64_add(current, m)?;
            if new_val == zero {
                coeffs.remove(&v.name);
            } else {
                coeffs.insert(v.name.clone(), new_val);
            }
            Some(())
        },
    )
}

// ---------------------------------------------------------------------------
// LRA-Lin (Real arithmetic) linear parsing — #chc25-lra-convergence.
//
// The `walk_linear_expr` walker used by `add_linear_expr` is Int-only: it
// rejects `ChcExpr::Real` literals and `Real`-constant coefficients
// (`(* (- 1.0) v)`, pervasive in the sally / vmt-cav12 LRA transition systems),
// and `add_linear_expr` additionally gates variables to `ChcSort::Int`. The
// net effect is that EVERY Farkas-family interpolation strategy returns
// `no_candidate` on LRA queries, starving the IMC / LAWI / DAR / CEGAR / PDR
// interpolation lanes and leaving only weak dual-MBP interpolants — the
// measured non-convergence cause for CHC-COMP LRA-Lin.
//
// The functions below provide a self-contained exact-rational parser used ONLY
// by the interpolant entry point (`compute_interpolant_until`). They never
// touch the Int path: `parse_linear_constraint_any` tries the existing Int
// parser first (byte-identical for LIA) and only falls back to the rational
// parser for constraints the Int parser rejects. Soundness is unchanged —
// every emitted candidate is still Craig-validated by `is_valid_interpolant*`
// over the actual (Real) theory before use.
// ---------------------------------------------------------------------------

/// Fold a variable-free arithmetic expression to an exact rational.
///
/// Returns `None` if the expression mentions a variable or a node this linear
/// evaluator does not model (fail-closed — the caller declines the parse).
/// `Rational64` is i64-backed, so out-of-range integer literals also decline
/// (never truncate), matching the i128-lockstep discipline of the Int path.
fn fold_const_rational(expr: &ChcExpr) -> Option<Rational64> {
    match expr {
        ChcExpr::Int(n) => Some(Rational64::from_integer(i64::try_from(*n).ok()?)),
        ChcExpr::Real(n, d) => {
            if *d == 0 {
                return None;
            }
            Some(Rational64::new(*n, *d))
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            checked_r64_neg(fold_const_rational(&args[0])?)
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut acc = Rational64::from_integer(0);
            for a in args {
                acc = checked_r64_add(acc, fold_const_rational(a)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut acc = fold_const_rational(&args[0])?;
            for a in &args[1..] {
                acc = checked_r64_add(acc, checked_r64_neg(fold_const_rational(a)?)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut acc = Rational64::from_integer(1);
            for a in args {
                acc = checked_r64_mul(acc, fold_const_rational(a)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => checked_r64_div(
            fold_const_rational(&args[0])?,
            fold_const_rational(&args[1])?,
        ),
        _ => None,
    }
}

/// Add a linear expression to a constraint with a rational multiplier,
/// accepting both `Int` and `Real` variables and `Real` coefficients/literals.
///
/// Sets `constraint.var_sort = Real` when any `Real`-sorted variable is seen so
/// the eventual emission reconstructs `Real` atoms. Returns `None` on any
/// non-linear or unmodelled node (fail-closed).
fn add_linear_expr_rational(
    expr: &ChcExpr,
    mult: Rational64,
    constraint: &mut LinearConstraint,
) -> Option<()> {
    match expr {
        ChcExpr::Var(v) => {
            match v.sort {
                ChcSort::Int => {}
                ChcSort::Real => constraint.var_sort = ChcSort::Real,
                _ => return None,
            }
            let zero = Rational64::from_integer(0);
            let current = constraint.coeffs.get(&v.name).copied().unwrap_or(zero);
            let new_val = checked_r64_add(current, mult)?;
            if new_val == zero {
                constraint.coeffs.remove(&v.name);
            } else {
                constraint.coeffs.insert(v.name.clone(), new_val);
            }
            Some(())
        }
        ChcExpr::Int(_) | ChcExpr::Real(_, _) => {
            let c = fold_const_rational(expr)?;
            let term = checked_r64_mul(mult, c)?;
            constraint.bound = checked_r64_add(constraint.bound, checked_r64_neg(term)?)?;
            Some(())
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            for a in args {
                add_linear_expr_rational(a, mult, constraint)?;
            }
            Some(())
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            add_linear_expr_rational(&args[0], mult, constraint)?;
            let neg_mult = checked_r64_neg(mult)?;
            for a in &args[1..] {
                add_linear_expr_rational(a, neg_mult, constraint)?;
            }
            Some(())
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            add_linear_expr_rational(&args[0], checked_r64_neg(mult)?, constraint)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            // Exactly one factor must be a constant (else it is non-linear).
            if let Some(c) = fold_const_rational(&args[0]) {
                add_linear_expr_rational(&args[1], checked_r64_mul(mult, c)?, constraint)
            } else if let Some(c) = fold_const_rational(&args[1]) {
                add_linear_expr_rational(&args[0], checked_r64_mul(mult, c)?, constraint)
            } else {
                None
            }
        }
        ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
            // Division by a constant is linear; a variable divisor is not.
            let c = fold_const_rational(&args[1])?;
            add_linear_expr_rational(&args[0], checked_r64_div(mult, c)?, constraint)
        }
        _ => None,
    }
}

/// Build `a - b <op> 0` over the rationals (`op` is `<` if `strict` else `≤`).
fn cmp_to_constraint_rational(a: &ChcExpr, b: &ChcExpr, strict: bool) -> Option<LinearConstraint> {
    let mut c = LinearConstraint::new(Rational64::from_integer(0), strict);
    add_linear_expr_rational(a, Rational64::from_integer(1), &mut c)?;
    add_linear_expr_rational(b, Rational64::from_integer(-1), &mut c)?;
    Some(c)
}

/// Exact-rational analogue of [`parse_linear_constraint`] that admits `Real`
/// variables/coefficients. Mirrors the Int parser's comparison normalisation
/// exactly (same negation directions), so results agree with the Int parser on
/// pure-LIA input.
fn parse_linear_constraint_rational(expr: &ChcExpr) -> Option<LinearConstraint> {
    match expr {
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            cmp_to_constraint_rational(&args[0], &args[1], false)
        }
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            cmp_to_constraint_rational(&args[0], &args[1], true)
        }
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            cmp_to_constraint_rational(&args[1], &args[0], false)
        }
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            cmp_to_constraint_rational(&args[1], &args[0], true)
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            cmp_to_constraint_rational(&args[0], &args[1], false)
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
            // NOT(a ≤ b)  =>  b < a
            ChcExpr::Op(ChcOp::Le, ia) if ia.len() == 2 => {
                cmp_to_constraint_rational(&ia[1], &ia[0], true)
            }
            // NOT(a < b)  =>  b ≤ a
            ChcExpr::Op(ChcOp::Lt, ia) if ia.len() == 2 => {
                cmp_to_constraint_rational(&ia[1], &ia[0], false)
            }
            // NOT(a ≥ b)  =>  a < b
            ChcExpr::Op(ChcOp::Ge, ia) if ia.len() == 2 => {
                cmp_to_constraint_rational(&ia[0], &ia[1], true)
            }
            // NOT(a > b)  =>  a ≤ b
            ChcExpr::Op(ChcOp::Gt, ia) if ia.len() == 2 => {
                cmp_to_constraint_rational(&ia[0], &ia[1], false)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Int-first parse that falls back to the exact-rational parser for
/// constraints the Int parser rejects (i.e. those over `Real`). Pure-LIA input
/// is handled entirely by the existing Int parser (byte-identical).
pub(crate) fn parse_linear_constraint_any(expr: &ChcExpr) -> Option<LinearConstraint> {
    parse_linear_constraint(expr).or_else(|| parse_linear_constraint_rational(expr))
}

/// Real-aware analogue of [`parse_linear_constraints_flat`].
pub(crate) fn parse_linear_constraints_flat_any(expr: &ChcExpr) -> Vec<LinearConstraint> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .flat_map(|arg| parse_linear_constraints_flat_any(arg))
            .collect(),
        _ => parse_linear_constraint_any(expr).into_iter().collect(),
    }
}

/// Real-aware analogue of [`parse_linear_constraints_split_eq`]: splits an
/// equality into both `≤` directions using whichever parser (Int or rational)
/// applies.
pub(crate) fn parse_linear_constraints_split_eq_any(expr: &ChcExpr) -> Vec<LinearConstraint> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .flat_map(|arg| parse_linear_constraints_split_eq_any(arg))
            .collect(),
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            // Int split first (byte-identical for LIA); rational split only when
            // the Int parser declined (Real operands).
            let int_split = parse_linear_constraints_split_eq(expr);
            if !int_split.is_empty() {
                return int_split;
            }
            let mut results = Vec::new();
            if let Some(c1) = cmp_to_constraint_rational(&args[0], &args[1], false) {
                results.push(c1);
            }
            if let Some(c2) = cmp_to_constraint_rational(&args[1], &args[0], false) {
                results.push(c2);
            }
            results
        }
        _ => parse_linear_constraint_any(expr).into_iter().collect(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum IntBound {
    Lower(i64),
    Upper(i64),
}

pub(super) fn floor_rational64(r: Rational64) -> Option<i64> {
    let n = i128::from(*r.numer());
    let d = i128::from(*r.denom());
    // Denominator must be positive for correct Euclidean division (#3095).
    if d <= 0 {
        safe_eprintln!("BUG: floor_rational64: non-positive denominator {d}");
        return None;
    }
    i64::try_from(n.div_euclid(d)).ok()
}

pub(super) fn ceil_rational64(r: Rational64) -> Option<i64> {
    let n = i128::from(*r.numer());
    let d = i128::from(*r.denom());
    // Denominator must be positive for correct Euclidean division (#3095).
    if d <= 0 {
        safe_eprintln!("BUG: ceil_rational64: non-positive denominator {d}");
        return None;
    }
    i64::try_from(-((-n).div_euclid(d))).ok()
}

pub(super) fn linear_constraint_to_int_bound(c: &LinearConstraint) -> Option<(String, IntBound)> {
    if c.coeffs.len() != 1 {
        return None;
    }
    let (var, coeff) = c.coeffs.iter().next()?;
    if *coeff == Rational64::from_integer(0) {
        return None;
    }

    // c is: coeff * x <= bound (or < if strict).
    // Divide by coeff to isolate x, taking care with strictness/rounding over Int.
    let r = checked_r64_div(c.bound, *coeff)?;
    if *coeff > Rational64::from_integer(0) {
        // x <= r  (or x < r if strict)
        let upper = if c.strict {
            // x < r  over Int  =>  x <= ceil(r) - 1
            let ceil_r = i128::from(ceil_rational64(r)?);
            i64::try_from(ceil_r - 1).ok()?
        } else {
            // x <= r  over Int  =>  x <= floor(r)
            floor_rational64(r)?
        };
        Some((var.clone(), IntBound::Upper(upper)))
    } else {
        // x >= r  (or x > r if strict)
        let lower = if c.strict {
            // x > r  over Int  =>  x >= floor(r) + 1
            let floor_r = i128::from(floor_rational64(r)?);
            i64::try_from(floor_r + 1).ok()?
        } else {
            // x >= r  over Int  =>  x >= ceil(r)
            ceil_rational64(r)?
        };
        Some((var.clone(), IntBound::Lower(lower)))
    }
}
