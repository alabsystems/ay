// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::farkas::checked_r64_add;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_rational::Rational64;

/// Compute a simple bound interpolant from A and B constraints.
///
/// Looks for cases where A implies a bound on a shared variable
/// that contradicts B.
pub(super) fn compute_bound_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    // Extract bounds from A constraints.
    let a_bounds = extract_variable_bounds(a_constraints);

    // Extract bounds from B constraints.
    let b_bounds = extract_variable_bounds(b_constraints);

    // Look for contradicting bounds on shared variables.
    for (var, (a_lower, a_upper)) in &a_bounds {
        if !shared_vars.contains(var) {
            continue;
        }

        if let Some((b_lower, b_upper)) = b_bounds.get(var) {
            // A says var >= a_lower, B says var < b_upper where b_upper <= a_lower.
            if let (Some(a_lb), Some(b_ub)) = (a_lower, b_upper) {
                if *b_ub < *a_lb {
                    let v = ChcVar::new(var, ChcSort::Int);
                    return Some(ChcExpr::ge(ChcExpr::var(v), ChcExpr::Int(*a_lb)));
                }
            }

            // A says var <= a_upper, B says var > b_lower where b_lower >= a_upper.
            if let (Some(a_ub), Some(b_lb)) = (a_upper, b_lower) {
                if *b_lb > *a_ub {
                    let v = ChcVar::new(var, ChcSort::Int);
                    return Some(ChcExpr::le(ChcExpr::var(v), ChcExpr::Int(*a_ub)));
                }
            }
        }
    }

    // Real-aware fallback (#chc25-lra-convergence, STEP 1): exact-rational bound
    // conflict over ℝ. The Int arms above are byte-identical for LIA and run
    // first; this path fires only on `Real`-sorted variables the Int extractor
    // declines. Strictness is carried EXACTLY (never folded via ±1 rounding —
    // that rounding is unsound over ℝ, cf. farkas Strategy 4). Every emitted
    // atom is still Craig-validated by the caller before use.
    compute_bound_interpolant_real(a_constraints, b_constraints, shared_vars)
}

/// Exact rational value of a literal constant (`Int` or `Real`); `None` for any
/// non-literal (fail-closed). `Rational64` is i64-backed, so out-of-range
/// integer literals decline rather than truncate.
fn literal_const_rational(expr: &ChcExpr) -> Option<Rational64> {
    match expr {
        ChcExpr::Int(c) => Some(Rational64::from_integer(i64::try_from(*c).ok()?)),
        ChcExpr::Real(n, d) => {
            if *d == 0 {
                return None;
            }
            Some(Rational64::new(*n, *d))
        }
        _ => None,
    }
}

/// Emit a `Real`-sorted rational constant atom operand.
fn real_const(r: Rational64) -> ChcExpr {
    ChcExpr::Real(*r.numer(), *r.denom())
}

/// A directional bound on one variable: the value and whether it is strict.
type RatBound = (Rational64, bool);

/// Lower/upper rational bounds on a single variable, plus its arithmetic sort.
#[derive(Clone)]
struct RationalVarBounds {
    lower: Option<RatBound>,
    upper: Option<RatBound>,
    sort: ChcSort,
}

impl RationalVarBounds {
    fn new(sort: ChcSort) -> Self {
        Self {
            lower: None,
            upper: None,
            sort,
        }
    }

    /// Tighten the lower bound: keep the larger value; on a tie prefer strict.
    fn add_lower(&mut self, value: Rational64, strict: bool) {
        self.lower = Some(match self.lower {
            Some((cur, cur_strict)) if cur > value => (cur, cur_strict),
            Some((cur, cur_strict)) if cur == value => (cur, cur_strict || strict),
            _ => (value, strict),
        });
    }

    /// Tighten the upper bound: keep the smaller value; on a tie prefer strict.
    fn add_upper(&mut self, value: Rational64, strict: bool) {
        self.upper = Some(match self.upper {
            Some((cur, cur_strict)) if cur < value => (cur, cur_strict),
            Some((cur, cur_strict)) if cur == value => (cur, cur_strict || strict),
            _ => (value, strict),
        });
    }
}

/// Extract a rational bound `var <op> c` (or `c <op> var`) with exact value,
/// strictness, and the variable's sort. Admits `Int` and `Real` variables and
/// literal constants. Returns `(var, value, is_upper, strict, sort)`.
fn extract_simple_bound_rational(
    expr: &ChcExpr,
) -> Option<(String, Rational64, bool, bool, ChcSort)> {
    let arith = |s: &ChcSort| matches!(s, ChcSort::Int | ChcSort::Real);
    match expr {
        ChcExpr::Op(op @ (ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt), args)
            if args.len() == 2 =>
        {
            let strict = matches!(op, ChcOp::Lt | ChcOp::Gt);
            // Normalize to `var <op> c`: is_upper true for Le/Lt (var <= / < c),
            // false for Ge/Gt. When the constant is on the LHS the direction
            // flips.
            let upper_when_var_lhs = matches!(op, ChcOp::Le | ChcOp::Lt);
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), rhs) if arith(&v.sort) => {
                    let c = literal_const_rational(rhs)?;
                    Some((
                        v.name.clone(),
                        c,
                        upper_when_var_lhs,
                        strict,
                        v.sort.clone(),
                    ))
                }
                (lhs, ChcExpr::Var(v)) if arith(&v.sort) => {
                    let c = literal_const_rational(lhs)?;
                    Some((
                        v.name.clone(),
                        c,
                        !upper_when_var_lhs,
                        strict,
                        v.sort.clone(),
                    ))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Build per-variable rational bounds from a constraint list. Equalities set
/// both a lower and an upper bound at the same value (tighter than the Int
/// extractor, which records equalities as a lower bound only).
fn extract_variable_bounds_rational(
    constraints: &[ChcExpr],
) -> FxHashMap<String, RationalVarBounds> {
    let arith = |s: &ChcSort| matches!(s, ChcSort::Int | ChcSort::Real);
    let mut bounds: FxHashMap<String, RationalVarBounds> = FxHashMap::default();

    for c in constraints {
        // Equality `var = const` (either operand order) → both bounds.
        if let ChcExpr::Op(ChcOp::Eq, args) = c {
            if args.len() == 2 {
                let eq =
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), rhs) if arith(&v.sort) => literal_const_rational(rhs)
                            .map(|val| (v.name.clone(), val, v.sort.clone())),
                        (lhs, ChcExpr::Var(v)) if arith(&v.sort) => literal_const_rational(lhs)
                            .map(|val| (v.name.clone(), val, v.sort.clone())),
                        _ => None,
                    };
                if let Some((name, val, sort)) = eq {
                    let entry = bounds
                        .entry(name)
                        .or_insert_with(|| RationalVarBounds::new(sort));
                    entry.add_lower(val, false);
                    entry.add_upper(val, false);
                    continue;
                }
            }
        }

        if let Some((var, val, is_upper, strict, sort)) = extract_simple_bound_rational(c) {
            let entry = bounds
                .entry(var)
                .or_insert_with(|| RationalVarBounds::new(sort));
            if is_upper {
                entry.add_upper(val, strict);
            } else {
                entry.add_lower(val, strict);
            }
        }
    }

    bounds
}

/// Real-only exact-rational bound-conflict interpolant. Emits a `Real`-sorted
/// atom (`var >= c` / `var > c` / `var <= c` / `var < c`) that is implied by A
/// and inconsistent with B. Sound by Craig validation in the caller.
fn compute_bound_interpolant_real(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let a_bounds = extract_variable_bounds_rational(a_constraints);
    let b_bounds = extract_variable_bounds_rational(b_constraints);

    for (var, a) in &a_bounds {
        if !shared_vars.contains(var) || !matches!(a.sort, ChcSort::Real) {
            continue;
        }
        let Some(b) = b_bounds.get(var) else {
            continue;
        };

        // A: var >= a_lb, B: var <= b_ub — contradiction if b_ub < a_lb, or
        // equal with either side strict. Emit A's lower bound.
        if let (Some((a_lb, a_strict)), Some((b_ub, b_strict))) = (a.lower, b.upper) {
            if b_ub < a_lb || (b_ub == a_lb && (a_strict || b_strict)) {
                let v = ChcExpr::var(ChcVar::new(var, ChcSort::Real));
                let c = real_const(a_lb);
                return Some(if a_strict {
                    ChcExpr::gt(v, c)
                } else {
                    ChcExpr::ge(v, c)
                });
            }
        }

        // A: var <= a_ub, B: var >= b_lb — contradiction if b_lb > a_ub, or
        // equal with either side strict. Emit A's upper bound.
        if let (Some((a_ub, a_strict)), Some((b_lb, b_strict))) = (a.upper, b.lower) {
            if b_lb > a_ub || (b_lb == a_ub && (a_strict || b_strict)) {
                let v = ChcExpr::var(ChcVar::new(var, ChcSort::Real));
                let c = real_const(a_ub);
                return Some(if a_strict {
                    ChcExpr::lt(v, c)
                } else {
                    ChcExpr::le(v, c)
                });
            }
        }
    }

    None
}

/// Compute a transitivity-based interpolant.
///
/// For constraint chains like: A says x <= y, B says y < x,
/// derive contradiction and produce interpolant involving shared variables.
pub(super) fn compute_transitivity_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    // Extract relational constraints from A (x <= y + c, x < y + c, etc.).
    let a_relations = extract_relational_constraints(a_constraints);

    // Extract relational constraints from B.
    let b_relations = extract_relational_constraints(b_constraints);

    // Look for transitivity contradictions.
    // A: x - y <= c1, B: y - x <= c2 where c1 + c2 < 0 is contradiction.
    for (a_vars, a_bound) in &a_relations {
        if a_vars.0 == a_vars.1 {
            continue;
        }

        // Look for opposite relation in B.
        let opposite = (a_vars.1.clone(), a_vars.0.clone());
        for (b_vars, b_bound) in &b_relations {
            if *b_vars == opposite
                && a_bound.checked_add(*b_bound).is_some_and(|s| s < 0)
                && shared_vars.contains(&a_vars.0)
                && shared_vars.contains(&a_vars.1)
            {
                let x = ChcVar::new(&a_vars.0, ChcSort::Int);
                let y = ChcVar::new(&a_vars.1, ChcSort::Int);
                return Some(ChcExpr::le(
                    ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y)),
                    ChcExpr::Int(*a_bound),
                ));
            }
        }
    }

    // Real-aware fallback (#chc25-lra-convergence, STEP 1): exact-rational
    // difference-bound (transitivity) conflict over ℝ. Int arms above run first
    // and are byte-identical for LIA; this fires only on `Real` difference
    // constraints. Craig-validated by the caller.
    compute_transitivity_interpolant_real(a_constraints, b_constraints, shared_vars)
}

/// Real difference constraint `x - y <op> c` with exact value, strictness, and
/// sort. Returns `((x, y), c, strict, sort)` meaning `x - y <= c` (or `<`).
fn extract_difference_constraint_rational(
    expr: &ChcExpr,
) -> Option<((String, String), Rational64, bool, ChcSort)> {
    match expr {
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            extract_difference_lhs_rational(&args[0], &args[1], false)
        }
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            extract_difference_lhs_rational(&args[0], &args[1], true)
        }
        // y >= x + ... i.e. args[0] >= args[1]  =>  args[1] - args[0] <= 0
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            extract_difference_lhs_rational(&args[1], &args[0], false)
        }
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            extract_difference_lhs_rational(&args[1], &args[0], true)
        }
        _ => None,
    }
}

/// Parse `x - y <op> c` from a comparison's LHS (`Sub(x, y)`) and RHS constant.
fn extract_difference_lhs_rational(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    strict: bool,
) -> Option<((String, String), Rational64, bool, ChcSort)> {
    let c = literal_const_rational(rhs)?;
    match lhs {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(x), ChcExpr::Var(y))
                    if matches!(x.sort, ChcSort::Real) && matches!(y.sort, ChcSort::Real) =>
                {
                    Some(((x.name.clone(), y.name.clone()), c, strict, x.sort.clone()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Real-only exact-rational transitivity interpolant. A: `x - y <= c1`,
/// B: `y - x <= c2` contradict when `c1 + c2 < 0` (or `= 0` with either
/// strict). Emits A's `Real`-sorted difference bound `x - y <= c1` (or `<`).
fn compute_transitivity_interpolant_real(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let a_relations: Vec<((String, String), Rational64, bool, ChcSort)> = a_constraints
        .iter()
        .filter_map(extract_difference_constraint_rational)
        .collect();
    let b_relations: Vec<((String, String), Rational64, bool, ChcSort)> = b_constraints
        .iter()
        .filter_map(extract_difference_constraint_rational)
        .collect();

    for (a_vars, a_bound, a_strict, sort) in &a_relations {
        if a_vars.0 == a_vars.1
            || !shared_vars.contains(&a_vars.0)
            || !shared_vars.contains(&a_vars.1)
        {
            continue;
        }
        let opposite = (a_vars.1.clone(), a_vars.0.clone());
        for (b_vars, b_bound, b_strict, _) in &b_relations {
            if *b_vars != opposite {
                continue;
            }
            let Some(sum) = checked_r64_add(*a_bound, *b_bound) else {
                continue;
            };
            let zero = Rational64::from_integer(0);
            if sum < zero || (sum == zero && (*a_strict || *b_strict)) {
                let x = ChcExpr::var(ChcVar::new(&a_vars.0, sort.clone()));
                let y = ChcExpr::var(ChcVar::new(&a_vars.1, sort.clone()));
                let diff = ChcExpr::sub(x, y);
                let c = real_const(*a_bound);
                return Some(if *a_strict {
                    ChcExpr::lt(diff, c)
                } else {
                    ChcExpr::le(diff, c)
                });
            }
        }
    }

    None
}

/// Extract a simple bound from an expression: var <= c or var >= c.
/// Returns (variable_name, bound_value, is_upper_bound).
pub(super) fn extract_simple_bound(expr: &ChcExpr) -> Option<(String, i128, bool)> {
    match expr {
        // var <= c  OR  c <= var (=> var >= c)
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, true))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, false))
                }
                _ => None,
            }
        }
        // var < c (=> var <= c-1)  OR  c < var (=> var >= c+1)
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), c.checked_sub(1)?, true))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), c.checked_add(1)?, false))
                }
                _ => None,
            }
        }
        // var >= c  OR  c >= var (=> var <= c)
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, false))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, true))
                }
                _ => None,
            }
        }
        // var > c (=> var >= c+1)  OR  c > var (=> var <= c-1)
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), c.checked_add(1)?, false))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), c.checked_sub(1)?, true))
                }
                _ => None,
            }
        }
        // var = c  =>  var >= c AND var <= c
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) | (ChcExpr::Int(c), ChcExpr::Var(v))
                    if matches!(v.sort, ChcSort::Int) =>
                {
                    // Return as lower bound; caller should handle both.
                    Some((v.name.clone(), *c, false))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract variable bounds from a list of constraints.
/// Returns map from variable name to (Option<lower_bound>, Option<upper_bound>).
fn extract_variable_bounds(
    constraints: &[ChcExpr],
) -> FxHashMap<String, (Option<i128>, Option<i128>)> {
    let mut bounds: FxHashMap<String, (Option<i128>, Option<i128>)> = FxHashMap::default();

    for c in constraints {
        if let Some((var, bound, is_upper)) = extract_simple_bound(c) {
            let entry = bounds.entry(var).or_insert((None, None));
            if is_upper {
                entry.1 = Some(entry.1.map_or(bound, |b| b.min(bound)));
            } else {
                entry.0 = Some(entry.0.map_or(bound, |b| b.max(bound)));
            }
        }
    }

    bounds
}

/// Extract relational constraints of form x - y <= c.
/// Returns list of ((x, y), c) tuples.
fn extract_relational_constraints(constraints: &[ChcExpr]) -> Vec<((String, String), i128)> {
    let mut result = Vec::new();

    for c in constraints {
        if let Some(rel) = extract_difference_constraint(c) {
            result.push(rel);
        }
    }

    result
}

/// Extract a difference constraint: x - y <= c or x - y < c.
fn extract_difference_constraint(expr: &ChcExpr) -> Option<((String, String), i128)> {
    match expr {
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            extract_difference_lhs(&args[0], &args[1], 0)
        }
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            extract_difference_lhs(&args[0], &args[1], -1)
        }
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            // y >= x + c  =>  x - y <= -c
            extract_difference_lhs(&args[1], &args[0], 0)
                .and_then(|((x, y), c)| Some(((y, x), c.checked_neg()?)))
        }
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            extract_difference_lhs(&args[1], &args[0], -1)
                .and_then(|((x, y), c)| Some(((y, x), c.checked_neg()?)))
        }
        _ => None,
    }
}

/// Extract x - y from LHS, c from RHS.
fn extract_difference_lhs(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    adjust: i128,
) -> Option<((String, String), i128)> {
    let c = match rhs {
        ChcExpr::Int(n) => n.checked_add(adjust)?,
        _ => return None,
    };

    match lhs {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(x), ChcExpr::Var(y))
                    if matches!(x.sort, ChcSort::Int) && matches!(y.sort, ChcSort::Int) =>
                {
                    Some(((x.name.clone(), y.name.clone()), c))
                }
                _ => None,
            }
        }
        _ => None,
    }
}
