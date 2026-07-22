// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::recurrence::{ClosedForm, TriangularSystem};
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use num_rational::Rational64;
use num_traits::Zero;

/// Eliminate iteration count n to derive algebraic invariants.
pub(super) fn eliminate_iteration_count(
    system: &TriangularSystem,
    init_values: &FxHashMap<String, i128>,
) -> Vec<ChcExpr> {
    // Find a ConstantDelta variable with non-zero delta
    let n_source = system.solutions.iter().find_map(|(name, cf)| {
        if let ClosedForm::ConstantDelta { delta } = cf {
            if *delta != 0 {
                return Some((name.clone(), *delta));
            }
        }
        None
    });

    let (n_var_name, n_delta) = match n_source {
        Some(v) => v,
        None => return Vec::new(),
    };

    // i128-lockstep: this module's rational arithmetic is Rational64 (i64
    // numerators); abstain (emit no invariants) when the init value does not
    // fit i64 rather than truncating.
    let Ok(n_init) = i64::try_from(init_values.get(&n_var_name).copied().unwrap_or(0)) else {
        return Vec::new();
    };

    let mut invariants = Vec::new();

    for (var_name, closed_form) in &system.solutions {
        if let ClosedForm::Polynomial { coeffs } = closed_form {
            if let Some(inv) = build_algebraic_equality(
                var_name,
                coeffs,
                &n_var_name,
                n_init,
                n_delta,
                init_values,
            ) {
                invariants.push(inv);
            }
        }
    }

    invariants
}

/// Build an algebraic equality by substituting n and clearing denominators.
fn build_algebraic_equality(
    var_name: &str,
    coeffs: &[FxHashMap<String, Rational64>],
    n_var_name: &str,
    n_init: i64,
    n_delta: i64,
    init_values: &FxHashMap<String, i128>,
) -> Option<ChcExpr> {
    // Evaluate each coefficient with init values
    let eval_coeffs: Vec<Rational64> = coeffs
        .iter()
        .map(|coeff_map| {
            let mut val = Rational64::from_integer(0);
            for (name, c) in coeff_map {
                if name.is_empty() {
                    val += c;
                } else {
                    // i128-lockstep: Rational64 numerator is i64; abstain (skip
                    // this invariant) when an init value does not fit.
                    let init_val =
                        i64::try_from(init_values.get(name).copied().unwrap_or(0)).ok()?;
                    val += *c * Rational64::from_integer(init_val);
                }
            }
            Some(val)
        })
        .collect::<Option<Vec<_>>>()?;

    // B_n = eval_coeffs[0] + eval_coeffs[1]*n + eval_coeffs[2]*n^2 + ...
    // n = (n_var - n_init) / n_delta

    // Substitute the loop iteration variable with:
    //
    //   step = (counter - counter_init) / counter_delta
    //
    // Earlier code only handled counter_delta = 1. Countdown accumulators
    // such as n' = n - 1, sum' = sum + n still have a perfectly valid
    // polynomial invariant, but need the affine substitution step = init - n.
    let substituted = compose_polynomial_affine(
        &eval_coeffs,
        Rational64::new(1, n_delta),
        Rational64::new(-n_init, n_delta),
    );
    build_polynomial_equality(var_name, &substituted, n_var_name)
}

/// Compose polynomial P(step) with `step = scale*x + offset`.
fn compose_polynomial_affine(
    coeffs: &[Rational64],
    scale: Rational64,
    offset: Rational64,
) -> Vec<Rational64> {
    let mut result = vec![Rational64::from_integer(0); coeffs.len()];

    // For P(t) = sum_k a_k t^k and t = scale*x + offset, expand:
    // (scale*x + offset)^k = sum_j C(k,j) scale^j offset^(k-j) x^j.
    for (k, a_k) in coeffs.iter().enumerate() {
        if *a_k == Rational64::from_integer(0) {
            continue;
        }
        let mut binom = Rational64::from_integer(1); // C(k,0) = 1
        for (j, result_j) in result[..=k].iter_mut().enumerate() {
            *result_j +=
                *a_k * binom * pow_rational(scale, j as u32) * pow_rational(offset, (k - j) as u32);
            if j < k {
                binom *= Rational64::from_integer((k - j) as i64);
                binom /= Rational64::from_integer((j + 1) as i64);
            }
        }
    }

    result
}

fn pow_rational(base: Rational64, exp: u32) -> Rational64 {
    let mut result = Rational64::from_integer(1);
    for _ in 0..exp {
        result *= base;
    }
    result
}

/// Build the algebraic equality: LCD*var = polynomial(n_var) with integer coefficients.
fn build_polynomial_equality(
    var_name: &str,
    coeffs: &[Rational64],
    n_var_name: &str,
) -> Option<ChcExpr> {
    if coeffs.is_empty() {
        return None;
    }

    // Find LCD of all coefficient denominators
    let mut lcd: i64 = 1;
    for c in coeffs {
        if *c != Rational64::from_integer(0) {
            lcd = lcm(lcd, *c.denom());
        }
    }

    // Scale all coefficients to integers
    let int_coeffs: Vec<i64> = coeffs
        .iter()
        .map(|c| (*c * Rational64::from_integer(lcd)).to_integer())
        .collect();

    let var = ChcVar::new(var_name.to_string(), ChcSort::Int);
    let n_var = ChcVar::new(n_var_name.to_string(), ChcSort::Int);

    // LHS: lcd * var
    let lhs = if lcd == 1 {
        ChcExpr::var(var)
    } else {
        ChcExpr::mul(ChcExpr::int(lcd), ChcExpr::var(var))
    };

    // RHS: int_coeffs[0] + int_coeffs[1]*A + int_coeffs[2]*A^2 + ...
    let mut rhs_terms: Vec<ChcExpr> = Vec::new();
    for (power, &coeff) in int_coeffs.iter().enumerate() {
        if coeff == 0 {
            continue;
        }
        let term = match power {
            0 => ChcExpr::int(coeff),
            1 => {
                if coeff == 1 {
                    ChcExpr::var(n_var.clone())
                } else {
                    ChcExpr::mul(ChcExpr::int(coeff), ChcExpr::var(n_var.clone()))
                }
            }
            _ => {
                let mut a_pow = ChcExpr::var(n_var.clone());
                for _ in 1..power {
                    a_pow = ChcExpr::mul(a_pow, ChcExpr::var(n_var.clone()));
                }
                if coeff == 1 {
                    a_pow
                } else {
                    ChcExpr::mul(ChcExpr::int(coeff), a_pow)
                }
            }
        };
        rhs_terms.push(term);
    }

    if rhs_terms.is_empty() {
        return Some(ChcExpr::eq(lhs, ChcExpr::int(0)));
    }

    let rhs = rhs_terms.into_iter().reduce(ChcExpr::add).unwrap();
    Some(ChcExpr::eq(lhs, rhs))
}

/// Derive a conserved quantity from polynomial closed forms (no init values needed).
///
/// For a quadratic polynomial variable X with closed form
/// X_k = X_0 + c1(init)*k + c2*k^2 and counter N with ConstantDelta(1),
/// the expression `LCD*X - LCD*r*N - LCD*q*N^2` is constant through the
/// self-loop, where r = constant part of c1, q = c2.
///
/// Returns (lcd, conserved_quantity_expression) or None if not quadratic.
/// The CQ expression uses var_name and n_var_name as current-state variables.
pub(super) fn derive_conserved_quantity(
    var_name: &str,
    coeffs: &[FxHashMap<String, Rational64>],
    n_var_name: &str,
) -> Option<(i64, ChcExpr)> {
    if coeffs.len() < 3 {
        return None;
    }

    let r = coeffs[1].get("").copied().unwrap_or_default();
    let q = coeffs[2].get("").copied().unwrap_or_default();

    if q.is_zero() {
        return None;
    }

    let lcd_val = lcm(*r.denom(), *q.denom());
    let int_r = (r * Rational64::from_integer(lcd_val)).to_integer();
    let int_q = (q * Rational64::from_integer(lcd_val)).to_integer();

    let var = ChcVar::new(var_name.to_string(), ChcSort::Int);
    let n = ChcVar::new(n_var_name.to_string(), ChcSort::Int);

    // Build: LCD*X + (-int_r)*N + (-int_q)*N^2
    let mut terms: Vec<ChcExpr> = Vec::new();

    // LCD * X
    terms.push(if lcd_val == 1 {
        ChcExpr::var(var)
    } else {
        ChcExpr::mul(ChcExpr::int(lcd_val), ChcExpr::var(var))
    });

    // (-int_r) * N
    let neg_r = -int_r;
    if neg_r != 0 {
        terms.push(match neg_r {
            1 => ChcExpr::var(n.clone()),
            -1 => ChcExpr::mul(ChcExpr::int(-1), ChcExpr::var(n.clone())),
            _ => ChcExpr::mul(ChcExpr::int(neg_r), ChcExpr::var(n.clone())),
        });
    }

    // (-int_q) * N^2
    let neg_q = -int_q;
    if neg_q != 0 {
        let n_sq = ChcExpr::mul(ChcExpr::var(n.clone()), ChcExpr::var(n));
        terms.push(match neg_q {
            1 => n_sq,
            -1 => ChcExpr::mul(ChcExpr::int(-1), n_sq),
            _ => ChcExpr::mul(ChcExpr::int(neg_q), n_sq),
        });
    }

    let cq = terms.into_iter().reduce(ChcExpr::add).unwrap();
    Some((lcd_val, cq))
}

/// Evaluate a conserved quantity expression at concrete entry values.
///
/// Given CQ(X, N) = LCD*X + corr(N), compute CQ(x_entry, n_entry).
pub(super) fn eval_conserved_at_entry(
    lcd: i64,
    x_entry: &ChcExpr,
    n_var_name: &str,
    n_entry: &ChcExpr,
    coeffs: &[FxHashMap<String, Rational64>],
) -> ChcExpr {
    let r = coeffs[1].get("").copied().unwrap_or_default();
    let q = coeffs[2].get("").copied().unwrap_or_default();

    let int_r = (r * Rational64::from_integer(lcd)).to_integer();
    let int_q = (q * Rational64::from_integer(lcd)).to_integer();

    let _ = n_var_name; // entry value provided directly

    let mut terms: Vec<ChcExpr> = Vec::new();

    // LCD * X_entry
    terms.push(if lcd == 1 {
        x_entry.clone()
    } else {
        ChcExpr::mul(ChcExpr::int(lcd), x_entry.clone())
    });

    // (-int_r) * N_entry
    let neg_r = -int_r;
    if neg_r != 0 {
        terms.push(match neg_r {
            1 => n_entry.clone(),
            -1 => ChcExpr::mul(ChcExpr::int(-1), n_entry.clone()),
            _ => ChcExpr::mul(ChcExpr::int(neg_r), n_entry.clone()),
        });
    }

    // (-int_q) * N_entry^2
    let neg_q = -int_q;
    if neg_q != 0 {
        let n_sq = ChcExpr::mul(n_entry.clone(), n_entry.clone());
        terms.push(match neg_q {
            1 => n_sq,
            -1 => ChcExpr::mul(ChcExpr::int(-1), n_sq),
            _ => ChcExpr::mul(ChcExpr::int(neg_q), n_sq),
        });
    }

    terms.into_iter().reduce(ChcExpr::add).unwrap()
}

fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn lcm(a: i64, b: i64) -> i64 {
    if a == 0 || b == 0 {
        return 1;
    }
    (a.abs() / gcd(a, b)) * b.abs()
}
