// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Neumaier–Shcherbina safe LP bounds: a RIGOROUS lower bound on `min obj·x`
//! from an APPROXIMATE row-dual vector `y`, computed entirely in `f64` with
//! directed rounding — no exact-rational solve.
//!
//! This is the fast path for [`crate::LpSession::rigorous_bound`], avoiding an
//! exact-rational solve when a floating-point dual suffices. The dual vector
//! is turned into a bound by a weak-duality argument evaluated with outward
//! rounding, so the result is a
//! true lower bound for the exact-arithmetic LP **no matter how wrong `y` is**
//! — the soundness never rests on the float dual being right, only the
//! tightness does (`ns_bound_never_exceeds_exact_optimum`,
//! `corrupted_duals_stay_valid_or_none`). Fail closed: any infinite bound side
//! that meets a wrong-signed reduced cost, or any non-finite input, yields
//! `None` and the caller falls back to the exact rim.

use crate::model::{Col, Model, Row};

/// `a + b` rounded toward −∞: the result never exceeds the exact sum.
#[inline]
pub(crate) fn add_down(a: f64, b: f64) -> f64 {
    (a + b).next_down()
}

/// `a − b` rounded toward −∞: the result never exceeds the exact difference.
#[inline]
pub(crate) fn sub_down(a: f64, b: f64) -> f64 {
    (a - b).next_down()
}

/// `a − b` rounded toward +∞: the result is never below the exact difference.
#[inline]
pub(crate) fn sub_up(a: f64, b: f64) -> f64 {
    (a - b).next_up()
}

/// `a · b` rounded toward −∞: the result never exceeds the exact product.
#[inline]
pub(crate) fn mul_down(a: f64, b: f64) -> f64 {
    (a * b).next_down()
}

/// `a · b` rounded toward +∞: the result is never below the exact product.
#[inline]
pub(crate) fn mul_up(a: f64, b: f64) -> f64 {
    (a * b).next_up()
}

/// A rigorous lower bound on `d·x` over `x ∈ [lb, ub]` (feasible points are
/// always finite), valid for every reduced cost `d` in `[dlo, dhi]`.
///
/// `d ↦ inf_x d·x` is concave (an infimum of functions linear in `d`), so its
/// minimum over the interval is attained at an endpoint: `d > 0` pins `x` at
/// `lb`, `d < 0` at `ub`, `d = 0` contributes nothing. `None` when an
/// endpoint's sign meets an infinite bound side (no finite rigorous bound) or
/// the interval itself is non-finite (fail closed; catches NaN).
fn term_lower(dlo: f64, dhi: f64, lb: f64, ub: f64) -> Option<f64> {
    if !dlo.is_finite() || !dhi.is_finite() {
        return None;
    }
    debug_assert!(dlo <= dhi, "inverted reduced-cost interval");
    let mut best = f64::INFINITY;
    for d in [dlo, dhi] {
        let cand = if d > 0.0 {
            if lb == f64::NEG_INFINITY {
                return None;
            }
            mul_down(d, lb)
        } else if d < 0.0 {
            if ub == f64::INFINITY {
                return None;
            }
            mul_down(d, ub)
        } else {
            0.0
        };
        best = best.min(cand);
    }
    Some(best)
}

/// A rigorous LOWER bound on `min obj·x` over the model's box and rows, from
/// APPROXIMATE row duals `y` (len `num_rows`), after Neumaier–Shcherbina.
///
/// Standard form: `min obj·x` s.t. `lb ≤ (x, s) ≤ ub`, `A·x − s = 0` (`s` the
/// row activities, so a row's `[lb, ub]` is its slack's box). For any `y`,
/// every feasible point has `obj·x = d·(x‖s)` with `d = (obj‖0) − [Aᵀ‖−I]·y`
/// (the `y`-combination of `A·x − s = 0` adds nothing), so `Σ_j inf d_j·x_j`
/// bounds the minimum from below. `d` is interval-evaluated with outward
/// rounding and summed downward, so the result is a true bound for the
/// exact-arithmetic LP regardless of `y`. Iteration is row-major (main's `A`
/// is stored by row); each `A` entry contributes one directed subtraction, so
/// the interval `[lo_j, hi_j]` always brackets the exact reduced cost.
///
/// `None` when an infinite bound side meets a wrong-signed reduced-cost
/// interval (no finite rigorous bound for this `y`) or on any non-finite input
/// (fail closed; NaN in `y` ⇒ `None`).
///
/// # Panics
/// Panics when `obj.len() != num_cols` or `y.len() != num_rows`.
pub(crate) fn rigorous_lower_bound(model: &Model, obj: &[f64], y: &[f64]) -> Option<f64> {
    let n = model.num_cols();
    let m = model.num_rows();
    assert_eq!(obj.len(), n, "rigorous_lower_bound: objective arity");
    assert_eq!(y.len(), m, "rigorous_lower_bound: dual arity");
    if y.iter().chain(obj).any(|v| !v.is_finite()) {
        return None;
    }
    // Reduced-cost interval per structural column: d_j = obj_j − Σ_r a_rj·y_r,
    // accumulated with outward rounding so [lo_j, hi_j] ∋ the exact d_j.
    let mut lo = obj.to_vec();
    let mut hi = obj.to_vec();
    for r in 0..m {
        let yr = y[r];
        let (coeffs, _lb, _ub) = model.row(Row(r as u32));
        for &(c, a) in coeffs {
            let cu = c as usize;
            lo[cu] = sub_down(lo[cu], mul_up(a, yr));
            hi[cu] = sub_up(hi[cu], mul_down(a, yr));
        }
    }
    let mut total = 0.0_f64;
    for j in 0..n {
        let (lb, ub) = model.col_bounds(Col(j as u32));
        total = add_down(total, term_lower(lo[j], hi[j], lb, ub)?);
    }
    // Slack terms: d_{n+r} = y_r exactly (the `−I` column), boxed by the row.
    for r in 0..m {
        let (_coeffs, lb, ub) = model.row(Row(r as u32));
        total = add_down(total, term_lower(y[r], y[r], lb, ub)?);
    }
    total.is_finite().then_some(total)
}

#[cfg(test)]
mod tests {
    use num_rational::BigRational;
    use num_traits::ToPrimitive;

    use super::*;
    use crate::cert::{BoundSide, FactRef, Multiplier};
    use crate::exact::{Budget, ExactLp, LpOptimum};
    use crate::model::Sense;
    use ay_lra::rational::Rational;

    /// Deterministic xorshift64 (tests only; the module itself is
    /// randomness-free).
    struct Rng(u64);
    impl Rng {
        fn new(seed: u64) -> Self {
            Self(seed | 1)
        }
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
        fn int(&mut self, lo: i64, hi: i64) -> i64 {
            lo + self.below((hi - lo + 1) as u64) as i64
        }
    }

    fn budget() -> Budget {
        Budget {
            deadline: None,
            max_iters: 10_000,
        }
    }

    /// A random small LP: finite column boxes (never unbounded below) and a
    /// mix of range and one-sided rows. Returns the model and a dense
    /// structural objective.
    fn random_lp(rng: &mut Rng) -> (Model, Vec<f64>) {
        let n = rng.int(2, 4) as usize;
        let mut model = Model::new();
        let mut cols = Vec::with_capacity(n);
        for _ in 0..n {
            let lb = rng.int(-3, 1) as f64;
            let ub = lb + rng.int(0, 4) as f64;
            cols.push(model.add_col(lb, ub));
        }
        for _ in 0..rng.int(1, 3) {
            let mut coeffs = Vec::new();
            for &c in &cols {
                if rng.below(3) < 2 {
                    let a = rng.int(-3, 3);
                    if a != 0 {
                        coeffs.push((c, a as f64));
                    }
                }
            }
            let lo = rng.int(-6, 2) as f64;
            let hi = lo + rng.int(0, 6) as f64;
            match rng.below(4) {
                0 => model.add_row(lo, f64::INFINITY, &coeffs),
                1 => model.add_row(f64::NEG_INFINITY, hi, &coeffs),
                _ => model.add_row(lo, hi, &coeffs),
            };
        }
        let obj: Vec<f64> = (0..n).map(|_| rng.int(-3, 3) as f64).collect();
        (model, obj)
    }

    fn exact_obj(obj: &[f64]) -> Vec<(u32, Rational)> {
        obj.iter()
            .enumerate()
            .filter(|&(_, &c)| c != 0.0)
            .map(|(j, &c)| {
                (
                    j as u32,
                    Rational::from_big(crate::model::exact(c).unwrap()),
                )
            })
            .collect()
    }

    /// Row duals implied by model-fact multipliers under this module's sign
    /// convention: Lower side ⇒ `+coeff`, Upper side ⇒ `−coeff`.
    fn row_duals(multipliers: &[Multiplier], m: usize) -> Vec<f64> {
        let mut y = vec![0.0; m];
        for mu in multipliers {
            if let FactRef::RowBound { row, side } = mu.fact {
                let v = mu.coeff.to_f64().expect("small rational");
                match side {
                    BoundSide::Lower => y[row.index()] += v,
                    BoundSide::Upper => y[row.index()] -= v,
                }
            }
        }
        y
    }

    #[test]
    fn directed_ops_bracket_exact_results() {
        assert!(add_down(0.1, 0.2) < 0.1 + 0.2);
        assert!(sub_down(0.3, 0.1) < 0.3 - 0.1);
        assert!(sub_up(0.3, 0.1) > 0.3 - 0.1);
        assert!(mul_down(0.1, 0.3) < 0.1 * 0.3);
        assert!(mul_up(0.1, 0.3) > 0.1 * 0.3);
        assert_eq!(add_down(f64::NEG_INFINITY, 1.0), f64::NEG_INFINITY);
        assert_eq!(mul_up(f64::INFINITY, 2.0), f64::INFINITY);
    }

    #[test]
    fn term_lower_edges() {
        assert_eq!(
            term_lower(0.0, 0.0, f64::NEG_INFINITY, f64::INFINITY),
            Some(0.0)
        );
        assert!(term_lower(0.5, 1.0, f64::NEG_INFINITY, 3.0).is_none());
        assert!(term_lower(-1.0, -0.5, 0.0, f64::INFINITY).is_none());
        let t = term_lower(-0.5, 1.0, -2.0, 3.0).unwrap();
        assert!((-2.0 - 1e-9..=-2.0).contains(&t));
        assert!(term_lower(f64::NAN, 0.0, 0.0, 1.0).is_none());
        assert!(term_lower(f64::NEG_INFINITY, 0.0, 0.0, 1.0).is_none());
    }

    #[test]
    fn bound_tight_on_hand_lp() {
        // min x + y  s.t.  x + y ≥ 1,  x, y ∈ [0, 1]: optimum 1, dual y = [1].
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        let yv = model.add_col(0.0, 1.0);
        model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (yv, 1.0)]);
        let b = rigorous_lower_bound(&model, &[1.0, 1.0], &[1.0]).unwrap();
        assert!((1.0 - 1e-9..=1.0).contains(&b), "bound {b} not tight");
    }

    #[test]
    fn bound_none_when_unbounded() {
        // min −x, x ∈ [0, ∞): no finite rigorous bound exists for any duals.
        let mut model = Model::new();
        model.add_col(0.0, f64::INFINITY);
        assert!(rigorous_lower_bound(&model, &[-1.0], &[]).is_none());
    }

    #[test]
    fn bound_none_on_nonfinite_input() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.add_row(0.0, 2.0, &[(x, 1.0)]);
        assert!(rigorous_lower_bound(&model, &[1.0], &[f64::NAN]).is_none());
        assert!(rigorous_lower_bound(&model, &[1.0], &[f64::INFINITY]).is_none());
        assert!(rigorous_lower_bound(&model, &[f64::NAN], &[0.5]).is_none());
    }

    #[test]
    fn ns_bound_never_exceeds_exact_optimum() {
        let mut rng = Rng::new(0x9E37_79B9_7F4A_7C15);
        let mut optimal_seen = 0;
        for _ in 0..80 {
            let (model, obj) = random_lp(&mut rng);
            let mut lp = ExactLp::new(&model);
            let LpOptimum::Optimal { value, multipliers } =
                lp.minimize(&exact_obj(&obj), &budget())
            else {
                continue;
            };
            optimal_seen += 1;
            // Zero duals: always a (weak) valid bound with finite boxes.
            let y0 = vec![0.0; model.num_rows()];
            let b0 = rigorous_lower_bound(&model, &obj, &y0).expect("zero-dual bound");
            assert!(
                BigRational::from_float(b0).unwrap() <= value,
                "zero-dual NS bound {b0} exceeds the exact optimum {value}"
            );
            // Duals recovered from the exact certificate: valid AND tight.
            let y = row_duals(&multipliers, model.num_rows());
            let b = rigorous_lower_bound(&model, &obj, &y).expect("derived-dual bound");
            assert!(
                BigRational::from_float(b).unwrap() <= value,
                "derived-dual NS bound {b} exceeds the exact optimum {value}"
            );
            let v = value.to_f64().expect("small rational");
            assert!(v - b <= 1e-6, "NS bound not tight: {b} vs {v}");
        }
        assert!(optimal_seen >= 40, "generator coverage: {optimal_seen}");
    }

    #[test]
    fn corrupted_duals_stay_valid_or_none() {
        let mut rng = Rng::new(0x1234_5678_9ABC_DEF0);
        let mut checked = 0;
        for _ in 0..80 {
            let (model, obj) = random_lp(&mut rng);
            let mut lp = ExactLp::new(&model);
            let LpOptimum::Optimal { value, .. } = lp.minimize(&exact_obj(&obj), &budget()) else {
                continue;
            };
            // Arbitrary/adversarial duals: whatever comes back MUST still be a
            // valid lower bound (or None). Soundness cannot depend on `y`.
            let y: Vec<f64> = (0..model.num_rows())
                .map(|_| rng.int(-5, 5) as f64 * 0.5)
                .collect();
            if let Some(b) = rigorous_lower_bound(&model, &obj, &y) {
                assert!(
                    BigRational::from_float(b).unwrap() <= value,
                    "corrupted-dual NS bound {b} exceeds the exact optimum {value}"
                );
                checked += 1;
            }
        }
        assert!(checked >= 10, "corruption coverage: {checked}");
        let _ = Sense::Minimize;
    }
}
