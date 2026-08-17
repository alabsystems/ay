// INDEPENDENT ADVERSARIAL SOUNDNESS HARNESS for the conditional (probing) coefficient
// tightening. Written by the verification pass, deliberately NOT reusing the shipped guards'
// generators, gates or shapes.

#![cfg(test)]

use num_rational::BigRational;
use num_traits::{Signed, Zero};

use crate::model::{exact, Col, Model, Row};
use crate::presolve::{tighten_bounds, tighten_coefficients_conditional, Presolved};

struct Rng(u64);
impl Rng {
    fn raw(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn between(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.raw() % ((hi - lo + 1) as u64)) as i64
    }
}

fn br(v: i64) -> BigRational {
    BigRational::from_integer(v.into())
}

/// EXHAUSTIVE both-directions check on an ALL-INTEGER model: the enumerated lattice IS the
/// feasible set, so any point whose feasibility moved in either direction is a soundness bug.
/// Hostile relative to the shipped guards: negative lower bounds, RANGE rows, equalities,
/// bigger coefficients, rows whose support is a random subset.
#[test]
fn adversarial_exhaustive_integer_set_is_preserved() {
    let mut rng = Rng(0xdead_beef_0000_0001);
    let mut rewrites = 0usize;
    let ranges = [(0i64, 1i64), (0, 1), (-2, 2), (0, 3), (-1, 1)];
    for _ in 0..1500 {
        let mut m = Model::new();
        let cols: Vec<_> = ranges
            .iter()
            .map(|&(l, u)| {
                if (l, u) == (0, 1) {
                    m.add_binary_col()
                } else {
                    m.add_int_col(l as f64, u as f64)
                }
            })
            .collect();
        for _ in 0..rng.between(2, 5) {
            let terms: Vec<_> = cols
                .iter()
                .map(|&c| (c, rng.between(-7, 7) as f64))
                .filter(|&(_, a)| a != 0.0)
                .collect();
            if terms.len() < 2 {
                continue;
            }
            let b = rng.between(-10, 12) as f64;
            match rng.between(0, 3) {
                0 => m.add_row(f64::NEG_INFINITY, b, &terms),
                1 => m.add_row(b, f64::INFINITY, &terms),
                2 => m.add_row(b, b, &terms),
                _ => m.add_row(b, b + rng.between(1, 6) as f64, &terms),
            };
        }
        let mut t = m.clone();
        rewrites += tighten_coefficients_conditional(&mut t, None);
        for a in 0..2i64 {
            for b in 0..2i64 {
                for c in -2..3i64 {
                    for d in 0..4i64 {
                        for e in -1..2i64 {
                            let p: Vec<BigRational> =
                                [a, b, c, d, e].iter().map(|&v| br(v)).collect();
                            assert_eq!(
                                m.check_point(&p).is_ok(),
                                t.check_point(&p).is_ok(),
                                "feasibility of {p:?} moved"
                            );
                        }
                    }
                }
            }
        }
    }
    assert!(rewrites > 0, "harness never exercised a rewrite");
}

/// The EXACT feasible interval of the single continuous column `x` with every integer column
/// pinned. `None` = empty. No sampling, so comparing it between two models is a complete
/// both-directions check on a MIXED model — including columns with genuinely INFINITE bounds,
/// which no grid can reach.
fn x_interval(
    m: &Model,
    xcol: usize,
    pinned: &[i64],
) -> Option<(Option<BigRational>, Option<BigRational>)> {
    let (xl, xu) = m.col_bounds(Col(xcol as u32));
    let mut lo = exact(xl);
    let mut hi = exact(xu);
    let mut vals: Vec<BigRational> = Vec::new();
    let mut k = 0usize;
    for j in 0..m.num_cols() {
        if j == xcol {
            vals.push(BigRational::zero());
            continue;
        }
        let v = br(pinned[k]);
        let (l, u) = m.col_bounds(Col(j as u32));
        if let Some(l) = exact(l) {
            if v < l {
                return None;
            }
        }
        if let Some(u) = exact(u) {
            if v > u {
                return None;
            }
        }
        vals.push(v);
        k += 1;
    }
    for r in 0..m.num_rows() {
        let (coeffs, rlb, rub) = m.row(Row(r as u32));
        let mut c = BigRational::zero();
        let mut ax = BigRational::zero();
        for &(col, a) in coeffs {
            let a = exact(a).expect("finite");
            if col as usize == xcol {
                ax += a;
            } else {
                c += a * &vals[col as usize];
            }
        }
        let (rl, ru) = (exact(rlb), exact(rub));
        if ax.is_zero() {
            if rl.as_ref().is_some_and(|l| c < *l) || ru.as_ref().is_some_and(|u| c > *u) {
                return None;
            }
            continue;
        }
        let (from_lo, from_hi) = (rl.map(|l| (l - &c) / &ax), ru.map(|u| (u - &c) / &ax));
        let (new_lo, new_hi) = if ax.is_positive() {
            (from_lo, from_hi)
        } else {
            (from_hi, from_lo)
        };
        if let Some(v) = new_lo {
            lo = Some(match lo {
                None => v,
                Some(cur) => {
                    if v > cur {
                        v
                    } else {
                        cur
                    }
                }
            });
        }
        if let Some(v) = new_hi {
            hi = Some(match hi {
                None => v,
                Some(cur) => {
                    if v < cur {
                        v
                    } else {
                        cur
                    }
                }
            });
        }
    }
    match (&lo, &hi) {
        (Some(l), Some(u)) if l > u => None,
        _ => Some((lo, hi)),
    }
}

/// MIXED model, EXACT both-directions check, with the continuous column allowed an INFINITE
/// bound — the shape the pass exists for, and the one a sampled grid cannot certify.
#[test]
fn adversarial_mixed_model_interval_is_preserved_exactly() {
    let mut rng = Rng(0x0bad_c0de_1234_5678);
    let mut rewrites = 0usize;
    let boxes = [
        (0.0, f64::INFINITY),
        (f64::NEG_INFINITY, 6.0),
        (-3.0, 7.0),
        (f64::NEG_INFINITY, f64::INFINITY),
        (0.0, 4.0),
    ];
    for it in 0..2000 {
        let mut m = Model::new();
        let b0 = m.add_binary_col();
        let b1 = m.add_binary_col();
        let g = m.add_int_col(-1.0, 2.0);
        let (xl, xu) = boxes[it % boxes.len()];
        let x = m.add_col(xl, xu);
        let xcol = x.index();
        let cols = [b0, b1, g, x];
        for _ in 0..rng.between(2, 4) {
            let terms: Vec<_> = cols
                .iter()
                .map(|&c| (c, rng.between(-6, 6) as f64))
                .filter(|&(_, a)| a != 0.0)
                .collect();
            if terms.len() < 2 {
                continue;
            }
            let b = rng.between(-9, 11) as f64;
            match rng.between(0, 3) {
                0 | 3 => m.add_row(f64::NEG_INFINITY, b, &terms),
                1 => m.add_row(b, f64::INFINITY, &terms),
                _ => m.add_row(b, b + rng.between(1, 5) as f64, &terms),
            };
        }
        let mut t = m.clone();
        rewrites += tighten_coefficients_conditional(&mut t, None);
        for a in 0..2i64 {
            for bb in 0..2i64 {
                for gg in -1..3i64 {
                    let pinned = [a, bb, gg];
                    assert_eq!(
                        x_interval(&m, xcol, &pinned),
                        x_interval(&t, xcol, &pinned),
                        "continuous slice moved at b0={a} b1={bb} g={gg} (iter {it})"
                    );
                }
            }
        }
    }
    assert!(rewrites > 0, "harness never exercised a rewrite");
}

/// The WHOLE presolve pipeline with the knob on — bound propagation, then the unconditional
/// coefficient rule, then the conditional one — must preserve the integer feasible set exactly.
/// Composition is where a locally-valid rule most often stops being valid.
#[test]
fn adversarial_full_pipeline_preserves_the_integer_set() {
    let mut rng = Rng(0xfeed_0001_beef_0002);
    let ranges = [(0i64, 1i64), (0, 1), (-2, 2), (0, 3)];
    for _ in 0..1200 {
        let mut m = Model::new();
        let cols: Vec<_> = ranges
            .iter()
            .map(|&(l, u)| {
                if (l, u) == (0, 1) {
                    m.add_binary_col()
                } else {
                    m.add_int_col(l as f64, u as f64)
                }
            })
            .collect();
        for _ in 0..rng.between(2, 5) {
            let terms: Vec<_> = cols
                .iter()
                .map(|&c| (c, rng.between(-6, 6) as f64))
                .filter(|&(_, a)| a != 0.0)
                .collect();
            if terms.len() < 2 {
                continue;
            }
            let b = rng.between(-8, 10) as f64;
            match rng.between(0, 3) {
                0 | 3 => m.add_row(f64::NEG_INFINITY, b, &terms),
                1 => m.add_row(b, f64::INFINITY, &terms),
                _ => m.add_row(b, b + rng.between(0, 4) as f64, &terms),
            };
        }
        // `tighten_bounds` already runs the unconditional rule; appending the conditional one
        // IS the shipped pipeline with `the cond-tighten knob` set.
        let presolved = match tighten_bounds(&m, None) {
            Presolved::Tightened(mut out) => {
                tighten_coefficients_conditional(&mut out, None);
                Some(out)
            }
            Presolved::Infeasible => None,
        };
        for a in 0..2i64 {
            for b in 0..2i64 {
                for c in -2..3i64 {
                    for d in 0..4i64 {
                        let p: Vec<BigRational> = [a, b, c, d].iter().map(|&v| br(v)).collect();
                        let orig = m.check_point(&p).is_ok();
                        match &presolved {
                            None => {
                                assert!(!orig, "presolve declared INFEASIBLE but {p:?} is feasible")
                            }
                            Some(out) => assert_eq!(
                                orig,
                                out.check_point(&p).is_ok(),
                                "pipeline moved the feasibility of {p:?}"
                            ),
                        }
                    }
                }
            }
        }
    }
}

/// IDEMPOTENCE / RATCHET: repeated application must converge, never walking a right-hand side
/// past the true conditional ceiling. Each re-run re-derives its bounds from the ALREADY
/// rewritten model, which is exactly where a subtly circular rule would drift.
#[test]
fn adversarial_repeated_application_never_drifts() {
    let mut rng = Rng(0x1111_2222_3333_4444);
    let ranges = [(0i64, 1i64), (0, 1), (0, 1), (-2, 2), (0, 3)];
    for _ in 0..600 {
        let mut m = Model::new();
        let cols: Vec<_> = ranges
            .iter()
            .map(|&(l, u)| {
                if (l, u) == (0, 1) {
                    m.add_binary_col()
                } else {
                    m.add_int_col(l as f64, u as f64)
                }
            })
            .collect();
        for _ in 0..rng.between(2, 5) {
            let terms: Vec<_> = cols
                .iter()
                .map(|&c| (c, rng.between(-6, 6) as f64))
                .filter(|&(_, a)| a != 0.0)
                .collect();
            if terms.len() < 2 {
                continue;
            }
            let b = rng.between(-8, 10) as f64;
            if rng.between(0, 1) == 0 {
                m.add_row(f64::NEG_INFINITY, b, &terms);
            } else {
                m.add_row(b, f64::INFINITY, &terms);
            }
        }
        let mut t = m.clone();
        for _ in 0..6 {
            tighten_coefficients_conditional(&mut t, None);
        }
        for a in 0..2i64 {
            for b in 0..2i64 {
                for c in 0..2i64 {
                    for d in -2..3i64 {
                        for e in 0..4i64 {
                            let p: Vec<BigRational> =
                                [a, b, c, d, e].iter().map(|&v| br(v)).collect();
                            assert_eq!(
                                m.check_point(&p).is_ok(),
                                t.check_point(&p).is_ok(),
                                "six applications moved the feasibility of {p:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// AN OPEN BOUND IN THE REST MUST ABORT THE ROW, not contribute zero.
///
/// Two FREE columns in one `<=` row keep each other unbounded (propagation needs every other
/// column finite to close one), so `up[u]`/`up[v]` survive as `None` all the way into the rest
/// sum. Treating a missing bound as a zero contribution understates the rest, overstates `d`,
/// and cuts off feasible points — this pins the guard that stops it.
#[test]
fn adversarial_an_open_rest_bound_blocks_the_rewrite() {
    let mut m = Model::new();
    let y = m.add_binary_col();
    let x = m.add_int_col(0.0, 6.0);
    let u = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let v = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    // x - 100*y + u + v <= 0 : `u` and `v` are mutually unclosable.
    m.add_row(
        f64::NEG_INFINITY,
        0.0,
        &[(x, 1.0), (y, -100.0), (u, 1.0), (v, 1.0)],
    );
    let mut t = m.clone();
    assert_eq!(
        tighten_coefficients_conditional(&mut t, None),
        0,
        "a row whose rest has an OPEN bound must be left alone"
    );
    // And the point an over-tightened big-M would have cut is still admitted.
    let p: Vec<BigRational> = [1, 6, 50, 0].iter().map(|&s| br(s)).collect();
    assert!(
        m.check_point(&p).is_ok(),
        "witness is feasible to begin with"
    );
    assert!(t.check_point(&p).is_ok(), "witness was cut off");
}

/// NON-DYADIC / large-magnitude coefficients: the fail-closed `as_exact_f64` round-trip is the
/// only thing standing between an inexact rewrite and a wrong answer. Feed it coefficients whose
/// arithmetic does NOT stay inside the f64 grid (thirds, sevenths, 2^-30 offsets) and assert the
/// feasible set still cannot move.
#[test]
fn adversarial_non_dyadic_coefficients_stay_sound() {
    let mut rng = Rng(0x7777_8888_9999_aaaa);
    let menu = [
        1.0 / 3.0,
        -1.0 / 7.0,
        1e9 + 1.0 / 3.0,
        -1e-9,
        2.0f64.powi(-30) + 1.0,
        1e15 + 1.0,
        -(1.0 / 3.0) * 1e6,
        0.1,
        -0.7,
        123_456.789,
    ];
    let ranges = [(0i64, 1i64), (0, 1), (-2, 2), (0, 3)];
    for _ in 0..1500 {
        let mut m = Model::new();
        let cols: Vec<_> = ranges
            .iter()
            .map(|&(l, u)| {
                if (l, u) == (0, 1) {
                    m.add_binary_col()
                } else {
                    m.add_int_col(l as f64, u as f64)
                }
            })
            .collect();
        for _ in 0..rng.between(2, 4) {
            let terms: Vec<_> = cols
                .iter()
                .map(|&c| {
                    let a = if rng.between(0, 2) == 0 {
                        rng.between(-6, 6) as f64
                    } else {
                        menu[rng.between(0, menu.len() as i64 - 1) as usize]
                            * f64::from(if rng.between(0, 1) == 0 { 1 } else { -1 })
                    };
                    (c, a)
                })
                .filter(|&(_, a)| a != 0.0)
                .collect();
            if terms.len() < 2 {
                continue;
            }
            let b = if rng.between(0, 1) == 0 {
                rng.between(-8, 10) as f64
            } else {
                menu[rng.between(0, menu.len() as i64 - 1) as usize]
            };
            if rng.between(0, 1) == 0 {
                m.add_row(f64::NEG_INFINITY, b, &terms);
            } else {
                m.add_row(b, f64::INFINITY, &terms);
            }
        }
        let mut t = m.clone();
        tighten_coefficients_conditional(&mut t, None);
        for a in 0..2i64 {
            for b in 0..2i64 {
                for c in -2..3i64 {
                    for d in 0..4i64 {
                        let p: Vec<BigRational> = [a, b, c, d].iter().map(|&v| br(v)).collect();
                        assert_eq!(
                            m.check_point(&p).is_ok(),
                            t.check_point(&p).is_ok(),
                            "non-dyadic rewrite moved the feasibility of {p:?}"
                        );
                    }
                }
            }
        }
    }
}
