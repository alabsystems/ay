// Copyright 2026 Andrew Yates
//! INDEPENDENT ADVERSARY for `presolve::structure`. Test-only.
//!
//! Written from the CONTRACT, not from the implementation's own harness:
//!
//! * feasibility is decided in EXACT `BigRational` with NO tolerance (the
//!   shipped guard's `rows_hold` allows `1e-9` slack on both sides);
//! * the map is checked as a BIJECTION IN BOTH DIRECTIONS. The shipped guard
//!   only walks reduced -> original. The other direction is what catches a
//!   reduction that DELETES a feasible point, and it also puts
//!   `tighten_bounds_opt`'s fixpoint under test: an original-feasible point
//!   whose eliminated column does not hold its "fixed" value is a refutation of
//!   `B*` itself;
//! * the generator produces what the shipped one never does — equality rows,
//!   one-sided and OPEN bounds, binary and continuous kinds, `Maximize`,
//!   objective offsets, dyadic fractional coefficients and bounds, and rows
//!   engineered to drive the inexact-shift fixpoint.
//!
//! Conversion is `BigRational::from_float`, deliberately NOT the crate's
//! `exact()`, so a bug in `exact()` cannot hide from this file.

#![cfg(test)]

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use super::structure::{eliminate_structure, StructurePostsolve};
use crate::model::{Col, Model, Row, Sense};

/// Exact f64 -> rational. Independent of the crate's `exact()`.
fn rat(f: f64) -> BigRational {
    assert!(f.is_finite(), "rat() on non-finite {f}");
    BigRational::from_float(f).expect("finite f64 is rational")
}

fn int(i: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(i))
}

/// EXACT feasibility: every row activity within its bounds, every column within
/// its box, every integral column at an integer. NO TOLERANCE ANYWHERE.
fn feasible_exact(m: &Model, x: &[BigRational]) -> bool {
    if x.len() != m.num_cols() {
        return false;
    }
    for j in 0..m.num_cols() {
        let c = Col(j as u32);
        let (l, u) = m.col_bounds(c);
        if l.is_finite() && x[j] < rat(l) {
            return false;
        }
        if u.is_finite() && x[j] > rat(u) {
            return false;
        }
        if m.col_kind(c).is_integral() && !x[j].is_integer() {
            return false;
        }
    }
    for r in 0..m.num_rows() {
        let (coeffs, lb, ub) = m.row(Row(r as u32));
        let mut act = BigRational::zero();
        for &(c, a) in coeffs {
            act += rat(a) * &x[c as usize];
        }
        if lb.is_finite() && act < rat(lb) {
            return false;
        }
        if ub.is_finite() && act > rat(ub) {
            return false;
        }
    }
    true
}

/// Exact objective value including the model's own offset.
fn obj_exact(m: &Model, x: &[BigRational]) -> BigRational {
    let mut v = rat(m.objective_offset());
    for j in 0..m.num_cols() {
        v += rat(m.obj_coeff(Col(j as u32))) * &x[j];
    }
    v
}

/// Enumerate the integer points of a model's box, clipping open/wide sides into
/// `[-window, window]` so an unbounded column is still exercised.
fn lattice(m: &Model, window: i64) -> Vec<Vec<BigRational>> {
    let n = m.num_cols();
    let mut ranges: Vec<(i64, i64)> = Vec::with_capacity(n);
    for j in 0..n {
        let (l, u) = m.col_bounds(Col(j as u32));
        let lo = if l.is_finite() {
            (l.ceil() as i64).max(-window)
        } else {
            -window
        };
        let hi = if u.is_finite() {
            (u.floor() as i64).min(window)
        } else {
            window
        };
        if lo > hi {
            return Vec::new();
        }
        ranges.push((lo, hi));
    }
    let total: u128 = ranges.iter().map(|&(l, h)| (h - l + 1) as u128).product();
    assert!(total <= 400_000, "adversary lattice too large: {total}");
    let mut out = Vec::new();
    let mut p: Vec<i64> = ranges.iter().map(|&(l, _)| l).collect();
    loop {
        out.push(p.iter().map(|&v| int(v)).collect());
        let mut k = 0;
        loop {
            if k == n {
                return out;
            }
            p[k] += 1;
            if p[k] <= ranges[k].1 {
                break;
            }
            p[k] = ranges[k].0;
            k += 1;
        }
    }
}

/// Restrict an original point to the reduced column space, if it agrees with
/// every eliminated column's recovered constant.
fn restrict(
    post: &StructurePostsolve,
    x: &[BigRational],
    n_reduced: usize,
) -> Option<Vec<BigRational>> {
    for rec in &post.recover {
        if x[rec.col] != rec.value {
            return None;
        }
    }
    let mut out = vec![BigRational::zero(); n_reduced];
    for (orig, slot) in post.map.iter().enumerate() {
        if let Some(nc) = slot {
            out[nc.index()] = x[orig].clone();
        }
    }
    Some(out)
}

/// THE AUDIT. Returns `Err(reason)` on any violation of the reduction contract.
///
/// Checked over the lattice of `window`-clipped integer points:
///  A. reduced-feasible  ==> widen is ORIGINAL-feasible   (no point INVENTED)
///  B. original-feasible ==> restrict is REDUCED-feasible (no point DELETED)
///  C. objectives agree exactly: obj_orig(widen q) == obj_red(q) + const_delta
///  D. an original-feasible point disagreeing with a recovered constant is a
///     refutation of the "fixed column" claim (and hence of `B*`).
fn audit(
    orig: &Model,
    reduced: &Model,
    post: &StructurePostsolve,
    window: i64,
) -> Result<(usize, usize), String> {
    let k = post.const_delta().clone();
    let mut n_red_feas = 0usize;
    let mut n_orig_feas = 0usize;

    // A + C
    for q in lattice(reduced, window) {
        if !feasible_exact(reduced, &q) {
            continue;
        }
        n_red_feas += 1;
        let w = post.widen(&q);
        if !feasible_exact(orig, &w) {
            return Err(format!(
                "INVENTED POINT: reduced-feasible {:?} widens to {:?}, infeasible in the original",
                q.iter().map(|v| v.to_f64().unwrap()).collect::<Vec<_>>(),
                w.iter().map(|v| v.to_f64().unwrap()).collect::<Vec<_>>()
            ));
        }
        let lhs = obj_exact(orig, &w);
        let rhs = obj_exact(reduced, &q) + &k;
        if lhs != rhs {
            return Err(format!(
                "OBJECTIVE DRIFT: original {} vs reduced+delta {}",
                lhs.to_f64().unwrap(),
                rhs.to_f64().unwrap()
            ));
        }
    }

    // B + D
    for p in lattice(orig, window) {
        if !feasible_exact(orig, &p) {
            continue;
        }
        n_orig_feas += 1;
        let Some(q) = restrict(post, &p, reduced.num_cols()) else {
            return Err(format!(
                "FIXED-COLUMN REFUTED: original-feasible {:?} disagrees with a recovered constant",
                p.iter().map(|v| v.to_f64().unwrap()).collect::<Vec<_>>()
            ));
        };
        if !feasible_exact(reduced, &q) {
            return Err(format!(
                "DELETED POINT: original-feasible {:?} restricts to {:?}, infeasible in the reduced",
                p.iter().map(|v| v.to_f64().unwrap()).collect::<Vec<_>>(),
                q.iter().map(|v| v.to_f64().unwrap()).collect::<Vec<_>>()
            ));
        }
    }
    Ok((n_red_feas, n_orig_feas))
}

/// Independent optimum by full enumeration (all-integer models only).
fn brute(m: &Model, window: i64) -> Option<BigRational> {
    let mut best: Option<BigRational> = None;
    for p in lattice(m, window) {
        if !feasible_exact(m, &p) {
            continue;
        }
        let v = obj_exact(m, &p);
        let better = match (&best, m.sense()) {
            (None, _) => true,
            (Some(b), Sense::Minimize) => &v < b,
            (Some(b), Sense::Maximize) => &v > b,
        };
        if better {
            best = Some(v);
        }
    }
    best
}

// ---------------------------------------------------------------------------
// Generator: xorshift, and shapes the shipped guard never produces.
// ---------------------------------------------------------------------------

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn pick(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
    fn chance(&mut self, one_in: u64) -> bool {
        self.next() % one_in == 0
    }
}

/// Coverage of the shapes the shipped generator cannot reach.
#[derive(Default)]
struct Coverage {
    fired: usize,
    fixed_cols: usize,
    dropped_rows: usize,
    equality_rows: usize,
    open_bounds: usize,
    maximize: usize,
    binary: usize,
    continuous: usize,
    offset: usize,
    fractional: usize,
}

fn random_model(rng: &mut Rng, cov: &mut Coverage, fractional: bool) -> Model {
    let n = rng.pick(2, 4) as usize;
    let nr = rng.pick(1, 4) as usize;
    let mut m = Model::new();
    let mut open = false;
    for _ in 0..n {
        let kind = rng.pick(0, 3);
        if kind == 0 {
            m.add_binary_col();
            cov.binary += 1;
            continue;
        }
        let lo = rng.pick(-2, 2);
        let fixed = rng.chance(3);
        let hi = if fixed { lo } else { lo + rng.pick(0, 3) };
        // OPEN BOUND: the shipped generator never makes one.
        if !fixed && rng.chance(9) {
            open = true;
            let c = m.add_int_col(lo as f64, f64::INFINITY);
            m.cols[c.index()].ub = f64::INFINITY;
            continue;
        }
        if kind == 3 {
            // Continuous column on an integer box.
            let c = m.add_col(lo as f64, hi as f64);
            m.cols[c.index()].lb = lo as f64;
            m.cols[c.index()].ub = hi as f64;
            cov.continuous += 1;
        } else {
            m.add_int_col(lo as f64, hi as f64);
        }
    }
    if open {
        cov.open_bounds += 1;
    }
    for _ in 0..nr {
        let mut coeffs = Vec::new();
        for j in 0..n {
            let a = rng.pick(-3, 3);
            if a != 0 {
                let v = if fractional && rng.chance(3) {
                    // Dyadic halves/quarters: exact in f64, and they make shifts
                    // that the emission path must still represent.
                    a as f64 / (1 << rng.pick(1, 2)) as f64
                } else {
                    a as f64
                };
                coeffs.push((Col(j as u32), v));
            }
        }
        if coeffs.is_empty() {
            coeffs.push((Col(0), 1.0));
        }
        if fractional {
            cov.fractional += 1;
        }
        // EQUALITY / ONE-SIDED / RANGED, in that order of rarity.
        let roll = rng.pick(0, 9);
        let (lb, ub) = if roll == 0 {
            cov.equality_rows += 1;
            let b = rng.pick(-4, 4) as f64;
            (b, b)
        } else if roll <= 3 {
            (f64::NEG_INFINITY, rng.pick(-2, 8) as f64)
        } else if roll <= 5 {
            (rng.pick(-8, 2) as f64, f64::INFINITY)
        } else {
            (rng.pick(-14, -2) as f64, rng.pick(2, 14) as f64)
        };
        m.add_row(lb, ub, &coeffs);
    }
    let obj: Vec<(Col, f64)> = (0..n)
        .map(|j| (Col(j as u32), rng.pick(-4, 4) as f64))
        .collect();
    let sense = if rng.chance(3) {
        cov.maximize += 1;
        Sense::Maximize
    } else {
        Sense::Minimize
    };
    m.set_objective(&obj, sense);
    if rng.chance(4) {
        cov.offset += 1;
        m.set_objective_offset(rng.pick(-5, 5) as f64);
    }
    m
}

// ---------------------------------------------------------------------------
// THE POSITIVE CONTROL ON MY OWN AUDIT.
// ---------------------------------------------------------------------------

/// My audit must catch a reduction that is wrong in each of the three ways it
/// claims to detect. If it cannot, every green result below is worthless.
#[test]
fn the_adversary_audit_catches_deliberately_broken_reductions() {
    // Base: x in [0,3], y in [0,3], row x + y <= 4, plus a fixed z = 2.
    let mut m = Model::new();
    m.add_int_col(0.0, 3.0);
    m.add_int_col(0.0, 3.0);
    m.add_int_col(2.0, 2.0);
    m.add_row(f64::NEG_INFINITY, 4.0, &[(Col(0), 1.0), (Col(1), 1.0)]);
    m.add_row(f64::NEG_INFINITY, 9.0, &[(Col(2), 1.0)]);
    m.set_objective(
        &[(Col(0), -1.0), (Col(1), -1.0), (Col(2), 3.0)],
        Sense::Minimize,
    );

    let (good, post) = eliminate_structure(&m, None).expect("z is fixed");
    audit(&m, &good, &post, 6).expect("the honest reduction must pass my audit");

    // Mutants carry the SAME objective as the honest reduction, so the only
    // thing that differs is the feasible set — otherwise the objective check
    // fires first and the structural probe is never exercised.
    let red_obj = [(Col(0), -1.0), (Col(1), -1.0)];

    // (1) INVENTED POINT: drop the x+y<=4 row that the box does NOT imply.
    let mut invented = Model::new();
    invented.add_int_col(0.0, 3.0);
    invented.add_int_col(0.0, 3.0);
    invented.set_objective(&red_obj, Sense::Minimize);
    let e1 = audit(&m, &invented, &post, 6).unwrap_err();
    assert!(e1.starts_with("INVENTED POINT"), "got {e1}");

    // (2) DELETED POINT: keep the row but tighten it to x + y <= 3.
    let mut deleted = Model::new();
    deleted.add_int_col(0.0, 3.0);
    deleted.add_int_col(0.0, 3.0);
    deleted.add_row(f64::NEG_INFINITY, 3.0, &[(Col(0), 1.0), (Col(1), 1.0)]);
    deleted.set_objective(&red_obj, Sense::Minimize);
    let e2 = audit(&m, &deleted, &post, 6).unwrap_err();
    assert!(e2.starts_with("DELETED POINT"), "got {e2}");

    // (3) OBJECTIVE DRIFT: correct feasible set, wrong objective coefficient.
    let mut drift = good.clone();
    drift.set_objective(&[(Col(0), -1.0), (Col(1), -2.0)], Sense::Minimize);
    let e3 = audit(&m, &drift, &post, 6).unwrap_err();
    assert!(e3.starts_with("OBJECTIVE DRIFT"), "got {e3}");

    // (4) FIXED-COLUMN REFUTED: a postsolve claiming z == 1 when z is 2.
    let bogus = StructurePostsolve {
        n_orig: post.n_orig,
        map: post.map.clone(),
        recover: vec![super::structure::FixedRecovery {
            col: 2,
            value: int(1),
        }],
        row_origin: post.row_origin.clone(),
        const_delta: int(3),
    };
    let e4 = audit(&m, &good, &bogus, 6).unwrap_err();
    assert!(
        e4.starts_with("FIXED-COLUMN REFUTED") || e4.starts_with("INVENTED POINT"),
        "got {e4}"
    );
}

mod sweeps;
