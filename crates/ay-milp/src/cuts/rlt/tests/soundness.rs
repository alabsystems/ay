// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exhaustive RLT validity, recognizer, and mutation regressions.

use super::*;

#[test]
fn rlt_cuts_never_remove_an_integer_point() {
    let mut rng = Lcg(0x5217_0BAD_u64);
    let mut fired = 0usize;
    for _case in 0..500 {
        let nbin = 3 + rng.upto(2) as usize;
        let ncont = 1 + rng.upto(2) as usize;
        let (m, rows, x, grids) = random_rlt_case(&mut rng, nbin, ncont);
        if rows.len() < 2 {
            continue;
        }
        let cuts = separate_rlt(&m, &x, m.num_rows(), 8);
        fired += cuts.len();
        assert_cuts_keep_every_feasible_point(&rows, &grids, &cuts, "mixed");
    }
    assert!(
        fired > 0,
        "no RLT cut was ever separated: the guard is vacuous"
    );
    eprintln!("rlt guard: {fired} cuts checked against the full integer sweep");
}

/// PURE-BINARY case, separately, so the conflict substitution is exercised on models where it
/// is the ONLY exact substitution available.
#[test]
fn rlt_cuts_never_remove_a_binary_point() {
    let mut rng = Lcg(0x0C0F_FEE5_u64);
    let mut fired = 0usize;
    for _case in 0..400 {
        let nbin = 4 + rng.upto(2) as usize;
        let (m, rows, x, grids) = random_rlt_case(&mut rng, nbin, 0);
        if rows.len() < 2 {
            continue;
        }
        let cuts = separate_rlt(&m, &x, m.num_rows(), 8);
        fired += cuts.len();
        assert_cuts_keep_every_feasible_point(&rows, &grids, &cuts, "binary");
    }
    assert!(
        fired > 0,
        "no RLT cut on a pure-binary model: guard is vacuous"
    );
    eprintln!("rlt binary guard: {fired} cuts checked");
}

/// THE HOLE IN A GRID SWEEP, CLOSED: EVERY VERTEX OF THE CONTINUOUS FACE, NOT A SAMPLE OF IT.
///
/// The two guards above sweep continuous columns on a fixed grid, and that is NOT a proof.
/// An RLT cut is linear, so over the feasible set of a FIXED binary assignment — a polytope in
/// the continuous columns — its maximum is attained at a VERTEX of that polytope, and a vertex
/// is where model rows intersect. There is no reason for it to land on `{1/2, 1, 3/2, 2, 5/2}`.
/// A cut that deletes a feasible point strictly between two grid points would pass both guards
/// silently, and the McCormick faces carry `l_j` and `u_j` into the coefficients, so a
/// continuous column is exactly where such a bug would live.
///
/// With ONE continuous column the polytope is an interval and the argument closes completely:
/// for each of the `2^nbin` binary assignments, intersect every row's implied range for that
/// column with its box, and check the cut at BOTH ENDPOINTS. The cut is affine in the column,
/// so if it holds at both endpoints it holds on the whole interval — this is a proof over a
/// continuum, not a sample of it.
#[test]
fn rlt_cuts_hold_at_every_vertex_of_the_continuous_face() {
    let mut rng = Lcg(0x1CE_B00C_u64);
    let mut checked = 0usize;
    let mut fired = 0usize;
    for _case in 0..400 {
        let nbin = 3 + rng.upto(2) as usize;
        let (m, rows, x, _grids) = random_rlt_case(&mut rng, nbin, 1);
        if rows.len() < 2 {
            continue;
        }
        let n = nbin + 1;
        let cuts = separate_rlt(&m, &x, m.num_rows(), 8);
        if cuts.is_empty() {
            continue;
        }
        fired += cuts.len();
        for code in 0..(1usize << nbin) {
            let mut p = vec![0.0f64; n];
            for (j, v) in p.iter_mut().take(nbin).enumerate() {
                *v = ((code >> j) & 1) as f64;
            }
            // The feasible interval for the single continuous column, from its box and
            // every row, given the binaries fixed.
            let (mut tlo, mut thi) = (0.5f64, 2.5f64);
            let mut feasible = true;
            for (a, lo, hi) in &rows {
                let base: f64 = (0..nbin).map(|j| a[j] * p[j]).sum();
                let ac = a[nbin];
                if ac == 0.0 {
                    if base < lo - 1e-9 || base > hi + 1e-9 {
                        feasible = false;
                        break;
                    }
                    continue;
                }
                // lo ≤ base + ac·t ≤ hi, solved for t with the sign of `ac` flipping it.
                let (mut a1, mut a2) = ((lo - base) / ac, (hi - base) / ac);
                if ac < 0.0 {
                    std::mem::swap(&mut a1, &mut a2);
                }
                if a1.is_finite() {
                    tlo = tlo.max(a1);
                }
                if a2.is_finite() {
                    thi = thi.min(a2);
                }
            }
            if !feasible || tlo > thi + 1e-9 {
                continue;
            }
            for t in [tlo, thi] {
                p[nbin] = t;
                // Re-check the point against the model itself; the interval arithmetic above
                // is f64 and may land a hair outside on a degenerate row.
                if !rows.iter().all(|(a, lo, hi)| {
                    let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
                    act >= lo - 1e-7 && act <= hi + 1e-7
                }) {
                    continue;
                }
                checked += 1;
                for c in &cuts {
                    let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                    assert!(
                        act <= c.ub + 1e-6,
                        "an RLT cut deleted the feasible VERTEX {p:?} of the continuous \
                         face: activity {act} > bound {}",
                        c.ub
                    );
                }
            }
        }
    }
    assert!(fired > 0, "no cut was ever separated: guard is vacuous");
    assert!(
        checked > 0,
        "no feasible continuous vertex was ever reached: guard is vacuous"
    );
    eprintln!("rlt continuous-face guard: {fired} cuts at {checked} exact interval endpoints");
}

/// THE CONFLICT ORACLE IS AN UPPER-BOUND INSTRUMENT AND MUST BE CHECKED AS ONE.
///
/// `rlt_conflicts` claims `x_i = 1 ⇒ x_j = 0`. If it ever claims that wrongly, `y_ij = 0` is
/// a false substitution and every cut built on it can delete feasible points — and it would
/// do so SILENTLY, because the cut is still a plausible-looking inequality. So: enumerate the
/// model's feasible integer points and assert that no claimed conflict has a witness with
/// both columns at 1. Positive control in the same test: the oracle must actually find edges.
#[test]
fn every_claimed_conflict_is_a_real_conflict() {
    let mut rng = Lcg(0x0BAD_5EED_u64);
    let mut edges = 0usize;
    for _case in 0..400 {
        let nbin = 4usize;
        let ncont = 1usize;
        let (m, rows, _x, grids) = random_rlt_case(&mut rng, nbin, ncont);
        let n = nbin + ncont;
        let mut rows_of: Vec<Vec<u32>> = vec![Vec::new(); m.num_cols()];
        for r in 0..m.num_rows() {
            for &(c, a) in m.row(Row(r as u32)).0 {
                if a != 0.0 {
                    rows_of[c as usize].push(r as u32);
                }
            }
        }
        // Every feasible point of the grid.
        let total: usize = grids.iter().map(|g| g.len()).product();
        let mut pts: Vec<Vec<f64>> = Vec::new();
        for code in 0..total {
            let mut p = vec![0.0f64; n];
            let mut t = code;
            for j in 0..n {
                p[j] = grids[j][t % grids[j].len()];
                t /= grids[j].len();
            }
            if rows.iter().all(|(a, lo, hi)| {
                let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
                act >= lo - 1e-9 && act <= hi + 1e-9
            }) {
                pts.push(p);
            }
        }
        for i in 0..nbin {
            for j in rlt_conflicts(&m, m.num_rows(), &rows_of, i) {
                edges += 1;
                for p in &pts {
                    assert!(
                        !(p[i] > 0.5 && p[j] > 0.5),
                        "rlt_conflicts claimed {i}⇒¬{j} but {p:?} is feasible with both on"
                    );
                }
            }
        }
    }
    assert!(
        edges > 0,
        "the conflict oracle found no edge at all: vacuous"
    );
    eprintln!("rlt conflict oracle: {edges} claimed edges, all witnessed sound");
}

/// EVERY CLAIMED VUB IS A REAL VUB — the second exact substitution, checked the same way.
/// `y_ij = x_j` requires `x_i = 0 ⇒ x_j = 0`; assert no feasible point has `x_i = 0` and
/// `x_j ≠ 0`.
#[test]
fn every_claimed_vub_forces_its_bounded_column_to_zero() {
    let mut rng = Lcg(0xFACE_1E55_u64);
    let mut found = 0usize;
    for _case in 0..400 {
        let (nbin, ncont) = (4usize, 1usize);
        let (m, rows, _x, grids) = random_rlt_case(&mut rng, nbin, ncont);
        let n = nbin + ncont;
        let by_switch = rlt_vub_by_switch(&m, m.num_rows());
        if by_switch.is_empty() {
            continue;
        }
        let total: usize = grids.iter().map(|g| g.len()).product();
        for code in 0..total {
            let mut p = vec![0.0f64; n];
            let mut t = code;
            for j in 0..n {
                p[j] = grids[j][t % grids[j].len()];
                t /= grids[j].len();
            }
            if !rows.iter().all(|(a, lo, hi)| {
                let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
                act >= lo - 1e-9 && act <= hi + 1e-9
            }) {
                continue;
            }
            for (&i, js) in &by_switch {
                for &j in js {
                    found += 1;
                    if p[i] < 0.5 {
                        assert!(
                            p[j].abs() < 1e-9,
                            "claimed VUB {j} ≤ u·{i} but {p:?} has the switch off and \
                             the bounded column at {}",
                            p[j]
                        );
                    }
                }
            }
        }
    }
    assert!(found > 0, "no VUB was ever claimed: vacuous");
}

/// MUTATION CHECK — the guard must FAIL on a derivation one step too greedy.
///
/// The single likeliest wrong turn in this family is getting the SUBSTITUTION DIRECTION
/// backwards in one of the two branches (I made exactly this error deriving branch (1b) by
/// hand). Reproduce it: build branch (1a) with the direction rule inverted — `a_j > 0` taking
/// an UPPER support instead of a lower one — and confirm the integer sweep catches it. If this
/// test ever stops finding a counterexample, the guard above has stopped guarding.
fn inverted_substitution_cut(model: &Model, point: &[f64], switch: Col, exact_col: Col) -> Cut {
    let (coeffs, _lb, ub) = model.row(Row(1));
    let rhs = exact(ub).unwrap();
    let mut multiplier = BigRational::zero();
    let mut products = Vec::new();
    for &(column, raw) in coeffs {
        let j = column as usize;
        let coefficient = exact(raw).unwrap();
        let exact_support = (j == exact_col.index()).then_some(RltExact::Equal);
        // INVERTED: `!a.is_positive()` where the derivation says `a.is_positive()`.
        let face = rlt_face(
            model,
            point[switch.index()],
            point[j],
            j,
            !coefficient.is_positive(),
            exact_support,
        )
        .unwrap();
        let (lo, up) = model.col_bounds(Col(column));
        let (p, q, _constant) = face.pqr(lo, up).unwrap();
        multiplier += &coefficient * &p;
        products.push((j, coefficient, q));
    }
    let mut terms = std::collections::BTreeMap::new();
    for (column, coefficient, product) in products {
        if !product.is_zero() {
            *terms.entry(column).or_insert_with(BigRational::zero) += coefficient * product;
        }
    }
    *terms
        .entry(switch.index())
        .or_insert_with(BigRational::zero) += multiplier - rhs;
    terms.retain(|_, coefficient| !coefficient.is_zero());
    emit_le_cut(model, &terms, &BigRational::zero()).expect("the mutated cut must emit")
}

#[test]
fn the_guard_catches_an_inverted_substitution_direction() {
    // A concrete, minimal fixed-charge model rather than a random search: `y` binary, the arc
    // `x ∈ [0,10]` switched by the LOOSE variable upper bound `x ≤ 10·y`, and a capacity row
    // `x + 2z ≤ 4` with `z ∈ [0,3]`. The looseness is the point — RLT's whole claim is that
    // the CAPACITY row, read when the switch is on, bounds the arc harder than its own big-M.
    let mut m = Model::new();
    let y = m.add_binary_col();
    let x = m.add_col(0.0, 10.0);
    let z = m.add_col(0.0, 3.0);
    m.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0), (y, -10.0)]);
    m.add_row(f64::NEG_INFINITY, 4.0, &[(x, 1.0), (z, 2.0)]);
    m.set_objective(&[(x, -1.0)], Sense::Minimize);
    // On the LP relaxation's own frontier: `x = 10y` and `x + 2z = 4`, both tight.
    let pt = vec![0.25, 2.5, 0.75];

    // The CORRECT derivation on the capacity row, branch (1a): x is VUB-switched by y so
    // y_yx = x exactly; z has a_z = 2 > 0 and no exact substitution, so it takes the tightest
    // LOWER support, which at l_z = 0 is `y_yz ≥ 0` — the term drops. The cut is `x ≤ 4y`,
    // violated at `pt` by 1.5, and strictly stronger than the model's own `x ≤ 10y`.
    let cuts = separate_rlt(&m, &pt, m.num_rows(), 8);
    assert!(
        !cuts.is_empty(),
        "the reference model must separate something"
    );
    // Every feasible point must satisfy every emitted cut (y ∈ {0,1} is the integrality the
    // derivation uses; x and z are continuous, so they are swept densely over their boxes).
    for yv in [0.0f64, 1.0] {
        for xi in 0..=40 {
            for zi in 0..=12 {
                let p = [yv, xi as f64 / 4.0, zi as f64 / 4.0];
                if p[1] - 10.0 * p[0] > 1e-9 || p[1] + 2.0 * p[2] > 4.0 + 1e-9 {
                    continue;
                }
                for c in &cuts {
                    let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                    assert!(
                        act <= c.ub + 1e-6,
                        "reference RLT cut deleted feasible point {p:?}: {act} > {}",
                        c.ub
                    );
                }
            }
        }
    }

    // THE MUTATION: invert the direction rule. `want_lower` becomes `!a.is_positive()` in
    // branch (1a), so a positive-coefficient term takes an UPPER support on `y_ij` where the
    // derivation needs a lower one. On this model z's term becomes `y_yz ≤ 3·y` instead of
    // `y_yz ≥ 0`, so the collected multiplier coefficient goes from `−b = −4` to `2·3 − 4 = 2`
    // and the emitted "cut" is `x + 2y ≤ 0` — which the feasible point `(y,x,z) = (1,4,0)`
    // breaks by 6.
    let bad = inverted_substitution_cut(&m, &pt, y, x);
    let mut caught = false;
    for yv in [0.0f64, 1.0] {
        for xi in 0..=40 {
            for zi in 0..=12 {
                let p = [yv, xi as f64 / 4.0, zi as f64 / 4.0];
                if p[1] - 10.0 * p[0] > 1e-9 || p[1] + 2.0 * p[2] > 4.0 + 1e-9 {
                    continue;
                }
                let act: f64 = bad.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
                if act > bad.ub + 1e-6 {
                    caught = true;
                }
            }
        }
    }
    assert!(
        caught,
        "the inverted-direction mutation produced a VALID cut — the sweep is not a guard"
    );
}

/// The family DECLINES a model with no structure to hold on to, rather than scanning it.
#[test]
fn rlt_is_inert_without_a_switch() {
    let mut m = Model::new();
    let a = m.add_int_col(0.0, 5.0);
    let b = m.add_int_col(0.0, 5.0);
    m.add_row(f64::NEG_INFINITY, 7.0, &[(a, 3.0), (b, 2.0)]);
    m.set_objective(&[(a, 1.0)], Sense::Minimize);
    assert!(separate_rlt(&m, &[1.5, 1.25], m.num_rows(), 8).is_empty());
}
