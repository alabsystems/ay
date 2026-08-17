// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn fixture_models() -> Vec<(String, Model)> {
    let mut smoke = Model::new();
    let fixed = smoke.add_int_col(1.0, 1.0);
    let live = smoke.add_int_col(0.0, 2.0);
    smoke.add_row(f64::NEG_INFINITY, 3.0, &[(fixed, 2.0), (live, 1.0)]);
    smoke.add_row(1.0, f64::INFINITY, &[(fixed, 1.0)]);
    smoke.set_objective(&[(fixed, 5.0), (live, -1.0)], Sense::Minimize);

    vec![("in-repository-smoke".to_owned(), smoke)]
}

/// For every row the pass drops, recompute — independently, in exact rational
/// arithmetic, from the model the pass actually emits — whether that row is
/// really implied. A row that is not implied is a deleted constraint.
#[test]
fn dropped_rows_are_really_implied_on_the_in_repository_fixture() {
    let mut checked = 0usize;
    for (name, model) in fixture_models() {
        checked += usize::from(check_one(&name, &model));
    }
    assert!(
        checked > 0,
        "the in-repository smoke model must exercise the pass"
    );
}

fn check_one(inst: &str, m: &Model) -> bool {
    eprint!("{inst}: ");
    let Some((reduced, post)) = eliminate_structure(m, None) else {
        eprintln!("{}r/{}c -- pass DECLINES", m.num_rows(), m.num_cols());
        return false;
    };
    eprint!(
        "{}r/{}c -> {}r/{}c ({} fixed cols, {} dropped rows) ",
        m.num_rows(),
        m.num_cols(),
        reduced.num_rows(),
        reduced.num_cols(),
        post.recover.len(),
        m.num_rows() - reduced.num_rows(),
    );

    // The exact box the REDUCED model carries, per ORIGINAL column: survivors
    // take the reduced model's bounds, eliminated columns their fixed value.
    let mut lo: Vec<Option<BigRational>> = vec![None; m.num_cols()];
    let mut up: Vec<Option<BigRational>> = vec![None; m.num_cols()];
    for j in 0..m.num_cols() {
        if let Some(nc) = post.map[j] {
            let (l, u) = reduced.col_bounds(nc);
            lo[j] = l.is_finite().then(|| exact(l).unwrap());
            up[j] = u.is_finite().then(|| exact(u).unwrap());
        }
    }
    for rec in &post.recover {
        lo[rec.col] = Some(rec.value.clone());
        up[rec.col] = Some(rec.value.clone());
    }

    // Which original rows survived? `row_origin` is per reduced row.
    let mut survived = vec![false; m.num_rows()];
    for &orig in &post.row_origin {
        survived[orig] = true;
    }

    let mut violations = 0usize;
    for r in 0..m.num_rows() {
        if survived[r] {
            continue;
        }
        let (coeffs, rlb, rub) = m.row(Row(r as u32));
        let (mut amin, mut amax) = (Some(BigRational::zero()), Some(BigRational::zero()));
        for &(c, a) in coeffs {
            let ax = exact(a).unwrap();
            let (for_min, for_max) = if a > 0.0 {
                (lo[c as usize].as_ref(), up[c as usize].as_ref())
            } else {
                (up[c as usize].as_ref(), lo[c as usize].as_ref())
            };
            amin = match (amin, for_min) {
                (Some(s), Some(b)) => Some(s + &ax * b),
                _ => None,
            };
            amax = match (amax, for_max) {
                (Some(s), Some(b)) => Some(s + &ax * b),
                _ => None,
            };
        }
        let lb_ok = !rlb.is_finite() || amin.as_ref().is_some_and(|v| *v >= exact(rlb).unwrap());
        let ub_ok = !rub.is_finite() || amax.as_ref().is_some_and(|v| *v <= exact(rub).unwrap());
        if !(lb_ok && ub_ok) {
            violations += 1;
            if violations <= 5 {
                eprintln!(
                    "\n  {inst} ROW {r} WAS DROPPED BUT IS NOT IMPLIED: bounds [{rlb}, {rub}], \
                     box activity [{}, {}], nnz {}",
                    amin.as_ref().map_or("-inf".into(), ToString::to_string),
                    amax.as_ref().map_or("+inf".into(), ToString::to_string),
                    coeffs.len()
                );
            }
        }
    }
    eprintln!("VERIFIED: every dropped row is implied ({violations} violations)");
    assert_eq!(
        violations, 0,
        "{inst}: {violations} rows were dropped that the emitted model's own box does NOT imply"
    );
    true
}

/// Independently re-derive the emitted fixture: each surviving reduced row
/// must be exactly the original row with fixed columns folded out and bounds
/// shifted by their exact contribution. This validates `row_origin` and the
/// shift without trusting a `debug_assert` that a release build strips.
#[test]
fn row_emission_is_exact_on_the_in_repository_fixture() {
    let mut fired = 0usize;
    for (inst, m) in fixture_models() {
        let Some((reduced, post)) = eliminate_structure(&m, None) else {
            continue;
        };
        fired += 1;
        let mut fixed: Vec<Option<BigRational>> = vec![None; m.num_cols()];
        for rec in &post.recover {
            fixed[rec.col] = Some(rec.value.clone());
        }
        assert_eq!(
            post.row_origin.len(),
            reduced.num_rows(),
            "{inst}: row_origin arity"
        );
        let mut checked = 0usize;
        for k in 0..reduced.num_rows() {
            let r = post.row_origin[k];
            let (ocoeffs, olb, oub) = m.row(Row(r as u32));
            let (rcoeffs, rlb, rub) = reduced.row(Row(k as u32));
            // exact fold of the fixed columns
            let mut shift = BigRational::zero();
            let mut want: Vec<(usize, f64)> = Vec::new();
            for &(c, a) in ocoeffs {
                match fixed[c as usize].as_ref() {
                    Some(v) => shift += exact(a).unwrap() * v,
                    None => want.push((post.map[c as usize].unwrap().index(), a)),
                }
            }
            want.sort_by_key(|&(c, _)| c);
            let got: Vec<(usize, f64)> = rcoeffs.iter().map(|&(c, a)| (c as usize, a)).collect();
            assert_eq!(
                want, got,
                "{inst}: reduced row {k} (origin {r}) coefficients differ"
            );
            for (o, rd, what) in [(olb, rlb, "lb"), (oub, rub, "ub")] {
                if o.is_finite() {
                    let expect = exact(o).unwrap() - &shift;
                    assert_eq!(
                        exact(rd).unwrap(), expect,
                        "{inst}: reduced row {k} (origin {r}) {what} is {rd}, exact fold says {expect}"
                    );
                } else {
                    assert_eq!(o, rd, "{inst}: reduced row {k} {what} openness changed");
                }
            }
            checked += 1;
        }
        // Objective: survivors keep their coefficient verbatim; const_delta is
        // exactly the eliminated columns' contribution.
        let mut delta = BigRational::zero();
        for rec in &post.recover {
            delta += exact(m.obj_coeff(Col(rec.col as u32))).unwrap() * &rec.value;
        }
        assert_eq!(&delta, post.const_delta(), "{inst}: const_delta mismatch");
        for j in 0..m.num_cols() {
            if let Some(nc) = post.map[j] {
                assert_eq!(
                    m.obj_coeff(Col(j as u32)),
                    reduced.obj_coeff(nc),
                    "{inst}: survivor column {j} objective coefficient rewritten"
                );
            }
        }
        assert_eq!(m.sense(), reduced.sense(), "{inst}: sense changed");
        assert_eq!(
            m.objective_offset(),
            reduced.objective_offset(),
            "{inst}: offset changed"
        );
        eprintln!("{inst}: {checked} surviving rows re-derived exactly; const_delta and objective verbatim");
    }
    assert!(
        fired > 0,
        "the in-repository smoke model must exercise the pass"
    );
}
