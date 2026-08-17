// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ---------------------------------------------------------------------------
// THE SWEEPS.
// ---------------------------------------------------------------------------

fn sweep(seed: u64, cases: usize, fractional: bool, window: i64) -> Coverage {
    let mut rng = Rng(seed);
    let mut cov = Coverage::default();
    for case in 0..cases {
        let m = random_model(&mut rng, &mut cov, fractional);
        let all_int = (0..m.num_cols()).all(|j| m.col_kind(Col(j as u32)).is_integral());
        let boxed = (0..m.num_cols()).all(|j| {
            let (l, u) = m.col_bounds(Col(j as u32));
            l.is_finite() && u.is_finite()
        });
        let Some((reduced, post)) = eliminate_structure(&m, None) else {
            continue;
        };
        cov.fired += 1;
        if reduced.num_cols() < m.num_cols() {
            cov.fixed_cols += 1;
        }
        if reduced.num_rows() < m.num_rows() {
            cov.dropped_rows += 1;
        }
        match audit(&m, &reduced, &post, window) {
            Ok(_) => {}
            Err(e) => panic!("seed {seed} case {case}: {e}"),
        }
        // Optimum equality is only meaningful when enumeration is complete.
        if all_int && boxed {
            let direct = brute(&m, window);
            let via = brute(&reduced, window).map(|v| v + post.const_delta());
            assert_eq!(
                direct, via,
                "seed {seed} case {case}: structural elimination changed the optimum"
            );
        }
    }
    cov
}

#[test]
fn integer_sweep_no_invented_or_deleted_points() {
    let cov = sweep(0x1234_5678_9abc_def1, 3000, false, 5);
    assert!(cov.fired > 300, "vacuous: fired {}", cov.fired);
    assert!(
        cov.fixed_cols > 50,
        "no column elimination ({})",
        cov.fixed_cols
    );
    assert!(
        cov.dropped_rows > 50,
        "no row elimination ({})",
        cov.dropped_rows
    );
    assert!(
        cov.equality_rows > 20,
        "no equality rows ({})",
        cov.equality_rows
    );
    assert!(cov.maximize > 50, "no Maximize ({})", cov.maximize);
    assert!(cov.binary > 50, "no binary columns ({})", cov.binary);
    assert!(
        cov.continuous > 50,
        "no continuous columns ({})",
        cov.continuous
    );
    assert!(cov.offset > 50, "no objective offsets ({})", cov.offset);
    assert!(cov.open_bounds > 5, "no open bounds ({})", cov.open_bounds);
    eprintln!(
        "adversary integer sweep: fired {} fixed {} dropped {} eq {} max {} bin {} cont {} off {} open {}",
        cov.fired, cov.fixed_cols, cov.dropped_rows, cov.equality_rows,
        cov.maximize, cov.binary, cov.continuous, cov.offset, cov.open_bounds
    );
}

#[test]
fn fractional_coefficient_sweep() {
    let cov = sweep(0x0fee_1dead_beefu64, 3000, true, 5);
    assert!(cov.fired > 300, "vacuous: fired {}", cov.fired);
    eprintln!(
        "adversary fractional sweep: fired {} fixed {} dropped {}",
        cov.fired, cov.fixed_cols, cov.dropped_rows
    );
}

/// Drive the INEXACT-SHIFT fixpoint deliberately: a huge coefficient against a
/// fixed value makes `b - Sigma a*v` unrepresentable, which must un-fix the
/// column rather than emit a rounded bound.
#[test]
fn inexact_shifts_never_emit_a_rounded_row_bound() {
    // `huge` is exactly representable; `huge - 1` is NOT (odd, above 2^53), so
    // folding a unit-coefficient fixed column into this row's bound cannot be
    // expressed and the column MUST be un-fixed instead of rounded away.
    let huge = 1.0e16_f64;
    // Sanity: the premise of this test is that `huge - k` is NOT an f64 for the
    // odd k below, i.e. f64 subtraction of it is a ROUNDED answer.
    for k in [1.0_f64, 3.0, 5.0, 7.0, 9.0] {
        assert_ne!(
            rat(huge - k),
            rat(huge) - rat(k),
            "premise broken: {huge} - {k} is exactly representable"
        );
    }
    let mut checked = 0usize;
    let mut saw_unfix = 0usize;
    for shift_coeff in [1.0_f64, 3.0, 5.0, 7.0, 9.0] {
        let mut m = Model::new();
        m.add_int_col(1.0, 1.0); // col 0: fixed, folded into the huge row
        m.add_int_col(0.0, 4.0); // col 1: survivor
        m.add_int_col(2.0, 2.0); // col 2: fixed, only in small rows
                                 // The huge row: satisfied by everything, so no tightening cascade.
        m.add_row(
            f64::NEG_INFINITY,
            huge,
            &[(Col(0), shift_coeff), (Col(1), 1.0)],
        );
        // A plainly redundant small row, so the pass has work even if it
        // un-fixes col 0.
        m.add_row(-60.0, 60.0, &[(Col(1), 1.0), (Col(2), 1.0)]);
        m.set_objective(
            &[(Col(0), 1.0), (Col(1), -1.0), (Col(2), 2.0)],
            Sense::Minimize,
        );
        let Some((reduced, post)) = eliminate_structure(&m, None) else {
            continue;
        };
        checked += 1;
        audit(&m, &reduced, &post, 6).unwrap_or_else(|e| panic!("shift_coeff={shift_coeff}: {e}"));

        // THE POINT OF THIS TEST: col 0 must have SURVIVED (un-fixed), because
        // `huge - shift_coeff` is not an f64. If it was eliminated, some row
        // bound was rounded.
        if post.map[0].is_some() {
            saw_unfix += 1;
        }
        assert!(
            post.map[0].is_some(),
            "shift_coeff={shift_coeff}: a column was folded into a row bound that \
             f64 cannot represent ({huge} - {shift_coeff})"
        );

        // Independently re-derive every emitted row bound and demand it be the
        // EXACT image of the true shifted bound.
        for rr in 0..reduced.num_rows() {
            let orig_r = post.row_origin[rr];
            let (ocoef, olb, oub) = m.row(Row(orig_r as u32));
            let mut s = BigRational::zero();
            for &(c, a) in ocoef {
                if post.map[c as usize].is_none() {
                    let v = post
                        .recover
                        .iter()
                        .find(|fr| fr.col == c as usize)
                        .map(|fr| fr.value.clone())
                        .expect("eliminated column must have a recovery");
                    s += rat(a) * v;
                }
            }
            let (_, rlb, rub) = reduced.row(Row(rr as u32));
            if olb.is_finite() {
                assert_eq!(
                    rat(rlb),
                    rat(olb) - &s,
                    "row {rr} lb is not the exact shift"
                );
            } else {
                assert!(rlb.is_infinite() && rlb < 0.0);
            }
            if oub.is_finite() {
                assert_eq!(
                    rat(rub),
                    rat(oub) - &s,
                    "row {rr} ub is not the exact shift"
                );
            } else {
                assert!(rub.is_infinite() && rub > 0.0);
            }
        }
    }
    assert!(
        checked >= 5,
        "inexact-shift test is vacuous: fired {checked}"
    );
    assert!(
        saw_unfix >= 5,
        "the un-fixing path was never taken ({saw_unfix})"
    );
    eprintln!("inexact-shift cases fired {checked}, un-fix observed {saw_unfix}");
}

/// The un-fixing fixpoint has to converge even when un-fixing one column makes
/// ANOTHER row's shift representable/unrepresentable in turn.
#[test]
fn chained_unfixing_terminates_and_stays_exact() {
    let mut rng = Rng(0xdead_beef_cafe_0001);
    let mut fired = 0usize;
    for _ in 0..1500 {
        let n = 4usize;
        let mut m = Model::new();
        for j in 0..n {
            if j % 2 == 0 {
                let v = rng.pick(1, 3) as f64;
                m.add_int_col(v, v);
            } else {
                m.add_int_col(0.0, 3.0);
            }
        }
        for _ in 0..3 {
            let mut coeffs = Vec::new();
            for j in 0..n {
                let a = if rng.chance(4) {
                    (rng.pick(1, 3) as f64) * 1.0e16
                } else {
                    rng.pick(-3, 3) as f64
                };
                if a != 0.0 {
                    coeffs.push((Col(j as u32), a));
                }
            }
            if coeffs.is_empty() {
                coeffs.push((Col(1), 1.0));
            }
            m.add_row(rng.pick(-30, -5) as f64, rng.pick(5, 30) as f64, &coeffs);
        }
        // A row the box plainly implies, so the pass has something to drop even
        // when the huge coefficients un-fix every column.
        m.add_row(-500.0, 500.0, &[(Col(1), 1.0), (Col(3), 1.0)]);
        m.set_objective(
            &(0..n)
                .map(|j| (Col(j as u32), rng.pick(-3, 3) as f64))
                .collect::<Vec<_>>(),
            Sense::Minimize,
        );
        let Some((reduced, post)) = eliminate_structure(&m, None) else {
            continue;
        };
        fired += 1;
        audit(&m, &reduced, &post, 4).expect("chained un-fixing broke exactness");
    }
    assert!(fired > 50, "chained un-fixing sweep vacuous: {fired}");
    eprintln!("chained un-fixing fired: {fired}");
}

/// A row that is redundant by EXACTLY ZERO margin must still be droppable, and
/// a row that misses by one ULP must NOT be dropped. This is the boundary the
/// containment test lives on.
#[test]
fn the_containment_boundary_is_exact_on_both_sides() {
    // max activity is exactly 6; ub = 6 -> implied, droppable.
    let mut tight = Model::new();
    tight.add_int_col(0.0, 3.0);
    tight.add_int_col(0.0, 3.0);
    tight.add_int_col(1.0, 1.0); // gives the pass something to do
    tight.add_row(f64::NEG_INFINITY, 6.0, &[(Col(0), 1.0), (Col(1), 1.0)]);
    tight.set_objective(
        &[(Col(0), -1.0), (Col(1), -1.0), (Col(2), 1.0)],
        Sense::Minimize,
    );
    let (red, post) = eliminate_structure(&tight, None).expect("fires");
    audit(&tight, &red, &post, 5).expect("zero-margin drop must be sound");

    // ub one ULP BELOW 6 -> NOT implied; (3,3) must remain excluded.
    let just_under = 6.0_f64 - f64::EPSILON * 4.0;
    assert!(just_under < 6.0);
    let mut sharp = Model::new();
    sharp.add_int_col(0.0, 3.0);
    sharp.add_int_col(0.0, 3.0);
    sharp.add_int_col(1.0, 1.0);
    sharp.add_row(
        f64::NEG_INFINITY,
        just_under,
        &[(Col(0), 1.0), (Col(1), 1.0)],
    );
    sharp.set_objective(
        &[(Col(0), -1.0), (Col(1), -1.0), (Col(2), 1.0)],
        Sense::Minimize,
    );
    let (red2, post2) = eliminate_structure(&sharp, None).expect("fires on the fixed column");
    audit(&sharp, &red2, &post2, 5).expect("ULP-sharp row must not be dropped unsoundly");
    // (3,3) is infeasible in the original, so it must be infeasible in the reduced.
    let three = vec![int(3), int(3)];
    assert!(
        !feasible_exact(&red2, &three),
        "a row missing implication by one ULP was dropped: (3,3) became reachable"
    );
}

/// `const_delta` must be exact even when the folded contribution is NOT an f64.
#[test]
fn const_delta_survives_a_non_representable_fold() {
    // Three fixed columns whose objective contributions sum to a value that is
    // fine in BigRational; each individually exact.
    let mut m = Model::new();
    m.add_int_col(1.0, 1.0);
    m.add_int_col(1.0, 1.0);
    m.add_int_col(0.0, 3.0);
    m.add_row(-50.0, 50.0, &[(Col(2), 1.0)]);
    m.set_objective(
        &[(Col(0), 1.0e16), (Col(1), 1.0), (Col(2), -1.0)],
        Sense::Minimize,
    );
    let (red, post) = eliminate_structure(&m, None).expect("two fixed columns");
    audit(&m, &red, &post, 4).expect("non-representable fold broke the objective");
    let expected = rat(1.0e16) + BigRational::one();
    assert_eq!(post.const_delta(), &expected, "const_delta lost precision");
}
