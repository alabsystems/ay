// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// A continuous model with fixed columns and one-sided rows: sampled on a
/// half-integer grid, both directions must hold.
#[test]
fn attack_continuous_columns_sampled() {
    let mut r = R(0xC0FF_EE01);
    let mut fired = 0usize;
    for case in 0..1500 {
        let n = r.range(3, 4) as usize;
        let mut m = Model::new();
        for _ in 0..n {
            let lo = r.range(-2, 2) as f64;
            let hi = if r.chance(3) {
                lo
            } else {
                lo + r.range(1, 3) as f64
            };
            if r.chance(3) {
                m.add_int_col(lo, hi);
            } else {
                m.add_col(lo, hi);
            }
        }
        let nr = r.range(2, 3) as usize;
        for _ in 0..nr {
            let mut c: Vec<(Col, f64)> = Vec::new();
            for j in 0..n {
                let a = coeff(&mut r);
                if a != 0.0 {
                    c.push((Col(j as u32), a));
                }
            }
            if c.is_empty() {
                c.push((Col(0), 1.0));
            }
            let (lb, ub) = match r.next() % 4 {
                0 => (-6.0, 6.0),
                1 => (f64::NEG_INFINITY, r.range(-2, 6) as f64),
                2 => (r.range(-6, 2) as f64, f64::INFINITY),
                _ => {
                    let v = r.range(-3, 3) as f64;
                    (v, v)
                }
            };
            m.add_row(lb, ub, &c);
        }
        let obj: Vec<(Col, f64)> = (0..n).map(|j| (Col(j as u32), coeff(&mut r))).collect();
        m.set_objective(
            &obj,
            if r.chance(2) {
                Sense::Maximize
            } else {
                Sense::Minimize
            },
        );

        let Some((reduced, post)) = eliminate_structure(&m, None) else {
            continue;
        };
        fired += 1;

        audit_half_integer_grid(case, &m, &reduced, &post);
    }
    eprintln!("CONTINUOUS ATTACK COVERAGE: fired {fired}/1500");
    assert!(fired > 100, "continuous attack is vacuous: fired {fired}");
}

fn audit_half_integer_grid(
    case: usize,
    model: &Model,
    reduced: &Model,
    post: &super::super::structure::StructurePostsolve,
) {
    let n = model.num_cols();
    let steps: Vec<Vec<BigRational>> = (0..n)
        .map(|j| {
            let (lower, upper) = model.col_bounds(Col(j as u32));
            // This fixture generates integral finite bounds, so the doubled
            // span is the exact number of half-steps to enumerate.
            let half_steps = ((upper - lower) * 2.0) as usize;
            let mut values = Vec::with_capacity(half_steps.saturating_add(1));
            for step in 0..=half_steps {
                let value = lower + step as f64 * 0.5;
                values.push(exact(value).unwrap());
            }
            values
        })
        .collect();
    let mut indices = vec![0usize; n];
    loop {
        let point: Vec<BigRational> = (0..n).map(|j| steps[j][indices[j]].clone()).collect();
        if feasible(model, &point) {
            for recovery in &post.recover {
                assert_eq!(
                    point[recovery.col], recovery.value,
                    "case {case}: column {} eliminated as fixed at {} but a feasible \
                     point has {}",
                    recovery.col, recovery.value, point[recovery.col]
                );
            }
            let restricted = restrict(post, &point, reduced.num_cols());
            assert!(
                feasible(reduced, &restricted),
                "case {case}: ORIGINAL-feasible point lost ({:?})",
                reduced.check_point(&restricted)
            );
            assert_eq!(
                objective_at(reduced, &restricted) + post.const_delta(),
                objective_at(model, &point),
                "case {case}: objective drift on a restricted witness"
            );
        }
        let mut column = 0;
        loop {
            if column == n {
                break;
            }
            indices[column] += 1;
            if indices[column] < steps[column].len() {
                break;
            }
            indices[column] = 0;
            column += 1;
        }
        if column == n {
            break;
        }
    }
}
