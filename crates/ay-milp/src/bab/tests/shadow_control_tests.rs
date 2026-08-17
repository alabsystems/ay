// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ---- THE PERTURBATION-MATCHED CUT CONTROL (`the cut-shadow knob`) ----
//
// The arm's entire value rests on TWO properties that pull against each other, so
// both are pinned here rather than asserted in prose:
//
//   (a) INFORMATION-FREE  -- it removes no point of the LP relaxation. Checked in
//       EXACT RATIONAL arithmetic, against the model's own column bounds, which is
//       the frame the solver's certificates live in. An f64 check would not be a
//       proof of the property that matters.
//   (b) BINDING AT THE ROOT VERTEX -- each row's activity at the cut-free root
//       vertex EQUALS its right-hand side. A row that is slack everywhere perturbs
//       nothing, and a vacuous control would make the whole measurement a
//       tautology.
//
// Plus the geometry match the measurement quotes (row count, nonzero count) and the
// one outcome that would make the arm a bug rather than a control: a changed answer.

/// A three-column model whose root vertex sits on a mixture of lower and upper
/// bounds, plus a hand-built "cut model" standing in for what the loop installs.
fn shadow_fixture() -> (Model, Model, Vec<f64>) {
    let mut m = Model::new();
    let a = m.add_int_col(0.0, 4.0);
    let b = m.add_int_col(-3.0, 5.0);
    let c = m.add_col(0.0, 10.0);
    let d = m.add_int_col(0.0, 1.0);
    let e = m.add_int_col(2.0, 9.0);
    let f = m.add_col(-1.0, 6.0);
    m.set_objective(&[(a, 1.0), (b, 1.0), (c, 1.0)], Sense::Minimize);
    m.add_row(1.0, f64::INFINITY, &[(a, 1.0), (b, 1.0), (c, 1.0)]);
    // The cut-free root vertex: every column on a bound EXCEPT `c`, which sits
    // strictly inside. `c` is the basic column a real cut's support routinely hits
    // and the one case no supporting inequality can anchor, so it exercises the
    // re-placement path; `d`/`e`/`f` are the anchored columns it can be re-placed on.
    let x0 = vec![0.0, 5.0, 2.5, 1.0, 2.0, -1.0];
    let mut cut = m.clone();
    cut.add_row(3.0, f64::INFINITY, &[(a, 2.0), (b, -7.0), (c, 1.5)]);
    cut.add_row(f64::NEG_INFINITY, -1.0, &[(a, -1.0), (c, 4.0)]);
    cut.add_row(2.0, f64::INFINITY, &[(d, 1.0), (e, -0.5), (f, 3.0)]);
    (m, cut, x0)
}

#[test]
fn the_shadow_pool_removes_no_point_of_the_box_in_exact_arithmetic() {
    let (model, cut, x0) = shadow_fixture();
    let out = shadow_control_model(&model, Some(&x0), &cut, ShadowMode::Binding);
    assert_eq!(
        out.num_rows() - model.num_rows(),
        cut.num_rows() - model.num_rows(),
        "the control must add EXACTLY one row per installed cut"
    );
    for r in model.num_rows()..out.num_rows() {
        let (coeffs, lb, ub) = out.row(Row(r as u32));
        // The minimum and maximum of the row's activity over the whole BOX, exact.
        // A row is implied by the bounds iff `lb <= min` and `max <= ub`, and that
        // test is NECESSARY AND SUFFICIENT -- it is not a sample, it is the whole
        // half-space. Every point of the LP relaxation is in the box, and every
        // node's box is a SUB-box of it, so implication here is implication
        // everywhere in the tree.
        let (mut lo, mut hi) = (BigRational::zero(), BigRational::zero());
        for &(c, a) in coeffs {
            let a = exact(a).expect("finite coefficient");
            let (cl, cu) = model.col_bounds(Col(c));
            let (cl, cu) = (
                exact(cl).expect("the control only uses finitely-bounded columns"),
                exact(cu).expect("the control only uses finitely-bounded columns"),
            );
            let (t0, t1) = (&a * &cl, &a * &cu);
            if t0 <= t1 {
                lo += t0;
                hi += t1;
            } else {
                lo += t1;
                hi += t0;
            }
        }
        if lb.is_finite() {
            let lb = exact(lb).expect("finite bound");
            assert!(
                lb <= lo,
                "shadow row {r} cuts the box off below: lb {lb} > box min {lo}"
            );
        }
        if ub.is_finite() {
            let ub = exact(ub).expect("finite bound");
            assert!(
                hi <= ub,
                "shadow row {r} cuts the box off above: box max {hi} > ub {ub}"
            );
        }
    }
}

#[test]
fn every_shadow_row_is_tight_at_the_cut_free_root_vertex() {
    let (model, cut, x0) = shadow_fixture();
    let out = shadow_control_model(&model, Some(&x0), &cut, ShadowMode::Binding);
    for r in model.num_rows()..out.num_rows() {
        let (coeffs, lb, ub) = out.row(Row(r as u32));
        let act: f64 = coeffs.iter().map(|&(c, a)| a * x0[c as usize]).sum();
        let rhs = if lb.is_finite() { lb } else { ub };
        assert!(
            (act - rhs).abs() <= 1e-9 * (1.0 + rhs.abs()),
            "shadow row {r} is SLACK at the root vertex (activity {act}, rhs {rhs}); \
             a control that binds nowhere perturbs nothing and is vacuous"
        );
    }
}

#[test]
fn the_shadow_pool_matches_the_real_pool_row_for_row_and_nonzero_for_nonzero() {
    let (model, cut, x0) = shadow_fixture();
    let out = shadow_control_model(&model, Some(&x0), &cut, ShadowMode::Binding);
    let n0 = model.num_rows();
    assert_eq!(out.num_rows() - n0, cut.num_rows() - n0);
    for k in 0..(cut.num_rows() - n0) {
        let (real, rlb, _) = cut.row(Row((n0 + k) as u32));
        let (shad, slb, sub) = out.row(Row((n0 + k) as u32));
        assert_eq!(
            real.len(),
            shad.len(),
            "row {k}: nonzero count must match ({} vs {})",
            real.len(),
            shad.len()
        );
        let mut rm: Vec<f64> = real.iter().map(|&(_, a)| a.abs()).collect();
        let mut sm: Vec<f64> = shad.iter().map(|&(_, a)| a.abs()).collect();
        rm.sort_by(f64::total_cmp);
        sm.sort_by(f64::total_cmp);
        assert_eq!(
            rm, sm,
            "row {k}: the multiset of coefficient MAGNITUDES must match"
        );
        // And the sidedness the cut had.
        assert_eq!(rlb.is_finite(), slb.is_finite(), "row {k}: orientation");
        assert_eq!(rlb.is_finite(), !sub.is_finite(), "row {k}: orientation");
    }
}

#[test]
fn a_row_with_nowhere_to_re_place_its_orphans_loses_them_rather_than_cutting() {
    // The ONE way the nonzero match above can fail, pinned so it is a known
    // shortfall rather than a surprise: when the model has no anchored column left
    // to carry a basic column's magnitude, the term is DROPPED. That makes the
    // control marginally sparser than the real pool -- never invalid, and never
    // informative. On the corpus the shortfall is zero (measured: real_nnz ==
    // shadow_nnz on every instance), because real models have far more nonbasic
    // columns than any one cut has support.
    let mut m = Model::new();
    let a = m.add_int_col(0.0, 4.0);
    let c = m.add_col(0.0, 10.0);
    m.set_objective(&[(a, 1.0), (c, 1.0)], Sense::Minimize);
    m.add_row(1.0, f64::INFINITY, &[(a, 1.0), (c, 1.0)]);
    let mut cut = m.clone();
    cut.add_row(3.0, f64::INFINITY, &[(a, 2.0), (c, 1.5)]);
    let out = shadow_control_model(&m, Some(&[0.0, 2.5]), &cut, ShadowMode::Binding);
    assert_eq!(
        out.num_rows() - m.num_rows(),
        1,
        "the row count still matches"
    );
    let (coeffs, lb, _) = out.row(Row(m.num_rows() as u32));
    assert_eq!(coeffs, &[(0u32, 2.0)], "only the anchorable term survives");
    assert!(lb <= 0.0, "and it is still implied by `a >= 0`");
}

#[test]
fn the_slack_control_is_valid_but_binds_nowhere() {
    // The report's own §9(1) construction, pinned for what it IS and for what it is
    // NOT: a perfect coefficient match that never touches the optimal face. Both
    // halves matter — the first is why it is a legitimate control, the second is why
    // it is a WEAKER one than the binding construction, and the corpus arms then
    // measure which of the two the perturbation rides on.
    let (model, cut, x0) = shadow_fixture();
    let out = shadow_control_model(&model, Some(&x0), &cut, ShadowMode::Slack);
    let n0 = model.num_rows();
    assert_eq!(out.num_rows() - n0, cut.num_rows() - n0);
    let mut any_slack = false;
    for k in 0..(cut.num_rows() - n0) {
        let (real, _, _) = cut.row(Row((n0 + k) as u32));
        let (shad, lb, ub) = out.row(Row((n0 + k) as u32));
        assert_eq!(
            real, shad,
            "row {k}: the coefficient vector must be VERBATIM"
        );
        let act: f64 = shad.iter().map(|&(c, a)| a * x0[c as usize]).sum();
        let (mut lo, mut hi) = (0.0f64, 0.0f64);
        for &(c, a) in shad {
            let (cl, cu) = model.col_bounds(Col(c));
            lo += if a >= 0.0 { a * cl } else { a * cu };
            hi += if a >= 0.0 { a * cu } else { a * cl };
        }
        if lb.is_finite() {
            assert!(lb <= lo, "row {k} cuts the box off below");
            any_slack |= act > lb + 1e-9 * (1.0 + lb.abs());
        }
        if ub.is_finite() {
            assert!(hi <= ub, "row {k} cuts the box off above");
            any_slack |= act < ub - 1e-9 * (1.0 + ub.abs());
        }
    }
    assert!(
        any_slack,
        "the slack control is supposed to be SLACK at the root vertex; if it binds \
         there it is not the weaker control this arm exists to be"
    );
}

#[test]
fn the_shadow_arm_refuses_rather_than_guessing_without_a_root_vertex() {
    let (model, cut, _) = shadow_fixture();
    let out = shadow_control_model(&model, None, &cut, ShadowMode::Binding);
    assert_eq!(
        out.num_rows(),
        model.num_rows(),
        "with no cut-free root vertex there is no anchor, so the arm must \
         degenerate to the no-cut model rather than invent one"
    );
}

#[test]
fn the_shadow_arm_does_not_change_the_answer() {
    // A control that moves a verdict or an objective is not information-free; it is
    // a bug. This is the in-process version of the corpus-wide check.
    let _env_lock = lock_env();
    let mut m = Model::new();
    let x = m.add_int_col(0.0, 10.0);
    let y = m.add_int_col(0.0, 10.0);
    m.set_objective(&[(x, -1.0), (y, -2.0)], Sense::Minimize);
    m.add_row(f64::NEG_INFINITY, 7.5, &[(x, 3.0), (y, 2.0)]);
    m.add_row(f64::NEG_INFINITY, 9.5, &[(x, 1.0), (y, 4.0)]);
    let opts = SolveOpts::default();
    let base = solve_milp(&m, &opts);
    let shadow = {
        let opts = opts
            .clone()
            .with_engine(crate::EngineEconomics::new().with_cut_shadow(1));
        solve_milp(&m, &opts)
    };
    match (&base, &shadow) {
        (Outcome::Optimal { value: a, .. }, Outcome::Optimal { value: b, .. }) => {
            assert_eq!(a, b, "the control changed the optimum")
        }
        other => panic!("both arms must prove this model: {other:?}"),
    }
}
