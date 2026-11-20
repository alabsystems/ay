// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use ay_milp::{BabSession, EngineEconomics, Model, Outcome, Sense, SolveOpts};
use num_rational::BigRational;

fn model(upper: f64) -> Model {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    model.add_row(f64::NEG_INFINITY, upper, &[(x, 2.0), (y, 2.0)]);
    model.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Maximize);
    model
}

fn options() -> SolveOpts {
    // Keep the real root separator responsible for this control. The normal
    // presolve/structural shortcuts can otherwise close this tiny instance.
    SolveOpts::new()
        .with_structure_routing(false)
        .with_time_limit(Duration::from_secs(20))
        .with_engine(
            EngineEconomics::new()
                .with_lattice(false)
                .with_dedup_cols(false)
                .with_presolve(false)
                .with_root_probe(false)
                .with_sym(false)
                .with_coef_tighten(false)
                .with_cuts(true),
        )
}

#[test]
fn integer_cut_actual_finished_tree_exports_replayable_fractional_separating_cut() {
    let source = model(3.0);
    let fractional = vec![
        BigRational::new(1.into(), 2.into()),
        BigRational::from_integer(1.into()),
    ];
    let mut relaxation = Model::new();
    let rx = relaxation.add_col(0.0, 1.0);
    let ry = relaxation.add_col(0.0, 1.0);
    relaxation.add_row(f64::NEG_INFINITY, 3.0, &[(rx, 2.0), (ry, 2.0)]);
    relaxation
        .check_point(&fractional)
        .expect("original LP-feasible fractional point");
    let mut session = BabSession::new(source.clone(), &options()).expect("session");
    let outcome = session.check().expect("actual native tree");
    assert!(matches!(outcome, Outcome::Optimal { .. }), "{outcome:?}");
    if let Outcome::Optimal {
        value,
        model_values,
        ..
    } = &outcome
    {
        assert_eq!(*value, BigRational::from_integer(1.into()));
        source
            .check_point(model_values)
            .expect("exact native source witness");
    }
    let summary = session.cut_harvest_summary();
    assert!(summary.native_tree_finished, "{summary:?}");
    assert!(summary.adoption_scan_complete, "{summary:?}");
    assert!(
        summary.adopted_root_sides > 0,
        "real root cuts must be adopted: {summary:?}"
    );
    let cuts = session.harvest_cuts();
    assert!(
        !cuts.is_empty(),
        "actual adopted rank-one cut must export: {summary:?}"
    );
    assert_eq!(summary.certified_sides, cuts.len());
    assert!(session.harvest_cuts().is_empty(), "drain once");
    assert!(
        cuts.iter().any(|cut| {
            let activity: BigRational = cut
                .coeffs
                .iter()
                .map(|(c, a)| a * &fractional[*c as usize])
                .sum();
            activity < cut.lb
        }),
        "a real integer cut must reject the original fractional LP point"
    );
    for cut in &cuts {
        cut.verify(&source)
            .expect("independent caller-model replay");
        assert!(cut
            .verify_with_deadline(&source, Some(std::time::Instant::now()))
            .is_err());
    }
    for (x, y) in [(0, 0), (1, 0), (0, 1)] {
        let point = [
            BigRational::from_integer(x.into()),
            BigRational::from_integer(y.into()),
        ];
        source.check_point(&point).expect("source integer witness");
        for cut in &cuts {
            let activity: BigRational = cut
                .coeffs
                .iter()
                .map(|(c, a)| a * &point[*c as usize])
                .sum();
            assert!(activity >= cut.lb);
        }
    }
}

#[test]
fn integer_cut_source_mutation_sibling_domains_and_tampering_cannot_lend_cut_authority() {
    let source = model(3.0);
    let mut session = BabSession::new(source.clone(), &options()).unwrap();
    let _ = session.check().unwrap();
    let cuts = session.harvest_cuts();
    assert_ne!(cuts, [] as [ay_milp::CertifiedIntegerCut; 0]);
    let relaxed = model(4.0);
    relaxed
        .check_point(&[
            BigRational::from_integer(1.into()),
            BigRational::from_integer(1.into()),
        ])
        .unwrap();
    for cut in &cuts {
        assert!(
            cut.verify(&relaxed).is_err(),
            "relaxing the actual premise invalidates its proof"
        );
        let mut malformed = cut.clone();
        malformed.coeffs[0].1 += BigRational::from_integer(1.into());
        assert!(malformed.verify(&source).is_err());
        let mut too_strong = cut.clone();
        too_strong.lb += BigRational::from_integer(1.into());
        assert!(too_strong.verify(&source).is_err());
        for value in [0.0, 1.0] {
            let mut child = source.clone();
            child.fix_col(child.col_at(0).unwrap(), value);
            cut.verify(&child)
                .expect("global source cut survives either sibling restriction");
        }
    }
    // A source fact introduced only in one domain cannot be replayed in its
    // sibling, even with identical column numbers.
    let mut local = model(4.0);
    let x = local.col_at(0).unwrap();
    let y = local.col_at(1).unwrap();
    local.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0), (y, 2.0)]);
    let mut local_session = BabSession::new(local, &options()).unwrap();
    let _ = local_session.check().unwrap();
    let local_cuts = local_session.harvest_cuts();
    assert_ne!(local_cuts, [] as [ay_milp::CertifiedIntegerCut; 0]);
    for cut in local_cuts {
        assert!(cut.verify(&relaxed).is_err());
    }
}

#[test]
fn integer_cut_harvest_is_invalidated_by_scope_mutation_new_check_and_failed_check() {
    let mut session = BabSession::new(model(3.0), &options()).unwrap();
    let _ = session.check().unwrap();
    assert!(session.cut_harvest_summary().certified_sides > 0);
    session.push().unwrap();
    assert_eq!(
        session.harvest_cuts(),
        [] as [ay_milp::CertifiedIntegerCut; 0]
    );
    let _ = session.check().unwrap();
    assert!(session.cut_harvest_summary().certified_sides > 0);
    session.pop().unwrap();
    assert!(
        session.harvest_cuts().is_empty(),
        "pop invalidates even a fresh scoped batch"
    );
    let _ = session.check().unwrap();
    let count = session.cut_harvest_summary().certified_sides;
    assert!(count > 0);
    let _ = session.check().unwrap();
    assert_eq!(
        session.harvest_cuts().len(),
        count,
        "a new check replaces rather than appends old cuts"
    );
    let _ = session.check().unwrap();
    let x = session.model().col_at(0).unwrap();
    session.fix_col(x, 0.0).unwrap();
    assert_eq!(
        session.harvest_cuts(),
        [] as [ay_milp::CertifiedIntegerCut; 0]
    );
    let mut other = BabSession::new(model(3.0), &options()).unwrap();
    let _ = other.check().unwrap();
    let x = other.model().col_at(0).unwrap();
    assert!(other.check_shared_binary_prefix(&[x, x]).is_err());
    assert!(
        other.harvest_cuts().is_empty(),
        "failed check cannot leave an old batch"
    );
}

#[test]
fn integer_cut_shadow_control_rows_are_not_advertised_as_real_cuts() {
    let mut opts = options();
    let engine = opts.engine().with_cut_shadow(2);
    opts = opts.with_engine(engine);
    let mut session = BabSession::new(model(3.0), &opts).unwrap();
    let _ = session.check().unwrap();
    assert_eq!(
        session.harvest_cuts(),
        [] as [ay_milp::CertifiedIntegerCut; 0]
    );
    assert_eq!(session.cut_harvest_summary().adopted_root_sides, 0);
}

/// One hidden ReLU layer lowered the way NY lowers it: per unit, a
/// continuous post-activation `y`, a binary phase `z`, and the big-M rows
/// `y >= h`, `y <= h - l(1 - z)`, `y <= u z` with `h = w·x + b` and
/// interval pre-activation bounds `l < 0 < u`. Every coefficient is dyadic,
/// so exact network evaluations are exact model points.
const RELU_UNITS: [([f64; 2], f64, f64); 4] = [
    ([1.0, -0.75], 0.25, 1.0),
    ([-0.5, 1.0], 0.125, -0.75),
    ([0.75, 0.5], -0.25, 0.5),
    ([-1.0, -0.25], 0.375, 0.75),
];

fn relu_network() -> Model {
    relu_network_with(false)
}

/// `relaxed` declares each phase column continuous in [0, 1]: the LP
/// relaxation of the same rows.
fn relu_network_with(relaxed: bool) -> Model {
    let mut model = Model::new();
    let x = [model.add_col(-1.0, 1.0), model.add_col(-1.0, 1.0)];
    let mut objective = Vec::new();
    for (w, b, c) in RELU_UNITS {
        let l = b - w[0].abs() - w[1].abs();
        let u = b + w[0].abs() + w[1].abs();
        assert!(l < 0.0 && 0.0 < u, "every unit must be unstable");
        let y = model.add_col(0.0, u);
        let z = if relaxed {
            model.add_col(0.0, 1.0)
        } else {
            model.add_binary_col()
        };
        // y - w·x >= b
        model.add_row(b, f64::INFINITY, &[(y, 1.0), (x[0], -w[0]), (x[1], -w[1])]);
        // y - w·x - l z <= b - l
        model.add_row(
            f64::NEG_INFINITY,
            b - l,
            &[(y, 1.0), (x[0], -w[0]), (x[1], -w[1]), (z, -l)],
        );
        // y - u z <= 0
        model.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -u)]);
        objective.push((y, c));
    }
    model.set_objective(&objective, Sense::Maximize);
    model
}

/// The exact network point for input `(x0, x1)`: `[x0, x1, y_1, z_1, ...]`.
fn relu_point(x0: f64, x1: f64) -> Vec<BigRational> {
    let q = |v: f64| BigRational::from_float(v).expect("finite dyadic");
    let mut point = vec![q(x0), q(x1)];
    for (w, b, _) in RELU_UNITS {
        let h = q(w[0]) * q(x0) + q(w[1]) * q(x1) + q(b);
        let active = h > BigRational::from_integer(0.into());
        point.push(if active {
            h
        } else {
            BigRational::from_integer(0.into())
        });
        point.push(BigRational::from_integer(i32::from(active).into()));
    }
    point
}

#[test]
fn integer_cut_big_m_relu_root_cuts_export_through_split_proofs() {
    let source = relu_network();
    let mut session = BabSession::new(source.clone(), &options()).expect("session");
    let outcome = session.check().expect("actual native tree");
    assert!(matches!(outcome, Outcome::Optimal { .. }), "{outcome:?}");
    let before = session.cut_harvest_summary();
    assert!(before.native_tree_finished, "{before:?}");
    assert!(
        before.unsupported_sides > 0,
        "big-M rows mix continuous columns, so rank-one rounding must leave \
         adopted sides unsupported: {before:?}"
    );
    let rank_one = session.harvest_cuts();
    let report =
        session.certify_cuts_by_split(Some(std::time::Instant::now() + Duration::from_secs(60)));
    let after = session.cut_harvest_summary();
    let split_cuts = session.harvest_cuts();
    eprintln!(
        "before={before:?} rank_one={} report={report:?} after={after:?}",
        rank_one.len()
    );
    assert!(!report.interrupted && report.remaining == 0, "{report:?}");
    assert_eq!(report.attempted, before.unsupported_sides, "{report:?}");
    assert!(
        report.certified > 0,
        "split proofs must export some big-M cut: {report:?}"
    );
    assert_eq!(split_cuts.len(), report.certified);
    assert_eq!(
        after.certified_sides,
        before.certified_sides + report.certified
    );
    assert_eq!(
        after.unsupported_sides,
        before.unsupported_sides - report.certified
    );
    assert_eq!(
        session.certify_cuts_by_split(None).attempted,
        0,
        "tried sides are not retried"
    );

    // Every exported cut holds at every exact network evaluation on a grid
    // (these are integer-feasible model points), independently of its proof.
    let grid: Vec<f64> = (-4..=4).map(|k| f64::from(k) * 0.25).collect();
    let mut points = Vec::new();
    for &a in &grid {
        for &b in &grid {
            let point = relu_point(a, b);
            source
                .check_point(&point)
                .expect("network point is feasible");
            points.push(point);
        }
    }
    let mut separates_some_lp_point = false;
    for cut in &split_cuts {
        assert!(
            matches!(cut.proof, ay_milp::IntegerCutProof::ElementarySplit { .. }),
            "{:?}",
            cut.proof
        );
        cut.verify(&source)
            .expect("independent caller-model replay");
        for point in &points {
            let activity: BigRational = cut
                .coeffs
                .iter()
                .map(|(c, a)| a * &point[*c as usize])
                .sum();
            assert!(activity >= cut.lb, "cut violated at a network point");
        }
        // A narrower sibling (one phase fixed either way) keeps every premise.
        let z = source.col_at(3).unwrap();
        for phase in [0.0, 1.0] {
            let mut child = source.clone();
            child.fix_col(z, phase);
            cut.verify(&child)
                .expect("source-global cut survives a sibling box");
        }
        // The exact LP optimum of the cut's own form over the relaxation lies
        // below `lb`: the cut is a genuine integer consequence, not an LP row.
        let mut relaxation = relu_network_with(true);
        let t = relaxation.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let mut tie = vec![(t, -1.0)];
        let mut dyadic = true;
        for (c, a) in &cut.coeffs {
            let f = num_traits::ToPrimitive::to_f64(a).unwrap_or(f64::NAN);
            dyadic &= BigRational::from_float(f).as_ref() == Some(a);
            tie.push((relaxation.col_at(*c as usize).unwrap(), f));
        }
        if dyadic {
            relaxation.add_row(0.0, 0.0, &tie);
            let mut lp = ay_milp::LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
            if let Outcome::Optimal { value, .. } = lp.optimize(t, Sense::Minimize).unwrap() {
                separates_some_lp_point |= value < cut.lb;
            }
        }
    }
    assert!(
        separates_some_lp_point,
        "some exported cut must cut the LP relaxation"
    );
    // Mutation and scope changes invalidate the retained sides too.
    let _ = session.check().unwrap();
    session.push().unwrap();
    assert_eq!(session.certify_cuts_by_split(None).attempted, 0);
}
