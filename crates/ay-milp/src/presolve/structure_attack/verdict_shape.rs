// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// A model that carries NO OBJECTIVE is a FEASIBILITY problem, and the crate
/// treats that as a distinct verdict shape (`Model::has_objective`'s doc, and
/// `BabSession::check`'s: reading the distinction off the coefficients "made
/// this lane answer `Feasible` where `LpSession` answered `Optimal { value: 0 }`
/// on the very same model").
///
/// `binary_complement` guards its emission with `if model.has_objective()`, and
/// `objective_singleton` declines outright on `!model.has_objective()`.
/// Structural elimination must likewise preserve the bit explicitly rather
/// than infer it from the (possibly empty or all-zero) coefficient vector.
#[test]
fn attack_feasibility_model_keeps_its_verdict_shape() {
    let mut m = Model::new();
    let a = m.add_int_col(2.0, 2.0); // fixed -> eliminated
    let b = m.add_int_col(0.0, 3.0);
    m.add_row(f64::NEG_INFINITY, 10.0, &[(a, 1.0), (b, 1.0)]); // redundant
    m.add_row(0.0, 5.0, &[(b, 1.0)]); // redundant
    assert!(
        !m.has_objective(),
        "the fixture must be a feasibility model"
    );

    let (reduced, post) = eliminate_structure(&m, None).expect("the fixed column fires the pass");
    assert!(post.const_delta().is_zero());

    // WHAT THE ENGINE ANSWERS ON EACH.
    let opts = crate::SolveOpts::new();
    let orig_verdict = crate::BabSession::new(m.clone(), &opts)
        .unwrap()
        .check()
        .unwrap();
    let red_verdict = crate::BabSession::new(reduced.clone(), &opts)
        .unwrap()
        .check()
        .unwrap();
    eprintln!("ORIGINAL (no objective) -> {orig_verdict:?}");
    eprintln!("REDUCED                 -> {red_verdict:?}");

    assert!(
        matches!(&orig_verdict, crate::Outcome::Feasible { .. }),
        "the original feasibility fixture returned {orig_verdict:?}"
    );
    assert!(
        matches!(&red_verdict, crate::Outcome::Feasible { .. }),
        "the reduced feasibility fixture returned {red_verdict:?}"
    );

    assert!(
        !reduced.has_objective(),
        "STRUCTURAL ELIMINATION TURNED A FEASIBILITY MODEL INTO AN OPTIMIZATION MODEL: \
         original has_objective={}, reduced has_objective={}; the engine answers {:?} on the \
         original and {:?} on the reduced model",
        m.has_objective(),
        reduced.has_objective(),
        orig_verdict,
        red_verdict,
    );
}

/// The inverse edge of the shape guard: an explicitly-set zero objective is
/// still an optimization problem. It must not be mistaken for no objective
/// merely because structural elimination rebuilds an empty coefficient list.
#[test]
fn attack_explicit_zero_objective_remains_optimization() {
    let mut m = Model::new();
    let a = m.add_int_col(2.0, 2.0); // fixed -> eliminated
    let b = m.add_int_col(0.0, 3.0);
    m.add_row(f64::NEG_INFINITY, 10.0, &[(a, 1.0), (b, 1.0)]);
    m.add_row(0.0, 5.0, &[(b, 1.0)]);
    m.set_objective(&[], Sense::Maximize);
    assert!(m.has_objective());

    let (reduced, post) = eliminate_structure(&m, None).expect("the fixed column fires the pass");
    assert!(post.const_delta().is_zero());
    assert!(
        reduced.has_objective(),
        "an explicitly-set zero objective became a feasibility model"
    );
    assert_eq!(reduced.sense(), Sense::Maximize);

    let opts = crate::SolveOpts::new();
    let orig_verdict = crate::BabSession::new(m, &opts).unwrap().check().unwrap();
    let red_verdict = crate::BabSession::new(reduced, &opts)
        .unwrap()
        .check()
        .unwrap();
    assert!(
        matches!(&orig_verdict, crate::Outcome::Optimal { value, .. } if value.is_zero()),
        "the original explicit-zero objective returned {orig_verdict:?}"
    );
    assert!(
        matches!(&red_verdict, crate::Outcome::Optimal { value, .. } if value.is_zero()),
        "the reduced explicit-zero objective returned {red_verdict:?}"
    );
}

/// END-TO-END through the real dispatch, with the arm actually armed.
#[test]
fn attack_feasibility_model_end_to_end_through_the_arm() {
    let _env_lock = ay_test_support::env::lock_env();
    let mut m = Model::new();
    let a = m.add_int_col(2.0, 2.0);
    let b = m.add_int_col(0.0, 3.0);
    m.add_row(f64::NEG_INFINITY, 10.0, &[(a, 1.0), (b, 1.0)]);
    m.add_row(0.0, 5.0, &[(b, 1.0)]);
    assert!(!m.has_objective());

    let opts = crate::SolveOpts::new();
    let off = crate::BabSession::new(m.clone(), &opts)
        .unwrap()
        .check()
        .unwrap();
    let on = {
        let opts = opts
            .clone()
            .with_engine(crate::EngineEconomics::new().with_struct_elim(true));
        crate::BabSession::new(m.clone(), &opts)
            .unwrap()
            .check()
            .unwrap()
    };

    let name = |o: &crate::Outcome| match o {
        crate::Outcome::Optimal { value, .. } => format!("OPTIMAL {value}"),
        crate::Outcome::Feasible { .. } => "FEASIBLE".to_string(),
        crate::Outcome::Infeasible { .. } => "INFEASIBLE".to_string(),
        other => format!("{other:?}"),
    };
    eprintln!("ARM OFF -> {}", name(&off));
    eprintln!("ARM ON  -> {}", name(&on));
    assert_eq!(
        name(&off),
        name(&on),
        "THE ARM CHANGED THE ANSWER END-TO-END on a feasibility model"
    );
}

/// Is the dispatch even REACHED on a no-objective model? Trace says.
#[test]
fn attack_probe_dispatch_reachability_on_a_feasibility_model() {
    let _env_lock = ay_test_support::env::lock_env();
    let mut r = R(0x1234_5678);
    let n = 12usize;
    let mut m = Model::new();
    for j in 0..n {
        if j % 5 == 0 {
            m.add_int_col(2.0, 2.0); // fixed
        } else {
            m.add_int_col(0.0, 4.0);
        }
    }
    for _ in 0..8 {
        let mut c: Vec<(Col, f64)> = Vec::new();
        for j in 0..n {
            let a = r.range(-3, 3) as f64;
            if a != 0.0 {
                c.push((Col(j as u32), a));
            }
        }
        if c.is_empty() {
            c.push((Col(0), 1.0));
        }
        m.add_row(-30.0, 30.0, &c); // wide: many rows redundant
    }
    assert!(!m.has_objective(), "fixture must be a feasibility model");
    assert!(
        eliminate_structure(&m, None).is_some(),
        "the pass must fire on the fixture"
    );

    let opts = crate::SolveOpts::new();
    let off = crate::BabSession::new(m.clone(), &opts)
        .unwrap()
        .check()
        .unwrap();
    let on = {
        let opts = opts
            .clone()
            .with_engine(crate::EngineEconomics::new().with_struct_elim(true));
        crate::BabSession::new(m.clone(), &opts)
            .unwrap()
            .check()
            .unwrap()
    };
    let name = |o: &crate::Outcome| match o {
        crate::Outcome::Optimal { value, .. } => format!("OPTIMAL {value}"),
        crate::Outcome::Feasible { .. } => "FEASIBLE".to_string(),
        crate::Outcome::Infeasible { .. } => "INFEASIBLE".to_string(),
        other => format!("{other:?}"),
    };
    eprintln!(
        "12-col feasibility model: ARM OFF -> {} | ARM ON -> {}",
        name(&off),
        name(&on)
    );
    assert_eq!(name(&off), name(&on), "THE ARM CHANGED THE ANSWER");
}

/// POSITIVE CONTROL for the reachability probe: the SAME model, but WITH an
/// objective. If the dispatch trace fires here and not on the feasibility
/// twin, the `has_objective` defect is latent rather than live.
#[test]
fn attack_probe_dispatch_reachability_with_an_objective() {
    let _env_lock = ay_test_support::env::lock_env();
    let mut r = R(0x1234_5678);
    let n = 12usize;
    let mut m = Model::new();
    for j in 0..n {
        if j % 5 == 0 {
            m.add_int_col(2.0, 2.0);
        } else {
            m.add_int_col(0.0, 4.0);
        }
    }
    for _ in 0..8 {
        let mut c: Vec<(Col, f64)> = Vec::new();
        for j in 0..n {
            let a = r.range(-3, 3) as f64;
            if a != 0.0 {
                c.push((Col(j as u32), a));
            }
        }
        if c.is_empty() {
            c.push((Col(0), 1.0));
        }
        m.add_row(-30.0, 30.0, &c);
    }
    m.set_objective(
        &(0..n).map(|j| (Col(j as u32), 1.0)).collect::<Vec<_>>(),
        Sense::Minimize,
    );
    let opts = crate::SolveOpts::new();
    let on = {
        let opts = opts
            .clone()
            .with_engine(crate::EngineEconomics::new().with_struct_elim(true));
        eprintln!(
            "=== WITH-OBJECTIVE TWIN, ARM ON: any struct-elim line below is the DISPATCH ==="
        );
        crate::BabSession::new(m.clone(), &opts)
            .unwrap()
            .check()
            .unwrap()
    };
    let off = crate::BabSession::new(m.clone(), &opts)
        .unwrap()
        .check()
        .unwrap();
    let val = |o: &crate::Outcome| match o {
        crate::Outcome::Optimal { value, .. } => format!("OPTIMAL {value}"),
        crate::Outcome::Feasible { .. } => "FEASIBLE".into(),
        other => format!("{other:?}"),
    };
    eprintln!(
        "WITH OBJECTIVE: ARM ON -> {} | ARM OFF -> {}",
        val(&on),
        val(&off)
    );
    assert_eq!(val(&on), val(&off));
}
