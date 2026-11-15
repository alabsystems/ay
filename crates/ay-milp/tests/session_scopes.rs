// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope-level soundness properties of `BabSession`, salvaged from the
//! retired `milp-for-ny` branch (archived at tag `archive/milp-for-ny`) when
//! it was audited against main on 2026-09-10: main had no test of either
//! property.

use ay_milp::{BabSession, Model, Outcome, SolveOpts};
use num_rational::BigRational;

/// A binary column fixed to a FRACTIONAL value inside a scope is an empty box
/// for an integer column. Whatever the engine answers has to be sound against
/// the session's own view of the model: an `Infeasible` verdict's evidence
/// must verify against that view, and `Unknown` is acceptable (fail-closed).
/// A sat answer would be a wrong verdict. Popping the scope restores the
/// original, feasible model.
#[test]
fn fractionally_fixed_binary_stays_sound() {
    let mut m = Model::new();
    let b = m.add_binary_col();
    let x = m.add_col(0.0, 1.0);
    m.add_row(0.0, f64::INFINITY, &[(x, 1.0), (b, 1.0)]);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    s.push().unwrap();
    s.fix_col(b, 0.5).unwrap();
    // The session's current view: b's box shrunk to [0.5, 0.5].
    let mut view = m.clone();
    view.fix_col(b, 0.5);
    match s.check().unwrap() {
        Outcome::Infeasible { cert, tree_cert } => {
            if let Some(c) = &cert {
                c.verify(&view).unwrap();
            }
            if let Some(t) = &tree_cert {
                t.verify(&view).unwrap();
            }
        }
        Outcome::Unknown { .. } => {} // fail-closed is acceptable
        other => panic!("expected Infeasible/Unknown, got {other:?}"),
    }
    s.pop().unwrap();
    assert!(
        s.check().unwrap().is_sat(),
        "popping the scope restores the feasible model"
    );
}

/// A seeded incumbent that is itself feasible is a complete answer to a
/// feasibility check: the witness the session returns must satisfy the model,
/// and — with no objective to improve on — it must BE the seed rather than an
/// arbitrary other feasible point, so an external heuristic's answer is
/// consumed and not merely stored.
#[test]
fn seeded_incumbent_is_the_witness() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    s.seed_incumbent(&[1.0, 0.0]);
    s.hint_branch_order(&[y, x]);
    let model_values = match s.check().unwrap() {
        Outcome::Feasible { model_values, .. } | Outcome::Optimal { model_values, .. } => {
            model_values
        }
        other => panic!("expected a sat verdict, got {other:?}"),
    };
    m.check_point(&model_values).unwrap();
    assert_eq!(
        model_values[x.index()],
        BigRational::from_integer(1.into()),
        "the seed is the answer"
    );
}
