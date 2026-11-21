// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The witness check (`CpSatEngine::set_witness`, `AY_CP_WITNESS`) sees the
//! encoders' clauses and auxiliary variables, knows constants, and counts
//! the clauses it cannot decide.

use super::*;
use crate::domain::Domain;
use crate::engine::CpSolveResult;

/// Two 2x2 squares in a 4x2 box, a known placement as the witness.
fn diffn_engine(witness: &[i64; 4]) -> CpSatEngine {
    let mut engine = CpSatEngine::new();
    let x0 = engine.new_int_var(Domain::new(0, 2), Some("x0"));
    let x1 = engine.new_int_var(Domain::new(0, 2), Some("x1"));
    let y0 = engine.new_int_var(Domain::new(0, 0), Some("y0"));
    let y1 = engine.new_int_var(Domain::new(0, 0), Some("y1"));
    // Constants: not named in the witness, known through their domain.
    let two = engine.new_int_var(Domain::singleton(2), None);
    engine.add_constraint(Constraint::Diffn {
        x: vec![x0, x1],
        y: vec![y0, y1],
        dx: vec![two, two],
        dy: vec![two, two],
    });
    engine.set_witness(&[
        (x0, witness[0]),
        (x1, witness[1]),
        (y0, witness[2]),
        (y1, witness[3]),
    ]);
    engine
}

#[test]
fn test_witness_checks_encoder_clauses_and_auxiliaries() {
    let mut engine = diffn_engine(&[0, 2, 0, 0]);
    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
    let (checked, falsified, unknown) = engine.witness_counts().expect("witness set");
    assert!(checked > 0, "encoder clauses must be checked");
    assert_eq!(falsified, 0, "a real solution falsifies nothing");
    assert_eq!(
        unknown, 0,
        "constants and the separation indicators are known"
    );
}

#[test]
fn test_witness_reports_a_falsified_encoder_clause() {
    // Overlapping squares: not a solution, so the at-least-one-separation
    // clause (an encoder clause, added before search) is falsified.
    let mut engine = diffn_engine(&[0, 1, 0, 0]);
    let _ = engine.solve();
    let (_, falsified, _) = engine.witness_counts().expect("witness set");
    assert!(falsified > 0, "the encoder clause must be seen falsified");
}

#[test]
fn test_witness_knows_circuit_positions() {
    let mut engine = CpSatEngine::new();
    let succ: Vec<IntVarId> = (0..4)
        .map(|i| engine.new_int_var(Domain::new(1, 4), Some(&format!("s{i}"))))
        .collect();
    engine.add_constraint(Constraint::Circuit {
        succ: succ.clone(),
        base: 1,
    });
    // 1 -> 3 -> 2 -> 4 -> 1 (nodes numbered from 1).
    let witness: Vec<(IntVarId, i64)> = succ.iter().copied().zip([3, 4, 2, 1]).collect();
    engine.set_witness(&witness);
    assert!(matches!(engine.solve(), CpSolveResult::Sat(_)));
    let (checked, falsified, unknown) = engine.witness_counts().expect("witness set");
    assert!(checked > 0);
    assert_eq!(falsified, 0);
    assert_eq!(unknown, 0, "positions follow from the successors");
}

#[test]
fn test_witness_counts_unknown_clauses() {
    // `z` is neither named nor fixed: clauses over it are unknown, counted.
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::new(0, 3), Some("x"));
    let z = engine.new_int_var(Domain::new(0, 3), None);
    engine.add_constraint(Constraint::Maximum {
        result: z,
        args: vec![x],
    });
    engine.set_witness(&[(x, 2)]);
    let _ = engine.solve();
    let (_, falsified, unknown) = engine.witness_counts().expect("witness set");
    assert_eq!(falsified, 0);
    assert!(unknown > 0, "clauses over z must be counted unknown");
}
