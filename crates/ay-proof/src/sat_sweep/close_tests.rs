// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The direct closing refutation's three answers.

use super::*;

fn pos(var: usize) -> Literal {
    literal(var, false)
}

fn neg(var: usize) -> Literal {
    literal(var, true)
}

/// Inputs `a b` (0, 1) and `g = a ∧ b` (2), the root unit `(g)` last, and
/// `(not a)` too when `refutable`.
fn conjunction(refutable: bool) -> (Vec<Gate>, Vec<Vec<Literal>>, usize) {
    let mut cnf = vec![
        vec![neg(2), pos(0)],
        vec![neg(2), pos(1)],
        vec![pos(2), neg(0), neg(1)],
    ];
    if refutable {
        cnf.push(vec![neg(0)]);
    }
    cnf.push(vec![pos(2)]);
    let root = cnf.len() - 1;
    let gates = vec![Gate::Input, Gate::Input, Gate::And(vec![pos(0), pos(1)])];
    (gates, cnf, root)
}

fn direct(refutable: bool) -> Direct {
    let (gates, cnf, root) = conjunction(refutable);
    let bytes = ResolutionProofLimits::default().max_proof_output_bytes;
    let mut keep_going = || true;
    refute_directly(
        gates,
        &cnf,
        &[root],
        true,
        SweepLimits::standalone(),
        bytes,
        &mut keep_going,
    )
}

/// A satisfiable CNF is reported as one, which only its solve over every
/// clause may say: the lemma it blasts is false, and no lane after this one
/// can refute it (`complete_blast/transport.rs`, `Directly::Satisfiable`).
#[test]
fn a_model_of_every_clause_is_reported_and_a_refutation_is_kept() {
    assert!(matches!(direct(false), Direct::Satisfiable));
    let Direct::Refuted(dag) = direct(true) else {
        panic!("the refutable conjunction must be refuted");
    };
    dag.validate().expect("the refutation replays");
}
