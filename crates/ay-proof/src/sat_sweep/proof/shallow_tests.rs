// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Two copies of one gate chain over the same inputs, a miter on their
//! outputs: every copied gate merges into its twin over the cut cone, and the
//! swept refutation closes.

use crate::sat_sweep::{literal, refute, Gate, SweepLimits};
use ay_sat::Literal;

/// `depth` levels of `and`/`xor` over inputs `0..inputs`, built twice, and a
/// unit clause asserting that the two outputs differ; the index of that
/// clause.
fn twin_chains(depth: usize) -> (Vec<Gate>, Vec<Vec<Literal>>, usize) {
    let inputs = 4;
    let mut gates: Vec<Gate> = (0..inputs).map(|_| Gate::Input).collect();
    let mut cnf: Vec<Vec<Literal>> = Vec::new();
    let mut outputs = Vec::new();
    for _copy in 0..2 {
        let mut previous = 0;
        for level in 0..depth {
            let (left, right) = (previous, 1 + level % (inputs - 1));
            let out = gates.len();
            let (l, r, o) = (
                literal(left, false),
                literal(right, false),
                literal(out, false),
            );
            if level % 2 == 0 {
                gates.push(Gate::And(vec![l, r]));
                cnf.extend([vec![o.negated(), l], vec![o.negated(), r]]);
                cnf.push(vec![o, l.negated(), r.negated()]);
            } else {
                gates.push(Gate::Xor(vec![l, r]));
                cnf.extend([
                    vec![o.negated(), l, r],
                    vec![o.negated(), l.negated(), r.negated()],
                ]);
                cnf.extend([vec![o, l.negated(), r], vec![o, l, r.negated()]]);
            }
            previous = out;
        }
        outputs.push(previous);
    }
    let miter = gates.len();
    let (a, b, m) = (
        literal(outputs[0], false),
        literal(outputs[1], false),
        literal(miter, false),
    );
    gates.push(Gate::Xor(vec![a, b]));
    cnf.extend([
        vec![m.negated(), a, b],
        vec![m.negated(), a.negated(), b.negated()],
    ]);
    cnf.extend([vec![m, a.negated(), b], vec![m, a, b.negated()]]);
    cnf.push(vec![m]);
    let root = cnf.len() - 1;
    (gates, cnf, root)
}

#[test]
fn twin_chains_merge_gate_by_gate_and_the_miter_is_refuted() {
    let (gates, cnf, root) = twin_chains(48);
    let mut keep_going = || true;
    let dag = refute(
        gates,
        &cnf,
        &[root],
        false,
        SweepLimits::standalone(),
        &mut keep_going,
    );
    assert!(dag.is_some(), "the twin miter must be refuted");
}

#[test]
fn a_miter_over_different_chains_is_never_refuted() {
    // `((x0 ∧ x1) ⊕ x2) ∧ x3` twice; the second copy's first gate is then
    // rewired to `x0 ∧ x3`, so the outputs differ at `x0 = x3 = 1, x1 = 0`
    // and no refutation may exist.
    let depth = 3;
    let (mut gates, mut cnf, root) = twin_chains(depth);
    let first_of_second = 4 + depth;
    let (other, out) = (literal(3, false), literal(first_of_second, false));
    gates[first_of_second] = Gate::And(vec![literal(0, false), other]);
    let start = cnf
        .iter()
        .position(|clause| clause.first() == Some(&out.negated()))
        .expect("the gate's clauses");
    cnf[start + 1] = vec![out.negated(), other];
    cnf[start + 2] = vec![out, literal(0, true), other.negated()];
    let mut keep_going = || true;
    assert!(refute(
        gates,
        &cnf,
        &[root],
        false,
        SweepLimits::standalone(),
        &mut keep_going
    )
    .is_none());
}
