// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::sat_sweep::{literal, Gate, SweepLimits};

#[test]
fn marks_answer_as_a_set_and_clear_in_one_step() {
    let mut marks = Marks::new(4);
    assert!(marks.insert(2));
    assert!(!marks.insert(2));
    assert!(marks.contains(2) && !marks.contains(1));
    // Past the initial length it grows rather than refusing.
    assert!(marks.insert(9) && marks.contains(9));
    marks.clear();
    assert!(!marks.contains(2) && !marks.contains(9));
    assert!(marks.insert(2));
}

#[test]
fn a_generation_wrap_forgets_every_mark() {
    let mut marks = Marks::new(2);
    marks.generation = u32::MAX;
    assert!(marks.insert(1));
    marks.clear();
    assert!(!marks.contains(1));
    assert!(marks.insert(1));
}

#[test]
fn local_indices_follow_first_appearance_and_reset() {
    let mut local = LocalIndex::new(2);
    let mut next = 0;
    let mut fresh = |next: &mut usize| {
        *next += 1;
        *next - 1
    };
    assert_eq!(local.index_of(7, || fresh(&mut next)), 0);
    assert_eq!(local.index_of(3, || fresh(&mut next)), 1);
    assert_eq!(local.index_of(7, || fresh(&mut next)), 0);
    local.clear();
    next = 0;
    assert_eq!(local.index_of(3, || fresh(&mut next)), 0);
}

/// Two inputs, `g2 = a ∧ b`, `g3 = g2 ∧ a`: the Tseitin clauses and gates.
fn and_chain() -> (Vec<Gate>, Vec<Vec<ay_sat::Literal>>) {
    let and = |out: usize, left: usize, right: usize| {
        vec![
            vec![literal(out, true), literal(left, false)],
            vec![literal(out, true), literal(right, false)],
            vec![
                literal(out, false),
                literal(left, true),
                literal(right, true),
            ],
        ]
    };
    let gates = vec![
        Gate::Input,
        Gate::Input,
        Gate::And(vec![literal(0, false), literal(1, false)]),
        Gate::And(vec![literal(2, false), literal(0, false)]),
    ];
    let mut cnf = and(2, 0, 1);
    cnf.extend(and(3, 2, 0));
    cnf.push(vec![literal(3, false)]);
    (gates, cnf)
}

#[test]
fn a_cut_cone_keeps_the_gates_at_the_cut_free_and_says_so() {
    let (gates, cnf) = and_chain();
    let root = cnf.len() - 1;
    let mut keep_going = || true;
    let sweep = Sweep::new(
        gates,
        &cnf,
        &[root],
        false,
        SweepLimits::standalone(),
        &mut keep_going,
    )
    .expect("a well-formed sweep");
    // One edge below `g3`: `g2` and `a` are in the cone, `g2` free.
    assert_eq!(sweep.cone_within(&[3], 1), Some((vec![0, 2, 3], true)));
    // Uncut, it is the whole cone, and nothing was cut.
    let whole = sweep.cone(&[3]).expect("a local cone");
    assert_eq!(whole, vec![0, 1, 2, 3]);
    assert_eq!(sweep.cone_within(&[3], usize::MAX), Some((whole, false)));
    // An input has no operands: reaching it at the cut cuts nothing.
    assert_eq!(sweep.cone_within(&[2], 1), Some((vec![0, 1, 2], false)));
}
