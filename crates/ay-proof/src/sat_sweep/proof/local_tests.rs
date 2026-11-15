// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A candidate's local problem never reads a root, however many roots the
//! CNF has, and the closing problem carries every root, each root variable
//! numbered into it once.
//!
//! A split's leaf core is swept with every clause no core gate defines as a
//! root (`split/core_sweep.rs`): measured 2026-10-15 on the strict
//! checker's 64-bit `(x / 7) * 7 <= x`, 22,760-22,782 roots over about
//! 19,390 variables per leaf. Asking each candidate clause whether it is a
//! root by scanning them was most of the split's time. That cost is a timing
//! property no test here sees; these pin what the index and the closing
//! map must keep meaning.

use super::*;

/// The parity of inputs `0 .. over`, as a chain of `xor` gates appended to
/// `gates` with their Tseitin rows.
fn parity_chain(gates: &mut Vec<Gate>, cnf: &mut Vec<Vec<Literal>>, over: usize) -> Literal {
    let mut parity = literal(0, false);
    for input in 1..over {
        let x = literal(input, false);
        let g = literal(gates.len(), false);
        gates.push(Gate::Xor(vec![parity, x]));
        cnf.push(vec![g.negated(), parity, x]);
        cnf.push(vec![g.negated(), parity.negated(), x.negated()]);
        cnf.push(vec![g, parity.negated(), x]);
        cnf.push(vec![g, parity, x.negated()]);
        parity = g;
    }
    parity
}

/// Inputs `x_0 .. x_{width-1}`, two copies of their parity chain, and the
/// miter roots `(a ∨ b)`, `(¬a ∨ ¬b)` over the two outputs: unsatisfiable
/// when `equal`, while otherwise the copy leaves out the last input. Then
/// `side` fresh inputs `f_i` and the satisfiable side roots `(f_i ∨ f_{i+1})`,
/// each `f` shared by two roots and mentioned by no other clause.
fn miter(width: usize, equal: bool, side: usize) -> (Vec<Gate>, Vec<Vec<Literal>>, Vec<usize>) {
    let mut gates: Vec<Gate> = (0..width).map(|_| Gate::Input).collect();
    let mut cnf: Vec<Vec<Literal>> = Vec::new();
    let a = parity_chain(&mut gates, &mut cnf, width);
    let b = parity_chain(&mut gates, &mut cnf, if equal { width } else { width - 1 });
    let mut roots = vec![cnf.len(), cnf.len() + 1];
    cnf.push(vec![a, b]);
    cnf.push(vec![a.negated(), b.negated()]);
    let first = gates.len();
    gates.extend((0..side).map(|_| Gate::Input));
    for f in first..first + side.saturating_sub(1) {
        roots.push(cnf.len());
        cnf.push(vec![literal(f, false), literal(f + 1, false)]);
    }
    (gates, cnf, roots)
}

#[test]
fn a_candidates_problem_reads_no_root_and_the_whole_problem_reads_every_root() {
    let (gates, cnf, roots) = miter(8, true, 64);
    let vars = gates.len();
    let mut keep_going = || true;
    let sweep = Sweep::new(
        gates,
        &cnf,
        &roots,
        false,
        SweepLimits::standalone(),
        &mut keep_going,
    )
    .expect("a well-formed sweep");
    let root_ids: Vec<Option<u64>> = roots.iter().map(|&root| Some(root as u64 + 1)).collect();
    // A cone over every variable, the side inputs included, still leaves
    // every root out of a candidate's problem ...
    let everything: Vec<usize> = (0..vars).collect();
    let local = sweep.local(&everything, false, &[]);
    assert!(local.origin.iter().all(|origin| !root_ids.contains(origin)));
    // ... and keeps every other clause.
    for index in (0..cnf.len()).filter(|index| !roots.contains(index)) {
        assert!(local.origin.contains(&Some(index as u64 + 1)), "{index}");
    }
    // The problem over every clause carries each root once.
    let whole = sweep.local(&[], true, &[]);
    for id in &root_ids {
        assert_eq!(
            whole.origin.iter().filter(|origin| *origin == id).count(),
            1
        );
    }
}

#[test]
fn the_closing_problem_numbers_each_root_variable_once() {
    let side = 64;
    let (gates, cnf, roots) = miter(8, true, side);
    let miter_vars = gates.len() - side;
    let mut keep_going = || true;
    let sweep = Sweep::new(
        gates,
        &cnf,
        &roots,
        false,
        SweepLimits::standalone(),
        &mut keep_going,
    )
    .expect("a well-formed sweep");
    // The cone of the miter alone: its outputs are numbered already, the
    // side roots' inputs are not, and all but the two ends are in two roots.
    let cone: Vec<usize> = (0..miter_vars).collect();
    let mut local = sweep.local(&cone, false, &[]);
    let numbered = local.global.clone();
    let clauses = local.clauses.len();
    sweep.push_roots(&mut local);
    // A variable already numbered keeps its number, and each side input is
    // numbered once, after them.
    assert_eq!(local.global[..numbered.len()], numbered[..]);
    let mut seen = DetHashSet::default();
    assert!(local.global.iter().all(|&var| seen.insert(var)));
    assert_eq!(local.global.len(), numbered.len() + side);
    // Each appended clause reads back, through the numbering, as its root.
    assert_eq!(local.clauses.len(), clauses + roots.len());
    for (at, &root) in roots.iter().enumerate() {
        let back: Vec<Literal> = local.clauses[clauses + at]
            .iter()
            .map(|lit| literal(local.global[lit.variable().index()], !lit.is_positive()))
            .collect();
        assert_eq!(back, cnf[root], "root {root}");
        assert_eq!(local.origin[clauses + at], Some(root as u64 + 1));
    }
}

/// End to end only: the swept DAG validates, and its satisfiable twin is
/// never refuted. Its pass does not rest on the cone close's numbering
/// (`push_roots`), since the close's whole-CNF attempt refutes the equal
/// miter as well; the test above pins that numbering.
#[test]
fn a_sweep_with_thousands_of_roots_closes_over_all_of_them() {
    let sweep = |equal: bool| {
        let (gates, cnf, roots) = miter(16, equal, 4_096);
        let mut keep_going = || true;
        let (dag, _) = refute_counted(
            gates,
            &cnf,
            &roots,
            false,
            SweepLimits::standalone(),
            &mut keep_going,
        );
        dag
    };
    sweep(true)
        .expect("the copies are equal gate by gate")
        .validate()
        .expect("the swept DAG is an ordinary RUP refutation of the same CNF");
    // The negative twin: the copy leaves out an input, so the miter has a
    // model, and no root renumbering may refute it.
    assert!(sweep(false).is_none());
}
