// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_sat::{Literal, SatResult, Solver};

const W: u32 = 3;

fn offset(terms: &mut TermStore, constant: u64, word: TermId) -> TermId {
    let constant = terms.mk_bitvec(BigInt::from(constant), W);
    terms.mk_app(
        Symbol::named("bvadd"),
        vec![constant, word],
        Sort::bitvec(W),
    )
}

fn satisfiable(solver: &BvSolver<'_>, units: &[CnfLit]) -> bool {
    let mut sat = Solver::new((solver.next_var - 1) as usize);
    for clause in solver.clauses() {
        sat.add_clause(
            clause
                .literals()
                .iter()
                .map(|&l| Literal::from_dimacs(l))
                .collect(),
        );
    }
    for &unit in units {
        sat.add_clause(vec![Literal::from_dimacs(unit)]);
    }
    matches!(sat.solve().into_inner(), SatResult::Sat(_))
}

/// The literal is the equality's truth value under every assignment of the
/// two words, for every pair of offsets at width three.
#[test]
fn an_offset_equality_blasts_to_its_own_truth_value() {
    for c1 in 0..8_u64 {
        for c2 in [0, 1, 5, 7] {
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", Sort::bitvec(W));
            let y = terms.mk_var("y", Sort::bitvec(W));
            let lhs = offset(&mut terms, c1, x);
            let rhs = offset(&mut terms, c2, y);
            let reading = terms.bv_offset_equality(lhs, rhs).expect("offset equality");
            let equality = terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool);
            // A second equality over the pair makes the difference shared.
            let other = offset(&mut terms, c1 + 3, x);
            let sharing = terms.mk_app(Symbol::named("="), vec![other, rhs], Sort::Bool);
            let mut solver = BvSolver::new(&terms);
            solver.count_offset_equalities(&[equality, sharing]);
            assert!(solver.offset_shares.uses(&reading));
            let literal = solver.bitblast_predicate(equality).expect("BV predicate");
            let (xs, ys) = (solver.get_bits(x), solver.get_bits(y));
            for vx in 0..8_u64 {
                for vy in 0..8_u64 {
                    let pin = |bits: &BvBits, value: u64| -> Vec<CnfLit> {
                        bits.iter()
                            .enumerate()
                            .map(|(i, &b)| if value >> i & 1 == 1 { b } else { -b })
                            .collect()
                    };
                    let mut units = pin(&xs, vx);
                    units.extend(pin(&ys, vy));
                    let holds = (vx + c1) % 8 == (vy + c2) % 8;
                    units.push(literal);
                    assert_eq!(satisfiable(&solver, &units), holds, "c1={c1} c2={c2}");
                    *units.last_mut().expect("pushed") = -literal;
                    assert_eq!(satisfiable(&solver, &units), !holds, "c1={c1} c2={c2}");
                }
            }
        }
    }
}

/// A second equality over the same pair of words adds a comparator, not a
/// second subtractor.
#[test]
fn equalities_over_one_pair_share_one_subtractor() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let mut atoms = Vec::new();
    for c in [24_u64, 25, 26] {
        let constant = terms.mk_bitvec(BigInt::from(c), 64);
        let lhs = terms.mk_app(Symbol::named("bvadd"), vec![constant, x], Sort::bitvec(64));
        atoms.push(terms.mk_app(Symbol::named("="), vec![lhs, y], Sort::Bool));
    }
    let mut solver = BvSolver::new(&terms);
    solver.count_offset_equalities(&atoms);
    let mut added = Vec::new();
    for &atom in &atoms {
        let before = solver.clauses().len();
        solver.bitblast_predicate(atom).expect("BV predicate");
        added.push(solver.clauses().len() - before);
    }
    assert!(
        added[1] * 2 < added[0] && added[2] * 2 < added[0],
        "later atoms reuse the subtractor: {added:?}"
    );
}

/// The blasted clauses of `atoms`, in order, each after `count`.
fn blasted(terms: &TermStore, atoms: &[TermId], count: &[TermId]) -> Vec<usize> {
    let mut solver = BvSolver::new(terms);
    solver.count_offset_equalities(count);
    atoms
        .iter()
        .map(|&atom| {
            let before = solver.clauses().len();
            solver.bitblast_predicate(atom).expect("BV predicate");
            solver.clauses().len() - before
        })
        .collect()
}

/// An equality whose pair no other equality reads keeps its authored blast:
/// `x + 24 = y` is one constant adder and a comparator, not a subtractor of
/// two free words (DR-33). Met outside a counted scope, the first equality
/// over a pair stays authored.
#[test]
fn a_difference_nothing_shares_is_not_built() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(64));
    let y = terms.mk_var("y", Sort::bitvec(64));
    let mut atoms = Vec::new();
    for c in [24_u64, 25] {
        let constant = terms.mk_bitvec(BigInt::from(c), 64);
        let lhs = terms.mk_app(Symbol::named("bvadd"), vec![constant, x], Sort::bitvec(64));
        atoms.push(terms.mk_app(Symbol::named("="), vec![lhs, y], Sort::Bool));
    }
    let alone = blasted(&terms, &atoms[..1], &atoms[..1]);
    let authored = {
        let mut solver = BvSolver::new(&terms);
        let TermData::App(_, args) = terms.get(atoms[0]).clone() else {
            panic!("an application");
        };
        let (a, b) = (solver.get_bits(args[0]), solver.get_bits(args[1]));
        solver.bitblast_eq(&a, &b);
        solver.clauses().len()
    };
    assert_eq!(alone, vec![authored], "blasted as authored");
    let counted = blasted(&terms, &atoms, &atoms);
    let uncounted = blasted(&terms, &atoms, &[]);
    assert_eq!(uncounted[0], authored, "the first one met stays authored");
    assert!(
        counted[1] * 2 < counted[0],
        "counted together, the second reuses the first's subtractor: {counted:?}"
    );
}
