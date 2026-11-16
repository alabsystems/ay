// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_core::original_query::FiniteAdmissionGrant;
use ay_sat::{Literal, SatResult, Solver};
use num_bigint::BigInt;

mod array_reads;
mod cleanup;
mod resources;
mod semantics;
mod signatures;

fn owner(work: u64, bytes: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn ample() -> CountedAdmission {
    owner(100_000_000, 1 << 30)
}

fn operation(terms: &mut TermStore, name: &str, a: TermId, b: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named(name), [a, b], Sort::bitvec(width))
}

// SAT here is an independent TEST oracle for encoding semantics. Its work is
// deliberately outside the encoder's receipt; this is not a counted solver.
fn pinned_solver(vars: u32, clauses: &[CnfClause], pins: &[(CnfLit, bool)]) -> Solver {
    let mut solver = Solver::new(vars as usize);
    for clause in clauses {
        solver.add_clause(
            clause
                .literals()
                .iter()
                .copied()
                .map(Literal::from_dimacs)
                .collect(),
        );
    }
    for &(literal, value) in pins {
        solver.add_clause(vec![Literal::from_dimacs(if value {
            literal
        } else {
            -literal
        })]);
    }
    solver
}

fn solve_model(vars: u32, clauses: &[CnfClause], pins: &[(CnfLit, bool)]) -> Vec<bool> {
    let SatResult::Sat(model) = pinned_solver(vars, clauses, pins).solve().into_inner() else {
        panic!("complete BV circuit must have a value");
    };
    model
}

fn literal_value(model: &[bool], literal: CnfLit) -> bool {
    model[literal.unsigned_abs() as usize - 1] == (literal > 0)
}

// Keep the entire original CNF and exact input pins. The added single clause
// demands at least one WRONG output bit; UNSAT therefore proves uniqueness,
// while the preceding SAT check rules out a vacuous inconsistent encoding.
fn reject_wrong_output(
    vars: u32,
    clauses: &[CnfClause],
    pins: &[(CnfLit, bool)],
    word: &[CnfLit],
    expected: &[bool],
) {
    assert_eq!(word.len(), expected.len());
    assert_ne!(word, &[] as &[CnfLit]);
    let mut solver = pinned_solver(vars, clauses, pins);
    solver.add_clause(
        word.iter()
            .zip(expected)
            .map(|(&literal, &value)| Literal::from_dimacs(if value { -literal } else { literal }))
            .collect(),
    );
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Unsat(_)),
        "original CNF admits a wrong output, or the uniqueness oracle stopped"
    );
}

fn assert_unique_bits(
    vars: u32,
    clauses: &[CnfClause],
    pins: &[(CnfLit, bool)],
    word: &[CnfLit],
    expected: &[bool],
) {
    let model = solve_model(vars, clauses, pins);
    let actual: Vec<bool> = word
        .iter()
        .map(|&literal| literal_value(&model, literal))
        .collect();
    assert_eq!(actual, expected);
    reject_wrong_output(vars, clauses, pins, word, expected);
}

fn solve_word(vars: u32, clauses: &[CnfClause], pins: &[(CnfLit, bool)], word: &[CnfLit]) -> u64 {
    assert!(word.len() <= 64);
    let model = solve_model(vars, clauses, pins);
    let bits: Vec<bool> = word
        .iter()
        .map(|&literal| literal_value(&model, literal))
        .collect();
    reject_wrong_output(vars, clauses, pins, word, &bits);
    bits.iter()
        .enumerate()
        .fold(0, |value, (bit, &set)| value | (u64::from(set) << bit))
}

fn pins(a: &[CnfLit], b: &[CnfLit], av: u64, bv: u64) -> Vec<(CnfLit, bool)> {
    a.iter()
        .enumerate()
        .map(|(i, &lit)| (lit, av & (1 << i) != 0))
        .chain(
            b.iter()
                .enumerate()
                .map(|(i, &lit)| (lit, bv & (1 << i) != 0)),
        )
        .collect()
}
