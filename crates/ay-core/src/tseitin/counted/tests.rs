// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;
use crate::original_query::FiniteAdmissionGrant;
use std::sync::Arc;
mod api;
mod bridge;
mod resources;
mod semantics;
mod signatures;

fn owner(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}
fn ample() -> CountedAdmission {
    owner(200_000_000, 512 * 1024 * 1024)
}

fn formula(op: CountedBuiltin) -> (TermStore, TermId, [TermId; 3]) {
    let source = ample();
    let mut terms = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut terms, &source).unwrap();
    let a = builder.variable("a", &Sort::Bool).unwrap();
    let b = builder.variable("b", &Sort::Bool).unwrap();
    let c = builder.variable("c", &Sort::Bool).unwrap();
    let args: &[TermId] = match op {
        CountedBuiltin::Not => &[a],
        CountedBuiltin::Ite => &[a, b, c],
        _ => &[a, b],
    };
    let root = builder.apply(op, args).unwrap();
    builder.finish().unwrap();
    (terms, root, [a, b, c])
}

fn eval(terms: &TermStore, id: TermId, variables: &[TermId], assignment: usize) -> bool {
    match terms.get(id) {
        TermData::Const(Constant::Bool(value)) => *value,
        TermData::Var(_, _) => {
            assignment & (1 << variables.iter().position(|v| *v == id).unwrap()) != 0
        }
        TermData::Not(arg) => !eval(terms, *arg, variables, assignment),
        TermData::Ite(c, t, e) => eval(
            terms,
            if eval(terms, *c, variables, assignment) {
                *t
            } else {
                *e
            },
            variables,
            assignment,
        ),
        TermData::App(Symbol::Named(name), args) => {
            if name == "and" {
                return args
                    .iter()
                    .all(|arg| eval(terms, *arg, variables, assignment));
            }
            if name == "or" {
                return args
                    .iter()
                    .any(|arg| eval(terms, *arg, variables, assignment));
            }
            let a = eval(terms, args[0], variables, assignment);
            let b = eval(terms, args[1], variables, assignment);
            match name.as_ref() {
                "=>" => !a || b,
                "xor" | "distinct" => a != b,
                "=" => a == b,
                _ => panic!("unexpected operator"),
            }
        }
        _ => panic!("unexpected test term"),
    }
}

fn lit_value(lit: i32, assignment: usize) -> bool {
    let value = assignment & (1 << (lit.unsigned_abs() - 1)) != 0;
    value == (lit > 0)
}

fn exhaustive(cnf: &CountedCnf<'_>, variables: &[TermId]) {
    assert_eq!(cnf.data.theory_atoms.as_slice(), &[]);
    for inputs in 0..(1 << variables.len()) {
        let expected = cnf
            .data
            .roots
            .iter()
            .all(|root| eval(cnf.terms, *root, variables, inputs));
        let exists = (0..(1_usize << cnf.data.num_vars)).any(|bits| {
            variables.iter().enumerate().all(|(index, var)| {
                cnf.data.term_literals[var.index()]
                    .is_none_or(|lit| lit_value(lit, bits) == (inputs & (1 << index) != 0))
            }) && cnf
                .data
                .rows
                .iter()
                .all(|row| row.literals.iter().any(|lit| lit_value(*lit, bits)))
        });
        assert_eq!(exists, expected, "input assignment {inputs}");
        for step in &cnf.data.steps {
            assert!(step
                .clause
                .iter()
                .any(|lit| eval(cnf.terms, lit.term, variables, inputs) == lit.positive));
        }
    }
}
