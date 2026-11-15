// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A finite test oracle for primitive total definitions only. This never
//! licenses a semantic certificate; production proof search remains symbolic.

use super::*;

fn satisfied(row: &[Literal], assignment: usize) -> bool {
    row.iter().any(|literal| {
        let value = (assignment >> literal.variable().index()) & 1 != 0;
        value == literal.is_positive()
    })
}

#[test]
fn boolean_gate_definitions_have_one_extension_for_each_actual_input_assignment() {
    for name in ["and", "or", "xor"] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Bool);
        let b = terms.mk_var("b", Sort::Bool);
        let root = app(&mut terms, name, &[a, b], Sort::Bool);
        let mut live = || ControlFlow::Continue(());
        let mut work = WorkBudget::new(1_000_000, &mut live);
        let cnf =
            compile(&terms, &[root], &limits(), &mut work).expect("canonical total definitions");
        assert!(cnf.num_vars < 16);
        let root = cnf.clauses.last().expect("source unit")[0];
        let definitions = &cnf.clauses[..cnf.clauses.len() - 1];
        for input in 0usize..4 {
            let extensions: Vec<_> = (0..(1usize << cnf.num_vars))
                .filter(|assignment| assignment & 3 == input)
                .filter(|assignment| definitions.iter().all(|row| satisfied(row, *assignment)))
                .collect();
            assert_eq!(extensions.len(), 1, "total and functional gate extension");
            let a = input & 1 != 0;
            let b = input & 2 != 0;
            let expected = match name {
                "and" => a && b,
                "or" => a || b,
                _ => a ^ b,
            };
            assert_eq!(satisfied(&[root], extensions[0]), expected);
        }
    }
}

#[test]
fn negate_and_conditional_preserve_literal_polarity_and_total_source_selection() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Bool);
    let a = terms.mk_var("a", Sort::Bool);
    let n = app(&mut terms, "not", &[a], Sort::Bool);
    let root = app(&mut terms, "ite", &[c, a, n], Sort::Bool);
    let mut live = || ControlFlow::Continue(());
    let mut work = WorkBudget::new(1_000_000, &mut live);
    let cnf = compile(&terms, &[root], &limits(), &mut work).expect("total source ITE");
    assert!(cnf.num_vars < 16);
    let root = cnf.clauses.last().expect("original root")[0];
    let definitions = &cnf.clauses[..cnf.clauses.len() - 1];
    for input in 0usize..4 {
        let extensions: Vec<_> = (0..(1usize << cnf.num_vars))
            .filter(|assignment| assignment & 3 == input)
            .filter(|assignment| definitions.iter().all(|row| satisfied(row, *assignment)))
            .collect();
        assert_eq!(extensions.len(), 1);
        let c = input & 1 != 0;
        let a = input & 2 != 0;
        assert_eq!(satisfied(&[root], extensions[0]), if c { a } else { !a });
    }
}
