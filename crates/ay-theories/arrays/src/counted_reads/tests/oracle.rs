// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Existing ordinary array kernel as an independent ROW oracle. Its work is
//! test-only and is deliberately not included in a counted solver receipt.

use super::*;
use crate::ArraySolver;
use ay_core::{TheoryLit, TheoryResult, TheorySolver};

#[test]
fn ordinary_kernel_rederives_the_actual_symbolic_row1_clause() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let (hit, miss) = row_steps(&closure);
    let guard = miss.literals()[0];
    let conclusion = hit.literals()[1];
    let mut solver = ArraySolver::new(&f.terms);
    solver.assert_literal(guard, true);
    solver.assert_literal(conclusion, false);
    solver.populate_caches();
    let TheoryResult::NeedLemmas(lemmas) = solver.check_row1().expect("real ROW1 conflict") else {
        panic!("ordinary ROW1 must produce its independent lemma");
    };
    assert_eq!(lemmas.len(), 1);
    assert!(lemmas[0].clause.contains(&TheoryLit::new(guard, false)));
    assert!(lemmas[0].clause.contains(&TheoryLit::new(conclusion, true)));
    assert_eq!(lemmas[0].clause.len(), 2);
    drop(solver);
    closure.finish().unwrap();
}

#[test]
fn ordinary_kernel_accepts_row2_agreement_and_rejects_its_negation() {
    let original = ample();
    let mut f = fixture(&original, IndexRelation::Symbolic).unwrap();
    let closure = derive_fixture(&mut f, &original);
    let (_, miss) = row_steps(&closure);
    let guard = miss.literals()[0];
    let conclusion = miss.literals()[1];
    for value in [true, false] {
        let mut solver = ArraySolver::new(&f.terms);
        solver.assert_literal(guard, false);
        solver.assert_literal(conclusion, value);
        if value {
            let result = solver.check();
            assert!(
                matches!(result, TheoryResult::Sat),
                "consistent ROW2: {result:?}"
            );
        } else {
            solver.populate_caches();
            solver.queue_row2_down_axiom(f.stored, f.read);
            let TheoryResult::NeedLemmas(lemmas) =
                solver.check_row2().expect("actual ROW2 conflict")
            else {
                panic!("ordinary ROW2 must independently derive the violated clause");
            };
            assert!(
                lemmas.iter().any(|lemma| lemma.clause.len() == 2
                    && lemma.clause.contains(&TheoryLit::new(guard, true))
                    && lemma.clause.contains(&TheoryLit::new(conclusion, true))),
                "an unrelated lemma is not evidence for this ROW2 instance"
            );
        }
    }
    closure.finish().unwrap();
}
