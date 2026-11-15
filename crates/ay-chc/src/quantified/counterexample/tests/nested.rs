// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_core::kani_compat::DetHashMap;

#[test]
fn nested_counterexample_controls_pin_the_original_off_diagonal_premise() {
    for bad in [false, true] {
        let source = fixtures::nested(bad, 8);
        let fact = &source.source_problem().clauses()[0];
        let ClauseHead::Predicate(_, arguments) = &fact.head else {
            panic!("source fact")
        };
        let constraint = fact.body.constraint.as_ref().unwrap();
        let world =
            crate::expr::evaluate_expr(fixtures::operand(constraint, 1), &DetHashMap::default())
                .expect("closed constructor/constant-array value");
        let mut model = DetHashMap::default();
        model.insert(fixtures::variable(&arguments[0]).to_owned(), world);
        assert_eq!(
            crate::expr::evaluate_expr(constraint, &model),
            Some(SmtValue::Bool(true))
        );
        let premise = &source.premises()[0][0];
        let binders = premise.binders().collect::<Vec<_>>();
        assert_eq!(binders.len(), 2);
        let mut false_cells = Vec::new();
        for row in 0..35u128 {
            model.insert(binders[0].name.clone(), SmtValue::BitVec(row, 64));
            for col in 0..66u128 {
                model.insert(binders[1].name.clone(), SmtValue::BitVec(col, 64));
                let actual = crate::expr::evaluate_expr(premise.matrix(), &model);
                assert!(matches!(actual, Some(SmtValue::Bool(_))));
                if actual == Some(SmtValue::Bool(false)) {
                    false_cells.push((row, col));
                }
            }
        }
        assert_eq!(false_cells, if bad { vec![(33, 64)] } else { vec![] });
        // All other BV64 pairs satisfy the guard vacuously: rows >=34 are
        // excluded and only row33 has a nonzero length, namely 65.
        assert_eq!(source.source_problem().datatype_defs().len(), 2);
    }
}

#[test]
#[timeout(180000)]
fn concrete_nested_vec_counterexample_replays_the_complete_grouped_source() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    // Hang backstop only, under ntest's 180 s. The source has one original
    // derivation, the fact then the query ([0, 1]): the search's cursor
    // counts reach it and then exhaust, and its probe, like the rechecks
    // below, ends on the native solver's own budgets
    // (`require_searched_unsafe`), not on `solve`'s quarter of a 45 s wall.
    let backstop = Instant::now() + Duration::from_secs(170);
    let _deadline = ScopedSmtDeadline::install_until(backstop);
    let token = CancellationToken::new();
    let source = fixtures::nested(false, 8);
    let evidence = require_searched_unsafe(&source, backstop, &token);
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    assert_eq!(evidence.clause_indices(), &[0, 1]);
    let replay = evidence.replay_obligation();
    assert!(replay.contains("(declare-datatype"));
    assert!(replay.contains("Inner"));
    assert!(replay.contains("Outer"));
    assert!(replay.contains("(forall (("));
    assert!(replay.contains("(select (fld_data (select (fld_data "));
    assert!(replay.contains("(_ bv33 64)"));
    assert!(replay.contains("(_ bv64 64)"));
    assert!(replay.ends_with("(check-sat)\n"));
    let rechecked = evidence.recheck(&source, remaining(backstop), &token);
    if !rechecked {
        require_before(backstop, "the complete-source recheck");
    }
    assert!(rechecked, "the complete grouped source must recheck SAT");
    assert!(!evidence.recheck(&fixtures::nested(false, 7), remaining(backstop), &token));
    assert!(!evidence.recheck(&fixtures::nested(true, 8), remaining(backstop), &token));
    // A recheck past the backstop declines without looking at the source, so
    // the two refusals above count only if they arrived before it.
    require_before(backstop, "the changed-source rechecks");
}

#[test]
#[timeout(180000)]
fn false_grouped_premise_or_false_query_never_mints_a_counterexample() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    for source in [fixtures::nested(false, 7), fixtures::nested(true, 8)] {
        assert!(!matches!(
            source.solve(
                remaining(deadline).min(Duration::from_secs(30)),
                Some(TERM_BUDGET),
                &CancellationToken::new(),
            ),
            QuantifiedChcResult::Unsafe(_)
        ));
    }
}
