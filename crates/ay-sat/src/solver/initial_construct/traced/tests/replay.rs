// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

fn dimacs(lit: Literal) -> i64 {
    let v = lit.variable().index() as i64 + 1;
    if lit.is_positive() {
        v
    } else {
        -v
    }
}
fn proof(s: &Solver, omit: Option<usize>) -> String {
    let mut text = String::new();
    for (id, clause, original, hints) in rows(s) {
        if original {
            continue;
        }
        text.push_str(&format!("{id} "));
        for lit in &clause {
            text.push_str(&format!("{} ", dimacs(*lit)));
        }
        text.push_str("0 ");
        for (i, hint) in hints.iter().enumerate() {
            if !(clause.is_empty() && omit == Some(i)) {
                text.push_str(&format!("{hint} "));
            }
        }
        text.push_str("0\n");
    }
    text
}
fn strict(clauses: &[&[Literal]], proof: &str) -> bool {
    let mut text = format!("p cnf 3 {}\n", clauses.len());
    for clause in clauses {
        for lit in *clause {
            text.push_str(&format!("{} ", dimacs(*lit)));
        }
        text.push_str("0\n");
    }
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(text.as_bytes()).unwrap();
    let steps = ay_lrat_check::lrat_parser::parse_text_lrat(proof).unwrap();
    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    for (id, clause) in cnf.clauses {
        assert!(checker.add_original(id, &clause));
    }
    checker.verify_proof(&steps)
}

#[test]
fn actual_bootstrap_root_conflict_composes_with_counted_terminal_and_strict_replay() {
    let clauses = [
        &[p(0), n(0)][..],
        &[p(0)],
        &[n(0), p(1)],
        &[n(1), p(2)],
        &[n(2)],
    ];
    let original = ample();
    let mut loaded = build(3, &clauses, &[], original.clone()).unwrap();
    let InitialConflict::Clause(conflict) = loaded.initial_conflict else {
        panic!("root conflict expected")
    };
    assert!(loaded.solver.veripb_hints_resolved_inactive());
    let before = original.usage().unwrap();
    let result = loaded
        .solver
        .declare_counted_root_unsat(Some(conflict), &original, None)
        .unwrap();
    assert!(matches!(result, SatResult::Unsat(_)));
    assert!(original.usage().unwrap().work_admitted > before.work_admitted);
    assert!(loaded.solver.cold.retain_unsat_certificate);
    // This is source registration/root proof composition, not proof that the
    // separate startup/reset streaming-support initialization is admitted.
    assert!(loaded.solver.cold.streaming_core.is_none());
    let (mut expected, conflict) = ordinary(3, &clauses);
    expected.record_level0_conflict_chain(conflict.unwrap());
    assert!(matches!(expected.declare_unsat(), SatResult::Unsat(_)));
    assert_eq!(proof(&loaded.solver, None), proof(&expected, None));
    assert_eq!(rows(&loaded.solver), rows(&expected));
    let actual = proof(&loaded.solver, None);
    assert!(!actual.is_empty() && strict(&clauses, &actual));
    let emitted = rows(&loaded.solver);
    let last = emitted.last().unwrap();
    assert!(last.1.is_empty() && last.3.len() >= 3);
    for omitted in 0..last.3.len() {
        assert!(
            !strict(&clauses, &proof(&loaded.solver, Some(omitted))),
            "hint {omitted}"
        );
    }
    // Actual source mutation with the same clause IDs is not authenticated by
    // the trace: replacing the positive root unit makes this formula SAT.
    let changed = [clauses[0], &[n(0)][..], clauses[2], clauses[3], clauses[4]];
    assert!(!strict(&changed, &actual));
}
