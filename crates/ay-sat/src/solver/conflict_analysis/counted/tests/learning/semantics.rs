// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn unit_binary_and_long_learning_match_actual_ordinary_tail_without_default_changes() {
    for guards in 0..=3 {
        let (mut expected, reference, _) = fork(guards, 0);
        expected.analyze_and_backtrack(reference, "ordinary parity", |_, _| {});
        let (mut s, reference, source) = fork(guards, 0);
        let original_ids = s.cold.original_clause_id_bits.clone();
        let owner = test_owner(100_000_000, 100_000_000);
        attach(&mut s, &owner);
        let step = learn(&mut s, reference).unwrap();
        assert_eq!(s.arena.len_of(step.reference.index()), guards as usize + 1);
        assert_eq!(step.uip, neg(guards));
        assert!(s.arena.is_learned(step.reference.index()));
        assert_eq!(s.cold.original_clause_id_bits, original_ids);
        assert!(!s.is_original_clause_id(s.clause_id(step.reference)));
        let rows = trace_rows(&s);
        let row = rows.last().unwrap();
        assert_eq!(row.0, s.clause_id(step.reference));
        assert!(!row.2 && row.3.len() >= 3 && row.3.iter().all(|id| *id != 0));
        parity(&s, &expected);
        let learned = s.arena.literals(step.reference.index());
        let satisfies = |clause: &[Literal], bits: usize| {
            clause
                .iter()
                .any(|lit| ((bits >> lit.variable().index()) & 1 == 1) == lit.is_positive())
        };
        let mut models = 0;
        for bits in 0..1usize << s.num_vars {
            if source.iter().all(|clause| satisfies(clause, bits)) {
                models += 1;
                assert!(satisfies(learned, bits));
            }
        }
        assert!(models > 0, "non-vacuous original consequence");
        clean(&s);
    }
}

#[test]
fn real_large_chrono_gap_preserves_ghost_levels_and_actual_trail_reuse() {
    let (mut expected, reference, _) = fork(1, 128);
    expected.analyze_and_backtrack(reference, "chrono gap", |_, _| {});
    let (mut s, reference, _) = fork(1, 128);
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    let step = learn(&mut s, reference).unwrap();
    assert!(
        step.backtrack > 1,
        "must use real chronological rather than jump level"
    );
    assert_eq!(s.var_data[step.uip.variable().index()].level, 1);
    assert!(
        s.trail.len() > 100,
        "retained irrelevant decisions are real ghosts"
    );
    parity(&s, &expected);
    clean(&s);
}

#[test]
fn learning_then_second_bcp_and_second_conflict_share_the_original_owner() {
    let source = vec![
        vec![neg(0), pos(1)],
        vec![neg(0), pos(2)],
        vec![neg(1), neg(2)],
        vec![pos(0), pos(6)],
        vec![neg(3), pos(4)],
        vec![neg(3), pos(5)],
        vec![neg(4), neg(5)],
    ];
    let mut s = Solver::new(7);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    s.set_preprocess_enabled(false);
    for clause in source {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    s.decide(pos(0));
    let first = s.search_propagate().unwrap();
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    let learned = learn(&mut s, first).unwrap();
    assert_eq!(learned.uip, neg(0));
    let at_first = owner.usage().unwrap();
    assert!(s.search_propagate_counted().unwrap().is_none());
    assert_eq!(s.lit_val(pos(6)), 1, "new learned unit must drive real BCP");
    s.decide_counted(pos(3)).unwrap();
    let second = s.search_propagate_counted().unwrap().unwrap();
    assert_ne!(first, second);
    let learned = learn(&mut s, second).unwrap();
    assert_eq!(learned.uip, neg(3));
    let used = owner.usage().unwrap();
    assert!(used.work_admitted > at_first.work_admitted);
    assert_eq!(s.counted_admission_usage().unwrap().unwrap(), used);
    assert!(s.search_propagate_counted().unwrap().is_none());
    assert!(!s.clause_trace().unwrap().proof_work_exhausted());
    clean(&s);
}
