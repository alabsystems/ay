// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn actual_global_unit_and_forced_chrono_match_ordinary_without_learning() {
    for fixture in [global_unit as fn() -> (Solver, ClauseRef), forced] {
        let (mut expected, reference) = fixture();
        let before = rows(&expected);
        let forced_before = expected.stats.forced_backtracks;
        expected.analyze_and_backtrack(reference, "dispatch parity", |_, _| {});
        let (mut s, reference) = fixture();
        let owner = generous();
        attach(&mut s, &owner);
        assert_eq!(
            s.dispatch_conflict_counted(reference),
            Ok(CountedDispatchStep::Forced)
        );
        assert_eq!(s.stats.forced_backtracks, forced_before + 1);
        assert_eq!(
            rows(&s),
            before,
            "no derived clause needed on the forced route"
        );
        parity(&s, &expected);
        assert_eq!(
            s.counted_admission_usage().unwrap().unwrap(),
            owner.usage().unwrap()
        );
        assert!(!s.clause_trace().unwrap().proof_work_exhausted());
        clean(&s);
    }
}

#[test]
fn ordinary_global_unit_callback_still_observes_prebacktrack_state() {
    let (mut s, reference) = global_unit();
    let level = s.decision_level;
    let mut calls = Vec::new();
    s.analyze_and_backtrack(reference, "callback order", |state, target| {
        calls.push((state.decision_level, target, state.lit_val(pos(0))))
    });
    assert_eq!(calls, vec![(level, 0, -1)]);
    assert_eq!(s.decision_level, 0);
    assert_eq!(s.lit_val(pos(0)), 1);
    assert_eq!(s.unit_proof_id[0], s.clause_id(reference));
}

#[test]
fn unit_binary_long_and_real_chrono_gap_dispatch_to_actual_learning() {
    for (guards, gap) in [(0, 0), (1, 0), (3, 0), (1, 128)] {
        let (mut expected, reference, _) = fork(guards, gap);
        expected.analyze_and_backtrack(reference, "full dispatch parity", |_, _| {});
        let (mut s, reference, source) = fork(guards, gap);
        let originals = s.cold.original_clause_id_bits.clone();
        attach(&mut s, &generous());
        let CountedDispatchStep::Learned {
            reference: learned_ref,
            uip,
            backtrack,
        } = s.dispatch_conflict_counted(reference).unwrap()
        else {
            panic!("genuine fork must learn");
        };
        assert_eq!(s.arena.len_of(learned_ref.index()), guards as usize + 1);
        assert_eq!(s.cold.original_clause_id_bits, originals);
        assert!(!s.is_original_clause_id(s.clause_id(learned_ref)));
        if gap > 0 {
            assert!(backtrack > 1 && s.trail.len() > 100);
            assert_eq!(s.var_data[uip.variable().index()].level, 1);
        } else {
            let satisfies = |clause: &[Literal], bits: usize| {
                clause
                    .iter()
                    .any(|lit| ((bits >> lit.variable().index()) & 1 == 1) == lit.is_positive())
            };
            let learned = s.arena.literals(learned_ref.index());
            let mut models = 0;
            for bits in 0..1usize << s.num_vars {
                if source.iter().all(|clause| satisfies(clause, bits)) {
                    models += 1;
                    assert!(satisfies(learned, bits));
                }
            }
            assert!(
                models > 0,
                "real satisfiable source, not vacuous entailment"
            );
        }
        parity(&s, &expected);
        clean(&s);
    }
}

#[test]
fn delayed_theory_conflict_backtracks_to_actual_level_before_first_uip() {
    let (mut expected, reference) = delayed();
    let mut callbacks = Vec::new();
    expected.analyze_and_backtrack(reference, "delayed conflict", |s, level| {
        callbacks.push((s.decision_level, level))
    });
    assert_eq!(callbacks.first(), Some(&(4, 3)));
    let (mut s, reference) = delayed();
    attach(&mut s, &generous());
    assert!(matches!(
        s.dispatch_conflict_counted(reference),
        Ok(CountedDispatchStep::Learned { .. })
    ));
    parity(&s, &expected);
    clean(&s);
}

#[test]
fn nonchrono_semantic_bailout_retains_real_backtrack_and_decay() {
    let (mut expected, reference) = delayed();
    expected.chrono_enabled = false;
    expected.analyze_and_backtrack(reference, "ordinary exhausted current level", |_, _| {});
    let (mut s, reference) = delayed();
    s.chrono_enabled = false;
    let before = rows(&s);
    attach(&mut s, &generous());
    assert_eq!(
        s.dispatch_conflict_counted(reference),
        Ok(CountedDispatchStep::BailedOut)
    );
    assert_eq!(s.decision_level, 0);
    assert_eq!(rows(&s), before);
    parity(&s, &expected);
    clean(&s);
}

#[test]
fn two_actual_conflicts_and_intervening_bcp_keep_one_owner() {
    let mut s = configured(7);
    for clause in [
        vec![neg(0), pos(1)],
        vec![neg(0), pos(2)],
        vec![neg(1), neg(2)],
        vec![pos(0), pos(6)],
        vec![neg(3), pos(4)],
        vec![neg(3), pos(5)],
        vec![neg(4), neg(5)],
    ] {
        assert!(s.add_clause(clause));
    }
    s.initialize_watches();
    s.decide(pos(0));
    let first = s.search_propagate().unwrap();
    let owner = generous();
    attach(&mut s, &owner);
    assert!(matches!(
        s.dispatch_conflict_counted(first),
        Ok(CountedDispatchStep::Learned { .. })
    ));
    let first_usage = owner.usage().unwrap();
    assert!(s.search_propagate_counted().unwrap().is_none());
    assert_eq!(s.lit_val(pos(6)), 1);
    s.decide_counted(pos(3)).unwrap();
    let second = s.search_propagate_counted().unwrap().unwrap();
    assert_ne!(first, second);
    assert!(matches!(
        s.dispatch_conflict_counted(second),
        Ok(CountedDispatchStep::Learned { .. })
    ));
    let after = owner.usage().unwrap();
    assert!(after.work_admitted > first_usage.work_admitted);
    assert_eq!(s.counted_admission_usage().unwrap().unwrap(), after);
    assert!(s.search_propagate_counted().unwrap().is_none());
    assert!(!s.clause_trace().unwrap().proof_work_exhausted());
    clean(&s);
}

#[test]
fn root_unit_retry_reserves_actual_pinned_slot_and_retains_proof_id() {
    fn retry() -> (Solver, ClauseRef) {
        let (mut s, reference) = global_unit();
        s.backtrack(0);
        assert!(s.install_theory_unit_at_root(reference));
        assert!(s.search_propagate().is_none());
        assert_eq!(s.qhead, s.trail.len());
        s.cold.lrat_level0_unit_materialize_cursor = s.trail.len();
        s.cold.lrat_level0_unit_materialize_pinned = Vec::new();
        let id = s.clause_id(reference);
        s.pending_theory_unit_proof_ids.push((reference, id));
        s.decide(pos(2));
        assert!(s.search_propagate().is_none());
        (s, reference)
    }
    let (mut expected, reference) = retry();
    expected.analyze_and_backtrack(reference, "root retry", |_, _| {});
    let (mut s, reference) = retry();
    let owner = generous();
    attach(&mut s, &owner);
    assert_eq!(
        s.dispatch_conflict_counted(reference),
        Ok(CountedDispatchStep::Forced)
    );
    assert_eq!(s.cold.lrat_level0_unit_materialize_pinned, vec![0]);
    assert_eq!(s.pending_theory_unit_proof_ids.len(), 0);
    assert!(owner.usage().unwrap().storage_admitted > 0);
    parity(&s, &expected);
}
