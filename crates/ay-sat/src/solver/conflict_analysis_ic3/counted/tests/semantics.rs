// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn actual_bcp_chains_match_the_ordinary_first_uip_and_complete_finalizer() {
    for kind in [Reasons::Binary, Reasons::Long] {
        for length in [1, 2, 4, 16] {
            let (mut expected, conflict, _) = fixture(length, kind);
            let raw = ordinary(&mut expected, conflict).unwrap();
            assert_eq!(
                raw,
                Resolved {
                    uip: neg(1),
                    lower: vec![neg(0)],
                    lbd: 1
                }
            );
            let (mut full, conflict, _) = fixture(length, kind);
            let finalized = full.analyze_conflict_ic3(conflict).unwrap();
            assert_eq!(finalized.learned_clause, vec![raw.uip, raw.lower[0]]);
            assert_eq!((finalized.lbd, finalized.backtrack_level), (raw.lbd, 1));
            let (mut actual, conflict, _) = fixture(length, kind);
            let before = state(&actual);
            attach(&mut actual, &test_owner(10_000_000, 10_000_000));
            assert_eq!(run(&mut actual, conflict), Ok(Some(raw)));
            assert_eq!(state(&actual), before);
            clean(&actual);
        }
    }
}

fn satisfies(clause: &[Literal], bits: usize) -> bool {
    clause
        .iter()
        .any(|lit| ((bits >> lit.variable().index()) & 1 == 1) == lit.is_positive())
}

#[test]
fn learned_raw_clause_is_entailed_by_all_original_models_not_an_unsat_claim() {
    for length in 1..=3 {
        for kind in [Reasons::Binary, Reasons::Long] {
            let (mut s, conflict, source) = fixture(length, kind);
            attach(&mut s, &test_owner(10_000_000, 10_000_000));
            let result = run(&mut s, conflict).unwrap().unwrap();
            let mut learned = vec![result.uip];
            learned.extend(result.lower);
            let mut models = 0;
            for bits in 0..(1usize << s.num_vars) {
                if source.iter().all(|clause| satisfies(clause, bits)) {
                    models += 1;
                    assert!(
                        satisfies(&learned, bits),
                        "non-entailed clause at assignment {bits}"
                    );
                }
            }
            assert!(
                models > 0,
                "the original formula is SAT, not a vacuous entailment test"
            );
        }
    }
}

#[test]
fn real_binary_literal_and_long_clause_reasons_are_both_traversed() {
    for kind in [Reasons::Binary, Reasons::Long] {
        let (mut s, conflict, _) = fixture(4, kind);
        let matching = s
            .trail
            .iter()
            .filter(|lit| {
                matches!(
                    (kind, s.var_reason_kind(lit.variable().index())),
                    (Reasons::Binary, ReasonKind::BinaryLiteral(_))
                        | (Reasons::Long, ReasonKind::Clause(_))
                )
            })
            .count();
        assert!(
            matching > 1,
            "fixture must reach the intended real reason representation"
        );
        attach(&mut s, &test_owner(10_000_000, 10_000_000));
        assert!(run(&mut s, conflict).unwrap().is_some());
    }
}

#[test]
fn repeated_scopes_reuse_capacity_but_never_renew_the_original_allowance() {
    let (mut s, conflict, _) = fixture(8, Reasons::Long);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    let first = run(&mut s, conflict).unwrap();
    let cold = owner.usage().unwrap();
    assert!(cold.storage_admitted > 0);
    assert_eq!(run(&mut s, conflict).unwrap(), first);
    let warm = owner.usage().unwrap();
    assert!(warm.work_admitted > cold.work_admitted);
    assert_eq!(warm.storage_admitted, cold.storage_admitted);
    assert!(warm.work_remaining < cold.work_remaining);
    clean(&s);
}

#[test]
fn unrelated_trail_tail_is_scanned_without_changing_the_first_uip() {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    // A legal same-level assignment not involved in this conflict extends the
    // real trail. Allocate it before taking the original-owner scope.
    let extra = s.new_var();
    s.enqueue(Literal::positive(extra), None);
    let before = state(&s);
    attach(&mut s, &test_owner(10_000_000, 10_000_000));
    assert_eq!(run(&mut s, conflict).unwrap().unwrap().uip, neg(1));
    assert_eq!(state(&s), before);
}

#[test]
fn ordinary_non_uip_decision_fallback_is_unchanged_counted_declines_it() {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    let last = s.trail.last().unwrap().variable().index();
    s.var_data[last].reason = NO_REASON;
    let (mut expected, same, _) = fixture(2, Reasons::Long);
    expected.var_data[last].reason = NO_REASON;
    let result = ordinary(&mut expected, same).unwrap();
    assert!(result
        .lower
        .iter()
        .any(|lit| lit.variable().index() == last));
    let before = state(&s);
    let owner = test_owner(10_000_000, 10_000_000);
    attach(&mut s, &owner);
    assert_eq!(run(&mut s, conflict), Err(SatUnknownReason::ResourceBudget));
    assert!(owner.usage().unwrap().refusal.is_some());
    assert_eq!(state(&s), before);
    clean(&s);
}
