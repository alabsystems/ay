// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every accepting residue family has satisfiable missing-case controls.

use ay_core::TermStore;

use super::super::super::{authenticate_bv_lia_unsat_query, MAX_WORK};
use super::*;

fn modulo_exclusions(
    terms: &mut TermStore,
    divisor: i64,
    excluded: &[i64],
) -> (TermId, TermId, Vec<TermId>) {
    let x = terms.mk_var("case_x", Sort::Int);
    let divisor = terms.mk_int(divisor.into());
    let remainder = terms.mk_app(Symbol::named("mod"), [x, divisor], Sort::Int);
    let mut roots = Vec::new();
    for &value in excluded {
        let value = terms.mk_int(value.into());
        let equality = terms.mk_eq(remainder, value);
        roots.push(terms.mk_not_raw(equality));
    }
    (x, remainder, roots)
}

fn must_not_authenticate(terms: &TermStore, roots: &[TermId]) {
    let error = authenticate_bv_lia_unsat_query(terms, roots, None)
        .expect_err("the explicitly satisfiable source query must never authenticate");
    assert!(
        error.is_capability_decline()
            || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
        "{error}"
    );
}

#[test]
fn complete_small_remainder_domains_authenticate() {
    for divisor in 1..=16 {
        let mut terms = TermStore::new();
        let excluded: Vec<i64> = (0..divisor).collect();
        let (_, _, roots) = modulo_exclusions(&mut terms, divisor, &excluded);
        authenticate_bv_lia_unsat_query(&terms, &roots, None)
            .unwrap_or_else(|error| panic!("all {divisor} residues are excluded: {error}"));
    }
}

#[test]
fn every_partial_small_domain_has_a_real_witness() {
    for divisor in 2..=5 {
        for mask in 0..(1_u32 << divisor) - 1 {
            let excluded: Vec<i64> = (0..divisor)
                .filter(|value| mask & (1 << value) != 0)
                .collect();
            if excluded.is_empty() {
                continue;
            }
            let witness = (0..divisor).find(|value| mask & (1 << value) == 0).unwrap();
            let mut terms = TermStore::new();
            let (x, _, mut roots) = modulo_exclusions(&mut terms, divisor, &excluded);
            // Pin the actual source dividend to an admitted missing residue.
            let witness = terms.mk_int(witness.into());
            roots.push(terms.mk_eq(x, witness));
            must_not_authenticate(&terms, &roots);
        }
    }
}

#[test]
fn upper_endpoint_and_outside_case_cap_are_not_dropped() {
    for divisor in [2, 3, 16, 17] {
        let mut terms = TermStore::new();
        let excluded: Vec<i64> = (0..divisor - 1).collect();
        let (_, _, roots) = modulo_exclusions(&mut terms, divisor, &excluded);
        // x=divisor-1 is a model, including outside the new 16-value cap.
        must_not_authenticate(&terms, &roots);
    }
}

#[test]
fn a_conflicting_first_case_does_not_leak_alias_bounds_into_the_next() {
    for exclude_last in [false, true] {
        let mut terms = TermStore::new();
        let (_, remainder, excluded) = modulo_exclusions(&mut terms, 2, &[0]);
        let out = terms.mk_var("case_out", Sort::Int);
        let zero = terms.mk_int(0.into());
        let one = terms.mk_int(1.into());
        // Case zero first propagates out=0 through this equality, then
        // conflicts with r!=0. Case one must begin with the original bounds.
        let mut roots = vec![
            terms.mk_eq(out, remainder),
            terms.mk_le(zero, out),
            terms.mk_le(out, one),
        ];
        roots.extend(excluded);
        if exclude_last {
            let out_one = terms.mk_eq(out, one);
            roots.push(terms.mk_not_raw(out_one));
            authenticate_bv_lia_unsat_query(&terms, &roots, None).expect("both cases refuted");
        } else {
            must_not_authenticate(&terms, &roots); // x=1, out=1.
        }
    }
}

fn guarded_ite_problem(
    terms: &mut TermStore,
    then_branch: bool,
    violate_taken: bool,
) -> Vec<TermId> {
    let x = terms.mk_var("ite_x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let guard = terms.mk_ge(x, zero);
    let remainder = terms.mk_app(Symbol::named("mod"), [x, two], Sort::Int);
    let selected = terms.mk_ite_raw(guard, remainder, three);
    let value = if then_branch == violate_taken {
        remainder
    } else {
        three
    };
    let equality = terms.mk_app(Symbol::named("="), [selected, value], Sort::Bool);
    let violated = terms.mk_not_raw(equality);
    let premise = if then_branch {
        guard
    } else {
        terms.mk_not_raw(guard)
    };
    vec![premise, violated]
}

#[test]
fn both_guarded_ite_arms_require_their_real_guard() {
    for then_branch in [false, true] {
        let mut terms = TermStore::new();
        let roots = guarded_ite_problem(&mut terms, then_branch, true);
        authenticate_bv_lia_unsat_query(&terms, &roots, None).expect("the actual arm is equal");
        let mut terms = TermStore::new();
        let roots = guarded_ite_problem(&mut terms, then_branch, false);
        // In the other arm, 3 differs from every possible mod-2 value.
        must_not_authenticate(&terms, &roots);
    }
}

#[test]
fn boolean_ite_comparisons_and_negations_follow_both_real_arms() {
    for then_branch in [false, true] {
        for negate_branch in [false, true] {
            for violate_taken in [false, true] {
                let mut terms = TermStore::new();
                let (x, remainder, _) = modulo_exclusions(&mut terms, 2, &[]);
                let condition = terms.mk_var("boolean_ite_guard", Sort::Bool);
                let zero = terms.mk_int(0.into());
                let one = terms.mk_int(1.into());
                let mut left = terms.mk_eq(remainder, zero);
                let mut right = terms.mk_eq(remainder, one);
                if negate_branch {
                    left = terms.mk_not_raw(left);
                    right = terms.mk_not_raw(right);
                }
                let selected = terms.mk_ite_raw(condition, left, right);
                let premise = if then_branch {
                    condition
                } else {
                    terms.mk_not_raw(condition)
                };
                let value = if then_branch { zero } else { one };
                let pin = terms.mk_eq(remainder, value);
                let pin_dividend = terms.mk_eq(x, value);
                let asserted = if violate_taken != negate_branch {
                    terms.mk_not_raw(selected)
                } else {
                    selected
                };
                let roots = [premise, pin, pin_dividend, asserted];
                let mut checker = QueryChecker::new(&terms, None);
                assert_eq!(
                    checker.has_interval_contradiction(&roots).unwrap(),
                    violate_taken
                );
                if violate_taken {
                    authenticate_bv_lia_unsat_query(&terms, &roots, None)
                        .expect("actual arm refuted");
                } else {
                    must_not_authenticate(&terms, &roots);
                }
            }
        }
    }
}

#[test]
fn smart_expanded_u32_crc_summary_refutes_without_enumerating_u32() {
    let mut terms = TermStore::new();
    let crc = terms.mk_var("crc", Sort::Int);
    let selected = terms.mk_var("selected", Sort::Int);
    let out = terms.mk_var("out", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let maximum = terms.mk_int(4_294_967_295_i64.into());
    let polynomial = terms.mk_int(3_988_292_384_i64.into());
    let nonnegative = terms.mk_le(zero, crc);
    let positive = terms.mk_app(Symbol::named("mod"), [crc, two], Sort::Int);
    let negated = terms.mk_app(Symbol::named("-"), [crc], Sort::Int);
    let negative = terms.mk_app(Symbol::named("mod"), [negated, two], Sort::Int);
    let negative = terms.mk_app(Symbol::named("-"), [negative], Sort::Int);
    let remainder = terms.mk_ite_raw(nonnegative, positive, negative);
    // The actual frontend's smart equality moves the Int ITE into Bool.
    let even = terms.mk_eq(remainder, zero);
    let odd = terms.mk_eq(remainder, one);
    assert!(matches!(terms.get(even), TermData::Ite(..)));
    assert!(matches!(terms.get(odd), TermData::Ite(..)));
    let selected_zero = terms.mk_eq(selected, zero);
    let selected_polynomial = terms.mk_eq(selected, polynomial);
    let even_arm = terms.mk_implies(even, selected_zero);
    let not_even = terms.mk_not(even);
    let odd_arm = terms.mk_implies(not_even, selected_polynomial);
    let linked = terms.mk_eq(out, selected);
    let out_zero = terms.mk_eq(out, zero);
    let out_polynomial = terms.mk_eq(out, polynomial);
    let even_result = terms.mk_and(vec![even, out_zero]);
    let odd_result = terms.mk_and(vec![odd, out_polynomial]);
    let summary = terms.mk_or(vec![even_result, odd_result]);
    let violation = terms.mk_not(summary);
    let mut roots = vec![even_arm, odd_arm, linked, violation];
    for value in [crc, selected, out] {
        roots.push(terms.mk_le(zero, value));
        roots.push(terms.mk_le(value, maximum));
    }
    let mut checker = QueryChecker::new(&terms, None);
    assert!(checker.has_interval_contradiction(&roots).unwrap());
    authenticate_bv_lia_unsat_query(&terms, &roots, None).expect("source CRC theorem");
}

#[test]
fn zero_and_negative_divisors_gain_no_positive_divisor_assumption() {
    for divisor in [0, -3] {
        let mut terms = TermStore::new();
        let (_, _, roots) = modulo_exclusions(&mut terms, divisor, &[0, 1]);
        // mod(x,-3)=2 is possible; mod(x,0) has no fixed domain theorem.
        must_not_authenticate(&terms, &roots);
    }
}

fn residue_case_state(terms: &mut TermStore) -> (TermId, Vec<TermId>) {
    let (_, remainder, roots) = modulo_exclusions(terms, 2, &[0, 1]);
    (remainder, roots)
}

#[test]
fn case_clones_do_not_receive_a_new_work_allowance() {
    let mut terms = TermStore::new();
    let (_, roots) = residue_case_state(&mut terms);
    let mut checker = QueryChecker::new(&terms, None);
    let mut clauses = Vec::new();
    let mut nodes = MAX_FORM_NODES;
    for root in roots {
        assert!(!checker
            .collect_clauses(root, true, 0, &mut nodes, &mut clauses)
            .unwrap()
            .is_truncated());
    }
    let state = checker.initial_interval_state(&clauses).unwrap().unwrap();
    checker.meter.work = MAX_INTERVAL_WORK;
    assert!(!checker
        .small_remainder_cases_refute(&clauses, &state, 0)
        .unwrap());
    checker.meter.work = MAX_WORK;
    assert!(matches!(
        checker.small_remainder_cases_refute(&clauses, &state, MAX_WORK),
        Err(BvLiaUnsatAuthenticationError::ResourceLimit { .. })
    ));
}

#[test]
fn an_expired_deadline_cannot_become_a_case_conflict_verdict() {
    let mut terms = TermStore::new();
    let (_, roots) = residue_case_state(&mut terms);
    let mut checker = QueryChecker::new(&terms, None);
    let mut clauses = Vec::new();
    let mut nodes = MAX_FORM_NODES;
    for root in roots {
        assert!(!checker
            .collect_clauses(root, true, 0, &mut nodes, &mut clauses)
            .unwrap()
            .is_truncated());
    }
    let state = checker.initial_interval_state(&clauses).unwrap().unwrap();
    checker.meter.deadline = Some(ay_core::time::Instant::now());
    let entry = checker.meter.work;
    assert!(matches!(
        checker.small_remainder_cases_refute(&clauses, &state, entry),
        Err(BvLiaUnsatAuthenticationError::ResourceLimit {
            resource: "caller deadline"
        })
    ));
}

#[test]
fn overflowed_case_copy_accounting_declines_before_allocation() {
    let terms = TermStore::new();
    let mut checker = QueryChecker::new(&terms, None);
    let state = IntervalState {
        bound_limbs: u64::MAX,
        ..IntervalState::default()
    };
    assert!(checker
        .copy_interval_case_state(&state, 0)
        .unwrap()
        .is_none());
}

#[test]
fn shared_large_guard_is_kept_exact_without_flattening_payload_copies() {
    let mut terms = TermStore::new();
    let variables: Vec<_> = (0..128)
        .map(|i| terms.mk_var(format!("wide_guard_{i}"), Sort::Int))
        .collect();
    let sum = terms.mk_app(Symbol::named("+"), variables, Sort::Int);
    let large = terms.mk_int(BigInt::one() << 65_000_usize);
    let scaled = terms.mk_app(Symbol::named("*"), [large, sum], Sort::Int);
    let zero = terms.mk_int(0.into());
    let equality = terms.mk_app(Symbol::named("="), [scaled, zero], Sort::Bool);
    let condition = terms.mk_app(Symbol::named("and"), vec![equality; 129], Sort::Bool);
    let one = terms.mk_int(1.into());
    let selected = terms.mk_ite_raw(condition, one, zero);
    // Smart mk_eq expands value ITEs. Retain the actual adversarial source
    // nodes so this control exercises the projection builder's allocation.
    let root = terms.mk_app(Symbol::named("="), [selected, zero], Sort::Bool);
    let mut checker = QueryChecker::new(&terms, None);
    let mut clauses = Vec::new();
    let mut nodes = MAX_FORM_NODES;
    let appended = checker
        .append_source_ite_clauses(&[root], &mut clauses, &mut nodes, 0)
        .unwrap();
    assert_eq!(appended, Some(2));
    for (clause, polarity) in clauses.iter().zip([false, true]) {
        assert!(
            matches!(clause.first(), Some(ClauseLiteral::Opaque { term, polarity: p })
            if *term == condition && *p == polarity)
        );
        assert_eq!(
            clause.len(),
            2,
            "the complex guard must remain one exact literal"
        );
    }
    assert!(checker.meter.work < MAX_INTERVAL_WORK);
    must_not_authenticate(&terms, &[root]); // choose one nonzero x: guard=false, selected=0.
}
