// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[path = "safety/nan_identity.rs"]
mod nan_identity;

fn bv_fixture(width: u32, symbol: Symbol, args: Vec<TermId>) -> Vec<(TermData, Sort)> {
    let mut entries = entries();
    entries.push((
        TermData::Var("bv".into(), 1),
        Sort::BitVec(BitVecSort::new(width)),
    ));
    entries.push((TermData::App(symbol, args), Sort::Bool));
    entries
}

#[test]
fn bounded_bv_limits_preserve_unsigned_signed_and_repeat_boundaries() {
    let steps = [lemma(vec![TermId(4)], TheoryLemmaKind::BoolTautology)];
    for (symbol, at_limit, rejected) in [
        (Symbol::named("bvule"), 64, 65),
        (Symbol::named("bvslt"), 63, 64),
        (Symbol::indexed("repeat", vec![1]), 63, 64),
    ] {
        let args = vec![TermId(3), TermId(3)];
        assert!(validate_proof_snapshot(
            &steps,
            &bv_fixture(at_limit, symbol.clone(), args.clone())
        )
        .is_ok());
        assert_malformed(&steps, &bv_fixture(rejected, symbol, args));
    }
}

#[test]
fn signed_and_repeat_operands_are_checked_before_indexing() {
    let steps = [lemma(vec![TermId(4)], TheoryLemmaKind::BoolTautology)];
    for symbol in [Symbol::named("bvslt"), Symbol::indexed("repeat", vec![1])] {
        for args in [vec![], vec![TermId(u32::MAX)]] {
            assert_malformed(&steps, &bv_fixture(8, symbol.clone(), args));
        }
    }
}

#[test]
fn every_child_shape_checks_missing_descendants_without_panicking() {
    let missing = TermId(u32::MAX);
    let cases = [
        TermData::App(Symbol::named("or"), vec![missing]),
        TermData::Let(vec![("x".into(), missing)], TermId(0)),
        TermData::Let(vec![], missing),
        TermData::Not(missing),
        TermData::Ite(TermId(0), missing, TermId(0)),
        TermData::Forall(vec![], missing, vec![]),
        TermData::Exists(vec![], TermId(0), vec![vec![], vec![missing]]),
    ];
    for data in cases {
        let mut entries = entries();
        entries.push((data, Sort::Bool));
        for kind in [
            TheoryLemmaKind::BoolTautology,
            TheoryLemmaKind::FpClassification {
                operation: FpOp::IsNaN,
            },
        ] {
            assert_malformed(&[lemma(vec![TermId(3)], kind)], &entries);
        }
    }
}

#[test]
fn repeated_edges_and_empty_trigger_sets_are_metered_even_for_visited_nodes() {
    let steps = [lemma(vec![TermId(3)], TheoryLemmaKind::BoolTautology)];
    let mut entries = entries();
    entries.push((
        TermData::App(Symbol::named("or"), vec![TermId(0)]),
        Sort::Bool,
    ));
    let (_, base_work, base_bytes) = measurements(&steps, &entries);
    entries[3].0 = TermData::App(Symbol::named("or"), vec![TermId(0); 1024]);
    let (_, repeated_work, repeated_bytes) = measurements(&steps, &entries);
    assert!(repeated_work >= base_work + 1023 * 3);
    assert!(repeated_bytes > base_bytes);
    entries[3].0 = TermData::Forall(vec![], TermId(0), vec![]);
    let (_, no_triggers, _) = measurements(&steps, &entries);
    entries[3].0 = TermData::Forall(vec![], TermId(0), vec![vec![]; 1024]);
    let (_, empty_triggers, _) = measurements(&steps, &entries);
    assert_eq!(empty_triggers, no_triggers + 1024);
}

#[test]
fn queue_and_visited_allocations_are_independently_refusable() {
    let entries = entries();
    let steps = [lemma(vec![TermId(0)], TheoryLemmaKind::BoolTautology)];
    for reject_allocation in [1, 2] {
        let mut allocations = 0;
        let result = validate_proof_snapshot_with_progress(&steps, &entries, &mut |_, bytes| {
            if bytes > 0 {
                allocations += 1;
            }
            allocations != reject_allocation
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(allocations, reject_allocation);
    }
}

#[test]
fn floating_point_assignments_count_distinct_variables_not_duplicate_edges() {
    let mut entries = entries();
    entries.push((TermData::Var("fp".into(), 1), Sort::FloatingPoint(5, 5)));
    entries.push((
        TermData::App(Symbol::named("fp.eq"), vec![TermId(3); 32]),
        Sort::Bool,
    ));
    let steps = [lemma(
        vec![TermId(4)],
        TheoryLemmaKind::FpClassification {
            operation: FpOp::IsNaN,
        },
    )];
    assert!(validate_proof_snapshot(&steps, &entries).is_ok());
    entries.push((
        TermData::Var("fp_other".into(), 2),
        Sort::FloatingPoint(5, 5),
    ));
    entries[4].0 = TermData::App(Symbol::named("fp.eq"), vec![TermId(3), TermId(5)]);
    assert_malformed(&steps, &entries);
    entries[3].1 = Sort::FloatingPoint(16, u32::MAX);
    assert_malformed(&steps, &entries);
}

#[test]
fn floating_point_nan_and_exponent_limits_remain_inclusive() {
    let steps = [lemma(
        vec![TermId(4)],
        TheoryLemmaKind::FpClassification {
            operation: FpOp::IsNaN,
        },
    )];
    for (exponent, significand, accepted) in [(64, 65, true), (65, 65, false), (15, 113, true)] {
        let mut entries = entries();
        entries.push((
            TermData::App(Symbol::indexed("NaN", vec![exponent, significand]), vec![]),
            Sort::FloatingPoint(exponent, significand),
        ));
        entries.push((
            TermData::App(Symbol::named("fp.isNaN"), vec![TermId(3)]),
            Sort::Bool,
        ));
        assert_eq!(validate_proof_snapshot(&steps, &entries).is_ok(), accepted);
    }
}

#[test]
fn checked_size_arithmetic_declines_without_calling_the_callback() {
    assert!(matches!(
        meter::add(usize::MAX, 1),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(matches!(
        meter::mul(usize::MAX, 2),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(meter::add(usize::MAX - 1, 1).unwrap(), usize::MAX);
}
