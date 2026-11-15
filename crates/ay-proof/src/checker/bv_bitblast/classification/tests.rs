// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use ay_core::AletheRule;
use num_bigint::BigInt;

use super::*;

mod fixtures;
mod oracle;
mod progress;

use fixtures::{eq, evaluate, tagged};

fn compare(terms: &TermStore, clause: &[TermId]) -> bool {
    let expected = oracle::classify(terms, clause);
    assert_eq!(
        clause_mentions_bv(terms, clause),
        oracle::mentions_bv(terms, clause)
    );
    assert_eq!(
        collect_bounded_vars(terms, clause),
        oracle::bounded_vars(terms, clause)
    );
    assert_eq!(requires_proof_producer(terms, clause), expected);
    assert_eq!(
        super::super::bv_bitblast_requires_proof_producer(terms, clause),
        expected
    );
    assert_eq!(
        bv_bitblast_requires_proof_producer_with_progress(terms, clause, &mut |work, bytes| {
            assert_eq!((work, bytes), (0, 0));
            true
        }),
        Ok(expected),
    );
    expected
}

#[test]
fn distinct_variable_and_constant_width_boundaries_match_the_old_classifier() {
    let mut terms = TermStore::new();
    for width in [1, 4, 5, 8, 64, 65] {
        let variable = terms.mk_var(format!("width-{width}"), Sort::bitvec(width));
        let identity = eq(&mut terms, variable, variable);
        assert_eq!(compare(&terms, &[identity]), width > 4);
        let zero = terms.mk_bitvec(BigInt::from(0u8), width);
        let one = terms.mk_bitvec(BigInt::from(1u8), width);
        let equality = eq(&mut terms, zero, one);
        assert_eq!(compare(&terms, &[equality]), width > 64);
    }
}

#[test]
fn assignment_bit_ceiling_and_shared_variables_are_unchanged() {
    let mut terms = TermStore::new();
    let boolean = terms.mk_var("assignment-bool", Sort::Bool);
    let four = terms.mk_var("assignment-four", Sort::bitvec(4));
    let three = terms.mk_var("assignment-three", Sort::bitvec(3));
    let other_four = terms.mk_var("other-four", Sort::bitvec(4));
    let a = eq(&mut terms, four, four);
    let b = eq(&mut terms, three, three);
    let c = eq(&mut terms, other_four, other_four);
    assert!(!compare(&terms, &[boolean, a, b])); // 1 + 4 + 3 = 8.
    assert!(compare(&terms, &[boolean, a, c])); // 1 + 4 + 4 = 9.
    assert!(!compare(&terms, &[a, a, a]));
}

#[test]
fn classification_does_not_establish_tautology_or_validate_operator_metadata() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("not-a-theorem", Sort::bitvec(4));
    let zero = terms.mk_bitvec(BigInt::from(0u8), 4);
    let falsifiable = eq(&mut terms, value, zero);
    assert!(!compare(&terms, &[falsifiable]));
    let unsupported = terms.mk_app(Symbol::named("unknown-bv"), [value], Sort::bitvec(4));
    let unsupported_eq = eq(&mut terms, unsupported, zero);
    assert!(compare(&terms, &[unsupported_eq]));
    // Classification historically checks the operator NAME only, not indices.
    let malformed_indexed =
        terms.mk_app(Symbol::indexed("bvand", vec![91]), [value], Sort::bitvec(4));
    let malformed_eq = eq(&mut terms, malformed_indexed, zero);
    assert!(!compare(&terms, &[malformed_eq]));
    let pure_uf = terms.mk_app(Symbol::named("unknown-bool"), [], Sort::Bool);
    assert!(!compare(&terms, &[pure_uf]));
    assert!(collect_bounded_vars(&terms, &[pure_uf]).is_none());
}

#[test]
fn presence_walk_sees_let_values_and_quantifier_triggers_but_bounded_walk_declines_them() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("hidden-bv", Sort::bitvec(1));
    let truth = terms.true_term();
    let local = terms.mk_let(vec![("local".to_owned(), value)], truth);
    let forall = terms.mk_forall_with_triggers(vec![], truth, vec![vec![], vec![value]]);
    let exists = terms.mk_exists_with_triggers(vec![], truth, vec![vec![value]]);
    for root in [local, forall, exists] {
        assert!(compare(&terms, &[root]));
        assert!(collect_bounded_vars(&terms, &[root]).is_none());
    }
}

#[test]
fn variable_discovery_keeps_recursive_clause_order_and_deduplication() {
    let mut terms = TermStore::new();
    let first = terms.mk_var("first", Sort::Bool);
    let second = terms.mk_var("second", Sort::bitvec(4));
    let third = terms.mk_var("third", Sort::bitvec(1));
    let fourth = terms.mk_var("fourth", Sort::Bool);
    let left = eq(&mut terms, second, second);
    let right = eq(&mut terms, third, third);
    let choice = terms.mk_ite(first, left, right);
    let roots = [choice, fourth, left];
    compare(&terms, &roots);
    let vars = collect_bounded_vars(&terms, &roots).unwrap();
    assert_eq!(
        vars.iter().map(|var| var.term).collect::<Vec<_>>(),
        [first, second, third, fourth]
    );
}

#[test]
fn depth_512_is_accepted_but_513_refuses_even_for_an_already_visited_leaf() {
    let mut terms = TermStore::new();
    let leaf = terms.mk_var("deep-leaf", Sort::Bool);
    let mut deep = leaf;
    for _ in 0..512 {
        deep = terms.mk_not_raw(deep);
    }
    let boundary = [leaf, deep];
    assert_eq!(
        collect_bounded_vars(&terms, &boundary),
        oracle::bounded_vars(&terms, &boundary)
    );
    assert!(collect_bounded_vars(&terms, &boundary).is_some());
    deep = terms.mk_not_raw(deep);
    let over = [leaf, deep];
    assert_eq!(
        collect_bounded_vars(&terms, &over),
        oracle::bounded_vars(&terms, &over)
    );
    assert!(collect_bounded_vars(&terms, &over).is_none());
}

#[test]
fn duplicate_edges_receive_checkpoints_in_both_walks() {
    let mut terms = TermStore::new();
    let leaf = terms.mk_var("duplicate", Sort::Bool);
    let narrow = terms.mk_app(Symbol::named("or"), [leaf], Sort::Bool);
    let wide = terms.mk_app(Symbol::named("or"), vec![leaf; 65], Sort::Bool);
    let usage = |root| {
        let mut presence_calls = 0;
        let mut variable_calls = 0;
        let presence: Result<_, Infallible> = mentions_bv(&terms, &[root], &mut || {
            presence_calls += 1;
            Ok(())
        });
        let variables: Result<_, Infallible> = bounded_vars(&terms, &[root], &mut || {
            variable_calls += 1;
            Ok(())
        });
        assert_eq!(presence, Ok(false));
        assert_eq!(variables.unwrap().unwrap().len(), 1);
        (presence_calls, variable_calls)
    };
    let a = usage(narrow);
    let b = usage(wide);
    assert_eq!(b.0 - a.0, 64 * 3); // Push, pop, visited-result poll.
    assert_eq!(b.1 - a.1, 64 * 2); // Recursive entry, visited-result poll.
}

#[test]
fn exact_mixed_census_totals_and_ninth_step_error_match_old_census() {
    let mut terms = TermStore::new();
    let wide = terms.mk_var("expensive", Sort::bitvec(16));
    let equality = eq(&mut terms, wide, wide);
    let mut proof = Proof::new();
    let kinds = [
        TheoryLemmaKind::BvBitBlast,
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 3,
        },
        TheoryLemmaKind::BvLiaTautology,
        TheoryLemmaKind::SeqExtensionalCompanionContradiction,
    ];
    for kind in kinds {
        proof.add_step(tagged(equality, kind));
    }
    proof.add_step(evaluate(&mut terms, "bvmul"));
    for _ in 0..3 {
        proof.add_step(tagged(equality, TheoryLemmaKind::BvLiaTautology));
    }
    let expected = oracle::census(&proof, &terms);
    assert_eq!(
        expected,
        Ok(ExpensiveBvAggregateCharge {
            work: 2 * MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize
                + 5 * MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA as usize
                + closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA as usize,
            bytes: 2 * MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
                + 5 * MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA
                + closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_BYTES_PER_LEMMA,
        })
    );
    assert_eq!(
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| true),
        expected
    );
    proof.add_step(tagged(equality, TheoryLemmaKind::BvBitBlast));
    let expected = oracle::census(&proof, &terms);
    assert!(matches!(
        expected,
        Err(ProofCheckError::InvalidTheoryLemma {
            step: ProofId(8),
            ..
        })
    ));
    assert_eq!(
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| true),
        expected
    );
}

#[test]
fn evaluate_census_stays_directional_and_counts_malformed_costly_roots() {
    let mut terms = TermStore::new();
    for name in ["bvmul", "zero_extend", "extract", "concat"] {
        let step = evaluate(&mut terms, name);
        let proof = Proof::from_steps(vec![step]);
        let expected = oracle::census(&proof, &terms).unwrap();
        assert_eq!(expected.work != 0, name != "concat");
        assert_eq!(
            validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| true),
            Ok(expected)
        );
    }
    let step = evaluate(&mut terms, "bvmul");
    let ProofStep::Step { clause, .. } = step else {
        panic!("evaluate fixture")
    };
    let TermData::App(_, args) = terms.get(clause[0]) else {
        panic!("equality fixture")
    };
    let (left, right) = (args[0], args[1]);
    let reversed = eq(&mut terms, right, left);
    let proof = Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::Evaluate,
        clause: vec![reversed],
        premises: vec![],
        args: vec![],
    }]);
    assert_eq!(
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| true),
        Ok(ExpensiveBvAggregateCharge::default())
    );
}

#[test]
fn unsafe_signed_and_repeat_words_refuse_before_bounded_evaluation() {
    for width in [63, 64, 65, 128] {
        let mut terms = TermStore::new();
        let value = terms.mk_bitvec(BigInt::from(1), width);
        for name in [
            "bvslt", "bvsle", "bvsgt", "bvsge", "bvsdiv", "bvsrem", "bvsmod",
        ] {
            let sort = if matches!(name, "bvslt" | "bvsle" | "bvsgt" | "bvsge") {
                Sort::Bool
            } else {
                Sort::bitvec(width)
            };
            let operation = terms.mk_app(Symbol::named(name), &[value, value], sort);
            assert_eq!(
                collect_bounded_vars(&terms, &[operation]).is_some(),
                width < 64,
                "{name}/{width}"
            );
        }
        let repeat = terms.mk_app(
            Symbol::indexed("repeat", vec![1]),
            &[value],
            Sort::bitvec(width),
        );
        assert_eq!(
            collect_bounded_vars(&terms, &[repeat]).is_some(),
            width < 64
        );
    }
}
