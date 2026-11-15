// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn controlled_alpha_keeps_the_existing_grammar_and_verdicts() {
    for (left, right) in [
        ("(= (* 3 m) x)", "(= x (* 3 m))"),
        ("#x03", "(_\tbv3\n8)"),
        ("#x03", "( _ bv3 8)"),
        ("(forall ((x Int)) (= x a))", "(forall ((y Int)) (= a y))"),
        ("(= x y)", "(= x z)"),
        ("(f x", "(f x)"),
    ] {
        assert_eq!(
            printed_terms_alpha_equivalent_with_progress(left, right, &mut |_| true),
            printed_terms_alpha_equivalent(left, right),
            "{left} versus {right}",
        );
    }
}

#[test]
fn every_actual_alpha_read_comparison_and_terminal_poll_can_refuse() {
    let left = "(forall ((left Int)) (= (f left) a))";
    let right = "(forall ((right Int)) (= a (f right)))";
    let mut charges = Vec::new();
    assert!(printed_terms_alpha_equivalent_with_progress(
        left,
        right,
        &mut |amount| {
            charges.push(amount);
            true
        }
    ));
    assert_eq!(charges.last(), Some(&0));
    for stop_at in 1..=charges.len() {
        let mut calls = 0;
        assert!(
            !printed_terms_alpha_equivalent_with_progress(left, right, &mut |_| {
                calls += 1;
                calls != stop_at
            }),
            "poll {stop_at}/{}",
            charges.len()
        );
        assert_eq!(
            calls, stop_at,
            "no sibling parse or swapped retry after refusal"
        );
    }
}

#[test]
fn alpha_scanner_allocation_is_admitted_before_fields_are_read() {
    let text = format!("(f {})", vec!["x"; 512].join(" "));
    let mut calls = 0;
    let mut progress = |_| {
        calls += 1;
        calls != 2
    };
    let mut budget = Budget {
        progress: Some(&mut progress),
        ..Budget::default()
    };
    assert!(read(&text, 0, &mut budget).is_none());
    assert_eq!(budget.nodes, 1);
    assert!(budget.refused);
    assert!(budget.spend(0).is_none());
    assert_eq!(calls, 2);
}

#[test]
fn long_ordinary_atom_mismatch_does_not_pay_a_numeric_square() {
    let left = format!("symbol_{}", "a".repeat(1024));
    let right = format!("symbol_{}", "b".repeat(1024));
    let mut charged = 0;
    assert!(!printed_terms_alpha_equivalent_with_progress(
        &left,
        &right,
        &mut |amount| {
            charged += amount;
            true
        }
    ));
    assert!(charged < ((left.len() + right.len()) * 100) as u64);
}

#[test]
fn caught_alpha_owner_unwind_cannot_reopen_the_same_budget() {
    let mut owner = |_| panic!("owner unwound");
    let mut budget = Budget {
        progress: Some(&mut owner),
        ..Budget::default()
    };
    assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| { budget.spend(1) })).is_err()
    );
    assert!(budget.refused);
    assert!(budget.spend(0).is_none());
}

#[test]
fn a_numeric_operand_is_charged_even_against_an_ordinary_symbol() {
    let numeral = format!("( _ bv{} 4096)", "9".repeat(256));
    for (left, right) in [("p", numeral.as_str()), (numeral.as_str(), "p")] {
        let mut charges = Vec::new();
        assert!(!printed_terms_alpha_equivalent_with_progress(
            left,
            right,
            &mut |amount| {
                charges.push(amount);
                true
            }
        ));
        assert!(charges.contains(&((numeral.len() * numeral.len()) as u64)));
    }
}
