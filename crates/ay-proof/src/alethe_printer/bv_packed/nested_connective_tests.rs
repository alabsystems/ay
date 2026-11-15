// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `(= (and true X) X)` with `X` itself a conjunction is printed through the
//! unary `(and X)` the consumer's `and_simplify` unwraps (likewise `or`).
//!
//! Measured on external-codegen's `narrow u8 mul`/`AtomicRmw ... Or` obligations: AY
//! printed the one-step form, which Carcara 9a352ee and Clean 414913cce both
//! refuse (`expected (and a b) to be (and (and a b))`), on 11 certificates AY
//! had disclosed hole-free.

use super::*;
use ay_core::TermStore;

fn bodies<'a>(table: &'a [(&'a str, &'a str)]) -> impl Fn(&str) -> Option<&'a str> + 'a {
    move |name| {
        table
            .iter()
            .find(|(defined, _)| *defined == name)
            .map(|(_, body)| *body)
    }
}

#[test]
fn only_the_nested_surviving_operand_is_rerouted() {
    let none: &[(&str, &str)] = &[];
    let named = [("n", "(and a b)"), ("m", "n"), ("o", "(or c d)")];
    let nested = [
        ("and_simplify", "(and true (and a b))", "(and a b)"),
        ("and_simplify", "(and (and a b) true)", "(and a b)"),
        ("and_simplify", "(and (and a b) (and a b))", "(and a b)"),
        ("and_simplify", "(and true n)", "n"),
        ("and_simplify", "(and true m)", "n"),
        ("or_simplify", "(or (or c d) false)", "(or c d)"),
        ("or_simplify", "(or o false)", "o"),
    ];
    for (rule, left, right) in nested {
        assert_eq!(
            nested_connective_simplification(rule, left, right, bodies(&named)),
            rule.strip_suffix("_simplify"),
            "{left} -> {right}"
        );
    }
    let direct = [
        // The consumer compares these directly; they must stay one step.
        ("and_simplify", "(and true a)", "a"),
        ("and_simplify", "(and true a b)", "(and a b)"),
        ("and_simplify", "(and false (and a b))", "false"),
        ("and_simplify", "(and n)", "n"),
        ("or_simplify", "(or c false)", "c"),
        ("ite_simplify", "(and true (and a b))", "(and a b)"),
    ];
    for (rule, left, right) in direct {
        assert_eq!(
            nested_connective_simplification(rule, left, right, bodies(&named)),
            None,
            "{left} -> {right}"
        );
    }
    assert_eq!(
        nested_connective_simplification("and_simplify", "(and true n)", "n", bodies(none)),
        None,
        "an undefined name is an atom, not a conjunction"
    );
}

#[test]
fn a_nested_simplification_prints_through_the_unary_application() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let mut proof = PackedProof::new(&printer, ProofId(7)).expect("packed proof");
    let equality = proof
        .equality("(and true (and a b))", "(and a b)", "and_simplify", &[])
        .expect("the simplification prints");
    assert_eq!(equality.left, "(and true (and a b))");
    assert_eq!(equality.right, "(and a b)");
    let steps: Vec<&str> = proof.out.lines().collect();
    assert_eq!(
        steps,
        [
            "(step t7.packed.0 (cl (= (and true (and a b)) (and (and a b)))) :rule and_simplify)",
            "(step t7.packed.1 (cl (= (and (and a b)) (and a b))) :rule and_simplify)",
            "(step t7.packed.2 (cl (= (and true (and a b)) (and a b))) :rule trans :premises (t7.packed.0 t7.packed.1))",
        ]
    );
}
