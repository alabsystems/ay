// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{CanonicalNode, Derivation};
use super::*;

fn bv(terms: &mut TermStore, name: &str, width: u32) -> TermId {
    terms.mk_var(name, Sort::bitvec(width))
}

fn app(terms: &mut TermStore, head: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(head), args, sort)
}

fn rules(steps: &[String]) -> Vec<String> {
    steps
        .iter()
        .map(|step| {
            let rule = step.split(":rule ").nth(1).expect("a rule");
            rule.split([' ', ')']).next().expect("a name").to_string()
        })
        .collect()
}

fn derive(terms: &TermStore, surface: &str, term: TermId) -> Option<Vec<String>> {
    let printer = AlethePrinter::new(terms);
    let canonical = printer.format_term(term);
    printer
        .printed_surface_equivalence_steps("t9.n", surface, term, &canonical)
        .map(|(steps, _)| steps)
}

/// `(or (= (g k) x) (not (bvult k n)))`.
fn guarded_disjunction(terms: &mut TermStore) -> TermId {
    let k = bv(terms, "k", 8);
    let n = bv(terms, "n", 8);
    let x = bv(terms, "x", 8);
    let applied = app(terms, "g", vec![k], Sort::bitvec(8));
    let equality = app(terms, "=", vec![applied, x], Sort::Bool);
    let guard = app(terms, "bvult", vec![k, n], Sort::Bool);
    let negated_guard = terms.mk_not_raw(guard);
    app(terms, "or", vec![equality, negated_guard], Sort::Bool)
}

/// `(not (not (bvuge j old)))` over the canonical `(bvule old j)`: the double
/// negation, then the operand-swap reversal on what it leaves.
#[test]
fn double_negation_joins_the_inner_schema_with_trans() {
    let mut terms = TermStore::new();
    let j = bv(&mut terms, "j", 4);
    let old = bv(&mut terms, "old", 4);
    let canonical = app(&mut terms, "bvule", vec![old, j], Sort::Bool);
    let steps = derive(&terms, "(not (not (bvuge j old)))", canonical).expect("not_simplify");
    assert_eq!(
        rules(&steps),
        [
            "pbblast_bvuge",
            "pbblast_bvule",
            "symm",
            "trans",
            "not_simplify",
            "trans"
        ]
    );
    assert_eq!(
        steps.last().map(String::as_str),
        Some("(step t9.n (cl (= (not (not (bvuge j old))) (bvule old j))) :rule trans :premises (t9.n.nn t9.n.nr))")
    );
}

/// `(not (distinct x y))` over the canonical `(= y x)`.
#[test]
fn negated_distinct_eliminates_onto_the_equality() {
    let mut terms = TermStore::new();
    let x = bv(&mut terms, "x", 8);
    let y = bv(&mut terms, "y", 8);
    let canonical = app(&mut terms, "=", vec![y, x], Sort::Bool);
    let steps = derive(&terms, "(not (distinct x y))", canonical).expect("distinct_elim");
    assert_eq!(
        rules(&steps),
        [
            "refl",
            "not_simplify",
            "trans",
            "distinct_elim",
            "cong",
            "trans"
        ]
    );
    assert!(steps.contains(
        &"(step t9.n.dc (cl (= (not (distinct x y)) (not (not (= x y))))) :rule cong :premises (t9.n.de))"
            .to_string()
    ));
}

/// NEGATIVE TWIN: a negation elaboration did NOT eliminate is no equivalence
/// these schemas may claim, and the caller keeps its refusal.
#[test]
fn negations_of_other_formulas_decline() {
    let mut terms = TermStore::new();
    let disjunction = guarded_disjunction(&mut terms);
    // A single double negation is one disjunct, not the disjunction.
    assert_eq!(derive(&terms, "(not (not (= (g k) x)))", disjunction), None);
    let j = bv(&mut terms, "j", 4);
    let old = bv(&mut terms, "old", 4);
    let non_strict = app(&mut terms, "bvule", vec![old, j], Sort::Bool);
    // Strict under a double negation is still strict.
    assert_eq!(
        derive(&terms, "(not (not (bvugt j old)))", non_strict),
        None
    );
    let x = bv(&mut terms, "x2", 8);
    let y = bv(&mut terms, "y2", 8);
    let z = bv(&mut terms, "z2", 8);
    let equality = app(&mut terms, "=", vec![x, z], Sort::Bool);
    // Another operand, and a ternary `distinct`, are other formulas.
    assert_eq!(derive(&terms, "(not (distinct x2 y2))", equality), None);
    assert_eq!(derive(&terms, "(not (distinct x2 z2 y2))", equality), None);
    let _ = y;
}

/// A first attempt never admits these schemas, so a pair an older schema
/// relates keeps its older derivation byte-for-byte.
#[test]
fn the_first_attempt_does_not_admit_the_negation_schemas() {
    let mut terms = TermStore::new();
    let x = bv(&mut terms, "x", 8);
    let y = bv(&mut terms, "y", 8);
    let canonical = app(&mut terms, "=", vec![x, y], Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    let text = printer.format_term(canonical);
    let node = CanonicalNode {
        term: canonical,
        text: &text,
    };
    let surface = "(not (not (= x y)))";
    let mut first = Derivation::default();
    assert!(!printer.derive_printed_equivalence("t9.n", surface, node, 0, &mut first));
    assert!(first.steps.is_empty());
    let mut second = Derivation {
        tier: SchemaTier::Extended,
        ..Derivation::default()
    };
    assert!(printer.derive_printed_equivalence("t9.n", surface, node, 0, &mut second));
    assert_eq!(rules(&second.steps), ["not_simplify"]);
}
