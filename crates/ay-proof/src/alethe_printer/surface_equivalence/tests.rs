// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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
            let rule = step
                .split(":rule ")
                .nth(1)
                .expect("every step names its rule");
            rule.split([' ', ')'])
                .next()
                .expect("rule name")
                .to_string()
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

/// `(=> (bvult k n) (= (select a k) x))` elaborates to
/// `(or (= x (select a k)) (not (bvult k n)))`: disjuncts swapped and the
/// consequent's equality reoriented.
#[test]
fn authored_implication_derives_its_canonical_disjunction() {
    let mut terms = TermStore::new();
    let k = bv(&mut terms, "k", 64);
    let n = bv(&mut terms, "n", 64);
    let x = bv(&mut terms, "x", 8);
    let a = terms.mk_var("a", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
    let select = app(&mut terms, "select", vec![a, k], Sort::bitvec(8));
    let equality = app(&mut terms, "=", vec![x, select], Sort::Bool);
    let guard = app(&mut terms, "bvult", vec![k, n], Sort::Bool);
    let negated_guard = terms.mk_not_raw(guard);
    let disjunction = app(&mut terms, "or", vec![equality, negated_guard], Sort::Bool);
    let steps = derive(&terms, "(=> (bvult k n) (= (select a k) x))", disjunction)
        .expect("the implication is its disjunction up to literal order and orientation");
    let last = steps.last().expect("a derivation");
    assert!(
        last.starts_with(
            "(step t9.n (cl (= (=> (bvult k n) (= (select a k) x)) (or (= x (select a k)) (not (bvult k n))))) :rule resolution"
        ),
        "{last}"
    );
    let used = rules(&steps);
    for rule in [
        "implies_pos",
        "implies_neg1",
        "implies_neg2",
        "or_pos",
        "or_neg",
        "equiv_neg1",
        "equiv_neg2",
        "refl",
    ] {
        assert!(
            used.iter().any(|used| used == rule),
            "{rule} missing: {steps:#?}"
        );
    }
}

/// `(bvuge j old)` is stored as `(bvule old j)`: both blast to the same
/// pseudo-Boolean constraint.
#[test]
fn swapped_unsigned_comparison_goes_through_pbblast() {
    let mut terms = TermStore::new();
    let j = bv(&mut terms, "j", 4);
    let old = bv(&mut terms, "old", 4);
    let canonical = app(&mut terms, "bvule", vec![old, j], Sort::Bool);
    let steps = derive(&terms, "(bvuge j old)", canonical).expect("pbblast pair");
    assert_eq!(
        rules(&steps),
        ["pbblast_bvuge", "pbblast_bvule", "symm", "trans"]
    );
    // Both blasts name the SAME constraint, which is what `trans` joins.
    let constraint = |step: &str| {
        step.split_once(") (>= ")
            .and_then(|(_, rest)| rest.rsplit_once(" :rule "))
            .map(|(constraint, _)| constraint.to_string())
            .expect("a pbblast conclusion")
    };
    assert_eq!(constraint(&steps[0]), constraint(&steps[1]));
}

#[test]
fn authored_distinct_is_eliminated_onto_either_orientation() {
    let mut terms = TermStore::new();
    let x = bv(&mut terms, "x", 8);
    let y = bv(&mut terms, "y", 8);
    let equality = app(&mut terms, "=", vec![y, x], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let steps = derive(&terms, "(distinct x y)", negated).expect("distinct_elim");
    assert_eq!(rules(&steps), ["distinct_elim"]);
}

/// Different operand VALUES, a signed comparison, or a head the canonical term
/// does not have are not equivalences this module may claim.
#[test]
fn unrelated_spellings_decline() {
    let mut terms = TermStore::new();
    let j = bv(&mut terms, "j", 4);
    let old = bv(&mut terms, "old", 4);
    let new = bv(&mut terms, "new", 4);
    let canonical = app(&mut terms, "bvule", vec![old, j], Sort::Bool);
    // Same operator, operands NOT swapped: `(bvule j old)` is a different atom.
    assert_eq!(derive(&terms, "(bvule j old)", canonical), None);
    // Swapped operator but a foreign operand.
    assert_eq!(derive(&terms, "(bvuge new old)", canonical), None);
    // Strict for non-strict is a different relation.
    assert_eq!(derive(&terms, "(bvugt j old)", canonical), None);
    // Signed comparisons are outside the pbblast table.
    assert_eq!(derive(&terms, "(bvsge j old)", canonical), None);

    // An implication whose consequent is not among the disjuncts.
    let guard = app(&mut terms, "bvult", vec![j, new], Sort::Bool);
    let negated_guard = terms.mk_not_raw(guard);
    let other = app(&mut terms, "bvult", vec![old, new], Sort::Bool);
    let disjunction = app(&mut terms, "or", vec![other, negated_guard], Sort::Bool);
    assert_eq!(
        derive(&terms, "(=> (bvult j new) (bvult j old))", disjunction),
        None
    );
    // An implication stated backwards is a different formula.
    assert_eq!(
        derive(&terms, "(=> (bvult old new) (bvult j new))", disjunction),
        None
    );
}

/// `QF_ABV_wide_mul_unsat`'s authored atom and the canonical term the store
/// keeps for it: `(bvugt (select (store a #x00 p) #x00) #x00000000)` is
/// `(bvult 0 p)` once preprocessing folds the read-over-write and flips the
/// comparison.
fn wide_mul_atom(terms: &mut TermStore) -> (TermId, TermId) {
    let x = bv(terms, "x", 32);
    let y = bv(terms, "y", 32);
    let _array = terms.mk_var("a", Sort::array(Sort::bitvec(8), Sort::bitvec(32)));
    let zero = terms.mk_bitvec(num_bigint::BigInt::from(0), 32);
    let product = app(terms, "bvmul", vec![x, y], Sort::bitvec(32));
    let canonical = app(terms, "bvult", vec![zero, product], Sort::Bool);
    (canonical, product)
}

#[test]
fn reversed_comparison_over_a_same_index_read_derives_the_folded_canonical() {
    let mut terms = TermStore::new();
    let (canonical, _) = wide_mul_atom(&mut terms);
    let steps = derive(
        &terms,
        "(bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000000)",
        canonical,
    )
    .expect("pbblast reversal, then arrays_idx under cong");
    let used = rules(&steps);
    assert_eq!(used.last().map(String::as_str), Some("trans"), "{steps:#?}");
    for rule in [
        "pbblast_bvugt",
        "pbblast_bvult",
        "symm",
        "arrays_idx",
        "cong",
    ] {
        assert!(used.iter().any(|used| used == rule), "{rule}: {steps:#?}");
    }
    let last = steps.last().expect("a derivation");
    assert!(
        last.starts_with(
            "(step t9.n (cl (= (bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000000) (bvult "
        ) && last.ends_with(":premises (t9.n.ps t9.n.cs t9.n.ro))"),
        "{last}"
    );
    let read = steps
        .iter()
        .find(|step| step.contains(":rule arrays_idx"))
        .expect("the read-over-write step");
    assert_eq!(
        read,
        "(step t9.n.ro.c1 (cl (= (select (store a #x00 (bvmul x y)) #x00) (bvmul x y))) :rule arrays_idx)"
    );

    // The same read without the reversal is one `arrays_idx` under `cong`.
    let steps = derive(
        &terms,
        "(bvult #x00000000 (select (store a #x00 (bvmul x y)) #x00))",
        canonical,
    )
    .expect("arrays_idx under cong");
    assert!(rules(&steps).iter().any(|rule| rule == "arrays_idx"));
    assert_eq!(rules(&steps).last().map(String::as_str), Some("cong"));
}

/// NEGATIVE TWIN: a read at ANOTHER index, a stored element that is not the
/// canonical operand, a reversal whose operand is unrelated, or the strict
/// relation for a non-strict one is not an equivalence this module may claim.
#[test]
fn foreign_reads_and_unrelated_operands_decline() {
    let mut terms = TermStore::new();
    let (canonical, product) = wide_mul_atom(&mut terms);
    for surface in [
        // Another index: `arrays_row` territory, which needs a disequality.
        "(bvugt (select (store a #x00 (bvmul x y)) #x01) #x00000000)",
        "(bvult #x00000000 (select (store a #x00 (bvmul x y)) #x01))",
        // The stored element is a different product.
        "(bvugt (select (store a #x00 (bvmul y x)) #x00) #x00000000)",
        "(bvugt (select (store a #x00 x) #x00) #x00000000)",
        // A read of the base array, not of the write.
        "(bvugt (select a #x00) #x00000000)",
        // The reversed constant operand is another value.
        "(bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000001)",
        // Non-strict for strict.
        "(bvuge (select (store a #x00 (bvmul x y)) #x00) #x00000000)",
        // The canonical relation with its operands swapped is another one.
        "(bvult (select (store a #x00 (bvmul x y)) #x00) #x00000000)",
        // Signed comparisons are outside the pbblast table.
        "(bvsgt (select (store a #x00 (bvmul x y)) #x00) #x00000000)",
    ] {
        assert_eq!(derive(&terms, surface, canonical), None, "{surface}");
    }
    // The bare read against the element, and against another element.
    assert!(derive(&terms, "(select (store a #x00 (bvmul x y)) #x00)", product).is_some());
    assert_eq!(
        derive(&terms, "(select (store a #x00 (bvmul x y)) #x01)", product),
        None
    );
}

/// A reversal whose re-spelled operand no schema relates declines WITHOUT
/// leaving its `pbblast_*` steps behind for a later alternative to inherit
/// (a stale `t9.n.ps` would be a second step of that name in the document).
#[test]
fn declined_respelled_reversal_leaves_no_steps_behind() {
    let mut terms = TermStore::new();
    let (canonical, _) = wide_mul_atom(&mut terms);
    let printer = AlethePrinter::new(&terms);
    let text = printer.format_term(canonical);
    let node = CanonicalNode {
        term: canonical,
        text: &text,
    };
    let earlier = "(step t8 (cl (= x x)) :rule refl)".to_string();
    let mut derivation = Derivation {
        steps: vec![earlier.clone()],
        ..Derivation::default()
    };
    // The read is at ANOTHER index, so the `cong` leg cannot be derived.
    let surface = "(bvugt (select (store a #x00 (bvmul x y)) #x01) #x00000000)";
    assert!(!printer.unsigned_comparison_reversal("t9.n", surface, node, 0, &mut derivation));
    assert_eq!(derivation.steps, [earlier]);
}
