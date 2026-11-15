// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The swapped-operand arm of the definition schema's equality leaf: an
//! authored equality whose operands the term store swapped AND one of which
//! names a nullary macro, replayed through pinned carcara.

use super::*;

const SWAP_DECLARATIONS: &str = "(set-logic QF_AX)\n(declare-sort Index 0)\n\
    (declare-sort Elem 0)\n(declare-fun a () (Array Index Elem))\n\
    (declare-fun i () Index)\n(declare-fun j () Index)\n\
    (define-fun a1 () (Array Index Elem) (store a i (select a j)))\n\
    (define-fun a2 () (Array Index Elem) (store a1 j (select a i)))\n";

/// The expanded read `(select a2 i)` of `QF_AX/swap_two_reads.smt2`.
const EXPANDED_READ: &str = "(select (store (store a i (select a j)) j (select a i)) i)";

/// `(not (= (select a j) <EXPANDED_READ>))`, the canonical root `mk_select`
/// and `mk_eq` give `(assert (not (= (select a2 i) (select a j))))`, built raw
/// so the canonical operand order is exactly the swapped one, plus its
/// negation.
fn swapped_read_contradiction(terms: &mut TermStore) -> (TermId, TermId) {
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Elem".to_string());
    let a = terms.mk_var("a", Sort::array(index.clone(), element));
    let i = terms.mk_var("i", index.clone());
    let j = terms.mk_var("j", index);
    let read_j = terms.mk_select(a, j);
    let read_i = terms.mk_select(a, i);
    let a1 = terms.mk_store(a, i, read_j);
    let a2 = terms.mk_store(a1, j, read_i);
    let read = terms.mk_select(a2, i);
    let equality = terms.mk_app(Symbol::named("="), [read_j, read], Sort::Bool);
    let root = terms.mk_not_raw(equality);
    (root, terms.mk_not_raw(root))
}

fn swap_definitions() -> HashMap<String, String> {
    table(&[
        ("a1", "(store a i (select a j))"),
        ("a2", "(store a1 j (select a i))"),
    ])
}

/// `QF_AX/swap_two_reads.smt2`: neither `cong` in the authored order (it
/// would need `(select a2 i)` equal to `(select a j)`) nor `eq_symmetric`
/// (the swapped operands print differently) reaches the canonical root, so
/// the bridge declined and the export was refused at the closing resolution.
/// The swapped pair is bridged through both definition premises and joined
/// by one `cong` under `=`, which pinned carcara checks in every orientation.
#[test]
fn a_swapped_equality_naming_a_macro_is_bridged_by_cong_over_the_swap() {
    let mut terms = TermStore::new();
    let (root, negated) = swapped_read_contradiction(&mut terms);
    let surface = "(not (= (select a2 i) (select a j)))";
    let definitions = swap_definitions();
    assert!(nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        surface,
        &definitions
    ));
    let proof = export(&terms, root, negated, surface, Some(&definitions))
        .expect("the swapped pair is bridged through the definition premises");
    for expected in [
        format!("(assume t0.a {surface})"),
        "(assume t0.n.c0.r0.c0.d (= a2 (store a1 j (select a i))))".to_string(),
        "(assume t0.n.c0.r0.c0.b.c0 (= a1 (store a i (select a j))))".to_string(),
        format!(
            "(step t0.n.c0.r0 (cl (= (select a2 i) {EXPANDED_READ})) :rule cong \
             :premises (t0.n.c0.r0.c0))"
        ),
        format!(
            "(step t0.n.c0 (cl (= (= (select a2 i) (select a j)) (= (select a j) \
             {EXPANDED_READ}))) :rule cong :premises (t0.n.c0.r0))"
        ),
        format!("(step t0 (cl (not (= (select a j) {EXPANDED_READ}))) :rule resolution"),
    ] {
        assert!(proof.contains(&expected), "{expected}:\n{proof}");
    }
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    assert_carcara_valid(
        "swapped_macro_equality",
        &format!(
            "{SWAP_DECLARATIONS}(assert {surface})\n\
             (assert (not (not (= (select a j) {EXPANDED_READ}))))\n(check-sat)\n"
        ),
        &proof,
    );
}

/// Negative twins of the swapped arm: without a table the arm is never tried,
/// a definition that is not the expansion never becomes a premise, and an
/// authored operand that is a DIFFERENT term is no orientation of the root,
/// whatever the definitions say: the macro read at `j` instead of `i`, and
/// (the half-provable swap) the macro read bridged while its partner reads
/// `a` at `i` instead of `j`. The arm joins the pairs only when EVERY one is
/// proved.
#[test]
fn a_swapped_equality_over_a_different_term_or_definition_is_never_bridged() {
    let mut terms = TermStore::new();
    let (root, negated) = swapped_read_contradiction(&mut terms);
    let surface = "(not (= (select a2 i) (select a j)))";
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        surface,
        &HashMap::default()
    ));
    let wrong = table(&[
        ("a1", "(store a i (select a j))"),
        ("a2", "(store a1 i (select a i))"),
    ]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms, root, surface, &wrong
    ));
    for different in [
        "(not (= (select a2 j) (select a j)))",
        "(not (= (select a2 i) (select a i)))",
    ] {
        assert!(
            !nullary_definition_assume_bridge_is_supported(
                &terms,
                root,
                different,
                &swap_definitions()
            ),
            "{different}"
        );
    }
    // Whatever the ordinary path renders (or refuses) without a table is
    // exactly what a non-matching table renders: no premise is invented.
    let without = format!("{:?}", export(&terms, root, negated, surface, None));
    assert!(!without.contains("(= a2 "), "{without}");
    let mismatched = format!("{:?}", export(&terms, root, negated, surface, Some(&wrong)));
    assert_eq!(mismatched, without);
}
