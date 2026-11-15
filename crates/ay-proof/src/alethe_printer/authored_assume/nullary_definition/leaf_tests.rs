// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The negated-macro unfolding and the equality-orientation leaf of the
//! definition schema, each replayed through pinned carcara.

use super::*;

/// `(assert (not nlo))` over `(define-fun nlo () Bool (not (= v0 #b1)))`, and
/// `(assert (not hi))` over `(define-fun hi () Bool (not lo))`: `mk_not`
/// drops the double negation the unfolding exposes, so the canonical root is
/// `(= v0 #b1)` and the authored text carries no textual double negation.
/// The definition premise under `cong` exposes it, and `not_simplify` strips
/// it.
#[test]
fn a_negated_macro_whose_body_is_a_negation_is_unfolded_and_stripped() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 1);
    let (root, negated) = one_bit_contradiction(&mut terms, one);
    let definitions = table(&[("nlo", "(not (= v0 #b1))")]);
    assert!(nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(not nlo)",
        &definitions
    ));
    let proof = export(&terms, root, negated, "(not nlo)", Some(&definitions))
        .expect("the unfolded double negation is stripped");
    for expected in [
        "(assume t0.a (not nlo))",
        "(assume t0.n.nd (= nlo (not (= v0 #b1))))",
        "(step t0.n.nu (cl (= (not nlo) (not (not (= v0 #b1))))) :rule cong :premises (t0.n.nd))",
        "(step t0.n.nn (cl (= (not (not (= v0 #b1))) (= v0 #b1))) :rule not_simplify)",
        "(step t0.n (cl (= (not nlo) (= v0 #b1))) :rule trans :premises (t0.n.nu t0.n.nn))",
    ] {
        assert!(proof.contains(expected), "{expected}:\n{proof}");
    }
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{proof}"
    );
    assert_carcara_valid(
        "negated_negation_body",
        "(set-logic ALL)\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun nlo () Bool (not (= v0 #b1)))\n(assert (not nlo))\n\
         (assert (not (= v0 #b1)))\n(check-sat)\n",
        &proof,
    );

    let chain = table(&[("lo", "(= v0 #b1)"), ("hi", "(not lo)")]);
    let proof = export(&terms, root, negated, "(not hi)", Some(&chain))
        .expect("the unfolded chain is stripped and bridged through `lo`");
    for expected in [
        "(assume t0.n.nd (= hi (not lo)))",
        "(step t0.n.nn (cl (= (not (not lo)) lo)) :rule not_simplify)",
        "(assume t0.n.nb (= lo (= v0 #b1)))",
        "(step t0.n (cl (= (not hi) (= v0 #b1))) :rule trans :premises (t0.n.nu t0.n.nn t0.n.nb))",
    ] {
        assert!(proof.contains(expected), "{expected}:\n{proof}");
    }
    assert_carcara_valid(
        "negated_macro_of_macro",
        "(set-logic ALL)\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun lo () Bool (= v0 #b1))\n(define-fun hi () Bool (not lo))\n\
         (assert (not hi))\n(assert (not (= v0 #b1)))\n(check-sat)\n",
        &proof,
    );
}

/// Negative twins of the unfolding: `hi` alone is the NEGATION of the root
/// (one `not` from its body), a macro whose body is no negation adds no
/// shell, and without a table nothing is unfolded.
#[test]
fn an_unfolding_of_odd_parity_or_without_a_negation_body_is_never_bridged() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 1);
    let (root, negated) = one_bit_contradiction(&mut terms, one);
    let chain = table(&[("lo", "(= v0 #b1)"), ("hi", "(not lo)")]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms, root, "hi", &chain
    ));
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(not (not hi))",
        &chain
    ));
    let plain = table(&[("nlo", "(= v0 #b1)")]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(not nlo)",
        &plain
    ));
    let without = format!("{:?}", export(&terms, root, negated, "(not nlo)", None));
    assert!(!without.contains(":rule not_simplify"), "{without}");
    assert!(!without.contains("(= nlo "), "{without}");
}

/// `(assert lo)` over `(define-fun lo () Bool (= #b1 v0))`: the term store
/// orients the equality as `(= v0 #b1)`, and `cong` under `=` would need
/// `#b1` equal to `v0`. One `eq_symmetric` step states the two orientations
/// equal.
#[test]
fn a_macro_equality_in_the_other_orientation_is_bridged_by_eq_symmetric() {
    let mut terms = TermStore::new();
    let one = terms.mk_bitvec(1.into(), 1);
    let (root, negated) = one_bit_contradiction(&mut terms, one);
    let definitions = table(&[("lo", "(= #b1 v0)")]);
    assert!(nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "lo",
        &definitions
    ));
    let proof = export(&terms, root, negated, "lo", Some(&definitions))
        .expect("eq_symmetric bridges the definition body");
    for expected in [
        "(assume t0.n.d (= lo (= #b1 v0)))",
        "(step t0.n.b (cl (= (= #b1 v0) (= v0 #b1))) :rule eq_symmetric)",
        "(step t0.n (cl (= lo (= v0 #b1))) :rule trans :premises (t0.n.d t0.n.b))",
    ] {
        assert!(proof.contains(expected), "{expected}:\n{proof}");
    }
    assert_carcara_valid(
        "equality_orientation",
        "(set-logic ALL)\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun lo () Bool (= #b1 v0))\n(assert lo)\n\
         (assert (not (= v0 #b1)))\n(check-sat)\n",
        &proof,
    );
    // Negative twins: different operands are no orientation of the root, and
    // without a table the symmetry is never tried.
    let wrong = table(&[("lo", "(= #b0 v0)")]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms, root, "lo", &wrong
    ));
    let without = format!("{:?}", export(&terms, root, negated, "lo", None));
    assert!(!without.contains("eq_symmetric"), "{without}");
}
