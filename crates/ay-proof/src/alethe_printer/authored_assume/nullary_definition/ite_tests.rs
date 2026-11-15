// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `ite` congruence head of the definition schema, each case replayed
//! through pinned carcara.
//!
//! `benchmarks/smt/known_bugs/bv_ite_shared_vars_minimal.smt2` asserts
//! `(ite m1 (= x1 ..) (= x1 ..))` over `(define-fun m1 () Bool (= mode_1 (_
//! bv0 1)))`. The canonical root is an `ite` (a term constructor, not a symbol
//! application), so before the `ite` arm no schema could split it, the
//! producer's preflight declined the authored spelling, and the query
//! published the expanded `(assume t0 (ite (= mode_1 #b0) ..))` that pinned
//! carcara refuses ("could not match term to any of the original problem
//! premises").

use super::*;

/// `(ite (= mode #b0) (= v0 #b1) (= v0 #b0))` built raw, so its canonical
/// text is exactly that, and its raw negation.
fn macro_guarded_ite(terms: &mut TermStore) -> (TermId, TermId) {
    let mode = terms.mk_var("mode", Sort::bitvec(1));
    let v0 = terms.mk_var("v0", Sort::bitvec(1));
    let zero = terms.mk_bitvec(0.into(), 1);
    let one = terms.mk_bitvec(1.into(), 1);
    let condition = terms.mk_app(Symbol::named("="), [mode, zero], Sort::Bool);
    let then_term = terms.mk_app(Symbol::named("="), [v0, one], Sort::Bool);
    let else_term = terms.mk_app(Symbol::named("="), [v0, zero], Sort::Bool);
    let root = terms.mk_ite_raw(condition, then_term, else_term);
    let negated = terms.mk_not_raw(root);
    (root, negated)
}

const CANONICAL: &str = "(ite (= mode #b0) (= v0 #b1) (= v0 #b0))";

/// The problem whose first assertion is `authored` over the definitions
/// `m`, `hi` and `lo`, refuted by the canonical term's negation.
fn problem(authored: &str) -> String {
    format!(
        "(set-logic ALL)\n(declare-const mode (_ BitVec 1))\n(declare-const v0 (_ BitVec 1))\n\
         (define-fun m () Bool (= mode (_ bv0 1)))\n(define-fun hi () Bool (= v0 #b1))\n\
         (define-fun lo () Bool (= v0 #b0))\n(assert {authored})\n\
         (assert (not {CANONICAL}))\n(check-sat)\n"
    )
}

/// The macro-guarded `ite` is assumed as written and bridged by `cong` under
/// the canonical `ite`, reading one definition premise per macro operand: the
/// condition alone (the `t0` shape of the known-bugs reproducer) and the
/// condition with macro branches (its `t1` shape, macros below the branch).
#[test]
fn a_macro_guarded_ite_assume_is_bridged_by_cong_under_ite() {
    let mut terms = TermStore::new();
    let (root, negated) = macro_guarded_ite(&mut terms);
    let definitions = table(&[
        ("m", "(= mode (_ bv0 1))"),
        ("hi", "(= v0 #b1)"),
        ("lo", "(= v0 #b0)"),
    ]);
    for (case, authored, premises) in [
        (
            "ite_condition",
            "(ite m (= v0 #b1) (= v0 #b0))",
            &["(assume t0.n.c0 (= m (= mode (_ bv0 1))))"][..],
        ),
        (
            "ite_branches",
            "(ite m hi lo)",
            &[
                "(assume t0.n.c0 (= m (= mode (_ bv0 1))))",
                "(assume t0.n.c1 (= hi (= v0 #b1)))",
                "(assume t0.n.c2 (= lo (= v0 #b0)))",
            ][..],
        ),
    ] {
        assert!(
            nullary_definition_assume_bridge_is_supported(&terms, root, authored, &definitions),
            "{case}"
        );
        let proof = export(&terms, root, negated, authored, Some(&definitions))
            .unwrap_or_else(|e| panic!("{case}: the definition premises bridge the ite: {e:?}"));
        assert!(
            proof.contains(&format!("(assume t0.a {authored})")),
            "{case}:\n{proof}"
        );
        for premise in premises {
            assert!(proof.contains(premise), "{case}: {premise}:\n{proof}");
        }
        assert!(
            proof.contains(&format!(
                "(step t0.n (cl (= {authored} {CANONICAL})) :rule cong"
            )),
            "{case}:\n{proof}"
        );
        assert!(
            proof.contains(&format!("(step t0 (cl {CANONICAL}) :rule resolution")),
            "{case}:\n{proof}"
        );
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{case}:\n{proof}"
        );
        assert_carcara_valid(case, &problem(authored), &proof);
    }
}

/// Negative twins of the `ite` arm: swapped branches are a different
/// assertion and are never bridged; a body that is not the term never becomes
/// a leaf; without a table the ordinary schema never treats `ite` as a
/// congruence head; and a respelling that reads no definition premise (only
/// a literal spelling differs) is not this schema's to bridge.
#[test]
fn a_macro_guarded_ite_without_its_definition_is_never_bridged() {
    let mut terms = TermStore::new();
    let (root, negated) = macro_guarded_ite(&mut terms);
    let definitions = table(&[
        ("m", "(= mode (_ bv0 1))"),
        ("hi", "(= v0 #b1)"),
        ("lo", "(= v0 #b0)"),
    ]);
    for swapped in ["(ite m (= v0 #b0) (= v0 #b1))", "(ite m lo hi)"] {
        assert!(
            !nullary_definition_assume_bridge_is_supported(&terms, root, swapped, &definitions),
            "{swapped}"
        );
    }
    let authored = "(ite m (= v0 #b1) (= v0 #b0))";
    let wrong = table(&[("m", "(= mode (_ bv1 1))")]);
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms, root, authored, &wrong
    ));
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        authored,
        &HashMap::default()
    ));
    assert!(!nullary_definition_assume_bridge_is_supported(
        &terms,
        root,
        "(ite (= mode (_ bv0 1)) (= v0 #b1) (= v0 #b0))",
        &definitions
    ));
    let without = format!("{:?}", export(&terms, root, negated, authored, None));
    assert!(!without.contains(":rule cong"), "{without}");
    assert!(!without.contains("(= m "), "{without}");
    let mismatched = format!(
        "{:?}",
        export(&terms, root, negated, authored, Some(&wrong))
    );
    assert_eq!(mismatched, without);
}
