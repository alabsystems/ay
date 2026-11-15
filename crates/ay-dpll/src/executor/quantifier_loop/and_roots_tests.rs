// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, Symbol, TermId, TermStore};

use super::{flatten_quantified_and_roots, roots_match_certificate_partition};

struct Fixture {
    terms: TermStore,
    forall: TermId,
    ground_a: TermId,
    ground_b: TermId,
}

/// `forall g. g >= h`, and the ground atoms `h >= a`, `h >= b`.
fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let h = terms.mk_var("h", Sort::Real);
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let g = terms.mk_var("g", Sort::Real);
    let body = terms.mk_ge(g, h);
    let forall = terms.mk_forall(vec![("g".to_string(), Sort::Real)], body);
    let ground_a = terms.mk_ge(h, a);
    let ground_b = terms.mk_ge(h, b);
    Fixture {
        terms,
        forall,
        ground_a,
        ground_b,
    }
}

/// A raw, UNFLATTENED `and` node: `mk_and` would flatten and sort its
/// arguments, and the point of these tests is the shape an authored root can
/// still have.
fn raw_and(terms: &mut TermStore, args: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named("and"), args, Sort::Bool)
}

#[test]
fn quantified_and_root_is_split_into_its_leaves_in_order() {
    let mut f = fixture();
    let inner = raw_and(&mut f.terms, &[f.ground_a, f.ground_b]);
    let root = raw_and(&mut f.terms, &[f.forall, inner]);
    assert_eq!(
        flatten_quantified_and_roots(&f.terms, &[root]),
        vec![f.forall, f.ground_a, f.ground_b]
    );
}

#[test]
fn nested_quantified_and_under_a_ground_prefix_is_split() {
    let mut f = fixture();
    let inner = raw_and(&mut f.terms, &[f.forall, f.ground_b]);
    let root = raw_and(&mut f.terms, &[f.ground_a, inner]);
    assert_eq!(
        flatten_quantified_and_roots(&f.terms, &[root]),
        vec![f.ground_a, f.forall, f.ground_b]
    );
}

/// Strict additivity: a ground `and` root, a bare `forall` and a ground atom
/// all pass through unchanged and in place, so every partition a producer
/// admitted before is reproduced exactly.
#[test]
fn roots_without_a_quantified_and_are_untouched() {
    let mut f = fixture();
    let ground_and = raw_and(&mut f.terms, &[f.ground_a, f.ground_b]);
    let roots = [f.ground_a, ground_and, f.forall];
    assert_eq!(
        flatten_quantified_and_roots(&f.terms, &roots),
        roots.to_vec()
    );
}

/// Only `and` is a conjunctive position. A quantifier below `or`/`not` stays
/// inside its root, so a producer still sees (and declines) the out-of-class
/// shape instead of a forall it could wrongly discharge on its own.
#[test]
fn quantifier_below_a_non_and_connective_is_not_lifted() {
    let mut f = fixture();
    let or = f.terms.mk_or(vec![f.forall, f.ground_a]);
    let not_forall = f.terms.mk_not(f.forall);
    let root = raw_and(&mut f.terms, &[or, not_forall, f.ground_b]);
    assert_eq!(
        flatten_quantified_and_roots(&f.terms, &[root]),
        vec![or, not_forall, f.ground_b]
    );
}

#[test]
fn several_roots_keep_their_relative_order() {
    let mut f = fixture();
    let root = raw_and(&mut f.terms, &[f.forall, f.ground_a]);
    assert_eq!(
        flatten_quantified_and_roots(&f.terms, &[f.ground_b, root, f.ground_a]),
        vec![f.ground_b, f.forall, f.ground_a, f.ground_a]
    );
}

/// The public-root rescue admits a `(and forall ground)` root, exactly as it
/// admits the same conjuncts asserted separately.
#[test]
fn partition_shape_admits_a_quantified_and_root() {
    let mut f = fixture();
    let root = raw_and(&mut f.terms, &[f.forall, f.ground_a]);
    assert!(roots_match_certificate_partition(
        &f.terms,
        &[root, f.ground_b]
    ));
    assert!(roots_match_certificate_partition(
        &f.terms,
        &[f.forall, f.ground_a]
    ));
}

/// It still refuses what no producer partitions: a quantifier below a
/// non-`and` connective, and a snapshot without any top-level `forall`.
#[test]
fn partition_shape_refuses_non_conjunctive_quantifiers_and_all_ground_roots() {
    let mut f = fixture();
    let or = f.terms.mk_or(vec![f.forall, f.ground_a]);
    let root = raw_and(&mut f.terms, &[f.forall, or]);
    assert!(!roots_match_certificate_partition(&f.terms, &[root]));
    let ground_and = raw_and(&mut f.terms, &[f.ground_a, f.ground_b]);
    assert!(!roots_match_certificate_partition(
        &f.terms,
        &[ground_and, f.ground_a]
    ));
}
