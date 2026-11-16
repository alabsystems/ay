// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nested tree construction (M2): top-level Skolemization, block merging,
//! polarity bookkeeping and the fail-closed declines. The search itself is
//! exercised end to end, with a real oracle, by
//! `executor/qlra_lane/nested_tests.rs` and `executor_tests/.../m2_nested.rs`.

use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;

use super::ntree::{build_nested_tree, Kind, NestedTreeDecline};

fn real(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(n.into()))
}

fn binder(name: &str) -> Vec<(String, Sort)> {
    vec![(name.to_string(), Sort::Real)]
}

/// `∃y ∀x. y > x`: the top existential is Skolemized; one universal node
/// over the Skolem constant remains.
#[test]
fn top_existential_is_skolemized() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let gt = terms.mk_gt(y, x);
    let inner = terms.mk_forall(binder("x"), gt);
    let root = terms.mk_exists(binder("y"), inner);
    let tree = build_nested_tree(&mut terms, &[root]).expect("tree");
    assert_eq!(tree.skolems.len(), 1);
    assert_eq!(tree.nodes.len(), 1);
    assert_eq!(tree.top, vec![0]);
    assert_eq!(tree.nodes[0].kind, Kind::Forall);
    assert!(
        tree.nodes[0].env.is_empty(),
        "a Skolem is not a CE constant"
    );
}

/// `∀a ∀b ∃c ∃d. φ`: two merged blocks, the child's environment is the
/// parent's counterexample constants.
#[test]
fn same_kind_blocks_merge_and_children_see_the_parent_constants() {
    let mut terms = TermStore::new();
    let vars: Vec<TermId> = ["a", "b", "c", "d"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Real))
        .collect();
    let sum = terms.mk_add(vec![vars[0], vars[1], vars[2]]);
    let atom = terms.mk_lt(sum, vars[3]);
    let e2 = terms.mk_exists(binder("d"), atom);
    let e1 = terms.mk_exists(binder("c"), e2);
    let a2 = terms.mk_forall(binder("b"), e1);
    let root = terms.mk_forall(binder("a"), a2);
    let tree = build_nested_tree(&mut terms, &[root]).expect("tree");
    assert_eq!(tree.nodes.len(), 2);
    assert_eq!(tree.nodes[0].binders.len(), 2);
    assert_eq!(tree.nodes[1].binders.len(), 2);
    assert_eq!(tree.nodes[1].kind, Kind::Exists);
    assert_eq!(tree.nodes[1].depth, 2);
    let mut parent_ce = tree.nodes[0].ce_vars.clone();
    parent_ce.sort();
    assert_eq!(tree.nodes[1].env, parent_ce);
    assert!(tree.nodes[0].children[0].pol.pos && !tree.nodes[0].children[0].pol.neg);
}

/// A quantifier under `not`, under `=>` and under an iff gets the right
/// occurrence polarity; a negated top universal is Skolemized away.
#[test]
fn polarity_is_tracked_through_connectives() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let p = terms.mk_var("p", Sort::Bool);
    let zero = real(&mut terms, 0);
    let zx = terms.mk_lt(z, x);
    let inner = terms.mk_forall(binder("z"), zx);
    // ∀x. (inner ⇒ x > 0) — inner occurs negatively.
    let pos = terms.mk_gt(x, zero);
    let imp = terms.mk_app(ay_core::Symbol::named("=>"), vec![inner, pos], Sort::Bool);
    let root = terms.mk_forall(binder("x"), imp);
    let tree = build_nested_tree(&mut terms, &[root]).expect("tree");
    let edge = tree.nodes[0].children[0];
    assert!(edge.pol.neg && !edge.pol.pos, "premise of => is negative");
    // (= p (∀x. x > 0)) at the top: both polarities, kept as a node.
    let gt = terms.mk_gt(x, zero);
    let q = terms.mk_forall(binder("x"), gt);
    let iff = terms.mk_app(ay_core::Symbol::named("="), vec![p, q], Sort::Bool);
    let tree = build_nested_tree(&mut terms, &[iff]).expect("tree");
    assert!(tree.nodes[0].top.expect("top").both());
    assert_eq!(tree.skolems, [] as [TermId; 0]);
    // (not (∀x. x > 0)) at the top: effectively existential, Skolemized.
    let neg = terms.mk_not(q);
    assert_eq!(
        build_nested_tree(&mut terms, &[neg]).err(),
        Some(NestedTreeDecline::NoQuantifier)
    );
}

/// An operator that is not a Boolean connective over a quantified argument
/// declines instead of guessing a polarity.
#[test]
fn non_connective_over_a_quantifier_declines() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let gt = terms.mk_gt(x, zero);
    let q = terms.mk_forall(binder("x"), gt);
    let weird = terms.mk_app(ay_core::Symbol::named("frob"), vec![q], Sort::Bool);
    assert_eq!(
        build_nested_tree(&mut terms, &[weird]).err(),
        Some(NestedTreeDecline::Connective)
    );
}
