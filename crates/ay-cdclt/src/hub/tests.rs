// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The hub alone: congruence, values, explanations, undo and re-attachment.

use ay_core::{TermId, TheoryLit};

use super::{Hub, HubEvent, NodeId};
use crate::plugin::ThVar;

fn t(i: u32) -> TermId {
    TermId(i)
}

/// A hub with leaves a, b, c, d (terms 10..13), `f(a)`..`f(d)` (terms
/// 20..23) and the atoms `a = b` (30), `b = c` (31), `f(a) = f(c)` (32).
struct Fixture {
    hub: Hub,
    leaf: [NodeId; 4],
    fx: [NodeId; 4],
    ab: NodeId,
    bc: NodeId,
    fafc: NodeId,
}

fn fixture() -> Fixture {
    let mut hub = Hub::sparse(t(0), t(1));
    let leaf = [0, 1, 2, 3].map(|i| hub.add_leaf(t(10 + i), false, None));
    let f = hub.func_id("f", 1, &ay_core::Sort::Uninterpreted("U".to_string()));
    let fx = [0, 1, 2, 3].map(|i| hub.add_app(t(20 + i), f, vec![leaf[i as usize]], false));
    let ab = hub.add_eq(t(30), leaf[0], leaf[1]);
    let bc = hub.add_eq(t(31), leaf[1], leaf[2]);
    let fafc = hub.add_eq(t(32), fx[0], fx[2]);
    hub.propagate();
    Fixture {
        hub,
        leaf,
        fx,
        ab,
        bc,
        fafc,
    }
}

#[test]
fn congruence_follows_argument_merges_and_is_explained() {
    let mut fx = fixture();
    let hub = &mut fx.hub;
    hub.push_scope();
    hub.assign(fx.ab, true);
    hub.propagate();
    hub.push_scope();
    hub.assign(fx.bc, true);
    hub.propagate();
    assert!(hub.take_conflict().is_none());
    assert_eq!(
        hub.root(fx.fx[0]),
        hub.root(fx.fx[2]),
        "f(a) = f(c) by congruence"
    );
    assert_ne!(hub.root(fx.fx[0]), hub.root(fx.fx[3]));
    let why = hub.explain(fx.fx[0], fx.fx[2]).expect("same class");
    assert_eq!(
        why,
        vec![TheoryLit::new(t(30), true), TheoryLit::new(t(31), true)]
    );
    // The equality atom f(a) = f(c) is now true: it is propagated.
    let props = hub.take_props();
    assert!(props.iter().any(|&(n, _)| n == fx.fafc), "{props:?}");
    // Pop the second scope: b = c and everything it caused is undone.
    hub.pop_scopes(1);
    assert_ne!(hub.root(fx.fx[0]), hub.root(fx.fx[2]));
    assert_eq!(hub.root(fx.leaf[0]), hub.root(fx.leaf[1]));
    hub.pop_scopes(1);
    assert_ne!(hub.root(fx.leaf[0]), hub.root(fx.leaf[1]));
}

#[test]
fn a_false_equality_between_merged_terms_is_a_conflict() {
    let mut fx = fixture();
    let hub = &mut fx.hub;
    hub.push_scope();
    hub.assign(fx.fafc, false);
    hub.assign(fx.ab, true);
    hub.assign(fx.bc, true);
    hub.propagate();
    let conflict = hub
        .take_conflict()
        .expect("f(a) = f(c) is false and forced");
    let why = hub.explain(conflict.a, conflict.b).expect("same class");
    assert_eq!(
        why,
        vec![
            TheoryLit::new(t(30), true),
            TheoryLit::new(t(31), true),
            TheoryLit::new(t(32), false)
        ]
    );
    hub.pop_scopes(1);
    hub.propagate();
    assert!(hub.take_conflict().is_none());
}

#[test]
fn numerals_of_different_value_clash_and_equal_values_do_not() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let mut hub = Hub::sparse(t(0), t(1));
    let q = |n: i64| {
        Some(super::HubValue::Num(BigRational::from_integer(
            BigInt::from(n),
        )))
    };
    let one_int = hub.add_leaf(t(10), false, q(1));
    let one_real = hub.add_leaf(t(11), false, q(1));
    let two = hub.add_leaf(t(12), false, q(2));
    let x = hub.add_leaf(t(13), false, None);
    let x1 = hub.add_eq(t(20), x, one_int);
    let x1r = hub.add_eq(t(21), x, one_real);
    let x2 = hub.add_eq(t(22), x, two);
    hub.push_scope();
    hub.assign(x1, true);
    hub.assign(x1r, true);
    hub.propagate();
    assert!(
        hub.take_conflict().is_none(),
        "Int 1 and Real 1 are one value"
    );
    hub.assign(x2, true);
    hub.propagate();
    let c = hub.take_conflict().expect("1 = 2 through x");
    let why = hub.explain(c.a, c.b).expect("same class");
    assert!(why.contains(&TheoryLit::new(t(22), true)), "{why:?}");
}

#[test]
fn theory_variables_raise_new_eq_once_per_merge() {
    let mut fx = fixture();
    let hub = &mut fx.hub;
    hub.attach_var(fx.leaf[0], 0, ThVar(0));
    hub.attach_var(fx.leaf[1], 0, ThVar(1));
    hub.attach_var(fx.leaf[2], 0, ThVar(2));
    hub.push_scope();
    hub.assign(fx.ab, true);
    hub.propagate();
    let events = hub.take_events();
    assert_eq!(events.len(), 1, "{events:?}");
    assert!(matches!(events[0], HubEvent::NewEq { th: 0, .. }));
    hub.pop_scopes(1);
    hub.push_scope();
    hub.assign(fx.ab, true);
    hub.assign(fx.bc, true);
    hub.propagate();
    assert_eq!(hub.take_events().len(), 2, "a~b then b~c: two new_eq");
}

#[test]
fn nodes_created_in_a_popped_scope_are_attached_again() {
    let mut fx = fixture();
    let hub = &mut fx.hub;
    hub.push_scope();
    hub.assign(fx.ab, true);
    hub.propagate();
    // Created while a ~ b: `f(a) = f(b)` starts true (EqTrue queued).
    let fafb = hub.add_eq(t(40), fx.fx[0], fx.fx[1]);
    hub.propagate();
    assert_eq!(hub.root(fafb), hub.root(0), "joins true");
    hub.pop_scopes(1);
    hub.propagate();
    assert_ne!(hub.root(fafb), hub.root(0), "no longer forced");
    // Still a live node: congruence reaches it at the lower level.
    hub.push_scope();
    hub.assign(fx.ab, true);
    hub.propagate();
    assert_eq!(hub.root(fafb), hub.root(0));
    let why = hub.explain(fafb, 0).expect("same class");
    assert_eq!(why, vec![TheoryLit::new(t(30), true)]);
}

#[test]
fn full_enode_mode_is_refused_and_sparse_is_the_default() {
    let refused = Hub::new(t(0), t(1), super::EnodeMode::Full);
    assert!(refused.is_err(), "Full is reserved for quantifiers (KC24)");
    let hub = Hub::new(t(0), t(1), super::EnodeMode::Sparse).expect("Sparse is implemented");
    assert_eq!(hub.mode(), super::EnodeMode::Sparse);
}

/// The reserved enode fields (§3.3): generation, the relevancy bit, the
/// label sets and the parent lists per (symbol, argument), across merges
/// and pops.
#[test]
fn reserved_enode_fields_follow_merges_and_pops() {
    let u = ay_core::Sort::Uninterpreted("U".to_string());
    let mut hub = Hub::sparse(t(0), t(1));
    let a = hub.add_leaf(t(10), false, None);
    let b = hub.add_leaf(t(11), false, None);
    let f = hub.func_id("f", 1, &u);
    let g = hub.func_id("g", 2, &u);
    let fa = hub.add_app(t(20), f, vec![a], false);
    let gab = hub.add_app(t(21), g, vec![a, b], false);
    let gba = hub.add_app(t(22), g, vec![b, a], false);
    let ab = hub.add_eq(t(30), a, b);
    hub.propagate();
    assert_eq!(hub.generation(fa), 0, "input terms are generation 0");
    // Parents of a's class: f at 0, g at 0 (g(a,b)) and g at 1 (g(b,a)).
    let at = |hub: &Hub, n, func, arg| {
        let mut v: Vec<NodeId> = hub.parents_at(n, func, arg).collect();
        v.sort_unstable();
        v
    };
    assert_eq!(at(&hub, a, f, 0), vec![fa]);
    assert_eq!(at(&hub, a, g, 0), vec![gab]);
    assert_eq!(at(&hub, a, g, 1), vec![gba]);
    assert_eq!(at(&hub, b, f, 0), Vec::<NodeId>::new());
    let (lbls_fa, _) = hub.labels(fa);
    let (_, plbls_b) = hub.labels(b);
    hub.push_scope();
    hub.set_relevant(fa);
    hub.assign(ab, true);
    hub.propagate();
    assert!(hub.is_relevant(fa));
    // a ~ b: the class's parents at each (symbol, position) are the union,
    // and g(a,b) ~ g(b,a) by congruence.
    assert_eq!(at(&hub, b, g, 0), {
        let mut v = vec![gab, gba];
        v.sort_unstable();
        v
    });
    assert_eq!(at(&hub, b, f, 0), vec![fa]);
    assert_eq!(hub.root(gab), hub.root(gba));
    let (_, plbls_merged) = hub.labels(a);
    assert_eq!(plbls_merged & plbls_b, plbls_b, "parent labels are a union");
    hub.pop_scopes(1);
    assert!(!hub.is_relevant(fa), "the relevancy bit is undone");
    assert_eq!(at(&hub, b, f, 0), Vec::<NodeId>::new());
    assert_eq!(at(&hub, a, g, 1), vec![gba]);
    assert_eq!(hub.labels(fa).0, lbls_fa);
    assert_eq!(hub.labels(b).1, plbls_b, "label sets are undone");
}

/// Equalities are congruent up to the order of their sides: with `a ≠ b`
/// asserted, `c = a` and `d = b` make `(= d c)` false, explained by all
/// three literals.
#[test]
fn equalities_are_commutatively_congruent() {
    let mut hub = Hub::sparse(t(0), t(1));
    let [a, b, c, d] = [10, 11, 12, 13].map(|i| hub.add_leaf(t(i), false, None));
    let ab = hub.add_eq(t(20), a, b);
    let ca = hub.add_eq(t(21), c, a);
    let db = hub.add_eq(t(22), d, b);
    let dc = hub.add_eq(t(23), d, c);
    hub.propagate();
    hub.push_scope();
    hub.assign(ab, false);
    hub.assign(ca, true);
    hub.assign(db, true);
    hub.propagate();
    assert!(hub.take_conflict().is_none());
    assert_eq!(hub.root(dc), hub.root(1), "(= d c) joins false");
    let props = hub.take_props();
    assert!(props.iter().any(|&(n, _)| n == dc), "{props:?}");
    let why = hub.explain(dc, 1).expect("same class");
    assert_eq!(
        why,
        vec![
            TheoryLit::new(t(20), false),
            TheoryLit::new(t(21), true),
            TheoryLit::new(t(22), true)
        ]
    );
    hub.pop_scopes(1);
    assert_ne!(hub.root(dc), hub.root(1));
}

/// A crosswise congruence of equalities is explained by the pairing found
/// when it was found, never by one that newer merges make possible (a lazy
/// reason must use only literals assigned before the literal it explains).
#[test]
fn crossed_equality_congruence_keeps_its_pairing() {
    let mut hub = Hub::sparse(t(0), t(1));
    let [a, b, c, d] = [10, 11, 12, 13].map(|i| hub.add_leaf(t(i), false, None));
    let ab = hub.add_eq(t(20), a, b);
    let cd = hub.add_eq(t(21), c, d);
    let ad = hub.add_eq(t(22), a, d);
    let bc = hub.add_eq(t(23), b, c);
    let ac = hub.add_eq(t(24), a, c);
    hub.propagate();
    hub.push_scope();
    hub.assign(ad, true);
    hub.assign(bc, true);
    hub.propagate();
    assert_eq!(hub.root(ab), hub.root(cd), "(= a b) ~ (= c d) crosswise");
    hub.push_scope();
    hub.assign(ac, true);
    hub.propagate();
    let why = hub.explain(ab, cd).expect("same class");
    assert_eq!(
        why,
        vec![TheoryLit::new(t(22), true), TheoryLit::new(t(23), true)],
        "the newer a = c is not part of the reason"
    );
}

/// KC9: an explanation lists its literals in the order of their nodes (the
/// canonical order nodes are created in), not in `TermId` order: here the
/// equality created first has the larger `TermId`.
#[test]
fn explanations_follow_node_order_not_term_ids() {
    let mut hub = Hub::sparse(t(0), t(1));
    let [a, b, c] = [0, 1, 2].map(|i| hub.add_leaf(t(10 + i), false, None));
    let ab = hub.add_eq(t(50), a, b);
    let bc = hub.add_eq(t(40), b, c);
    hub.propagate();
    hub.push_scope();
    hub.assign(bc, true);
    hub.assign(ab, true);
    hub.propagate();
    let why = hub.explain(a, c).expect("same class");
    assert_eq!(
        why,
        vec![TheoryLit::new(t(50), true), TheoryLit::new(t(40), true)]
    );
}
