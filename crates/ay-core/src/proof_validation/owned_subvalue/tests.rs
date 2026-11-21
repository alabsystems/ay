// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::BTreeMap;

fn registry() -> [OwnedSubvalueConstructor<'static>; 1] {
    [OwnedSubvalueConstructor {
        identity: "owned_r",
        carrier: "OwnedR",
    }]
}
fn run(
    terms: &TermStore,
    classes: &BTreeMap<TermId, u64>,
    values: &BTreeMap<TermId, bool>,
) -> Result<Option<OwnedSubvalueCycle>, OwnedSubvalueRefusal> {
    let universe: Vec<_> = (0..terms.len()).map(|id| TermId(id as u32)).collect();
    owned_subvalue_cycle_with_progress(
        terms,
        &registry(),
        &universe,
        &mut |id| {
            (
                classes.get(&id).copied().unwrap_or(u64::from(id.0)),
                values.get(&id).copied(),
            )
        },
        &mut OwnedSubvalueBudget::new(1 << 20, 8 << 20),
        &mut |_, _| true,
    )
}
fn carrier() -> Sort {
    Sort::Uninterpreted("OwnedR".into())
}
fn ctor(terms: &mut TermStore, sequence: TermId) -> TermId {
    terms.mk_app(Symbol::named("owned_r"), [sequence], carrier())
}

#[test]
fn owned_subvalue_unit_parent_cycle_requires_strict_datatype_edge() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let unit = terms.mk_app(Symbol::named("seq.unit"), [r], Sort::seq(carrier()));
    let parent = ctor(&mut terms, unit);
    let classes = BTreeMap::from([(parent, u64::from(r.0))]);
    let witness = run(&terms, &classes, &BTreeMap::new())
        .unwrap()
        .expect("genuine R contains unit(R)");
    assert_eq!(witness.edges.len(), 2);
    assert!(matches!(
        witness.edges[0].kind,
        OwnedSubvalueEdgeKind::DatatypeField { index: 0 }
    ));
    assert!(matches!(
        witness.edges[1].kind,
        OwnedSubvalueEdgeKind::SequenceUnit
    ));
    assert_eq!(witness.edges[0].container, parent);
    assert_eq!(witness.edges[1].content, r);
    let mut owner = OwnedSubvalueBudget::new(1 << 20, 8 << 20);
    let universe: Vec<_> = (0..terms.len()).map(|id| TermId(id as u32)).collect();
    assert!(owned_subvalue_cycle_with_progress(
        &terms,
        &[],
        &universe,
        &mut |id| (classes.get(&id).copied().unwrap_or(u64::from(id.0)), None),
        &mut owner,
        &mut |_, _| true
    )
    .unwrap()
    .is_none());
}

#[test]
fn owned_subvalue_empty_leaf_and_finite_nesting_have_no_cycle() {
    let mut terms = TermStore::new();
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], Sort::seq(carrier()));
    let leaf = ctor(&mut terms, empty);
    let children = terms.mk_app(Symbol::named("seq.unit"), [leaf], Sort::seq(carrier()));
    let _parent = ctor(&mut terms, children);
    assert!(run(&terms, &BTreeMap::new(), &BTreeMap::new())
        .unwrap()
        .is_none());
}

#[test]
fn owned_subvalue_concat_identity_is_not_strict_descent() {
    let mut terms = TermStore::new();
    let sequence = terms.mk_var("s", Sort::seq(carrier()));
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], Sort::seq(carrier()));
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        [sequence, empty],
        Sort::seq(carrier()),
    );
    let _value = ctor(&mut terms, concat);
    let classes = BTreeMap::from([(concat, u64::from(sequence.0))]);
    assert!(run(&terms, &classes, &BTreeMap::new()).unwrap().is_none());
}

fn guarded_cycle() -> (TermStore, BTreeMap<TermId, u64>, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let r = terms.mk_var("guarded_r", carrier());
    let sequence = terms.mk_var("children", Sort::seq(carrier()));
    let index = terms.mk_var("index", Sort::Int);
    let parent = ctor(&mut terms, sequence);
    let nth = terms.mk_app(Symbol::named("seq.nth"), [sequence, index], carrier());
    let zero = terms.mk_int(0.into());
    let len = terms.mk_app(Symbol::named("seq.len"), [sequence], Sort::Int);
    let lower = terms.mk_app(Symbol::named("<="), [zero, index], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("<"), [index, len], Sort::Bool);
    (
        terms,
        BTreeMap::from([(parent, u64::from(r.0)), (nth, u64::from(r.0))]),
        lower,
        upper,
        sequence,
    )
}

#[test]
fn owned_subvalue_nth_cycle_retains_both_actual_guards() {
    let (terms, classes, lower, upper, _) = guarded_cycle();
    let values = BTreeMap::from([(lower, true), (upper, true)]);
    let witness = run(&terms, &classes, &values)
        .unwrap()
        .expect("guarded owned cycle");
    assert!(witness.edges.iter().any(|edge|matches!(edge.kind,OwnedSubvalueEdgeKind::SequenceNth { lower:Some(a),upper:b } if a==TheoryLit::new(lower,true)&&b==TheoryLit::new(upper,true))));
    for values in [
        BTreeMap::from([(upper, true)]),
        BTreeMap::from([(lower, true)]),
        BTreeMap::from([(lower, true), (upper, false)]),
    ] {
        assert!(
            run(&terms, &classes, &values).unwrap().is_none(),
            "missing/OOB guard is not membership"
        );
    }
}

#[test]
fn owned_subvalue_nth_wrong_sequence_guard_and_wrong_unit_sort_refuse() {
    let (mut terms, classes, lower, _, _) = guarded_cycle();
    let other = terms.mk_var("wrong_children", Sort::seq(carrier()));
    let index = terms.mk_var("index", Sort::Int);
    let wrong_len = terms.mk_app(Symbol::named("seq.len"), [other], Sort::Int);
    let wrong_upper = terms.mk_app(Symbol::named("<"), [index, wrong_len], Sort::Bool);
    assert!(run(
        &terms,
        &classes,
        &BTreeMap::from([(lower, true), (wrong_upper, true)])
    )
    .unwrap()
    .is_none());
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let forged = terms.mk_app(Symbol::named("seq.unit"), [r], Sort::seq(Sort::Int));
    let parent = ctor(&mut terms, forged);
    assert!(run(
        &terms,
        &BTreeMap::from([(parent, u64::from(r.0))]),
        &BTreeMap::new()
    )
    .unwrap()
    .is_none());
}

#[test]
fn owned_subvalue_invalid_handles_and_sticky_limit_do_not_return_witnesses() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let unit = terms.mk_app(Symbol::named("seq.unit"), [r], Sort::seq(carrier()));
    let parent = ctor(&mut terms, unit);
    let classes = BTreeMap::from([(parent, u64::from(r.0))]);
    let universe: Vec<_> = (0..terms.len()).map(|id| TermId(id as u32)).collect();
    let mut owner = OwnedSubvalueBudget::new(0, 1 << 20);
    for _ in 0..2 {
        assert_eq!(
            owned_subvalue_cycle_with_progress(
                &terms,
                &registry(),
                &universe,
                &mut |id| (classes.get(&id).copied().unwrap_or(u64::from(id.0)), None),
                &mut owner,
                &mut |_, _| true
            )
            .err(),
            Some(OwnedSubvalueRefusal::Limit)
        );
    }
    let mut owner = OwnedSubvalueBudget::new(1 << 20, 8 << 20);
    assert_eq!(
        owned_subvalue_cycle_with_progress(
            &terms,
            &registry(),
            &[TermId(u32::MAX)],
            &mut |_| panic!("invalid source must precede callback"),
            &mut owner,
            &mut |_, _| true
        )
        .err(),
        Some(OwnedSubvalueRefusal::InvalidSource)
    );
    let mut owner = OwnedSubvalueBudget::new(1 << 20, 8 << 20);
    assert_eq!(
        owned_subvalue_cycle_with_progress(
            &terms,
            &registry(),
            &universe,
            &mut |id| (u64::from(id.0), None),
            &mut owner,
            &mut |_, _| false
        )
        .err(),
        Some(OwnedSubvalueRefusal::Cancelled)
    );
    assert_eq!(owner.refusal(), Some(OwnedSubvalueRefusal::Cancelled));
}

#[test]
fn owned_subvalue_cross_sort_equality_classes_confer_no_cycle_authority() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let integer = terms.mk_var("integer", Sort::Int);
    let unit = terms.mk_app(Symbol::named("seq.unit"), [integer], Sort::seq(Sort::Int));
    let parent = ctor(&mut terms, unit);
    let classes = BTreeMap::from([(parent, u64::from(r.0)), (integer, u64::from(r.0))]);
    assert_eq!(
        run(&terms, &classes, &BTreeMap::new()).err(),
        Some(OwnedSubvalueRefusal::InvalidSource)
    );
}
