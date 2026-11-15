// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #8512-forced-or on Bool-element arrays, the shape model-checker-consumer's CHC encoding
//! emits for its `obj_valid` map:
//!
//! * a forced arm's `(= obj (store (const true) 66 true))` reaches the model
//!   as `(= obj (const true))`, because `mk_store` folds the no-op store, and
//!   that definition must lift the nested-only withholding just as a `store`
//!   definition does;
//! * an arm whose only refuting conjunct is a negated Bool-element `select`
//!   must count as dead, since the `select` is a SAT atom with no BV bits.
//!
//! Each case has a twin where the arm is NOT forced, and that twin must stay
//! withheld. A const-array whose default has no model value (a Bool-element
//! `select` at an index with no value) neither lifts nor poisons its variable.

use super::*;

const IDX: u8 = 0x42;

fn bv32(terms: &mut TermStore, value: u8) -> TermId {
    terms.mk_bitvec(BigInt::from(value), 32)
}

fn bool_array() -> Sort {
    Sort::array(Sort::bitvec(32), Sort::Bool)
}

fn model(values: &[(TermId, u8)], bools: &[(TermId, bool)]) -> BvModel {
    BvModel {
        values: values.iter().map(|&(t, v)| (t, BigInt::from(v))).collect(),
        term_to_bits: HashMap::default(),
        bool_overrides: bools.iter().copied().collect(),
    }
}

fn extract(terms: &TermStore, bv_model: &BvModel, assertion: TermId) -> ArrayModel {
    Executor::extract_array_model_from_bv_model(terms, bv_model, &[assertion], &Default::default())
}

/// `(= obj (store (const true) #x42 true))`, folded to a const-array definition.
fn folded_obj_definition(terms: &mut TermStore, obj: TermId) -> TermId {
    let tru = terms.mk_bool(true);
    let all_true = terms.mk_const_array(Sort::bitvec(32), tru);
    let idx = bv32(terms, IDX);
    let store = terms.mk_store(all_true, idx, tru);
    assert_eq!(store, all_true, "mk_store must fold the no-op store");
    terms.mk_eq_coerce_no_ite_expand(obj, store)
}

#[test]
fn forced_or_arm_const_array_definition_lifts_withholding() {
    let mut terms = TermStore::new();
    let obj = terms.mk_var("obj", bool_array());
    let p = terms.mk_var("p", Sort::bitvec(32));
    let def = folded_obj_definition(&mut terms, obj);
    let one = bv32(&mut terms, 1);
    let two = bv32(&mut terms, 2);
    let p_is_one = terms.mk_eq_coerce(p, one);
    let p_is_two = terms.mk_eq_coerce(p, two);
    let arm_live = terms.mk_and(vec![p_is_one, def]);
    let assertion = terms.mk_or(vec![arm_live, p_is_two]);

    // p = 1 falsifies the second arm, so the first is forced.
    let array_model = extract(&terms, &model(&[(p, 1)], &[]), assertion);

    assert!(
        !array_model.read_conflicted.contains(&obj),
        "a forced const-array definition must not stay withheld"
    );
    let interp = array_model
        .array_values
        .get(&obj)
        .expect("the forced definition gives obj an interpretation");
    assert_eq!(interp.default.as_deref(), Some("true"));
    assert!(
        interp.stores.iter().all(|(_, v)| v == "true"),
        "every cell of (const true) is true, got {:?}",
        interp.stores
    );
}

/// An unforced definition is not adopted, and no longer withholds `obj`
/// (`live_definitions.rs`): it keeps what its reads give it, none here.
#[test]
fn unforced_const_array_definition_is_not_adopted() {
    let mut terms = TermStore::new();
    let obj = terms.mk_var("obj", bool_array());
    let p = terms.mk_var("p", Sort::bitvec(32));
    let def = folded_obj_definition(&mut terms, obj);
    let two = bv32(&mut terms, 2);
    let p_is_two = terms.mk_eq_coerce(p, two);
    let assertion = terms.mk_or(vec![def, p_is_two]);

    // p = 2 makes the other arm true: both arms are live, nothing is forced.
    let array_model = extract(&terms, &model(&[(p, 2)], &[]), assertion);

    assert!(
        !array_model.read_conflicted.contains(&obj),
        "an unforced const-array definition does not withhold obj"
    );
    assert!(
        array_model
            .array_values
            .get(&obj)
            .is_none_or(|interp| interp.default.as_deref() != Some("true")),
        "the unforced definition must not have been adopted"
    );
}

/// `(or (not (select a #x42)) (= c (store (const false) #x42 true)))`.
fn negated_select_guard(terms: &mut TermStore) -> (TermId, TermId, TermId) {
    let a = terms.mk_var("a", bool_array());
    let c = terms.mk_var("c", bool_array());
    let idx = bv32(terms, IDX);
    let read = terms.mk_select(a, idx);
    let guard = terms.mk_not(read);
    let fls = terms.mk_bool(false);
    let tru = terms.mk_bool(true);
    let all_false = terms.mk_const_array(Sort::bitvec(32), fls);
    let store = terms.mk_store(all_false, idx, tru);
    let def = terms.mk_eq_coerce_no_ite_expand(c, store);
    (terms.mk_or(vec![guard, def]), read, c)
}

#[test]
fn negated_true_select_arm_forces_the_store_definition() {
    let mut terms = TermStore::new();
    let (assertion, read, c) = negated_select_guard(&mut terms);

    // The SAT model set the Bool-element read true, so `(not read)` is false.
    let array_model = extract(&terms, &model(&[], &[(read, true)]), assertion);

    assert!(
        !array_model.read_conflicted.contains(&c),
        "the negated true read is a dead arm, so c's definition is forced"
    );
    let interp = array_model
        .array_values
        .get(&c)
        .expect("the forced definition gives c an interpretation");
    assert_eq!(interp.default.as_deref(), Some("false"));
    assert_eq!(
        interp.stores,
        vec![("#x00000042".to_string(), "true".to_string())]
    );
}

#[test]
fn negated_false_or_unknown_select_arm_leaves_definition_unadopted() {
    // Without a value for the read, or with the read FALSE (`(not read)`
    // holds), both arms stay live: c's definition is not adopted, and c
    // keeps what its reads give it (none here) without being withheld.
    for read_value in [None, Some(false)] {
        let mut terms = TermStore::new();
        let (assertion, read, c) = negated_select_guard(&mut terms);
        let assigned: Vec<(TermId, bool)> = read_value.map(|v| (read, v)).into_iter().collect();
        let array_model = extract(&terms, &model(&[], &assigned), assertion);
        assert!(
            !array_model.read_conflicted.contains(&c),
            "a live guard arm does not withhold c ({assigned:?})"
        );
        assert!(
            !array_model.array_values.contains_key(&c),
            "with the guard arm live, c's definition must not be adopted ({assigned:?})"
        );
    }
}

/// `(= obj (const (select a i)))` with `i` unassigned: the read's index has no
/// value, so `const_array_interp` cannot resolve the default even when the
/// read itself carries a SAT value. (A read at an assigned index resolves
/// through `a`'s interpretation, `definition_operands.rs`.)
fn unresolvable_const_definition(terms: &mut TermStore, obj: TermId) -> (TermId, TermId) {
    let a = terms.mk_var("a", bool_array());
    let idx = terms.mk_var("i", Sort::bitvec(32));
    let read = terms.mk_select(a, idx);
    let all_read = terms.mk_const_array(Sort::bitvec(32), read);
    (terms.mk_eq_coerce_no_ite_expand(obj, all_read), read)
}

#[test]
fn forced_or_arm_unresolvable_const_array_default_publishes_nothing() {
    let mut terms = TermStore::new();
    let obj = terms.mk_var("obj", bool_array());
    let p = terms.mk_var("p", Sort::bitvec(32));
    let (def, read) = unresolvable_const_definition(&mut terms, obj);
    let one = bv32(&mut terms, 1);
    let two = bv32(&mut terms, 2);
    let p_is_one = terms.mk_eq_coerce(p, one);
    let p_is_two = terms.mk_eq_coerce(p, two);
    let arm_live = terms.mk_and(vec![p_is_one, def]);
    let assertion = terms.mk_or(vec![arm_live, p_is_two]);

    // The arm is forced, but the definition cannot be built: even with the
    // read assigned, nothing may publish a value for obj. An unbuilt
    // const-array neither lifts nor poisons, and a nested-only variable is
    // not withheld (`live_definitions.rs`), so obj is left without an entry
    // for the gate to find unpinned.
    let array_model = extract(&terms, &model(&[(p, 1)], &[(read, true)]), assertion);

    assert!(
        !array_model.array_values.contains_key(&obj),
        "an unbuilt forced const-array definition must publish nothing for obj"
    );
    assert!(!array_model.read_conflicted.contains(&obj));
}

#[test]
fn top_level_conjunct_unresolvable_const_array_default_does_not_poison() {
    let mut terms = TermStore::new();
    let obj = terms.mk_var("obj", bool_array());
    let p = terms.mk_var("p", Sort::bitvec(32));
    let (def, _) = unresolvable_const_definition(&mut terms, obj);
    let one = bv32(&mut terms, 1);
    let p_is_one = terms.mk_eq_coerce(p, one);
    let assertion = terms.mk_and(vec![p_is_one, def]);

    // A top-level conjunct was never withheld; failing to build it must not
    // start withholding it now (the gate judges whatever entry obj has).
    let array_model = extract(&terms, &model(&[(p, 1)], &[]), assertion);

    assert!(
        !array_model.read_conflicted.contains(&obj),
        "an unbuilt const-array default must not poison a top-level conjunct"
    );
}
