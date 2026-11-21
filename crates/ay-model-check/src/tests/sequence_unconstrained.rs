// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn sequence_unconstrained_read_uses_exact_negative_and_large_out_of_bounds_values() {
    for index in [int(-1), int(0), BigInt::from(1) << 256usize] {
        let mut terms = TermStore::new();
        let empty = app(&mut terms, "seq.empty", &[], Sort::seq(Sort::Int));
        let index = terms.mk_int(index);
        let read = app(&mut terms, "seq.nth", &[empty, index], Sort::Int);
        let seven = terms.mk_int(int(7));
        let root = terms.mk_eq(read, seven);
        let model = UfStubModel::new().unconstrained(
            read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Int(int(7)),
        );
        assert_confirmed(&verdict(&terms, &model, &[root]));
        assert_eq!(model.unconstrained_calls.get(), 1);
        assert_cannot(&verdict(&terms, &StubModel::new(), &[root]));
    }
}

#[test]
fn sequence_unconstrained_read_never_adopts_an_in_bounds_pin() {
    let mut terms = TermStore::new();
    let one = terms.mk_int(int(1));
    let seven = terms.mk_int(int(7));
    let zero = terms.mk_int(int(0));
    let unit = app(&mut terms, "seq.unit", &[one], Sort::seq(Sort::Int));
    let read = app(&mut terms, "seq.nth", &[unit, zero], Sort::Int);
    let wrong = terms.mk_eq(read, seven);
    let correct = terms.mk_eq(read, one);
    let model = UfStubModel::new()
        .uf(read, ModelValue::Int(int(7)))
        .unconstrained(
            read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Int(int(7)),
        );
    assert_violates(&verdict(&terms, &model, &[wrong]));
    assert_confirmed(&verdict(&terms, &model, &[correct]));
    assert_eq!(model.unconstrained_calls.get(), 0);
}

#[test]
fn sequence_unconstrained_read_is_value_keyed_across_sequence_and_index_aliases() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::seq(Sort::Int));
    let t = terms.mk_var("t", Sort::seq(Sort::Int));
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let left = app(&mut terms, "seq.nth", &[s, i], Sort::Int);
    let right = app(&mut terms, "seq.nth", &[t, j], Sort::Int);
    let one = terms.mk_int(int(1));
    let two = terms.mk_int(int(2));
    let a = terms.mk_eq(left, one);
    let b = terms.mk_eq(right, two);
    let model = UfStubModel::new()
        .leaf(s, ModelValue::Seq(vec![]))
        .leaf(t, ModelValue::Seq(vec![]))
        .leaf(i, ModelValue::Int(int(5)))
        .leaf(j, ModelValue::Int(int(5)))
        .uf(left, ModelValue::Int(int(1)))
        .uf(right, ModelValue::Int(int(2)));
    assert_violates(&verdict(&terms, &model, &[a, b]));
    assert_violates(&verdict(&terms, &model, &[b, a]));
    let independent = UfStubModel::new()
        .leaf(s, ModelValue::Seq(vec![]))
        .leaf(t, ModelValue::Seq(vec![ModelValue::Int(int(8))]))
        .leaf(i, ModelValue::Int(int(5)))
        .leaf(j, ModelValue::Int(int(5)))
        .uf(left, ModelValue::Int(int(1)))
        .uf(right, ModelValue::Int(int(2)));
    assert_confirmed(&verdict(&terms, &independent, &[a, b]));
}

#[test]
fn sequence_unconstrained_read_separates_actual_polymorphic_instances() {
    let mut terms = TermStore::new();
    let integers = app(&mut terms, "seq.empty", &[], Sort::seq(Sort::Int));
    let booleans = app(&mut terms, "seq.empty", &[], Sort::seq(Sort::Bool));
    let zero = terms.mk_int(int(0));
    let int_read = app(&mut terms, "seq.nth", &[integers, zero], Sort::Int);
    let bool_read = app(&mut terms, "seq.nth", &[booleans, zero], Sort::Bool);
    let seven = terms.mk_int(int(7));
    let expected = terms.mk_eq(int_read, seven);
    let model = UfStubModel::new()
        .unconstrained(
            int_read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Int(int(7)),
        )
        .unconstrained(
            bool_read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Bool(true),
        );
    assert_confirmed(&verdict(&terms, &model, &[expected, bool_read]));
}

#[test]
fn sequence_unconstrained_read_validates_the_actual_datatype_element_sort() {
    let mut terms = TermStore::new();
    let element = Sort::Datatype(DatatypeSort::new(
        "ReadR",
        vec![DatatypeConstructor::new(
            "read_node",
            vec![DatatypeField::new(
                "read_children",
                Sort::seq(Sort::Uninterpreted("ReadR".into())),
            )],
        )],
    ));
    let empty = app(&mut terms, "seq.empty", &[], Sort::seq(element.clone()));
    let zero = terms.mk_int(int(0));
    let read = app(&mut terms, "seq.nth", &[empty, zero], element.clone());
    let children = app(
        &mut terms,
        "seq.empty",
        &[],
        Sort::seq(Sort::Uninterpreted("ReadR".into())),
    );
    let leaf = app(&mut terms, "read_node", &[children], element);
    let equality = terms.mk_eq(read, leaf);
    let value = ModelValue::Datatype {
        ctor: "read_node".into(),
        args: vec![ModelValue::Seq(vec![])],
    };
    assert_confirmed(&verdict(
        &terms,
        &UfStubModel::new().unconstrained(read, ProvenUnconstrainedKind::SeqNthOutOfBounds, value),
        &[equality],
    ));
    assert_cannot(&verdict(
        &terms,
        &UfStubModel::new().unconstrained(
            read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Bool(true),
        ),
        &[equality],
    ));
}

#[test]
fn sequence_unconstrained_read_refuses_missing_inputs_wrong_signature_and_legacy_authority() {
    let mut terms = TermStore::new();
    let empty = app(&mut terms, "seq.empty", &[], Sort::seq(Sort::Int));
    let index = terms.mk_var("missing_index", Sort::Int);
    let zero = terms.mk_int(int(0));
    let read = app(&mut terms, "seq.nth", &[empty, index], Sort::Int);
    let bad = app(&mut terms, "seq.nth", &[empty, zero], Sort::Bool);
    let seven = terms.mk_int(int(7));
    let equality = terms.mk_eq(read, seven);
    assert_cannot(&verdict(
        &terms,
        &UfStubModel::new().unconstrained(
            read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Int(int(7)),
        ),
        &[equality],
    ));
    assert_cannot(&verdict(
        &terms,
        &UfStubModel::new().unconstrained(
            bad,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Bool(true),
        ),
        &[bad],
    ));
    let read = app(&mut terms, "seq.nth", &[empty, zero], Sort::Int);
    let equality = terms.mk_eq(read, seven);
    assert_cannot(&verdict(
        &terms,
        &LegacyUnconstrainedModel::new().unconstrained(read, ModelValue::Int(int(7))),
        &[equality],
    ));
}

#[test]
fn sequence_unconstrained_read_does_not_adopt_one_pin_for_multiple_bound_instances() {
    let mut terms = TermStore::new();
    let guard = terms.mk_var("nth_guard", Sort::Bool);
    let zero = terms.mk_int(int(0));
    let one = terms.mk_int(int(1));
    let seven = terms.mk_int(int(7));
    let index = terms.mk_ite(guard, zero, one);
    let empty = app(&mut terms, "seq.empty", &[], Sort::seq(Sort::Int));
    let read = app(&mut terms, "seq.nth", &[empty, index], Sort::Int);
    let body = terms.mk_eq(read, seven);
    let root = terms.mk_forall(vec![("nth_guard".into(), Sort::Bool)], body);
    let model = UfStubModel::new()
        .uf(read, ModelValue::Int(int(7)))
        .unconstrained(
            read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Int(int(7)),
        );
    assert_cannot(&verdict(&terms, &model, &[root]));
    assert_eq!(model.unconstrained_calls.get(), 0);
}

#[test]
fn sequence_unconstrained_read_preserves_committed_priority_and_bounded_type_payload() {
    let mut terms = TermStore::new();
    let empty = app(&mut terms, "seq.empty", &[], Sort::seq(Sort::Int));
    let zero = terms.mk_int(int(0));
    let seven = terms.mk_int(int(7));
    let read = app(&mut terms, "seq.nth", &[empty, zero], Sort::Int);
    let equality = terms.mk_eq(read, seven);
    let model = UfStubModel::new()
        .uf(read, ModelValue::Bool(true))
        .unconstrained(
            read,
            ProvenUnconstrainedKind::SeqNthOutOfBounds,
            ModelValue::Int(int(7)),
        );
    assert_cannot(&verdict(&terms, &model, &[equality]));
    assert_eq!(
        model.unconstrained_calls.get(),
        0,
        "a bad committed value is not replaced with the asserted wish"
    );

    let mut deep = Sort::Int;
    for _ in 0..80 {
        deep = Sort::seq(deep);
    }
    let sequence = app(&mut terms, "seq.empty", &[], Sort::seq(deep.clone()));
    let read = app(&mut terms, "seq.nth", &[sequence, zero], deep.clone());
    let wanted = app(&mut terms, "seq.empty", &[], deep);
    let equality = terms.mk_eq(read, wanted);
    let model = UfStubModel::new().unconstrained(
        read,
        ProvenUnconstrainedKind::SeqNthOutOfBounds,
        ModelValue::Seq(vec![]),
    );
    assert_cannot(&verdict(&terms, &model, &[equality]));
    assert_eq!(
        model.unconstrained_calls.get(),
        0,
        "raw sort admission precedes model completion"
    );
}
