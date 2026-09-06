// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn residual_free_dt_array_alias_with_consistent_reads_confirms() {
    // Free a, b : (Array Int S); (= a b); f(a[0]) = 5, g(b[0]) = 7,
    // f(b[0]) = 5 (duplicate, consistent), f(a[1]) = 6 (distinct index).
    // Jointly satisfiable: a = b = [0 -> mk(5,7), 1 -> mk(6,_)] extends the
    // partial model, so the gate must CONFIRM instead of failing closed.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let i1 = ts.mk_int(int(1));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let c7 = ts.mk_int(int(7));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "g", b, i0, c7);
    let r3 = field_read_eq(&mut ts, "f", b, i0, c5);
    let r4 = field_read_eq(&mut ts, "f", a, i1, c6);
    let m = StubModel::new();
    assert_confirmed(&verdict(&ts, &m, &[alias, r1, r2, r3, r4]));
}

#[test]
fn residual_free_dt_array_bv64_alias_with_consistent_reads_confirms() {
    // MODEL_CHECKER_CONSUMER models Rust memory/Vec indices as BV64. Exercise that exact
    // carrier (including the high-bit range) rather than relying on the Int
    // control above: a = b and matching field requirements at one BV64 cell
    // admit a concrete finite-store witness and residual-disabled replay.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::bitvec(64), struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let index = ts.mk_bitvec(BigInt::from(0x8000_0000_0000_0001u64), 64);
    let c5 = ts.mk_int(int(5));
    let c7 = ts.mk_int(int(7));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, index, c5);
    let r2 = field_read_eq(&mut ts, "f", b, index, c5);
    let r3 = field_read_eq(&mut ts, "g", b, index, c7);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[alias, r1, r2, r3]));
}

#[test]
fn residual_free_dt_array_bool_indices_with_consistent_reads_confirms() {
    let mut ts = TermStore::new();
    let array = ts.mk_var("a", Sort::array(Sort::Bool, struct_sort()));
    let false_index = ts.mk_bool(false);
    let true_index = ts.mk_bool(true);
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let at_false = field_read_eq(&mut ts, "f", array, false_index, five);
    let at_true = field_read_eq(&mut ts, "f", array, true_index, six);

    assert_confirmed(&verdict(&ts, &StubModel::new(), &[at_false, at_true]));
}

#[test]
fn residual_free_dt_array_alias_only_materializes_and_replays() {
    // Even with no explicit store cells, the residual proof must construct a
    // real array value for the class and replay the alias equality. Both leaves
    // receive the SAME canonical default array, so the equality confirms.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[alias]));
}

#[test]
fn residual_field_witness_selects_a_fitting_constructor() {
    // The canonical DEFAULT may use `empty`, but the explicit cell constrained
    // through selector `f` must use `full` and synthesize only its unconstrained
    // `g` field. The fresh replay projects `f(full(5, 0))` and confirms it.
    let mut ts = TermStore::new();
    let datatype = Sort::Datatype(DatatypeSort::new(
        "Choice",
        vec![
            DatatypeConstructor::unit("empty"),
            DatatypeConstructor::new(
                "full",
                vec![
                    DatatypeField::new("f", Sort::Int),
                    DatatypeField::new("g", Sort::Int),
                ],
            ),
        ],
    ));
    let array = ts.mk_var("a", Sort::array(Sort::Int, datatype.clone()));
    let index = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let select = app(&mut ts, "select", &[array, index], datatype);
    let field = app(&mut ts, "f", &[select], Sort::Int);
    let assertion = app(&mut ts, "=", &[field, five], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[assertion]));
}

#[test]
fn residual_witness_replay_rejects_malformed_whole_element() {
    // The residual consistency map alone sees one unopposed whole-element
    // requirement. It is NOT enough: the model value names `mk` with the wrong
    // arity. Materialization followed by the ordinary typed replay must refuse
    // it instead of turning this malformed commitment into ConfirmedSat.
    let mut ts = TermStore::new();
    let datatype = struct_sort();
    let array = ts.mk_var("a", Sort::array(Sort::Int, datatype.clone()));
    let bad = ts.mk_var("bad", datatype.clone());
    let index = ts.mk_int(int(0));
    let select = app(&mut ts, "select", &[array, index], datatype);
    let assertion = app(&mut ts, "=", &[select, bad], Sort::Bool);
    let model = StubModel::new().with(
        bad,
        ModelValue::Datatype {
            ctor: "mk".to_string(),
            args: vec![ModelValue::Int(int(1))],
        },
    );
    assert_cannot(&verdict(&ts, &model, &[assertion]));
}

#[test]
fn residual_rejects_selector_result_sort_mismatch() {
    let mut ts = TermStore::new();
    let datatype = struct_sort();
    let array = ts.mk_var("a", Sort::array(Sort::Int, datatype.clone()));
    let index = ts.mk_int(int(0));
    let selected = app(&mut ts, "select", &[array, index], datatype);
    let malformed_field = app(&mut ts, "f", &[selected], Sort::Bool);
    let false_value = ts.mk_bool(false);
    let assertion = app(&mut ts, "=", &[malformed_field, false_value], Sort::Bool);

    assert_cannot(&verdict(&ts, &StubModel::new(), &[assertion]));
}

#[test]
fn residual_rejects_ambiguous_selector_metadata() {
    let mut ts = TermStore::new();
    let datatype = Sort::Datatype(DatatypeSort::new(
        "Ambiguous",
        vec![
            DatatypeConstructor::new("left", vec![DatatypeField::new("value", Sort::Int)]),
            DatatypeConstructor::new("right", vec![DatatypeField::new("value", Sort::Int)]),
        ],
    ));
    let array = ts.mk_var("a", Sort::array(Sort::Int, datatype.clone()));
    let index = ts.mk_int(int(0));
    let selected = app(&mut ts, "select", &[array, index], datatype);
    let ambiguous_field = app(&mut ts, "value", &[selected], Sort::Int);
    let zero = ts.mk_int(int(0));
    let assertion = app(&mut ts, "=", &[ambiguous_field, zero], Sort::Bool);

    assert_cannot(&verdict(&ts, &StubModel::new(), &[assertion]));
}

#[test]
fn residual_rejects_wrong_shape_bool_indices_before_witness_grouping() {
    // Three different field values force the three indices to be pairwise
    // distinct, which is impossible in Bool's two-element carrier. A malformed
    // model used to launder that contradiction by publishing three distinct
    // opaque tokens for the Bool leaves; the finite-store replay then treated
    // those tokens as three keys. Source-sort authentication must refuse the
    // malformed indices before they acquire witness authority.
    let mut ts = TermStore::new();
    let array = ts.mk_var("a", Sort::array(Sort::Bool, struct_sort()));
    let first_index = ts.mk_var("i0", Sort::Bool);
    let second_index = ts.mk_var("i1", Sort::Bool);
    let third_index = ts.mk_var("i2", Sort::Bool);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let two = ts.mk_int(int(2));
    let first = field_read_eq(&mut ts, "f", array, first_index, zero);
    let second = field_read_eq(&mut ts, "f", array, second_index, one);
    let third = field_read_eq(&mut ts, "f", array, third_index, two);
    let model = StubModel::new()
        .with(
            first_index,
            ModelValue::Uninterpreted("@malformed-bool-0".to_string()),
        )
        .with(
            second_index,
            ModelValue::Uninterpreted("@malformed-bool-1".to_string()),
        )
        .with(
            third_index,
            ModelValue::Uninterpreted("@malformed-bool-2".to_string()),
        );

    assert_cannot(&verdict(&ts, &model, &[first, second, third]));
}

#[test]
fn residual_witness_entry_budget_fails_closed() {
    // A satisfiable family just beyond the documented hard entry cap must be
    // rejected wholesale, never truncated to a partial finite-store witness.
    let mut ts = TermStore::new();
    let array = ts.mk_var("a", Sort::array(Sort::Int, struct_sort()));
    let five = ts.mk_int(int(5));
    let mut assertions = Vec::new();
    for offset in 0..=residual::MAX_WITNESS_ENTRIES {
        let index = ts.mk_int(BigInt::from(offset));
        assertions.push(field_read_eq(&mut ts, "f", array, index, five));
    }
    assert_cannot(&verdict(&ts, &StubModel::new(), &assertions));
}

#[test]
fn residual_rejects_one_node_scalar_payload_beyond_witness_budget() {
    let mut ts = TermStore::new();
    let datatype = Sort::Datatype(DatatypeSort::new(
        "TextCell",
        vec![DatatypeConstructor::new(
            "text_cell",
            vec![DatatypeField::new("payload", Sort::String)],
        )],
    ));
    let array = ts.mk_var("a", Sort::array(Sort::Int, datatype.clone()));
    let index = ts.mk_int(int(0));
    let selected = app(&mut ts, "select", &[array, index], datatype);
    let payload = app(&mut ts, "payload", &[selected], Sort::String);
    let pinned = ts.mk_var("pinned", Sort::String);
    let assertion = app(&mut ts, "=", &[payload, pinned], Sort::Bool);
    let model = StubModel::new().with(
        pinned,
        ModelValue::Str("x".repeat(residual::MAX_WITNESS_VALUE_WORK)),
    );

    assert_cannot(&verdict(&ts, &model, &[assertion]));
}

#[test]
fn residual_classifier_depth_budget_fails_closed() {
    let mut ts = TermStore::new();
    let array = ts.mk_var("a", Sort::array(Sort::Int, struct_sort()));
    let index = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let mut at_limit = field_read_eq(&mut ts, "f", array, index, five);
    for _ in 0..residual::MAX_CLASSIFY_DEPTH {
        at_limit = app(&mut ts, "and", &[at_limit], Sort::Bool);
    }
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[at_limit]));

    let over_limit = app(&mut ts, "and", &[at_limit], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[over_limit]));
}

#[test]
fn residual_classifier_width_budget_fails_closed_before_argument_snapshot() {
    let mut ts = TermStore::new();
    let array = ts.mk_var("a", Sort::array(Sort::Int, struct_sort()));
    let index = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let residual = field_read_eq(&mut ts, "f", array, index, five);
    let arguments = vec![residual; residual::MAX_CLASSIFY_WORK];
    let over_limit = app(&mut ts, "and", &arguments, Sort::Bool);

    assert_cannot(&verdict(&ts, &StubModel::new(), &[over_limit]));
}

#[test]
fn residual_alias_edge_budget_fails_closed_without_truncation() {
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Int, struct_sort());
    let left = ts.mk_var("left", array_sort.clone());
    let right = ts.mk_var("right", array_sort);
    let alias = app(&mut ts, "=", &[left, right], Sort::Bool);

    let at_limit = vec![alias; residual::MAX_WITNESS_ALIASES];
    assert_confirmed(&verdict(&ts, &StubModel::new(), &at_limit));

    let over_limit = vec![alias; residual::MAX_WITNESS_ALIASES + 1];
    assert_cannot(&verdict(&ts, &StubModel::new(), &over_limit));
}

#[test]
fn residual_member_budget_fails_closed_without_partial_classes() {
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Int, struct_sort());
    let index = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let mut assertions = Vec::new();
    for member in 0..=residual::MAX_WITNESS_MEMBERS {
        let array = ts.mk_var(format!("array_{member}"), array_sort.clone());
        assertions.push(field_read_eq(&mut ts, "f", array, index, five));
    }

    assert_confirmed(&verdict(
        &ts,
        &StubModel::new(),
        &assertions[..residual::MAX_WITNESS_MEMBERS],
    ));
    assert_cannot(&verdict(&ts, &StubModel::new(), &assertions));
}

#[test]
fn residual_occurrence_node_budget_fails_closed() {
    let mut ts = TermStore::new();
    let array = ts.mk_var("a", Sort::array(Sort::Int, struct_sort()));
    let index = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let residual = field_read_eq(&mut ts, "f", array, index, five);
    let mut assertions = vec![residual];
    let mut model = StubModel::new();
    for node in 0..=residual::MAX_OCCURRENCE_NODES {
        let pinned_true = ts.mk_var(format!("pinned_true_{node}"), Sort::Bool);
        assertions.push(pinned_true);
        model = model.with(pinned_true, ModelValue::Bool(true));
    }

    assert_cannot(&verdict(&ts, &model, &assertions));
}

#[test]
fn residual_occurrence_pending_width_budget_fails_closed() {
    let mut ts = TermStore::new();
    let array = ts.mk_var("a", Sort::array(Sort::Int, struct_sort()));
    let index = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let residual = field_read_eq(&mut ts, "f", array, index, five);
    let pinned_true = ts.mk_var("pinned_true", Sort::Bool);
    let arguments = vec![pinned_true; residual::MAX_OCCURRENCE_NODES];
    let wide_true = app(&mut ts, "and", &arguments, Sort::Bool);
    let model = StubModel::new().with(pinned_true, ModelValue::Bool(true));

    assert_cannot(&verdict(&ts, &model, &[residual, wide_true]));
}

#[test]
fn residual_free_dt_array_conflicting_reads_stay_unknown() {
    // Same shape but f(a[0]) = 5 vs f(b[0]) = 6 with a = b: two constraints
    // force different values at ONE (class, index, field) slot — the residue
    // is NOT jointly satisfiable, so the gate must keep failing closed.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "f", b, i0, c6);
    let m = StubModel::new();
    assert_cannot(&verdict(&ts, &m, &[alias, r1, r2]));
}

#[test]
fn residual_free_dt_array_bv64_alias_with_conflicting_reads_stays_unknown() {
    // The positive BV64 case must not widen the fragment: aliased arrays
    // still identify the same high-bit index, so contradictory requirements
    // at that cell cannot produce a witness or ConfirmedSat.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::bitvec(64), struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let index = ts.mk_bitvec(BigInt::from(0x8000_0000_0000_0001u64), 64);
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, index, c5);
    let r2 = field_read_eq(&mut ts, "f", b, index, c6);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[alias, r1, r2]));
}

#[test]
fn residual_free_dt_array_symbolic_index_evaluated_under_model() {
    // The read index is a VARIABLE the model pins: i = 0 makes f(a[i]) = 5
    // collide with f(b[0]) = 6 under a = b ⇒ CannotConfirm. With i = 1 the
    // keys are distinct ⇒ ConfirmedSat. (Indices are evaluated, not
    // syntactically compared.)
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i = ts.mk_var("i", Sort::Int);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i, c5);
    let r2 = field_read_eq(&mut ts, "f", b, i0, c6);
    let colliding = StubModel::new().with(i, ModelValue::Int(int(0)));
    assert_cannot(&verdict(&ts, &colliding, &[alias, r1, r2]));
    let disjoint = StubModel::new().with(i, ModelValue::Int(int(1)));
    assert_confirmed(&verdict(&ts, &disjoint, &[alias, r1, r2]));
}

#[test]
fn residual_free_dt_array_whole_element_reads() {
    // Whole-element requirements: (= (select a 0) (mk 1 2)) twice through the
    // alias is consistent ⇒ ConfirmedSat; against (mk 3 4) ⇒ CannotConfirm.
    let mut ts = TermStore::new();
    let ssort = struct_sort();
    let asort = Sort::array(Sort::Int, ssort.clone());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c2 = ts.mk_int(int(2));
    let c3 = ts.mk_int(int(3));
    let c4 = ts.mk_int(int(4));
    let mk12 = app(&mut ts, "mk", &[c1, c2], ssort.clone());
    let mk34 = app(&mut ts, "mk", &[c3, c4], ssort.clone());
    let sel_a = app(&mut ts, "select", &[a, i0], ssort.clone());
    let sel_b = app(&mut ts, "select", &[b, i0], ssort);
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let w1 = app(&mut ts, "=", &[sel_a, mk12], Sort::Bool);
    let w2_ok = app(&mut ts, "=", &[sel_b, mk12], Sort::Bool);
    let w2_bad = app(&mut ts, "=", &[sel_b, mk34], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[alias, w1, w2_ok]));
    assert_cannot(&verdict(&ts, &StubModel::new(), &[alias, w1, w2_bad]));
}

#[test]
fn residual_free_dt_array_disequality_stays_unknown() {
    // A DISEQUALITY between free arrays is outside the decided fragment
    // (hard constraint: only eq-alias + element-read shapes) ⇒ CannotConfirm,
    // even though it is trivially satisfiable.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort.clone());
    let c = ts.mk_var("c", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let eq_bc = app(&mut ts, "=", &[b, c], Sort::Bool);
    let diseq = app(&mut ts, "not", &[eq_bc], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[alias, diseq, r1]));
}

#[test]
fn residual_free_dt_array_store_context_stays_unknown() {
    // A free class member occurring inside a `store` is outside the fragment
    // (the store could constrain the array beyond element reads) ⇒ refuse.
    let mut ts = TermStore::new();
    let ssort = struct_sort();
    let asort = Sort::array(Sort::Int, ssort.clone());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort.clone());
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c2 = ts.mk_int(int(2));
    let c5 = ts.mk_int(int(5));
    let mk12 = app(&mut ts, "mk", &[c1, c2], ssort);
    let stored = app(&mut ts, "store", &[a, i0, mk12], asort);
    let eq_store = app(&mut ts, "=", &[b, stored], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq_store, r1]));
}

#[test]
fn residual_free_dt_array_guarded_alias_confirms() {
    // The model-checker-consumer VC shape: the alias sits under an `or` whose other
    // disjunct concretely evaluates FALSE — `(or (not (= x 1)) (= a b))`
    // with x = 1. The guard's value is preserved by the extension, so the
    // alias is still forced and the decision applies.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let x = ts.mk_var("x", Sort::Int);
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let eq_x1 = app(&mut ts, "=", &[x, c1], Sort::Bool);
    let not_x1 = app(&mut ts, "not", &[eq_x1], Sort::Bool);
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let guarded = app(&mut ts, "or", &[not_x1, alias], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "f", b, i0, c5);
    let r2_bad = field_read_eq(&mut ts, "f", b, i0, c6);
    let m = || StubModel::new().with(x, ModelValue::Int(int(1)));
    assert_confirmed(&verdict(&ts, &m(), &[guarded, r1, r2]));
    // The guarded alias still JOINS the classes: conflicting reads refuse.
    assert_cannot(&verdict(&ts, &m(), &[guarded, r1, r2_bad]));
}

#[test]
fn residual_free_dt_array_unpinned_scalar_side_stays_unknown() {
    // The ground side of an element read must EVALUATE under the fixed
    // partial model; an unpinned scalar keeps the fail-closed verdict.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort);
    let y = ts.mk_var("y", Sort::Int);
    let i0 = ts.mk_int(int(0));
    let r1 = field_read_eq(&mut ts, "f", a, i0, y);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[r1]));
}

#[test]
fn residual_free_dt_array_pinned_member_not_free() {
    // An "alias" whose side the model PINS is not the free fragment: the
    // pinned side resolves, the equality constrains the free side to a
    // committed value — exactly what the decision must NOT adjudicate.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let r1 = field_read_eq(&mut ts, "f", b, i0, c5);
    let m = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Datatype {
                ctor: "mk".to_string(),
                args: vec![ModelValue::Int(int(9)), ModelValue::Int(int(9))],
            },
            store: vec![],
        })),
    );
    assert_cannot(&verdict(&ts, &m, &[alias, r1]));
}

#[test]
fn residual_conflicting_committed_read_cannot_be_laundered_by_late_pin() {
    // Scan the residual requirement first, while its concrete-index read is
    // unpinned. A later assertion then adopts a solver commitment for a
    // syntactically different read whose symbolic index evaluates to that same
    // concrete value. Reclassification must observe the value-keyed committed
    // read, discover that it projects `f = 6` rather than the required `f = 5`,
    // and fail closed instead of materializing a witness that launders the pin.
    let mut ts = TermStore::new();
    let datatype = struct_sort();
    let array = ts.mk_var("a", Sort::array(Sort::Int, datatype.clone()));
    let symbolic_index = ts.mk_var("i", Sort::Int);
    let concrete_index = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let zero = ts.mk_int(int(0));
    let committed_element = app(&mut ts, "mk", &[six, zero], datatype.clone());
    let committed_read = app(&mut ts, "select", &[array, symbolic_index], datatype);
    let residual = field_read_eq(&mut ts, "f", array, concrete_index, five);
    let adopting_assertion = app(
        &mut ts,
        "=",
        &[committed_read, committed_element],
        Sort::Bool,
    );
    let model = ArraySelectStubModel::new()
        .leaf(symbolic_index, ModelValue::Int(int(0)))
        .sel(
            committed_read,
            ModelValue::Datatype {
                ctor: "mk".to_string(),
                args: vec![ModelValue::Int(int(6)), ModelValue::Int(int(0))],
            },
        );

    assert_cannot(&verdict(&ts, &model, &[residual, adopting_assertion]));
}

#[test]
fn residual_matching_late_committed_read_is_localized_and_confirms() {
    // Positive control for the conflicting-pin attack above: a syntactically
    // different read at the same model-evaluated index is admissible when its
    // committed element agrees with the residual field requirement.
    let mut ts = TermStore::new();
    let datatype = struct_sort();
    let array = ts.mk_var("a", Sort::array(Sort::Int, datatype.clone()));
    let symbolic_index = ts.mk_var("i", Sort::Int);
    let concrete_index = ts.mk_int(int(0));
    let other_index = ts.mk_int(int(1));
    let five = ts.mk_int(int(5));
    let seven = ts.mk_int(int(7));
    let zero = ts.mk_int(int(0));
    let committed_element = app(&mut ts, "mk", &[five, zero], datatype.clone());
    let committed_read = app(&mut ts, "select", &[array, symbolic_index], datatype);
    let residual = field_read_eq(&mut ts, "f", array, concrete_index, five);
    let unpinned_residual = field_read_eq(&mut ts, "g", array, other_index, seven);
    let adopting_assertion = app(
        &mut ts,
        "=",
        &[committed_read, committed_element],
        Sort::Bool,
    );
    let model = ArraySelectStubModel::new()
        .leaf(symbolic_index, ModelValue::Int(int(0)))
        .sel(
            committed_read,
            ModelValue::Datatype {
                ctor: "mk".to_string(),
                args: vec![ModelValue::Int(int(5)), ModelValue::Int(int(0))],
            },
        );

    assert_confirmed(&verdict(
        &ts,
        &model,
        &[residual, unpinned_residual, adopting_assertion],
    ));
}

#[test]
fn residual_free_dt_array_whole_plus_field_mix_projects_exactly() {
    // Whole-element AND field requirements at ONE (class, index) reconcile by
    // EXACT constructor projection: f(mk(1,2)) = 1 is consistent ⇒ confirmed;
    // f(mk(1,2)) = 3 contradicts ⇒ fail closed.
    let mut ts = TermStore::new();
    let ssort = struct_sort();
    let asort = Sort::array(Sort::Int, ssort.clone());
    let a = ts.mk_var("a", asort);
    let i0 = ts.mk_int(int(0));
    let c1 = ts.mk_int(int(1));
    let c2 = ts.mk_int(int(2));
    let c3 = ts.mk_int(int(3));
    let mk12 = app(&mut ts, "mk", &[c1, c2], ssort.clone());
    let sel_a = app(&mut ts, "select", &[a, i0], ssort);
    let w1 = app(&mut ts, "=", &[sel_a, mk12], Sort::Bool);
    let r_ok = field_read_eq(&mut ts, "f", a, i0, c1);
    let r_bad = field_read_eq(&mut ts, "f", a, i0, c3);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[w1, r_ok]));
    assert_cannot(&verdict(&ts, &StubModel::new(), &[w1, r_bad]));
}

#[test]
fn residual_reads_only_no_alias_confirms() {
    // Singleton classes (no alias equalities at all) are decided too:
    // consistent reads at distinct indices over ONE free array confirm.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, struct_sort());
    let a = ts.mk_var("a", asort);
    let i0 = ts.mk_int(int(0));
    let i1 = ts.mk_int(int(1));
    let c5 = ts.mk_int(int(5));
    let c6 = ts.mk_int(int(6));
    let r1 = field_read_eq(&mut ts, "f", a, i0, c5);
    let r2 = field_read_eq(&mut ts, "f", a, i1, c6);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[r1, r2]));
}

#[test]
fn residual_non_dt_element_array_stays_unknown() {
    // The decision is scoped to DATATYPE-element arrays: a free Int-element
    // array read keeps today's fail-closed behaviour.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort.clone());
    let b = ts.mk_var("b", asort);
    let i0 = ts.mk_int(int(0));
    let c5 = ts.mk_int(int(5));
    let alias = app(&mut ts, "=", &[a, b], Sort::Bool);
    let sel = app(&mut ts, "select", &[a, i0], Sort::Int);
    let r1 = app(&mut ts, "=", &[c5, sel], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[alias, r1]));
}
