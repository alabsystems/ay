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
