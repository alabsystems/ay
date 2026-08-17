// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

#[test]
fn sat_array_store_select() {
    // (= (select (store a 1 9) 1) 9) holds for ANY a.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort.clone());
    let one = ts.mk_int(int(1));
    let nine = ts.mk_int(int(9));
    let stored = app(&mut ts, "store", &[a, one, nine], asort);
    let sel = app(&mut ts, "select", &[stored, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, nine], Sort::Bool);
    // a as a const-0 array — irrelevant, the store overrides index 1.
    let m = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: vec![],
        })),
    );
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn array_default_reads_model_else_value_and_rejects_disagreement() {
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let default = app(&mut ts, "default", &[a], Sort::Int);
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let equals_five = app(&mut ts, "=", &[default, five], Sort::Bool);
    let equals_six = app(&mut ts, "=", &[default, six], Sort::Bool);
    let model = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(5)),
            store: vec![],
        })),
    );

    assert_confirmed(&verdict(&ts, &model, &[equals_five]));
    assert_violates(&verdict(&ts, &model, &[equals_six]));
}

#[test]
fn array_default_reduces_const_and_store_but_unpinned_leaf_fails_closed() {
    let mut ts = TermStore::new();
    let five = ts.mk_int(int(5));
    let const_five = app(
        &mut ts,
        "const-array",
        &[five],
        Sort::array(Sort::Int, Sort::Int),
    );
    let unpinned_index = ts.mk_var("unpinned_index", Sort::Int);
    let unpinned_value = ts.mk_var("unpinned_value", Sort::Int);
    let stored = app(
        &mut ts,
        "store",
        &[const_five, unpinned_index, unpinned_value],
        Sort::array(Sort::Int, Sort::Int),
    );
    let structural_default = app(&mut ts, "default", &[stored], Sort::Int);
    let structural_eq = app(&mut ts, "=", &[structural_default, five], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[structural_eq]));

    let free = ts.mk_var("free", Sort::array(Sort::Int, Sort::Int));
    let unpinned_default = app(&mut ts, "default", &[free], Sort::Int);
    let zero = ts.mk_int(int(0));
    let unpinned_eq = app(&mut ts, "=", &[unpinned_default, zero], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[unpinned_eq]));
}

#[test]
fn dependent_lambda_default_uses_only_committed_opaque_scalar() {
    let mut ts = TermStore::new();
    let bound = ts.mk_var("bound", Sort::Bool);
    let one = ts.mk_int(int(1));
    let zero = ts.mk_int(int(0));
    let body = ts.mk_ite(bound, one, zero);
    let lambda = ts.mk_lambda_array(bound, body);
    let default = ts.mk_array_default(lambda);
    let two = ts.mk_int(int(2));
    let equals_two = app(&mut ts, "=", &[default, two], Sort::Bool);

    assert_confirmed(&verdict(
        &ts,
        &UfStubModel::new().uf(default, ModelValue::Int(int(2))),
        &[equals_two],
    ));
    assert_cannot(&verdict(&ts, &UfStubModel::new(), &[equals_two]));
}

#[test]
fn aliased_dependent_lambda_default_uses_only_committed_opaque_scalar() {
    let mut ts = TermStore::new();
    let bound = ts.mk_var("bound", Sort::Bool);
    let one = ts.mk_int(int(1));
    let zero = ts.mk_int(int(0));
    let body = ts.mk_ite(bound, one, zero);
    let lambda = ts.mk_lambda_array(bound, body);
    // Model an expanded define-fun/alias whose outer syntax hides the lambda
    // from `eval_array_default`'s direct fast path.
    let true_term = ts.mk_bool(true);
    let alias = ts.mk_ite(true_term, lambda, lambda);
    let default = ts.mk_array_default(alias);
    let two = ts.mk_int(int(2));
    let equals_two = app(&mut ts, "=", &[default, two], Sort::Bool);

    assert_confirmed(&verdict(
        &ts,
        &UfStubModel::new().uf(default, ModelValue::Int(int(2))),
        &[equals_two],
    ));
    assert_cannot(&verdict(&ts, &UfStubModel::new(), &[equals_two]));
}

#[test]
fn finite_store_default_uses_committed_scalar_instead_of_base_default() {
    let mut ts = TermStore::new();
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let false_term = ts.mk_bool(false);
    let array_sort = Sort::array(Sort::Bool, Sort::Int);
    let base = app(&mut ts, "const-array", &[zero], array_sort.clone());
    let stored = app(&mut ts, "store", &[base, false_term, one], array_sort);
    let default = app(&mut ts, "default", &[stored], Sort::Int);
    let assertion = app(&mut ts, "=", &[default, one], Sort::Bool);
    let model = UfStubModel::new().uf(default, ModelValue::Int(int(1)));

    assert_confirmed(&verdict(&ts, &model, &[assertion]));
}

#[test]
fn unit_store_default_is_structurally_the_stored_value() {
    let mut ts = TermStore::new();
    let unit_sort = Sort::FiniteDomain("Unit".to_string(), 1);
    let unit = ts.mk_var("unit", unit_sort.clone());
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let array_sort = Sort::array(unit_sort, Sort::Int);
    let base = app(&mut ts, "const-array", &[zero], array_sort.clone());
    let stored = app(&mut ts, "store", &[base, unit, one], array_sort);
    let default = app(&mut ts, "default", &[stored], Sort::Int);
    let assertion = app(&mut ts, "=", &[default, one], Sort::Bool);

    assert_confirmed(&verdict(&ts, &StubModel::new(), &[assertion]));
}

#[test]
fn malformed_array_default_fails_closed() {
    let mut ts = TermStore::new();
    let scalar = ts.mk_var("scalar", Sort::Int);
    let malformed = app(&mut ts, "default", &[scalar], Sort::Int);
    let zero = ts.mk_int(int(0));
    let assertion = app(&mut ts, "=", &[malformed, zero], Sort::Bool);
    let model = StubModel::new().with(scalar, ModelValue::Int(int(0)));
    assert_cannot(&verdict(&ts, &model, &[assertion]));
}

#[test]
fn sat_lambda_array_store_beta_reduces_and_restores_binding() {
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let x = ts.mk_var("x", Sort::Int);
    let one = ts.mk_int(int(1));
    let body = app(&mut ts, "+", &[x, one], Sort::Int);
    let lambda = ts.mk_lambda_array(x, body);
    let three = ts.mk_int(int(3));
    let five = ts.mk_int(int(5));
    let seven = ts.mk_int(int(7));
    let forty_two = ts.mk_int(int(42));
    let stored = app(&mut ts, "store", &[lambda, five, forty_two], asort);

    // Raw select applications ensure model-time store peeling and beta
    // reduction are exercised, rather than TermStore's eager rewrites.
    let at_stored = app(&mut ts, "select", &[stored, five], Sort::Int);
    let at_lambda = app(&mut ts, "select", &[stored, three], Sort::Int);
    let at_second_lambda_index = app(&mut ts, "select", &[stored, seven], Sort::Int);

    // The ambient model pin deliberately conflicts with both beta instances.
    // It must be shadowed only while the body is evaluated.
    let model = StubModel::new().with(x, ModelValue::Int(int(99)));
    let evaluator = Evaluator::new(&ts, &model);
    assert!(matches!(
        evaluator.evaluate(at_stored),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(42)
    ));
    assert!(matches!(
        evaluator.evaluate(at_lambda),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(4)
    ));
    // The body has the same TermId in both beta reductions. A TermId-only
    // memo must not reuse the value computed under x=3 when x=7 is active.
    assert!(matches!(
        evaluator.evaluate(at_second_lambda_index),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(8)
    ));
    assert!(matches!(
        evaluator.evaluate(body),
        EvalOutcome::Value(ModelValue::Int(n)) if n == int(100)
    ));
}

#[test]
fn sat_binder_independent_lambda_materializes_for_array_equality() {
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let x = ts.mk_var("x", Sort::Int);
    let zero = ts.mk_int(int(0));
    let five = ts.mk_int(int(5));
    let forty_two = ts.mk_int(int(42));
    let lambda = ts.mk_lambda_array(x, zero);
    let actual = app(&mut ts, "store", &[lambda, five, forty_two], asort.clone());
    let constant = app(&mut ts, "const-array", &[zero], asort.clone());
    let expected = app(&mut ts, "store", &[constant, five, forty_two], asort);
    let eq = app(&mut ts, "=", &[actual, expected], Sort::Bool);

    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn lambda_beta_does_not_trust_non_contextual_uf_pin() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let fx = app(&mut ts, "f", &[x], Sort::Int);
    let lambda = ts.mk_lambda_array(x, fx);
    let three = ts.mk_int(int(3));
    let seven = ts.mk_int(int(7));
    let read = app(&mut ts, "select", &[lambda, three], Sort::Int);
    let eq = app(&mut ts, "=", &[read, seven], Sort::Bool);

    // A per-TermId pin for f(x) is not a value for f(3): accepting it under the
    // beta binding would conflate distinct lambda environments. Fail closed.
    let model = UfStubModel::new().uf(fx, ModelValue::Int(int(7)));
    assert_cannot(&verdict(&ts, &model, &[eq]));
}

#[test]
fn lambda_beta_allows_binder_independent_model_pins() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let five = ts.mk_int(int(5));
    let f_five = app(&mut ts, "f", &[five], Sort::Int);
    let lambda_uf = ts.mk_lambda_array(x, f_five);
    let three = ts.mk_int(int(3));
    let uf_read = app(&mut ts, "select", &[lambda_uf, three], Sort::Int);
    let seven = ts.mk_int(int(7));
    let uf_eq = app(&mut ts, "=", &[uf_read, seven], Sort::Bool);
    let uf_model = UfStubModel::new().uf(f_five, ModelValue::Int(int(7)));
    assert_confirmed(&verdict(&ts, &uf_model, &[uf_eq]));

    let a = ts.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let at_five = app(&mut ts, "select", &[a, five], Sort::Int);
    let lambda_select = ts.mk_lambda_array(x, at_five);
    let select_read = app(&mut ts, "select", &[lambda_select, three], Sort::Int);
    let select_eq = app(&mut ts, "=", &[select_read, seven], Sort::Bool);
    let select_model = UfStubModel::new().sel(at_five, ModelValue::Int(int(7)));
    assert_confirmed(&verdict(&ts, &select_model, &[select_eq]));
}

#[test]
fn lambda_beta_uf_reuses_only_a_value_keyed_graph_entry() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let three = ts.mk_int(int(3));
    let seven = ts.mk_int(int(7));

    // Seed the independent evaluator's graph with the concrete point f(3).
    let f_three = app(&mut ts, "f", &[three], Sort::Int);
    let seed = app(&mut ts, "=", &[f_three, seven], Sort::Bool);

    // The contextual f(x) has no per-TermId model pin. It is nevertheless the
    // same function point after beta reduction, so recursive argument
    // evaluation may soundly reuse the value-keyed f(3) graph entry.
    let f_x = app(&mut ts, "f", &[x], Sort::Int);
    let lambda = ts.mk_lambda_array(x, f_x);
    let read = app(&mut ts, "select", &[lambda, three], Sort::Int);
    let beta = app(&mut ts, "=", &[read, seven], Sort::Bool);
    let model = UfStubModel::new().uf(f_three, ModelValue::Int(int(7)));

    assert_confirmed(&verdict(&ts, &model, &[seed, beta]));
}

#[test]
fn lambda_beta_selector_fallback_rejects_context_free_pins() {
    let mut ts = TermStore::new();
    let pair = Sort::Datatype(DatatypeSort::new(
        "Pair",
        vec![DatatypeConstructor::new(
            "mk",
            vec![DatatypeField::new("fst", Sort::Int)],
        )],
    ));
    let x = ts.mk_var("x", Sort::Int);
    let a = ts.mk_var("a", Sort::array(Sort::Int, pair.clone()));
    let pair_at_x = app(&mut ts, "select", &[a, x], pair);
    let fst_at_x = app(&mut ts, "fst", &[pair_at_x], Sort::Int);
    let lambda = ts.mk_lambda_array(x, fst_at_x);
    let three = ts.mk_int(int(3));
    let read = app(&mut ts, "select", &[lambda, three], Sort::Int);
    let seven = ts.mk_int(int(7));
    let eq = app(&mut ts, "=", &[read, seven], Sort::Bool);

    // Neither commitment is indexed by the beta environment. In particular,
    // the selector fallback must not use the ambient value of select(a, x) to
    // manufacture a value for fst(select(a, 3)).
    let model = UfStubModel::new()
        .sel(
            pair_at_x,
            ModelValue::Datatype {
                ctor: "mk".to_string(),
                args: vec![ModelValue::Int(int(7))],
            },
        )
        .uf(fst_at_x, ModelValue::Int(int(7)));
    assert_cannot(&verdict(&ts, &model, &[eq]));
}

// ---------------------------------------------------------------------------
// S1 REGRESSION (the development design notes) — CLOSED at the gate level.
// UF congruence over equal arrays: (= (select a i) v) ⇒ store(a,i,v) ≡ a ⇒
// f(store(a,i,v)) = f(a), so (not (= (f (store a i v)) (f a))) is UNSAT. The
// independent gate now CATCHES a model that violates this as `ModelViolates`, via
// the congruence rule in `eval_eq` (equalities of same-head applications with
// argument-wise-equal values evaluate to `true`, no interpretation of `f` needed).
// The (unconditional) `ModelViolates` enforcement demotes S1's wrong `sat` to
// `unknown`.
// ---------------------------------------------------------------------------
#[test]
fn s1_uf_congruence_over_equal_arrays_should_violate() {
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort.clone());
    let i = ts.mk_var("i", Sort::Int);
    let v = ts.mk_var("v", Sort::Int);
    // (= (select a i) v)
    let sel = app(&mut ts, "select", &[a, i], Sort::Int);
    let eq_sel_v = app(&mut ts, "=", &[sel, v], Sort::Bool);
    // (not (= (f (store a i v)) (f a)))  — with select(a,i)=v, store(a,i,v) ≡ a.
    let stored = app(&mut ts, "store", &[a, i, v], asort);
    let f_store = app(&mut ts, "f", &[stored], Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let eq_ff = app(&mut ts, "=", &[f_store, f_a], Sort::Bool);
    let neq_ff = app(&mut ts, "not", &[eq_ff], Sort::Bool);
    // Model: a = const-0 array, i = 0, v = 0  ⇒ select(a,0)=0=v and store(a,0,0) ≡ a.
    let m = StubModel::new()
        .with(
            a,
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![],
            })),
        )
        .with(i, ModelValue::Int(int(0)))
        .with(v, ModelValue::Int(int(0)));
    // TARGET behaviour once the congruence rule lands (today: CannotConfirm ⇒ this fails):
    assert_violates(&verdict(&ts, &m, &[eq_sel_v, neq_ff]));
}

#[test]
fn sat_const_array() {
    // (= (select (const-array 5) 99) 5).
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let five = ts.mk_int(int(5));
    let ca = app(&mut ts, "const-array", &[five], asort);
    let n99 = ts.mk_int(int(99));
    let sel = app(&mut ts, "select", &[ca, n99], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, five], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn sat_seq_prefix_and_len() {
    // (seq.prefixof (seq.unit true) s) with s = [true, false]; and
    // (= (seq.len (seq.++ (seq.unit 1) (seq.unit 2))) 2).
    let mut ts = TermStore::new();
    let sseq = Sort::seq(Sort::Bool);
    let s = ts.mk_var("s", sseq.clone());
    let tt = ts.mk_bool(true);
    let unit_t = app(&mut ts, "seq.unit", &[tt], sseq.clone());
    let pre = app(&mut ts, "seq.prefixof", &[unit_t, s], Sort::Bool);

    let iseq = Sort::seq(Sort::Int);
    let i1 = ts.mk_int(int(1));
    let i2 = ts.mk_int(int(2));
    let u1 = app(&mut ts, "seq.unit", &[i1], iseq.clone());
    let u2 = app(&mut ts, "seq.unit", &[i2], iseq.clone());
    let cat = app(&mut ts, "seq.++", &[u1, u2], iseq);
    let len = app(&mut ts, "seq.len", &[cat], Sort::Int);
    let two = ts.mk_int(int(2));
    let eqlen = app(&mut ts, "=", &[len, two], Sort::Bool);

    let m = StubModel::new().with(
        s,
        ModelValue::Seq(vec![ModelValue::Bool(true), ModelValue::Bool(false)]),
    );
    assert_confirmed(&verdict(&ts, &m, &[pre, eqlen]));
}
