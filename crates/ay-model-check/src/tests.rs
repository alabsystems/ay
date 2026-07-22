// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hand-constructed `(assertions, model)` pairs exercising the gate:
//!
//! * (a) models that SATISFY ⇒ `ConfirmedSat`;
//! * (b) models that VIOLATE an assertion ⇒ `ModelViolates` — including
//!   analogues of real wrong-`sat` bugs (seq prefix, array select, datatype
//!   recognizer, seq.indexof);
//! * (c) under-specified / unimplemented / unpinned / quantified ⇒
//!   `CannotConfirm` (never a false `ConfirmedSat`).

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use std::collections::HashMap;

/// A trivial stub model: a fixed map from leaf `TermId` to value.
struct StubModel {
    leaves: HashMap<TermId, ModelValue>,
}

impl StubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
        }
    }
    fn with(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
}

impl ModelView for StubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
}

fn int(n: i64) -> BigInt {
    BigInt::from(n)
}

fn app(ts: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    ts.mk_app(Symbol::named(name), args, sort)
}

fn verdict(ts: &TermStore, model: &dyn ModelView, asserts: &[TermId]) -> GateVerdict {
    confirm_model(ts, model, asserts)
}

fn assert_confirmed(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ConfirmedSat),
        "expected ConfirmedSat, got {v:?}"
    );
}
fn assert_violates(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::ModelViolates { .. }),
        "expected ModelViolates, got {v:?}"
    );
}
fn assert_cannot(v: &GateVerdict) {
    assert!(
        matches!(v, GateVerdict::CannotConfirm { .. }),
        "expected CannotConfirm, got {v:?}"
    );
}

// ===========================================================================
// (a) Satisfying models ⇒ ConfirmedSat
// ===========================================================================

#[test]
fn sat_bool_leaf() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    let m = StubModel::new().with(x, ModelValue::Bool(true));
    assert_confirmed(&verdict(&ts, &m, &[x]));
}

#[test]
fn sat_int_arithmetic() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let one = ts.mk_int(int(1));
    let four = ts.mk_int(int(4));
    let sum = app(&mut ts, "+", &[x, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sum, four], Sort::Bool);
    let m = StubModel::new().with(x, ModelValue::Int(int(3)));
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn sat_euclidean_mod_and_div() {
    // SMT-LIB: (-7) = 3*(-3) + 2, so (mod -7 3) = 2 and (div -7 3) = -3.
    let mut ts = TermStore::new();
    let neg7 = ts.mk_int(int(-7));
    let three = ts.mk_int(int(3));
    let two = ts.mk_int(int(2));
    let neg3 = ts.mk_int(int(-3));
    let m = app(&mut ts, "mod", &[neg7, three], Sort::Int);
    let d = app(&mut ts, "div", &[neg7, three], Sort::Int);
    let em = app(&mut ts, "=", &[m, two], Sort::Bool);
    let ed = app(&mut ts, "=", &[d, neg3], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[em, ed]));
}

#[test]
fn sat_bitvector_add() {
    let mut ts = TermStore::new();
    let a = ts.mk_bitvec(int(3), 4);
    let b = ts.mk_bitvec(int(1), 4);
    let four = ts.mk_bitvec(int(4), 4);
    let sum = app(&mut ts, "bvadd", &[a, b], Sort::bitvec(4));
    let eq = app(&mut ts, "=", &[sum, four], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn sat_bitvector_signed_div_and_extract() {
    // bvsdiv of -6 / 2 over 4 bits = -3 (= 1101). extract [1:0] of 1101 = 01.
    let mut ts = TermStore::new();
    let neg6 = ts.mk_bitvec(int(-6), 4); // 1010
    let two = ts.mk_bitvec(int(2), 4);
    let q = app(&mut ts, "bvsdiv", &[neg6, two], Sort::bitvec(4)); // 1101
    let expect = ts.mk_bitvec(int(-3), 4);
    let eq = app(&mut ts, "=", &[q, expect], Sort::Bool);
    let ext = ts.mk_app(Symbol::indexed("extract", vec![1, 0]), [q], Sort::bitvec(2));
    let one2 = ts.mk_bitvec(int(1), 2); // 01
    let eq2 = app(&mut ts, "=", &[ext, one2], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq, eq2]));
}

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

#[test]
fn sat_datatype_constructor_selector() {
    // (= (fst (mk 3 4)) 3) for datatype Pair = mk(fst: Int, snd: Int).
    let mut ts = TermStore::new();
    let pair = Sort::Datatype(DatatypeSort::new(
        "Pair",
        vec![DatatypeConstructor::new(
            "mk",
            vec![
                DatatypeField::new("fst", Sort::Int),
                DatatypeField::new("snd", Sort::Int),
            ],
        )],
    ));
    let i3 = ts.mk_int(int(3));
    let i4 = ts.mk_int(int(4));
    let mk = app(&mut ts, "mk", &[i3, i4], pair);
    let fst = app(&mut ts, "fst", &[mk], Sort::Int);
    let eq = app(&mut ts, "=", &[fst, i3], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

// ===========================================================================
// (b) Violating models ⇒ ModelViolates  (caught wrong-`sat`)
// ===========================================================================

#[test]
fn violate_seq_prefix_empty() {
    // BUG ANALOGUE: s = [] (or [false]) under (seq.prefixof (seq.unit true) s).
    let mut ts = TermStore::new();
    let sseq = Sort::seq(Sort::Bool);
    let s = ts.mk_var("s", sseq.clone());
    let tt = ts.mk_bool(true);
    let unit_t = app(&mut ts, "seq.unit", &[tt], sseq);
    let pre = app(&mut ts, "seq.prefixof", &[unit_t, s], Sort::Bool);

    let empty = StubModel::new().with(s, ModelValue::Seq(vec![]));
    assert_violates(&verdict(&ts, &empty, &[pre]));

    let false_only = StubModel::new().with(s, ModelValue::Seq(vec![ModelValue::Bool(false)]));
    assert_violates(&verdict(&ts, &false_only, &[pre]));
}

#[test]
fn violate_array_select() {
    // BUG ANALOGUE: a = const-0 under (= (select a 1) 9).
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a = ts.mk_var("a", asort);
    let one = ts.mk_int(int(1));
    let nine = ts.mk_int(int(9));
    let sel = app(&mut ts, "select", &[a, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, nine], Sort::Bool);
    let m = StubModel::new().with(
        a,
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(0)),
            store: vec![],
        })),
    );
    assert_violates(&verdict(&ts, &m, &[eq]));
}

#[test]
fn violate_datatype_recognizer_and_bool() {
    // BUG ANALOGUE (datatype/Bool): ((_ is Red) c) with c = Green.
    let mut ts = TermStore::new();
    let color = Sort::enum_type("Color", ["Red", "Green"]);
    let c = ts.mk_var("c", color);
    let is_red = app(&mut ts, "is-Red", &[c], Sort::Bool);
    let m = StubModel::new().with(
        c,
        ModelValue::Datatype {
            ctor: "Green".to_string(),
            args: vec![],
        },
    );
    assert_violates(&verdict(&ts, &m, &[is_red]));

    // Plain Bool violation: assert p, model says p = false.
    let mut ts2 = TermStore::new();
    let p = ts2.mk_var("p", Sort::Bool);
    let mp = StubModel::new().with(p, ModelValue::Bool(false));
    assert_violates(&verdict(&ts2, &mp, &[p]));
}

#[test]
fn violate_seq_indexof() {
    // BUG ANALOGUE (indexof): claim "7 is absent" — (= (seq.indexof s [7] 0) -1)
    // — but the model has s = [7], where the true index is 0.
    let mut ts = TermStore::new();
    let iseq = Sort::seq(Sort::Int);
    let s = ts.mk_var("s", iseq.clone());
    let seven = ts.mk_int(int(7));
    let unit7 = app(&mut ts, "seq.unit", &[seven], iseq);
    let zero = ts.mk_int(int(0));
    let idx = app(&mut ts, "seq.indexof", &[s, unit7, zero], Sort::Int);
    let neg1 = ts.mk_int(int(-1));
    let eq = app(&mut ts, "=", &[idx, neg1], Sort::Bool);
    let m = StubModel::new().with(s, ModelValue::Seq(vec![ModelValue::Int(int(7))]));
    assert_violates(&verdict(&ts, &m, &[eq]));
}

#[test]
fn violate_bitvector() {
    // (= (bvadd #b0011 #b0001) #b0000) — actually 0100.
    let mut ts = TermStore::new();
    let a = ts.mk_bitvec(int(3), 4);
    let b = ts.mk_bitvec(int(1), 4);
    let zero = ts.mk_bitvec(int(0), 4);
    let sum = app(&mut ts, "bvadd", &[a, b], Sort::bitvec(4));
    let eq = app(&mut ts, "=", &[sum, zero], Sort::Bool);
    assert_violates(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn violate_one_of_many_assertions() {
    // First assertion holds, second is falsified — gate must report violation.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let zero = ts.mk_int(int(0));
    let ten = ts.mk_int(int(10));
    let ge = app(&mut ts, ">=", &[x, zero], Sort::Bool); // x >= 0  (true)
    let eq = app(&mut ts, "=", &[x, ten], Sort::Bool); // x = 10  (false)
    let m = StubModel::new().with(x, ModelValue::Int(int(3)));
    assert_violates(&verdict(&ts, &m, &[ge, eq]));
}

// ===========================================================================
// (c) Cannot confirm  (fail closed — never a false ConfirmedSat)
// ===========================================================================

#[test]
fn cannot_unpinned_leaf() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    // model pins nothing.
    assert_cannot(&verdict(&ts, &StubModel::new(), &[x]));
}

#[test]
fn cannot_uninterpreted_function() {
    // (= (f 3) 5) where f is an uninterpreted function the gate does not value.
    let mut ts = TermStore::new();
    let i3 = ts.mk_int(int(3));
    let fa = app(&mut ts, "f", &[i3], Sort::Int);
    let five = ts.mk_int(int(5));
    let eq = app(&mut ts, "=", &[fa, five], Sort::Bool);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn cannot_quantifier() {
    let mut ts = TermStore::new();
    let y = ts.mk_var("y", Sort::Int);
    let zero = ts.mk_int(int(0));
    let body = app(&mut ts, ">=", &[y, zero], Sort::Bool);
    let forall = ts.mk_forall(vec![("y".to_string(), Sort::Int)], body);
    assert_cannot(&verdict(&ts, &StubModel::new(), &[forall]));
}

#[test]
fn cannot_unimplemented_op() {
    // A floating-point op is intentionally not implemented ⇒ unevaluable.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::FloatingPoint(8, 24));
    let is_nan = app(&mut ts, "fp.isNaN", &[x], Sort::Bool);
    let m = StubModel::new(); // even if pinned, fp.isNaN is unimplemented.
    assert_cannot(&verdict(&ts, &m, &[is_nan]));
}

#[test]
fn cannot_selector_wrong_constructor() {
    // Selector applied to a value built with a different constructor is
    // under-specified ⇒ unevaluable, NOT a fabricated value.
    let mut ts = TermStore::new();
    let dt = DatatypeSort::new(
        "T",
        vec![
            DatatypeConstructor::new("A", vec![DatatypeField::new("geta", Sort::Int)]),
            DatatypeConstructor::new("B", vec![DatatypeField::new("getb", Sort::Int)]),
        ],
    );
    let tsort = Sort::Datatype(dt);
    let x = ts.mk_var("x", tsort.clone());
    // (= (geta x) 0) but x is built with constructor B.
    let geta = app(&mut ts, "geta", &[x], Sort::Int);
    let zero = ts.mk_int(int(0));
    let eq = app(&mut ts, "=", &[geta, zero], Sort::Bool);
    let m = StubModel::new().with(
        x,
        ModelValue::Datatype {
            ctor: "B".to_string(),
            args: vec![ModelValue::Int(int(0))],
        },
    );
    assert_cannot(&verdict(&ts, &m, &[eq]));
}

// ===========================================================================
// Targeted operator-semantics checks
// ===========================================================================

#[test]
fn and_false_with_unevaluable_sibling_is_false() {
    // (and false <unpinned x>) must be Bool(false), not Unevaluable — so an
    // assertion (not (and false x)) is confirmed even though x is unpinned.
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    let ff = ts.mk_bool(false);
    let conj = app(&mut ts, "and", &[ff, x], Sort::Bool);
    let neg = ts.mk_not(conj);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[neg]));
}

#[test]
fn or_true_with_unevaluable_sibling_is_true() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Bool);
    let tt = ts.mk_bool(true);
    let disj = app(&mut ts, "or", &[tt, x], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[disj]));
}

#[test]
fn ite_only_evaluates_taken_branch() {
    // (= (ite true 1 <unpinned>) 1): the else branch must not be evaluated.
    let mut ts = TermStore::new();
    let tt = ts.mk_bool(true);
    let one = ts.mk_int(int(1));
    let junk = ts.mk_var("junk", Sort::Int); // unpinned
    let ite = ts.mk_ite(tt, one, junk);
    let eq = app(&mut ts, "=", &[ite, one], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));
}

#[test]
fn distinct_detects_duplicate() {
    // (distinct 1 2 1) is false.
    let mut ts = TermStore::new();
    let a = ts.mk_int(int(1));
    let b = ts.mk_int(int(2));
    let c = ts.mk_int(int(1));
    let d = app(&mut ts, "distinct", &[a, b, c], Sort::Bool);
    assert_violates(&verdict(&ts, &StubModel::new(), &[d]));
}

#[test]
fn array_equality_extensional() {
    // (= (store (const-array 0) 1 5) (store (const-array 0) 1 5)) is true;
    // changing one value breaks equality.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let z = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let ca1 = app(&mut ts, "const-array", &[z], asort.clone());
    let ca2 = app(&mut ts, "const-array", &[z], asort.clone());
    let s1 = app(&mut ts, "store", &[ca1, one, five], asort.clone());
    let s2 = app(&mut ts, "store", &[ca2, one, five], asort.clone());
    let eq = app(&mut ts, "=", &[s1, s2], Sort::Bool);
    assert_confirmed(&verdict(&ts, &StubModel::new(), &[eq]));

    let s3 = app(&mut ts, "store", &[ca1, one, six], asort);
    let neq = app(&mut ts, "=", &[s1, s3], Sort::Bool);
    assert_violates(&verdict(&ts, &StubModel::new(), &[neq]));
}

#[test]
fn evaluate_term_exposes_outcome() {
    let mut ts = TermStore::new();
    let x = ts.mk_var("x", Sort::Int);
    let one = ts.mk_int(int(1));
    let sum = app(&mut ts, "+", &[x, one], Sort::Int);
    let m = StubModel::new().with(x, ModelValue::Int(int(41)));
    match evaluate_term(&ts, &m, sum) {
        EvalOutcome::Value(ModelValue::Int(n)) => assert_eq!(n, int(42)),
        other => panic!("expected Int(42), got {other:?}"),
    }
}

// ===========================================================================
// (d) Uninterpreted-function applications — value-keyed function graph
//
// An uninterpreted function is single-valued: two applications whose ARGUMENTS
// evaluate to equal values must return the same value. The gate builds a
// value-keyed graph as it evaluates (`uf_app_value` supplies the committed
// per-application value); the FIRST application to reach a given
// `(name, arg-values)` key fixes the value for every later application with the
// same key. This is what catches the QF_UFLIA / array-select wrong-model class
// where a degenerate integer assignment collapses two distinct applications'
// arguments to the same value while the model pins them to different results.
// ===========================================================================

/// A stub model that also answers `uf_app_value` for whole application terms.
struct UfStubModel {
    leaves: HashMap<TermId, ModelValue>,
    uf_apps: HashMap<TermId, ModelValue>,
    selects: HashMap<TermId, ModelValue>,
}

impl UfStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            uf_apps: HashMap::new(),
            selects: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn uf(mut self, t: TermId, v: ModelValue) -> Self {
        self.uf_apps.insert(t, v);
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
}

impl ModelView for UfStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn uf_app_value(&self, t: TermId) -> Option<ModelValue> {
        self.uf_apps.get(&t).cloned()
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

#[test]
fn uf_collapsed_arguments_refute_strict_inequality() {
    // The uflia89 shape: `(> (f (* 3 i0)) (f i0))` with `i0 = 0`. Both `(* 3 i0)`
    // and `i0` evaluate to 0, so both applications are `f(0)`; the model pins
    // them to different results (0 and -1). The gate collapses them to one value
    // (first-wins), so `(> v v)` is `false` — a caught wrong witness. (Emitting
    // 0 and -1 for the SAME `f(0)` is exactly the internally-inconsistent model
    // z3 rejects when the scalars are pinned.)
    let mut ts = TermStore::new();
    let i0 = ts.mk_var("i0", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i0], Sort::Int);
    let f_hi = app(&mut ts, "f", &[mul], Sort::Int); // f(3*i0)
    let f_lo = app(&mut ts, "f", &[i0], Sort::Int); // f(i0)
    let gt = app(&mut ts, ">", &[f_hi, f_lo], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(i0, ModelValue::Int(int(0)))
        .uf(f_hi, ModelValue::Int(int(0)))
        .uf(f_lo, ModelValue::Int(int(-1)));
    assert_violates(&verdict(&ts, &m, &[gt]));
}

#[test]
fn uf_distinct_arguments_confirm_valid_model() {
    // Distinct arguments (a = 5, b = 7): the two applications key differently and
    // keep their own committed values (f(5) = 1 > f(7) = 0), so the witness is
    // confirmed. The UF handling must NOT over-refute genuine models.
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let f_b = app(&mut ts, "f", &[b], Sort::Int);
    let gt = app(&mut ts, ">", &[f_a, f_b], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(7)))
        .uf(f_a, ModelValue::Int(int(1)))
        .uf(f_b, ModelValue::Int(int(0)));
    assert_confirmed(&verdict(&ts, &m, &[gt]));
}

#[test]
fn uf_congruent_applications_share_one_value() {
    // Two applications with equal arguments (a = b = 5) must denote the same
    // value: `(= (f a) (f b))` holds even though the model pins them to
    // different committed values (the first-seen value, 1, wins for both).
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let f_b = app(&mut ts, "f", &[b], Sort::Int);
    let eq = app(&mut ts, "=", &[f_a, f_b], Sort::Bool);
    let m = UfStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(5)))
        .uf(f_a, ModelValue::Int(int(1)))
        .uf(f_b, ModelValue::Int(int(2)));
    // Congruent apps collapse to one value, so equality is TRUE (not a spurious
    // violation): `(= 1 1)`.
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn uf_unpinned_application_cannot_confirm() {
    // If the model does not pin an application value, the application is
    // unevaluable and the gate fails closed (never assumed) — CannotConfirm.
    let mut ts = TermStore::new();
    let a = ts.mk_var("a", Sort::Int);
    let f_a = app(&mut ts, "f", &[a], Sort::Int);
    let zero = ts.mk_int(int(0));
    let gt = app(&mut ts, ">", &[f_a, zero], Sort::Bool);
    let m = UfStubModel::new().leaf(a, ModelValue::Int(int(5))); // no uf pin
    assert_cannot(&verdict(&ts, &m, &[gt]));
}

// ===========================================================================
// (e) Array-`select` reads via the model — value-keyed select graph
//
// `select` over an array is a single-valued function of the index. When the
// gate cannot resolve the array operand to a concrete `(default, finite-store)`
// value (a partial / unreconstructable array leaf), it reads the model's
// committed per-read value (`array_select_value`) but keys reads by
// `(array-term, index-value)` and takes the first committed value per key. Two
// reads of the SAME array at index values that evaluate EQUAL therefore resolve
// to one element — exposing (rather than honouring) a model that pins them to
// different values — and, because the gate evaluates indices itself, a
// degenerate array whose reads contradict an asserted (in)equality evaluates the
// assertion to `false`. This is the array analogue of the UF value-keyed graph
// above, closing the array-`select` wrong-model class (#array-select-collapse)
// at the gate even when the theory's array interpretation is unavailable.
// ===========================================================================

/// A stub model that pins scalar leaves and answers `array_select_value` for
/// whole `(select A i)` application terms — but deliberately does NOT pin the
/// array leaf itself, so the gate must go through the `select`-via-model fallback
/// (mirroring the real gate, whose fallback fires exactly when the theory array
/// interpretation cannot be reconstructed).
struct ArraySelectStubModel {
    leaves: HashMap<TermId, ModelValue>,
    selects: HashMap<TermId, ModelValue>,
}

impl ArraySelectStubModel {
    fn new() -> Self {
        Self {
            leaves: HashMap::new(),
            selects: HashMap::new(),
        }
    }
    fn leaf(mut self, t: TermId, v: ModelValue) -> Self {
        self.leaves.insert(t, v);
        self
    }
    fn sel(mut self, t: TermId, v: ModelValue) -> Self {
        self.selects.insert(t, v);
        self
    }
}

impl ModelView for ArraySelectStubModel {
    fn leaf_value(&self, t: TermId) -> Option<ModelValue> {
        self.leaves.get(&t).cloned()
    }
    fn array_select_value(&self, t: TermId) -> Option<ModelValue> {
        self.selects.get(&t).cloned()
    }
}

#[test]
fn array_select_seed21011_distinct_indices_equal_reads_refute() {
    // The seed-21011 shape: `(< (select A0 idx1) (select A0 idx2))` with DISTINCT
    // index values (idx1 = 0, idx2 = -5) that the model reads to the SAME element
    // (both 1). The array leaf A0 is NOT reconstructable (unpinned), so the gate
    // reads each `select` through the model; the two reads key differently
    // (distinct index values) and keep their committed value 1, so `(< 1 1)` is
    // `false` — a caught wrong witness. Pinning that array model into z3 is
    // UNSAT; the gate demotes the `sat` to `unknown`.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort); // deliberately unpinned as a leaf
    let idx1 = ts.mk_int(int(0));
    let idx2 = ts.mk_int(int(-5));
    let sel1 = app(&mut ts, "select", &[a0, idx1], Sort::Int);
    let sel2 = app(&mut ts, "select", &[a0, idx2], Sort::Int);
    let lt = app(&mut ts, "<", &[sel1, sel2], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .sel(sel1, ModelValue::Int(int(1)))
        .sel(sel2, ModelValue::Int(int(1)));
    assert_violates(&verdict(&ts, &m, &[lt]));
}

#[test]
fn array_select_collapsed_indices_refute_strict_inequality() {
    // Collapse analogue of the UF case: two reads of the SAME array A0 at index
    // values that COINCIDE (i = 0 and 3*i = 0) must denote the same element, yet
    // the model pins them to different values (5 and 7). The gate collapses them
    // to one value (first-wins), so `(> read read)` is `false`. Honouring the
    // per-read pins (7 > 5) would confirm an internally-inconsistent array model;
    // the value-keyed graph exposes it instead.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort); // unpinned leaf
    let i = ts.mk_var("i", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i], Sort::Int); // 3*i = 0
    let sel_lo = app(&mut ts, "select", &[a0, i], Sort::Int); // A0[i]
    let sel_hi = app(&mut ts, "select", &[a0, mul], Sort::Int); // A0[3*i]
    let gt = app(&mut ts, ">", &[sel_hi, sel_lo], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(i, ModelValue::Int(int(0)))
        .sel(sel_hi, ModelValue::Int(int(7)))
        .sel(sel_lo, ModelValue::Int(int(5)));
    assert_violates(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_via_model_distinct_reads_confirm_valid_model() {
    // NO OVER-REFUTATION: distinct index values (a = 5, b = 7) key the two reads
    // differently, so each keeps its own committed value (A0[a] = 1 > A0[b] = 0)
    // and the witness is CONFIRMED. The select-via-model fallback must not
    // over-refute a genuinely-valid array model.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let sel_a = app(&mut ts, "select", &[a0, a], Sort::Int);
    let sel_b = app(&mut ts, "select", &[a0, b], Sort::Int);
    let gt = app(&mut ts, ">", &[sel_a, sel_b], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(a, ModelValue::Int(int(5)))
        .leaf(b, ModelValue::Int(int(7)))
        .sel(sel_a, ModelValue::Int(int(1)))
        .sel(sel_b, ModelValue::Int(int(0)));
    assert_confirmed(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_coincident_reads_confirm_when_consistent() {
    // NO OVER-REFUTATION under coincidence: two reads of the same array at
    // coinciding index values (i = 0, 3*i = 0) that the model pins CONSISTENTLY
    // (both 4). `(= A0[i] A0[3*i])` is `(= 4 4)` = true — the single-valuedness
    // collapse yields the shared value, not a spurious violation.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let i = ts.mk_var("i", Sort::Int);
    let three = ts.mk_int(int(3));
    let mul = app(&mut ts, "*", &[three, i], Sort::Int);
    let sel_lo = app(&mut ts, "select", &[a0, i], Sort::Int);
    let sel_hi = app(&mut ts, "select", &[a0, mul], Sort::Int);
    let eq = app(&mut ts, "=", &[sel_lo, sel_hi], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(i, ModelValue::Int(int(0)))
        .sel(sel_lo, ModelValue::Int(int(4)))
        .sel(sel_hi, ModelValue::Int(int(4)));
    assert_confirmed(&verdict(&ts, &m, &[eq]));
}

#[test]
fn array_select_unpinned_read_cannot_confirm() {
    // If neither the array leaf NOR the per-read value is pinned, the `select` is
    // unevaluable and the gate fails closed (never assumed) — CannotConfirm.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let a = ts.mk_var("a", Sort::Int);
    let sel = app(&mut ts, "select", &[a0, a], Sort::Int);
    let zero = ts.mk_int(int(0));
    let gt = app(&mut ts, ">", &[sel, zero], Sort::Bool);
    let m = ArraySelectStubModel::new().leaf(a, ModelValue::Int(int(5))); // no select pin
    assert_cannot(&verdict(&ts, &m, &[gt]));
}

#[test]
fn array_select_reconstructable_leaf_still_uses_structural_path() {
    // When the array leaf IS reconstructable (pinned as a concrete array value),
    // the structural path handles the read and the model's per-read pins are
    // IGNORED — even a contradictory per-read pin cannot override the real array.
    // `(= (select A0 1) 9)` with A0 = const-0 is `(= 0 9)` = false (structural),
    // regardless of a bogus `array_select_value` pin of 9.
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort);
    let one = ts.mk_int(int(1));
    let nine = ts.mk_int(int(9));
    let sel = app(&mut ts, "select", &[a0, one], Sort::Int);
    let eq = app(&mut ts, "=", &[sel, nine], Sort::Bool);
    let m = ArraySelectStubModel::new()
        .leaf(
            a0,
            ModelValue::Array(Box::new(ArrayValue {
                default: ModelValue::Int(int(0)),
                store: vec![],
            })),
        )
        .sel(sel, ModelValue::Int(int(9))); // bogus pin — must be ignored
    assert_violates(&verdict(&ts, &m, &[eq]));
}

#[test]
fn seed21425_shape_emitted_array_model_is_refuted() {
    // Exact seed-21425 shape (arrays fuzz) with the INVALID array model AY
    // emitted (its get-model output pins UNSAT in z3). Given that emitted model
    // as leaf values, the gate's array-`select` evaluation ground-falsifies AY's
    // own assertion — `(= -5 (select A0 -5))` is `(= -5 0)` under the emitted
    // A0 = store(const 0, -3, 2) — and reports ModelViolates. This localizes the
    // (separate, deeper) AUFLIA residual to model RECONSTRUCTION/COMPLETION: the
    // gate's evaluation is correct; the emitted array's default is simply not
    // present in `array_model` at gate time (see report).
    let mut ts = TermStore::new();
    let asort = Sort::array(Sort::Int, Sort::Int);
    let a0 = ts.mk_var("A0", asort.clone());
    let a1 = ts.mk_var("A1", asort.clone());
    let a2 = ts.mk_var("A2", asort.clone());
    let i0 = ts.mk_var("i0", Sort::Int);
    let i1 = ts.mk_var("i1", Sort::Int);
    let i2 = ts.mk_var("i2", Sort::Int);
    let i3 = ts.mk_var("i3", Sort::Int);
    let b0 = ts.mk_var("b0", Sort::Bool);
    let n5 = ts.mk_int(int(-5));
    let n3 = ts.mk_int(int(-3));
    let n2 = ts.mk_int(int(-2));
    let two = ts.mk_int(int(2));
    let five = ts.mk_int(int(5));
    let six = ts.mk_int(int(6));
    let c24 = ts.mk_int(int(24));
    let four = ts.mk_int(int(4));
    // D1 = (< (select (store (store A0 -2 (- i1)) 6 i0) (+ i2 6)) (+ i0 (- i3)))
    let neg_i1 = app(&mut ts, "-", &[i1], Sort::Int);
    let s1 = app(&mut ts, "store", &[a0, n2, neg_i1], asort.clone());
    let s2 = app(&mut ts, "store", &[s1, six, i0], asort.clone());
    let i2p6 = app(&mut ts, "+", &[i2, six], Sort::Int);
    let sel_d1 = app(&mut ts, "select", &[s2, i2p6], Sort::Int);
    let neg_i3 = app(&mut ts, "-", &[i3], Sort::Int);
    let i0mi3 = app(&mut ts, "+", &[i0, neg_i3], Sort::Int);
    let d1 = app(&mut ts, "<", &[sel_d1, i0mi3], Sort::Bool);
    // A2eq = (= -5 (select A0 -5))
    let sel_a0m5 = app(&mut ts, "select", &[a0, n5], Sort::Int);
    let a2eq = app(&mut ts, "=", &[n5, sel_a0m5], Sort::Bool);
    // NEQ = (not (= (select A0 -3) (select (store (store A1 6 2) i0 (ite (<= 24 (+ i1 i3)) -3 i0)) i3)))
    let sel_a0m3 = app(&mut ts, "select", &[a0, n3], Sort::Int);
    let a1s1 = app(&mut ts, "store", &[a1, six, two], asort.clone());
    let i1pi3 = app(&mut ts, "+", &[i1, i3], Sort::Int);
    let le = app(&mut ts, "<=", &[c24, i1pi3], Sort::Bool);
    let ite = ts.mk_ite(le, n3, i0);
    let a1s2 = app(&mut ts, "store", &[a1s1, i0, ite], asort.clone());
    let sel_a1 = app(&mut ts, "select", &[a1s2, i3], Sort::Int);
    let eqn = app(&mut ts, "=", &[sel_a0m3, sel_a1], Sort::Bool);
    let neq = ts.mk_not(eqn);
    // C1 = (< (select A2 (+ i2 2)) (select A2 5))
    let i2p2 = app(&mut ts, "+", &[i2, two], Sort::Int);
    let sel_a2a = app(&mut ts, "select", &[a2, i2p2], Sort::Int);
    let sel_a2b = app(&mut ts, "select", &[a2, five], Sort::Int);
    let c1 = app(&mut ts, "<", &[sel_a2a, sel_a2b], Sort::Bool);
    // C2 = (< (select A2 i3) (select A1 4))
    let sel_a2c = app(&mut ts, "select", &[a2, i3], Sort::Int);
    let sel_a1b = app(&mut ts, "select", &[a1, four], Sort::Int);
    let c2 = app(&mut ts, "<", &[sel_a2c, sel_a1b], Sort::Bool);
    let and = app(&mut ts, "and", &[b0, a2eq, neq, c1, c2], Sort::Bool);
    let asrt = app(&mut ts, "or", &[d1, and], Sort::Bool);
    // AY's INVALID emitted model.
    let arr = |d: i64, kv: &[(i64, i64)]| {
        ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Int(int(d)),
            store: kv
                .iter()
                .map(|(k, v)| (ModelValue::Int(int(*k)), ModelValue::Int(int(*v))))
                .collect(),
        }))
    };
    let m = StubModel::new()
        .with(a0, arr(0, &[(-3, 2)]))
        .with(a1, arr(1, &[(4, 2)]))
        .with(a2, arr(0, &[(7, -1), (-4, 1)]))
        .with(i0, ModelValue::Int(int(-10)))
        .with(i1, ModelValue::Int(int(0)))
        .with(i2, ModelValue::Int(int(5)))
        .with(i3, ModelValue::Int(int(-4)))
        .with(b0, ModelValue::Bool(true));
    assert_violates(&verdict(&ts, &m, &[asrt]));
}

// ===========================================================================
// (d) The model-INDEPENDENT datatype-congruence NORMALIZER
//     (`is_datatype_tautology_with`): it must PROVE genuine free-datatype
//     tautologies AND REJECT every near-miss non-tautology (soundness).
// ===========================================================================

/// `Option`-like datatype: `None` (nullary) + `Some(value: Int)`.
fn option_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Opt",
        vec![
            DatatypeConstructor::new("None", vec![]),
            DatatypeConstructor::new("Some", vec![DatatypeField::new("value", Sort::Int)]),
        ],
    ))
}

/// Single-constructor datatype `Box = Mk(fst: Int, snd: Int)`.
fn box_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "Box",
        vec![DatatypeConstructor::new(
            "Mk",
            vec![
                DatatypeField::new("fst", Sort::Int),
                DatatypeField::new("snd", Sort::Int),
            ],
        )],
    ))
}

fn is_taut(ts: &TermStore, t: TermId) -> bool {
    is_datatype_tautology_with(ts, t, &|_| None)
}

#[test]
fn norm_proves_constructor_characterization() {
    // (= (= (Some v) x) (and (is-Some x) (= v (value x)))) — a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let v = ts.mk_var("v", Sort::Int);
    let some_v = app(&mut ts, "Some", &[v], opt.clone());
    let inner = app(&mut ts, "=", &[some_v, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let value_x = app(&mut ts, "value", &[x], Sort::Int);
    let feq = app(&mut ts, "=", &[v, value_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_some, feq], Sort::Bool);
    let bicond = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "constructor characterization must be proved"
    );
}

#[test]
fn norm_proves_is_ctor_roundtrip_and_sole_ctor() {
    // (= (is-Mk x) (= x (Mk (fst x) (snd x)))) — round-trip, sole ctor.
    let mut ts = TermStore::new();
    let bx = box_sort();
    let x = ts.mk_var("x", bx.clone());
    let is_mk = app(&mut ts, "is-Mk", &[x], Sort::Bool);
    let fst = app(&mut ts, "fst", &[x], Sort::Int);
    let snd = app(&mut ts, "snd", &[x], Sort::Int);
    let mk = app(&mut ts, "Mk", &[fst, snd], bx.clone());
    let eq = app(&mut ts, "=", &[x, mk], Sort::Bool);
    let bicond = app(&mut ts, "=", &[is_mk, eq], Sort::Bool);
    assert!(is_taut(&ts, bicond), "is-C round-trip must be proved");

    // Sole-constructor tester is a tautology: (is-Mk x).
    assert!(is_taut(&ts, is_mk), "sole-ctor tester must be proved");
}

#[test]
fn norm_proves_nullary_and_none_equality() {
    // None is nullary: (is-None None), (not (is-Some None)),
    // (= (= None x) (is-None x)).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let none = ts.mk_var("None", opt.clone()); // front-end lowering of `(None)`
    let x = ts.mk_var("x", opt.clone());
    let is_none_none = app(&mut ts, "is-None", &[none], Sort::Bool);
    assert!(is_taut(&ts, is_none_none), "is-None(None) must be proved");

    let is_some_none = app(&mut ts, "is-Some", &[none], Sort::Bool);
    let not_is_some = app(&mut ts, "not", &[is_some_none], Sort::Bool);
    assert!(
        is_taut(&ts, not_is_some),
        "(not is-Some(None)) must be proved"
    );

    let none_eq_x = app(&mut ts, "=", &[none, x], Sort::Bool);
    let is_none_x = app(&mut ts, "is-None", &[x], Sort::Bool);
    let bicond = app(&mut ts, "=", &[none_eq_x, is_none_x], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "(= (= None x)(is-None x)) must be proved"
    );
}

#[test]
fn norm_rejects_missing_field_characterization() {
    // SOUNDNESS near-miss: DROP the field equality.
    // (= (= (Some v) x) (is-Some x)) is NOT a tautology (needs v = value x).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let v = ts.mk_var("v", Sort::Int);
    let some_v = app(&mut ts, "Some", &[v], opt.clone());
    let inner = app(&mut ts, "=", &[some_v, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, is_some], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "dropping the field eq must NOT be proved (unsound)"
    );
}

#[test]
fn norm_rejects_wrong_field_and_bare_constructor_eq() {
    // (= (= (Some a) x) (and (is-Some x) (= b (value x)))) with a != b: NOT valid.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let inner = app(&mut ts, "=", &[some_a, x], Sort::Bool);
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let value_x = app(&mut ts, "value", &[x], Sort::Int);
    let feq_b = app(&mut ts, "=", &[b, value_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_some, feq_b], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "wrong field var must NOT be proved (unsound)"
    );

    // Bare (= (Some a) x) is NOT a tautology.
    assert!(
        !is_taut(&ts, inner),
        "bare constructor eq must NOT be proved"
    );

    // Injectivity is NOT vacuous: (= (Some a)(Some b)) is NOT a tautology.
    let some_b = app(&mut ts, "Some", &[b], opt.clone());
    let inj = app(&mut ts, "=", &[some_a, some_b], Sort::Bool);
    assert!(
        !is_taut(&ts, inj),
        "(= (Some a)(Some b)) must NOT be proved"
    );
}

#[test]
fn norm_rejects_two_ctor_tester_and_distinctness_confusion() {
    // (is-Some x) for the 2-ctor Opt with x free: NOT a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let is_some = app(&mut ts, "is-Some", &[x], Sort::Bool);
    assert!(
        !is_taut(&ts, is_some),
        "2-ctor tester on free var must NOT be proved"
    );

    // (= (Some a) None) reduces to false; asserting it is NOT a tautology,
    // but its NEGATION is: (not (= (Some a) None)).
    let a = ts.mk_var("a", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let none = ts.mk_var("None", opt.clone());
    let eq = app(&mut ts, "=", &[some_a, none], Sort::Bool);
    assert!(
        !is_taut(&ts, eq),
        "(= (Some a) None) must NOT be proved true"
    );
    let neg = app(&mut ts, "not", &[eq], Sort::Bool);
    assert!(
        is_taut(&ts, neg),
        "distinct constructors: negation IS a tautology"
    );
}

#[test]
fn norm_proves_injectivity_biconditional() {
    // (= (= (Some a) (Some b)) (= a b)) — injectivity, a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let a = ts.mk_var("a", Sort::Int);
    let b = ts.mk_var("b", Sort::Int);
    let some_a = app(&mut ts, "Some", &[a], opt.clone());
    let some_b = app(&mut ts, "Some", &[b], opt.clone());
    let lhs = app(&mut ts, "=", &[some_a, some_b], Sort::Bool);
    let rhs = app(&mut ts, "=", &[a, b], Sort::Bool);
    let bicond = app(&mut ts, "=", &[lhs, rhs], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "injectivity biconditional must be proved"
    );
}

#[test]
fn norm_proves_nested_datatype_field_characterization() {
    // Mirrors g4: PbConstraint_mk(fld_terms: Vec, ...) where Vec is itself a
    // single-ctor datatype. The congruence axiom over a NESTED constructor field
    // must characterize recursively through the selector path.
    let mut ts = TermStore::new();
    let vec_s = Sort::Datatype(DatatypeSort::new(
        "Vec",
        vec![DatatypeConstructor::new(
            "Vmk",
            vec![DatatypeField::new("data", Sort::Int)],
        )],
    ));
    let pc = Sort::Datatype(DatatypeSort::new(
        "PC",
        vec![DatatypeConstructor::new(
            "Pmk",
            vec![
                DatatypeField::new("terms", vec_s.clone()),
                DatatypeField::new("rhs", Sort::Int),
            ],
        )],
    ));
    let x = ts.mk_var("x", pc.clone());
    let d = ts.mk_var("d", Sort::Int);
    let rhs = ts.mk_var("rhs", Sort::Int);
    let vmk = app(&mut ts, "Vmk", &[d], vec_s.clone());
    let pmk = app(&mut ts, "Pmk", &[vmk, rhs], pc.clone());
    let inner = app(&mut ts, "=", &[pmk, x], Sort::Bool);
    // RHS: (and (is-Pmk x) (= (Vmk d) (terms x)) (= rhs (rhs x)))
    let is_pmk = app(&mut ts, "is-Pmk", &[x], Sort::Bool);
    let terms_x = app(&mut ts, "terms", &[x], vec_s.clone());
    let vmk2 = app(&mut ts, "Vmk", &[d], vec_s.clone());
    let eq_terms = app(&mut ts, "=", &[vmk2, terms_x], Sort::Bool);
    let rhs_x = app(&mut ts, "rhs", &[x], Sort::Int);
    let eq_rhs = app(&mut ts, "=", &[rhs, rhs_x], Sort::Bool);
    let conj = app(&mut ts, "and", &[is_pmk, eq_terms, eq_rhs], Sort::Bool);
    let bicond = app(&mut ts, "=", &[inner, conj], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "nested-field constructor characterization must be proved"
    );

    // SOUNDNESS near-miss: swap the nested field var d -> e (e != d).
    let e = ts.mk_var("e", Sort::Int);
    let vmk_e = app(&mut ts, "Vmk", &[e], vec_s.clone());
    let eq_terms_bad = app(&mut ts, "=", &[vmk_e, terms_x], Sort::Bool);
    let conj_bad = app(&mut ts, "and", &[is_pmk, eq_terms_bad, eq_rhs], Sort::Bool);
    let bad = app(&mut ts, "=", &[inner, conj_bad], Sort::Bool);
    assert!(
        !is_taut(&ts, bad),
        "mismatched nested field must NOT be proved (unsound)"
    );
}

#[test]
fn norm_proves_structural_equality_characterization_two_ctor() {
    // (= (= None x) (and (= (is-None x)(is-None None)) (= (is-Some x)(is-Some None))
    //                    (or (not (is-Some None)) (= (value x)(value None)))))
    // — the full 2-ctor structural-equality axiom; a tautology.
    let mut ts = TermStore::new();
    let opt = option_sort();
    let none = ts.mk_var("None", opt.clone());
    let x = ts.mk_var("x", opt.clone());
    let none_eq_x = app(&mut ts, "=", &[none, x], Sort::Bool);
    let isn_x = app(&mut ts, "is-None", &[x], Sort::Bool);
    let isn_n = app(&mut ts, "is-None", &[none], Sort::Bool);
    let e1 = app(&mut ts, "=", &[isn_x, isn_n], Sort::Bool);
    let iss_x = app(&mut ts, "is-Some", &[x], Sort::Bool);
    let iss_n = app(&mut ts, "is-Some", &[none], Sort::Bool);
    let e2 = app(&mut ts, "=", &[iss_x, iss_n], Sort::Bool);
    let not_iss_n = app(&mut ts, "not", &[iss_n], Sort::Bool);
    let val_x = app(&mut ts, "value", &[x], Sort::Int);
    let val_n = app(&mut ts, "value", &[none], Sort::Int);
    let e3v = app(&mut ts, "=", &[val_x, val_n], Sort::Bool);
    let e3 = app(&mut ts, "or", &[not_iss_n, e3v], Sort::Bool);
    let big = app(&mut ts, "and", &[e1, e2, e3], Sort::Bool);
    let bicond = app(&mut ts, "=", &[none_eq_x, big], Sort::Bool);
    assert!(
        is_taut(&ts, bicond),
        "2-ctor structural-eq characterization must be proved"
    );
}

#[test]
fn norm_two_ctor_exclusivity_is_not_overreaching() {
    // SOUNDNESS: is-None(x) alone is NOT a tautology; nor is is-Some(x); nor their
    // conjunction; but their disjunction IS (exhaustiveness).
    let mut ts = TermStore::new();
    let opt = option_sort();
    let x = ts.mk_var("x", opt.clone());
    let isn = app(&mut ts, "is-None", &[x], Sort::Bool);
    let iss = app(&mut ts, "is-Some", &[x], Sort::Bool);
    assert!(!is_taut(&ts, isn), "is-None(x) must NOT be a tautology");
    assert!(!is_taut(&ts, iss), "is-Some(x) must NOT be a tautology");
    let conj = app(&mut ts, "and", &[isn, iss], Sort::Bool);
    assert!(
        !is_taut(&ts, conj),
        "is-None ∧ is-Some must NOT be a tautology"
    );
    let disj = app(&mut ts, "or", &[isn, iss], Sort::Bool);
    assert!(
        is_taut(&ts, disj),
        "is-None ∨ is-Some IS a tautology (exhaustive)"
    );
}

// ===========================================================================
// (e) Residual free-datatype-array joint-satisfiability
//     (#free-dt-array-residual): a residue consisting ONLY of alias
//     equalities and ground element reads over FREE datatype-element arrays
//     confirms iff no two constraints force different values at one
//     (class, index, field) slot. Everything else stays fail-closed.
// ===========================================================================

/// Datatype `S = mk(f: Int, g: Int)` and its array sort `(Array Int S)`.
fn struct_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "S",
        vec![DatatypeConstructor::new(
            "mk",
            vec![
                DatatypeField::new("f", Sort::Int),
                DatatypeField::new("g", Sort::Int),
            ],
        )],
    ))
}

/// `(= <ground-int> (fld (select arr idx)))` — a field read over `arr`.
fn field_read_eq(
    ts: &mut TermStore,
    fld: &str,
    arr: TermId,
    idx: TermId,
    ground: TermId,
) -> TermId {
    let sel = app(ts, "select", &[arr, idx], struct_sort());
    let prj = app(ts, fld, &[sel], Sort::Int);
    app(ts, "=", &[ground, prj], Sort::Bool)
}

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

// --- seq.last_indexof / seq.replace_all value-level parity (#p0.1-seq) ------
//
// These VALUE-level tests pin the independent-gate evaluator's semantics for
// `seq.last_indexof` and `seq.replace_all` against HAND-COMPUTED SMT-LIB
// results. z3 4.15.4 is deliberately NOT used as the oracle here: it does not
// recognise `seq.replace_all` at all ("unknown constant") and it computes
// WRONG `seq.last_indexof` values (its rightmost-of-[5,5] for [5] is neither 0
// nor 1). The gate must therefore be validated against the specification, and
// its implementation is kept independent of the solver's own evaluator
// (crate::seq uses `match_at`; the solver uses inline loops) so a shared bug
// cannot mutually confirm a wrong `sat`.

fn mvseq_i(xs: &[i64]) -> ModelValue {
    ModelValue::Seq(xs.iter().map(|&n| ModelValue::Int(int(n))).collect())
}

fn li(s: &[i64], sub: &[i64]) -> BigInt {
    match seq::eval("seq.last_indexof", &[mvseq_i(s), mvseq_i(sub)]).unwrap() {
        ModelValue::Int(n) => n,
        other => panic!("expected Int, got {other:?}"),
    }
}

fn ra(s: &[i64], src: &[i64], dst: &[i64]) -> Vec<i64> {
    match seq::eval("seq.replace_all", &[mvseq_i(s), mvseq_i(src), mvseq_i(dst)]).unwrap() {
        ModelValue::Seq(v) => v
            .into_iter()
            .map(|e| match e {
                ModelValue::Int(n) => n.try_into().unwrap(),
                other => panic!("expected Int element, got {other:?}"),
            })
            .collect(),
        other => panic!("expected Seq, got {other:?}"),
    }
}

#[test]
fn seq_last_indexof_semantics() {
    assert_eq!(li(&[5, 5, 5], &[5]), int(2)); // rightmost tie
    assert_eq!(li(&[5, 5], &[5]), int(1)); // z3-4.15.4 gets THIS wrong
    assert_eq!(li(&[9, 1, 2], &[9]), int(0)); // single leftmost occurrence
    assert_eq!(li(&[5, 6], &[9]), int(-1)); // not found
    assert_eq!(li(&[5, 6, 7], &[]), int(3)); // empty needle -> |s|
    assert_eq!(li(&[], &[]), int(0)); // empty haystack + empty needle
    assert_eq!(li(&[1], &[1, 1]), int(-1)); // needle longer than haystack
    assert_eq!(li(&[1, 1, 1], &[1, 1]), int(1)); // rightmost multi-element match
}

#[test]
fn seq_replace_all_semantics() {
    assert_eq!(ra(&[1, 2, 1], &[1], &[9]), vec![9, 2, 9]); // both occurrences
    assert_eq!(ra(&[1, 1, 1], &[1, 1], &[0]), vec![0, 1]); // non-overlapping l-to-r
    assert_eq!(ra(&[1, 2], &[], &[9]), vec![1, 2]); // empty src -> unchanged
    assert_eq!(ra(&[1, 2], &[3], &[9]), vec![1, 2]); // not found -> unchanged
    assert_eq!(ra(&[1, 2], &[1], &[8, 8]), vec![8, 8, 2]); // expanding dst
    assert_eq!(ra(&[1, 2, 1], &[1], &[]), vec![2]); // deleting dst
    assert_eq!(ra(&[1, 1], &[1, 1], &[9]), vec![9]); // whole-sequence match
}
