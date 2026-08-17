// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests` to preserve test FQNs.

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
fn bool_index_array_full_store_coverage_hides_differing_defaults() {
    // Both arrays denote the constant-zero function over Bool: the left array's
    // two stores cover the complete index domain, so its default `1` is
    // unreachable. The typed comparator must use Bool's exact cardinality and
    // refute `(distinct left right)` instead of treating the defaults as
    // evidence that the arrays differ.
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Int);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let false_index = ts.mk_bool(false);
    let true_index = ts.mk_bool(true);
    let one_default = app(&mut ts, "const-array", &[one], array_sort.clone());
    let with_false = app(
        &mut ts,
        "store",
        &[one_default, false_index, zero],
        array_sort.clone(),
    );
    let fully_covered = app(
        &mut ts,
        "store",
        &[with_false, true_index, zero],
        array_sort.clone(),
    );
    let zero_default = app(&mut ts, "const-array", &[zero], array_sort);
    let disequality = app(
        &mut ts,
        "distinct",
        &[fully_covered, zero_default],
        Sort::Bool,
    );

    assert_violates(&verdict(&ts, &StubModel::new(), &[disequality]));
}

#[test]
fn int_index_array_differing_defaults_prove_disequality() {
    // A finite store chain cannot cover Int. At some unwritten index the left
    // array reads 1 and the right array reads 0, so they are extensionally
    // distinct even though the one explicit store makes their reads agree at 5.
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let five = ts.mk_int(int(5));
    let one_default = app(&mut ts, "const-array", &[one], array_sort.clone());
    let zero_default = app(&mut ts, "const-array", &[zero], array_sort.clone());
    let stored_zero = app(&mut ts, "store", &[one_default, five, zero], array_sort);
    let disequality = app(
        &mut ts,
        "distinct",
        &[stored_zero, zero_default],
        Sort::Bool,
    );

    assert_confirmed(&verdict(&ts, &StubModel::new(), &[disequality]));
}

#[test]
fn bool_index_array_partial_store_coverage_exposes_differing_defaults() {
    // Only `false` is overwritten, leaving `true` to observe the differing
    // defaults. Exact finite-domain accounting therefore proves disequality.
    let mut ts = TermStore::new();
    let array_sort = Sort::array(Sort::Bool, Sort::Int);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let false_index = ts.mk_bool(false);
    let one_default = app(&mut ts, "const-array", &[one], array_sort.clone());
    let with_false = app(
        &mut ts,
        "store",
        &[one_default, false_index, zero],
        array_sort.clone(),
    );
    let zero_default = app(&mut ts, "const-array", &[zero], array_sort);
    let disequality = app(&mut ts, "distinct", &[with_false, zero_default], Sort::Bool);

    assert_confirmed(&verdict(&ts, &StubModel::new(), &[disequality]));
}

#[test]
fn uninterpreted_index_array_coverage_remains_fail_closed() {
    // The carrier may contain only `k`, in which case the store covers it and
    // the defaults are unreachable; or it may contain another element, in which
    // case the defaults prove disequality. The model checker has no cardinality
    // theorem for an uninterpreted sort, so it must not choose either answer.
    let mut ts = TermStore::new();
    let index_sort = Sort::Uninterpreted("U".to_string());
    let array_sort = Sort::array(index_sort.clone(), Sort::Int);
    let key = ts.mk_var("k", index_sort);
    let zero = ts.mk_int(int(0));
    let one = ts.mk_int(int(1));
    let one_default = app(&mut ts, "const-array", &[one], array_sort.clone());
    let with_key = app(
        &mut ts,
        "store",
        &[one_default, key, zero],
        array_sort.clone(),
    );
    let zero_default = app(&mut ts, "const-array", &[zero], array_sort);
    let disequality = app(&mut ts, "distinct", &[with_key, zero_default], Sort::Bool);
    let model = StubModel::new().with(key, ModelValue::Uninterpreted("u!0".to_string()));

    assert_cannot(&verdict(&ts, &model, &[disequality]));
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
