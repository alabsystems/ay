// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{Executor, Model};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::Symbol;
use ay_core::Sort;
use ay_frontend::parse;
use ay_seq::SeqModel;
use num_bigint::BigInt;
use num_rational::BigRational;

fn completed_seq(model: &Model, term: ay_core::TermId) -> &Vec<super::EvalValue> {
    match model.completed_values.get(&term) {
        Some(super::EvalValue::Seq(elems)) => elems,
        other => panic!("expected concrete completed sequence, got {other:?}"),
    }
}

fn declared_seq_var(exec: &mut Executor, name: &str, sort: Sort) -> ay_core::TermId {
    let term = exec.ctx.terms.mk_var(name, sort.clone());
    exec.ctx.register_symbol(name.to_string(), term, sort);
    term
}

#[test]
fn authenticated_datatype_carriers_are_narrow_without_a_bv_model() {
    let commands = parse(
        "(declare-datatype U ((mk (g (Array Int Bool)))))\
             (declare-fun f (Int) U)",
    )
    .expect("datatype carrier fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("datatype carrier declarations execute");
    let sort = Sort::Uninterpreted("U".to_string());
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let f0 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [zero], sort.clone());
    let f1 = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), [one], sort.clone());
    let ineligible = declared_seq_var(&mut exec, "dt-ineligible", sort);
    let equal = exec.ctx.terms.mk_eq(f0, f1);
    let ineligible_root = exec.ctx.terms.mk_eq(ineligible, ineligible);
    exec.ctx.assertions.extend([equal, ineligible_root]);
    let eligible: HashSet<_> = [f0, f1].into_iter().collect();
    let mut model = Model::empty();
    assert!(model.bv_model.is_none());

    exec.complete_uninterpreted_sort_model(&mut model, &[], Some(&eligible));

    let euf = model
        .euf_model
        .as_ref()
        .expect("eligible datatype terms receive EUF carriers");
    assert_eq!(euf.term_values.get(&f0), euf.term_values.get(&f1));
    assert!(euf.term_values.contains_key(&f0));
    assert!(!euf.term_values.contains_key(&ineligible));
}

#[test]
fn nested_sat_true_sequence_equality_gets_one_model_class_without_bv() {
    let mut exec = Executor::new();
    exec.set_self_check(true);
    let seq_int = Sort::Seq(Box::new(Sort::Int));
    let x = declared_seq_var(&mut exec, "seq-class-x", seq_int.clone());
    let y = declared_seq_var(&mut exec, "seq-class-y", seq_int.clone());
    let z = declared_seq_var(&mut exec, "seq-class-z", seq_int);
    let equal = exec.ctx.terms.mk_eq(x, y);
    let guard = exec.ctx.terms.mk_var("seq-class-guard", Sort::Bool);
    let nested = exec.ctx.terms.mk_or(vec![equal, guard]);
    let distinct = exec.ctx.terms.mk_distinct(vec![x, z]);
    exec.self_check_authored_assertions = Some(vec![nested, distinct]);
    assert!(exec.ctx.assertions.is_empty());

    let mut model = Model::empty();
    model.sat_model = vec![true];
    model.term_to_var.insert(equal, 0);
    assert!(model.bv_model.is_none());

    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert_eq!(completed_seq(&model, x), completed_seq(&model, y));
    assert_ne!(completed_seq(&model, x), completed_seq(&model, z));
    assert!(model.euf_model.as_ref().is_none_or(|euf| {
        [x, y, z].iter().all(|term| {
            !euf.term_values
                .get(term)
                .is_some_and(|v| v.starts_with("@ay-seq"))
        })
    }));
}

#[test]
fn default_completion_ignores_independent_gate_only_authored_roots() {
    let mut exec = Executor::new();
    let seq_int = Sort::Seq(Box::new(Sort::Int));
    let x = declared_seq_var(&mut exec, "seq-gate-only-x", seq_int.clone());
    let y = declared_seq_var(&mut exec, "seq-gate-only-y", seq_int.clone());
    let z = declared_seq_var(&mut exec, "seq-gate-only-z", seq_int);
    let equal = exec.ctx.terms.mk_eq(x, y);
    let guard = exec.ctx.terms.mk_var("seq-gate-only-guard", Sort::Bool);
    let nested = exec.ctx.terms.mk_or(vec![equal, guard]);
    let distinct = exec.ctx.terms.mk_distinct(vec![x, z]);
    exec.independent_gate_authored_assertions = Some(vec![nested, distinct]);
    assert!(!exec.self_check(), "the regression exercises default mode");
    assert!(exec.self_check_authored_assertions.is_none());
    assert!(exec.ctx.assertions.is_empty());

    let mut model = Model::empty();
    model.sat_model = vec![true];
    model.term_to_var.insert(equal, 0);

    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert!(
        [x, y, z]
            .iter()
            .all(|term| !model.completed_values.contains_key(term)),
        "installing independent-gate roots must not make default model \
             completion consume self-check-only carrier roots"
    );
}

#[test]
fn nested_sat_false_sequence_equality_does_not_merge_classes() {
    let mut exec = Executor::new();
    let seq_int = Sort::Seq(Box::new(Sort::Int));
    let x = declared_seq_var(&mut exec, "seq-false-x", seq_int.clone());
    let y = declared_seq_var(&mut exec, "seq-false-y", seq_int);
    let equal = exec.ctx.terms.mk_eq(x, y);
    let guard = exec.ctx.terms.mk_var("seq-false-guard", Sort::Bool);
    let nested = exec.ctx.terms.mk_or(vec![equal, guard]);
    exec.ctx.assertions.push(nested);

    let mut model = Model::empty();
    model.sat_model = vec![false];
    model.term_to_var.insert(equal, 0);

    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert_ne!(
        completed_seq(&model, x),
        completed_seq(&model, y),
        "a nested equality assigned false must not merge its operands"
    );
}

#[test]
fn sequence_completion_reuses_an_existing_model_class() {
    let mut exec = Executor::new();
    let seq_int = Sort::Seq(Box::new(Sort::Int));
    let x = declared_seq_var(&mut exec, "seq-existing-x", seq_int.clone());
    let y = declared_seq_var(&mut exec, "seq-existing-y", seq_int);
    let equal = exec.ctx.terms.mk_eq(x, y);
    exec.ctx.assertions.push(equal);

    let mut model = Model::empty();
    let mut euf = ay_euf::EufModel::default();
    euf.term_values.insert(x, "model-class-7".to_string());
    model.euf_model = Some(euf);

    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert_eq!(completed_seq(&model, x), completed_seq(&model, y));
    assert!(matches!(
        model.euf_model.as_ref().and_then(|euf| euf.term_values.get(&x)),
        Some(value) if value == "model-class-7"
    ));
}

#[test]
fn conflicting_concrete_sequences_forced_equal_do_not_fill_missing_member() {
    let mut exec = Executor::new();
    let seq_int = Sort::Seq(Box::new(Sort::Int));
    let x = declared_seq_var(&mut exec, "seq-conflict-x", seq_int.clone());
    let y = declared_seq_var(&mut exec, "seq-conflict-y", seq_int.clone());
    let missing = declared_seq_var(&mut exec, "seq-conflict-missing", seq_int);
    let xy = exec.ctx.terms.mk_eq(x, y);
    let ym = exec.ctx.terms.mk_eq(y, missing);
    exec.ctx.assertions.extend([xy, ym]);

    let mut model = Model::empty();
    let mut values = HashMap::default();
    values.insert(x, Vec::new());
    values.insert(y, vec!["7".to_string()]);
    model.seq_model = Some(SeqModel { values });

    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert!(
        !model.completed_values.contains_key(&missing),
        "a conflicting concrete class must remain unresolved and fail closed"
    );
}

#[test]
fn concrete_sequence_class_is_propagated_without_an_opaque_identity() {
    let mut exec = Executor::new();
    let seq_int = Sort::Seq(Box::new(Sort::Int));
    let concrete = declared_seq_var(&mut exec, "seq-concrete", seq_int.clone());
    let missing = declared_seq_var(&mut exec, "seq-missing", seq_int);
    let equal = exec.ctx.terms.mk_eq(concrete, missing);
    exec.ctx.assertions.push(equal);

    let mut model = Model::empty();
    let mut values = HashMap::default();
    values.insert(concrete, vec!["11".to_string()]);
    model.seq_model = Some(SeqModel { values });

    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert_eq!(
        completed_seq(&model, concrete),
        completed_seq(&model, missing)
    );
    assert_eq!(completed_seq(&model, missing).len(), 1);
    assert!(model.euf_model.as_ref().is_none_or(|euf| {
        !euf.term_values
            .get(&missing)
            .is_some_and(|v| v.starts_with("@ay-seq"))
    }));
}

#[test]
fn native_sequence_term_anchors_class_but_is_never_completed() {
    let mut exec = Executor::new();
    let seq_int = Sort::Seq(Box::new(Sort::Int));
    let x = declared_seq_var(&mut exec, "seq-native-anchor-x", seq_int.clone());
    let seven = exec.ctx.terms.mk_int(BigInt::from(7));
    let unit = exec
        .ctx
        .terms
        .mk_app(Symbol::Named("seq.unit".to_string()), vec![seven], seq_int);
    let equal = exec.ctx.terms.mk_eq(x, unit);
    exec.ctx.assertions.push(equal);

    let mut model = Model::empty();
    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert_eq!(completed_seq(&model, x).len(), 1);
    assert_eq!(
        completed_seq(&model, x)[0],
        super::EvalValue::Rational(BigRational::from_integer(BigInt::from(7)))
    );
    assert!(
        !model.completed_values.contains_key(&unit),
        "native seq.unit is a semantic class anchor, never a completion target"
    );
}

#[test]
fn opaque_uninterpreted_elements_do_not_become_public_sequence_witnesses() {
    let mut exec = Executor::new();
    let elem = Sort::Uninterpreted("SeqElem".to_string());
    let seq = Sort::Seq(Box::new(elem));
    let x = declared_seq_var(&mut exec, "seq-uninterp-x", seq.clone());
    let y = declared_seq_var(&mut exec, "seq-uninterp-y", seq);
    let distinct = exec.ctx.terms.mk_distinct(vec![x, y]);
    exec.ctx.assertions.push(distinct);

    let mut model = Model::empty();
    exec.complete_uninterpreted_sort_model(&mut model, &[], None);

    assert!(model.completed_values.get(&x).is_none());
    assert!(model.completed_values.get(&y).is_none());
    assert_eq!(
        exec.last_statistics
            .get_int("model_completion.sequence_budget_or_value_blocked"),
        Some(1)
    );
}

#[test]
fn sequence_completion_cell_budget_has_exact_fail_closed_boundary() {
    // Lengths 0..63 consume 2016 cells in class representatives and 2016
    // more in per-term completed values: 4032 <= the 4096-cell budget.
    // Adding class 64 would consume 4160 total cells and must commit none.
    for (classes, should_complete) in [(64usize, true), (65usize, false)] {
        let mut exec = Executor::new();
        let seq = Sort::Seq(Box::new(Sort::Int));
        let vars: Vec<_> = (0..classes)
            .map(|idx| {
                declared_seq_var(
                    &mut exec,
                    &format!("seq-budget-{classes}-{idx}"),
                    seq.clone(),
                )
            })
            .collect();
        let distinct = exec.ctx.terms.mk_distinct(vars.clone());
        exec.ctx.assertions.push(distinct);
        let mut model = Model::empty();

        exec.complete_uninterpreted_sort_model(&mut model, &[], None);

        assert_eq!(
            vars.iter()
                .all(|term| model.completed_values.contains_key(term)),
            should_complete,
            "unexpected completion decision for {classes} classes"
        );
        if !should_complete {
            assert!(vars
                .iter()
                .all(|term| !model.completed_values.contains_key(term)));
            assert_eq!(
                exec.last_statistics
                    .get_int("model_completion.sequence_budget_or_value_blocked"),
                Some(1)
            );
        }
    }
}

#[test]
fn equality_only_sequence_model_and_values_round_trip_without_opaque_tokens() {
    let input = "\
(set-logic QF_SEQ)\n\
(set-option :produce-models true)\n\
(declare-const x (Seq Int))\n\
(declare-const y (Seq Int))\n\
(declare-const z (Seq Int))\n\
(assert (= x y))\n\
(assert (distinct x z))\n\
(check-sat)\n\
(get-model)\n\
(get-value (x y z))";
    let commands = parse(input).expect("valid sequence equality query");
    let mut exec = Executor::new();
    exec.set_self_check(true);
    let outputs = exec.execute_all(&commands).expect("query executes");
    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let model = outputs.get(1).expect("get-model output");
    let values = outputs.get(2).expect("get-value output");
    assert!(!model.contains("@ay-seq"), "opaque class leaked: {model}");
    assert!(!values.contains("@ay-seq"), "opaque class leaked: {values}");
    assert!(model.contains("(define-fun x () (Seq Int)"));
    assert!(model.contains("(define-fun y () (Seq Int)"));
    assert!(model.contains("(define-fun z () (Seq Int)"));

    // Re-feed the emitted definitions as an ordinary SMT-LIB query. This
    // checks both syntax and semantics: the concrete model must still make
    // x=y and x!=z true, and its get-value answers must match the original.
    let definitions = model
        .strip_prefix("(model\n")
        .and_then(|body| body.strip_suffix("\n)"))
        .expect("canonical model response");
    let replay = format!(
        "(set-logic QF_SEQ)\n{definitions}\n\
             (assert (= x y))\n\
             (assert (distinct x z))\n\
             (check-sat)\n\
             (get-value (x y z))"
    );
    let replay_commands = parse(&replay).expect("emitted model reparses");
    let mut replay_exec = Executor::new();
    let replay_outputs = replay_exec
        .execute_all(&replay_commands)
        .expect("emitted model re-executes");
    assert_eq!(replay_outputs.first().map(String::as_str), Some("sat"));
    assert_eq!(replay_outputs.get(1), Some(values));
}

#[test]
fn sequence_semantic_builtins_cannot_be_repaired_into_sat() {
    let cases = [
        "(assert (= (seq.len (seq.unit 7)) 0))",
        "(assert (distinct (seq.++ (seq.unit 1) (seq.unit 2)) \
                               (seq.++ (seq.unit 1) (seq.unit 2))))",
        "(assert (distinct (seq.extract (seq.unit 1) 0 1) (seq.unit 1)))",
    ];
    for assertion in cases {
        let input = format!("(set-logic QF_SEQ)\n{assertion}\n(check-sat)");
        let commands = parse(&input).expect("valid adversarial sequence query");
        let mut exec = Executor::new();
        exec.set_self_check(true);
        let outputs = exec.execute_all(&commands).expect("query executes");
        assert_ne!(
            outputs.first().map(String::as_str),
            Some("sat"),
            "false native-sequence assertion was repaired into sat: {assertion}"
        );
    }
}
