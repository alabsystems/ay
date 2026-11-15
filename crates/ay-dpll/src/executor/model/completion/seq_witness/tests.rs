// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Positional construction on hand-built models: concatenation, `seq.nth`
//! binding and fresh elements, relevancy, and the contradictions that must
//! abandon the construction.

use super::super::super::{EvalValue, Model};
use crate::executor::Executor;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::Symbol;
use ay_core::{Sort, TermId};
use ay_lia::LiaModel;
use ay_seq::SeqModel;
use num_bigint::BigInt;
use num_rational::BigRational;

fn seq_int() -> Sort {
    Sort::Seq(Box::new(Sort::Int))
}

fn int(v: i64) -> EvalValue {
    EvalValue::Rational(BigRational::from_integer(BigInt::from(v)))
}

fn declared(exec: &mut Executor, name: &str) -> TermId {
    let term = exec.ctx.terms.mk_var(name, seq_int());
    exec.ctx.register_symbol(name.to_string(), term, seq_int());
    term
}

fn app(exec: &mut Executor, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    exec.ctx.terms.mk_app(Symbol::named(name), args, sort)
}

fn unit(exec: &mut Executor, v: i64) -> TermId {
    let k = exec.ctx.terms.mk_int(BigInt::from(v));
    app(exec, "seq.unit", vec![k], seq_int())
}

/// Assert `(= (seq.len s) n)` and record `n` as the LIA model row.
fn pin_len(exec: &mut Executor, rows: &mut HashMap<TermId, BigInt>, s: TermId, n: i64) {
    let len = app(exec, "seq.len", vec![s], Sort::Int);
    let k = exec.ctx.terms.mk_int(BigInt::from(n));
    let eq = exec.ctx.terms.mk_eq(len, k);
    exec.ctx.assertions.push(eq);
    rows.insert(len, BigInt::from(n));
}

fn seq_model(rows: HashMap<TermId, BigInt>) -> Model {
    let mut model = Model::empty();
    model.lia_model = Some(LiaModel { values: rows });
    model.seq_model = Some(SeqModel::default());
    model
}

fn witness(exec: &Executor, model: &Model) -> Option<HashMap<TermId, Vec<EvalValue>>> {
    exec.positional_seq_witness(model, &exec.ctx.assertions.clone())
}

#[test]
fn internal_word_equation_derives_a_missing_segment_without_overwriting_it() {
    let mut exec = Executor::new();
    let one = unit(&mut exec, 1);
    let two = unit(&mut exec, 2);
    let whole = app(&mut exec, "seq.++", vec![one, two], seq_int());
    let missing = exec.ctx.terms.mk_fresh_var("internal-word-tail", seq_int());
    let expression = app(&mut exec, "seq.++", vec![one, missing], seq_int());
    let equality = exec.ctx.terms.mk_eq(whole, expression);
    exec.ctx.assertions.push(equality);
    let mut model = seq_model(HashMap::default());
    exec.complete_internal_seq_equations(&mut model, &[]);
    assert_eq!(
        model.completed_values.get(&missing),
        Some(&EvalValue::Seq(vec![int(2)]))
    );
    model
        .completed_values
        .insert(missing, EvalValue::Seq(vec![int(99)]));
    exec.complete_internal_seq_equations(&mut model, &[]);
    assert_eq!(
        model.completed_values.get(&missing),
        Some(&EvalValue::Seq(vec![int(99)]))
    );
}

#[test]
fn internal_word_equation_refuses_a_conflicting_known_prefix() {
    let mut exec = Executor::new();
    let one = unit(&mut exec, 1);
    let nine = unit(&mut exec, 9);
    let missing = exec.ctx.terms.mk_fresh_var("internal-word-tail", seq_int());
    let expression = app(&mut exec, "seq.++", vec![nine, missing], seq_int());
    let equality = exec.ctx.terms.mk_eq(one, expression);
    exec.ctx.assertions.push(equality);
    let mut model = seq_model(HashMap::default());
    exec.complete_internal_seq_equations(&mut model, &[]);
    assert!(!model.completed_values.contains_key(&missing));
}

#[test]
fn concrete_prefix_activates_its_equation_despite_the_old_abstract_atom() {
    let mut exec = Executor::new();
    let prefix = declared(&mut exec, "completed-prefix");
    let whole = unit(&mut exec, 1);
    let tail = exec.ctx.terms.mk_fresh_var("internal-word-tail", seq_int());
    let concatenation = app(&mut exec, "seq.++", vec![prefix, tail], seq_int());
    let equality = exec.ctx.terms.mk_eq(whole, concatenation);
    let predicate = app(&mut exec, "seq.prefixof", vec![prefix, whole], Sort::Bool);
    let decomposition = exec.ctx.terms.mk_implies(predicate, equality);
    exec.ctx.assertions.push(decomposition);
    let mut model = seq_model(HashMap::default());
    model
        .completed_values
        .insert(prefix, EvalValue::Seq(Vec::new()));
    model.term_to_var.insert(predicate, 0);
    model.sat_model.push(false);
    exec.complete_internal_seq_equations(&mut model, &[]);
    assert_eq!(
        model.completed_values.get(&tail),
        Some(&EvalValue::Seq(vec![int(1)]))
    );
    assert_eq!(
        exec.evaluate_term(&model, decomposition),
        EvalValue::Bool(true)
    );
}

#[test]
fn repeated_conjunction_children_share_the_original_memory_limit() {
    let mut exec = Executor::new();
    let one = unit(&mut exec, 1);
    let two = unit(&mut exec, 2);
    let whole = app(&mut exec, "seq.++", vec![one, two], seq_int());
    let tail = exec.ctx.terms.mk_fresh_var("internal-word-tail", seq_int());
    let expression = app(&mut exec, "seq.++", vec![one, tail], seq_int());
    let equality = exec.ctx.terms.mk_eq(whole, expression);
    // Preserve repeated slots over a small DAG: canonical mk_and would
    // deduplicate them and miss the actual allocation boundary.
    let conjunction = app(
        &mut exec,
        "and",
        vec![equality; super::MAX_WITNESS_TERMS],
        Sort::Bool,
    );
    exec.ctx.assertions.push(conjunction);
    let source = exec.ctx.terms.true_memory_bytes();
    exec.set_term_memory_limit(Some(source + 16 * 1024));
    let mut model = seq_model(HashMap::default());
    exec.complete_internal_seq_equations(&mut model, &[]);
    assert!(!model.completed_values.contains_key(&tail));
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(crate::executor_types::UnknownOrigin::MemoryBudget)
    );
}

#[test]
fn abstract_equality_truth_does_not_replace_its_concrete_word_witness() {
    let mut exec = Executor::new();
    let prefix = declared(&mut exec, "completed-prefix");
    let whole = unit(&mut exec, 1);
    let tail = exec.ctx.terms.mk_fresh_var("internal-word-tail", seq_int());
    let concatenation = app(&mut exec, "seq.++", vec![prefix, tail], seq_int());
    let equality = exec.ctx.terms.mk_eq(whole, concatenation);
    let predicate = app(&mut exec, "seq.prefixof", vec![prefix, whole], Sort::Bool);
    let decomposition = exec.ctx.terms.mk_implies(predicate, equality);
    exec.ctx.assertions.push(decomposition);
    let mut model = seq_model(HashMap::default());
    model
        .completed_values
        .insert(prefix, EvalValue::Seq(Vec::new()));
    let _memo = super::super::super::EvalMemoSession::new();
    super::super::super::eval_memo::seed_for_test(equality, EvalValue::Bool(true));
    assert_eq!(exec.evaluate_term(&model, equality), EvalValue::Bool(true));
    assert_eq!(
        exec.required_completed_seq_equations(&model, vec![decomposition]),
        Some(vec![(whole, concatenation)])
    );
    exec.complete_internal_seq_equations(&mut model, &[]);
    assert_eq!(
        model.completed_values.get(&tail),
        Some(&EvalValue::Seq(vec![int(1)]))
    );
}

/// `s = [1] ++ t`, `len s = 3`, `(seq.nth t 1) = 9`.
fn head_tail_fixture() -> (Executor, TermId, TermId, Model) {
    let mut exec = Executor::new();
    let s = declared(&mut exec, "sw-s");
    let t = declared(&mut exec, "sw-t");
    let one = unit(&mut exec, 1);
    let cat = app(&mut exec, "seq.++", vec![one, t], seq_int());
    let def = exec.ctx.terms.mk_eq(s, cat);
    exec.ctx.assertions.push(def);
    let mut rows = HashMap::default();
    pin_len(&mut exec, &mut rows, s, 3);
    pin_len(&mut exec, &mut rows, t, 2);
    let k = exec.ctx.terms.mk_int(BigInt::from(1));
    let nth = app(&mut exec, "seq.nth", vec![t, k], Sort::Int);
    let nine = exec.ctx.terms.mk_int(BigInt::from(9));
    let read = exec.ctx.terms.mk_eq(nth, nine);
    exec.ctx.assertions.push(read);
    rows.insert(nth, BigInt::from(9));
    (exec, s, t, seq_model(rows))
}

#[test]
fn concatenation_and_reads_shape_one_joint_witness() {
    let (exec, s, t, model) = head_tail_fixture();
    let w = witness(&exec, &model).expect("consistent structure builds");
    let (sv, tv) = (&w[&s], &w[&t]);
    assert_eq!(tv.len(), 2);
    assert_eq!(tv[1], int(9), "the seq.nth row binds its cell");
    assert_eq!(sv[..], [vec![int(1)], tv.clone()].concat()[..]);
    // The one free cell avoids every literal (1, 2, 3, 9) of the problem.
    assert!(!matches!(&tv[0], v if [int(1), int(2), int(3), int(9)].contains(v)));
}

#[test]
fn the_candidate_offers_only_carriers_without_a_value() {
    let (exec, s, t, mut model) = head_tail_fixture();
    let mut values = HashMap::default();
    values.insert(s, vec!["1".to_string(), "4".to_string(), "9".to_string()]);
    model.seq_model = Some(SeqModel { values });
    let candidate = exec
        .positional_seq_candidate(&model, &[])
        .expect("t has no value");
    // `t` follows the value `s` already has, cell for cell; `s` is not
    // offered, and computing the candidate writes nothing.
    assert_eq!(candidate.values, vec![(t, vec![int(4), int(9)])]);
    assert_eq!(exec.evaluate_term(&model, t), EvalValue::Unknown);
}

#[test]
fn no_candidate_without_a_sequence_model() {
    let (exec, _, _, mut model) = head_tail_fixture();
    model.seq_model = None;
    assert!(exec.positional_seq_candidate(&model, &[]).is_none());
}

#[test]
fn positional_snapshot_refuses_an_unaffordable_deep_payload_without_mutation() {
    let mut exec = Executor::new();
    let s = declared(&mut exec, "snapshot-source");
    let mut model = seq_model(HashMap::default());
    model
        .completed_values
        .insert(s, EvalValue::Seq(vec![int(1); 4096]));
    let source = exec.ctx.terms.true_memory_bytes();
    exec.set_term_memory_limit(Some(source + 16 * 1024));
    let _scope = super::EvaluationCopyScope::enter(&exec).expect("small scope fits");
    assert!(exec.copy_seq_completion_slots(&model).is_none());
    assert!(
        matches!(model.completed_values.get(&s), Some(EvalValue::Seq(cells)) if cells.len() == 4096)
    );
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(crate::executor_types::UnknownOrigin::MemoryBudget)
    );
}

/// `s = (seq.unit e) ++ t` with `e` unvalued and a `(seq.nth s 0)` row: the
/// cell belongs to whatever value a later phase gives `e`, so `s` must not be
/// emitted with the row's value in it, while an unrelated class still is.
#[test]
fn a_unit_whose_element_has_no_value_keeps_its_classes_open() {
    let mut exec = Executor::new();
    let s = declared(&mut exec, "sw-s");
    let t = declared(&mut exec, "sw-t");
    let other = declared(&mut exec, "sw-o");
    let e = exec.ctx.terms.mk_var("sw-e", Sort::Int);
    let unit_e = app(&mut exec, "seq.unit", vec![e], seq_int());
    let cat = app(&mut exec, "seq.++", vec![unit_e, t], seq_int());
    let def = exec.ctx.terms.mk_eq(s, cat);
    exec.ctx.assertions.push(def);
    let mut rows = HashMap::default();
    pin_len(&mut exec, &mut rows, s, 2);
    pin_len(&mut exec, &mut rows, t, 1);
    pin_len(&mut exec, &mut rows, other, 1);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let nth = app(&mut exec, "seq.nth", vec![s, zero], Sort::Int);
    let five = exec.ctx.terms.mk_int(BigInt::from(5));
    let read = exec.ctx.terms.mk_eq(nth, five);
    exec.ctx.assertions.push(read);
    rows.insert(nth, BigInt::from(5));
    let w = witness(&exec, &seq_model(rows)).expect("consistent structure builds");
    assert!(
        !w.contains_key(&s),
        "s shares the open cell of (seq.unit e)"
    );
    assert!(w.contains_key(&t), "t does not share it");
    assert!(w.contains_key(&other));
}

/// `(or (not c) (= a b))` with `len a = len b = 1`: the equality atom is SAT
/// true either way; it only counts when `c` makes it relevant.
fn guarded_equality(c_value: bool) -> (Executor, TermId, TermId, Model) {
    let mut exec = Executor::new();
    let a = declared(&mut exec, "sw-a");
    let b = declared(&mut exec, "sw-b");
    let c = exec.ctx.terms.mk_var("sw-c", Sort::Bool);
    let eq = exec.ctx.terms.mk_eq(a, b);
    let not_c = exec.ctx.terms.mk_not(c);
    let guard = exec.ctx.terms.mk_or(vec![not_c, eq]);
    exec.ctx.assertions.push(guard);
    let mut rows = HashMap::default();
    pin_len(&mut exec, &mut rows, a, 1);
    pin_len(&mut exec, &mut rows, b, 1);
    let mut model = seq_model(rows);
    model.term_to_var.insert(eq, 0);
    model.term_to_var.insert(c, 1);
    model.sat_model = vec![true, c_value];
    (exec, a, b, model)
}

#[test]
fn a_dont_care_equality_does_not_merge_classes() {
    let (exec, a, b, model) = guarded_equality(false);
    let w = witness(&exec, &model).expect("builds");
    assert_ne!(w[&a], w[&b], "the atom is not relevant when c is false");
}

#[test]
fn a_relevant_equality_merges_classes() {
    let (exec, a, b, model) = guarded_equality(true);
    let w = witness(&exec, &model).expect("builds");
    assert_eq!(w[&a], w[&b]);
}

#[test]
fn two_values_forced_onto_one_cell_abandon_the_construction() {
    let mut exec = Executor::new();
    let s = declared(&mut exec, "sw-s");
    for v in [1, 2] {
        let u = unit(&mut exec, v);
        let eq = exec.ctx.terms.mk_eq(s, u);
        exec.ctx.assertions.push(eq);
    }
    assert!(witness(&exec, &seq_model(HashMap::default())).is_none());
}

#[test]
fn a_length_the_concatenation_contradicts_abandons_the_construction() {
    let mut exec = Executor::new();
    let s = declared(&mut exec, "sw-s");
    let t = declared(&mut exec, "sw-t");
    let tt = app(&mut exec, "seq.++", vec![t, t], seq_int());
    let def = exec.ctx.terms.mk_eq(s, tt);
    exec.ctx.assertions.push(def);
    let mut rows = HashMap::default();
    pin_len(&mut exec, &mut rows, s, 3);
    pin_len(&mut exec, &mut rows, t, 1);
    assert!(witness(&exec, &seq_model(rows)).is_none());
}
