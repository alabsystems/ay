// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) const FINITE: &str = "
 (declare-const a (Array (_ BitVec 64) (_ BitVec 128)))
 (assert (= a (store (store
   ((as const (Array (_ BitVec 64) (_ BitVec 128))) #xffffffffffffffffffffffffffffffff)
   (_ bv0 64) (_ bv7 128))
   (_ bv18446744073709551615 64) #xffffffffffffffffffffffffffffffff)))
 (assert (forall ((i (_ BitVec 64)))
   (= (select a i)
      (ite (= i (_ bv0 64)) (_ bv7 128)
           #xffffffffffffffffffffffffffffffff))))";

pub(super) const RANGE: &str = "
 (declare-const b (Array (_ BitVec 64) (_ BitVec 8)))
 (declare-const w (Array (_ BitVec 64) (_ BitVec 8)))
 (assert (= b (store (store
   ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
   (_ bv18446744073709551615 64) #x0b) (_ bv0 64) #x09)))
 (assert (= w (lambda ((i (_ BitVec 64)))
   (ite (and (bvule (_ bv1 64) i)
             (bvult i (_ bv18446744073709551615 64)))
        (select b (bvadd (bvsub i (_ bv1 64))
                        (_ bv18446744073709551615 64)))
        (select b i)))))
 (assert (forall ((i (_ BitVec 64))) (bvule (select w i) #x0b)))";

pub(super) fn loaded(source: &str, end: Instant) -> Executor {
    let mut exec = Executor::new();
    exec.set_term_memory_limit(Some(128 * 1024 * 1024));
    let commands = parse(source).expect("complete original fixture source");
    assert_eq!(
        exec.execute_all(&commands).expect("elaborate, not solve"),
        [] as [String; 0]
    );
    exec.begin_external_decision_query(false);
    exec.set_deadline(Some(end));
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(
        model.functional_arrays.is_some(),
        "actual complete producer DATA"
    );
    exec.last_model = Some(model);
    assert!(
        exec.last_result.is_none(),
        "no fixture query or published verdict"
    );
    assert!(Instant::now() < end);
    exec
}

pub(super) fn variable(exec: &Executor, name: &str) -> TermId {
    exec.ctx
        .symbol_info(name)
        .and_then(|info| info.term)
        .expect("original free leaf")
}

pub(super) fn matrix(exec: &Executor) -> TermId {
    *exec
        .ctx
        .assertions
        .last()
        .expect("complete original matrix")
}

pub(super) fn pins(
    exec: &mut Executor,
    root: TermId,
    exclude: &HashSet<TermId>,
) -> QuantifiedGatePins {
    exec.quantified_gate_model_pins(root, &mut QuantifiedGateElements::default(), exclude)
}

pub(super) fn snapshot(exec: &Executor, leaf: TermId) -> Arc<ArraySnapshot> {
    exec.last_model
        .as_ref()
        .expect("installed same model")
        .functional_array_value(exec, leaf)
        .expect("original source binding")
        .expect("complete selected function")
}

pub(super) fn args<'a>(exec: &'a Executor, id: TermId, head: &str) -> &'a [TermId] {
    let TermData::App(symbol, args) = exec.ctx.terms.get(id) else {
        panic!("named exact term")
    };
    assert_eq!(symbol.name(), head);
    args
}

pub(super) fn rhs(exec: &Executor, pins: &QuantifiedGatePins, leaf: TermId) -> TermId {
    let found: Vec<_> = pins
        .equalities
        .iter()
        .filter_map(|&id| {
            let row = args(exec, id, "=");
            assert_eq!(row.len(), 2);
            (row[0] == leaf).then_some(row[1])
        })
        .collect();
    assert_eq!(found.len(), 1, "one exact original leaf pin");
    found[0]
}

pub(super) fn whole(exec: &Executor, leaf: TermId, value: TermId) {
    let original = snapshot(exec, leaf);
    let model = exec.last_model.as_ref().expect("same model");
    let view = IndependentModelView::new(exec, model);
    let mut left = model.functional_work_left();
    let rebuilt = Evaluator::new(&exec.ctx.terms, &view)
        .capture_array_snapshot_with_work(value, &mut left)
        .expect("independent complete RHS capture, not point sampling");
    let before = model.functional_work_left();
    let mut left = before;
    let equal = original.same_function_with_stop(&rebuilt, &mut left, &mut || {
        exec.poll_evaluation_stop().is_err() || check_stop_requested()
    });
    model
        .charge_functional_array_work(exec, before - left)
        .expect("SAME original comparison debit");
    assert!(equal.expect("whole closed graph comparison"));
    assert!(exec.last_result.is_none(), "pins are DATA, not SAT");
}

pub(super) fn bv(exec: &Executor, id: TermId, expected: u64) {
    assert!(matches!(exec.ctx.terms.get(id),
        TermData::Const(Constant::BitVec { value, width: 64 }) if *value == expected.into()));
}

pub(super) fn refused(exec: &mut Executor, root: TermId) {
    let pins = pins(exec, root, &HashSet::new());
    assert!(
        !pins.total,
        "one refused complete input cannot become a total pin set"
    );
    assert!(pins.equalities.is_empty(), "no sampled/default replacement");
    assert!(exec.last_result.is_none(), "no fixture verdict");
}
