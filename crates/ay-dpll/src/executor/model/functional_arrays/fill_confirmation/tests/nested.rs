// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::Ordering;

fn nested_root(exec: &mut Executor) -> TermId {
    let terms = &mut exec.ctx.terms;
    let index = Sort::bitvec(64);
    let cell = Sort::array(index.clone(), Sort::bitvec(8));
    let array = Sort::array(index.clone(), cell.clone());
    let binder = terms.mk_var("nested_i", index.clone());
    let dst = terms.mk_var("nested_dst", array.clone());
    let out = terms.mk_var("nested_out", array.clone());
    let src = terms.mk_var("nested_src", array);
    let lo = terms.mk_bitvec(1.into(), 64);
    let hi = terms.mk_bitvec(3.into(), 64);
    let lower = terms.mk_app(Symbol::named("bvule"), [lo, binder], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("bvult"), [binder, hi], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("and"), [lower, upper], Sort::Bool);
    let target = terms.mk_app(Symbol::named("select"), [out, binder], cell.clone());
    let frame = terms.mk_app(Symbol::named("select"), [dst, binder], cell.clone());
    let byte = terms.mk_bitvec(9.into(), 8);
    let positive = terms.mk_const_array(index.clone(), byte);
    let _ = src; // Distinct typed source rows exist, but Fill has no source capture.
    let rhs = terms.mk_app(Symbol::named("ite"), [guard, positive, frame], cell);
    let eq = terms.mk_app(Symbol::named("="), [target, rhs], Sort::Bool);
    terms.mk_forall(vec![("nested_i".into(), index)], eq)
}

#[test]
fn nested_cell_refuses_before_ite_sort_comparison_with_an_independently_healthy_model() {
    let end = Instant::now() + Duration::from_secs(20);
    let _owner = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(end);
    let original = root(&exec);
    assert!(
        confirm(&exec, original),
        "actual selected model is independently healthy"
    );
    let nested = nested_root(&mut exec);
    assert!(
        confirm(&exec, original),
        "only inert term rows were appended; source/model still healthy"
    );
    let model = exec.last_model.as_ref().expect("actual model");
    let view = IndependentModelView::new(&exec, model);
    let mut admission = PinAdmission::capture(&exec, model).expect("same healthy owner");
    let used = &model.functional_arrays.as_ref().expect("data").work_used;
    let before = used.load(Ordering::Acquire);
    assert!(grammar::recognize(&exec, &view, nested, &mut admission).is_none());
    assert_eq!(
        used.load(Ordering::Acquire) - before,
        640,
        "root + Eq header + two shallow sort headers; NO ite/child/deep-sort visits"
    );
    drop((admission, view));
    assert!(!exec.complete_array_fill_restoration_candidate(nested));
    assert!(!confirm(&exec, nested));
    assert!(
        confirm(&exec, original),
        "nested refusal is not a sticky resource or stale-source fault"
    );
    assert!(Instant::now() < end);
}
