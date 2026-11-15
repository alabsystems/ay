// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::resource::enter_check_stop;

use super::{bv, euf_witness, Executor, Model, Sort, TermId, WIDTH};
use crate::executor_types::UnknownOrigin;

fn fixture() -> (Executor, Model, TermId) {
    let mut exec = Executor::new();
    let b = exec.ctx.terms.mk_var("b", Sort::bitvec(WIDTH));
    let zero = bv(&mut exec, 0);
    let equal = exec.ctx.terms.mk_eq(b, zero);
    let apart = exec.ctx.terms.mk_not(equal);
    exec.ctx.assertions.push(apart);
    (exec, euf_witness(&[(b, "#x01")]), b)
}

#[test]
fn every_observed_stop_rolls_back_offers_and_prevents_fresh_retry() {
    let (exec, mut model, _) = fixture();
    let count = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&count);
    let scope = enter_check_stop(Arc::new(move || {
        counter.fetch_add(1, Ordering::SeqCst);
        false
    }));
    assert_eq!(
        exec.complete_uninterpreted_bitvec_values(&mut model, &[], &HashSet::default()),
        Ok(1)
    );
    let polls = count.load(Ordering::SeqCst);
    drop(scope);
    assert!(
        polls > 20,
        "cover traversal, insertion, atom checks and final poll"
    );
    for cutoff in 0..polls {
        let (exec, mut model, b) = fixture();
        let count = Arc::new(AtomicUsize::new(0));
        let counter = Arc::clone(&count);
        let scope = enter_check_stop(Arc::new(move || {
            counter.fetch_add(1, Ordering::SeqCst) == cutoff
        }));
        let result =
            exec.complete_uninterpreted_bitvec_values(&mut model, &[], &HashSet::default());
        assert!(result.is_err(), "stop at poll {cutoff}/{polls} was lost");
        assert!(
            !model.completed_values.contains_key(&b),
            "partial offer at poll {cutoff}"
        );
        drop(scope);
        assert!(exec
            .complete_uninterpreted_bitvec_values(&mut model, &[], &HashSet::default())
            .is_err());
    }
}

#[test]
fn refused_scratch_growth_does_not_default_the_offered_variable() {
    let (mut exec, model, b) = fixture();
    exec.set_term_memory_limit(Some(exec.ctx.terms.true_memory_bytes()));
    exec.last_result = Some(crate::executor_types::SolveResult::Sat);
    exec.last_model = Some(model);
    exec.complete_model_for_validation(&[]);
    assert_eq!(
        exec.evaluation_stop_origin(),
        Some(UnknownOrigin::MemoryBudget)
    );
    assert!(!exec
        .last_model
        .as_ref()
        .expect("retained candidate")
        .completed_values
        .contains_key(&b));
}
