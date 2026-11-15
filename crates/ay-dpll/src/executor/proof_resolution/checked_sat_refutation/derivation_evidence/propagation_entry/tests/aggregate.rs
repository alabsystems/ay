// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod parsed;

#[test]
fn aggregate_entry_requires_exact_bounded_core_sort_identity() {
    let mut executor = Executor::new();
    let exact = Sort::array(
        Sort::bitvec(64),
        Sort::array(Sort::Bool, Sort::Uninterpreted("MCVec".into())),
    );
    let terms = &mut executor.ctx.terms;
    let left = terms.mk_var("aggregate left", exact.clone());
    let right = terms.mk_var("aggregate right", exact.clone());
    let record = entry(terms, left, right);
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_some());
    let mut reversed = record.clone();
    reversed.source_assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [right, left], Sort::Bool);
    assert!(CheckedPropagationEntry::seal(&executor, &reversed).is_some());
    for sort in [
        Sort::array(
            Sort::bitvec(32),
            Sort::array(Sort::Bool, Sort::Uninterpreted("MCVec".into())),
        ),
        Sort::array(
            Sort::bitvec(64),
            Sort::array(Sort::Bool, Sort::Uninterpreted("OtherVec".into())),
        ),
        Sort::array(Sort::bitvec(64), Sort::Uninterpreted("MCVec".into())),
    ] {
        let terms = &mut executor.ctx.terms;
        let wrong = terms.mk_var("different carrier", sort);
        let record = entry(terms, left, wrong);
        assert!(CheckedPropagationEntry::seal(&executor, &record).is_none());
    }
    // Compare borrowed descriptors directly: no recursive clone, Eq or Hash is
    // needed before this new admission bound. Rich DT definitions stay closed.
    let inline = Sort::Datatype(ay_core::DatatypeSort::new("MCVec", vec![]));
    assert!(!same_variable_sort(&inline, &inline));
    let long = Sort::Uninterpreted("x".repeat(PLAN_NODE_BUDGET));
    assert!(!same_variable_sort(&long, &long));
    let mut nested = Sort::Int;
    for _ in 0..MAX_SCALAR_REPLACEMENT_DEPTH {
        nested = Sort::array(Sort::Bool, nested);
    }
    assert!(same_variable_sort(&nested, &nested));
    nested = Sort::array(Sort::Bool, nested);
    assert!(!same_variable_sort(&nested, &nested));
    assert!(same_variable_sort(&exact, &exact));
}

#[test]
fn aggregate_entry_keeps_source_endpoint_epoch_and_slot_authority() {
    let mut executor = Executor::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let terms = &mut executor.ctx.terms;
    let variable = terms.mk_var("array", sort.clone());
    let value = terms.mk_var("authored array", sort.clone());
    let record = entry(terms, variable, value);
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_some());
    let other = executor.ctx.terms.mk_var("unauthored array", sort.clone());
    let mut forged = record.clone();
    forged.value = other;
    assert!(CheckedPropagationEntry::seal(&executor, &forged).is_none());
    let token = CheckedPropagationEntry::seal(&executor, &record).unwrap();
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(token.into_current(&executor).is_none());
    let token = CheckedPropagationEntry::seal(&executor, &record).unwrap();
    executor
        .ctx
        .process_command(&ay_frontend::Command::Push(1))
        .unwrap();
    assert!(token.into_current(&executor).is_none());

    // Scratch entries are not asserted: rollback leaves no source/model cache.
    let checkpoint = executor.ctx.terms.rollback_checkpoint();
    let value = executor.ctx.terms.mk_var("scratch old array", sort.clone());
    let scratch = entry(&mut executor.ctx.terms, variable, value);
    let token = CheckedPropagationEntry::seal(&executor, &scratch).unwrap();
    executor.ctx.terms.rollback_to(checkpoint);
    let replacement = executor.ctx.terms.mk_var("scratch new array", sort);
    assert_eq!(replacement, value, "exercise same numeric slot, new stamp");
    let _ = entry(&mut executor.ctx.terms, variable, replacement);
    assert!(token.into_current(&executor).is_none());
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_some());
}

#[test]
fn aggregate_entry_retains_occurs_depth_and_work_refusals() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("MCVec".into());
    let terms = &mut executor.ctx.terms;
    let variable = terms.mk_var("v", sort.clone());
    let base = terms.mk_var("other", sort.clone());
    let cyclic = terms.mk_app(Symbol::named("wrap"), [variable], sort.clone());
    let cycle = entry(terms, variable, cyclic);
    assert!(CheckedPropagationEntry::seal(&executor, &cycle).is_none());
    let terms = &mut executor.ctx.terms;
    let wide = terms.mk_app(
        Symbol::named("wide"),
        vec![base; PLAN_NODE_BUDGET],
        sort.clone(),
    );
    let wide = entry(terms, variable, wide);
    assert!(CheckedPropagationEntry::seal(&executor, &wide).is_none());
    let terms = &mut executor.ctx.terms;
    let mut below = base;
    for _ in 0..MAX_SCALAR_REPLACEMENT_DEPTH {
        below = terms.mk_app(Symbol::named("wrap"), [below], sort.clone());
    }
    let boundary = entry(terms, variable, below);
    assert!(CheckedPropagationEntry::seal(&executor, &boundary).is_some());
    let terms = &mut executor.ctx.terms;
    let over = terms.mk_app(Symbol::named("wrap"), [below], sort);
    let over = entry(terms, variable, over);
    let before = terms.len();
    assert!(CheckedPropagationEntry::seal(&executor, &over).is_none());
    assert_eq!(executor.ctx.terms.len(), before);
    assert!(CheckedPropagationEntry::seal(&executor, &boundary).is_some());
}
