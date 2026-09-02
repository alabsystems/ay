// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::{Symbol, TermData};

const FIXTURE: &str = "(set-logic ALL)\
     (declare-datatype U1 ((mk (g (Array Int Bool)))))\
     (declare-const v3 (Array Int U1))\
     (declare-const v5 (Array Int U1))\
     (assert (distinct v3 v5))\
     (check-sat)\
     (check-sat)";

fn current_outer_read(executor: &Executor, model: &Model) -> (TermId, TermId, TermId) {
    let cell = model
        .dt_array_field_classes
        .iter()
        .flat_map(|class| class.members.keys().copied())
        .find(|&term| {
            matches!(executor.ctx.terms.get(term), TermData::App(symbol, args)
                if symbol.name() == "select" && args.len() == 2)
        })
        .expect("fixture inventories an outer-array read");
    let outer = match executor.ctx.terms.get(cell) {
        TermData::App(_, args) => args[0],
        _ => unreachable!("selected inventory member is an application"),
    };
    let sibling = executor
        .ctx
        .terms
        .term_ids()
        .find(|&term| {
            term != outer
                && executor.ctx.terms.sort(term) == executor.ctx.terms.sort(outer)
                && matches!(executor.ctx.terms.get(term), TermData::Var(_, _))
        })
        .expect("fixture has a second outer-array variable");
    (outer, sibling, cell)
}

fn install_extensionality_roots(
    executor: &mut Executor,
    outer: TermId,
    sibling: TermId,
    cell: TermId,
) {
    let outer_equality =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [outer, sibling], Sort::Bool);
    let read_root = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [cell, cell], Sort::Bool);
    let roots = vec![outer_equality, read_root];
    executor.ctx.assertions = roots.clone();
    executor.independent_gate_authored_assertions = Some(roots);
}

#[test]
fn extensionality_fallback_rejects_omitted_partial_and_stale_inventory() {
    let commands = ay_frontend::parse(FIXTURE).expect("extensionality fixture parses");
    let mut executor = Executor::new();
    assert_eq!(
        executor
            .execute_all(&commands)
            .expect("extensionality fixture solves"),
        ["sat", "sat"]
    );
    let model = executor
        .last_model
        .as_ref()
        .expect("sat retains the completed model")
        .clone();
    let (outer, sibling, cell) = current_outer_read(&executor, &model);
    install_extensionality_roots(&mut executor, outer, sibling, cell);

    let mut omitted = model.clone();
    omitted.array_model = None;
    omitted.dt_array_field_classes.clear();
    assert!(executor
        .independent_array_leaf_value_for_test(&omitted, outer)
        .is_none());

    let mut partial = model.clone();
    partial.array_model = None;
    partial
        .dt_array_field_classes
        .retain(|class| !class.members.contains_key(&cell));
    assert!(!partial.dt_array_field_classes.is_empty());
    assert!(partial.dt_ground.contains_key(&cell));
    assert!(executor
        .independent_array_leaf_value_for_test(&partial, outer)
        .is_none());

    assert!(executor
        .execute(&ay_frontend::Command::Reset)
        .expect("SMT reset executes")
        .is_none());
    assert_eq!(
        executor
            .execute_all(&commands)
            .expect("reset fixture solves"),
        ["sat", "sat"]
    );
    let current = executor
        .last_model
        .as_ref()
        .expect("rerun retains the current model")
        .clone();
    let (new_outer, new_sibling, new_cell) = current_outer_read(&executor, &current);
    install_extensionality_roots(&mut executor, new_outer, new_sibling, new_cell);
    assert!(executor
        .independent_array_leaf_value_for_test(&model, new_outer)
        .is_none());
}
