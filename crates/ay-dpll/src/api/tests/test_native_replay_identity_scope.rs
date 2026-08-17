// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial lexical-identity tests for native replay.

use crate::api::{
    DatatypeConstructor, DatatypeSort, Logic, NativeReplayEventKind, NativeReplayMetadata,
    NativeReplaySymbolKind, Solver, SolverError, Sort,
};
use ay_core::term::{Symbol, TermData};

#[test]
fn constructor_collision_bound_in_one_root_and_free_in_another_is_rejected() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let color = DatatypeSort::new(
        "DualContextColor",
        vec![
            DatatypeConstructor::unit("DualContextRed"),
            DatatypeConstructor::unit("DualContextBlue"),
        ],
    );
    solver.try_declare_datatype(&color).expect("datatype");
    let red = solver.datatype_constructor(&color, "DualContextRed", &[]);
    let shared = solver.declare_const_with_fresh_identity(
        "DualContextRed",
        "!ay.dual-context-red",
        Sort::Datatype(color),
    );
    let free = solver
        .try_eq(shared, red)
        .and_then(|equal| solver.try_not(equal))
        .expect("free shared != red");
    solver.try_assert_term(free).expect("free root");

    // Preserve the Var node in a bound context without folding `x = x`.
    let body =
        solver
            .terms_mut()
            .mk_app(Symbol::named("="), [shared.id(), shared.id()], Sort::Bool);
    let body = solver.wrap_term(body);
    let quantified = solver.try_forall(&[shared], body).expect("bound root");
    solver.try_assert_term(quantified).expect("bound root");

    let mut artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let _ = Solver::replay_native_replay_artifact(&artifact).expect("original dual-context replay");

    let shared_core = artifact
        .declarations
        .iter()
        .find(|declaration| declaration.term == shared.id())
        .expect("shared declaration")
        .core_name
        .clone();
    let constructor_core = artifact
        .symbol_identities
        .iter()
        .find(|identity| {
            identity.surface_name == "DualContextRed"
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
        })
        .expect("constructor identity")
        .core_name
        .clone();
    artifact
        .declarations
        .retain(|declaration| declaration.term != shared.id());
    artifact.events.retain(|event| {
        !matches!(&event.kind, NativeReplayEventKind::DeclareConst { term, .. } if *term == shared.id())
    });
    artifact.symbol_identities.retain(|identity| {
        !(identity.kind == NativeReplaySymbolKind::Uninterpreted
            && identity.core_name == shared_core)
    });
    let shared_node = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == shared.id())
        .expect("shared node");
    let TermData::Var(name, _) = &mut shared_node.data else {
        panic!("shared node is a Var")
    };
    name.clone_from(&constructor_core);
    let quantifier = artifact
        .terms
        .iter_mut()
        .find(|node| node.id == quantified.id())
        .expect("quantifier node");
    let TermData::Forall(bindings, _, _) = &mut quantifier.data else {
        panic!("quantifier node is a forall")
    };
    bindings[0].0.clone_from(&constructor_core);

    assert!(matches!(
        Solver::replay_native_replay_artifact(&artifact),
        Err(SolverError::InvalidArgument {
            operation: "native_replay",
            ..
        })
    ));
}
