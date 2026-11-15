// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod array_owner;
mod opaque_scope;
mod query_authority;

use super::*;
use ay_frontend::parse;

fn loaded(input: &str) -> Executor {
    let commands = parse(input).expect("valid SMT-LIB fixture");
    let mut exec = Executor::new();
    for command in &commands {
        assert!(
            exec.execute(command).expect("fixture executes").is_none(),
            "fixture must not contain a query"
        );
    }
    exec
}

fn class_for_term(builder: &DtBuilder<'_>, term: TermId) -> usize {
    let index = *builder.index.get(&term).expect("term is collected");
    builder.class_of[index]
}

fn forced_constructor<'a>(builder: &'a DtBuilder<'_>, root: usize) -> &'a ForcedConstructor {
    builder.info[&root]
        .forced
        .as_ref()
        .expect("class has a fixed constructor tag")
}

#[test]
fn ground_definition_recovery_requires_closed_well_typed_bounded_constructors() {
    let mut exec = loaded("(declare-datatype D ((nil) (next (tail D))))");
    let sort = Sort::Uninterpreted("D".to_string());
    let from = exec.ctx.terms.mk_var("eliminated", sort.clone());
    let nil = exec.ctx.terms.mk_var("nil", sort.clone());
    let next = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("next"), [nil], sort.clone());
    exec.recorded_var_substitutions.insert(from, next);
    assert_eq!(
        exec.ground_datatype_definition(from, &mut OpaqueDtCollectionBudget::new()),
        Some(next)
    );

    let free = exec.ctx.terms.mk_var("free", sort.clone());
    let open = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("next"), [free], sort.clone());
    exec.recorded_var_substitutions.insert(from, open);
    assert_eq!(
        exec.ground_datatype_definition(from, &mut OpaqueDtCollectionBudget::new()),
        None
    );

    let wrong = exec.ctx.terms.mk_int(BigInt::from(3));
    let ill_typed = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("next"), [wrong], sort.clone());
    exec.recorded_var_substitutions.insert(from, ill_typed);
    assert_eq!(
        exec.ground_datatype_definition(from, &mut OpaqueDtCollectionBudget::new()),
        None
    );

    let mut deep = nil;
    for _ in 0..=MAX_DT_TERMS {
        deep = exec
            .ctx
            .terms
            .mk_app(ay_core::Symbol::named("next"), [deep], sort.clone());
    }
    exec.recorded_var_substitutions.insert(from, deep);
    assert_eq!(
        exec.ground_datatype_definition(from, &mut OpaqueDtCollectionBudget::new()),
        None
    );
}
