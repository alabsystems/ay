// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn only_authorized_constructor_members_can_poison_reconstruction() {
    let commands = ay_frontend::parse(
        "(set-logic ALL)
         (declare-datatype U ((mk (g (Array Int Bool)))))
         (declare-fun f (Int) U)
         (declare-fun h (Int) (Array Int Bool))
         (assert (= (f 0) (mk (h 0))))",
    )
    .expect("unresolved source fixture parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("unresolved source declarations execute");
    let (member, source) = executor
        .ctx
        .terms
        .term_ids()
        .find_map(|term| match executor.ctx.terms.get(term) {
            TermData::App(symbol, args) if symbol.name() == "mk" && args.len() == 1 => {
                Some((term, args[0]))
            }
            _ => None,
        })
        .expect("fixture retains the constructor source");
    assert!(matches!(
        executor.ctx.terms.get(source),
        TermData::App(symbol, _) if symbol.name() == "h"
    ));
    let field_sort = executor.ctx.terms.sort(source).clone();
    let class = ExactClass {
        cell_sort: executor.ctx.terms.sort(member).clone(),
        carrier: "@U!0".to_string(),
        members: [member].into_iter().collect(),
        fields: vec![(0, "g".to_string(), field_sort.clone())],
    };
    let model = Model::empty();

    let mut generated_work = 0;
    let generated = executor
        .constructor_array_field_sources(
            &model,
            &class,
            "mk",
            0,
            &field_sort,
            &HashSet::default(),
            &mut generated_work,
        )
        .expect("unrooted generated source is ignored");
    assert!(generated.exact.is_empty() && !generated.unresolved);

    let mut source_only = HashSet::default();
    source_only.insert(source);
    let mut source_only_work = 0;
    let source_only = executor
        .constructor_array_field_sources(
            &model,
            &class,
            "mk",
            0,
            &field_sort,
            &source_only,
            &mut source_only_work,
        )
        .expect("a queried argument does not authorize its generated owner");
    assert!(source_only.exact.is_empty() && !source_only.unresolved);

    let authorized = [member].into_iter().collect();
    let mut authorized_work = 0;
    let authorized = executor
        .constructor_array_field_sources(
            &model,
            &class,
            "mk",
            0,
            &field_sort,
            &authorized,
            &mut authorized_work,
        )
        .expect("an authored constructor's unresolved source is classified");
    assert!(authorized.exact.is_empty() && authorized.unresolved);
}
