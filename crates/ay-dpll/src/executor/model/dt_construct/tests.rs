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
