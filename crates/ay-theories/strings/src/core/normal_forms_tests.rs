// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[test]
fn concat_normal_form_flattens() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let ab = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, ab);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(!core.check(&terms, &state, &mut infer, &mut SkolemCache::new()));

    let nf = core.get_normal_form(&ab).expect("normal form exists");
    assert_eq!(nf.len(), 2);
    assert_eq!(nf.base[0], a);
    assert_eq!(nf.base[1], b);
}
