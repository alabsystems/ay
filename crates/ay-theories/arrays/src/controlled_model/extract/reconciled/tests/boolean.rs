// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn boolean_const_base_literal_fallback_matches_legacy_candidate_only() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Bool, Sort::Bool);
    let alias = terms.mk_var("alias", sort.clone());
    let index = terms.mk_var("index", Sort::Bool);
    let false_value = terms.mk_bool(false);
    let true_value = terms.mk_bool(true);
    let constant = terms.mk_const_array(Sort::Bool, false_value);
    let chain = terms.mk_app(Symbol::named("store"), [constant, index, true_value], sort);
    let _alias_read = terms.mk_app(Symbol::named("select"), [alias, index], Sort::Bool);
    let equality = terms.mk_eq(alias, chain);
    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    solver.register_atom(equality);
    solver.assert_literal(equality, true);
    let _ = solver.check();
    solver.rebuild_assign_indices();
    let mut values = HashMap::default();
    values.insert(index, "false".into());
    values.insert(true_value, "true".into());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert!(output.array_values[&chain].default.is_none());
    assert_eq!(
        output.store_chain_class_candidate.as_ref().unwrap()[&chain]
            .default
            .as_deref(),
        Some("false")
    );
    assert!(!values.contains_key(&false_value));
    drop(output);
    original.check().unwrap();
}
