// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;

fn fixture() -> (TermStore, TermId, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let carrier = Sort::Uninterpreted("D@exact".into());
    let variable = terms.mk_var("x", carrier.clone());
    let field = terms.mk_var("field", Sort::bitvec(8));
    let value = terms.mk_app(Symbol::named("make"), [field], carrier);
    let definition = terms.mk_app(Symbol::named("="), [variable, value], Sort::Bool);
    let query = terms.mk_app(Symbol::named("keep"), [variable], Sort::Bool);
    (terms, variable, value, definition, query)
}

#[test]
fn nominal_direct_equality_rewrites_with_exact_authored_source() {
    for reversed in [false, true] {
        let (mut terms, variable, value, definition, query) = fixture();
        let definition = if reversed {
            terms.mk_app(Symbol::named("="), [value, variable], Sort::Bool)
        } else {
            definition
        };
        let mut roots = vec![definition, query];
        let mut sources = vec![vec![definition], vec![query]];
        let original_sources = sources.clone();
        let mut pass = VariableSubstitution::new();
        assert!(pass.apply_with_sources(&mut terms, &mut roots, &mut sources));
        assert_eq!(pass.substitutions().get(&variable), Some(&value));
        assert_eq!(
            pass.substitution_sources().get(&variable),
            Some(&definition)
        );
        let expected = terms.mk_app(Symbol::named("keep"), [value], Sort::Bool);
        assert_eq!(roots, vec![terms.true_term(), expected]);
        assert_eq!(sources, original_sources);
    }
}

#[test]
fn nominal_direct_equality_refuses_wrong_or_oversized_carrier_and_nonboolean_root() {
    let exact = Sort::Uninterpreted("D@exact".into());
    let oversized = Sort::Uninterpreted("D".repeat(VAR_SUBST_NOMINAL_IDENTITY_BYTE_LIMIT / 2 + 1));
    for (variable_sort, replacement_sort, assertion_sort) in [
        (
            exact.clone(),
            Sort::Uninterpreted("D@different".into()),
            Sort::Bool,
        ),
        (exact.clone(), Sort::Bool, Sort::Bool),
        (Sort::Bool, exact.clone(), Sort::Bool),
        (
            exact.clone(),
            Sort::array(Sort::bitvec(8), Sort::bitvec(8)),
            Sort::Bool,
        ),
        (exact.clone(), exact, Sort::Int),
        (oversized.clone(), oversized, Sort::Bool),
    ] {
        let mut terms = TermStore::new();
        let variable = terms.mk_var("x", variable_sort);
        let query = terms.mk_app(Symbol::named("keep"), [variable], Sort::Bool);
        let replacement = terms.mk_var("bad", replacement_sort);
        let malformed = terms.mk_app(Symbol::named("="), [variable, replacement], assertion_sort);
        let mut roots = vec![malformed, query];
        let before = roots.clone();
        let mut pass = VariableSubstitution::new();
        assert!(!pass.apply(&mut terms, &mut roots));
        assert!(pass.substitutions().is_empty());
        assert_eq!(roots, before);
    }
    let (mut terms, variable, value, _, query) = fixture();
    for (symbol, args) in [
        (Symbol::indexed("=", vec![0]), vec![variable, value]),
        (Symbol::named("="), vec![variable]),
        (Symbol::named("not_equality"), vec![variable, value]),
    ] {
        let malformed = terms.mk_app(symbol, args, Sort::Bool);
        let mut roots = vec![malformed, query];
        let before = roots.clone();
        let mut pass = VariableSubstitution::new();
        assert!(!pass.apply(&mut terms, &mut roots));
        assert!(pass.substitutions().is_empty());
        assert_eq!(roots, before);
    }
}

#[test]
fn nominal_direct_equality_retains_mode_budget_cycle_and_shape_refusals() {
    let (mut terms, variable, _, definition, query) = fixture();
    let mut roots = vec![definition, query];
    let mut constants = VariableSubstitution::new_constants_only();
    assert!(!constants.apply(&mut terms, &mut roots));
    assert!(constants.substitutions().is_empty());
    let mut bounded = VariableSubstitution::new();
    bounded.set_scalar_replacement_node_limit(1);
    assert!(!bounded.apply(&mut terms, &mut roots));
    assert!(bounded.substitutions().is_empty());

    let carrier = terms.sort(variable).clone();
    let cyclic = terms.mk_app(Symbol::named("make_cycle"), [variable], carrier.clone());
    let cyclic_eq = terms.mk_app(Symbol::named("="), [variable, cyclic], Sort::Bool);
    let mut cycle = VariableSubstitution::new();
    assert!(!cycle.apply(&mut terms, &mut vec![cyclic_eq, query]));
    assert!(cycle.substitutions().is_empty());

    let other = terms.mk_var("other", carrier);
    let other_eq = terms.mk_app(Symbol::named("="), [variable, other], Sort::Bool);
    let condition = terms.mk_var("condition", Sort::Bool);
    let conditional = terms.mk_ite(condition, definition, other_eq);
    let disjunction = terms.mk_app(Symbol::named("or"), [definition, other_eq], Sort::Bool);
    for root in [conditional, disjunction] {
        let mut pass = VariableSubstitution::new();
        assert!(!pass.apply(&mut terms, &mut vec![root, query]));
        assert!(pass.substitutions().is_empty());
    }
}
