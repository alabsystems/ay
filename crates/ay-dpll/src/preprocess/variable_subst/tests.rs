// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::{Symbol, TermData};
use ay_core::Sort;
use num_bigint::BigInt;

#[test]
fn test_datatype_variable_elimination_folds_nested_selector() {
    use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut terms = TermStore::new();

    // datatype D = D_mk(fld_ptr: BV8, fld_len: BV8)
    let bv8 = Sort::bitvec(8);
    let dt = Sort::Datatype(DatatypeSort::new(
        "D",
        vec![DatatypeConstructor::new(
            "D_mk",
            vec![
                DatatypeField::new("fld_ptr", bv8.clone()),
                DatatypeField::new("fld_len", bv8.clone()),
            ],
        )],
    ));

    let v = terms.mk_var("v", dt.clone());
    let c1 = terms.mk_var("c1", Sort::Bool);
    let c2 = terms.mk_var("c2", Sort::Bool);
    let zero = terms.mk_bitvec(BigInt::from(0), 8);

    // Three distinct reconstruction arms (different fld_ptr) so the ite genuinely
    // nests, but every arm has fld_len = 0 (an empty-collection post-state).
    let mk_arm = |terms: &mut TermStore, ptr: i64| {
        let p = terms.mk_bitvec(BigInt::from(ptr), 8);
        let arm = terms.mk_app(Symbol::named("D_mk"), [p, zero], dt.clone());
        terms.mk_eq(v, arm)
    };
    let eq1 = mk_arm(&mut terms, 1);
    let eq2 = mk_arm(&mut terms, 2);
    let eq3 = mk_arm(&mut terms, 3);

    // Distributed nested ite of per-arm equalities, as fold_datatype_eq produces:
    //   ite(c1, (= v A1), ite(c2, (= v A2), (= v A3)))
    let inner = terms.mk_ite(c2, eq2, eq3);
    let def = terms.mk_ite(c1, eq1, inner);

    // A selector read that must collapse to the concrete len once v is folded.
    let sel = terms.mk_app(Symbol::named("fld_len"), [v], bv8.clone());
    let read = terms.mk_eq(sel, zero); // (= (fld_len v) 0)

    let mut assertions = vec![def, read];
    let mut pass = VariableSubstitution::new();
    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified, "datatype variable elimination should fire");
    assert!(
        pass.substitutions().contains_key(&v),
        "v should be substituted by its ite-of-constructors definition"
    );
    // (fld_len v) folds through the ite to the literal 0 in every arm, so the read
    // (= 0 0) simplifies to true — proving the selector-over-constructor/ite fold ran.
    assert_eq!(
        assertions[1],
        terms.true_term(),
        "selector read should fold to true after datatype var-elim"
    );
}

#[test]
fn test_simple_substitution() {
    let mut terms = TermStore::new();

    // Create: (= x y), (= y #b01)
    // After substitution: (= x x), (= x #b01) [simplified to: true, (= x #b01)]
    let x = terms.mk_var("x", Sort::bitvec(2));
    let y = terms.mk_var("y", Sort::bitvec(2));
    let eq_xy = terms.mk_eq(x, y);

    let const_01 = terms.mk_bitvec(BigInt::from(1), 2);
    let eq_y_01 = terms.mk_eq(y, const_01);

    let mut assertions = vec![eq_xy, eq_y_01];
    let mut pass = VariableSubstitution::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);

    // After substitution, (= y #b01) should become (= x #b01)
    // Check that the second assertion changed
    assert_ne!(assertions[1], eq_y_01);

    // The new assertion should be (= x #b01)
    let expected_eq = terms.mk_eq(x, const_01);
    assert_eq!(assertions[1], expected_eq);
}

#[test]
fn test_no_substitution_for_cycle() {
    let mut terms = TermStore::new();

    // Create: (= x x) - no substitution should happen (trivial cycle)
    let x = terms.mk_var("x", Sort::bitvec(2));
    let eq_xx = terms.mk_eq(x, x);

    let mut assertions = vec![eq_xx];
    let mut pass = VariableSubstitution::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    // No substitution extracted because rhs contains var
    assert!(!modified);
}

#[test]
fn test_no_substitution_for_non_variable() {
    let mut terms = TermStore::new();

    // Create: (= (bvadd x y) z) - no substitution (lhs is not a variable)
    let x = terms.mk_var("x", Sort::bitvec(2));
    let y = terms.mk_var("y", Sort::bitvec(2));
    let z = terms.mk_var("z", Sort::bitvec(2));
    let add_xy = terms.mk_bvadd(vec![x, y]);
    let eq = terms.mk_eq(add_xy, z);

    let mut assertions = vec![eq];
    let mut pass = VariableSubstitution::new();

    // z -> (bvadd x y) should be extracted
    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);
}

#[test]
fn test_bool_substitution() {
    let mut terms = TermStore::new();

    // Create: (= p q), (and q r)
    // After substitution: (= p p), (and p r)
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);

    let eq_pq = terms.mk_eq(p, q);
    let and_qr = terms.mk_and(vec![q, r]);

    let mut assertions = vec![eq_pq, and_qr];
    let mut pass = VariableSubstitution::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);

    // After substitution, (and q r) should become (and p r)
    let expected_and = terms.mk_and(vec![p, r]);
    assert_eq!(assertions[1], expected_and);
}

#[test]
fn test_rejects_indirect_cycle_due_to_ordering() {
    let mut terms = TermStore::new();

    // Create:
    //   a = (bvadd b 1)
    //   b = a
    //
    // Accepting both substitutions would create an indirect cycle.
    // The graph-based cycle detection (#2830) accepts `a -> (bvadd b 1)`
    // first (assertion order), then rejects `b -> a` because a's
    // replacement contains b.
    let a = terms.mk_var("a", Sort::bitvec(2));
    let b = terms.mk_var("b", Sort::bitvec(2));
    let one = terms.mk_bitvec(BigInt::from(1), 2);
    let a_rhs = terms.mk_bvadd(vec![b, one]);
    let a_def = terms.mk_eq(a, a_rhs);
    let b_eq_a = terms.mk_eq(b, a);

    let mut assertions = vec![a_def, b_eq_a];
    let mut pass = VariableSubstitution::new();

    // This should NOT cause infinite recursion
    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);

    // Only one substitution should be accepted (a -> bvadd(b,1)).
    // b -> a is rejected because a's replacement contains b (cycle).
    // The second assertion `b = a` becomes `b = (bvadd b 1)` after
    // substituting a.
    assert_eq!(pass.substitutions().len(), 1);
    assert_eq!(pass.substitutions().get(&a).copied(), Some(a_rhs));
}

/// Regression test for #2830: equality chain through addition.
///
/// b = d, a = b + 2, c = d + 2, NOT(a = c) is trivially UNSAT.
/// The old TermId-ordering constraint rejected `a -> (+ b 2)` because
/// b had a higher TermId than a. Graph-based cycle detection allows it.
#[test]
fn test_equality_chain_through_addition_2830() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));

    // b = d
    let eq_bd = terms.mk_eq(b, d);
    // a = b + 2
    let b_plus_2 = terms.mk_add(vec![b, two]);
    let eq_a = terms.mk_eq(a, b_plus_2);
    // c = d + 2
    let d_plus_2 = terms.mk_add(vec![d, two]);
    let eq_c = terms.mk_eq(c, d_plus_2);
    // NOT(a = c)
    let eq_ac = terms.mk_eq(a, c);
    let neg = terms.mk_not(eq_ac);

    let mut assertions = vec![eq_bd, eq_a, eq_c, neg];
    let mut pass = VariableSubstitution::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(
        modified,
        "variable substitution should have found substitutions"
    );

    // After substitution, at least d -> b and one of {a, c} should be substituted.
    // The key invariant: the negated equality should become trivially false
    // because both a and c get the same replacement expression (b + 2).
    let substs = pass.substitutions();
    assert!(
        substs.len() >= 2,
        "expected at least 2 substitutions (d->b and a or c), got {}",
        substs.len()
    );
}

/// Test multi-hop cycle detection: a -> b+1, b -> c+1 should block c -> a+1
/// because the chain c -> a -> b -> c would loop.
#[test]
fn test_rejects_multihop_cycle() {
    let mut terms = TermStore::new();

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));

    // a = b + 1
    let b_plus_1 = terms.mk_add(vec![b, one]);
    let eq_a = terms.mk_eq(a, b_plus_1);
    // b = c + 1
    let c_plus_1 = terms.mk_add(vec![c, one]);
    let eq_b = terms.mk_eq(b, c_plus_1);
    // c = a + 1 — this would create a cycle: c -> a -> b -> c
    let a_plus_1 = terms.mk_add(vec![a, one]);
    let eq_c = terms.mk_eq(c, a_plus_1);

    let mut assertions = vec![eq_a, eq_b, eq_c];
    let mut pass = VariableSubstitution::new();

    pass.apply(&mut terms, &mut assertions);

    // At most 2 substitutions should be accepted; the third creates a cycle
    assert!(
        pass.substitutions().len() <= 2,
        "expected at most 2 substitutions (third creates cycle), got {}",
        pass.substitutions().len()
    );
}

/// Regression test for #5731: stale subst_cache entries in quantifier scopes.
#[test]
fn test_subst_cache_stale_compound_in_quantifier() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let forty_two = terms.mk_int(BigInt::from(42));

    let x_plus_y = terms.mk_add(vec![x, y]);
    let outer_gt = terms.mk_gt(x_plus_y, zero);
    let forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], outer_gt);
    let eq_y_42 = terms.mk_eq(y, forty_two);

    let mut assertions = vec![eq_y_42, outer_gt, forall];
    let mut pass = VariableSubstitution::new();

    let modified = pass.apply(&mut terms, &mut assertions);
    assert!(modified);

    // Outer assertion should substitute y -> 42
    let x_plus_42 = terms.mk_add(vec![x, forty_two]);
    let expected_outer = terms.mk_gt(x_plus_42, zero);
    assert_eq!(assertions[1], expected_outer);

    // Forall body should NOT substitute bound y
    let expected_forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], outer_gt);
    assert_eq!(assertions[2], expected_forall);
}

/// Regression test for substitute_let shadowing bug (#5731 variant):
/// let-bound variables must shadow outer substitutions in the body.
///
/// Formula: (= y 42), (let ((y 7)) (= y 7))
/// After substitution with y -> 42:
///   CORRECT:   (let ((y 7)) (= y 7))   -- inner y is shadowed, body unchanged
///   BUGGY:     (let ((y 7)) (= 42 7))  -- inner y incorrectly substituted
#[test]
fn test_substitute_let_must_shadow_bound_vars() {
    let mut terms = TermStore::new();

    let y = terms.mk_var("y", Sort::Int);
    let seven = terms.mk_int(BigInt::from(7));
    let forty_two = terms.mk_int(BigInt::from(42));

    // (= y 7) inside the let body — y refers to the let-bound 7
    let eq_y_7 = terms.mk_eq(y, seven);
    // (let ((y 7)) (= y 7))
    let let_expr = terms.mk_let(vec![("y".to_string(), seven)], eq_y_7);

    // (= y 42) outside — establishes substitution y -> 42
    let eq_y_42 = terms.mk_eq(y, forty_two);

    let mut assertions = vec![eq_y_42, let_expr];
    let mut pass = VariableSubstitution::new();

    pass.apply(&mut terms, &mut assertions);

    // The let body must NOT have y -> 42 applied.
    // The let expression should be unchanged because the inner y is
    // shadowed by the let binding.
    let expected_let = terms.mk_let(vec![("y".to_string(), seven)], eq_y_7);
    assert_eq!(
        assertions[1], expected_let,
        "let-bound y must shadow outer substitution y -> 42; body should be unchanged"
    );
}

#[test]
fn test_substitution_rebuilds_ite_equality_without_expansion_11936() {
    let mut terms = TermStore::new();

    let c = terms.mk_var("c", Sort::Bool);
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let a = terms.mk_var("a", Sort::bitvec(8));
    let b = terms.mk_var("b", Sort::bitvec(8));
    let ite = terms.mk_ite(c, a, b);

    let y_def = terms.mk_app(Symbol::named("="), vec![y, ite], Sort::Bool);
    let y_eq_x = terms.mk_app(Symbol::named("="), vec![y, x], Sort::Bool);
    let y_neq_x = terms.mk_not(y_eq_x);
    let mut assertions = vec![y_def, y_neq_x];
    let mut pass = VariableSubstitution::new();

    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified);
    let TermData::Not(inner) = terms.get(assertions[1]) else {
        panic!("expected substituted assertion to remain a negated equality");
    };
    let TermData::App(sym, args) = terms.get(*inner) else {
        panic!("substituted equality was expanded instead of left structural");
    };
    assert_eq!(sym.name(), "=");
    assert_eq!(args.len(), 2);
    assert!(args.contains(&ite));
    assert!(args.contains(&x));
}

#[test]
fn test_rejects_large_scalar_replacement_rhs_8140() {
    let mut terms = TermStore::new();

    let target = terms.mk_var("member_result", Sort::bitvec(8));
    let mut rhs = terms.mk_var("leaf", Sort::bitvec(8));

    for i in 0..(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT + 8) {
        let cond = terms.mk_var(format!("guard_{i}"), Sort::Bool);
        let value = terms.mk_var(format!("value_{i}"), Sort::bitvec(8));
        rhs = terms.mk_ite(cond, value, rhs);
    }

    let def = terms.mk_app(Symbol::named("="), vec![target, rhs], Sort::Bool);
    let mut assertions = vec![def];
    let mut pass = VariableSubstitution::new();
    pass.set_scalar_replacement_node_limit(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT);

    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(!modified);
    assert!(
        !pass.substitutions().contains_key(&target),
        "large scalar RHS should not be accepted as a substitution"
    );
    assert_eq!(assertions[0], def);
}

#[test]
fn test_large_scalar_replacement_rhs_allowed_without_budget_8140() {
    let mut terms = TermStore::new();

    let target = terms.mk_var("member_result", Sort::bitvec(8));
    let mut rhs = terms.mk_var("leaf", Sort::bitvec(8));

    for i in 0..(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT + 8) {
        let cond = terms.mk_var(format!("guard_{i}"), Sort::Bool);
        let value = terms.mk_var(format!("value_{i}"), Sort::bitvec(8));
        rhs = terms.mk_ite(cond, value, rhs);
    }

    let def = terms.mk_app(Symbol::named("="), vec![target, rhs], Sort::Bool);
    let mut assertions = vec![def];
    let mut pass = VariableSubstitution::new();

    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified);
    assert_eq!(pass.substitutions().get(&target).copied(), Some(rhs));
    assert_eq!(assertions[0], terms.true_term());
}

#[test]
fn test_rejects_transitively_large_scalar_replacement_rhs_8140() {
    let mut terms = TermStore::new();

    let mut assertions = Vec::new();
    let mut previous = terms.mk_var("chain_0", Sort::bitvec(8));
    let mut variables = Vec::new();

    for i in 1..(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT + 8) {
        let current = terms.mk_var(format!("chain_{i}"), Sort::bitvec(8));
        let cond = terms.mk_var(format!("guard_{i}"), Sort::Bool);
        let value = terms.mk_var(format!("value_{i}"), Sort::bitvec(8));
        let rhs = terms.mk_ite(cond, value, previous);
        assertions.push(terms.mk_app(Symbol::named("="), vec![current, rhs], Sort::Bool));
        previous = current;
        variables.push(current);
    }

    let mut pass = VariableSubstitution::new();
    pass.set_scalar_replacement_node_limit(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT);

    pass.apply(&mut terms, &mut assertions);

    assert!(
        pass.substitutions().len() < variables.len(),
        "scalar chain should stop before accepting every transitive link"
    );
}

#[test]
fn test_rejects_forward_referenced_transitive_scalar_chain_8140() {
    let mut terms = TermStore::new();

    let mut assertions = Vec::new();
    let mut variables = Vec::new();

    for i in 0..(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT + 8) {
        let current = terms.mk_var(format!("forward_chain_{i}"), Sort::bitvec(8));
        let next = terms.mk_var(format!("forward_chain_{}", i + 1), Sort::bitvec(8));
        let cond = terms.mk_var(format!("forward_guard_{i}"), Sort::Bool);
        let value = terms.mk_var(format!("forward_value_{i}"), Sort::bitvec(8));
        let rhs = terms.mk_ite(cond, value, next);
        assertions.push(terms.mk_app(Symbol::named("="), vec![current, rhs], Sort::Bool));
        variables.push(current);
    }

    let mut pass = VariableSubstitution::new();
    pass.set_scalar_replacement_node_limit(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT);

    pass.apply(&mut terms, &mut assertions);

    assert!(
        pass.substitutions().len() < variables.len(),
        "forward-referenced scalar chain should not bypass the transitive budget"
    );
    for (&var, &replacement) in pass.substitutions() {
        assert!(
            VariableSubstitution::term_dag_size_within_limit(
                &terms,
                replacement,
                pass.substitutions(),
                VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT,
            ),
            "accepted substitution {var:?} exceeds the final transitive scalar budget"
        );
    }
}

#[test]
fn test_rejects_later_scalar_substitution_that_overbudgets_existing_one_8140() {
    let mut terms = TermStore::new();

    let target = terms.mk_var("already_substituted", Sort::bitvec(8));
    let tail = terms.mk_var("later_tail", Sort::bitvec(8));
    let mut target_rhs = tail;

    for i in 0..((VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT - 1) / 3) {
        let cond = terms.mk_var(format!("old_guard_{i}"), Sort::Bool);
        let value = terms.mk_var(format!("old_value_{i}"), Sort::bitvec(8));
        target_rhs = terms.mk_ite(cond, value, target_rhs);
    }

    let target_def = terms.mk_app(Symbol::named("="), vec![target, target_rhs], Sort::Bool);
    let mut assertions = vec![target_def];
    let mut pass = VariableSubstitution::new();
    pass.set_scalar_replacement_node_limit(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT);

    assert!(pass.apply(&mut terms, &mut assertions));
    assert_eq!(pass.substitutions().get(&target).copied(), Some(target_rhs));
    assert!(VariableSubstitution::term_dag_size_within_limit(
        &terms,
        target_rhs,
        pass.substitutions(),
        VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT,
    ));

    pass.reset();

    let leaf = terms.mk_var("later_leaf", Sort::bitvec(8));
    let cond = terms.mk_var("later_guard", Sort::Bool);
    let value = terms.mk_var("later_value", Sort::bitvec(8));
    let tail_rhs = terms.mk_ite(cond, value, leaf);
    let tail_def = terms.mk_app(Symbol::named("="), vec![tail, tail_rhs], Sort::Bool);
    let mut assertions = vec![tail_def];

    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(!modified);
    assert!(
        !pass.substitutions().contains_key(&tail),
        "later scalar substitution should not make an existing substitution exceed budget"
    );
    assert!(VariableSubstitution::term_dag_size_within_limit(
        &terms,
        target_rhs,
        pass.substitutions(),
        VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT,
    ));
}

#[test]
fn test_large_array_store_chain_replacement_still_allowed_8140() {
    let mut terms = TermStore::new();

    let array_sort = Sort::array(Sort::bitvec(8), Sort::bitvec(8));
    let base = terms.mk_var("arr_0", array_sort.clone());
    let next = terms.mk_var("arr_1", array_sort);
    let mut chain = base;
    let mut last_index = terms.mk_bitvec(BigInt::from(0), 8);
    let mut last_value = terms.mk_bitvec(BigInt::from(0), 8);

    for i in 0..(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT + 8) {
        last_index = terms.mk_bitvec(BigInt::from(i), 8);
        last_value = terms.mk_bitvec(BigInt::from(i + 1), 8);
        chain = terms.mk_store(chain, last_index, last_value);
    }

    let def = terms.mk_app(Symbol::named("="), vec![next, chain], Sort::Bool);
    let selected = terms.mk_select(next, last_index);
    let selected_eq = terms.mk_eq(selected, last_value);

    let mut assertions = vec![def, selected_eq];
    let mut pass = VariableSubstitution::new();
    pass.set_scalar_replacement_node_limit(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT);

    let modified = pass.apply(&mut terms, &mut assertions);

    assert!(modified);
    assert_eq!(pass.substitutions().get(&next).copied(), Some(chain));
    assert_eq!(assertions[1], terms.true_term());
}
