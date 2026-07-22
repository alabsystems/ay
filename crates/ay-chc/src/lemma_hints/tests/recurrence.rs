// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_recurrence_conserved_equality_provider_basic() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Create a problem modeling s_multipl pattern:
    // predicate inv(x1, x2) -- two vars
    // init: x1 = 0 /\ x2 = 0 => inv(x1, x2)
    // trans: inv(a, b) /\ a' = a + 1 /\ b' = b - 1 => inv(a', b')
    //
    // x1 + x2 should be conserved = 0

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Init clause: x1 = 0 /\ x2 = 0 => inv(x1, x2)
    let x1 = ChcVar::new("x1", ChcSort::Int);
    let x2 = ChcVar::new("x2", ChcSort::Int);
    let init_constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(x2.clone()), ChcExpr::int(0)),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(init_constraint),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x1), ChcExpr::var(x2)]),
    ));

    // Trans clause: inv(a, b) => inv(a + 1, b - 1)
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(a), ChcExpr::int(1)),
                ChcExpr::sub(ChcExpr::var(b), ChcExpr::int(1)),
            ],
        ),
    ));

    // Define canonical vars for inv
    let canonical_x1 = ChcVar::new("a0", ChcSort::Int);
    let canonical_x2 = ChcVar::new("a1", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_x1, canonical_x2];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let provider = RecurrenceConservedEqualityProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // Should emit hint: a0 + a1 = 0
    assert!(
        !hints.is_empty(),
        "Expected at least one hint from RecurrenceConservedEqualityProvider"
    );
    assert_eq!(hints[0].predicate, inv);
    assert_eq!(hints[0].source, "recurrence-conserved-eq-v1");
    assert_eq!(hints[0].priority, 200);
}

#[test]
fn test_recurrence_provider_no_self_loop() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Problem with no self-loop - should not generate hints
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![ChcSort::Int]);
    let q = problem.declare_predicate("q", vec![ChcSort::Int]);

    // Trans: p(x) => q(x) (not a self-loop)
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x)]),
    ));

    let canonical_vars: Vec<ChcVar> = vec![ChcVar::new("a0", ChcSort::Int)];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(canonical_ref) };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let provider = RecurrenceConservedEqualityProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // No self-loops, so no hints
    assert!(hints.is_empty());
}

#[test]
fn test_recurrence_providers_registered() {
    // Check that all providers are registered
    // (Bounds, Recurrence, ParametricMultiplication, ModResidue, ModSum, BoolModParity)
    assert_eq!(ALWAYS_ON_HINT_PROVIDERS.len(), 1);
    assert_eq!(ARITHMETIC_HINT_PROVIDERS.len(), 5);
    assert!(has_providers());
}

#[test]
fn test_extract_aux_var_definitions() {
    use crate::ChcSort;

    // Constraint: E = v1 - F AND D = v0 + F AND F = v2 + 1
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v1 = ChcVar::new("v1", ChcSort::Int);
    let v2 = ChcVar::new("v2", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let f = ChcVar::new("F", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::var(e.clone()),
                ChcExpr::sub(ChcExpr::var(v1.clone()), ChcExpr::var(f.clone())),
            ),
            ChcExpr::eq(
                ChcExpr::var(d.clone()),
                ChcExpr::add(ChcExpr::var(v0.clone()), ChcExpr::var(f.clone())),
            ),
        ),
        ChcExpr::eq(
            ChcExpr::var(f.clone()),
            ChcExpr::add(ChcExpr::var(v2.clone()), ChcExpr::int(1)),
        ),
    );

    // Exclude canonical vars (v0, v1, v2) from being captured
    let exclude: ay_core::kani_compat::DetHashSet<&str> = ["v0", "v1", "v2"].into_iter().collect();
    let next_var_names: ay_core::kani_compat::DetHashSet<String> =
        ["v0_next", "v1_next", "v2_next"]
            .into_iter()
            .map(String::from)
            .collect();
    let defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
        &constraint,
        &exclude,
        &next_var_names,
    );

    // Should capture D, E, F but not v0, v1, v2
    assert!(defs.contains_key(&e));
    assert!(defs.contains_key(&d));
    assert!(defs.contains_key(&f));
    assert!(!defs.contains_key(&v0));
    assert!(!defs.contains_key(&v1));
    assert!(!defs.contains_key(&v2));
}

#[test]
fn test_inline_aux_vars() {
    use crate::ChcSort;

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let v2 = ChcVar::new("v2", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let f = ChcVar::new("F", ChcSort::Int);

    // Build aux var definitions: F = v2 + 1, D = v0 + F
    let mut defs: ay_core::kani_compat::DetHashMap<ChcVar, ChcExpr> =
        ay_core::kani_compat::DetHashMap::default();
    defs.insert(f.clone(), ChcExpr::add(ChcExpr::var(v2), ChcExpr::int(1)));
    defs.insert(d.clone(), ChcExpr::add(ChcExpr::var(v0), ChcExpr::var(f)));

    // Inline D: should become v0 + (v2 + 1)
    let d_expr = ChcExpr::var(d);
    let inlined = RecurrenceConservedEqualityProvider::inline_aux_vars(&d_expr, &defs);

    // After inlining, D should be replaced with v0 + F, then F with v2 + 1
    // Result: v0 + (v2 + 1)
    let vars = inlined.vars();
    let var_names: ay_core::kani_compat::DetHashSet<_> =
        vars.iter().map(|v| v.name.as_str()).collect();

    // D and F should be eliminated, only v0 and v2 remain
    assert!(!var_names.contains("D"));
    assert!(!var_names.contains("F"));
    assert!(var_names.contains("v0"));
    assert!(var_names.contains("v2"));
}

#[test]
fn test_inline_aux_vars_simplification() {
    use crate::ChcSort;

    let v2 = ChcVar::new("v2", ChcSort::Int);
    let f = ChcVar::new("F", ChcSort::Int);

    // F = v2 + 1
    let mut defs: ay_core::kani_compat::DetHashMap<ChcVar, ChcExpr> =
        ay_core::kani_compat::DetHashMap::default();
    defs.insert(f.clone(), ChcExpr::add(ChcExpr::var(v2), ChcExpr::int(1)));

    // Expr: F (just the variable)
    let expr = ChcExpr::var(f);
    let inlined = RecurrenceConservedEqualityProvider::inline_aux_vars(&expr, &defs);

    // After simplify_constants, should be: v2 + 1
    let simplified = inlined.simplify_constants();
    let vars = simplified.vars();
    assert!(vars.iter().any(|v| v.name == "v2"));
    assert!(!vars.iter().any(|v| v.name == "F"));
}

fn extract_update_rhs(transition: &ChcExpr, next_var_name: &str) -> Option<ChcExpr> {
    fn go(expr: &ChcExpr, next_var_name: &str) -> Option<ChcExpr> {
        match expr {
            ChcExpr::Op(ChcOp::And, args) if args.len() == 2 => {
                go(args[0].as_ref(), next_var_name).or_else(|| go(args[1].as_ref(), next_var_name))
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == next_var_name {
                        return Some(args[1].as_ref().clone());
                    }
                }
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if v.name == next_var_name {
                        return Some(args[0].as_ref().clone());
                    }
                }
                None
            }
            _ => None,
        }
    }

    go(transition, next_var_name)
}

#[test]
fn test_extract_transition_with_sequential_assignments() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Test case inspired by s_multipl_25_000:
    // Body: inv(B, A) with constraint F = A + 1 AND D = B + F
    // Head: inv(D, F)
    // Expected: a0_next = a0 + a1 + 1, a1_next = a1 + 1

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Variables as used in clause
    let a_var = ChcVar::new("A", ChcSort::Int);
    let b_var = ChcVar::new("B", ChcSort::Int);
    let d_var = ChcVar::new("D", ChcSort::Int);
    let f_var = ChcVar::new("F", ChcSort::Int);

    // Constraint: F = A + 1 AND D = B + F
    let constraint = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(f_var.clone()),
            ChcExpr::add(ChcExpr::var(a_var.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(d_var.clone()),
            ChcExpr::add(ChcExpr::var(b_var.clone()), ChcExpr::var(f_var.clone())),
        ),
    );

    // Body: inv(B, A) with constraint
    let body = ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(b_var), ChcExpr::var(a_var)])],
        Some(constraint),
    );

    // Head: inv(D, F)
    let head = ClauseHead::Predicate(inv, vec![ChcExpr::var(d_var), ChcExpr::var(f_var)]);

    let clause = HornClause::new(body, head);
    problem.add_clause(clause.clone());

    // Canonical vars: a0, a1
    let canonical_vars = vec![
        ChcVar::new("a0", ChcSort::Int),
        ChcVar::new("a1", ChcSort::Int),
    ];

    let result = RecurrenceConservedEqualityProvider::extract_transition(&clause, &canonical_vars);
    assert!(result.is_some(), "extract_transition should succeed");

    let (transition, state_var_names) = result.unwrap();
    assert_eq!(state_var_names, vec!["a0", "a1"]);

    // The transition should contain a0_next and a1_next
    let vars = transition.vars();
    let var_names: ay_core::kani_compat::DetHashSet<_> =
        vars.iter().map(|v| v.name.as_str()).collect();

    assert!(var_names.contains("a0_next"), "Should have a0_next");
    assert!(var_names.contains("a1_next"), "Should have a1_next");
    // Aux vars D, F should NOT appear in the result
    assert!(!var_names.contains("D"), "Aux var D should be inlined");
    assert!(!var_names.contains("F"), "Aux var F should be inlined");

    let a0_rhs = extract_update_rhs(&transition, "a0_next").expect("a0_next update missing");
    let a1_rhs = extract_update_rhs(&transition, "a1_next").expect("a1_next update missing");

    assert_eq!(format!("{}", a0_rhs.simplify_constants()), "(+ a0 a1 1)");
    assert_eq!(format!("{}", a1_rhs.simplify_constants()), "(+ a1 1)");
}

#[test]
fn test_extract_transition_with_sequential_assignments_reversed_equalities() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Same as test_extract_transition_with_sequential_assignments, but with the aux defs
    // written in reverse equality order (expr = var instead of var = expr).
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Variables as used in clause
    let a_var = ChcVar::new("A", ChcSort::Int);
    let b_var = ChcVar::new("B", ChcSort::Int);
    let d_var = ChcVar::new("D", ChcSort::Int);
    let f_var = ChcVar::new("F", ChcSort::Int);

    // Constraint: (A + 1) = F AND (B + F) = D
    let constraint = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::add(ChcExpr::var(a_var.clone()), ChcExpr::int(1)),
            ChcExpr::var(f_var.clone()),
        ),
        ChcExpr::eq(
            ChcExpr::add(ChcExpr::var(b_var.clone()), ChcExpr::var(f_var.clone())),
            ChcExpr::var(d_var.clone()),
        ),
    );

    // Body: inv(B, A) with constraint
    let body = ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(b_var), ChcExpr::var(a_var)])],
        Some(constraint),
    );

    // Head: inv(D, F)
    let head = ClauseHead::Predicate(inv, vec![ChcExpr::var(d_var), ChcExpr::var(f_var)]);

    let clause = HornClause::new(body, head);
    problem.add_clause(clause.clone());

    // Canonical vars: a0, a1
    let canonical_vars = vec![
        ChcVar::new("a0", ChcSort::Int),
        ChcVar::new("a1", ChcSort::Int),
    ];

    let result = RecurrenceConservedEqualityProvider::extract_transition(&clause, &canonical_vars);
    assert!(
        result.is_some(),
        "extract_transition should succeed with reversed equalities"
    );

    let (transition, state_var_names) = result.unwrap();
    assert_eq!(state_var_names, vec!["a0", "a1"]);

    // The transition should contain a0_next and a1_next
    let vars = transition.vars();
    let var_names: ay_core::kani_compat::DetHashSet<_> =
        vars.iter().map(|v| v.name.as_str()).collect();

    assert!(var_names.contains("a0_next"), "Should have a0_next");
    assert!(var_names.contains("a1_next"), "Should have a1_next");
    // Aux vars D, F should NOT appear in the result
    assert!(!var_names.contains("D"), "Aux var D should be inlined");
    assert!(!var_names.contains("F"), "Aux var F should be inlined");

    let a0_rhs = extract_update_rhs(&transition, "a0_next").expect("a0_next update missing");
    let a1_rhs = extract_update_rhs(&transition, "a1_next").expect("a1_next update missing");

    assert_eq!(format!("{}", a0_rhs.simplify_constants()), "(+ a0 a1 1)");
    assert_eq!(format!("{}", a1_rhs.simplify_constants()), "(+ a1 1)");
}

#[test]
fn test_extract_aux_var_definitions_rejects_self_referential() {
    use crate::ChcSort;

    // Constraint with self-referential definition: X = X + 1
    // This should NOT be captured as a definition
    let x = ChcVar::new("X", ChcSort::Int);
    let y = ChcVar::new("Y", ChcSort::Int);

    // X = X + 1 (self-referential)
    let self_ref = ChcExpr::eq(
        ChcExpr::var(x.clone()),
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
    );

    // Y = X (valid)
    let valid = ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::var(x.clone()));

    let constraint = ChcExpr::and(self_ref, valid);

    let exclude: ay_core::kani_compat::DetHashSet<&str> = Default::default();
    let next_var_names: ay_core::kani_compat::DetHashSet<String> =
        ay_core::kani_compat::DetHashSet::default();
    let defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
        &constraint,
        &exclude,
        &next_var_names,
    );

    // X should NOT be captured (self-referential)
    assert!(
        !defs.contains_key(&x),
        "Self-referential X = X + 1 should not be captured"
    );
    // Y should be captured (valid: Y = X)
    assert!(defs.contains_key(&y), "Valid Y = X should be captured");
}

#[test]
fn test_extract_aux_var_definitions_does_not_capture_both_directions() {
    use crate::ChcSort;

    // Regression test for #1235: For an equality Y = X, only capture Y -> X,
    // not also X -> Y (which creates circular aux var definitions).
    let x = ChcVar::new("X", ChcSort::Int);
    let y = ChcVar::new("Y", ChcSort::Int);

    let constraint = ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::var(x.clone()));
    let exclude: ay_core::kani_compat::DetHashSet<&str> = Default::default();
    let next_var_names: ay_core::kani_compat::DetHashSet<String> =
        ay_core::kani_compat::DetHashSet::default();
    let defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
        &constraint,
        &exclude,
        &next_var_names,
    );

    assert!(defs.contains_key(&y), "Y should be captured from Y = X");
    assert!(
        !defs.contains_key(&x),
        "X should not be captured from Y = X"
    );
}

#[test]
fn test_extract_aux_var_definitions_allows_var_with_next_substring() {
    use crate::ChcSort;

    let v0 = ChcVar::new("v0", ChcSort::Int);
    let counter_next_val = ChcVar::new("counter_next_val", ChcSort::Int);

    let constraint = ChcExpr::eq(
        ChcExpr::var(counter_next_val.clone()),
        ChcExpr::var(v0.clone()),
    );

    let exclude: ay_core::kani_compat::DetHashSet<&str> = ["v0"].into_iter().collect();
    let next_var_names: ay_core::kani_compat::DetHashSet<String> =
        ["v0_next"].into_iter().map(String::from).collect();
    let defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
        &constraint,
        &exclude,
        &next_var_names,
    );

    assert!(
        defs.contains_key(&counter_next_val),
        "counter_next_val should be captured"
    );
    assert!(
        !defs.contains_key(&v0),
        "Excluded canonical vars must not be captured"
    );
}

// Note: test_extract_aux_var_definitions_excludes_noncanonical_next_var was removed.
// User next vars like z_next SHOULD be captured as aux definitions - they define
// the transition relation (e.g., z_next = z + 1). The previous test was incorrect.
// See issue #1379 for details.

#[test]
fn test_extract_aux_var_definitions_captures_reverse_when_lhs_excluded() {
    use crate::ChcSort;

    // If the LHS is excluded (canonical var), we should still be able to capture
    // the aux variable definition from the reverse direction.
    let v0 = ChcVar::new("v0", ChcSort::Int);
    let f = ChcVar::new("F", ChcSort::Int);

    let constraint = ChcExpr::eq(ChcExpr::var(v0.clone()), ChcExpr::var(f.clone()));
    let exclude: ay_core::kani_compat::DetHashSet<&str> = ["v0"].into_iter().collect();
    let next_var_names: ay_core::kani_compat::DetHashSet<String> =
        ay_core::kani_compat::DetHashSet::default();
    let defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
        &constraint,
        &exclude,
        &next_var_names,
    );

    assert!(
        !defs.contains_key(&v0),
        "Excluded canonical vars must not be captured"
    );
    assert_eq!(
        defs.get(&f),
        Some(&ChcExpr::var(v0)),
        "F should be captured from v0 = F via reverse direction"
    );
}

#[test]
fn test_extract_aux_var_definitions_rejects_mutual_recursion() {
    use crate::ChcSort;

    // Test for #1227: Mutual recursion should be detected and rejected.
    // D = E + 1, E = D + 1 forms a cycle.
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let z = ChcVar::new("Z", ChcSort::Int);

    // D = E + 1 (part of cycle)
    let d_def = ChcExpr::eq(
        ChcExpr::var(d.clone()),
        ChcExpr::add(ChcExpr::var(e.clone()), ChcExpr::int(1)),
    );

    // E = D + 1 (part of cycle)
    let e_def = ChcExpr::eq(
        ChcExpr::var(e.clone()),
        ChcExpr::add(ChcExpr::var(d.clone()), ChcExpr::int(1)),
    );

    // Z = 42 (not part of cycle, should be kept)
    let z_def = ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::int(42));

    let constraint = ChcExpr::and(ChcExpr::and(d_def, e_def), z_def);

    let exclude: ay_core::kani_compat::DetHashSet<&str> = Default::default();
    let next_var_names: ay_core::kani_compat::DetHashSet<String> =
        ay_core::kani_compat::DetHashSet::default();
    let defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
        &constraint,
        &exclude,
        &next_var_names,
    );

    // D and E should NOT be captured (mutual recursion)
    assert!(
        !defs.contains_key(&d),
        "Mutually recursive D should not be captured"
    );
    assert!(
        !defs.contains_key(&e),
        "Mutually recursive E should not be captured"
    );
    // Z should be captured (not part of cycle)
    assert!(
        defs.contains_key(&z),
        "Non-cyclic Z = 42 should be captured"
    );
}

#[test]
fn test_extract_aux_var_definitions_rejects_transitive_cycle() {
    use crate::ChcSort;

    // Test for #1227: Transitive cycle A -> B -> C -> A
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    // A = B + 1
    let a_def = ChcExpr::eq(
        ChcExpr::var(a.clone()),
        ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(1)),
    );

    // B = C + 1
    let b_def = ChcExpr::eq(
        ChcExpr::var(b.clone()),
        ChcExpr::add(ChcExpr::var(c.clone()), ChcExpr::int(1)),
    );

    // C = A + 1 (completes the cycle)
    let c_def = ChcExpr::eq(
        ChcExpr::var(c.clone()),
        ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(1)),
    );

    let constraint = ChcExpr::and(ChcExpr::and(a_def, b_def), c_def);

    let exclude: ay_core::kani_compat::DetHashSet<&str> = Default::default();
    let next_var_names: ay_core::kani_compat::DetHashSet<String> =
        ay_core::kani_compat::DetHashSet::default();
    let defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
        &constraint,
        &exclude,
        &next_var_names,
    );

    // All three should be rejected due to cycle
    assert!(!defs.contains_key(&a), "Cyclic A should not be captured");
    assert!(!defs.contains_key(&b), "Cyclic B should not be captured");
    assert!(!defs.contains_key(&c), "Cyclic C should not be captured");
}
