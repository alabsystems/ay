// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// compute_materialization_delta() tests — InfRational → BigRational conversion
// ============================================================================

/// When no variables have epsilon components, delta should default to 1/2.
#[test]
fn test_materialization_delta_no_epsilon() {
    let terms = TermStore::new();
    let solver = LraSolver::new(&terms);
    let delta = solver.compute_materialization_delta();
    // Default delta = 1 / 2 (halved from initial 1)
    assert_eq!(
        delta,
        BigRational::new(BigInt::from(1), BigInt::from(2)),
        "no epsilon vars → delta = 1/2"
    );
}

/// Delta must be constrained by upper bound when epsilon is positive.
/// If var has value (3, +ε) and upper bound 5, then:
///   3 + 1*δ ≤ 5 → δ ≤ 2 → halved → δ = 1 (but capped by initial 1)
/// So final delta = min(1, 2) / 2 = 1/2.
#[test]
fn test_materialization_delta_positive_epsilon_upper_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    // x >= 3 (lower bound) and x <= 5 (upper bound)
    // After strict x > 3, simplex sets x = 3 + ε
    let atom_gt = terms.mk_gt(x, three); // x > 3 (strict)
    let atom_le = terms.mk_le(x, five); // x <= 5

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(atom_gt, true);
    solver.assert_literal(atom_le, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let delta = solver.compute_materialization_delta();
    // delta must be positive
    assert!(
        delta > BigRational::zero(),
        "delta must be positive, got {delta}"
    );
    // Materialize x: should be 3 + epsilon * delta, which must be <= 5
    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    let x_val = &solver.vars[x_var as usize].value;
    let materialized = x_val.materialize(&delta);
    assert!(
        materialized > BigRational::from(BigInt::from(3)),
        "materialized x must be > 3, got {materialized}"
    );
    assert!(
        materialized <= BigRational::from(BigInt::from(5)),
        "materialized x must be <= 5, got {materialized}"
    );
}

/// The δ envelope is the exact minimum over every ε-carrying variable's
/// slack/|ε| candidate, halved — including candidates whose ε magnitude
/// is not 1 and candidates at big-rational scales. Pins the exact value
/// so the scan's min-tracking arithmetic cannot drift.
#[test]
fn test_materialization_delta_exact_minimum_over_candidates() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let third = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(3)));
    let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let one = terms.mk_rational(BigRational::one());
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let a_gt = terms.mk_gt(a, zero);
    let a_le = terms.mk_le(a, third);
    let b_gt = terms.mk_gt(b, zero);
    let b_le = terms.mk_le(b, half);
    let c_ge = terms.mk_ge(c, zero);
    let c_lt = terms.mk_lt(c, one);

    let mut solver = LraSolver::new(&terms);
    for atom in [a_gt, a_le, b_gt, b_le, c_ge, c_lt] {
        solver.register_atom(atom);
        solver.assert_literal(atom, true);
    }
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // a = 0 + ε (candidate (1/3)/1), b = 0 + 2ε (candidate (1/2)/2 = 1/4,
    // the minimum), c = 1 − ε (candidate (1−0)/1, above the cap).
    let set_value = |solver: &mut LraSolver, var: TermId, x: BigRational, y: BigRational| {
        let idx = *solver.term_to_var.get(&var).expect("var registered");
        solver.vars[idx as usize].value = InfRational::new(x, y);
    };
    set_value(&mut solver, a, BigRational::zero(), BigRational::one());
    set_value(
        &mut solver,
        b,
        BigRational::zero(),
        BigRational::from(BigInt::from(2)),
    );
    set_value(&mut solver, c, BigRational::one(), -BigRational::one());

    let delta = solver.compute_materialization_delta();
    assert_eq!(
        delta,
        BigRational::new(BigInt::from(1), BigInt::from(8)),
        "delta must be min(1, 1/3, 1/4, 1) halved = 1/8"
    );
}

/// Same exact-minimum contract at a scale past the i64 fast path:
/// a bound at 1/10^25 must yield δ = 1/(2·10^25) exactly.
#[test]
fn test_materialization_delta_exact_at_big_scale() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let tiny = terms.mk_rational(BigRational::new(
        BigInt::from(1),
        BigInt::parse_bytes(b"10000000000000000000000000", 10).expect("decimal"),
    ));
    let d = terms.mk_var("d", Sort::Real);
    let d_gt = terms.mk_gt(d, zero);
    let d_le = terms.mk_le(d, tiny);

    let mut solver = LraSolver::new(&terms);
    for atom in [d_gt, d_le] {
        solver.register_atom(atom);
        solver.assert_literal(atom, true);
    }
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let idx = *solver.term_to_var.get(&d).expect("d registered");
    solver.vars[idx as usize].value = InfRational::new(BigRational::zero(), BigRational::one());

    let delta = solver.compute_materialization_delta();
    assert_eq!(
        delta,
        BigRational::new(
            BigInt::from(1),
            BigInt::parse_bytes(b"20000000000000000000000000", 10).expect("decimal"),
        ),
        "delta must be (1/10^25) halved exactly"
    );
}

/// #7654: extract_model() must snap asserted single-variable equalities back
/// to their exact constant instead of returning a delta-shifted value.
/// An asserted disequality whose simplex value is `x + k·ε` (accepted by the
/// check: not zero) must not be zeroed by the materialisation δ
/// (DPLL_LRA_perf_2026-09-23 §1). `x > 0`, `x <= 1`, `2x = 1` asserted false,
/// `x = 0+ε`: the bound envelope alone gives δ = 1/2 and publishes x = 1/2.
#[test]
fn test_materialization_delta_avoids_disequality_zero_point() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::one());
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let two_x = terms.mk_mul(vec![two, x]);
    let x_gt_zero = terms.mk_gt(x, zero);
    let x_le_one = terms.mk_le(x, one);
    let two_x_eq_one = terms.mk_eq(two_x, one);

    let mut solver = LraSolver::new(&terms);
    for atom in [x_gt_zero, x_le_one, two_x_eq_one] {
        solver.register_atom(atom);
    }
    solver.assert_literal(x_gt_zero, true);
    solver.assert_literal(x_le_one, true);
    solver.assert_literal(two_x_eq_one, false);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    solver.vars[x_var as usize].value = InfRational::new(BigRational::zero(), BigRational::one());

    let model = solver.extract_model();
    let x_val = model
        .values
        .get(&x)
        .expect("x must be in the model")
        .clone();
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    assert!(
        x_val > BigRational::zero() && x_val <= BigRational::one(),
        "materialised x must keep its bounds, got {x_val}"
    );
    assert_ne!(
        x_val, half,
        "materialised x must not land on the excluded 2x = 1"
    );
}

#[test]
fn test_extract_model_snaps_asserted_single_var_equality_7654() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let eq_atom = terms.mk_eq(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq_atom);
    solver.assert_literal(eq_atom, true);

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    solver.vars[x_var as usize].value = InfRational::new(BigRational::zero(), BigRational::one());

    let model = solver.extract_model();
    assert_eq!(
        model.values.get(&x),
        Some(&BigRational::zero()),
        "extract_model must snap x = 0 exactly"
    );
}

/// #7654: after snapping a direct equality to an exact value, extract_model()
/// must propagate that exact value through asserted two-variable equalities.
#[test]
fn test_extract_model_propagates_snapped_equality_value_7654() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let x_eq_zero = terms.mk_eq(x, zero);
    let y_eq_x = terms.mk_eq(y, x);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_eq_zero);
    solver.register_atom(y_eq_x);
    solver.assert_literal(x_eq_zero, true);
    solver.assert_literal(y_eq_x, true);

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    let y_var = *solver.term_to_var.get(&y).expect("y must be registered");
    solver.vars[x_var as usize].value = InfRational::new(BigRational::zero(), BigRational::one());
    solver.vars[y_var as usize].value =
        InfRational::from_rational(BigRational::from(BigInt::from(7)));

    let model = solver.extract_model();
    assert_eq!(
        model.values.get(&x),
        Some(&BigRational::zero()),
        "direct equality must snap x to 0"
    );
    assert_eq!(
        model.values.get(&y),
        Some(&BigRational::zero()),
        "y = x must inherit the exact snapped value"
    );
}

/// #7654 follow-up: `distinct` asserted false is semantically equality, and
/// exact snapped values must propagate through equality chains, not just one hop.
#[test]
fn test_extract_model_propagates_negated_distinct_through_chain_7654() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let x_ne_zero = terms.mk_distinct(vec![x, zero]);
    let y_eq_x = terms.mk_eq(y, x);
    let z_eq_y = terms.mk_eq(z, y);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ne_zero);
    solver.register_atom(y_eq_x);
    solver.register_atom(z_eq_y);
    solver.assert_literal(x_ne_zero, false);
    solver.assert_literal(y_eq_x, true);
    solver.assert_literal(z_eq_y, true);

    let x_var = *solver.term_to_var.get(&x).expect("x must be registered");
    let y_var = *solver.term_to_var.get(&y).expect("y must be registered");
    let z_var = *solver.term_to_var.get(&z).expect("z must be registered");
    solver.vars[x_var as usize].value = InfRational::new(BigRational::zero(), BigRational::one());
    solver.vars[y_var as usize].value =
        InfRational::from_rational(BigRational::from(BigInt::from(7)));
    solver.vars[z_var as usize].value =
        InfRational::from_rational(BigRational::from(BigInt::from(9)));

    let model = solver.extract_model();
    assert_eq!(
        model.values.get(&x),
        Some(&BigRational::zero()),
        "negated distinct must snap x to 0 exactly"
    );
    assert_eq!(
        model.values.get(&y),
        Some(&BigRational::zero()),
        "y = x must inherit the snapped value"
    );
    assert_eq!(
        model.values.get(&z),
        Some(&BigRational::zero()),
        "z = y must inherit the snapped value transitively"
    );
}

// ─── propagate_model_equalities tests ───────────────────────────────────

/// Two-variable equality x + y = 0 (i.e., y = -x). After patching x = 7,
/// propagate_model_equalities should set y = -7.
#[test]
fn test_propagate_model_equalities_basic_two_var() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq_atom = terms.mk_eq(x, y); // x = y, parsed as x - y = 0

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq_atom);
    solver.assert_literal(eq_atom, true);
    // Run check so model is populated
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x registered");

    // Build model with patched x = 7
    let seven = BigRational::from(BigInt::from(7));
    let mut model = LraModel {
        values: HashMap::default(),
    };
    model.values.insert(x, seven.clone());
    model.values.insert(y, BigRational::zero()); // initial y

    let mut patched = HashSet::default();
    patched.insert(x_var);

    solver.propagate_model_equalities(&mut model, &patched);

    // x = y, so after patching x = 7, y should become 7
    let y_val = model.values.get(&y).expect("y must be in model");
    assert_eq!(*y_val, seven, "y should be propagated to 7 via x = y");
}

/// When the patched variable is the second coefficient in the equality,
/// propagation should still work (reverse direction).
#[test]
fn test_propagate_model_equalities_reverse_direction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq_atom = terms.mk_eq(x, y); // x = y

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq_atom);
    solver.assert_literal(eq_atom, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let y_var = *solver.term_to_var.get(&y).expect("y registered");

    // Patch y = 3, should propagate to x = 3
    let three = BigRational::from(BigInt::from(3));
    let mut model = LraModel {
        values: HashMap::default(),
    };
    model.values.insert(x, BigRational::zero());
    model.values.insert(y, three.clone());

    let mut patched = HashSet::default();
    patched.insert(y_var);

    solver.propagate_model_equalities(&mut model, &patched);

    let x_val = model.values.get(&x).expect("x must be in model");
    assert_eq!(*x_val, three, "x should be propagated to 3 via x = y");
}

/// Negated equality (asserted false) should NOT trigger propagation.
#[test]
fn test_propagate_model_equalities_negated_equality_no_propagation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let eq_atom = terms.mk_eq(x, y);
    let x_ge = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq_atom);
    // Assert equality as FALSE
    solver.assert_literal(eq_atom, false);
    solver.assert_literal(x_ge, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x registered");

    let mut model = LraModel {
        values: HashMap::default(),
    };
    model.values.insert(x, BigRational::from(BigInt::from(10)));
    model.values.insert(y, BigRational::from(BigInt::from(99)));

    let mut patched = HashSet::default();
    patched.insert(x_var);

    solver.propagate_model_equalities(&mut model, &patched);

    // y should NOT be changed because equality was negated
    let y_val = model.values.get(&y).expect("y must be in model");
    assert_eq!(
        *y_val,
        BigRational::from(BigInt::from(99)),
        "y should NOT be propagated when equality is false"
    );
}

/// Negated distinct is semantically equality, so propagation should occur.
#[test]
fn test_propagate_model_equalities_negated_distinct_propagation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ne_atom = terms.mk_distinct(vec![x, y]);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ne_atom);
    solver.assert_literal(ne_atom, false);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x registered");

    let five = BigRational::from(BigInt::from(5));
    let mut model = LraModel {
        values: HashMap::default(),
    };
    model.values.insert(x, five.clone());
    model.values.insert(y, BigRational::zero());

    let mut patched = HashSet::default();
    patched.insert(x_var);

    solver.propagate_model_equalities(&mut model, &patched);

    let y_val = model.values.get(&y).expect("y must be in model");
    assert_eq!(
        *y_val, five,
        "y should be propagated when distinct is asserted false"
    );
}

/// No patched variables means no propagation occurs.
#[test]
fn test_propagate_model_equalities_empty_patched_set() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq_atom = terms.mk_eq(x, y);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq_atom);
    solver.assert_literal(eq_atom, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let mut model = LraModel {
        values: HashMap::default(),
    };
    model.values.insert(x, BigRational::from(BigInt::from(42)));
    model.values.insert(y, BigRational::from(BigInt::from(0)));

    let patched = HashSet::default(); // empty

    solver.propagate_model_equalities(&mut model, &patched);

    // Neither x nor y should change
    assert_eq!(
        *model.values.get(&y).unwrap(),
        BigRational::from(BigInt::from(0)),
        "y should be unchanged with empty patched set"
    );
}
