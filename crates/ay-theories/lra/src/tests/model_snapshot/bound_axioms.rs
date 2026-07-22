// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ─── sort_atom_index tests ──────────────────────────────────────────────

/// sort_atom_index sorts atom entries by bound_value within each variable.
#[test]
fn test_sort_atom_index_orders_by_bound_value() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    // Register atoms in non-sorted order: x<=10, x<=3, x<=7
    let a10 = terms.mk_le(x, ten);
    let a3 = terms.mk_le(x, three);
    let a7 = terms.mk_le(x, seven);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(a10);
    solver.register_atom(a3);
    solver.register_atom(a7);

    solver.sort_atom_index();

    let x_var = *solver.term_to_var.get(&x).expect("x registered");
    let atoms = solver.atom_index.get(&x_var).expect("atom_index for x");
    assert!(atoms.len() >= 3, "should have at least 3 atoms for x");

    // Verify sorted ascending by bound_value
    for i in 1..atoms.len() {
        assert!(
            atoms[i - 1].bound_value <= atoms[i].bound_value,
            "atom_index not sorted: {} > {} at positions {}, {}",
            atoms[i - 1].bound_value,
            atoms[i].bound_value,
            i - 1,
            i
        );
    }
}

/// sort_atom_index with a single atom is a no-op.
#[test]
fn test_sort_atom_index_single_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(atom);

    solver.sort_atom_index();

    let x_var = *solver.term_to_var.get(&x).expect("x registered");
    let atoms = solver.atom_index.get(&x_var).expect("atom_index for x");
    assert_eq!(atoms.len(), 1, "single atom");
    assert_eq!(atoms[0].bound_value, Rational::from(5));
}

/// sort_atom_index handles multiple variables independently.
#[test]
fn test_sort_atom_index_multiple_variables() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);

    // x atoms: x <= 9, x <= 1
    let r9 = terms.mk_rational(BigRational::from(BigInt::from(9)));
    let x9 = terms.mk_le(x, r9);
    let r1 = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let x1 = terms.mk_le(x, r1);
    // y atoms: y <= 8, y <= 2
    let r8 = terms.mk_rational(BigRational::from(BigInt::from(8)));
    let y8 = terms.mk_le(y, r8);
    let r2 = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let y2 = terms.mk_le(y, r2);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x9);
    solver.register_atom(x1);
    solver.register_atom(y8);
    solver.register_atom(y2);

    solver.sort_atom_index();

    let x_var = *solver.term_to_var.get(&x).expect("x registered");
    let y_var = *solver.term_to_var.get(&y).expect("y registered");

    let x_atoms = solver.atom_index.get(&x_var).expect("atom_index for x");
    assert!(
        x_atoms[0].bound_value <= x_atoms[1].bound_value,
        "x atoms sorted"
    );

    let y_atoms = solver.atom_index.get(&y_var).expect("atom_index for y");
    assert!(
        y_atoms[0].bound_value <= y_atoms[1].bound_value,
        "y atoms sorted"
    );
}

// ─── generate_bound_axiom_terms tests ───────────────────────────────────

/// With two lower bounds on the same variable (x >= 3, x >= 7),
/// generate_bound_axiom_terms produces an implication axiom.
#[test]
fn test_generate_bound_axiom_terms_two_lower_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge7 = terms.mk_ge(x, seven); // x >= 7

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge3);
    solver.register_atom(ge7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for two lower bounds on same variable"
    );
    // With two lower bounds, the axiom should encode:
    // (x >= 7) => (x >= 3), i.e., ~ge7 | ge3
    // The tuple format is (term1, pol1, term2, pol2)
    let has_expected = axioms.iter().any(|&(t1, p1, t2, p2)| {
        // ~ge7 | ge3  OR  ge3 | ~ge7  (depending on order in mk_bound_axiom_terms)
        (t1 == ge7 && !p1 && t2 == ge3 && p2) || (t1 == ge3 && p1 && t2 == ge7 && !p2)
    });
    assert!(
        has_expected,
        "expected axiom encoding (x>=7) => (x>=3), got: {axioms:?}",
    );
}

/// With two upper bounds on the same variable (x <= 3, x <= 7),
/// generate_bound_axiom_terms produces an implication axiom.
#[test]
fn test_generate_bound_axiom_terms_two_upper_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let le3 = terms.mk_le(x, three); // x <= 3
    let le7 = terms.mk_le(x, seven); // x <= 7

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(le3);
    solver.register_atom(le7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for two upper bounds on same variable"
    );
    // (x <= 3) => (x <= 7), i.e., ~le3 | le7
    // mk_bound_axiom_terms: both upper, k1=7 >= k2=3 → l1 | ~l2 where b1.is_upper
    // But which is b1? Depends on iteration order. Check both orientations.
    let has_expected = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (t1 == le3 && !p1 && t2 == le7 && p2) || (t1 == le7 && p1 && t2 == le3 && !p2)
    });
    assert!(
        has_expected,
        "expected axiom encoding (x<=3) => (x<=7), got: {axioms:?}",
    );
}

/// Lower and upper bounds on the same variable with compatible ranges produce
/// a tautology-aiding axiom (l1 | l2).
#[test]
fn test_generate_bound_axiom_terms_lower_upper_compatible() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let ge3 = terms.mk_ge(x, three); // x >= 3 (lower)
    let le7 = terms.mk_le(x, seven); // x <= 7 (upper)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge3);
    solver.register_atom(le7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for lower + upper bounds"
    );
    // Lower k1=3 <= upper k2=7 → tautology: l1 | l2
    let has_tautology = axioms.iter().any(|&(t1, p1, t2, p2)| {
        // Either (ge3, true, le7, true) or (le7, true, ge3, true)
        (p1 && p2) && ((t1 == ge3 && t2 == le7) || (t1 == le7 && t2 == ge3))
    });
    assert!(
        has_tautology,
        "expected tautology axiom (ge3 | le7), got: {axioms:?}",
    );
}

/// With conflicting lower > upper bounds (x >= 7, x <= 3), generate
/// a conflict-exclusion axiom (~l1 | ~l2).
#[test]
fn test_generate_bound_axiom_terms_lower_upper_conflicting() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let ge7 = terms.mk_ge(x, seven); // x >= 7 (lower, k=7)
    let le3 = terms.mk_le(x, three); // x <= 3 (upper, k=3)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge7);
    solver.register_atom(le3);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    assert!(
        !axioms.is_empty(),
        "should generate at least one axiom for conflicting bounds"
    );
    // Lower k=7 > upper k=3 → conflict exclusion: ~l1 | ~l2
    let has_conflict = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (!p1 && !p2) && ((t1 == ge7 && t2 == le3) || (t1 == le3 && t2 == ge7))
    });
    assert!(
        has_conflict,
        "expected conflict axiom (~ge7 | ~le3), got: {axioms:?}",
    );
}

/// An equality atom with a single variable (x = 5) generates one-directional
/// axioms to related bound atoms.
#[test]
fn test_generate_bound_axiom_terms_equality_to_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));

    let eq5 = terms.mk_eq(x, five); // x = 5
    let ge3 = terms.mk_ge(x, three); // x >= 3 (lower, k=3)
    let le7 = terms.mk_le(x, seven); // x <= 7 (upper, k=7)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq5);
    solver.register_atom(ge3);
    solver.register_atom(le7);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();

    // (x = 5) → (x >= 3): ~eq5 | ge3
    let has_eq_to_lower = axioms
        .iter()
        .any(|&(t1, p1, t2, p2)| t1 == eq5 && !p1 && t2 == ge3 && p2);
    assert!(
        has_eq_to_lower,
        "expected axiom (x=5) => (x>=3), i.e., ~eq5 | ge3. Got: {axioms:?}",
    );

    // (x = 5) → (x <= 7): ~eq5 | le7
    let has_eq_to_upper = axioms
        .iter()
        .any(|&(t1, p1, t2, p2)| t1 == eq5 && !p1 && t2 == le7 && p2);
    assert!(
        has_eq_to_upper,
        "expected axiom (x=5) => (x<=7), i.e., ~eq5 | le7. Got: {axioms:?}",
    );
}

/// No atoms registered → generate_bound_axiom_terms returns empty.
#[test]
fn test_generate_bound_axiom_terms_empty() {
    let terms = TermStore::new();
    let solver = LraSolver::new(&terms);
    let axioms = solver.generate_bound_axiom_terms_inner();
    assert!(axioms.is_empty(), "no atoms → no axioms");
}

/// Single atom → no pairs → no axioms (need at least 2 atoms per variable).
#[test]
fn test_generate_bound_axiom_terms_single_atom_no_axioms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let le5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(le5);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    assert!(
        axioms.is_empty(),
        "single atom per variable → no bound pair axioms"
    );
}

// ─── generate_incremental_bound_axioms tests (#4919) ──────────────────────

/// Incremental bound axiom generation returns nearest-neighbor axioms for a
/// newly-registered atom against existing atoms on the same variable.
#[test]
fn test_generate_incremental_bound_axioms_nearest_neighbors() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let ge1 = terms.mk_ge(x, one); // x >= 1
    let ge3 = terms.mk_ge(x, three); // x >= 3
    let ge5 = terms.mk_ge(x, five); // x >= 5

    let mut solver = LraSolver::new(&terms);
    // Register the outer bounds first
    solver.register_atom(ge1);
    solver.register_atom(ge5);
    solver.sort_atom_index();

    // Now generate incremental axioms for ge3 (the middle bound)
    // ge3 must also be registered so atom_cache has its info
    solver.register_atom(ge3);
    solver.sort_atom_index();

    let axioms = solver.generate_incremental_bound_axioms_inner(ge3);
    assert!(
        !axioms.is_empty(),
        "should generate axioms for ge3 vs nearest neighbors ge1 and ge5"
    );

    // ge5 => ge3 (stronger lower bound implies weaker): ~ge5 | ge3
    let has_ge5_implies_ge3 = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (t1 == ge5 && !p1 && t2 == ge3 && p2) || (t1 == ge3 && p1 && t2 == ge5 && !p2)
    });
    assert!(
        has_ge5_implies_ge3,
        "expected axiom (x>=5) => (x>=3), got: {axioms:?}",
    );

    // ge3 => ge1 (stronger lower bound implies weaker): ~ge3 | ge1
    let has_ge3_implies_ge1 = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (t1 == ge3 && !p1 && t2 == ge1 && p2) || (t1 == ge1 && p1 && t2 == ge3 && !p2)
    });
    assert!(
        has_ge3_implies_ge1,
        "expected axiom (x>=3) => (x>=1), got: {axioms:?}",
    );

    // At most 4 axioms (nearest-neighbor strategy)
    assert!(
        axioms.len() <= 4,
        "nearest-neighbor should produce at most 4 axioms, got {}",
        axioms.len()
    );
}

/// Incremental bound axioms for an atom with no existing neighbors returns empty.
#[test]
fn test_generate_incremental_bound_axioms_no_neighbors() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ge5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge5);
    solver.sort_atom_index();

    let axioms = solver.generate_incremental_bound_axioms_inner(ge5);
    assert!(
        axioms.is_empty(),
        "single atom per variable → no neighbors → no axioms"
    );
}

/// Incremental bound axioms skip equality/distinct atoms.
#[test]
fn test_generate_incremental_bound_axioms_skips_eq() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let eq5 = terms.mk_eq(x, five); // x = 5

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(eq5);
    solver.sort_atom_index();

    let axioms = solver.generate_incremental_bound_axioms_inner(eq5);
    assert!(
        axioms.is_empty(),
        "equality atoms should be skipped (handled by eq-to-bound path)"
    );
}

// ─── Integer trichotomy soundness tests (seed-981) ─────────────────

/// Integer mode, adjacent INTEGER bounds: (x <= 2) ∨ (x >= 3) is a genuine
/// tautology over the integers and must still be generated.
#[test]
fn test_integer_trichotomy_generated_for_adjacent_integer_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    // SMT-LIB: an integer var with a rational bound coerces the Int side via to_real.
    let xr = terms.mk_to_real(x);
    let le2 = terms.mk_le(xr, two); // x <= 2 (upper)
    let ge3 = terms.mk_ge(xr, three); // x >= 3 (lower)

    let mut solver = LraSolver::new(&terms);
    solver.set_integer_mode(true);
    solver.register_atom(le2);
    solver.register_atom(ge3);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    let has_trichotomy = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (p1 && p2) && ((t1 == le2 && t2 == ge3) || (t1 == ge3 && t2 == le2))
    });
    assert!(
        has_trichotomy,
        "expected integer trichotomy (x<=2 | x>=3), got: {axioms:?}"
    );
}

/// Seed-981 regression: FRACTIONAL bounds exactly 1 apart must NOT
/// produce a trichotomy axiom. `(<= 5 (* -3 x))` and `(<= (* -3 x) 2)`
/// normalize to upper bound x <= -5/3 and lower bound x >= -2/3 — values
/// exactly 1 apart, but the integer x = -1 sits in the open gap, so
/// (x <= -5/3) ∨ (x >= -2/3) is NOT a tautology over the integers. The old
/// `k1 == k2 - 1` check emitted it; injected without validation on the
/// incremental path, it flipped a satisfiable instance to a false UNSAT.
#[test]
fn test_integer_trichotomy_not_generated_for_fractional_gap_with_integer() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let minus_5_3 = terms.mk_rational(BigRational::new(BigInt::from(-5), BigInt::from(3)));
    let minus_2_3 = terms.mk_rational(BigRational::new(BigInt::from(-2), BigInt::from(3)));

    // SMT-LIB: an integer var with a rational bound coerces the Int side via to_real.
    let xr = terms.mk_to_real(x);
    let upper = terms.mk_le(xr, minus_5_3); // x <= -5/3 (upper)
    let lower = terms.mk_ge(xr, minus_2_3); // x >= -2/3 (lower)

    let mut solver = LraSolver::new(&terms);
    solver.set_integer_mode(true);
    solver.register_atom(upper);
    solver.register_atom(lower);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    let has_trichotomy = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (p1 && p2) && ((t1 == upper && t2 == lower) || (t1 == lower && t2 == upper))
    });
    assert!(
        !has_trichotomy,
        "unsound trichotomy (x<=-5/3 | x>=-2/3) excludes integer x=-1; got: {axioms:?}"
    );
    // The conflict-exclusion axiom (~upper | ~lower) IS sound and expected.
    let has_conflict = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (!p1 && !p2) && ((t1 == upper && t2 == lower) || (t1 == lower && t2 == upper))
    });
    assert!(
        has_conflict,
        "expected sound conflict axiom (~upper | ~lower), got: {axioms:?}"
    );
}

/// The exact gap test also accepts sound fractional cases the old
/// `k1 == k2 - 1` equality missed: (x <= 5/2) ∨ (x >= 14/5) has no integer
/// in the open gap (2.5, 2.8), so it IS a tautology over the integers.
#[test]
fn test_integer_trichotomy_generated_for_fractional_empty_gap() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five_halves = terms.mk_rational(BigRational::new(BigInt::from(5), BigInt::from(2)));
    let fourteen_fifths = terms.mk_rational(BigRational::new(BigInt::from(14), BigInt::from(5)));

    // SMT-LIB: an integer var with a rational bound coerces the Int side via to_real.
    let xr = terms.mk_to_real(x);
    let upper = terms.mk_le(xr, five_halves); // x <= 5/2 (upper)
    let lower = terms.mk_ge(xr, fourteen_fifths); // x >= 14/5 (lower)

    let mut solver = LraSolver::new(&terms);
    solver.set_integer_mode(true);
    solver.register_atom(upper);
    solver.register_atom(lower);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    let has_trichotomy = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (p1 && p2) && ((t1 == upper && t2 == lower) || (t1 == lower && t2 == upper))
    });
    assert!(
        has_trichotomy,
        "no integer lies in (5/2, 14/5): (x<=5/2 | x>=14/5) is an integer \
         tautology and should be generated; got: {axioms:?}"
    );
}

/// Rational (non-integer) mode must never emit trichotomy axioms, even for
/// adjacent integer bounds: x = 2.5 violates (x <= 2) ∨ (x >= 3) over Real.
#[test]
fn test_integer_trichotomy_not_generated_in_rational_mode() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let le2 = terms.mk_le(x, two);
    let ge3 = terms.mk_ge(x, three);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(le2);
    solver.register_atom(ge3);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    let has_trichotomy = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (p1 && p2) && ((t1 == le2 && t2 == ge3) || (t1 == ge3 && t2 == le2))
    });
    assert!(
        !has_trichotomy,
        "trichotomy is unsound over Real (x=2.5 in the gap); got: {axioms:?}"
    );
}

// ─── Batch bound axiom scaling tests (#4919 Phase 4, #8256) ────────────────

/// With 10 lower bounds on the same variable (below ALL_PAIRS_THRESHOLD=30),
/// the all-pairs path produces n*(n-1)/2 = 45 axiom pairs (after dedup by
/// the `seen` set, some may be filtered). This matches Z3's mk_bound_axioms
/// which generates axioms between ALL bounds on the same theory variable.
#[test]
fn test_generate_bound_axiom_terms_batch_all_pairs_scaling() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);

    // Register 10 lower bounds: x >= 1, x >= 2, ..., x >= 10
    let mut atoms = Vec::new();
    for i in 1..=10 {
        let r = terms.mk_rational(BigRational::from(BigInt::from(i)));
        let ge = terms.mk_ge(x, r);
        atoms.push(ge);
    }

    let mut solver = LraSolver::new(&terms);
    for &a in &atoms {
        solver.register_atom(a);
    }
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();

    // With all-pairs (#8256), 10 atoms below the ALL_PAIRS_THRESHOLD
    // produce up to C(10,2)*2 = 90 directed axiom pairs. After dedup
    // via the `seen` set, the actual count depends on bound_value
    // ordering and polarity. Must be > nearest-neighbor (~9) and <= 90.
    assert!(
        axioms.len() >= 20,
        "all-pairs should produce more axioms than nearest-neighbor (~9), got {}",
        axioms.len()
    );
    assert!(
        !axioms.is_empty(),
        "should generate axioms for 10 lower bounds"
    );

    // Verify consecutive pairs are connected: for each pair (ge_i, ge_{i+1}),
    // there should be an axiom encoding ge_{i+1} => ge_i.
    for w in atoms.windows(2) {
        let (weaker, stronger) = (w[0], w[1]);
        let has_pair = axioms.iter().any(|&(t1, p1, t2, p2)| {
            (t1 == stronger && !p1 && t2 == weaker && p2)
                || (t1 == weaker && p1 && t2 == stronger && !p2)
        });
        assert!(
            has_pair,
            "missing axiom for consecutive pair (stronger={stronger:?} => weaker={weaker:?})"
        );
    }
}

/// Mixed bound kinds (lower + upper) in the batch path produce the correct
/// axiom types: tautology, conflict, and implication.
#[test]
fn test_generate_bound_axiom_terms_batch_mixed_kinds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let eight = terms.mk_rational(BigRational::from(BigInt::from(8)));

    let ge2 = terms.mk_ge(x, two); // x >= 2 (lower)
    let le5 = terms.mk_le(x, five); // x <= 5 (upper)
    let ge8 = terms.mk_ge(x, eight); // x >= 8 (lower)

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge2);
    solver.register_atom(le5);
    solver.register_atom(ge8);
    solver.sort_atom_index();

    let axioms = solver.generate_bound_axiom_terms_inner();
    assert!(
        !axioms.is_empty(),
        "should generate axioms for mixed bound kinds"
    );

    // ge2 (lower, k=2) and le5 (upper, k=5): k_lower <= k_upper -> tautology (l1 | l2)
    let has_tautology = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (p1 && p2) && ((t1 == ge2 && t2 == le5) || (t1 == le5 && t2 == ge2))
    });
    assert!(
        has_tautology,
        "expected tautology axiom (ge2 | le5), got: {axioms:?}"
    );

    // ge8 (lower, k=8) and le5 (upper, k=5): k_lower > k_upper -> conflict (~l1 | ~l2)
    let has_conflict = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (!p1 && !p2) && ((t1 == ge8 && t2 == le5) || (t1 == le5 && t2 == ge8))
    });
    assert!(
        has_conflict,
        "expected conflict axiom (~ge8 | ~le5), got: {axioms:?}"
    );

    // ge8 (lower, k=8) => ge2 (lower, k=2): implication (~ge8 | ge2)
    let has_implication = axioms.iter().any(|&(t1, p1, t2, p2)| {
        (t1 == ge8 && !p1 && t2 == ge2 && p2) || (t1 == ge2 && p1 && t2 == ge8 && !p2)
    });
    assert!(
        has_implication,
        "expected implication axiom (ge8 => ge2), got: {axioms:?}"
    );
}
