// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A modular "unique value excluded by a disequality" conflict must cite the
//! NEGATED atoms its bound window rests on.
//!
//! `x = 4y + 2` (so `x ≡ 2 (mod 4)`) with `(not (<= x 147))`,
//! `(not (>= x 152))` and `(not (= x 150))`: the window `[148, 151]` holds one
//! residue, 150, and the disequality excludes it — a correct refutation of
//! this assignment. The conflict used to keep only the TRUE-valued asserted
//! literals, i.e. `x = 4y + 2 → x = 150`, which is false (`x = 162`): with
//! `(or (> x 151) (and (> x 147) (< x 152)))` around it, planted-sat
//! `puniq_31_00276` of the linear hunt was answered `unsat` by main
//! 8b71d73999 in both postures.

use super::*;
use ay_core::DisequalitySplitRequest;
use num_bigint::BigInt;
use num_rational::BigRational;

struct Fixture {
    terms: TermStore,
    x: TermId,
    y: TermId,
    eq: TermId,
    le147: TermId,
    ge152: TermId,
    eq149: TermId,
    c150: TermId,
    eq150: TermId,
    c151: TermId,
    shared_reason: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let two = terms.mk_int(BigInt::from(2));
    let four_y = terms.mk_mul(vec![four, y]);
    let rhs = terms.mk_add(vec![four_y, two]);
    let eq = terms.mk_eq(x, rhs);
    let c147 = terms.mk_int(BigInt::from(147));
    let c152 = terms.mk_int(BigInt::from(152));
    let c149 = terms.mk_int(BigInt::from(149));
    let c150 = terms.mk_int(BigInt::from(150));
    let c151 = terms.mk_int(BigInt::from(151));
    let le147 = terms.mk_le(x, c147);
    let ge152 = terms.mk_ge(x, c152);
    let eq149 = terms.mk_eq(x, c149);
    let eq150 = terms.mk_eq(x, c150);
    let shared_reason = terms.mk_var("shared_reason", Sort::Bool);
    Fixture {
        terms,
        x,
        y,
        eq,
        le147,
        ge152,
        eq149,
        c150,
        eq150,
        c151,
        shared_reason,
    }
}

fn assert_window(solver: &mut LiaSolver<'_>, f: &Fixture) {
    solver.assert_literal(f.eq, true);
    solver.assert_literal(f.le147, false);
    solver.assert_literal(f.ge152, false);
    solver.assert_literal(f.eq150, false);
}

fn assert_window_without_disequality(solver: &mut LiaSolver<'_>, f: &Fixture) {
    solver.assert_literal(f.eq, true);
    solver.assert_literal(f.le147, false);
    solver.assert_literal(f.ge152, false);
}

fn assert_cites_window(conflict: &[TheoryLit], f: &Fixture) {
    for (lit, what) in [(f.le147, "(not (<= x 147))"), (f.ge152, "(not (>= x 152))")] {
        assert!(
            conflict.contains(&TheoryLit::new(lit, false)),
            "the conflict must cite {what}: without it it claims x = 4y + 2 -> x = 150; got {conflict:?}"
        );
    }
}

#[test]
fn unique_value_conflict_cites_negated_window_atoms() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    assert_window(&mut solver, &f);
    // Build the Diophantine caches, then ask the modular check directly.
    let _ = solver.check();
    let _ = solver.try_diophantine_solve();
    let conflict = solver
        .check_modular_constraint_conflict()
        .expect("x ≡ 2 (mod 4) in [148, 151] leaves only 150, which is excluded");
    assert_cites_window(&conflict, &f);
}

#[test]
fn disequality_split_expanded_gcd_conflict_cites_negated_window_atoms() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    assert_window(&mut solver, &f);
    let _ = solver.check();
    // Only the expanded-GCD form of the modulus: the substitution branch of
    // `check_disequality_vs_modular` must not be the one that answers.
    solver.dioph_cached_substitutions.clear();
    solver.dioph_cached_modular_gcds = vec![(f.x, BigInt::from(4), BigInt::from(2))];
    let split = DisequalitySplitRequest {
        variable: f.x,
        excluded_value: BigRational::from(BigInt::from(150)),
        disequality_term: Some(f.eq150),
        is_distinct: false,
    };
    let conflict = solver
        .check_disequality_vs_modular(&split)
        .expect("the only residue in [148, 151] is the excluded 150");
    assert_cites_window(&conflict, &f);
    assert!(conflict.contains(&TheoryLit::new(f.eq150, false)));

    // The asserted atom itself is the premise. The split request need not
    // repeat it when LIA can independently cite that asserted disequality.
    let unnamed_split = DisequalitySplitRequest {
        variable: f.x,
        excluded_value: BigRational::from(BigInt::from(150)),
        disequality_term: None,
        is_distinct: false,
    };
    let conflict = solver
        .check_disequality_vs_modular(&unnamed_split)
        .expect("the asserted x != 150 still excludes the unique residue");
    assert!(conflict.contains(&TheoryLit::new(f.eq150, false)));
}

#[test]
fn unasserted_shared_disequality_cannot_justify_a_modular_conflict() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    assert_window_without_disequality(&mut solver, &f);
    let _ = solver.check(); // Install the asserted window in LRA's bounds.
    solver.assert_shared_disequality(f.x, f.c150, &[TheoryLit::new(f.eq150, false)]);
    assert_eq!(solver.shared_disequalities.len(), 1);
    assert!(!solver.asserted.iter().any(|&(term, _)| term == f.eq150));

    // The LRA split may name an equality found in the term store even though
    // its disequality came from Nelson-Oppen and is absent from LIA's asserted
    // trail. Both Some and None are possible split shapes. The asserted facts
    // alone have the model x=150, y=37, so none may yield a conflict.
    for disequality_term in [Some(f.eq150), None] {
        let split = DisequalitySplitRequest {
            variable: f.x,
            excluded_value: BigRational::from(BigInt::from(150)),
            disequality_term,
            is_distinct: false,
        };

        // Force each of the three unique-value paths independently. These
        // cached relations all follow from x=4y+2; only the exclusion is
        // unrepresented. Before the guard, each path returned a SAT conflict.
        solver.dioph_cached_substitutions =
            vec![(f.x, vec![(f.y, BigInt::from(4))], BigInt::from(2))];
        solver.dioph_cached_modular_gcds.clear();
        assert!(
            solver.check_disequality_vs_modular(&split).is_none(),
            "a substitution must not turn a shared-only split into a conflict"
        );

        solver.dioph_cached_substitutions.clear();
        solver.dioph_cached_modular_gcds = vec![(f.x, BigInt::from(4), BigInt::from(2))];
        assert!(
            solver.check_disequality_vs_modular(&split).is_none(),
            "an expanded GCD must not turn a shared-only split into a conflict"
        );

        solver.dioph_cached_modular_gcds.clear();
        assert!(
            solver.check_disequality_vs_modular(&split).is_none(),
            "the single-equality path must not turn a shared-only split into a conflict"
        );
    }
}

#[test]
fn unrelated_asserted_disequality_does_not_justify_the_split_value() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    assert_window_without_disequality(&mut solver, &f);
    solver.assert_literal(f.eq149, false);
    let _ = solver.check();
    solver.dioph_cached_substitutions.clear();
    solver.dioph_cached_modular_gcds.clear();

    let split = DisequalitySplitRequest {
        variable: f.x,
        excluded_value: BigRational::from(BigInt::from(150)),
        disequality_term: Some(f.eq150),
        is_distinct: false,
    };
    assert!(
        solver.check_disequality_vs_modular(&split).is_none(),
        "x != 149 does not exclude the sole residue x=150 (y=37)"
    );
}

/// Install one of the two exact cached forms of x = 4y + 2. The shared-bound
/// tests inject these *after* the ordinary check, so a different early LRA or
/// Dioph conflict cannot accidentally stand in for the modular path tested.
fn install_cached_modulus(solver: &mut LiaSolver<'_>, f: &Fixture, expanded_gcd: bool) {
    solver.dioph_cached_substitutions.clear();
    solver.dioph_cached_modular_gcds.clear();
    solver.dioph_cached_reasons = vec![(f.eq, true)];
    solver.dioph_cached_fold_reasons.clear();
    if expanded_gcd {
        solver.dioph_cached_modular_gcds = vec![(f.x, BigInt::from(4), BigInt::from(2))];
    } else {
        solver.dioph_cached_substitutions =
            vec![(f.x, vec![(f.y, BigInt::from(4))], BigInt::from(2))];
    }
}

#[test]
fn shared_equality_window_is_cited_by_no_residue_conflicts() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    solver.assert_literal(f.eq, true);
    // EUF supplied x=151 with its own reason; LIA did not assert that atom.
    // It pins x to a value impossible under x=4y+2, while x=4y+2 alone is SAT.
    solver.assert_shared_equality(f.x, f.c151, &[TheoryLit::new(f.shared_reason, true)]);
    let _ = solver.check();
    assert!(!solver
        .asserted
        .iter()
        .any(|&(term, _)| term == f.shared_reason));
    let split = DisequalitySplitRequest {
        variable: f.x,
        excluded_value: BigRational::from(BigInt::from(150)),
        disequality_term: None,
        is_distinct: false,
    };

    for expanded_gcd in [false, true] {
        install_cached_modulus(&mut solver, &f, expanded_gcd);
        let conflict = solver
            .check_modular_constraint_conflict()
            .expect("x=151 has no value congruent to 2 modulo 4");
        assert!(conflict.contains(&TheoryLit::new(f.shared_reason, true)));
        let split_conflict = solver
            .check_disequality_vs_modular(&split)
            .expect("no-residue conflict is independent of the split disequality");
        assert!(split_conflict.contains(&TheoryLit::new(f.shared_reason, true)));
    }
}

#[test]
fn shared_equality_window_is_cited_by_unique_value_conflicts() {
    let f = fixture();
    let mut solver = LiaSolver::new(&f.terms);
    solver.assert_literal(f.eq, true);
    solver.assert_literal(f.eq150, false);
    // The shared fact fixes the window at the sole permitted residue. Its
    // external Boolean reason is not in LIA's asserted trail, whose atoms
    // alone admit x=162, y=40 and x!=150.
    solver.assert_shared_equality(f.x, f.c150, &[TheoryLit::new(f.shared_reason, true)]);
    let _ = solver.check();
    assert!(!solver.asserted.contains(&(f.shared_reason, true)));
    let _ = solver.try_diophantine_solve();
    assert!(
        solver
            .dioph_cached_fold_reasons
            .contains(&TheoryLit::new(f.shared_reason, true)),
        "folding x=150 into the Dioph equation must retain its shared premise"
    );
    let split = DisequalitySplitRequest {
        variable: f.x,
        excluded_value: BigRational::from(BigInt::from(150)),
        disequality_term: Some(f.eq150),
        is_distinct: false,
    };

    for expanded_gcd in [false, true] {
        install_cached_modulus(&mut solver, &f, expanded_gcd);
        let conflict = solver
            .check_modular_constraint_conflict()
            .expect("the unique residue 150 is excluded by the asserted disequality");
        assert!(conflict.contains(&TheoryLit::new(f.shared_reason, true)));
        assert!(conflict.contains(&TheoryLit::new(f.eq150, false)));
        let split_conflict = solver
            .check_disequality_vs_modular(&split)
            .expect("the split route must cite the shared bound window too");
        assert!(split_conflict.contains(&TheoryLit::new(f.shared_reason, true)));
        assert!(split_conflict.contains(&TheoryLit::new(f.eq150, false)));
    }
}

#[test]
fn folded_shared_value_is_cited_by_cached_modular_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let two = terms.mk_int(BigInt::from(2));
    let c150 = terms.mk_int(BigInt::from(150));
    let c152 = terms.mk_int(BigInt::from(152));
    let four_y = terms.mk_mul(vec![four, y]);
    let rhs = terms.mk_add(vec![four_y, z]);
    let eq = terms.mk_eq(x, rhs);
    let lower = terms.mk_ge(x, c150);
    let upper = terms.mk_le(x, c152);
    let excluded = terms.mk_eq(x, c150);
    let shared_reason = terms.mk_var("shared_z_is_two", Sort::Bool);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(lower, true);
    solver.assert_literal(upper, true);
    solver.assert_literal(excluded, false);
    // EUF fixes z=2 under a reason LIA did not assert. The Dioph solve must
    // fold z, deriving x=4y+2 and hence x≡2 (mod 4). The interval [150,152]
    // then has one residue, 150, excluded by the asserted disequality.
    solver.assert_shared_equality(z, two, &[TheoryLit::new(shared_reason, true)]);
    assert!(!solver.asserted.contains(&(shared_reason, true)));
    // LRA installs asserted inequality bounds during its check; the direct
    // Dioph helper below only reads the current tableau/bound store. Checking
    // LRA alone avoids a full LIA pass that may already consume this conflict.
    let _ = solver.lra.check();
    let (lower_bound, upper_bound) = solver.justified_bounds(x).expect("x is registered in LRA");
    let lower_bound = lower_bound.expect("the asserted x>=150 bound was processed");
    let upper_bound = upper_bound.expect("the asserted x<=152 bound was processed");
    assert_eq!(
        LiaSolver::effective_int_lower(&lower_bound),
        BigInt::from(150)
    );
    assert_eq!(
        LiaSolver::effective_int_upper(&upper_bound),
        BigInt::from(152)
    );
    assert!(
        solver.try_diophantine_solve().is_none(),
        "the folded equation is feasible before the disequality is applied"
    );
    assert!(
        solver
            .dioph_cached_fold_reasons
            .contains(&TheoryLit::new(shared_reason, true)),
        "Dioph cache must record the premise of the folded z=2"
    );
    assert!(
        solver
            .dioph_cached_modular_gcds
            .iter()
            .any(|(term, gcd, residue)| *term == x
                && *gcd == BigInt::from(4)
                && *residue == BigInt::from(2))
            || solver
                .dioph_cached_substitutions
                .iter()
                .any(|(term, coeffs, constant)| *term == x
                    && *constant == BigInt::from(2)
                    && coeffs == &vec![(y, BigInt::from(4))]),
        "the folded system must cache x≡2 (mod 4)"
    );

    let conflict = solver
        .check_modular_constraint_conflict()
        .expect("x≡2 (mod 4) in [150,152] with x!=150 is infeasible");
    assert!(
        conflict.contains(&TheoryLit::new(shared_reason, true)),
        "without the shared z=2 premise, the asserted atoms are SAT at x=151, y=37, z=3: {conflict:?}"
    );
    assert!(conflict.contains(&TheoryLit::new(excluded, false)));
}
