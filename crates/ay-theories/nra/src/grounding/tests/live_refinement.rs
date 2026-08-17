// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct LiveRefinementFixture {
    multipliers: Vec<TermId>,
    templates: Vec<TermId>,
    atoms: Vec<TermId>,
}

fn live_refinement_fixture(terms: &mut TermStore) -> LiveRefinementFixture {
    let multipliers: Vec<TermId> = (0..7)
        .map(|index| terms.mk_var(format!("m{index}"), Sort::Real))
        .collect();
    let templates: Vec<TermId> = (0..7)
        .map(|index| terms.mk_var(format!("t{index}"), Sort::Real))
        .collect();
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::one());
    let two = terms.mk_rational(BigRational::from_integer(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from_integer(BigInt::from(3)));
    let mut atoms = vec![
        terms.mk_ge(multipliers[0], one),
        terms.mk_ge(multipliers[1], one),
        terms.mk_le(multipliers[0], three),
        terms.mk_le(multipliers[1], three),
        terms.mk_ge(templates[0], zero),
        terms.mk_ge(templates[1], zero),
        terms.mk_le(templates[0], three),
        terms.mk_le(templates[1], three),
    ];
    let p00 = terms.mk_mul(vec![multipliers[0], templates[0]]);
    let p11 = terms.mk_mul(vec![multipliers[1], templates[1]]);
    let straight = terms.mk_add(vec![p00, p11]);
    atoms.push(terms.mk_eq(straight, one));
    let p10 = terms.mk_mul(vec![multipliers[1], templates[0]]);
    let p01 = terms.mk_mul(vec![multipliers[0], templates[1]]);
    let swapped = terms.mk_add(vec![p10, p01]);
    atoms.push(terms.mk_eq(swapped, two));
    // Widen the support past `icp::MAX_ICP_VARS` so no earlier exact phase
    // takes the instance and the verdict really is the refinement loop's.
    for index in 2..7 {
        let padding = terms.mk_mul(vec![multipliers[index], templates[index]]);
        atoms.push(terms.mk_eq(padding, zero));
    }
    LiveRefinementFixture {
        multipliers,
        templates,
        atoms,
    }
}

fn assert_earlier_exact_phases_decline(solver: &mut NraSolver<'_>) {
    assert!(matches!(
        solver.try_linear_substitution_decide(),
        crate::univariate::UniResult::Unknown
    ));
    assert!(matches!(
        solver.try_univariate_decide(),
        crate::univariate::UniResult::Unknown
    ));
    assert!(matches!(
        solver.try_multivariate_witness_search(),
        crate::univariate::UniResult::Unknown
    ));
    assert!(matches!(
        solver.try_icp_branch_and_prune(),
        crate::univariate::UniResult::Unknown
    ));
}

fn assert_live_refinement_probe(probe: GroundingProbe) {
    assert_eq!(probe.successes, 1, "grounding must be what decided this");
    assert!(
        probe.tangent_lemmas > 0,
        "refinement must already have run when grounding succeeded"
    );
    assert!(
        probe.tentative_scopes > 0,
        "the injection must happen with a tentative scope still open"
    );
    // The load-bearing one.  A monotone lemma counter cannot tell "lemmas are
    // live" from "lemmas were added and then discarded"; a pop is exactly what
    // retires these bounds, so a nonzero count proves the scope the install
    // pops was carrying real state.
    assert!(
        probe.scoped_bounds > 0,
        "the popped scope must carry live LRA bounds, not just a scope marker"
    );
}

fn assert_verified_live_refinement_model(
    solver: &NraSolver<'_>,
    multipliers: &[TermId],
    templates: &[TermId],
) {
    // And the reported model must be the VERIFIED point — the value grounding
    // proved, not whatever the relaxation happened to hold.  (This does NOT
    // discriminate on the pop: deleting `undo_tentative_patch` was measured to
    // change no test outcome.  Claiming otherwise is the failure mode this
    // test was written to end.)
    let value = |term: TermId| solver.var_value(term).expect("model value");
    let m0 = value(multipliers[0]);
    let m1 = value(multipliers[1]);
    let t0 = value(templates[0]);
    let t1 = value(templates[1]);
    assert_eq!(&m0 * &t0 + &m1 * &t1, BigRational::one(), "straight row");
    assert_eq!(
        &m1 * &t0 + &m0 * &t1,
        BigRational::from_integer(BigInt::from(2)),
        "swapped row"
    );
    for bounded in [&m0, &m1] {
        assert!(*bounded >= BigRational::one());
        assert!(*bounded <= BigRational::from_integer(BigInt::from(3)));
    }
    for bounded in [&t0, &t1] {
        assert!(*bounded >= BigRational::zero());
        assert!(*bounded <= BigRational::from_integer(BigInt::from(3)));
    }
    for index in 2..7 {
        assert!(
            (value(multipliers[index]) * value(templates[index])).is_zero(),
            "padding row {index}"
        );
    }
}

/// THE STRUCTURAL RISK, inside ONE `check()`: this phase is the only exact
/// lane that can inject a model MID refinement.  Every other one runs before
/// the loop, into a pristine relaxation; this one can fire on iteration `k`
/// on top of the tangent lemmas, tentative sign cuts and patch bounds that
/// iterations `0..k` pushed into the still-open tentative scope.
/// [`NraSolver::install_grounded_model`] pops the scope before injecting.
/// That pop is HYGIENE, not a load-bearing guard: deleting it changes no test
/// outcome (measured — LRA bounds only ever tighten, and the next
/// `assert_literal` pops the scope anyway).  What this test does verify is the
/// entry itself: grounding firing at iteration `k > 0` with live refinement
/// bounds in an open tentative scope, and the reported model BEING the
/// verified point.
///
/// The instance forces `k > 0` structurally rather than incidentally.  Rows
/// `straight` and `swapped` are the same polynomial with different constants
/// whenever `m0 == m1`, and `m0`/`m1` share a lower bound, so the relaxation's
/// FIRST point (both multipliers at 1, both templates at 0) makes every
/// pinning singular and inconsistent — both bipartite covers and the zero
/// snap decline there.  The boxes on the four live variables are what make
/// the loop move at all: with unbounded factors the tangent relaxation never
/// cuts the point off, the pin vector repeats, and the phase's own stall
/// detector suppresses every later attempt (measured: the same system without
/// the upper bounds sits on its first point for all 15 debug iterations and
/// the phase is offered exactly two distinct pin vectors in the whole check).
#[test]
fn grounding_installs_its_verified_point_over_live_refinement_bounds() {
    let mut terms = TermStore::new();
    let fixture = live_refinement_fixture(&mut terms);
    let mut solver = NraSolver::new(&terms);
    for atom in fixture.atoms {
        solver.assert_literal(atom, true);
    }
    assert_earlier_exact_phases_decline(&mut solver);

    reset_test_successes();
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat), "got {result:?}");
    assert_live_refinement_probe(test_probe());
    assert_verified_live_refinement_model(&solver, &fixture.multipliers, &fixture.templates);
}
