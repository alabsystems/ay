// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #warm-simplex (`AY_LRA_WARM_SIMPLEX_STATE`) tests.
//!
//! The flag must be verdict-neutral: it changes WHEN the simplex pays for
//! candidate discovery (persistent heap + dirty set + last-feasible restore
//! vs per-pop rebuild + O(vars) scans), never WHAT it answers. The
//! randomized differential test drives flag-on and flag-off solvers through
//! identical bound-assert / check / push / pop sequences and requires
//! identical sat/unsat/unknown classes at every check point.

use super::*;

/// Coarse verdict class: 0 = unsat, 1 = sat-like (Sat or any split/model
/// request — "not refuted"), 2 = unknown. Split-request and model-equality
/// selections may legitimately differ between the two configurations (they
/// are model-value tie-breaks); the FEASIBILITY class may not.
fn classify(result: &TheoryResult) -> u8 {
    match result {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => 0,
        TheoryResult::Unknown => 2,
        _ => 1,
    }
}

fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

/// Build a deterministic atom pool over three Real vars: single-variable
/// bounds (both polarities give strict bounds via negation), compound rows
/// (2- and 3-var sums, weighted sums, shared slack expressions with several
/// constants), and one equality (negated assertion exercises the
/// disequality path).
fn build_atom_pool(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let consts: Vec<TermId> = [-8i64, -3, 0, 2, 5, 7, 12]
        .iter()
        .map(|&c| terms.mk_rational(BigRational::from(BigInt::from(c))))
        .collect();
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let sum_xy = terms.mk_add(vec![x, y]);
    let sum_yz = terms.mk_add(vec![y, z]);
    let sum_xyz = terms.mk_add(vec![x, y, z]);
    let two_x = terms.mk_mul(vec![two, x]);
    let three_y = terms.mk_mul(vec![three, y]);
    let weighted = terms.mk_add(vec![two_x, three_y]);

    let mut atoms = Vec::new();
    for var in [x, y, z] {
        for &c in &[consts[1], consts[2], consts[4]] {
            atoms.push(terms.mk_le(var, c));
            atoms.push(terms.mk_ge(var, c));
        }
    }
    for expr in [sum_xy, sum_yz, sum_xyz, weighted] {
        for &c in &[consts[0], consts[3], consts[5], consts[6]] {
            atoms.push(terms.mk_le(expr, c));
        }
        atoms.push(terms.mk_ge(expr, consts[2]));
    }
    atoms.push(terms.mk_eq(x, consts[3]));
    atoms.push(terms.mk_eq(sum_xy, consts[4]));
    atoms
}

/// Run one seeded random assert/check/push/pop sequence and record the
/// verdict class at every check point.
fn run_sequence(terms: &TermStore, atoms: &[TermId], seed: u64, warm: bool) -> Vec<u8> {
    let mut solver = LraSolver::new(terms);
    solver.warm.enabled = warm;
    for &atom in atoms {
        solver.register_atom(atom);
    }
    let mut rng = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    let mut depth = 0usize;
    let mut verdicts = Vec::new();
    for _ in 0..90 {
        match xorshift(&mut rng) % 10 {
            0 | 1 => {
                solver.push();
                depth += 1;
            }
            2 | 3 => {
                if depth > 0 {
                    solver.pop();
                    depth -= 1;
                    // Post-pop check: this is the path the warm state
                    // accelerates (heap repair instead of rebuild).
                    verdicts.push(classify(&solver.check()));
                } else {
                    solver.push();
                    depth += 1;
                }
            }
            4..=7 => {
                let atom = atoms[(xorshift(&mut rng) as usize) % atoms.len()];
                let value = xorshift(&mut rng).is_multiple_of(2);
                solver.assert_literal(atom, value);
            }
            _ => {
                verdicts.push(classify(&solver.check()));
            }
        }
    }
    // Unwind with a check at every level (pop-heavy tail).
    loop {
        verdicts.push(classify(&solver.check()));
        if depth == 0 {
            break;
        }
        solver.pop();
        depth -= 1;
    }
    verdicts
}

/// Randomized differential: flag-on vs flag-off must produce identical
/// verdict classes on identical random bound-assert/check/push/pop sequences.
#[test]
fn warm_simplex_state_randomized_differential() {
    let mut terms = TermStore::new();
    let atoms = build_atom_pool(&mut terms);
    for seed in 1..=48u64 {
        let cold = run_sequence(&terms, &atoms, seed, false);
        let warm = run_sequence(&terms, &atoms, seed, true);
        assert_eq!(
            cold, warm,
            "verdict divergence between AY_LRA_WARM_SIMPLEX_STATE off/on for seed {seed} \
             (0=unsat, 1=sat-like, 2=unknown)"
        );
        assert!(
            !cold.is_empty(),
            "seed {seed} produced no check points — sequence generator broken"
        );
    }
}

/// White-box: with the flag ON, pop repairs the infeasible-candidate heap
/// instead of marking it stale; with the flag OFF, pop marks it stale
/// (today's behavior).
#[test]
fn warm_pop_keeps_heap_warm_cold_pop_marks_stale() {
    for warm in [false, true] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
        let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
        let sum = terms.mk_add(vec![x, y]);
        let sum_le_10 = terms.mk_le(sum, ten);
        let x_ge_3 = terms.mk_ge(x, three);

        let mut solver = LraSolver::new(&terms);
        solver.warm.enabled = warm;
        solver.register_atom(sum_le_10);
        solver.register_atom(x_ge_3);

        solver.assert_literal(sum_le_10, true);
        let r = solver.check();
        assert!(is_sat_like(&r), "base check must be sat-like");
        assert!(
            !solver.heap_stale,
            "after a full check the heap must be freshly built (warm={warm})"
        );

        solver.push();
        solver.assert_literal(x_ge_3, true);
        let r = solver.check();
        assert!(is_sat_like(&r), "pushed check must be sat-like");
        assert!(!solver.heap_stale, "heap current before pop (warm={warm})");
        solver.pop();

        if warm {
            assert!(
                !solver.heap_stale,
                "#warm-simplex: pop must REPAIR the candidate heap, not mark it stale"
            );
        } else {
            assert!(
                solver.heap_stale,
                "flag OFF: pop must mark the heap stale (unchanged behavior)"
            );
        }

        let r = solver.check();
        assert!(
            is_sat_like(&r),
            "post-pop check must be sat-like (warm={warm})"
        );
    }
}

/// End-to-end warm run of the nested UNSAT/SAT push/pop scenario (mirrors
/// `test_nested_push_pop_compound_slack_7772` with the flag ON): the
/// conflict → restore-last-feasible → pop → repair cycle must preserve
/// verdicts.
#[test]
fn warm_nested_push_pop_unsat_then_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let fifteen = terms.mk_rational(BigRational::from(BigInt::from(15)));
    let eight = terms.mk_rational(BigRational::from(BigInt::from(8)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_15 = terms.mk_le(sum, fifteen);
    let sum_le_5 = terms.mk_le(sum, five);
    let x_ge_8 = terms.mk_ge(x, eight);
    let y_ge_3 = terms.mk_ge(y, three);

    let mut solver = LraSolver::new(&terms);
    solver.warm.enabled = true;
    for atom in [sum_le_15, sum_le_5, x_ge_8, y_ge_3] {
        solver.register_atom(atom);
    }

    solver.push();
    solver.assert_literal(sum_le_15, true);
    solver.assert_literal(x_ge_8, true);
    solver.assert_literal(y_ge_3, true);
    let result = solver.check();
    assert!(
        is_sat_like(&result),
        "outer scope should be sat-like, got {result:?}"
    );

    solver.push();
    solver.assert_literal(sum_le_5, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "inner scope should be UNSAT under the warm flag, got {result:?}"
    );

    solver.pop();
    let result = solver.check();
    assert!(
        is_sat_like(&result),
        "after inner pop should be sat-like again, got {result:?}"
    );
    solver.pop();
}

/// The non-basic candidate set must catch a bound activation that pushes a
/// NON-basic var out of bounds after a pop (the case the O(vars) SAT-exit
/// scan used to cover): warm verdicts must match cold verdicts including the
/// strict/negated-bound variants.
#[test]
fn warm_nonbasic_violation_after_pop_strict_bounds() {
    for warm in [false, true] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(BigRational::zero());
        let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
        let x_le_0 = terms.mk_le(x, zero);
        let x_ge_5 = terms.mk_ge(x, five);
        let x_le_5 = terms.mk_le(x, five);

        let mut solver = LraSolver::new(&terms);
        solver.warm.enabled = warm;
        for atom in [x_le_0, x_ge_5, x_le_5] {
            solver.register_atom(atom);
        }

        // Scope 1: x >= 5 (x snaps to 5).
        solver.push();
        solver.assert_literal(x_ge_5, true);
        let r = solver.check();
        assert!(is_sat_like(&r), "x>=5 sat-like (warm={warm})");
        solver.pop();

        // Scope 2 after pop: x <= 0 while x's VALUE is still 5 (values are
        // not rolled back by pop) — the violation must be discovered.
        solver.push();
        solver.assert_literal(x_le_0, true);
        let r = solver.check();
        assert!(
            is_sat_like(&r),
            "x<=0 alone must be sat-like even with stale value 5 (warm={warm}), got {r:?}"
        );

        // Now make it genuinely unsat with a strict negation: NOT(x <= 5)
        // means x > 5, contradicting x <= 0.
        solver.assert_literal(x_le_5, false);
        let r = solver.check();
        assert!(
            matches!(r, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)),
            "x<=0 AND x>5 must be UNSAT (warm={warm}), got {r:?}"
        );
        solver.pop();

        let r = solver.check();
        assert!(
            is_sat_like(&r),
            "empty scope after pop must be sat-like (warm={warm}), got {r:?}"
        );
    }
}
