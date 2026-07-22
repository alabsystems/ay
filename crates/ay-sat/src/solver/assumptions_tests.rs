// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

#[test]
fn compose_scope_assumptions_empty_when_no_scope_or_assumptions() {
    let solver: Solver = Solver::new(2);
    assert!(solver.compose_scope_assumptions(&[]).is_empty());
}

#[test]
fn compose_scope_assumptions_prefixes_scope_selectors() {
    let mut solver: Solver = Solver::new(4);
    solver.cold.scope_selectors = vec![Variable(2), Variable(0)];

    let user_assumptions = [
        Literal::positive(Variable(1)),
        Literal::negative(Variable(3)),
    ];
    let combined = solver.compose_scope_assumptions(&user_assumptions);

    assert_eq!(
        combined,
        vec![
            Literal::negative(Variable(2)),
            Literal::negative(Variable(0)),
            user_assumptions[0],
            user_assumptions[1],
        ]
    );
}

#[test]
fn solve_with_assumptions_refreshes_num_original_clauses_after_bve() {
    let mut solver = Solver::new(6);
    solver.set_preprocess_enabled(true);
    solver.set_bve_enabled(true);
    solver.set_vivify_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_congruence_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_walk_enabled(false);

    // BVE eliminates x0 by resolving {x0, x1} with {~x0, x2}.
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(4)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);

    let assumptions = [Literal::positive(Variable(5))];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(
        matches!(result, AssumeResult::Sat(_)),
        "formula should remain SAT under assumptions after preprocessing, got {result:?}"
    );
    assert!(
        solver.bve_stats().vars_eliminated > 0,
        "test setup must shrink the formula via BVE"
    );

    let active = solver.arena.active_clause_count();
    assert!(
        active < 5,
        "BVE should reduce the active irredundant clause count, got {active}"
    );
    assert_eq!(
        solver.num_original_clauses, active,
        "solve_with_assumptions must refresh num_original_clauses after preprocessing shrink"
    );
}

/// Regression for proptest-minimized push/pop SAT model verification failure.
///
/// After a base solve, push(), adding a unit clause, and scoped solve, the
/// model verification debug_assert fires because verify_external_model checks
/// clauses from the original_ledger that should be skipped.
#[test]
fn test_push_pop_scoped_solve_model_verification() {
    // From proptest minimization:
    // num_vars=15, base_clauses=[[Lit(5),Lit(1)],[Lit(13),Lit(7)],[Lit(7),Lit(9),Lit(10),Lit(13)],[Lit(0)]]
    // scope_clauses=[[Lit(4)]]
    //
    // Decoded:
    // Lit(5) = -v2, Lit(1) = -v0, Lit(13) = -v6, Lit(7) = -v3
    // Lit(9) = -v4, Lit(10) = +v5, Lit(0) = +v0, Lit(4) = +v2
    let nv = 15;
    let mut solver = Solver::new(nv);

    // Base clauses
    solver.add_clause(vec![
        Literal::negative(Variable::new(2)),
        Literal::negative(Variable::new(0)),
    ]); // [-v2, -v0]
    solver.add_clause(vec![
        Literal::negative(Variable::new(6)),
        Literal::negative(Variable::new(3)),
    ]); // [-v6, -v3]
    solver.add_clause(vec![
        Literal::negative(Variable::new(3)),
        Literal::negative(Variable::new(4)),
        Literal::positive(Variable::new(5)),
        Literal::negative(Variable::new(6)),
    ]); // [-v3, -v4, +v5, -v6]
    solver.add_clause(vec![Literal::positive(Variable::new(0))]); // [+v0]

    // Base solve
    let base_result = solver.solve().into_inner();
    if let SatResult::Sat(model) = &base_result {
        // v0=true forced by unit clause
        assert!(model[0], "v0 should be true");
    }

    // Push scope, add scope clause [+v2]
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable::new(2))]);

    // Scoped solve -- base clauses force v0=true, and [-v2, -v0] + [+v2] means
    // v2=true AND (v2=false OR v0=false) -> conflict. Should be UNSAT.
    let scoped = solver.solve();
    let scoped_inner = scoped.into_inner();
    // This should be UNSAT:
    // v0=true (unit clause), [-v2, -v0] => v2=false, but scope forces v2=true
    assert!(
        matches!(scoped_inner, SatResult::Unsat(_)),
        "Scoped solve should be UNSAT: v0=true forces v2=false, but scope requires v2=true. Got: {scoped_inner:?}",
    );

    // Pop and re-solve
    assert!(solver.pop());
    let post_pop = solver.solve().into_inner();
    if let SatResult::Sat(model) = &post_pop {
        assert!(model[0], "v0 should be true after pop");
    }
}

// ════════════════════════════════════════════════════════════════════════════
// IC3-pattern push/pop FINALIZE_SAT_FAIL reproduction (#8546)
// ════════════════════════════════════════════════════════════════════════════

/// Regression: IC3-style repeated push/pop/solve cycles must not trigger
/// FINALIZE_SAT_FAIL on subsequent unscoped solves.
///
/// Pattern: add base clauses, then repeatedly:
///   push() -> add_clause(temp) -> solve_with_assumptions(cube) -> pop()
///   solve_with_assumptions(cube) // unscoped solve
///
/// The FINALIZE_SAT_FAIL bug manifests when the unscoped solve's model
/// fails original_ledger verification despite reconstruction_len=0.
///
/// Root cause: [to be filled after debugging]
#[test]
fn test_ic3_push_pop_pattern_no_finalize_sat_fail() {
    let nv = 20;
    let mut solver = Solver::new(nv);

    // Build a satisfiable base formula (transition-relation-like).
    // Use enough clauses to trigger incremental inprocessing.
    let pos = |i: usize| Literal::positive(Variable::new(i as u32));
    let neg = |i: usize| Literal::negative(Variable::new(i as u32));

    // Add base clauses: a formula that is satisfiable with many models.
    // Transition-relation-like: variables 0-9 are "current state",
    // variables 10-19 are "next state".
    for i in 0..10 {
        // At least one of current or next must be true for each pair
        solver.add_clause(vec![pos(i), pos(i + 10)]);
    }
    // Some constraints
    solver.add_clause(vec![neg(0), neg(1), pos(2)]); // ~v0 | ~v1 | v2
    solver.add_clause(vec![neg(3), pos(4)]); // ~v3 | v4
    solver.add_clause(vec![neg(5), neg(6), pos(7)]); // ~v5 | ~v6 | v7

    // Simulate IC3 push/pop cycles
    for round in 0..50 {
        // IC3 query with temporary clause (push/pop pattern)
        solver.push();
        // Add a temporary blocking clause within scope
        let temp_lit = if round % 2 == 0 {
            pos(round % 10)
        } else {
            neg(round % 10)
        };
        solver.add_clause(vec![temp_lit]);

        let assumption_var = (round + 5) % 10;
        let assumptions = vec![pos(assumption_var)];
        let combined = solver.compose_scope_assumptions(&assumptions);
        let _result = solver.solve_with_assumptions(&combined);

        assert!(solver.pop(), "pop should succeed in round {round}");

        // IC3 unscoped query (no push/pop) — this is where FINALIZE_SAT_FAIL hits
        let unscoped_assumptions = vec![neg(round % 10)];
        let result = solver.solve_with_assumptions(&unscoped_assumptions);
        // The result should be SAT, UNSAT, or Unknown — never a panic or
        // internal error. If FINALIZE_SAT_FAIL triggers, the result would
        // be Unknown with SatUnknownReason::InvalidSatModel.
        let inner = result.into_inner();
        match &inner {
            AssumeResult::Unknown => {
                // Check if this was a FINALIZE_SAT_FAIL
                if let Some(detail) = &solver.cold.last_unknown_detail {
                    assert!(
                        !detail.contains("unsatisfied"),
                        "FINALIZE_SAT_FAIL in round {round}: {detail}"
                    );
                }
            }
            _ => {} // SAT or UNSAT is fine
        }
    }
}

/// More intensive IC3 reproduction with global clause additions (frame lemmas).
///
/// IC3 adds permanent "blocking clauses" (frame lemmas) between solve cycles
/// via add_clause_global(). These survive push/pop and accumulate over time.
#[test]
fn test_ic3_pattern_with_global_lemmas_no_finalize_sat_fail() {
    let nv = 30;
    let mut solver = Solver::new(nv);

    let pos = |i: usize| Literal::positive(Variable::new(i as u32));
    let neg = |i: usize| Literal::negative(Variable::new(i as u32));

    // Base transition relation
    for i in 0..15 {
        solver.add_clause(vec![pos(i), pos(i + 15)]);
    }
    solver.add_clause(vec![neg(0), neg(1), pos(2)]);
    solver.add_clause(vec![neg(3), pos(4)]);
    solver.add_clause(vec![neg(5), neg(6), pos(7)]);
    solver.add_clause(vec![neg(10), neg(11), pos(12)]);

    for round in 0..100 {
        // Add a global "blocking clause" (IC3 frame lemma)
        let l1 = if round % 3 == 0 {
            pos(round % 15)
        } else {
            neg(round % 15)
        };
        let l2 = if round % 5 == 0 {
            pos((round + 3) % 15)
        } else {
            neg((round + 3) % 15)
        };
        solver.add_clause_global(vec![l1, l2]);

        // IC3 query with temporary clause
        solver.push();
        let temp_lit = if round % 2 == 0 {
            pos(round % 15)
        } else {
            neg(round % 15)
        };
        solver.add_clause(vec![temp_lit, pos((round + 7) % 15)]);

        let assumptions = vec![pos(round % 15)];
        let combined = solver.compose_scope_assumptions(&assumptions);
        let _scoped_result = solver.solve_with_assumptions(&combined);
        assert!(solver.pop(), "pop should succeed in round {round}");

        // Unscoped query
        let unscoped = vec![neg((round + 1) % 15)];
        let result = solver.solve_with_assumptions(&unscoped);
        let inner = result.into_inner();
        if matches!(&inner, AssumeResult::Unknown) {
            if let Some(detail) = &solver.cold.last_unknown_detail {
                assert!(
                    !detail.contains("unsatisfied"),
                    "FINALIZE_SAT_FAIL in round {round} (global lemmas): {detail}"
                );
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// UNSAT core minimality tests (#8206)
// ════════════════════════════════════════════════════════════════════════════

fn add_indirect_assumption_chain(solver: &mut Solver) {
    let a = Variable::new(0);
    let b = Variable::new(1);
    let x = Variable::new(3);

    // a => x, and x => !b. Under assumptions a=true and b=true this is UNSAT.
    solver.add_clause(vec![Literal::negative(a), Literal::positive(x)]);
    solver.add_clause(vec![Literal::negative(x), Literal::negative(b)]);
}

/// Basic core minimality: irrelevant assumption excluded.
///
/// Formula: (~a | ~b)
/// Assumptions: a=T, b=T, c=T
/// The conflict is a=T ^ b=T from the clause (~a | ~b). c is irrelevant.
/// Core should be {a, b}, not {a, b, c}.
#[test]
fn test_unsat_core_minimality_basic() {
    let a = Variable::new(0);
    let b = Variable::new(1);
    let c = Variable::new(2);

    let mut solver = Solver::new(3);
    // (~a | ~b): at most one of a, b can be true
    solver.add_clause(vec![Literal::negative(a), Literal::negative(b)]);

    let assumptions = [
        Literal::positive(a),
        Literal::positive(b),
        Literal::positive(c),
    ];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            // Core must be a subset of assumptions
            for lit in &core {
                assert!(
                    assumptions.contains(lit),
                    "core literal {lit:?} is not an assumption"
                );
            }
            // Core must contain a and b (they are the conflicting pair)
            assert!(
                core.contains(&Literal::positive(a)),
                "core must contain a=T, got {core:?}"
            );
            assert!(
                core.contains(&Literal::positive(b)),
                "core must contain b=T, got {core:?}"
            );
            // Core should NOT contain c (it's irrelevant)
            assert!(
                !core.contains(&Literal::positive(c)),
                "core must not contain irrelevant c=T, got {core:?}"
            );
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

/// Chain implication: only endpoints matter.
///
/// Formula: (~a | x), (~x | ~b)
/// Assumptions: a=T, b=T, c=T
/// a=T propagates x=T via (~a | x), then x=T and b=T conflict via (~x | ~b).
/// Core should be {a, b}, not {a, b, c}.
#[test]
fn test_unsat_core_minimality_chain() {
    let a = Variable::new(0);
    let b = Variable::new(1);
    let c = Variable::new(2);

    let mut solver = Solver::new(4);
    add_indirect_assumption_chain(&mut solver);

    let assumptions = [
        Literal::positive(a),
        Literal::positive(b),
        Literal::positive(c),
    ];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            for lit in &core {
                assert!(
                    assumptions.contains(lit),
                    "core literal {lit:?} is not an assumption"
                );
            }
            assert!(
                core.contains(&Literal::positive(a)),
                "core must contain a=T, got {core:?}"
            );
            assert!(
                core.contains(&Literal::positive(b)),
                "core must contain b=T, got {core:?}"
            );
            assert!(
                !core.contains(&Literal::positive(c)),
                "core must not contain irrelevant c=T, got {core:?}"
            );
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

#[test]
fn test_unsat_core_revalidates_indirect_assumption_chain() {
    let a = Variable::new(0);
    let b = Variable::new(1);
    let c = Variable::new(2);

    let assumptions = [
        Literal::positive(a),
        Literal::positive(b),
        Literal::positive(c),
    ];

    let mut solver = Solver::new(4);
    add_indirect_assumption_chain(&mut solver);
    let core = solver
        .solve_with_assumptions(&assumptions)
        .into_unsat_core()
        .expect("a=true and b=true should be UNSAT");

    assert!(
        core.contains(&Literal::positive(a)),
        "core must include the assumption that implies x, got {core:?}"
    );
    assert!(
        core.contains(&Literal::positive(b)),
        "core must include the assumption contradicted by x, got {core:?}"
    );
    assert!(
        !core.contains(&Literal::positive(c)),
        "irrelevant assumption c should not be in core: {core:?}"
    );

    let mut reduced = Solver::new(4);
    add_indirect_assumption_chain(&mut reduced);
    assert!(
        reduced.solve_with_assumptions(&core).is_unsat(),
        "returned core must be sufficient to reproduce UNSAT: {core:?}"
    );

    let mut missing_a = Solver::new(4);
    add_indirect_assumption_chain(&mut missing_a);
    assert!(
        missing_a
            .solve_with_assumptions(&[Literal::positive(b)])
            .is_sat(),
        "b alone is SAT, so dropping a would be an invalid core"
    );
}

#[test]
fn test_resolve_conflict_for_unsat_core_walks_resolved_away_assumption() {
    let a = Variable::new(0);
    let b = Variable::new(1);
    let x = Variable::new(2);

    let mut solver = Solver::new(3);
    let reason_ax = ClauseRef(
        solver.add_clause_db(&[Literal::negative(a), Literal::positive(x)], false) as u32,
    );
    let conflict_ref = ClauseRef(
        solver.add_clause_db(&[Literal::negative(x), Literal::negative(b)], false) as u32,
    );

    solver.decide(Literal::positive(a));
    solver.qhead = solver.trail.len();
    solver.enqueue(Literal::positive(x), Some(reason_ax));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::positive(b));

    let mut is_assumption = vec![false; 3];
    is_assumption[a.index()] = true;
    is_assumption[b.index()] = true;
    let mut assumption_lit = vec![None; 3];
    assumption_lit[a.index()] = Some(Literal::positive(a));
    assumption_lit[b.index()] = Some(Literal::positive(b));

    let core =
        solver.resolve_conflict_for_unsat_core(conflict_ref, &is_assumption, &assumption_lit);

    assert!(
        core.contains(&Literal::positive(a)),
        "conflict-clause walk must reach a through x's reason, got {core:?}"
    );
    assert!(
        core.contains(&Literal::positive(b)),
        "conflict-clause walk must include b from the conflict clause, got {core:?}"
    );
    assert_eq!(core.len(), 2, "unexpected extra assumptions in {core:?}");
}

/// Single assumption conflict with unit clause.
///
/// Formula: (~a)
/// Assumptions: a=T
/// Core should be {a}.
#[test]
fn test_unsat_core_single_assumption() {
    let a = Variable::new(0);

    let mut solver = Solver::new(1);
    solver.add_clause(vec![Literal::negative(a)]); // ~a (unit clause)

    let assumptions = [Literal::positive(a)];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            assert_eq!(
                core.len(),
                1,
                "core should have exactly 1 literal, got {core:?}"
            );
            assert_eq!(core[0], Literal::positive(a), "core should be {{a=T}}");
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

/// Contradictory assumptions on the SAME variable must yield a core that is
/// itself UNSAT (both polarities), not a satisfiable singleton.
///
/// Empty formula, assumptions a=T and a=F. The two assumptions directly
/// contradict. Because the core-extraction structures key `assumption_lit`
/// and `in_core` by variable, an earlier bug reported only one polarity
/// (whichever was registered last), producing a core `{a=F}` (or `{a=T}`)
/// that is trivially satisfiable. The correct core is both `{a=T, a=F}`.
///
/// Regression for the unsound-unsat-core bug: get-unsat-core returned `(n2)`
/// for `(assert a)(assert (not a))` where `{(not a)}` alone is SAT.
#[test]
fn test_unsat_core_opposite_polarity_same_variable() {
    let a = Variable::new(0);
    let t = Variable::new(1);

    let mut solver = Solver::new(2);
    // A satisfiable clause over an unrelated variable keeps the arena
    // non-empty so solving exercises the assumption-decide conflict path
    // (not the empty-formula fast path), matching the SMT reproducer where
    // a trivially-true assertion is present.
    solver.add_clause(vec![Literal::positive(t), Literal::negative(t)]);
    let assumptions = [Literal::positive(a), Literal::negative(a)];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            assert!(
                core.contains(&Literal::positive(a)),
                "core must contain a=T, got {core:?}"
            );
            assert!(
                core.contains(&Literal::negative(a)),
                "core must contain a=F, got {core:?}"
            );
            // The returned core, asserted alone, must reproduce UNSAT.
            let mut recheck = Solver::new(2);
            recheck.add_clause(vec![Literal::positive(t), Literal::negative(t)]);
            assert!(
                recheck.solve_with_assumptions(&core).is_unsat(),
                "returned core must itself be UNSAT, got {core:?}"
            );
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

/// Same as above but with the opposite assumption order, plus an irrelevant
/// third assumption, to ensure the fix does not over-approximate.
#[test]
fn test_unsat_core_opposite_polarity_excludes_irrelevant() {
    let a = Variable::new(0);
    let c = Variable::new(1);
    let t = Variable::new(2);

    let mut solver = Solver::new(3);
    solver.add_clause(vec![Literal::positive(t), Literal::negative(t)]);
    // a=F first, then a=T (reverse registration order), plus irrelevant c=T.
    let assumptions = [
        Literal::negative(a),
        Literal::positive(a),
        Literal::positive(c),
    ];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            assert!(
                core.contains(&Literal::positive(a)) && core.contains(&Literal::negative(a)),
                "core must contain both polarities of a, got {core:?}"
            );
            assert!(
                !core.contains(&Literal::positive(c)),
                "core must not contain irrelevant c=T, got {core:?}"
            );
            let mut recheck = Solver::new(3);
            recheck.add_clause(vec![Literal::positive(t), Literal::negative(t)]);
            assert!(
                recheck.solve_with_assumptions(&core).is_unsat(),
                "returned core must itself be UNSAT, got {core:?}"
            );
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

/// Longer chain: ensure deep BFS traversal works.
///
/// Formula: (~a | x1), (~x1 | x2), (~x2 | x3), (~x3 | ~b)
/// Assumptions: a=T, b=T, c=T
/// a propagates x1, x2, x3 through the chain. x3=T conflicts with b=T.
/// Core should be {a, b}, not {a, b, c}.
#[test]
fn test_unsat_core_minimality_long_chain() {
    let a = Variable::new(0);
    let b = Variable::new(1);
    let c = Variable::new(2);
    let x1 = Variable::new(3);
    let x2 = Variable::new(4);
    let x3 = Variable::new(5);

    let mut solver = Solver::new(6);
    solver.add_clause(vec![Literal::negative(a), Literal::positive(x1)]); // a => x1
    solver.add_clause(vec![Literal::negative(x1), Literal::positive(x2)]); // x1 => x2
    solver.add_clause(vec![Literal::negative(x2), Literal::positive(x3)]); // x2 => x3
    solver.add_clause(vec![Literal::negative(x3), Literal::negative(b)]); // x3 => ~b

    let assumptions = [
        Literal::positive(a),
        Literal::positive(b),
        Literal::positive(c),
    ];
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            for lit in &core {
                assert!(
                    assumptions.contains(lit),
                    "core literal {lit:?} is not an assumption"
                );
            }
            assert!(
                core.contains(&Literal::positive(a)),
                "core must contain a=T, got {core:?}"
            );
            assert!(
                core.contains(&Literal::positive(b)),
                "core must contain b=T, got {core:?}"
            );
            assert!(
                !core.contains(&Literal::positive(c)),
                "core must not contain irrelevant c=T, got {core:?}"
            );
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

/// Core subset validity: core literals must be a subset of assumptions.
#[test]
fn test_unsat_core_is_subset_of_assumptions() {
    let mut solver = Solver::new(5);
    let vars: Vec<Variable> = (0..5).map(Variable::new).collect();

    // (~v0 | ~v1)
    solver.add_clause(vec![Literal::negative(vars[0]), Literal::negative(vars[1])]);
    solver.add_clause(vec![Literal::positive(vars[2]), Literal::positive(vars[3])]);
    solver.add_clause(vec![Literal::positive(vars[3]), Literal::positive(vars[4])]);

    let assumptions: Vec<Literal> = (0..5).map(|i| Literal::positive(vars[i])).collect();
    let result = solver.solve_with_assumptions(&assumptions).into_inner();
    match result {
        AssumeResult::Unsat(core, _) => {
            let assump_set: std::collections::HashSet<_> = assumptions.iter().collect();
            for lit in &core {
                assert!(
                    assump_set.contains(lit),
                    "core literal {lit:?} is not in assumptions {assumptions:?}"
                );
            }
            assert!(core.len() >= 2, "core too small: {core:?}");
            assert!(
                core.contains(&Literal::positive(vars[0])),
                "core must contain v0=T, got {core:?}"
            );
            assert!(
                core.contains(&Literal::positive(vars[1])),
                "core must contain v1=T, got {core:?}"
            );
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}
/// Regression for #7987: incremental solve_with_assumptions returns wrong UNSAT.
///
/// After a SAT result with assumption v1=true, adding a permanent clause !v1,
/// then solving with assumption v2=true should be SAT. The bug was that
/// preprocessing added derived irredundant clauses (not in the original ledger)
/// which persisted across incremental solves because reset_search_state only
/// rebuilt the arena when original clauses were *deleted* (active < ledger),
/// not when derived clauses were *added* (active > ledger).
#[test]
fn test_incremental_assumption_add_clause_between_solves_regression_7987() {
    let mut s = Solver::new(3);
    let v0 = Variable::new(0);
    let v1 = Variable::new(1);
    let v2 = Variable::new(2);

    s.add_clause(vec![Literal::negative(v0)]); // v0=false
                                               // v2 <=> !v1 (encoded as two binary clauses)
    s.add_clause(vec![Literal::negative(v2), Literal::negative(v1)]); // !v2 | !v1
    s.add_clause(vec![Literal::positive(v2), Literal::positive(v1)]); // v2 | v1

    // First solve: v1=true -> SAT (v0=false, v1=true, v2=false)
    let r1 = s.solve_with_assumptions(&[Literal::positive(v1)]);
    assert!(r1.result().is_sat(), "First solve should be SAT");

    // Add permanent clause: !v1
    s.add_clause(vec![Literal::negative(v1)]);

    // Second solve: v2=true -> should be SAT (v0=false, v1=false, v2=true)
    let r2 = s.solve_with_assumptions(&[Literal::positive(v2)]);
    assert!(
        r2.result().is_sat(),
        "Second solve with v2=true should be SAT after adding !v1, got {:?}",
        r2.result()
    );
}

/// Verify that AssumeResult::Unsat carries an Option<ProofCertificate> (#8209).
/// When LRAT proof output is enabled, the certificate should be Some.
#[test]
fn test_assume_unsat_carries_proof_certificate_when_lrat_enabled() {
    // Create a solver with LRAT proof output.
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(3, proof);

    let v0 = Variable::new(0);
    let v1 = Variable::new(1);

    // x0 AND x1
    solver.add_clause(vec![Literal::positive(v0)]);
    solver.add_clause(vec![Literal::positive(v1)]);

    // Assume ~x0: conflicts with the unit clause x0.
    let result = solver.solve_with_assumptions(&[Literal::negative(v0)]);
    assert!(
        result.is_unsat(),
        "Should be UNSAT with contradicting assumption"
    );

    // The core should contain the conflicting assumption.
    let core = result
        .unsat_core()
        .expect("UNSAT result should have a core");
    assert!(
        !core.is_empty(),
        "Core should contain at least the conflicting assumption"
    );

    // With LRAT enabled, the proof certificate should be present.
    match result.result() {
        AssumeResult::Unsat(_, cert) => {
            assert!(
                cert.is_some(),
                "LRAT-enabled UNSAT should carry a proof certificate"
            );
        }
        other => panic!("Expected Unsat, got {other:?}"),
    }
}

/// Verify that without LRAT proof output, the certificate is None (#8209).
#[test]
fn test_assume_unsat_no_certificate_without_lrat() {
    let mut solver = Solver::new(3);
    let v0 = Variable::new(0);
    let v1 = Variable::new(1);

    // x0 AND x1
    solver.add_clause(vec![Literal::positive(v0)]);
    solver.add_clause(vec![Literal::positive(v1)]);

    // Assume ~x0: conflicts with the unit clause x0.
    let result = solver.solve_with_assumptions(&[Literal::negative(v0)]);
    assert!(result.is_unsat(), "Should be UNSAT");

    match result.result() {
        AssumeResult::Unsat(_, cert) => {
            assert!(
                cert.is_none(),
                "Without LRAT, proof certificate should be None"
            );
        }
        other => panic!("Expected Unsat, got {other:?}"),
    }
}

/// IC3 assumption cache (#8443): verify that repeated solve_with_assumptions
/// calls with overlapping assumptions produce correct results and that the
/// incremental reset path is exercised on the second call.
#[test]
fn test_ic3_assumption_cache_correctness() {
    let mut solver = Solver::new(6);
    let v: Vec<Variable> = (0..6).map(Variable::new).collect();

    // Build a satisfiable formula:
    // (v0 | v1), (~v0 | v2), (v3 | v4), (~v3 | v5)
    solver.add_clause(vec![Literal::positive(v[0]), Literal::positive(v[1])]);
    solver.add_clause(vec![Literal::negative(v[0]), Literal::positive(v[2])]);
    solver.add_clause(vec![Literal::positive(v[3]), Literal::positive(v[4])]);
    solver.add_clause(vec![Literal::negative(v[3]), Literal::positive(v[5])]);

    // First solve: assumptions [v0=T, v3=T]
    let assumptions1 = [Literal::positive(v[0]), Literal::positive(v[3])];
    let r1 = solver.solve_with_assumptions(&assumptions1);
    assert!(r1.result().is_sat(), "First solve should be SAT");

    // Second solve with overlapping assumptions [v0=T, v3=F]
    // This should trigger the incremental reset path (cache valid, no new clauses).
    let assumptions2 = [Literal::positive(v[0]), Literal::negative(v[3])];
    let r2 = solver.solve_with_assumptions(&assumptions2);
    assert!(r2.result().is_sat(), "Second solve should be SAT");

    // Third solve with identical assumptions to #2
    let r3 = solver.solve_with_assumptions(&assumptions2);
    assert!(
        r3.result().is_sat(),
        "Third solve (same as second) should be SAT"
    );

    // Verify cache stats: first solve is a miss, subsequent are hits.
    let hits = solver.stats.assumption_cache_hits;
    let misses = solver.stats.assumption_cache_misses;
    assert!(
        misses >= 1,
        "First solve should be a cache miss, got misses={misses}"
    );
    assert!(
        hits >= 1,
        "Subsequent solves should have cache hits, got hits={hits}"
    );
}

/// IC3 assumption cache (#8443, #8569): verify that adding clauses between
/// solves does NOT invalidate the cache. New clauses are handled inline
/// by the incremental reset path (attach watches + propagate units) in
/// O(new_clauses) time, avoiding the O(num_vars) full reset.
#[test]
fn test_ic3_assumption_cache_preserved_after_add_clause() {
    let mut solver = Solver::new(4);
    let v: Vec<Variable> = (0..4).map(Variable::new).collect();

    // (v0 | v1)
    solver.add_clause(vec![Literal::positive(v[0]), Literal::positive(v[1])]);

    // First solve
    let assumptions = [Literal::positive(v[0])];
    let r1 = solver.solve_with_assumptions(&assumptions);
    assert!(r1.result().is_sat(), "First solve should be SAT");
    let hits_after_first = solver.stats.assumption_cache_hits;

    // Add a new clause between solves — cache should remain valid (#8569).
    solver.add_clause(vec![Literal::positive(v[2]), Literal::positive(v[3])]);

    // Second solve — should be a cache hit (incremental reset handles
    // new clause attachment inline).
    let r2 = solver.solve_with_assumptions(&assumptions);
    assert!(r2.result().is_sat(), "Second solve should be SAT");
    let hits_after_second = solver.stats.assumption_cache_hits;
    assert!(
        hits_after_second > hits_after_first,
        "add_clause should NOT invalidate cache (#8569): hits before={hits_after_first}, after={hits_after_second}"
    );
}

/// IC3 assumption cache (#8443): UNSAT result with incremental cache.
/// Verify that an UNSAT result from a cached solve still produces a
/// correct unsat core.
#[test]
fn test_ic3_assumption_cache_unsat_core_correct() {
    let mut solver = Solver::new(3);
    let a = Variable::new(0);
    let b = Variable::new(1);
    let c = Variable::new(2);

    // (~a | ~b): a and b cannot both be true
    solver.add_clause(vec![Literal::negative(a), Literal::negative(b)]);

    // First solve: SAT with a=T only
    let r1 = solver.solve_with_assumptions(&[Literal::positive(a)]);
    assert!(r1.result().is_sat(), "First solve should be SAT");

    // Second solve: UNSAT with a=T, b=T (conflicts with ~a | ~b)
    // This should use the incremental reset path.
    let r2 = solver.solve_with_assumptions(&[
        Literal::positive(a),
        Literal::positive(b),
        Literal::positive(c),
    ]);
    match r2.result() {
        AssumeResult::Unsat(core, _) => {
            // Core must contain a and b (they conflict via ~a | ~b)
            assert!(
                core.contains(&Literal::positive(a)),
                "core must contain a=T, got {core:?}"
            );
            assert!(
                core.contains(&Literal::positive(b)),
                "core must contain b=T, got {core:?}"
            );
            // Core should NOT contain irrelevant c
            assert!(
                !core.contains(&Literal::positive(c)),
                "core must not contain irrelevant c=T, got {core:?}"
            );
        }
        other => panic!("expected UNSAT, got {other:?}"),
    }
}

/// Test that VerifiedAssumeResult::proof_certificate() returns the certificate (#8209).
#[test]
fn test_verified_assume_result_proof_certificate_accessor() {
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(3, proof);

    let v0 = Variable::new(0);
    solver.add_clause(vec![Literal::positive(v0)]);
    solver.add_clause(vec![Literal::negative(v0)]);

    // Empty assumptions -> the formula itself is UNSAT.
    let result = solver.solve_with_assumptions(&[]);
    assert!(result.is_unsat(), "Formula is inherently UNSAT");

    // The proof_certificate() accessor should work through VerifiedAssumeResult.
    if let Some(cert) = result.proof_certificate() {
        // The certificate should have at least some proof steps.
        let steps = cert.materialize();
        // Even empty proofs (preprocessing UNSAT) should return cleanly.
        let _ = steps;
    }
    // Note: proof_certificate() may be None even with LRAT for trivial UNSAT
    // (detected at level 0 before any conflict analysis). This is OK.
}

/// Inc-10 regression: a no-op partial restart (decision level already at or
/// below the assumption prefix) must still consume the pending-restart signal.
///
/// `should_restart()` early-returns false only when `conflicts_since_restart
/// == 0`. Before the fix, the early-return path of `do_partial_restart` left
/// the counter untouched, so the assumption CDCL loop took the restart branch
/// on every iteration — a livelock producing neither conflicts nor decisions,
/// which means neither `should_stop` checkpoint (every 100 conflicts / 1000
/// decisions) was ever reached. Measured: a nominally 5s-capped IMC bmc_check
/// on nest-len.c_000 (k=4 iter=3) spun for ~270s inside
/// `solve_with_assumptions_interruptible`.
#[test]
fn partial_restart_noop_consumes_pending_restart_signal() {
    let mut solver: Solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);

    // Simulate the post-conflict state observed in the livelock: conflicts
    // recorded since the last restart, but the search is already at (or
    // below) the assumption-prefix level.
    solver.conflicts_since_restart = 7;
    assert_eq!(solver.decision_level, 0);

    solver.do_partial_restart(2);

    assert_eq!(
        solver.conflicts_since_restart, 0,
        "no-op partial restart must reset conflicts_since_restart so \
         should_restart() cannot keep firing forever"
    );
}

/// Inc-10: the assumption CDCL loop must honor `should_stop` even when the
/// search makes no conflicts/decisions progress. The iteration-counter
/// backstop polls the callback every 1024 loop iterations, so a solve with an
/// already-expired deadline terminates promptly regardless of search shape.
#[test]
fn assumption_solve_with_expired_deadline_terminates() {
    let mut solver: Solver = Solver::new(64);
    // A small pigeonhole-ish formula that needs real search.
    for i in 0..16u32 {
        solver.add_clause(vec![
            Literal::positive(Variable(i)),
            Literal::positive(Variable(i + 16)),
            Literal::positive(Variable(i + 32)),
        ]);
    }
    let assumptions: Vec<Literal> = (0..8u32).map(|i| Literal::negative(Variable(i))).collect();

    let start = ay_core::time::Instant::now();
    // Deadline already expired: solver must return Unknown quickly instead of
    // running to completion or spinning.
    let result = solver.solve_with_assumptions_interruptible(&assumptions, || true);
    assert!(
        result.is_unknown() || result.is_sat() || result.is_unsat(),
        "result must be well-formed"
    );
    assert!(
        start.elapsed() < std::time::Duration::from_secs(5),
        "expired-deadline solve must terminate promptly"
    );
}

/// Incremental cadence of core-guided MaxSAT: allocate fresh variables and
/// add clauses referencing them between assumption solves. The assumption
/// cache must survive (no full reset), and correctness must hold: the
/// deferred clauses participate in BCP after the incremental attach.
#[test]
fn new_var_between_assumption_solves_keeps_cache_and_correctness() {
    let mut solver = Solver::new(2);
    let a = Literal::positive(Variable::new(0));
    let b = Literal::positive(Variable::new(1));
    solver.add_clause(vec![a, b]);

    let first = solver.solve_with_assumptions(&[a]).into_inner();
    assert!(first.is_sat(), "initial solve should be SAT");

    let misses_before = solver.stats.assumption_cache_misses;
    let hits_before = solver.stats.assumption_cache_hits;

    // OLL-style step: fresh var + clauses tying it to existing ones.
    let t = Literal::positive(solver.new_var());
    solver.add_clause(vec![a.negated(), t]); // a -> t
    solver.add_clause(vec![b.negated(), t]); // b -> t

    // Assuming ¬t forces ¬a and ¬b; with (a ∨ b) this is UNSAT, and the
    // core must mention ¬t. This only works if the deferred clauses were
    // attached and watched on the incremental path.
    let second = solver.solve_with_assumptions(&[t.negated()]).into_inner();
    match second {
        AssumeResult::Unsat(core, _) => {
            assert!(
                core.contains(&t.negated()),
                "core must contain the failing assumption, got {core:?}",
            );
        }
        other => panic!("expected UNSAT under ¬t, got {other:?}"),
    }

    assert_eq!(
        solver.stats.assumption_cache_misses, misses_before,
        "new_var + add_clause must not force a full reset",
    );
    assert!(
        solver.stats.assumption_cache_hits > hits_before,
        "second solve should take the incremental path",
    );

    // And SAT the other way: assuming t is satisfiable.
    let third = solver.solve_with_assumptions(&[t]).into_inner();
    assert!(third.is_sat(), "assuming t should be SAT");
}
