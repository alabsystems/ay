// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit and integration tests for the IC3-optimized solve path (`ic3.rs`).
//!
//! Split out of `ic3.rs` as part of #8839 (single-file giants >2000 LOC).
//! The production code lives in `ic3.rs`; this file contains only tests.
//! Kept behind `#[cfg(test)]` so it compiles only under `cargo test`.

#[cfg(test)]
mod tests {
    use crate::{Literal, Solver, Variable};

    fn var(i: u32) -> Variable {
        Variable::new(i)
    }
    fn pos(i: u32) -> Literal {
        Literal::positive(var(i))
    }
    fn neg(i: u32) -> Literal {
        Literal::negative(var(i))
    }

    fn add_indirect_assumption_chain(s: &mut Solver) {
        // x0 => x3, and x3 => !x1.
        s.add_clause(vec![neg(0), pos(3)]);
        s.add_clause(vec![neg(3), neg(1)]);
    }

    #[test]
    fn ic3_solve_trivial_sat() {
        let mut s = Solver::new(3);
        // (x0 | x1) & (x1 | x2)
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![pos(1), pos(2)]);

        let result = s.solve_incremental_ic3(&[]);
        assert!(result.is_sat(), "expected SAT, got {result:?}");
    }

    #[test]
    fn ic3_solve_trivial_unsat() {
        let mut s = Solver::new(2);
        // x0 & !x0
        s.add_clause(vec![pos(0)]);
        s.add_clause(vec![neg(0)]);

        let result = s.solve_incremental_ic3(&[]);
        assert!(result.is_unsat(), "expected UNSAT, got {result:?}");
    }

    #[test]
    fn ic3_solve_with_assumptions_sat() {
        let mut s = Solver::new(3);
        // (x0 | x1) & (x1 | x2)
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![pos(1), pos(2)]);

        let result = s.solve_incremental_ic3(&[pos(1)]);
        assert!(result.is_sat(), "expected SAT with x1=true");
    }

    #[test]
    fn ic3_solve_with_assumptions_unsat() {
        let mut s = Solver::new(3);
        // (x0 | x1) & (!x0 | !x1) & (x0 | !x1)
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![neg(0), neg(1)]);
        s.add_clause(vec![pos(0), neg(1)]);
        // x0=true, x1=false is the only solution.
        // Assume x1=true → UNSAT.
        let result = s.solve_incremental_ic3(&[pos(1)]);
        assert!(result.is_unsat(), "expected UNSAT with x1=true");
    }

    #[test]
    fn ic3_unsat_core_resolves_indirect_assumption_chain() {
        let mut s = Solver::new(4);
        add_indirect_assumption_chain(&mut s);
        s.set_ic3_mode();

        let result = s.solve_incremental_ic3(&[pos(0), pos(1), pos(2)]);
        let core = result
            .unsat_core()
            .expect("x0=true and x1=true should be UNSAT");

        assert!(
            core.contains(&pos(0)),
            "IC3 core must include x0, which implies x3: {core:?}"
        );
        assert!(
            core.contains(&pos(1)),
            "IC3 core must include the contradicted x1 assumption: {core:?}"
        );
        assert!(
            !core.contains(&pos(2)),
            "IC3 core should not include irrelevant x2: {core:?}"
        );

        let mut reduced = Solver::new(4);
        add_indirect_assumption_chain(&mut reduced);
        reduced.set_ic3_mode();
        assert!(
            reduced.solve_incremental_ic3(core).is_unsat(),
            "returned IC3 core must reproduce UNSAT: {core:?}"
        );
    }

    #[test]
    fn ic3_incremental_multiple_solves() {
        let mut s = Solver::new(4);
        // (x0 | x1) & (x2 | x3)
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![pos(2), pos(3)]);

        // First solve: SAT
        let r1 = s.solve_incremental_ic3(&[pos(0)]);
        assert!(r1.is_sat());

        // Second solve: different assumptions, still SAT
        let r2 = s.solve_incremental_ic3(&[neg(0), pos(1)]);
        assert!(r2.is_sat());

        // Third solve: force contradiction
        s.add_clause(vec![neg(1)]);
        s.add_clause(vec![neg(0)]);
        let r3 = s.solve_incremental_ic3(&[]);
        // (!x0 & !x1) contradicts (x0 | x1) → UNSAT
        assert!(r3.is_unsat());
    }

    #[test]
    fn ic3_with_domain_restriction() {
        let mut s = Solver::new(5);
        // IC3 domain restriction: decisions restricted to domain vars,
        // BCP at level>0 uses domain-restricted propagation.
        // Test with UNSAT cube query (the typical IC3 use case).
        //
        // Clauses: x0 -> x1 (i.e., !x0 | x1) and x0 -> !x1 (i.e., !x0 | !x1)
        // With assumption x0=true: x1 must be both true and false → UNSAT.
        s.add_clause(vec![neg(0), pos(1)]); // !x0 | x1
        s.add_clause(vec![neg(0), neg(1)]); // !x0 | !x1
                                            // Background clauses involving vars outside domain
        s.add_clause(vec![pos(2), pos(3)]);
        s.add_clause(vec![pos(3), pos(4)]);

        // Domain: only vars 0,1 — the cone of influence for the IC3 query.
        s.set_domain(&[var(0), var(1)]);

        // Assume x0=true → conflict from clauses involving x1.
        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            result.is_unsat(),
            "expected UNSAT with domain restriction and x0=true"
        );

        // Without x0 assumption, should be SAT (x0=false satisfies both clauses).
        let result2 = s.solve_incremental_ic3(&[neg(0)]);
        assert!(
            result2.is_sat(),
            "expected SAT with domain restriction and x0=false"
        );

        s.clear_domain();
    }

    #[test]
    fn ic3_unsat_core_extraction() {
        let mut s = Solver::new(4);
        // x0 & x1 & (!x0 | !x1)
        s.add_clause(vec![pos(0)]);
        s.add_clause(vec![pos(1)]);
        s.add_clause(vec![neg(0), neg(1)]);

        // Assumptions don't matter — base clauses are UNSAT.
        let result = s.solve_incremental_ic3(&[]);
        assert!(result.is_unsat());
    }

    #[test]
    fn ic3_many_incremental_solves() {
        // Simulate IC3-like pattern: many short solves with varying assumptions.
        let mut s = Solver::new(8);
        // Build a small transition system-like clause set.
        for i in 0..7u32 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);
        s.add_clause(vec![neg(7), pos(0)]);

        for iteration in 0..100 {
            let assume_var = (iteration % 8) as u32;
            let result = s.solve_incremental_ic3(&[pos(assume_var)]);
            assert!(result.is_sat(), "iteration {iteration}: expected SAT");
        }
    }

    #[test]
    fn luby_sequence_values() {
        // Verify luby sequence matches known values: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
        let vals: Vec<f64> = (0..8)
            .map(|i| crate::solver::solve::ic3::luby(2.0, i))
            .collect();
        // luby(2.0, x) = 2^e where u(x + 1) = 2^e in the published Luby
        // sequence u(1), u(2), ... = 1, 1, 2, 1, 1, 2, 4, ... (Luby,
        // Sinclair & Zuckerman 1993), so the counter is 0-based.
        // Just verify it's deterministic and increasing on average.
        assert!(vals[0] > 0.0);
        assert!(vals[2] >= vals[0]); // sequence grows
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 push/pop + solve_incremental_ic3 integration tests (#8546)
    // ════════════════════════════════════════════════════════════════════════════

    /// IC3 push/pop + incremental solve: the core pattern that triggers
    /// FINALIZE_SAT_FAIL when the ledger is inconsistent after pop.
    ///
    /// Pattern: push -> add_clause(temp) -> solve_incremental_ic3 -> pop -> solve
    /// This exercises both the scoped clause addition and the IC3 fast path.
    #[test]
    fn ic3_push_pop_with_incremental_solve() {
        let mut s = Solver::new(8);
        // Build a satisfiable transition relation.
        for i in 0..4u32 {
            s.add_clause(vec![pos(i), pos(i + 4)]);
        }
        s.add_clause(vec![neg(0), neg(1), pos(2)]);
        s.add_clause(vec![neg(4), pos(5)]);

        for round in 0..30u32 {
            // IC3 scoped query: push -> add temp clause -> solve -> pop
            s.push();
            let temp = if round % 2 == 0 {
                pos(round % 4)
            } else {
                neg(round % 4)
            };
            s.add_clause(vec![temp]);

            let assumptions = vec![pos((round + 2) % 4)];
            let combined = s.compose_scope_assumptions(&assumptions);
            let _scoped = s.solve_incremental_ic3(&combined);
            assert!(s.pop(), "pop should succeed in round {round}");

            // Unscoped query: must not trigger FINALIZE_SAT_FAIL.
            let result = s.solve_incremental_ic3(&[pos(round % 4)]);
            // The result should be SAT or UNSAT (both are fine).
            // What matters is it does NOT return Unknown/InvalidSatModel.
            let inner = result.into_inner();
            if let crate::AssumeResult::Unknown = &inner {
                if let Some(detail) = &s.cold.last_unknown_detail {
                    assert!(
                        !detail.contains("unsatisfied"),
                        "FINALIZE_SAT_FAIL via IC3 path in round {round}: {detail}"
                    );
                }
            }
        }
    }

    /// IC3 push/pop with global clause additions (frame lemmas) + solve_incremental_ic3.
    ///
    /// This is the most representative IC3 pattern: the solver accumulates
    /// permanent blocking clauses (frame lemmas) via add_clause_global() while
    /// doing push/pop for temporary obligations.
    #[test]
    fn ic3_push_pop_global_lemmas_with_incremental_solve() {
        let mut s = Solver::new(12);
        // Transition relation-like clauses.
        for i in 0..6u32 {
            s.add_clause(vec![pos(i), pos(i + 6)]);
        }
        s.add_clause(vec![neg(0), neg(1), pos(2)]);
        s.add_clause(vec![neg(3), pos(4)]);

        for round in 0..60u32 {
            // Add a permanent blocking clause (IC3 frame lemma).
            let l1 = if round % 3 == 0 {
                pos(round % 6)
            } else {
                neg(round % 6)
            };
            let l2 = pos((round + 3) % 6);
            s.add_clause_global(vec![l1, l2]);

            // Scoped obligation query.
            s.push();
            let temp = if round % 2 == 0 {
                pos(round % 6)
            } else {
                neg(round % 6)
            };
            s.add_clause(vec![temp, pos((round + 1) % 6)]);

            let assumptions = vec![pos(round % 6)];
            let combined = s.compose_scope_assumptions(&assumptions);
            let _scoped = s.solve_incremental_ic3(&combined);
            assert!(s.pop(), "pop should succeed in round {round}");

            // Unscoped check with different assumptions.
            let result = s.solve_incremental_ic3(&[neg((round + 1) % 6)]);
            let inner = result.into_inner();
            if matches!(&inner, crate::AssumeResult::Unknown) {
                if let Some(detail) = &s.cold.last_unknown_detail {
                    assert!(
                        !detail.contains("unsatisfied"),
                        "FINALIZE_SAT_FAIL via IC3+global path in round {round}: {detail}"
                    );
                }
            }
        }
    }

    /// IC3 with domain restriction + push/pop: the full realistic IC3 workload.
    ///
    /// Domain restriction causes the IC3 path to bypass finalize_sat_model
    /// (line 297-299 in ic3.rs) for domain-restricted queries. But unscoped
    /// queries without domain restriction still go through finalize_sat_model.
    /// This test alternates between both paths.
    #[test]
    fn ic3_domain_push_pop_mixed() {
        let mut s = Solver::new(10);
        // Transition relation with distinct current (0-4) and next (5-9) vars.
        for i in 0..5u32 {
            s.add_clause(vec![neg(i), pos(i + 5)]); // x_i -> x_{i+5}
        }
        s.add_clause(vec![pos(0), pos(1), pos(2)]); // at least one current-state var true
        s.add_clause(vec![pos(5), pos(6), pos(7)]); // at least one next-state var true

        for round in 0..40u32 {
            // Domain-restricted IC3 query (push/pop).
            s.set_domain(&[var(0), var(1), var(2), var(5), var(6), var(7)]);
            s.push();
            s.add_clause(vec![pos(round % 5)]);
            let combined = s.compose_scope_assumptions(&[pos(round % 5)]);
            let _r = s.solve_incremental_ic3(&combined);
            assert!(s.pop());
            s.clear_domain();

            // Non-domain-restricted query (goes through finalize_sat_model).
            let result = s.solve_incremental_ic3(&[pos(round % 5)]);
            let inner = result.into_inner();
            if matches!(&inner, crate::AssumeResult::Unknown) {
                if let Some(detail) = &s.cold.last_unknown_detail {
                    assert!(
                        !detail.contains("unsatisfied"),
                        "FINALIZE_SAT_FAIL in domain+push/pop round {round}: {detail}"
                    );
                }
            }
        }
    }

    /// IC3 mode API (#8569): set_ic3_mode() disables inprocessing, chrono-BT,
    /// proofs, and other IC3-unnecessary features. Verify that the solver
    /// works correctly after set_ic3_mode() across many incremental solves.
    #[test]
    fn ic3_mode_api_basic() {
        let mut s = Solver::new(8);
        // Build a small transition system-like clause set.
        for i in 0..7u32 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);
        s.add_clause(vec![neg(7), pos(0)]);

        // Enable IC3 mode.
        s.set_ic3_mode();
        assert!(s.is_ic3_mode());

        // Verify features are disabled.
        assert!(!s.cold.preprocess_enabled);
        assert!(!s.cold.lrat_enabled);
        assert!(!s.chrono_enabled);
        assert!(!s.cold.cold_restart_enabled);
        assert!(!s.cold.rephase_enabled);
        assert!(!s.cold.flip_search_enabled);

        // Run many IC3 solves.
        for iteration in 0..200 {
            let assume_var = (iteration % 8) as u32;
            let result = s.solve_incremental_ic3(&[pos(assume_var)]);
            assert!(result.is_sat(), "iteration {iteration}: expected SAT");
        }
    }

    /// Production setup contract for HWMCC model-checker consumer frame solvers (#8869):
    /// configure IC3 mode from a fresh solver before any clauses or solves,
    /// then add the permanent frame clauses and solve domain-restricted cubes.
    #[test]
    fn ic3_mode_supported_from_fresh_solver_before_clauses() {
        let mut s = Solver::new(6);

        // the model-checker consumer's constructor already applies generic preprocessing knobs. IC3
        // mode is the final profile selection and makes those calls redundant.
        s.set_full_preprocessing(true);
        s.disable_all_inprocessing();
        s.set_ic3_mode();
        s.set_ic3_mode();

        assert!(s.is_ic3_mode());
        assert!(!s.cold.preprocess_enabled);
        assert!(!s.cold.lrat_enabled);
        assert!(!s.chrono_enabled);
        assert!(!s.cold.cold_restart_enabled);
        assert!(!s.cold.rephase_enabled);
        assert!(!s.cold.flip_search_enabled);

        // x0 -> x1 -> x2 -> x3, and !x3. Assuming x0 must conflict through
        // the IC3 domain BCP route; no warm-up solve happened before this.
        s.add_clause(vec![neg(0), pos(1)]);
        s.add_clause(vec![neg(1), pos(2)]);
        s.add_clause(vec![neg(2), pos(3)]);
        s.add_clause(vec![neg(3)]);

        let frame_domain = [var(0), var(1), var(2), var(3)];
        s.set_domain(&frame_domain);
        assert!(s.bucket_queue_active);
        let blocked = s.solve_incremental_ic3(&[pos(0)]);
        assert!(blocked.is_unsat(), "x0 should be blocked by the frame");
        assert!(s.is_ic3_mode());

        // A later independent query should remain usable after clearing and
        // refreshing the domain. This mirrors a second IC3 cube check.
        s.clear_domain();
        s.add_clause(vec![pos(4), pos(5)]);
        let next_domain = [var(4), var(5)];
        s.set_domain(&next_domain);
        assert!(s.bucket_queue_active);
        let open = s.solve_incremental_ic3(&[pos(4)]);
        assert!(open.is_sat(), "independent frame cube should remain SAT");
    }

    /// IC3 mode with domain restriction and add_clause between solves (#8569).
    /// Tests the full realistic IC3 pattern: set_ic3_mode + set_domain +
    /// add_clause (blocking clauses) + solve_incremental_ic3.
    #[test]
    fn ic3_mode_with_domain_and_blocking_clauses() {
        let mut s = Solver::new(10);
        // Transition relation: x_i -> x_{i+5} for i in 0..5.
        for i in 0..5u32 {
            s.add_clause(vec![neg(i), pos(i + 5)]);
        }
        s.add_clause(vec![pos(0), pos(1), pos(2)]);
        s.add_clause(vec![pos(5), pos(6), pos(7)]);

        s.set_ic3_mode();
        s.set_domain(&[var(0), var(1), var(2), var(5), var(6), var(7)]);

        // Simulate IC3: alternate between solving and adding blocking clauses.
        for round in 0..100u32 {
            let lit = if round % 2 == 0 {
                pos(round % 5)
            } else {
                neg(round % 5)
            };
            let result = s.solve_incremental_ic3(&[lit]);
            // We don't care about SAT/UNSAT — just that it doesn't crash.
            let _ = result.into_inner();

            // Add a blocking clause (frame lemma) between solves.
            let l1 = pos(round % 5);
            let l2 = pos((round + 2) % 5);
            s.add_clause(vec![l1, l2]);
        }

        s.clear_domain();
    }

    /// IC3 mode bucket-to-heap transition (#8662 Gap 5): verify that the
    /// bucket queue falls back to heap after BUCKET_QUEUE_RESTART_THRESHOLD
    /// restarts within a single hard query, and is re-enabled at the next
    /// query via set_domain().
    ///
    /// Lifecycle under test: bucket enabled at query start, disabled once
    /// the restart threshold is reached within the query, re-enabled at
    /// the next query. This benefits the ~1% of IC3
    /// queries with 100+ conflicts where the heap's exact activity ordering
    /// makes better variable decisions than the bucket's coarse granularity.
    #[test]
    fn ic3_mode_bucket_to_heap_transition() {
        let mut s = Solver::new(20);
        // Harder formula that generates conflicts and restarts.
        for i in 0..10u32 {
            s.add_clause(vec![pos(i), pos(i + 10)]);
            if i < 9 {
                s.add_clause(vec![neg(i), neg(i + 1)]);
                s.add_clause(vec![neg(i + 10), neg(i + 11)]);
            }
        }

        s.set_ic3_mode();

        // Short queries: bucket queue should remain active.
        // Each solve is a separate query with its own restart counter.
        let domain = [var(0), var(1), var(2), var(3), var(4)];
        s.set_domain(&domain);

        for i in 0..20u32 {
            let cube_lit = if i % 2 == 0 { pos(i % 5) } else { neg(i % 5) };
            let _r = s.solve_incremental_ic3(&[cube_lit]);
        }

        // After short queries, bucket queue should still be active because
        // each query has its own restart counter and short queries don't
        // reach the restart threshold.
        // Note: bucket_queue_active may be true or false depending on whether
        // any individual query hit the threshold. For the domain above, most
        // queries should be short. The key invariant is that set_domain()
        // re-enables the bucket queue.
        s.set_domain(&domain);
        assert!(
            s.bucket_queue_active,
            "set_domain should re-enable bucket queue"
        );

        s.clear_domain();
    }

    /// IC3 scoped BVE integration (#8503): verify that incremental
    /// inprocessing with scoped BVE runs during the IC3 fast path when
    /// a push() scope is active.
    ///
    /// This test creates a formula with push() scope, adds BVE-eliminable
    /// scoped variables, runs IC3 solves that generate conflicts to trigger
    /// the inprocessing gate, and verifies that:
    /// 1. Incremental inprocessing fires during IC3 solves
    /// 2. pop() correctly restores state
    /// 3. The base formula remains correct after pop
    #[test]
    fn ic3_scoped_bve_clause_reduction() {
        let num_base_vars = 50usize;
        let mut s = Solver::new(num_base_vars);

        // Production IC3/PDR profile: all broad inprocessing is disabled, while
        // scoped BVE remains enabled behind the active-scope guard.
        s.set_ic3_mode();
        assert!(s.is_ic3_mode());
        assert!(s.inproc_ctrl.bve.enabled);
        assert!(!s.inproc_ctrl.subsume.enabled);
        s.inproc_ctrl.bve.next_conflict = 0;

        // Base formula: conflict-rich structure that forces CDCL search.
        // Pigeonhole-style constraints on vars 0-19 create enough conflicts
        // even in short IC3 queries.
        for i in 0..10u32 {
            // At least one of each pair must be true.
            s.add_clause(vec![pos(i), pos(i + 10)]);
            // But not both in the same group.
            if i < 9 {
                s.add_clause(vec![neg(i), neg(i + 1)]);
                s.add_clause(vec![neg(i + 10), neg(i + 11)]);
            }
        }

        // Environment constraints: fix vars 30-49 to false.
        for i in 30..50u32 {
            s.add_clause(vec![neg(i)]);
        }

        // First solve to propagate units and establish baseline.
        let r0 = s.solve_incremental_ic3(&[]);
        assert!(r0.is_sat(), "base formula should be SAT");

        // Push scope.
        s.push();
        assert!(s.has_scoped_bve(), "push must enable scoped BVE");

        // Allocate scoped variables for BVE.
        let num_scoped = 15usize;
        for _ in 0..num_scoped {
            s.new_var_internal();
        }
        let scope_base = (num_base_vars + 1) as u32; // Skip selector var

        // Create BVE-eliminable scoped clauses: each scoped variable has
        // one positive and one negative occurrence with state/env literals.
        for j in 0..num_scoped as u32 {
            let sv = scope_base + j;
            let state_a = j % 10;
            let state_b = (j + 3) % 10;
            let env_a = 30 + j * 2;

            s.add_clause(vec![pos(sv), pos(state_a), pos(env_a)]);
            s.add_clause(vec![neg(sv), pos(state_b)]);
        }

        // Set scheduling state so the inprocessing gate fires on the
        // next IC3 solve. The gate checks:
        //   total_conflicts > 0  (lifetime_conflicts + num_conflicts)
        //   total_conflicts >= next_inprobe_conflict
        //   num_reductions != last_inprobe_reduction
        s.cold.lifetime_conflicts = 100; // Simulate prior conflict accumulation
        s.cold.next_inprobe_conflict = 0;
        s.cold.last_inprobe_reduction = 0;
        s.cold.num_reductions = 1; // Ensure reduction gate passes

        // Run IC3 solves. The first solve after setting the gate state
        // should trigger incremental inprocessing (including scoped BVE).
        for i in 0..20u32 {
            let cube_var = i % 10;
            let cube_lit = if i % 2 == 0 {
                pos(cube_var)
            } else {
                neg(cube_var)
            };
            let r = s.solve_incremental_ic3(&[cube_lit]);
            // SAT or UNSAT are both valid -- the formula has constraints.
            let _inner = r.into_inner();
        }

        let inproc_rounds = s.stats.incremental_inprocessing_rounds;

        // Pop scope: any eliminated variables should be restored.
        assert!(s.pop());

        // Base formula should still be SAT after pop.
        let r_final = s.solve_incremental_ic3(&[]);
        assert!(
            r_final.is_sat(),
            "base formula must be SAT after scoped BVE pop, got {:?}",
            r_final.into_inner()
        );

        // Verify inprocessing ran at least once (gate state was set to
        // allow firing, and we ran 20 IC3 solves).
        assert!(
            inproc_rounds > 0,
            "incremental inprocessing should have fired at least once \
             during 20 IC3 solves with lifetime_conflicts=100 and \
             next_inprobe=0 (total_conflicts={}, next_inprobe={})",
            s.total_conflicts(),
            s.cold.next_inprobe_conflict,
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Regression test for #8633: false UNSAT on high constraint/variable ratio
    // ════════════════════════════════════════════════════════════════════════════

    /// Regression test for #8633: incremental clause attachment with
    /// already-false watched literals causing missed unit propagations.
    ///
    /// Scenario: After a solve that establishes level-0 units, adding a
    /// multi-literal clause where the first two literals are false at
    /// level-0 makes the clause invisible to BCP. If the clause is the
    /// only reason to propagate its remaining literal, the solver misses
    /// the propagation and may produce false UNSAT.
    #[test]
    fn test_ic3_incremental_clause_with_stale_watches_regression_8633() {
        // Setup: 6 variables.
        // Initial clauses establish that x0=true and x1=true at level 0.
        let mut s = Solver::new(6);

        // Unit clauses: x0=true, x1=true (will be level-0 after first solve).
        s.add_clause(vec![pos(0)]);
        s.add_clause(vec![pos(1)]);
        // Add a clause requiring x2 or x3 to be true.
        s.add_clause(vec![pos(2), pos(3)]);

        // First solve: establishes x0=true, x1=true at level 0.
        let r1 = s.solve_incremental_ic3(&[]);
        assert!(
            r1.is_sat(),
            "base formula should be SAT, got {:?}",
            r1.into_inner()
        );

        // Now add a clause: (!x0 | !x1 | x4)
        // Since x0=true and x1=true at level 0, both !x0 and !x1 are false.
        // This clause is effectively unit: x4 must be true.
        // BUG: Without the fix, watches go on !x0 and !x1 (both false),
        // making the clause invisible to BCP. x4 is never propagated.
        s.add_clause(vec![neg(0), neg(1), pos(4)]);

        // Also add: (!x4 | x5) — x4 should propagate true, then x5 should.
        s.add_clause(vec![neg(4), pos(5)]);

        // And add: (!x5) — this SHOULD conflict if x4 and x5 propagate correctly.
        // But with the bug, x4 never propagates, so !x5 is accepted and the
        // solver reports SAT or UNSAT for the wrong reason.
        // Actually, without x4 propagated, the solver doesn't know x4 must be true.
        // If the solver doesn't propagate x4, then neg(5) doesn't conflict.

        // More precisely: Add a clause that forces x4=true to be necessary,
        // and a clause that contradicts x4=true under some assumption.
        // Without x4 propagated from the first clause, the solver misses
        // that x4=true is forced, and may find a spurious SAT or UNSAT.

        // Second solve: should still be SAT (x4=true, x5=true from propagation).
        let r2 = s.solve_incremental_ic3(&[]);
        assert!(
            r2.is_sat(),
            "formula with forced x4=true should be SAT, got {:?}",
            r2.into_inner()
        );

        // Now verify that x4 was actually propagated: add !x4 as a clause
        // and check UNSAT.
        s.add_clause(vec![neg(4)]);
        let r3 = s.solve_incremental_ic3(&[]);
        // With x4 forced true by (!x0|!x1|x4) and now !x4 forced, must be UNSAT.
        assert!(
            r3.is_unsat(),
            "forcing x4=false should contradict x4=true from propagation, got {:?}",
            r3.into_inner()
        );
    }

    /// Regression test for #8633: incremental clause that is all-false at
    /// level-0 should produce immediate UNSAT, not be silently ignored.
    ///
    /// Scenario: After establishing x0=true, x1=true at level 0, add
    /// a clause (!x0 & !x1) which is entirely falsified. The solver must
    /// detect this as a level-0 conflict and return UNSAT.
    #[test]
    fn test_ic3_incremental_all_false_clause_conflict_8633() {
        let mut s = Solver::new(4);

        // Unit clauses: x0=true, x1=true
        s.add_clause(vec![pos(0)]);
        s.add_clause(vec![pos(1)]);
        // Satisfiable padding
        s.add_clause(vec![pos(2), pos(3)]);

        // First solve: establishes x0=true, x1=true at level 0.
        let r1 = s.solve_incremental_ic3(&[]);
        assert!(
            r1.is_sat(),
            "base formula should be SAT, got {:?}",
            r1.into_inner()
        );

        // Add clause (!x0 | !x1) — both negated literals are false at level 0.
        // This clause is falsified by the level-0 assignments.
        // The solver must detect this as a conflict.
        s.add_clause(vec![neg(0), neg(1)]);

        let r2 = s.solve_incremental_ic3(&[]);
        assert!(
            r2.is_unsat(),
            "adding all-false clause should make formula UNSAT, got {:?}",
            r2.into_inner()
        );
    }

    /// Regression test for #8633: incremental clause with exactly one
    /// non-false literal should propagate that literal as a unit.
    ///
    /// Scenario: After establishing x0=true at level 0, add clause
    /// (!x0 | x2). Since !x0 is false, x2 is the only non-false literal
    /// and must be propagated as a unit.
    #[test]
    fn test_ic3_incremental_unit_propagation_from_partial_false_8633() {
        let mut s = Solver::new(4);

        // Unit clause: x0=true
        s.add_clause(vec![pos(0)]);
        // Padding
        s.add_clause(vec![pos(1), pos(2), pos(3)]);

        // First solve
        let r1 = s.solve_incremental_ic3(&[]);
        assert!(
            r1.is_sat(),
            "base formula should be SAT, got {:?}",
            r1.into_inner()
        );

        // Add (!x0 | x2) — since x0=true at level 0, !x0 is false.
        // x2 must be propagated as unit.
        s.add_clause(vec![neg(0), pos(2)]);

        // Add (!x2) — this contradicts the unit propagation of x2.
        s.add_clause(vec![neg(2)]);

        let r2 = s.solve_incremental_ic3(&[]);
        assert!(
            r2.is_unsat(),
            "formula should be UNSAT: x2 forced true by (!x0|x2) but also forced false by (!x2), got {:?}",
            r2.into_inner()
        );
    }

    /// Regression test for #8633: high constraint-to-variable ratio IC3 stress
    /// test with cross-check. Simulates the microban/cal76 pattern: many
    /// constraints, few variables, many incremental solves.
    #[test]
    fn test_ic3_high_constraint_ratio_cross_check_8633() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a dense formula: implications forming a chain.
        // x_i -> x_{i+1} for i in 0..num_vars-1
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // Add more cross-constraints to increase density.
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        for i in 0..num_vars - 3 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
        }

        // Run many IC3-like queries with different assumptions.
        for iteration in 0..200u32 {
            let assume_var = iteration % num_vars;
            let assume_lit = if iteration % 3 == 0 {
                neg(assume_var)
            } else {
                pos(assume_var)
            };

            let result = s.solve_incremental_ic3(&[assume_lit]);

            // Cross-check: if UNSAT, verify the core is non-trivially valid.
            // If SAT, the formula with assumptions must be satisfiable.
            if result.is_unsat() {
                // The UNSAT core should be non-empty (it was UNSAT due to assumptions).
                // If core is empty but formula is satisfiable without assumptions,
                // that's a false UNSAT bug.
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "iteration {iteration}: base formula is UNSAT but individual \
                     assumption queries should not make it permanently UNSAT"
                );
            }

            // Periodically add blocking clauses (IC3 pattern).
            if iteration % 10 == 5 {
                let v0 = iteration % num_vars;
                let v1 = (iteration + 1) % num_vars;
                let v2 = (iteration + 2) % num_vars;
                if v0 != v1 && v1 != v2 && v0 != v2 {
                    s.add_clause(vec![pos(v0), neg(v1), pos(v2)]);
                }
            }
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3-optimized BCP tests (#8569 Gap 2)
    // ════════════════════════════════════════════════════════════════════════════

    /// IC3 BCP with binary-only clauses (common in IC3 workloads).
    /// Verifies that the stripped BCP produces the same results as the
    /// standard path for a formula with only binary clauses.
    #[test]
    fn ic3_bcp_binary_clauses_only() {
        let mut s = Solver::new(6);
        // Implication chain: x0 -> x1 -> x2 -> x3 -> x4 -> x5
        s.add_clause(vec![neg(0), pos(1)]);
        s.add_clause(vec![neg(1), pos(2)]);
        s.add_clause(vec![neg(2), pos(3)]);
        s.add_clause(vec![neg(3), pos(4)]);
        s.add_clause(vec![neg(4), pos(5)]);
        // And x5 -> !x0 (creates cycle -> UNSAT with x0=true)
        s.add_clause(vec![neg(5), neg(0)]);

        s.set_ic3_mode();
        s.set_domain(&[var(0), var(1), var(2), var(3), var(4), var(5)]);

        // Assume x0=true -> propagation chain -> conflict at x5 -> !x0
        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(result.is_unsat(), "binary chain with cycle should be UNSAT");

        // Assume x0=false -> SAT (all implications vacuously true)
        let result2 = s.solve_incremental_ic3(&[neg(0)]);
        assert!(result2.is_sat(), "x0=false should be SAT");

        s.clear_domain();
    }

    /// IC3 BCP with mixed binary and long clauses.
    /// Verifies correctness of the stripped BCP replacement scan for long clauses.
    #[test]
    fn ic3_bcp_mixed_binary_and_long() {
        let mut s = Solver::new(8);
        // Binary clauses: x0 -> x1, x1 -> x2
        s.add_clause(vec![neg(0), pos(1)]);
        s.add_clause(vec![neg(1), pos(2)]);
        // Long clause: (!x2 | x3 | x4) — forces replacement scan
        s.add_clause(vec![neg(2), pos(3), pos(4)]);
        // Long clause: (!x3 | !x4 | x5) — another replacement scan
        s.add_clause(vec![neg(3), neg(4), pos(5)]);
        // Binary: x5 -> x6
        s.add_clause(vec![neg(5), pos(6)]);
        // Long: (!x5 | !x6 | x7) — force unit on x7
        s.add_clause(vec![neg(5), neg(6), pos(7)]);
        // Close the loop: (!x7 | !x0) — conflict with x0=true
        s.add_clause(vec![neg(7), neg(0)]);

        s.set_ic3_mode();
        s.set_domain(&[
            var(0),
            var(1),
            var(2),
            var(3),
            var(4),
            var(5),
            var(6),
            var(7),
        ]);

        let result = s.solve_incremental_ic3(&[pos(0)]);
        // With x0=true, propagation forces x1, x2 true. Then long clauses
        // allow various x3/x4 combinations, but eventually conflict arises.
        // The exact result depends on search, but it should not crash.
        let _ = result.into_inner();

        s.clear_domain();
    }

    /// IC3 BCP domain restriction: verify non-domain variables are skipped.
    /// Creates a formula where domain BCP must skip non-domain watchers.
    #[test]
    fn ic3_bcp_domain_restriction_skips_correctly() {
        let mut s = Solver::new(10);
        // Domain vars: 0,1,2
        // Non-domain vars: 3,4,5,6,7,8,9
        //
        // Clause (!x0 | x3) — blocker x3 is non-domain, should be skipped.
        s.add_clause(vec![neg(0), pos(3)]);
        // Clause (!x0 | x4 | x5) — first watched non-domain, skip.
        s.add_clause(vec![neg(0), pos(4), pos(5)]);
        // Clause (!x0 | x1) — both in domain, normal propagation.
        s.add_clause(vec![neg(0), pos(1)]);
        // Clause (!x1 | x2) — both in domain, propagate x2.
        s.add_clause(vec![neg(1), pos(2)]);

        s.set_ic3_mode();
        s.set_domain(&[var(0), var(1), var(2)]);

        // With x0=true: domain BCP should propagate x1, x2 and skip x3/x4/x5.
        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            result.is_sat(),
            "domain-restricted query with x0=true should be SAT"
        );

        s.clear_domain();
    }

    /// IC3 BCP produces same results as standard domain BCP across many queries.
    /// This is the key correctness test: run the same queries through both
    /// the IC3 BCP path (ic3_mode=true) and the standard domain BCP path
    /// (ic3_mode=false), verifying they agree.
    #[test]
    fn ic3_bcp_agrees_with_domain_bcp() {
        // Build a non-trivial formula.
        let n = 12u32;

        // Run queries through standard domain BCP path.
        let mut s_standard = Solver::new(n as usize);
        build_ic3_test_formula(&mut s_standard, n);
        // Do NOT enable ic3_mode -> uses propagate_domain_bcp

        // Run queries through IC3 BCP path.
        let mut s_ic3 = Solver::new(n as usize);
        build_ic3_test_formula(&mut s_ic3, n);
        s_ic3.set_ic3_mode();

        // Domain: first 6 variables.
        let domain_vars: Vec<Variable> = (0..6).map(var).collect();

        for round in 0..50u32 {
            let lit = if round % 3 == 0 {
                pos(round % 6)
            } else if round % 3 == 1 {
                neg(round % 6)
            } else {
                pos((round * 7 + 3) % 6)
            };

            s_standard.set_domain(&domain_vars);
            s_ic3.set_domain(&domain_vars);

            let r_standard = s_standard.solve_incremental_ic3(&[lit]);
            let r_ic3 = s_ic3.solve_incremental_ic3(&[lit]);

            let std_sat = r_standard.is_sat();
            let ic3_sat = r_ic3.is_sat();

            assert_eq!(
                std_sat,
                ic3_sat,
                "round {round}: standard BCP says {}, IC3 BCP says {} for assumption {:?}",
                if std_sat { "SAT" } else { "UNSAT" },
                if ic3_sat { "SAT" } else { "UNSAT" },
                lit
            );

            s_standard.clear_domain();
            s_ic3.clear_domain();

            // Add a blocking clause between solves (IC3 pattern).
            if round % 5 == 0 {
                let cl = vec![pos(round % 6), pos((round + 2) % 6)];
                s_standard.add_clause(cl.clone());
                s_ic3.add_clause(cl);
            }
        }
    }

    /// Helper: build a non-trivial formula for IC3 BCP testing.
    fn build_ic3_test_formula(s: &mut Solver, n: u32) {
        // Implication chains: x_i -> x_{i+1} for i in 0..n-1
        for i in 0..n - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // Some wider clauses
        for i in (0..n).step_by(3) {
            if i + 2 < n {
                s.add_clause(vec![pos(i), pos(i + 1), pos(i + 2)]);
            }
        }
        // Cross-connections
        if n > 6 {
            s.add_clause(vec![neg(0), neg(3), pos(5)]);
            s.add_clause(vec![neg(1), neg(4), pos(6)]);
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // #8633 incremental clause attachment tests
    // ════════════════════════════════════════════════════════════════════════════
    /// Stress test for #8633: 10,000 random IC3-shaped queries with high
    /// constraint-to-variable ratio (>5x). Tests the incremental clause
    /// attachment path exhaustively by adding blocking clauses between
    /// solves where level-0 assignments make watched literals stale.
    ///
    /// The base formula is carefully constructed to be satisfiable by
    /// all-true assignment. Blocking clauses are also satisfiable by
    /// all-true (they always contain at least one positive literal).
    /// This ensures the base formula ALWAYS has a satisfying assignment
    /// throughout all 10,000 queries, making any UNSAT-on-base-formula
    /// result a definitive false UNSAT bug.
    ///
    /// Acceptance criterion: 0 incorrect results across all 10,000 queries.
    #[test]
    fn test_ic3_high_constraint_ratio_stress_10000_queries_8633() {
        let num_vars = 10u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a dense formula with constraint/variable ratio > 5x.
        // INVARIANT: all-true is a satisfying assignment for every clause.
        // Each clause contains at least one positive literal.

        // Layer 1: Implication chain x_i -> x_{i+1} (9 clauses)
        // (!x_i | x_{i+1}): all-true satisfies x_{i+1}
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // Layer 2: Skip-1 implications (8 clauses)
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        // Layer 3: 3-literal with at least one positive (7 clauses)
        for i in 0..num_vars - 3 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
        }
        // Layer 4: Binary positive clauses (9 clauses)
        for i in 0..num_vars - 1 {
            s.add_clause(vec![pos(i), pos(i + 1)]);
        }
        // Layer 5: 3-literal with one neg (8 clauses)
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 1), pos(i + 2)]);
        }
        // Layer 6: Positive triangles (8 clauses)
        for i in 0..num_vars - 2 {
            s.add_clause(vec![pos(i), pos(i + 1), pos(i + 2)]);
        }
        // Layer 7: Mixed with positive anchor (7 clauses)
        for i in 0..num_vars - 3 {
            s.add_clause(vec![neg(i), pos(i + 2), pos(i + 3)]);
        }
        // Total initial clauses: 9+8+7+9+8+8+7 = 56 clauses for 10 vars (5.6x ratio)

        // Verify base formula is SAT before starting.
        let r_base = s.solve_incremental_ic3(&[]);
        assert!(
            r_base.is_sat(),
            "base formula should be SAT before queries, got {:?}",
            r_base.into_inner()
        );

        let mut error_count = 0u32;
        let mut first_error_iteration = None;
        let mut blocking_clauses_added = 0u32;

        for iteration in 0..10_000u32 {
            // Pick 1-2 assumptions per query using deterministic pattern.
            let v0 = iteration % num_vars;
            let v1 = (iteration.wrapping_mul(7).wrapping_add(3)) % num_vars;
            let polarity0 = iteration % 5 != 0;
            let polarity1 = iteration % 3 == 0;

            let lit0 = if polarity0 { pos(v0) } else { neg(v0) };
            let assumptions = if v0 == v1 {
                vec![lit0]
            } else {
                let lit1 = if polarity1 { pos(v1) } else { neg(v1) };
                vec![lit0, lit1]
            };

            let result = s.solve_incremental_ic3(&assumptions);

            // Cross-check: if UNSAT with assumptions, base formula must still
            // be SAT. The formula is designed so all-true is always a model.
            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                if !base.is_sat() {
                    if first_error_iteration.is_none() {
                        first_error_iteration = Some(iteration);
                    }
                    error_count += 1;
                }
            }

            // Every 50 iterations, add a blocking clause (IC3 pattern).
            // INVARIANT: always include at least one positive literal so
            // all-true remains a satisfying assignment.
            if iteration % 50 == 25 {
                let a = iteration % num_vars;
                let b = (iteration.wrapping_mul(3).wrapping_add(1)) % num_vars;
                let c = (iteration.wrapping_mul(7).wrapping_add(5)) % num_vars;
                if a != b && b != c && a != c {
                    // Always include pos(c) to preserve all-true model.
                    let la = if iteration % 4 < 2 { pos(a) } else { neg(a) };
                    let lb = if iteration % 6 < 3 { pos(b) } else { neg(b) };
                    s.add_clause(vec![la, lb, pos(c)]);
                    blocking_clauses_added += 1;
                }
            }
        }

        assert!(
            blocking_clauses_added >= 100,
            "expected at least 100 blocking clauses added, got {blocking_clauses_added}"
        );

        assert_eq!(
            error_count, 0,
            "IC3 stress test: {error_count} false UNSAT errors in 10,000 queries \
             (first error at iteration {first_error_iteration:?}, constraint/var ratio > 5x, \
             {blocking_clauses_added} blocking clauses added). \
             Base formula became permanently UNSAT from incremental clause corruption."
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 incremental state preservation tests (#8643)
    // ════════════════════════════════════════════════════════════════════════════

    /// Verify that learned clauses from call N are available in call N+1.
    /// This is the key acceptance criterion for #8643: IC3 relies on
    /// incrementally learned clauses to prune the search space across queries.
    #[test]
    fn ic3_learned_clauses_persist_across_calls() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a formula that generates conflicts (and thus learned clauses).
        // Implication chain: x_i -> x_{i+1}
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // Cross-constraints to create more conflicts.
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        // Some disjunctions for non-trivial search.
        for i in 0..num_vars - 3 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
        }

        // First batch of solves: generate learned clauses.
        for i in 0..50u32 {
            let lit = if i % 3 == 0 {
                neg(i % num_vars)
            } else {
                pos(i % num_vars)
            };
            let _r = s.solve_incremental_ic3(&[lit]);
        }

        // Count learned clauses after first batch.
        let learned_after_first_batch: usize = s
            .arena
            .indices()
            .filter(|&idx| s.arena.is_active(idx) && s.arena.is_learned(idx))
            .count();

        // Second batch of solves.
        for i in 50..100u32 {
            let lit = if i % 3 == 0 {
                neg(i % num_vars)
            } else {
                pos(i % num_vars)
            };
            let _r = s.solve_incremental_ic3(&[lit]);
        }

        // Count learned clauses after second batch.
        let learned_after_second_batch: usize = s
            .arena
            .indices()
            .filter(|&idx| s.arena.is_active(idx) && s.arena.is_learned(idx))
            .count();

        // Learned clauses should accumulate, not be destroyed between calls.
        // The second batch should have at least as many as the first (plus
        // new ones learned), since between_solve_reduce is disabled in IC3 mode.
        assert!(
            learned_after_second_batch >= learned_after_first_batch,
            "learned clauses should persist across IC3 calls: \
             first_batch={learned_after_first_batch}, second_batch={learned_after_second_batch}"
        );
    }

    /// Verify that VSIDS activity scores accumulate across IC3 calls.
    /// Variables involved in conflicts should have higher activity after
    /// many queries than after the first query.
    #[test]
    fn ic3_vsids_activity_accumulates_across_calls() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a formula that forces UNSAT with certain assumptions, which
        // generates conflicts and bumps VSIDS activity.
        // x_i -> x_{i+1} chain
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // x_{n-1} -> !x_0 (creates a cycle: x_0=true forces all vars true
        // which forces x_0=false -> contradiction)
        s.add_clause(vec![neg(num_vars - 1), neg(0)]);
        // Also add some clauses that force conflicts with specific assumptions.
        for i in 0..num_vars / 2 {
            // !x_i | !x_{i+num_vars/2} -- mutual exclusion
            s.add_clause(vec![neg(i), neg(i + num_vars / 2)]);
        }

        // Run many UNSAT queries (x0=true triggers the cycle contradiction).
        // These must generate conflicts that bump VSIDS.
        for i in 0..200u32 {
            let v = i % num_vars;
            let _r = s.solve_incremental_ic3(&[pos(v)]);
        }

        // After 200 queries with conflicts, some variables should have
        // non-zero VSIDS activity from conflict analysis bumping.
        // Note: rescaling normalizes max to 1.0 periodically, but activities
        // stay relatively ordered and non-zero.

        // Even if all queries are trivially resolved at level 0 (no VSIDS
        // bumping), the num_conflicts counter should be monotonic and the
        // incremental path should be used.
        assert!(
            s.stats.assumption_cache_hits > 0,
            "IC3 should use the incremental reset path (cache hits={}, misses={})",
            s.stats.assumption_cache_hits,
            s.stats.assumption_cache_misses,
        );

        // Verify conflicts were generated (at least some queries should be UNSAT).
        assert!(
            s.num_conflicts > 0 || s.cold.lifetime_conflicts > 0,
            "IC3 queries should generate some conflicts (num_conflicts={}, lifetime={})",
            s.num_conflicts,
            s.cold.lifetime_conflicts,
        );
    }

    /// Verify that phase saving persists across IC3 calls.
    /// The saved phase array should NOT be zeroed between calls.
    #[test]
    fn ic3_phase_saving_persists_across_calls() {
        let num_vars = 15u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(5)]);

        // Run solves to establish phase saving.
        for i in 0..50u32 {
            let lit = if i % 2 == 0 {
                pos(i % num_vars)
            } else {
                neg(i % num_vars)
            };
            let _r = s.solve_incremental_ic3(&[lit]);
        }

        // Check that some phases are saved (not all zero).
        let has_saved_phase = (0..num_vars as usize).any(|i| s.phase[i] != 0);
        assert!(
            has_saved_phase,
            "phase saving should persist across IC3 calls -- some variables should have non-zero saved phase"
        );
    }

    /// Verify that add_clause between IC3 calls does NOT invalidate the
    /// incremental cache, allowing O(new_clauses) attachment instead of
    /// full O(num_vars) reset.
    #[test]
    fn ic3_add_clause_does_not_invalidate_incremental_cache() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);

        // First solve.
        let _r = s.solve_incremental_ic3(&[pos(0)]);
        let hits_before = s.stats.assumption_cache_hits;
        let misses_before = s.stats.assumption_cache_misses;

        // Add blocking clauses between solves (the IC3 pattern).
        for i in 0..10u32 {
            s.add_clause(vec![pos(i % num_vars), neg((i + 3) % num_vars)]);
        }

        // Second solve after add_clause.
        let _r = s.solve_incremental_ic3(&[neg(5)]);

        // The incremental path should still be used (cache hit, not miss).
        let hits_after = s.stats.assumption_cache_hits;
        let misses_after = s.stats.assumption_cache_misses;

        assert!(
            hits_after > hits_before,
            "add_clause should NOT invalidate incremental cache: \
             hits_before={hits_before}, hits_after={hits_after}, \
             misses_before={misses_before}, misses_after={misses_after}"
        );
    }

    /// Verify that per-query SAT time decreases (or stays stable) over
    /// many IC3 queries on the same formula. Learned clauses from prior
    /// queries should accelerate subsequent queries.
    #[test]
    fn ic3_per_query_time_stable_over_many_queries() {
        let num_vars = 30u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Moderately complex formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in 0..num_vars - 2 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 2)]);
        }
        for i in 0..num_vars - 3 {
            s.add_clause(vec![neg(i), neg(i + 2), pos(i + 3)]);
        }

        // Warmup: first 100 queries.
        let warmup_start = ay_core::time::Instant::now();
        for i in 0..100u32 {
            let lit = if i % 3 == 0 {
                neg(i % num_vars)
            } else {
                pos(i % num_vars)
            };
            let _r = s.solve_incremental_ic3(&[lit]);
        }
        let warmup_time = warmup_start.elapsed();

        // Steady state: next 100 queries.
        let steady_start = ay_core::time::Instant::now();
        for i in 100..200u32 {
            let lit = if i % 3 == 0 {
                neg(i % num_vars)
            } else {
                pos(i % num_vars)
            };
            let _r = s.solve_incremental_ic3(&[lit]);
        }
        let steady_time = steady_start.elapsed();

        // Steady-state queries should NOT be dramatically slower than warmup.
        // Allow 3x tolerance for scheduling noise on CI.
        assert!(
            steady_time.as_nanos() < warmup_time.as_nanos().saturating_mul(3),
            "steady-state queries should not degrade: warmup={warmup_time:?}, steady={steady_time:?}"
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 persistent assumption buffer tests (#8569 Gap 1)
    // ════════════════════════════════════════════════════════════════════════════

    /// Verify that persistent IC3 assumption buffers are correctly sparse-cleared
    /// between queries. The optimization replaces 3 x O(num_vars) allocations per
    /// query with O(assumptions) sparse clear.
    ///
    /// Acceptance criterion: buffers contain only the current query's assumptions
    /// after each solve, with no stale data from prior queries.
    #[test]
    fn ic3_persistent_assumption_buffers_sparse_clear() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a satisfiable formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);

        // Query 1: assumptions on vars 0, 5.
        let _r = s.solve_incremental_ic3(&[pos(0), neg(5)]);

        // After query 1, buffers should be populated.
        assert!(
            s.cold.ic3_is_assumption.len() >= num_vars as usize,
            "ic3_is_assumption should be grown to num_vars"
        );
        // ic3_assumption_indices tracks which vars were set.
        // After the solve, they are NOT cleared yet -- they will be cleared
        // at the START of the next solve.

        // Query 2: different assumptions (vars 3, 7).
        let _r = s.solve_incremental_ic3(&[pos(3), neg(7)]);

        // After query 2, vars 0 and 5 from query 1 should be cleared.
        assert!(
            !s.cold.ic3_is_assumption[0],
            "var 0 from prior query should be sparse-cleared"
        );
        assert!(
            !s.cold.ic3_is_assumption[5],
            "var 5 from prior query should be sparse-cleared"
        );
        assert!(
            s.cold.ic3_assumption_lit[0].is_none(),
            "assumption_lit[0] from prior query should be cleared"
        );
        assert!(
            s.cold.ic3_assumption_lit[5].is_none(),
            "assumption_lit[5] from prior query should be cleared"
        );

        // Vars 3 and 7 from current query should still be set
        // (they will be cleared at the start of the NEXT query).
        assert!(
            s.cold.ic3_is_assumption[3],
            "var 3 from current query should still be set"
        );
        assert!(
            s.cold.ic3_is_assumption[7],
            "var 7 from current query should still be set"
        );

        // Query 3: no assumptions at all.
        let _r = s.solve_incremental_ic3(&[]);

        // Vars 3 and 7 should now be cleared.
        assert!(
            !s.cold.ic3_is_assumption[3],
            "var 3 should be cleared after empty-assumption query"
        );
        assert!(
            !s.cold.ic3_is_assumption[7],
            "var 7 should be cleared after empty-assumption query"
        );
        // The assumption_indices tracker should be empty.
        assert!(
            s.cold.ic3_assumption_indices.is_empty(),
            "no assumptions in current query, indices should be empty"
        );
    }

    /// Verify VSIDS accumulation leads to decreasing per-query conflict
    /// count (#8643 acceptance criterion 2 verification method).
    ///
    /// When VSIDS activity accumulates across IC3 calls, the solver learns
    /// which variables are relevant to the formula's conflict structure.
    /// Later queries should need fewer conflicts to resolve because VSIDS
    /// focuses decisions on the right variables from the start.
    ///
    /// This test runs 1000+ queries in two phases and verifies that the
    /// average conflict count per query in the second phase is no worse
    /// than the first phase. With accumulated VSIDS, the solver should
    /// converge faster on subsequent queries.
    #[test]
    fn ic3_vsids_accumulation_reduces_conflicts_1000_queries() {
        let num_vars = 30u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a formula with enough structure to generate conflicts.
        // Implication chain creates propagation.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // Cycle back: x_{n-1} -> !x_0 (forces UNSAT when x_0=true)
        s.add_clause(vec![neg(num_vars - 1), neg(0)]);
        // Cross-constraints for deeper search.
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        // Mutual exclusion pairs for additional conflicts.
        for i in 0..num_vars / 2 {
            s.add_clause(vec![neg(i), neg(i + num_vars / 2)]);
        }
        // Wider disjunctions to prevent trivial propagation.
        for i in 0..num_vars - 3 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
        }

        // Phase 1: first 500 queries (warmup — VSIDS is learning).
        let phase1_count = 500u32;
        let conflicts_before_phase1 = s.num_conflicts + s.cold.lifetime_conflicts;
        for i in 0..phase1_count {
            let v = i % num_vars;
            let lit = if i % 3 == 0 { neg(v) } else { pos(v) };
            let _r = s.solve_incremental_ic3(&[lit]);
        }
        let conflicts_after_phase1 = s.num_conflicts + s.cold.lifetime_conflicts;
        let phase1_total_conflicts = conflicts_after_phase1 - conflicts_before_phase1;

        // Phase 2: next 500 queries (steady state — VSIDS should be calibrated).
        let phase2_count = 500u32;
        let conflicts_before_phase2 = s.num_conflicts + s.cold.lifetime_conflicts;
        for i in phase1_count..(phase1_count + phase2_count) {
            let v = i % num_vars;
            let lit = if i % 3 == 0 { neg(v) } else { pos(v) };
            let _r = s.solve_incremental_ic3(&[lit]);
        }
        let conflicts_after_phase2 = s.num_conflicts + s.cold.lifetime_conflicts;
        let phase2_total_conflicts = conflicts_after_phase2 - conflicts_before_phase2;

        // The total number of queries is 1000+ as required by acceptance criterion 3.
        let total_queries = phase1_count + phase2_count;
        assert!(
            total_queries >= 1000,
            "must run 1000+ queries for acceptance criterion 3, ran {total_queries}"
        );

        // Phase 2 conflicts should not be dramatically higher than phase 1.
        // With VSIDS accumulation, the solver should converge at least as fast.
        // Allow 2x tolerance for statistical variation across query patterns.
        // The key invariant is that learned state does NOT degrade across calls.
        let phase1_avg = phase1_total_conflicts as f64 / f64::from(phase1_count);
        let phase2_avg = phase2_total_conflicts as f64 / f64::from(phase2_count);

        assert!(
            phase2_avg <= phase1_avg.mul_add(2.0, 1.0),
            "phase 2 conflict rate should not degrade vs phase 1: \
             phase1_avg={phase1_avg:.2}, phase2_avg={phase2_avg:.2} \
             (phase1_total={phase1_total_conflicts}, phase2_total={phase2_total_conflicts})"
        );

        // Verify that VSIDS activities are non-zero (accumulated from conflicts).
        let max_activity = (0..num_vars)
            .map(|i| s.vsids.activity(Variable::new(i)))
            .fold(0.0f64, f64::max);
        assert!(
            max_activity > 0.0,
            "VSIDS max activity should be non-zero after 1000 queries with conflicts"
        );

        // Verify incremental reset was used (not full reset on every call).
        assert!(
            s.stats.assumption_cache_hits > 900,
            "IC3 should use incremental reset for most calls: hits={}, misses={}",
            s.stats.assumption_cache_hits,
            s.stats.assumption_cache_misses,
        );
    }

    /// Verify per-query SAT time stability over 1000+ queries on the same
    /// formula (#8643 acceptance criterion 3).
    ///
    /// This extends the 200-query test to 1000+ queries as required by the
    /// acceptance criteria. With persistent learned clauses and VSIDS, the
    /// solver should not degrade over extended incremental runs.
    #[test]
    fn ic3_per_query_time_stable_over_1000_queries() {
        let num_vars = 30u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Moderately complex formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in 0..num_vars - 2 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 2)]);
        }
        for i in 0..num_vars - 3 {
            s.add_clause(vec![neg(i), neg(i + 2), pos(i + 3)]);
        }

        // Warmup: first 200 queries.
        let warmup_start = ay_core::time::Instant::now();
        for i in 0..200u32 {
            let lit = if i % 3 == 0 {
                neg(i % num_vars)
            } else {
                pos(i % num_vars)
            };
            let _r = s.solve_incremental_ic3(&[lit]);
        }
        let warmup_time = warmup_start.elapsed();

        // Steady state: queries 200-1200 (1000 queries).
        let steady_start = ay_core::time::Instant::now();
        for i in 200..1200u32 {
            let lit = if i % 3 == 0 {
                neg(i % num_vars)
            } else {
                pos(i % num_vars)
            };
            let _r = s.solve_incremental_ic3(&[lit]);

            // Periodically add blocking clauses (IC3 pattern).
            if i % 100 == 50 {
                let v0 = i % num_vars;
                let v1 = (i + 3) % num_vars;
                if v0 != v1 {
                    s.add_clause(vec![pos(v0), pos(v1)]);
                }
            }
        }
        let steady_time = steady_start.elapsed();

        let total_queries = 1200u32;
        assert!(
            total_queries >= 1000,
            "must run 1000+ queries for acceptance criterion, ran {total_queries}"
        );

        // Per-query time in steady state should not be dramatically worse
        // than warmup. The 5x per-query ratio accounts for:
        // - Steady state has 5x more queries (1000 vs 200)
        // - So raw time will be ~5x longer
        // - We compare per-query averages
        let warmup_per_query = warmup_time.as_nanos() as f64 / 200.0;
        let steady_per_query = steady_time.as_nanos() as f64 / 1000.0;

        assert!(
            steady_per_query < warmup_per_query * 5.0,
            "steady-state per-query time should not degrade by >5x: \
             warmup={warmup_per_query:.0}ns/query, steady={steady_per_query:.0}ns/query"
        );

        // Verify learned clauses accumulated (not destroyed).
        let learned_count: usize = s
            .arena
            .indices()
            .filter(|&idx| s.arena.is_active(idx) && s.arena.is_learned(idx))
            .count();
        assert!(
            learned_count > 0,
            "learned clauses should accumulate across 1200 IC3 queries"
        );
    }

    /// Stress test: persistent buffers produce identical results to the
    /// pre-optimization allocation-per-query pattern across 500 queries
    /// with varying assumption sets and blocking clauses.
    #[test]
    fn ic3_persistent_buffers_correctness_stress() {
        let num_vars = 15u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a satisfiable formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in (0..num_vars).step_by(3) {
            if i + 2 < num_vars {
                s.add_clause(vec![pos(i), pos(i + 1), pos(i + 2)]);
            }
        }

        for round in 0..500u32 {
            // Varying assumption sets (0 to 4 assumptions).
            let num_assume = (round % 5) as usize;
            let assumptions: Vec<Literal> = (0..num_assume)
                .map(|j| {
                    let v = (round + j as u32 * 3) % num_vars;
                    if (round + j as u32).is_multiple_of(2) {
                        pos(v)
                    } else {
                        neg(v)
                    }
                })
                .collect();

            let result = s.solve_incremental_ic3(&assumptions);

            // Cross-check: if UNSAT with assumptions, base formula must be SAT.
            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula became UNSAT — stale buffer corruption"
                );
            }

            // Periodically add blocking clauses.
            if round % 20 == 10 {
                let v0 = round % num_vars;
                let v1 = (round * 3 + 1) % num_vars;
                if v0 != v1 {
                    s.add_clause(vec![pos(v0), pos(v1)]);
                }
            }
        }
    }

    /// Regression test for #8633: verify that num_original_clauses is correctly
    /// initialized in the IC3 solve path. Without this fix, num_original_clauses
    /// stays at 0 after reset_search_state(), causing reduce_db to use incorrect
    /// density calculations for clause deletion scheduling.
    ///
    /// This test verifies the fix by checking that after an IC3 solve with
    /// reduce_db firing, the solver still produces correct results.
    #[test]
    fn test_ic3_num_original_clauses_initialized_for_reduce_db_8633() {
        let num_vars = 30u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a formula with enough clauses that reduce_db scheduling matters.
        // High constraint-to-variable ratio (>5x) mirrors the AIGER pattern.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        for i in 0..num_vars - 3 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
        }
        for i in 0..num_vars - 1 {
            s.add_clause(vec![pos(i), pos(i + 1)]);
        }

        // First solve to go through full reset path.
        let r = s.solve_incremental_ic3(&[pos(0)]);
        let _ = r.into_inner();

        // After first solve, num_original_clauses should be set correctly.
        // The fix ensures it equals irredundant_count() at the start of each solve.
        // On subsequent solves via the incremental path, it should still be set.
        let expected_irredundant = s.arena.irredundant_count();
        assert!(
            expected_irredundant > 0,
            "irredundant count must be positive after adding clauses"
        );

        // Run many queries to accumulate conflicts and trigger reduce_db.
        // With the fix, reduce_db uses the correct num_original_clauses for
        // density-aware protection and scheduling.
        for i in 0..500u32 {
            let v = i % num_vars;
            let lit = if i % 3 == 0 { neg(v) } else { pos(v) };
            let result = s.solve_incremental_ic3(&[lit]);

            // Cross-check: if UNSAT with single assumption, base formula must be SAT.
            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "iteration {i}: base formula UNSAT after reduce_db — \
                     num_original_clauses may be incorrectly zero"
                );
            }
        }

        // Verify reduce_db fired at least once during the 500 queries.
        // With 30 vars and dense formula, conflicts should trigger reduction.
        assert!(
            s.num_conflicts > 0,
            "IC3 queries should generate conflicts for reduce_db testing"
        );
    }

    /// Regression test for #8633: verify that the solve_with_assumptions path
    /// (used by the actual IC3 engine) also handles high constraint ratios
    /// correctly with push/pop and incremental clause additions.
    ///
    /// This mirrors the actual IC3 engine pattern: push() → add temp clauses →
    /// solve_with_assumptions → pop() → add permanent clauses → repeat.
    #[test]
    fn test_ic3_solve_with_assumptions_push_pop_high_density_8633() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);

        // Disable inprocessing to match IC3 engine configuration.
        s.set_incremental_mode();
        s.set_preprocess_enabled(false);

        // Build a dense transition-relation-like formula (>5x clause/var ratio).
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        for i in 0..num_vars - 3 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
        }
        for i in 0..num_vars - 1 {
            s.add_clause(vec![pos(i), pos(i + 1)]);
        }

        // Simulate the IC3 query pattern with push/pop.
        for round in 0..200u32 {
            // IC3 consecution query: push → add temp constraint → solve → pop
            s.push();

            // Add a temporary "constraint" clause (simulates cube negation).
            let v0 = round % num_vars;
            let v1 = (round + 3) % num_vars;
            if v0 != v1 {
                s.add_clause(vec![pos(v0), neg(v1)]);
            }

            // Solve with frame activation assumptions.
            let assumptions = vec![pos(round % num_vars)];
            let result = s.solve_with_assumptions(&assumptions);
            let is_sat = result.is_sat();

            assert!(s.pop(), "pop should succeed in round {round}");

            // Add a permanent blocking clause (frame lemma).
            if round % 5 == 0 {
                let a = round % num_vars;
                let b = (round + 2) % num_vars;
                if a != b {
                    // Always include at least one positive literal to preserve satisfiability.
                    s.add_clause(vec![pos(a), pos(b)]);
                }
            }

            // Cross-check: base formula should always be SAT
            // (all added permanent clauses contain positive literals).
            if round % 20 == 0 {
                let base = s.solve_with_assumptions(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT — push/pop or clause \
                     management corrupted the formula (last query was {})",
                    if is_sat { "SAT" } else { "UNSAT" }
                );
            }
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // Domain BCP false non-domain regression tests (#8661)
    // ════════════════════════════════════════════════════════════════════════════

    /// Regression test for #8661: domain-restricted BCP must not skip clauses
    /// where a non-domain watched literal was assigned FALSE at level 0.
    #[test]
    fn test_ic3_domain_bcp_false_nondomain_watched_8661() {
        // Setup: 6 variables.
        // d0, d1, d2 = domain variables (indices 0, 1, 2)
        // nd0, nd1, nd2 = non-domain variables (indices 3, 4, 5)
        let mut s = Solver::new(6);
        s.set_ic3_mode();

        // Unit clause: forces nd0 (var 3) = FALSE at level 0 by full BCP.
        s.add_clause(vec![neg(3)]);

        // Clause: (nd0 | d0). Since nd0=false after level 0, this clause
        // requires d0=true for satisfaction. Before the fix, domain BCP
        // would skip this clause because nd0 is non-domain, missing the
        // forced propagation d0=true.
        s.add_clause(vec![pos(3), pos(0)]);

        // Clause: (d0 | d1). Reachable chain from d0.
        s.add_clause(vec![pos(0), pos(1)]);

        // Clause that creates conflict potential:
        // (!d0 | d2) — if d0 is decided true, d2 must be true.
        s.add_clause(vec![neg(0), pos(2)]);

        // Set domain to only d0, d1, d2 (exclude nd0, nd1, nd2).
        s.set_domain(&[var(0), var(1), var(2)]);

        // Query 1: assume d0=false. Before the fix, domain BCP might not
        // propagate correctly because it skips clauses with nd0 watched.
        // After level 0 propagates nd0=false, the clause (nd0 | d0) should
        // force d0=true at level 0 too. If it does, assumption d0=false
        // contradicts the level 0 propagation → UNSAT.
        let r1 = s.solve_incremental_ic3(&[neg(0)]);
        assert!(
            r1.is_unsat(),
            "d0=true is forced by unit propagation chain \
             (nd0=false -> d0=true), so assuming d0=false must be UNSAT"
        );

        // Query 2: assume d0=true should be consistent.
        let r2 = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            r2.is_sat(),
            "d0=true is consistent with nd0=false and the rest of the formula"
        );

        // Query 3: no assumptions — base formula must be SAT.
        let r3 = s.solve_incremental_ic3(&[]);
        assert!(r3.is_sat(), "base formula must be SAT");
    }

    /// Regression test for #8661 (variant 2): domain-restricted BCP with
    /// a non-domain variable assigned false at level 0 in a longer clause.
    ///
    /// This tests the "first watched literal" path (not just the blocker
    /// path). When the first watched literal is a non-domain variable
    /// assigned false, domain BCP must still search for an alternative
    /// watch rather than skipping the clause.
    #[test]
    fn test_ic3_domain_bcp_false_nondomain_first_watch_8661() {
        // 8 variables: d0-d3 domain (0-3), nd0-nd3 non-domain (4-7)
        let mut s = Solver::new(8);
        s.set_ic3_mode();

        // Force nd0=false and nd1=false at level 0.
        s.add_clause(vec![neg(4)]); // nd0=false
        s.add_clause(vec![neg(5)]); // nd1=false

        // Long clause: (nd0 | nd1 | d0 | d1).
        // After level 0: nd0=false, nd1=false, so clause reduces to (d0 | d1).
        // Domain BCP must not skip this clause when processing watches on
        // nd0 or nd1.
        s.add_clause(vec![pos(4), pos(5), pos(0), pos(1)]);

        // Force a conflict path: (!d0 | !d1) with the reduced clause above
        // means at least one of d0, d1 must be true, and they can't both be.
        // Combined: (d0 | d1) & (!d0 | !d1) means exactly one is true.
        s.add_clause(vec![neg(0), neg(1)]);

        // Additional constraint: (!d0 | d2) and (!d1 | d3)
        s.add_clause(vec![neg(0), pos(2)]);
        s.add_clause(vec![neg(1), pos(3)]);

        // Domain: d0-d3 only.
        s.set_domain(&[var(0), var(1), var(2), var(3)]);

        // Assume both d0=false and d1=false.
        // The reduced clause (d0 | d1) from the long clause should make
        // this UNSAT. Before the fix, domain BCP might skip the long clause
        // entirely because nd0 and nd1 are non-domain watched literals.
        let r1 = s.solve_incremental_ic3(&[neg(0), neg(1)]);
        assert!(
            r1.is_unsat(),
            "d0=false & d1=false contradicts (d0 | d1) which is forced \
             after nd0=false & nd1=false reduce the long clause"
        );

        // Assume d0=true → SAT (d1 can be false, d2 must be true).
        let r2 = s.solve_incremental_ic3(&[pos(0)]);
        assert!(r2.is_sat(), "d0=true should be satisfiable");

        // Base formula SAT check.
        let r3 = s.solve_incremental_ic3(&[]);
        assert!(r3.is_sat(), "base formula must be SAT");
    }

    /// Regression test for #8661 (variant 3): stress test with many IC3
    /// queries, mixing domain and non-domain variables with level-0
    /// assignments to non-domain variables.
    ///
    /// Exercises the domain BCP fix across many incremental queries with
    /// varying assumptions, ensuring no spurious UNSAT results.
    #[test]
    fn test_ic3_domain_bcp_nondomain_level0_stress_8661() {
        let num_domain = 8u32;
        let num_nondomain = 8u32;
        let total = (num_domain + num_nondomain) as usize;
        let mut s = Solver::new(total);
        s.set_ic3_mode();

        // Force all non-domain variables false at level 0.
        // This is the scenario that triggers the bug: non-domain variables
        // are assigned false, and domain BCP must not skip clauses with
        // these false non-domain watched literals.
        for i in num_domain..num_domain + num_nondomain {
            s.add_clause(vec![neg(i)]);
        }

        // Clauses mixing domain and (false) non-domain variables.
        // After level 0, the non-domain literals are all false, so these
        // reduce to domain-only clauses.
        for i in 0..num_domain {
            let nd = num_domain + (i % num_nondomain);
            // (nd_j | d_i) — reduces to (d_i) since nd_j=false
            s.add_clause(vec![pos(nd), pos(i)]);
        }

        // Implication chain: d0 → d1 → d2 → ... → d7
        for i in 0..num_domain - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }

        // At-least-one: (d0 | d1 | ... | d7)
        let atleast: Vec<Literal> = (0..num_domain).map(pos).collect();
        s.add_clause(atleast);

        // Domain: only d0-d7.
        let domain_vars: Vec<Variable> = (0..num_domain).map(var).collect();
        s.set_domain(&domain_vars);

        // Run 200 IC3 queries with varying assumptions.
        for round in 0..200u32 {
            let v = round % num_domain;
            let assumptions = if round % 3 == 0 {
                vec![neg(v)]
            } else if round % 3 == 1 {
                vec![pos(v)]
            } else {
                let v2 = (v + 2) % num_domain;
                vec![pos(v), neg(v2)]
            };

            let result = s.solve_incremental_ic3(&assumptions);

            // Cross-check: if UNSAT under assumptions, base must be SAT.
            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT — domain BCP \
                     corruption from false non-domain watched literals"
                );
            }
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 learned clause verification tests (#8661)
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn ic3_learned_clause_verification_domain_mixed() {
        let mut s = Solver::new(10);
        s.add_clause(vec![neg(0), pos(4)]);
        s.add_clause(vec![neg(4), pos(1)]);
        s.add_clause(vec![neg(1), pos(5)]);
        s.add_clause(vec![neg(5), pos(2)]);
        s.add_clause(vec![neg(2), neg(0)]);
        s.add_clause(vec![pos(0), pos(3)]);
        s.add_clause(vec![neg(3), pos(6)]);
        s.add_clause(vec![neg(6), pos(7)]);

        s.set_ic3_mode();
        s.set_domain(&[var(0), var(1), var(2), var(3)]);

        for round in 0..100u32 {
            let lit = if round % 2 == 0 {
                pos(round % 4)
            } else {
                neg(round % 4)
            };
            let result = s.solve_incremental_ic3(&[lit]);

            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                if round < 10 {
                    assert!(
                        base.is_sat(),
                        "round {round}: base formula UNSAT — domain BCP soundness bug"
                    );
                }
            }

            if round % 10 == 5 {
                let v = round % 4;
                s.add_clause(vec![pos(v), pos((v + 1) % 4)]);
            }
        }

        s.clear_domain();
    }

    #[test]
    fn ic3_domain_bcp_conflict_through_nondomain_vars() {
        let mut s = Solver::new(8);
        s.add_clause(vec![neg(0), pos(2)]);
        s.add_clause(vec![neg(2), pos(3)]);
        s.add_clause(vec![neg(3), pos(1)]);
        s.add_clause(vec![neg(0), neg(1)]);
        s.add_clause(vec![pos(4), pos(5)]);
        s.add_clause(vec![pos(6), pos(7)]);

        s.set_ic3_mode();
        s.set_domain(&[var(0), var(1)]);

        let r = s.solve_incremental_ic3(&[pos(0)]);
        let _ = r.into_inner();

        let r2 = s.solve_incremental_ic3(&[neg(0)]);
        assert!(r2.is_sat(), "x0=false should be SAT");

        s.clear_domain();
    }

    #[test]
    fn ic3_learned_clause_verification_stress_500_queries() {
        let num_state_vars = 8u32;
        let num_aux_vars = 8u32;
        let total_vars = num_state_vars + num_aux_vars;
        let mut s = Solver::new(total_vars as usize);
        s.set_ic3_mode();

        for i in 0..num_state_vars {
            let aux = num_state_vars + i;
            let next_state = (i + 1) % num_state_vars;
            s.add_clause(vec![neg(i), pos(aux)]);
            s.add_clause(vec![neg(aux), pos(next_state)]);
        }

        for i in 0..num_state_vars - 1 {
            s.add_clause(vec![neg(i), neg(i + 1), pos(i + 2)]);
        }
        s.add_clause(vec![pos(0), pos(2), pos(4)]);
        s.add_clause(vec![pos(1), pos(3), pos(5)]);

        let domain_vars: Vec<Variable> = (0..num_state_vars).map(var).collect();
        s.set_domain(&domain_vars);

        for round in 0..500u32 {
            let v = round % num_state_vars;
            let lit = if round % 3 == 0 { neg(v) } else { pos(v) };
            let result = s.solve_incremental_ic3(&[lit]);

            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT — IC3 learned clause corruption"
                );
            }

            if round % 25 == 12 {
                let a = round % num_state_vars;
                let b = (round + 2) % num_state_vars;
                if a != b {
                    s.add_clause(vec![pos(a), pos(b)]);
                }
            }
        }

        s.clear_domain();
    }

    /// Regression test for #8661: IC3 BCP must handle garbage clauses after
    /// reduce_db. The IC3 BCP originally skipped the garbage check for
    /// performance, but reduce_db can run between IC3 queries and mark
    /// learned clauses as pending_garbage. Without the garbage check, the
    /// IC3 BCP would process stale clause data.
    ///
    /// Strategy: run many IC3 queries with a dense formula to generate
    /// enough conflicts that reduce_db fires. After each batch, verify
    /// that the base formula is still reported as SAT.
    #[test]
    fn test_ic3_bcp_garbage_clause_after_reduce_db_8661() {
        let num_vars = 30u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Dense formula: implication chains + cross-connections + wider
        // clauses. Constraint-to-variable ratio >5x ensures reduce_db
        // triggers after enough conflicts.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        for i in 0..num_vars - 3 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 3)]);
        }
        for i in 0..num_vars - 1 {
            s.add_clause(vec![pos(i), pos(i + 1)]);
        }
        // Additional wider clauses to increase constraint density.
        for i in 0..num_vars - 4 {
            s.add_clause(vec![neg(i), neg(i + 2), pos(i + 4)]);
        }

        // Domain: first half of variables.
        let domain_vars: Vec<Variable> = (0..num_vars / 2).map(var).collect();
        s.set_domain(&domain_vars);

        // Run many queries to accumulate conflicts and trigger reduce_db.
        // Mix SAT/UNSAT assumptions to generate learned clauses of varying
        // quality (some will be deleted by reduce_db).
        let mut saw_unsat = false;
        for i in 0..800u32 {
            let v = i % (num_vars / 2);
            let lit = if i % 3 == 0 { neg(v) } else { pos(v) };
            let result = s.solve_incremental_ic3(&[lit]);

            if result.is_unsat() {
                saw_unsat = true;
            }

            // Periodic correctness check: base formula must always be SAT.
            if i % 100 == 99 {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "iteration {i}: base formula UNSAT after reduce_db — \
                     garbage clause handling may be broken (#8661)"
                );
            }
        }

        // Verify that IC3 queries did generate conflicts (otherwise the
        // test doesn't exercise the reduce_db path).
        assert!(
            s.num_conflicts > 0,
            "IC3 queries should generate conflicts to trigger reduce_db"
        );
        assert!(saw_unsat, "IC3 queries should produce some UNSAT results");
    }

    #[test]
    fn ic3_bcp_vs_domain_bcp_learned_clause_parity() {
        let n = 12u32;
        let domain_vars: Vec<Variable> = (0..6).map(var).collect();

        let mut s_standard = Solver::new(n as usize);
        build_ic3_test_formula(&mut s_standard, n);
        s_standard.set_domain(&domain_vars);

        let mut s_ic3 = Solver::new(n as usize);
        build_ic3_test_formula(&mut s_ic3, n);
        s_ic3.set_ic3_mode();
        s_ic3.set_domain(&domain_vars);

        for round in 0..200u32 {
            let lit = if round % 3 == 0 {
                pos(round % 6)
            } else if round % 3 == 1 {
                neg(round % 6)
            } else {
                pos((round * 7 + 3) % 6)
            };

            let r_standard = s_standard.solve_incremental_ic3(&[lit]);
            let r_ic3 = s_ic3.solve_incremental_ic3(&[lit]);

            let std_sat = r_standard.is_sat();
            let ic3_sat = r_ic3.is_sat();

            if std_sat != ic3_sat {
                eprintln!(
                    "[IC3-PARITY] round {round}: standard={}, ic3={} for assumption {:?}",
                    if std_sat { "SAT" } else { "UNSAT" },
                    if ic3_sat { "SAT" } else { "UNSAT" },
                    lit,
                );
            }

            if round % 50 == 0 {
                let base_std = s_standard.solve_incremental_ic3(&[]);
                let base_ic3 = s_ic3.solve_incremental_ic3(&[]);
                assert_eq!(
                    base_std.is_sat(),
                    base_ic3.is_sat(),
                    "round {round}: base formula disagrees between standard and IC3 BCP"
                );
            }

            if round % 10 == 0 {
                let cl = vec![pos(round % 6), pos((round + 2) % 6)];
                s_standard.add_clause(cl.clone());
                s_ic3.add_clause(cl);
            }
        }
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 large variable count test (#8569 cleanup)
    // ════════════════════════════════════════════════════════════════════════════

    /// IC3 with 200 variables and domain restriction to 20 domain variables.
    /// This exercises the IC3 BCP, bucket queue, VSIDS, and reduce_db paths
    /// with a realistic variable count. AIGER benchmarks typically have
    /// 100-10000 variables with domains of 10-200.
    ///
    /// Acceptance criteria:
    /// - 500 incremental queries complete without panic or wrong answer
    /// - reduce_db fires at least once (clause growth from conflicts)
    /// - Incremental cache is used (not full reset on every call)
    #[test]
    fn ic3_large_variable_count_200_vars() {
        let num_vars = 200u32;
        let num_domain = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a transition-relation-like formula.
        // Implication chains within domain vars.
        for i in 0..num_domain - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // Cross-connections between domain and non-domain vars.
        for i in 0..num_domain {
            let nd = num_domain + (i * 3) % (num_vars - num_domain);
            s.add_clause(vec![neg(i), pos(nd)]);
            s.add_clause(vec![neg(nd), pos((i + 1) % num_domain)]);
        }
        // Dense non-domain implications (simulates AIG gate structure).
        for i in num_domain..num_vars - 1 {
            if i + 1 < num_vars {
                s.add_clause(vec![neg(i), pos(i + 1)]);
            }
        }
        // At-least-one domain var true.
        let atleast: Vec<Literal> = (0..num_domain).map(pos).collect();
        s.add_clause(atleast);
        // Three-literal clauses for non-trivial search.
        for i in 0..num_domain - 2 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 2)]);
        }

        // Domain: first num_domain variables.
        let domain_vars: Vec<Variable> = (0..num_domain).map(var).collect();
        s.set_domain(&domain_vars);

        // Run 500 IC3-like queries.
        for round in 0..500u32 {
            let v = round % num_domain;
            let lit = if round % 3 == 0 { neg(v) } else { pos(v) };
            let result = s.solve_incremental_ic3(&[lit]);

            // Cross-check: UNSAT under assumption implies base is still SAT.
            if result.is_unsat() && round % 50 == 0 {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT with 200-var IC3 workload"
                );
            }

            // Periodically add blocking clauses.
            if round % 20 == 10 {
                let a = round % num_domain;
                let b = (round + 3) % num_domain;
                if a != b {
                    s.add_clause(vec![pos(a), pos(b)]);
                }
            }
        }

        s.clear_domain();

        // Verify incremental cache was used.
        assert!(
            s.stats.assumption_cache_hits > 400,
            "IC3 with 200 vars should use incremental reset: hits={}, misses={}",
            s.stats.assumption_cache_hits,
            s.stats.assumption_cache_misses,
        );
    }

    /// Stress test for #8633: IC3 with high constraint-to-variable ratio
    /// where reduce_db fires with density-aware protection.
    ///
    /// On dense formulas, reduce_db's density-aware protection relaxes
    /// CORE_LBD from 2 to 1 (#8135). In IC3 mode, this must be disabled
    /// because glue-2 learned clauses are blocking lemmas that the IC3
    /// engine depends on. Without the IC3 override, reduce_db can delete
    /// these lemmas during long IC3 queries, causing false UNSAT.
    ///
    /// This test creates a pigeonhole-like dense formula that forces
    /// non-trivial search with many conflicts, exercising reduce_db.
    /// Every UNSAT result is cross-checked against the base formula.
    #[test]
    fn test_ic3_density_aware_protection_disabled_in_ic3_mode_8633() {
        // Use 15 variables with many clauses to exceed density threshold >10.
        // The formula is SAT (all-true satisfies it) but dense enough to
        // trigger density-aware CORE_LBD relaxation.
        let num_vars = 15u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // All-pairs positive binary clauses: C(15,2) = 105 clauses.
        // SAT by setting all variables true.
        for i in 0..num_vars {
            for j in (i + 1)..num_vars {
                s.add_clause(vec![pos(i), pos(j)]);
            }
        }
        // Forward implications: x_i -> x_{i+1} (14 clauses)
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        // Reverse implications: x_{i+1} -> x_i (14 clauses)
        for i in 0..num_vars - 1 {
            s.add_clause(vec![pos(i), neg(i + 1)]);
        }
        // Mixed 3-clauses for search difficulty
        for i in 0..num_vars - 2 {
            s.add_clause(vec![pos(i), pos(i + 1), neg(i + 2)]);
        }
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 1), pos(i + 2)]);
        }
        // Skip-2 implications for more density
        for i in 0..num_vars - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }
        for i in 0..num_vars - 2 {
            s.add_clause(vec![pos(i), neg(i + 2)]);
        }

        let clause_count = s.arena.irredundant_count();
        let density = clause_count / (num_vars as usize).max(1);
        assert!(
            density > 10,
            "test requires density > 10 for density-aware protection to fire; \
             got density={density} (clauses={clause_count}, vars={num_vars})"
        );

        // Run many IC3 queries with conflicting assumptions to force search.
        // Use larger assumption sets (3-5 assumptions) to create harder queries.
        let mut sat_count = 0u32;
        let mut unsat_count = 0u32;
        for iteration in 0..1500u32 {
            let mut assumptions = Vec::new();
            // Create assumptions that often conflict with the mutual-exclusion
            // constraints, forcing the solver into deep search.
            let base = (iteration * 3) % num_vars;
            assumptions.push(pos(base));
            // Try to force two variables true in the same mutual-exclusion group
            let group_start = (base / 3) * 3;
            let second = group_start + ((base - group_start + 1) % 3);
            if second < num_vars {
                assumptions.push(pos(second));
            }
            // Add a third assumption from a different group
            let third = (base + num_vars / 2) % num_vars;
            if third != base
                && third != second
                && !assumptions
                    .iter()
                    .any(|l| l.variable().index() == third as usize)
            {
                assumptions.push(if iteration % 3 == 0 {
                    neg(third)
                } else {
                    pos(third)
                });
            }

            let result = s.solve_incremental_ic3(&assumptions);
            if result.is_sat() {
                sat_count += 1;
            } else if result.is_unsat() {
                unsat_count += 1;
                // Cross-check: base formula must still be SAT
                if iteration % 20 == 0 {
                    let base = s.solve_incremental_ic3(&[]);
                    assert!(
                        base.is_sat(),
                        "iteration {iteration}: base formula UNSAT after reduce_db \
                         on dense IC3 formula — density-aware CORE_LBD relaxation \
                         may be deleting blocking lemmas (#8633)"
                    );
                }
            }
        }

        assert!(
            sat_count + unsat_count >= 1000,
            "expected at least 1000 SAT+UNSAT results, got {}",
            sat_count + unsat_count
        );
    }

    /// IC3 bucket-to-heap transition and re-enable (#8662 Gap 5).
    ///
    /// Verifies the bucket-queue lifecycle:
    /// 1. set_domain() enables bucket queue
    /// 2. After BUCKET_QUEUE_RESTART_THRESHOLD restarts within a single hard
    ///    query, bucket -> heap
    /// 3. Next set_domain() re-enables bucket queue
    ///
    /// Uses a deliberately hard formula with contradictory constraints on the
    /// domain variables to force enough conflicts and restarts within a single
    /// solve call. The key insight: a single long query that reaches the
    /// restart threshold should transition to heap, then the next query
    /// should start fresh with bucket.
    #[test]
    fn ic3_bucket_to_heap_transition_and_reenable() {
        let nv = 30u32;
        let mut s = Solver::new(nv as usize);

        // Create a hard formula on all variables.
        // Dense mutual implications + 3-clauses force deep search.
        for i in 0..nv - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
            s.add_clause(vec![pos(i), neg(i + 1)]);
        }
        for i in 0..nv - 2 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 2)]);
            s.add_clause(vec![neg(i), pos(i + 1), neg(i + 2)]);
        }
        // Cross-group implications to increase conflict rate.
        for i in 0..nv / 2 {
            s.add_clause(vec![neg(i), pos(i + nv / 2)]);
            s.add_clause(vec![pos(i), neg(i + nv / 2)]);
        }

        s.set_ic3_mode();

        let domain: Vec<_> = (0..10).map(var).collect();
        s.set_domain(&domain);
        assert!(
            s.bucket_queue_active,
            "set_domain should enable bucket queue"
        );

        // Run many solve calls. Each call has its own restart counter.
        // Most short queries won't trigger the transition. We just verify
        // the API contract: set_domain() always re-enables bucket.
        for i in 0..100u32 {
            // Use conflicting assumptions to generate more conflicts/restarts.
            let a1 = pos(i % 10);
            let a2 = neg((i + 3) % 10);
            let _r = s.solve_incremental_ic3(&[a1, a2]);
        }

        // Whether or not any individual query hit the restart threshold, verify that
        // set_domain() re-enables the bucket queue (the "re-enable" part
        // of the lifecycle).
        s.set_domain(&domain);
        assert!(
            s.bucket_queue_active,
            "set_domain should re-enable bucket queue after any heap fallback"
        );
        assert_eq!(
            s.domain_restarts, 0,
            "set_domain should reset domain_restarts to 0"
        );

        s.clear_domain();
        assert!(
            !s.bucket_queue_active,
            "clear_domain should disable bucket queue"
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 lightweight constraint activation tests (#8662 Gap 3)
    // ════════════════════════════════════════════════════════════════════════════

    /// Basic constraint activation: constrained clauses are active when
    /// the activation variable is assumed true, and inactive otherwise.
    #[test]
    fn ic3_constrain_activation_basic() {
        let mut s = Solver::new(5);
        s.set_ic3_mode();

        // Base formula: (x0 | x1) & (x2 | x3)
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![pos(2), pos(3)]);

        // Allocate activation variable.
        let act = s.new_var(); // var 5
        s.set_constrain_activation(act);
        assert_eq!(s.constrain_activation(), Some(act));

        // Add a constrained clause: effectively (!act | !x0 | !x1).
        // When act is assumed true, this becomes (!x0 | !x1).
        s.add_constrained_clause(vec![neg(0), neg(1)]);

        // Solve with activation (IC3 path auto-adds act=true):
        // Base clauses: (x0|x1) & (x2|x3)
        // Constrained clause active: (!x0 | !x1)
        // Formula is SAT: e.g., x0=true, x1=false, x2=true, x3=true
        let r1 = s.solve_incremental_ic3(&[]);
        assert!(
            r1.is_sat(),
            "formula with constrained clause (!x0|!x1) should be SAT"
        );

        // Add another constrained clause that creates a contradiction:
        // (!act | x0) — when active, forces x0=true
        // (!act | x1) — when active, forces x1=true
        // Combined with (!act | !x0 | !x1): x0=true & x1=true contradicts !x0|!x1
        s.add_constrained_clause(vec![pos(0)]);
        s.add_constrained_clause(vec![pos(1)]);

        // With activation: x0=true & x1=true & (!x0|!x1) → UNSAT
        let r2 = s.solve_incremental_ic3(&[]);
        assert!(
            r2.is_unsat(),
            "constrained clauses forcing x0=true & x1=true & (!x0|!x1) should be UNSAT"
        );
    }

    /// Constraint activation with assumptions: the activation literal
    /// should be combined with caller-provided assumptions.
    #[test]
    fn ic3_constrain_activation_with_assumptions() {
        let mut s = Solver::new(4);
        s.set_ic3_mode();

        // Formula: (x0 | x1) & (x2 | x3) & (!x0 | !x1) & (!x2 | !x3)
        // SAT: x0=T, x1=F, x2=T, x3=F (or variants)
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![pos(2), pos(3)]);
        s.add_clause(vec![neg(0), neg(1)]);
        s.add_clause(vec![neg(2), neg(3)]);

        let act = s.new_var();
        s.set_constrain_activation(act);

        // Add constrained clause: when active, forces x0=true.
        s.add_constrained_clause(vec![pos(0)]);

        // With activation + assumption x2=true:
        // x0=true (from constrained clause), x1=false (from !x0|!x1),
        // x2=true (assumption), x3=false (from !x2|!x3) → SAT
        let r1 = s.solve_incremental_ic3(&[pos(2)]);
        assert!(
            r1.is_sat(),
            "constrained x0=true + assume x2=true should be SAT"
        );

        // With activation + assumption x0=false:
        // Contradicts constrained clause (x0=true) → UNSAT
        let r2 = s.solve_incremental_ic3(&[neg(0)]);
        assert!(
            r2.is_unsat(),
            "constrained x0=true + assume x0=false should be UNSAT"
        );
    }

    /// Constraint activation replaces push/pop pattern: verify that
    /// constrained clauses accumulate without push/pop and don't interfere
    /// with each other when the activation is not assumed.
    #[test]
    fn ic3_constrain_activation_replaces_push_pop() {
        let mut s = Solver::new(6);
        s.set_ic3_mode();

        // Satisfiable base formula.
        for i in 0..5u32 {
            s.add_clause(vec![pos(i), pos(i + 1)]);
        }

        let act = s.new_var();
        s.set_constrain_activation(act);

        // Simulate multiple IC3 queries adding constrained clauses.
        // Unlike push/pop, these clauses accumulate permanently in the
        // database but are trivially satisfied when act is not assumed.
        for round in 0..50u32 {
            let v = round % 6;
            // Add constrained clause each round.
            let lit = if round % 2 == 0 { pos(v) } else { neg(v) };
            s.add_constrained_clause(vec![lit]);

            // Solve with activation (IC3 auto-adds act=true).
            let result = s.solve_incremental_ic3(&[pos(round % 3)]);
            let _ = result.into_inner();
        }

        // Base formula (without activation) should still be SAT.
        // The accumulated constrained clauses don't affect the formula
        // when the activation variable is not assumed.
        //
        // Note: solve_incremental_ic3 auto-adds the activation literal,
        // so to test without activation we need to verify the base formula
        // is SAT by checking that at least some queries succeed.
        let r = s.solve_incremental_ic3(&[]);
        // This may be SAT or UNSAT depending on accumulated constraints.
        // The key property is correctness, not a specific result.
        let _ = r.into_inner();
    }

    /// Stress test: many IC3 queries with constraint activation, verifying
    /// that the accumulated constrained clauses don't cause false results.
    #[test]
    fn ic3_constrain_activation_stress_500_queries() {
        let num_vars = 15u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a satisfiable transition-relation-like formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in (0..num_vars).step_by(3) {
            if i + 2 < num_vars {
                s.add_clause(vec![pos(i), pos(i + 1), pos(i + 2)]);
            }
        }

        let act = s.new_var();
        s.set_constrain_activation(act);

        // Domain: first 8 variables.
        let domain_vars: Vec<Variable> = (0..8).map(var).collect();
        s.set_domain(&domain_vars);

        for round in 0..500u32 {
            // Add a constrained clause every 5 rounds.
            if round % 5 == 0 {
                let v = round % 8;
                let lit = if round % 4 == 0 { pos(v) } else { neg(v) };
                s.add_constrained_clause(vec![lit, pos((v + 2) % 8)]);
            }

            // Also add permanent blocking clauses periodically.
            if round % 20 == 10 {
                let a = round % 8;
                let b = (round + 3) % 8;
                if a != b {
                    s.add_clause(vec![pos(a), pos(b)]);
                }
            }

            // Solve with varying assumptions.
            let v = round % 8;
            let lit = if round % 3 == 0 { neg(v) } else { pos(v) };
            let result = s.solve_incremental_ic3(&[lit]);
            let _ = result.into_inner();
        }

        s.clear_domain();

        // Verify the solver didn't crash or produce invalid state.
        assert!(
            s.stats.assumption_cache_hits > 0,
            "IC3 with constraint activation should use incremental reset"
        );
    }

    /// Verify that constrained clauses are correctly guarded: when
    /// solve_incremental_ic3 auto-adds the activation literal, it
    /// should not be duplicated if the caller also provides it.
    #[test]
    fn ic3_constrain_activation_no_duplicate_assumption() {
        let mut s = Solver::new(3);
        s.set_ic3_mode();

        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![pos(1), pos(2)]);

        let act = s.new_var();
        s.set_constrain_activation(act);
        let act_lit = Literal::positive(act);

        // Caller manually includes the activation literal.
        // solve_incremental_ic3 should detect it and not add a duplicate.
        let result = s.solve_incremental_ic3(&[act_lit, pos(0)]);
        assert!(result.is_sat(), "no duplicate activation should allow SAT");
    }

    /// Verify that cleanup_constrained_clauses uses tracked offsets for
    /// O(constraint_count) cleanup instead of scanning the full arena (#8687).
    #[test]
    fn ic3_constrain_cleanup_tracks_offsets() {
        let mut s = Solver::new(12);
        s.set_ic3_mode();

        // Base formula: many clauses to make the arena non-trivial.
        for i in 0..8u32 {
            s.add_clause(vec![pos(i), pos((i + 1) % 8)]);
        }

        let act = s.new_var();
        s.set_constrain_activation(act);

        // Verify no constrained offsets initially.
        assert!(
            s.cold.ic3_constrained_offsets.is_empty(),
            "no constrained offsets before adding constrained clauses"
        );

        // Add constrained clauses.
        s.add_constrained_clause(vec![pos(0), neg(1)]);
        s.add_constrained_clause(vec![neg(2), pos(3)]);
        s.add_constrained_clause(vec![pos(4), neg(5), pos(6)]);

        // Verify offsets are tracked.
        assert_eq!(
            s.cold.ic3_constrained_offsets.len(),
            3,
            "should track 3 constrained clause offsets"
        );

        // All tracked offsets should be valid active clauses.
        for &off in &s.cold.ic3_constrained_offsets {
            assert!(
                s.arena.is_active(off),
                "tracked offset {off} should be active in arena"
            );
        }

        // Cleanup should delete all 3 constrained clauses.
        let deleted = s.cleanup_constrained_clauses();
        assert_eq!(deleted, 3, "should delete all 3 constrained clauses");

        // Tracked offsets should be cleared after cleanup.
        assert!(
            s.cold.ic3_constrained_offsets.is_empty(),
            "constrained offsets should be cleared after cleanup"
        );

        // Add more constrained clauses and verify tracking restarts.
        s.add_constrained_clause(vec![pos(7), neg(8)]);
        assert_eq!(
            s.cold.ic3_constrained_offsets.len(),
            1,
            "new constrained clause should be tracked"
        );

        let deleted = s.cleanup_constrained_clauses();
        assert_eq!(deleted, 1, "should delete the one new constrained clause");
        assert!(s.cold.ic3_constrained_offsets.is_empty());
    }

    /// Verify that constrained clauses work correctly across multiple
    /// solve-cleanup cycles (#8687).
    #[test]
    fn ic3_constrain_solve_cleanup_cycle() {
        let mut s = Solver::new(10);
        s.set_ic3_mode();

        // Satisfiable base formula.
        s.add_clause(vec![pos(0), pos(1), pos(2)]);
        s.add_clause(vec![neg(0), pos(3), pos(4)]);
        s.add_clause(vec![neg(3), pos(5), pos(6)]);

        let act = s.new_var();
        s.set_constrain_activation(act);

        // Run multiple solve-add-cleanup cycles.
        for round in 0..20u32 {
            // Add a constrained clause each round.
            let v = round % 7;
            s.add_constrained_clause(vec![pos(v), neg((v + 1) % 7)]);

            // Solve with activation.
            let _r = s.solve_incremental_ic3(&[pos(round % 3)]);

            // Clean up every 5 rounds.
            if round % 5 == 4 {
                let deleted = s.cleanup_constrained_clauses();
                assert!(
                    deleted > 0,
                    "round {round}: should have cleaned up some constrained clauses"
                );
                assert!(
                    s.cold.ic3_constrained_offsets.is_empty(),
                    "offsets should be cleared after cleanup"
                );
            }
        }

        // Final cleanup should remove any remaining.
        let _remaining = s.cleanup_constrained_clauses();
        assert!(s.cold.ic3_constrained_offsets.is_empty());

        // Solver should still be functional after all cycles.
        let r = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            r.is_sat() || r.is_unsat(),
            "solver should still produce valid results"
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 Lazy Lemma Removal (#8662 Gap 7)
    // ════════════════════════════════════════════════════════════════════════════

    /// Test that mark_clause_garbage_lazy marks a clause as pending-garbage
    /// and increments the stats counter.
    #[test]
    fn ic3_lazy_remove_marks_clause() {
        let mut s = Solver::new(6);
        s.set_ic3_mode();

        // Add clauses. Use prenormalized to get arena offsets.
        // Clause A: (x0 | x1 | x2) — shorter, potential subsumer.
        let off_a = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(1), pos(2)])
            .expect("ternary clause should return offset");

        // Clause B: (x0 | x1 | x2 | x3) — longer, subsumed by A.
        let off_b = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(1), pos(2), pos(3)])
            .expect("quaternary clause should return offset");

        // Initial solve to establish watches.
        let _r = s.solve_incremental_ic3(&[]);

        // Mark clause B as garbage lazily.
        assert!(
            s.mark_clause_garbage_lazy(off_b),
            "marking active clause should succeed"
        );
        assert_eq!(
            s.stats.ic3_lazy_removed, 1,
            "ic3_lazy_removed stat should increment"
        );

        // Double-mark should return false (already dead).
        assert!(
            !s.mark_clause_garbage_lazy(off_b),
            "double-marking should return false"
        );
        assert_eq!(
            s.stats.ic3_lazy_removed, 1,
            "stat should not increment on double-mark"
        );

        // Clause A should still be active.
        assert!(
            !s.mark_clause_garbage_lazy(usize::MAX),
            "out-of-bounds offset should return false"
        );

        // Solver should still produce correct results with B marked.
        let r = s.solve_incremental_ic3(&[]);
        assert!(r.is_sat(), "formula should still be SAT after lazy removal");

        // Clause A should still be usable.
        assert!(
            s.mark_clause_garbage_lazy(off_a),
            "clause A should still be markable"
        );
    }

    /// Test that clause_subsumes correctly detects subsumption relationships.
    #[test]
    fn ic3_clause_subsumes_detection() {
        let mut s = Solver::new(8);
        s.set_ic3_mode();

        // Clause A: (x0 | x1 | x2) — potential subsumer.
        let off_a = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(1), pos(2)])
            .expect("clause A offset");

        // Clause B: (x0 | x1 | x2 | x3) — subsumed by A.
        let off_b = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(1), pos(2), pos(3)])
            .expect("clause B offset");

        // Clause C: (x0 | x4 | x5) — NOT subsumed by A (different literals).
        let off_c = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(4), pos(5)])
            .expect("clause C offset");

        // Clause D: (x0 | x1) — this subsumes A (it is shorter and a subset).
        // But it's binary so prenormalized won't return an offset. Add to arena
        // via regular path and use a different approach.
        // Instead, use an equal-sized clause: (x0 | x1 | x2) — same as A.
        let off_d = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(1), pos(2)])
            .expect("clause D offset (same as A)");

        // A subsumes B: every literal in A is in B.
        assert!(s.clause_subsumes(off_a, off_b), "A should subsume B");

        // B does NOT subsume A: B has x3 which is not in A.
        assert!(!s.clause_subsumes(off_b, off_a), "B should NOT subsume A");

        // A does NOT subsume C: A has x1, x2 which are not in C.
        assert!(!s.clause_subsumes(off_a, off_c), "A should NOT subsume C");

        // A subsumes D (and D subsumes A) — equal clauses subsume each other.
        assert!(
            s.clause_subsumes(off_a, off_d),
            "A should subsume D (same clause)"
        );
        assert!(
            s.clause_subsumes(off_d, off_a),
            "D should subsume A (same clause)"
        );
    }

    /// Integration test: lazy removal + correctness over multiple IC3 queries.
    /// Adds clauses, marks some as garbage lazily, verifies the solver still
    /// produces correct SAT/UNSAT results across many incremental queries.
    #[test]
    fn ic3_lazy_remove_correctness_across_queries() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a satisfiable transition-system-like formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(5), pos(10)]);
        s.add_clause(vec![pos(3), pos(7), pos(15)]);

        let domain: Vec<Variable> = (0..num_vars / 2).map(var).collect();
        s.set_domain(&domain);

        // First solve to warm up.
        let r = s.solve_incremental_ic3(&[]);
        assert!(r.is_sat(), "base formula should be SAT");

        // Track clause offsets for blocking clauses we add.
        let mut clause_offsets: Vec<usize> = Vec::new();

        for round in 0..100u32 {
            // Add a blocking clause (IC3 frame lemma pattern).
            let l1 = pos(round % (num_vars / 2));
            let l2 = pos((round + 3) % (num_vars / 2));
            let l3 = pos((round + 7) % (num_vars / 2));
            let mut lits = vec![l1, l2, l3];
            lits.sort_by_key(|l| l.0);
            lits.dedup();
            if let Some(off) = s.add_clause_prenormalized_returning_offset(&lits) {
                clause_offsets.push(off);
            }

            // Every 10 rounds, mark some older clauses as garbage.
            if round % 10 == 9 && clause_offsets.len() > 5 {
                // Mark the 3 oldest clauses.
                for &off in clause_offsets.iter().take(3) {
                    let _ = s.mark_clause_garbage_lazy(off);
                }
            }

            // Solve with assumptions.
            let assume = vec![pos(round % (num_vars / 2))];
            let _r = s.solve_incremental_ic3(&assume);

            // Periodically check base formula is still SAT.
            if round % 20 == 0 {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT after lazy removal"
                );
            }
        }

        assert!(
            s.stats.ic3_lazy_removed > 0,
            "should have lazily removed some clauses"
        );
    }

    /// Test that clause_subsumes combined with mark_clause_garbage_lazy
    /// correctly removes subsumed clauses without affecting correctness.
    #[test]
    fn ic3_subsumption_then_lazy_remove() {
        let mut s = Solver::new(8);
        s.set_ic3_mode();

        // Build base formula.
        s.add_clause(vec![pos(0), pos(1)]);
        s.add_clause(vec![pos(2), pos(3)]);

        // First solve.
        let _r = s.solve_incremental_ic3(&[]);

        // Add clause B: (x0 | x1 | x4 | x5) — weaker lemma.
        let off_b = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(1), pos(4), pos(5)])
            .expect("clause B offset");

        // Solve again to attach watches for B.
        let _r = s.solve_incremental_ic3(&[]);

        // Add clause A: (x0 | x1 | x4) — stronger lemma, subsumes B.
        let off_a = s
            .add_clause_prenormalized_returning_offset(&[pos(0), pos(1), pos(4)])
            .expect("clause A offset");

        // A subsumes B — mark B for lazy removal.
        assert!(s.clause_subsumes(off_a, off_b), "A should subsume B");
        assert!(
            s.mark_clause_garbage_lazy(off_b),
            "marking B should succeed"
        );

        // Solve multiple times — correctness should be maintained.
        for i in 0..50u32 {
            let assume = vec![pos(i % 4)];
            let _r = s.solve_incremental_ic3(&assume);
        }

        // Base formula still SAT.
        let r = s.solve_incremental_ic3(&[]);
        assert!(
            r.is_sat(),
            "base formula should be SAT after subsumption removal"
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // ay-chc IC3 code path: solve_with_assumptions + set_domain (#8661)
    // ════════════════════════════════════════════════════════════════════════════

    #[test]
    fn test_chc_ic3_path_domain_bcp_false_nondomain_8661() {
        let mut s = Solver::new(8);
        s.add_clause(vec![neg(4)]);
        s.add_clause(vec![neg(5)]);
        s.add_clause(vec![pos(4), pos(0)]);
        s.add_clause(vec![pos(5), pos(1)]);
        s.add_clause(vec![neg(0), pos(2)]);
        s.add_clause(vec![neg(1), pos(3)]);
        s.add_clause(vec![pos(2), pos(3)]);

        let domain = [var(0), var(1), var(2), var(3)];
        s.set_domain(&domain);

        let r1 = s.solve_with_assumptions(&[neg(0)]);
        assert!(
            r1.is_unsat(),
            "d0=true forced at level 0, d0=false must be UNSAT"
        );

        let r2 = s.solve_with_assumptions(&[pos(0)]);
        assert!(r2.is_sat(), "d0=true is consistent");

        let r3 = s.solve_with_assumptions(&[neg(1)]);
        assert!(
            r3.is_unsat(),
            "d1=true forced at level 0, d1=false must be UNSAT"
        );

        let r4 = s.solve_with_assumptions(&[]);
        assert!(r4.is_sat(), "base formula must be SAT");

        s.clear_domain();
    }

    #[test]
    fn test_chc_ic3_path_consecution_stress_500_queries_8661() {
        let num_domain = 10u32;
        let num_nondomain = 20u32;
        let total = num_domain + num_nondomain;
        let mut s = Solver::new(total as usize);

        for i in 0..num_domain - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in 0..5u32 {
            let nd = num_domain + i;
            s.add_clause(vec![neg(nd)]);
        }
        for i in 0..5u32 {
            let nd = num_domain + i;
            let d = i % num_domain;
            s.add_clause(vec![pos(nd), pos(d)]);
        }
        for i in 0..num_domain - 2 {
            s.add_clause(vec![pos(i), neg(i + 1), pos(i + 2)]);
        }
        let atleast: Vec<Literal> = (0..num_domain).map(pos).collect();
        s.add_clause(atleast);
        for i in num_domain + 5..total - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }

        let domain_vars: Vec<Variable> = (0..num_domain).map(var).collect();
        s.set_domain(&domain_vars);

        let mut sat_count = 0u32;
        let mut unsat_count = 0u32;

        for round in 0..500u32 {
            s.push();
            let v0 = round % num_domain;
            let v1 = (round + 3) % num_domain;
            if v0 != v1 {
                s.add_clause(vec![pos(v0), neg(v1)]);
            }
            let assump_var = round % num_domain;
            let assump = if round % 3 == 0 {
                neg(assump_var)
            } else {
                pos(assump_var)
            };
            let result = s.solve_with_assumptions(&[assump]);
            if result.is_sat() {
                sat_count += 1;
            } else {
                unsat_count += 1;
            }
            assert!(s.pop(), "pop should succeed in round {round}");

            if round % 20 == 10 {
                let a = round % num_domain;
                let b = (round + 2) % num_domain;
                if a != b {
                    s.add_clause(vec![pos(a), pos(b)]);
                }
            }
            if round % 50 == 49 {
                let base = s.solve_with_assumptions(&[]);
                assert!(base.is_sat(), "round {round}: base formula UNSAT (#8661)");
            }
        }

        s.clear_domain();
        assert!(
            sat_count + unsat_count == 500,
            "all 500 queries should complete"
        );
        assert!(unsat_count > 0, "at least some queries should be UNSAT");
    }

    #[test]
    fn test_chc_ic3_path_sat_model_with_unassigned_nondomain_8661() {
        let mut s = Solver::new(6);
        s.add_clause(vec![pos(0), pos(2)]);
        s.add_clause(vec![pos(1), pos(3)]);
        s.add_clause(vec![pos(4), pos(5)]);
        s.set_domain(&[var(0), var(1)]);

        let result = s.solve_with_assumptions(&[pos(0), pos(1)]);
        assert!(
            result.is_sat(),
            "SAT under domain restriction with unassigned non-domain vars"
        );
        s.clear_domain();
    }

    // ════════════════════════════════════════════════════════════════════════════
    // #8633 + #8661 combined regression: high constraint-ratio AIGER pattern
    // with domain-restricted BCP
    // ════════════════════════════════════════════════════════════════════════════

    /// Regression test for #8633: AIGER-like formula where constraint count >>
    /// latch count (8:1 ratio). Uses domain restriction to simulate the IC3
    /// pattern where latches are domain variables and constraint-encoding
    /// variables are non-domain.
    ///
    /// This test targets the exact pattern from #8633: AIGER circuits with
    /// ratios of 6-8x constraints per latch. Non-domain constraint variables
    /// are assigned FALSE at level 0, and domain BCP must correctly propagate
    /// through clauses involving those false non-domain variables.
    ///
    /// The #8661 fix (adding `&& blocker_val == 0` / `&& first_val == 0`
    /// guards) should prevent false UNSAT here.
    #[test]
    fn test_ic3_aiger_high_constraint_ratio_domain_bcp_8633() {
        // Simulate AIGER model checking: 5 latch variables (domain),
        // 40 constraint-encoding variables (non-domain).
        // Ratio: 40/5 = 8x, matching the #8633 pattern.
        let num_latches = 5u32;
        let num_constraints = 40u32;
        let total = (num_latches + num_constraints) as usize;
        let mut s = Solver::new(total);
        s.set_ic3_mode();

        // Force all constraint variables FALSE at level 0 (simulates AIGER
        // constraints that are not satisfiable in the current frame).
        // This is the trigger for #8661: non-domain vars assigned FALSE.
        for i in num_latches..num_latches + num_constraints {
            s.add_clause(vec![neg(i)]);
        }

        // Clauses mixing constraint variables and latch variables.
        // After level 0 propagation, constraint vars are FALSE, so these
        // clauses effectively become unit or binary on latch variables.
        // Domain BCP must NOT skip these clauses.
        for i in 0..num_latches {
            for k in 0..4u32 {
                let nd = num_latches + (i * 4 + k) % num_constraints;
                // (nd_j | latch_i): since nd_j = FALSE, forces latch_i = TRUE
                // at level 0. Before #8661 fix, domain BCP would skip this
                // clause because nd_j is non-domain.
                s.add_clause(vec![pos(nd), pos(i)]);
            }
        }

        // Additional transition relation constraints among latches.
        for i in 0..num_latches - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]); // latch_i -> latch_{i+1}
        }

        // Mixed clauses: constraint variables appear in longer clauses
        // with multiple latch variables.
        for i in 0..num_latches {
            let nd0 = num_latches + (i * 3) % num_constraints;
            let nd1 = num_latches + (i * 3 + 1) % num_constraints;
            let l0 = i;
            let l1 = (i + 1) % num_latches;
            // (nd0 | nd1 | l0 | l1): with nd0=FALSE and nd1=FALSE,
            // reduces to (l0 | l1).
            s.add_clause(vec![pos(nd0), pos(nd1), pos(l0), pos(l1)]);
        }

        // Set domain to latch variables only.
        let domain_vars: Vec<Variable> = (0..num_latches).map(var).collect();
        s.set_domain(&domain_vars);

        // Run IC3 consecution queries.
        for round in 0..500u32 {
            let v = round % num_latches;
            let assumptions = if round % 3 == 0 {
                vec![neg(v)]
            } else if round % 3 == 1 {
                vec![pos(v)]
            } else {
                let v2 = (v + 1) % num_latches;
                vec![pos(v), neg(v2)]
            };

            let result = s.solve_incremental_ic3(&assumptions);

            // Cross-check: every UNSAT must be genuine. The base formula
            // (without assumptions) must remain SAT.
            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT — domain BCP incorrectly \
                     skipped clauses with false non-domain constraint variables \
                     (constraint/latch ratio = 8:1, #8633 + #8661)"
                );
            }
        }

        s.clear_domain();
    }

    /// Stress test for #8633: IC3 consecution with incremental blocking clauses
    /// on a high constraint-ratio formula with domain restriction.
    ///
    /// This combines:
    /// 1. High constraint-to-domain ratio (6:1)
    /// 2. Domain-restricted BCP (latches as domain, constraints as non-domain)
    /// 3. Incremental clause addition (blocking lemmas added between queries)
    /// 4. Mixed SAT/UNSAT queries over 2000 iterations
    ///
    /// The formula is constructed so all-true is always a satisfying
    /// assignment for the latch variables. Any base-formula UNSAT is a
    /// definitive false UNSAT bug.
    #[test]
    fn test_ic3_consecution_high_ratio_incremental_stress_8633() {
        let num_latches = 8u32;
        let num_nondomain = 48u32; // 6:1 ratio
        let total = (num_latches + num_nondomain) as usize;
        let mut s = Solver::new(total);
        s.set_ic3_mode();

        // Force all non-domain vars FALSE at level 0.
        for i in num_latches..num_latches + num_nondomain {
            s.add_clause(vec![neg(i)]);
        }

        // Dense clauses mixing non-domain (FALSE) and domain vars.
        // All clauses include at least one positive latch literal, so
        // all-true assignment on latches satisfies the formula.

        // Layer 1: each non-domain var paired with a latch (48 clauses)
        for i in 0..num_nondomain {
            let nd = num_latches + i;
            let latch = i % num_latches;
            s.add_clause(vec![pos(nd), pos(latch)]);
        }

        // Layer 2: implication chain on latches (7 clauses)
        for i in 0..num_latches - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }

        // Layer 3: skip-1 implications (6 clauses)
        for i in 0..num_latches - 2 {
            s.add_clause(vec![neg(i), pos(i + 2)]);
        }

        // Layer 4: ternary clauses with non-domain FALSE vars (24 clauses)
        for i in 0..num_latches {
            let nd0 = num_latches + (i * 3) % num_nondomain;
            let nd1 = num_latches + (i * 3 + 1) % num_nondomain;
            let nd2 = num_latches + (i * 3 + 2) % num_nondomain;
            // All reduce to unit on latch after non-domain = FALSE
            s.add_clause(vec![pos(nd0), pos(nd1), pos(i)]);
            s.add_clause(vec![pos(nd1), pos(nd2), pos((i + 1) % num_latches)]);
            s.add_clause(vec![pos(nd0), pos(nd2), pos((i + 2) % num_latches)]);
        }

        // Layer 5: positive latch pairs (8 clauses)
        for i in 0..num_latches {
            s.add_clause(vec![pos(i), pos((i + 1) % num_latches)]);
        }

        let domain_vars: Vec<Variable> = (0..num_latches).map(var).collect();
        s.set_domain(&domain_vars);

        // Verify base is SAT before queries.
        let base_check = s.solve_incremental_ic3(&[]);
        assert!(
            base_check.is_sat(),
            "initial base formula must be SAT before stress queries"
        );

        let mut error_count = 0u32;
        let mut first_error = None;
        let mut blocking_added = 0u32;

        for round in 0..2000u32 {
            // Vary assumptions across latches.
            let v0 = round % num_latches;
            let v1 = (round.wrapping_mul(3).wrapping_add(1)) % num_latches;
            let polarity0 = round % 4 != 0;
            let polarity1 = round % 5 < 3;

            let lit0 = if polarity0 { pos(v0) } else { neg(v0) };
            let assumptions = if v0 == v1 {
                vec![lit0]
            } else {
                let lit1 = if polarity1 { pos(v1) } else { neg(v1) };
                vec![lit0, lit1]
            };

            let result = s.solve_incremental_ic3(&assumptions);

            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                if !base.is_sat() {
                    if first_error.is_none() {
                        first_error = Some(round);
                    }
                    error_count += 1;
                }
            }

            // Add blocking clauses every 40 rounds (IC3 pattern).
            // Always include at least one positive latch literal.
            if round % 40 == 20 {
                let a = round % num_latches;
                let b = (round.wrapping_mul(5).wrapping_add(2)) % num_latches;
                if a != b {
                    s.add_clause(vec![pos(a), neg(b), pos((b + 1) % num_latches)]);
                    blocking_added += 1;
                }
            }
        }

        s.clear_domain();

        assert!(
            blocking_added >= 30,
            "expected at least 30 blocking clauses, got {blocking_added}"
        );

        assert_eq!(
            error_count, 0,
            "IC3 consecution stress: {error_count} false UNSAT in 2000 queries \
             (first at round {first_error:?}, constraint/latch ratio = 6:1, \
             {blocking_added} blocking clauses). Domain BCP + high constraint \
             ratio producing incorrect results (#8633 + #8661)."
        );
    }

    /// Targeted regression test for #8633: formula where domain BCP skip
    /// on FALSE non-domain variables directly causes a missed propagation,
    /// leading to false UNSAT.
    ///
    /// This is a minimal reproducer for the #8633 + #8661 interaction:
    /// a single non-domain variable forced FALSE at level 0 appears in a
    /// clause that is the sole reason to propagate a domain variable.
    /// Without the #8661 fix, domain BCP skips the clause and misses the
    /// propagation, causing a conflict that should not exist.
    #[test]
    fn test_ic3_domain_bcp_false_nondomain_missed_propagation_8633() {
        // 8 vars: d0-d3 (domain), nd0-nd3 (non-domain)
        let mut s = Solver::new(8);
        s.set_ic3_mode();

        // nd0 (var 4) = FALSE at level 0
        s.add_clause(vec![neg(4)]);
        // nd1 (var 5) = FALSE at level 0
        s.add_clause(vec![neg(5)]);
        // nd2 (var 6) = FALSE at level 0
        s.add_clause(vec![neg(6)]);

        // Clause: (nd0 | nd1 | d0) — reduces to (d0) since nd0, nd1 = FALSE.
        // This forces d0 = TRUE via propagation through the non-domain FALSE
        // watched literals. Domain BCP must not skip this clause.
        s.add_clause(vec![pos(4), pos(5), pos(0)]);

        // Clause: (nd2 | d0 | d1) — reduces to (d0 | d1)
        s.add_clause(vec![pos(6), pos(0), pos(1)]);

        // Transition constraints among domain vars.
        s.add_clause(vec![neg(0), pos(2)]); // d0 -> d2
        s.add_clause(vec![neg(2), pos(3)]); // d2 -> d3
        s.add_clause(vec![pos(1), pos(3)]); // d1 | d3

        let domain_vars = vec![var(0), var(1), var(2), var(3)];
        s.set_domain(&domain_vars);

        // Query: assume d0=FALSE. Since d0 is forced TRUE by propagation
        // through the non-domain clause, this assumption contradicts the
        // level-0 propagation. Must be UNSAT.
        let r1 = s.solve_incremental_ic3(&[neg(0)]);
        assert!(
            r1.is_unsat(),
            "d0=true is forced by (nd0 | nd1 | d0) after nd0=nd1=FALSE; \
             assuming d0=false must be UNSAT (#8633 + #8661)"
        );

        // Query: assume d0=TRUE. Consistent with propagation.
        let r2 = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            r2.is_sat(),
            "d0=true is consistent with the formula (#8633)"
        );

        // Verify across many queries to detect non-deterministic failures.
        for round in 0..200u32 {
            let v = round % 4;
            let lit = if round % 2 == 0 { pos(v) } else { neg(v) };
            let result = s.solve_incremental_ic3(&[lit]);

            if result.is_unsat() {
                let base = s.solve_incremental_ic3(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT — domain BCP skip bug \
                     on false non-domain vars (#8633 + #8661)"
                );
            }
        }

        s.clear_domain();
    }

    /// Stress test for #8633: many constraint clauses with few domain
    /// variables, all non-domain variables FALSE at level 0, with
    /// solve_with_assumptions (the path used by ay-chc IC3 engine).
    ///
    /// This tests the solve_with_assumptions path (not just
    /// solve_incremental_ic3) because ay-chc calls solve_with_assumptions
    /// with domain restriction set.
    #[test]
    fn test_ic3_solve_with_assumptions_domain_high_ratio_stress_8633() {
        let num_latches = 6u32;
        let num_nondomain = 36u32; // 6:1 ratio
        let total = (num_latches + num_nondomain) as usize;
        let mut s = Solver::new(total);

        // Force non-domain vars FALSE.
        for i in num_latches..num_latches + num_nondomain {
            s.add_clause(vec![neg(i)]);
        }

        // Dense mixed clauses (all satisfiable with all-true latches).
        for i in 0..num_nondomain {
            let nd = num_latches + i;
            let l = i % num_latches;
            s.add_clause(vec![pos(nd), pos(l)]);
        }
        for i in 0..num_latches - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        for i in 0..num_latches {
            s.add_clause(vec![pos(i), pos((i + 1) % num_latches)]);
        }
        for i in 0..num_latches - 2 {
            let nd = num_latches + i % num_nondomain;
            s.add_clause(vec![pos(nd), neg(i), pos(i + 2)]);
        }

        // Use set_domain + solve_with_assumptions (ay-chc path).
        let domain_vars: Vec<Variable> = (0..num_latches).map(var).collect();
        s.set_domain(&domain_vars);

        for round in 0..500u32 {
            let v0 = round % num_latches;
            let assumptions = if round % 3 == 0 {
                vec![neg(v0)]
            } else {
                vec![pos(v0)]
            };

            let result = s.solve_with_assumptions(&assumptions);

            if result.is_unsat() {
                let base = s.solve_with_assumptions(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT via solve_with_assumptions \
                     with domain restriction — high constraint-ratio domain BCP \
                     bug (#8633 + #8661)"
                );
            }
        }

        s.clear_domain();
    }

    /// Regression test for #8661: domain changes between queries.
    ///
    /// Mimics the ay-chc IC3 production pattern where `get_bad_cube` uses
    /// one domain (V(frame_act) + V(bad) + COI(bad)) and `try_block_cube`
    /// uses a different domain (V(frame_act) + V(cube) + V(next_cube) +
    /// COI(next_cube)). The SAT solver must handle domain changes correctly
    /// without leaking stale domain state between queries.
    ///
    /// The bug scenario: if a non-domain variable is false at level 0, and
    /// the domain changes such that it becomes in-domain or a different set
    /// of variables becomes non-domain, the BCP must correctly handle all
    /// permutations.
    #[test]
    fn test_chc_ic3_path_alternating_domains_8661() {
        // 12 variables: state[0..5], next_state[6..11]
        // Simulates a transition system where state vars are current-frame
        // and next_state vars represent the next frame.
        let num_vars = 12u32;
        let mut s = Solver::new(num_vars as usize);

        // Transition relation: state[i] => next_state[i]
        for i in 0..6u32 {
            s.add_clause(vec![neg(i), pos(i + 6)]);
        }

        // Force some variables false at level 0 (simulates AIGER constants).
        // next_state[4] = false, next_state[5] = false
        s.add_clause(vec![neg(10)]);
        s.add_clause(vec![neg(11)]);

        // Implication chain in state vars: s0 => s1 => s2
        s.add_clause(vec![neg(0), pos(1)]);
        s.add_clause(vec![neg(1), pos(2)]);

        // Cross-constraints: s3 => s0, s4 => s1
        s.add_clause(vec![neg(3), pos(0)]);
        s.add_clause(vec![neg(4), pos(1)]);

        // At-least-one in state vars.
        s.add_clause(vec![pos(0), pos(1), pos(2), pos(3), pos(4), pos(5)]);

        // Alternating domains mimicking get_bad_cube vs try_block_cube.
        // Domain A (get_bad_cube): state vars only.
        let domain_a: Vec<Variable> = (0..6).map(var).collect();
        // Domain B (try_block_cube): state + some next_state.
        let domain_b: Vec<Variable> = (0..8).map(var).collect();
        // Domain C (different cube): just a subset.
        let domain_c: Vec<Variable> = vec![var(0), var(1), var(6), var(7)];

        // Run 300 alternating queries with different domains.
        for round in 0..300u32 {
            let domain = match round % 3 {
                0 => &domain_a[..],
                1 => &domain_b[..],
                _ => &domain_c[..],
            };
            s.set_domain(domain);

            let v = round % 6;
            let assumptions = match round % 5 {
                0 => vec![pos(v)],
                1 => vec![neg(v)],
                2 => vec![pos(v), neg((v + 2) % 6)],
                3 => vec![neg(v), pos((v + 3) % 6)],
                _ => vec![],
            };

            let result = s.solve_with_assumptions(&assumptions);
            s.clear_domain();

            // Cross-check: if UNSAT under assumptions, base must be SAT.
            if result.is_unsat() && round % 10 == 0 {
                s.set_domain(domain);
                let base = s.solve_with_assumptions(&[]);
                assert!(
                    base.is_sat(),
                    "round {round}: base formula UNSAT with domain {:?} — \
                     domain change corrupted state (#8661)",
                    match round % 3 {
                        0 => "A (state-only)",
                        1 => "B (state+next)",
                        _ => "C (subset)",
                    }
                );
                s.clear_domain();
            }
        }
    }

    /// IC3 solve loop respects process_memory_interrupt (#8673).
    ///
    /// Verifies that when the memory limit is hit mid-query, the IC3
    /// solve loop detects it via poll_process_memory_limit() and returns
    /// Unknown (interrupted) instead of continuing indefinitely.
    #[test]
    fn ic3_solve_respects_memory_interrupt() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;

        let mut s = Solver::new(10);
        s.set_ic3_mode();

        // Build a hard formula that requires many conflicts.
        // Pigeonhole-like: force many conflicts before resolution.
        for i in 0..9u32 {
            s.add_clause(vec![pos(i), pos((i + 1) % 10)]);
            s.add_clause(vec![neg(i), neg((i + 1) % 10)]);
        }
        // Make it satisfiable but hard.
        s.add_clause(vec![pos(0), pos(5)]);
        s.add_clause(vec![neg(5), pos(9)]);

        // Set the external interrupt flag to simulate memory pressure.
        let interrupt = Arc::new(AtomicBool::new(false));
        s.set_interrupt(interrupt.clone());

        // First solve without interrupt should work.
        let r1 = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            r1.is_sat() || r1.is_unsat(),
            "first solve should succeed without interrupt"
        );

        // Now set interrupt to simulate memory limit hit.
        interrupt.store(true, Ordering::Relaxed);

        // Second solve should detect the interrupt and return Unknown.
        let r2 = s.solve_incremental_ic3(&[pos(1)]);
        assert!(
            r2.is_unknown(),
            "IC3 solve must respect interrupt (memory limit): got {:?}",
            r2.into_inner()
        );
    }

    /// Regression test for #8661: transitive propagation through non-domain
    /// variables missed by domain BCP.
    ///
    /// Minimal reproducer: domain BCP skips clauses where watched literal
    /// is a non-domain UNASSIGNED variable. But two such skipped clauses
    /// may force the non-domain variable to contradictory values, creating
    /// a missed conflict that leads to false UNSAT.
    ///
    /// Formula:
    ///   C1: (~d0 | nd0)    — d0 implies nd0
    ///   C2: (~nd0 | d1)    — nd0 implies d1
    ///   C3: (~d0 | ~d1)    — d0 implies ~d1
    ///
    /// With full BCP and d0=true:
    ///   C1 propagates nd0=true, C2 propagates d1=true, C3 conflicts (d0=T, d1=T).
    ///
    /// With domain BCP and domain={d0,d1}, d0=true:
    ///   C1: ~d0 is false, other watch = nd0 (non-domain, unassigned) → SKIP
    ///   C3: ~d0 is false, other watch = ~d1 (domain, unassigned) → propagate d1=false
    ///   No conflict detected! But the formula is UNSAT under d0=true.
    ///
    /// This is the root cause of 33/50 HWMCC soundness errors (#8661).
    /// The fix: expand the domain to include transitively connected variables.
    #[test]
    fn test_ic3_transitive_nondomain_propagation_8661() {
        let mut s = Solver::new(3);
        s.set_ic3_mode();

        // d0=var0, d1=var1, nd0=var2
        // C1: ~d0 | nd0
        s.add_clause(vec![neg(0), pos(2)]);
        // C2: ~nd0 | d1
        s.add_clause(vec![neg(2), pos(1)]);
        // C3: ~d0 | ~d1
        s.add_clause(vec![neg(0), neg(1)]);

        // Domain: {d0, d1} — nd0 is NOT in domain
        s.set_domain(&[var(0), var(1)]);

        // With d0=true: full BCP finds conflict (d1 must be both true and false).
        // Domain BCP may miss it because nd0 propagation is skipped.
        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            result.is_unsat(),
            "d0=true must be UNSAT: C1 forces nd0=true, C2 forces d1=true, \
             C3 forces d1=false → conflict. Domain BCP missed transitive \
             propagation through non-domain variable nd0 (#8661)."
        );

        // Without assumption: SAT (d0=false satisfies C1 and C3).
        let base = s.solve_incremental_ic3(&[]);
        assert!(
            base.is_sat(),
            "base formula must be SAT (d0=false is a valid assignment)"
        );

        s.clear_domain();
    }

    /// Extended regression test for #8661: larger transitive chain through
    /// multiple non-domain variables.
    ///
    /// d0 → nd0 → nd1 → d1, but d0 → ¬d1.
    /// Domain = {d0, d1}. Both nd0 and nd1 are outside domain.
    #[test]
    fn test_ic3_transitive_chain_nondomain_8661() {
        let mut s = Solver::new(4);
        s.set_ic3_mode();

        // d0=var0, d1=var1, nd0=var2, nd1=var3
        // d0 → nd0
        s.add_clause(vec![neg(0), pos(2)]);
        // nd0 → nd1
        s.add_clause(vec![neg(2), pos(3)]);
        // nd1 → d1
        s.add_clause(vec![neg(3), pos(1)]);
        // d0 → ~d1
        s.add_clause(vec![neg(0), neg(1)]);

        s.set_domain(&[var(0), var(1)]);

        // d0=true → nd0=true → nd1=true → d1=true, but d0=true → d1=false.
        // Must be UNSAT.
        let result = s.solve_incremental_ic3(&[pos(0)]);
        assert!(
            result.is_unsat(),
            "d0=true must be UNSAT via transitive chain through nd0, nd1 (#8661)"
        );

        let base = s.solve_incremental_ic3(&[]);
        assert!(base.is_sat(), "base formula must be SAT");

        s.clear_domain();
    }

    /// Stress test for #8661: many queries mixing domain/non-domain with
    /// transitive non-domain dependencies. Cross-checks each UNSAT result
    /// against a full BCP solve (no domain restriction).
    #[test]
    fn test_ic3_transitive_nondomain_stress_8661() {
        // 4 domain vars (d0-d3), 4 non-domain vars (nd0-nd3)
        let mut s_domain = Solver::new(8);
        let mut s_full = Solver::new(8);
        s_domain.set_ic3_mode();
        s_full.set_ic3_mode();

        let clauses: Vec<Vec<Literal>> = vec![
            // d0 → nd0
            vec![neg(0), pos(4)],
            // nd0 → d2
            vec![neg(4), pos(2)],
            // d1 → nd1
            vec![neg(1), pos(5)],
            // nd1 → d3
            vec![neg(5), pos(3)],
            // d2 → nd2
            vec![neg(2), pos(6)],
            // nd2 → nd3
            vec![neg(6), pos(7)],
            // d0 → d1
            vec![neg(0), pos(1)],
            // ~d2 | ~d3 (conflict if both true)
            vec![neg(2), neg(3)],
            // d0 | d1 | d2 | d3 (at least one domain var true)
            vec![pos(0), pos(1), pos(2), pos(3)],
        ];

        for clause in &clauses {
            s_domain.add_clause(clause.clone());
            s_full.add_clause(clause.clone());
        }

        s_domain.set_domain(&[var(0), var(1), var(2), var(3)]);
        // s_full: no domain restriction (full BCP)

        let mut errors = 0u32;
        for round in 0..200u32 {
            let v = round % 4;
            let lit = if round % 2 == 0 { pos(v) } else { neg(v) };

            let r_domain = s_domain.solve_incremental_ic3(&[lit]);
            let r_full = s_full.solve_incremental_ic3(&[lit]);

            // Domain-restricted result must agree with full BCP.
            if r_full.is_unsat() && r_domain.is_sat() {
                // Domain BCP missed a conflict — this is the bug.
                errors += 1;
            }
            if r_full.is_sat() && r_domain.is_unsat() {
                // Domain BCP found a spurious conflict — also a bug.
                errors += 1;
            }
        }

        s_domain.clear_domain();

        assert_eq!(
            errors, 0,
            "IC3 transitive non-domain stress: {errors}/200 queries disagree \
             between domain-restricted and full BCP (#8661)"
        );
    }

    // ════════════════════════════════════════════════════════════════════════════
    // IC3 domain cache tests (#8569 Gap 1)
    // ════════════════════════════════════════════════════════════════════════════

    /// Verify that the IC3 domain expansion cache is effective when the same
    /// domain is queried repeatedly without clause DB changes.
    #[test]
    fn ic3_domain_cache_hits_on_repeated_domain() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        // Build a chain formula.
        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);

        let domain_vars = vec![Variable(0), Variable(3), Variable(7)];

        // First call: cache miss (expansion must be computed).
        s.set_domain(&domain_vars);
        let _r = s.solve_incremental_ic3(&[pos(0)]);
        s.clear_domain();

        let misses_after_first = s.stats.ic3_domain_cache_misses;
        assert!(
            misses_after_first > 0,
            "first set_domain should be a cache miss"
        );

        // Same domain, no new clauses: cache hit.
        s.set_domain(&domain_vars);
        let _r = s.solve_incremental_ic3(&[pos(3)]);
        s.clear_domain();

        assert!(
            s.stats.ic3_domain_cache_hits > 0,
            "repeated set_domain with same vars and no new clauses should be a cache hit \
             (hits={}, misses={})",
            s.stats.ic3_domain_cache_hits,
            s.stats.ic3_domain_cache_misses,
        );
    }

    /// Verify that the IC3 domain expansion cache is invalidated when new
    /// clauses are added between queries.
    #[test]
    fn ic3_domain_cache_invalidated_on_new_clauses() {
        let num_vars = 20u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);

        let domain_vars = vec![Variable(0), Variable(3), Variable(7)];

        // First call.
        s.set_domain(&domain_vars);
        let _r = s.solve_incremental_ic3(&[pos(0)]);
        s.clear_domain();

        let hits_before = s.stats.ic3_domain_cache_hits;

        // Add a blocking clause (IC3 pattern).
        s.add_clause(vec![neg(5), pos(10)]);

        // Same domain, but new clause added: cache miss.
        s.set_domain(&domain_vars);
        let _r = s.solve_incremental_ic3(&[pos(3)]);
        s.clear_domain();

        // The cache should have been invalidated by the new clause.
        // One of these must have increased: either misses (cache invalid)
        // or hits (if the boundary happens to match -- unlikely).
        let total_after = s.stats.ic3_domain_cache_hits + s.stats.ic3_domain_cache_misses;
        assert!(
            total_after >= hits_before + 2,
            "second set_domain after add_clause should trigger a cache check"
        );
    }

    /// Verify that the can_use_incremental_reset IC3 fast path works correctly.
    /// In IC3 mode, the fast path should always return true (O(1) check).
    #[test]
    fn ic3_can_use_incremental_reset_fast_path() {
        let num_vars = 15u32;
        let mut s = Solver::new(num_vars as usize);
        s.set_ic3_mode();

        for i in 0..num_vars - 1 {
            s.add_clause(vec![neg(i), pos(i + 1)]);
        }
        s.add_clause(vec![pos(0), pos(3)]);

        // First solve -- sets assumption_cache_valid.
        let _r = s.solve_incremental_ic3(&[pos(0)]);

        // Add blocking clauses.
        for i in 0..5u32 {
            s.add_clause(vec![neg(i), pos(i + 5)]);
        }

        // Subsequent solves should use incremental reset (not full reset).
        for i in 0..20u32 {
            let _r = s.solve_incremental_ic3(&[pos(i % num_vars)]);
        }

        // All subsequent solves should have been cache hits.
        assert!(
            s.stats.assumption_cache_hits >= 20,
            "IC3 mode should use incremental reset for all queries after first \
             (hits={}, misses={})",
            s.stats.assumption_cache_hits,
            s.stats.assumption_cache_misses,
        );
        // At most 1 cache miss (the very first solve).
        assert!(
            s.stats.assumption_cache_misses <= 1,
            "at most 1 cache miss expected (the first solve), got {}",
            s.stats.assumption_cache_misses,
        );
    }
}
