// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod cursor;

#[test]
fn actual_standard_bcp_matches_clause_order_lbd_backtrack_activity_and_trace() {
    for reasons in [Reasons::Binary, Reasons::Long] {
        for length in [1, 2, 4, 16] {
            let (mut expected, conflict, _) = fixture(length, reasons);
            let result = ordinary(&mut expected, conflict).unwrap();
            if matches!(reasons, Reasons::Long) {
                assert!(expected.cold.lrat_enabled && expected.has_live_clause_trace());
                assert!(!expected.cold.unsat_certificate_enabled);
                assert!(result.chain.len() >= 3);
                assert!(result.chain.iter().all(|id| *id > 0));
            } else {
                assert!(result.chain.is_empty());
            }
            let (mut s, conflict, _) = fixture(length, reasons);
            let trace = format!("{:?}", s.clause_trace());
            let before = clauses(&s);
            attach(&mut s, &test_owner(100_000_000, 100_000_000));
            assert_eq!(run(&mut s, conflict), Ok(Some(result)));
            assert_eq!(s.search_ticks, expected.search_ticks);
            assert_eq!(s.stats.otfs_candidates, expected.stats.otfs_candidates);
            assert_eq!(s.stats.ibcl_attempts, expected.stats.ibcl_attempts);
            assert_eq!(
                s.stats.ibcl_skipped_short_chain,
                expected.stats.ibcl_skipped_short_chain
            );
            assert_eq!(
                s.stats.ibcl_skipped_missing_pivots,
                expected.stats.ibcl_skipped_missing_pivots
            );
            assert_eq!(
                s.stats.lrat_original_learned_snapshot_singleton_skips,
                expected
                    .stats
                    .lrat_original_learned_snapshot_singleton_skips
            );
            assert_eq!(
                s.stats.trail_at_conflict_sum,
                expected.stats.trail_at_conflict_sum
            );
            assert_eq!(
                s.stats.level_at_conflict_sum,
                expected.stats.level_at_conflict_sum
            );
            for var in 0..s.num_vars {
                assert_eq!(
                    s.vsids.bump_order(Variable(var as u32)),
                    expected.vsids.bump_order(Variable(var as u32))
                );
            }
            assert_eq!(format!("{:?}", s.clause_trace()), trace);
            assert_eq!(clauses(&s), before);
            clean(&s);
        }
    }
}

fn satisfies(clause: &[Literal], bits: usize) -> bool {
    clause
        .iter()
        .any(|lit| (((bits >> lit.variable().index()) & 1) == 1) == lit.is_positive())
}

#[test]
fn complete_learned_clause_is_entailed_by_nonempty_original_model_sets() {
    for reasons in [Reasons::Binary, Reasons::Long] {
        for length in 1..=3 {
            let (mut s, conflict, source) = fixture(length, reasons);
            attach(&mut s, &test_owner(100_000_000, 100_000_000));
            let learned = run(&mut s, conflict).unwrap().unwrap();
            assert_eq!(learned.clause[0], neg(2));
            let mut models = 0;
            for bits in 0..(1usize << s.num_vars) {
                if source.iter().all(|clause| satisfies(clause, bits)) {
                    models += 1;
                    assert!(satisfies(&learned.clause, bits), "nonconsequence at {bits}");
                }
            }
            assert!(models > 0, "SAT antecedents: no vacuous UNSAT entailment");
            assert!(!learned.clause.is_empty());
        }
    }
}

#[test]
fn real_binary_and_arena_reason_routes_are_nonvacuous() {
    for reasons in [Reasons::Binary, Reasons::Long] {
        let (mut s, conflict, _) = fixture(4, reasons);
        let count = s
            .trail
            .iter()
            .filter(
                |lit| match (reasons, s.var_reason_kind(lit.variable().index())) {
                    (Reasons::Binary, ReasonKind::BinaryLiteral(_)) => true,
                    (Reasons::Long, ReasonKind::Clause(_)) => true,
                    _ => false,
                },
            )
            .count();
        assert!(count >= 4);
        attach(&mut s, &test_owner(100_000_000, 100_000_000));
        assert!(run(&mut s, conflict).unwrap().is_some());
        clean(&s);
    }
}

#[test]
fn default_chronological_stale_cursor_cap_preserves_semantic_bailout() {
    let (mut expected, conflict) = late_conflict_fixture(2, Reasons::Binary);
    assert!(ordinary(&mut expected, conflict).is_none());
    let (mut s, conflict) = late_conflict_fixture(2, Reasons::Binary);
    let before = s.stats.trail_exhaustion_bailouts;
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert_eq!(run(&mut s, conflict), Ok(None));
    assert_eq!(s.stats.trail_exhaustion_bailouts, before + 1);
    assert_eq!(s.search_ticks, expected.search_ticks);
    clean(&s);
}

/// Delay the actual lower-level conflict clause until after the extra decision.
/// No decision skips pending propagation or crosses a previously found conflict.
fn late_conflict_fixture(length: u32, reasons: Reasons) -> (Solver, ClauseRef) {
    let (mut s, source) = fork_formula(length, reasons);
    let (conflict, antecedents) = source.split_last().unwrap();
    for clause in antecedents {
        assert!(s.add_clause(clause.clone()));
    }
    s.initialize_watches();
    for var in [0, 1, 2] {
        s.decide(pos(var));
        assert!(s.search_propagate().is_none());
    }
    let extra = s.new_var();
    s.decide(Literal::positive(extra));
    assert!(s.search_propagate().is_none());
    assert_eq!(s.qhead, s.trail.len());
    assert!(conflict.iter().all(|&lit| s.lit_val(lit) < 0));
    assert!(conflict
        .iter()
        .all(|lit| s.var_data[lit.variable().index()].level < s.decision_level));
    let reference = s.add_clause_db(conflict, false);
    assert!(s.chrono_enabled);
    (s, ClauseRef(reference as u32))
}

#[test]
fn unmaterialized_lazy_and_non_uip_decision_preserve_standard_bailout() {
    for lazy in [false, true] {
        let (mut s, conflict, _) = fixture(2, Reasons::Long);
        let last = s.trail.last().unwrap().variable().index();
        s.var_data[last].reason = if lazy { 0 } else { NO_REASON };
        s.var_data[last].set_lazy_theory_reason(lazy);
        attach(&mut s, &test_owner(100_000_000, 100_000_000));
        assert_eq!(run(&mut s, conflict), Ok(None));
        assert_eq!(s.stats.trail_exhaustion_bailouts, 1);
        clean(&s);
    }
}

#[test]
fn earlier_lazy_materialization_failure_is_cleared_without_learning() {
    let (mut s, conflict, _) = fixture(2, Reasons::Long);
    s.cold.lazy_materialization_failed = true;
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert_eq!(run(&mut s, conflict), Ok(None));
    assert!(!s.cold.lazy_materialization_failed);
    clean(&s);
}

#[cfg(all(feature = "jit", target_arch = "aarch64"))]
#[test]
fn selected_native_kernel_preserves_binary_empty_steps_and_scalar_result() {
    for reasons in [Reasons::Binary, Reasons::Long] {
        let (mut scalar, reference, _) = fixture(3, reasons);
        assert!(!scalar.standard_native_available());
        let scalar_result = ordinary(&mut scalar, reference).unwrap();
        let (mut ordinary_solver, conflict, _) = fixture(3, reasons);
        ordinary_solver.compile_conflict_processor();
        assert!(
            ordinary_solver.standard_native_available(),
            "native selection must be real"
        );
        let expected = ordinary(&mut ordinary_solver, conflict).unwrap();
        assert_eq!(expected, scalar_result);
        let (mut s, conflict, _) = fixture(3, reasons);
        if matches!(reasons, Reasons::Binary) {
            assert_eq!(s.stats.jumped_reasons, 4);
            for var in 3..9 {
                assert!(matches!(
                    s.var_reason_kind(var),
                    ReasonKind::BinaryLiteral(lit) if lit == neg(2)
                ));
            }
        }
        s.compile_conflict_processor();
        assert!(s.standard_native_available());
        attach(&mut s, &test_owner(100_000_000, 100_000_000));
        assert_eq!(run(&mut s, conflict), Ok(Some(expected)));
        assert!(s.stats.sat_conflict_analysis_native_applications > 0);
        if matches!(reasons, Reasons::Binary) {
            // The legacy native path reprocesses the previous arena clause
            // after each binary reason even though scalar w.len is zero.
            // Jump compression above preserves six real assignments but only
            // two endpoint resolutions: the initial clause plus two empty steps.
            assert_eq!(s.stats.sat_conflict_analysis_native_applications, 3);
        }
        assert_eq!(
            s.stats.sat_conflict_analysis_native_applications,
            ordinary_solver
                .stats
                .sat_conflict_analysis_native_applications
        );
        clean(&s);
    }
}

#[cfg(all(feature = "jit", target_arch = "aarch64", debug_assertions))]
#[test]
fn selected_debug_crosscheck_grows_its_real_output_under_original_owner() {
    let (mut expected, reference, _) = fixture(3, Reasons::Long);
    while expected.num_vars < 69 {
        expected.new_var();
    }
    expected.compile_conflict_processor();
    assert!(expected.standard_native_available());
    assert!(expected.cold.debug_interp_output.capacity() < expected.num_vars);
    let result = ordinary(&mut expected, reference).unwrap();
    let (mut s, reference, _) = fixture(3, Reasons::Long);
    while s.num_vars < 69 {
        s.new_var();
    }
    s.compile_conflict_processor();
    assert!(s.cold.debug_interp_output.capacity() < s.num_vars);
    let owner = test_owner(100_000_000, 100_000_000);
    attach(&mut s, &owner);
    assert_eq!(run(&mut s, reference), Ok(Some(result)));
    assert_eq!(s.cold.debug_interp_output.capacity(), s.num_vars);
    assert_eq!(
        s.cold.debug_interp_output.capacity(),
        expected.cold.debug_interp_output.capacity()
    );
    assert!(owner.usage().unwrap().storage_admitted > 0);
    assert!(s.stats.sat_conflict_analysis_native_applications > 6);
    clean(&s);
}

#[test]
fn chronological_stale_position_is_capped_after_real_reason_discovery() {
    let (mut expected, reference, _) = fixture(3, Reasons::Binary);
    let result = ordinary(&mut expected, reference).unwrap();
    // Both an out-of-range position and an in-range entry for a different
    // variable used to rewind past resolved seen entries and select a false UIP.
    for claimed in [u32::MAX, 8] {
        let (mut ordinary_solver, reference, _) = fixture(3, Reasons::Binary);
        ordinary_solver.var_data[2].trail_pos = claimed;
        assert_eq!(
            ordinary(&mut ordinary_solver, reference),
            Some(result.clone())
        );
        let (mut s, reference, source) = fixture(3, Reasons::Binary);
        s.var_data[2].trail_pos = claimed;
        attach(&mut s, &test_owner(100_000_000, 100_000_000));
        let actual = run(&mut s, reference).unwrap().unwrap();
        assert_eq!(actual, result);
        assert_eq!(s.stats.trail_exhaustion_bailouts, 0);
        let mut models = 0;
        for bits in 0..1usize << s.num_vars {
            if source.iter().all(|clause| satisfies(clause, bits)) {
                models += 1;
                assert!(satisfies(&actual.clause, bits), "nonconsequence at {bits}");
            }
        }
        assert!(models > 0);
        // An explicit original-CNF model refutes the old wrong-UIP clause.
        assert!(source.iter().all(|clause| satisfies(clause, 59)));
        assert!(!satisfies(&[neg(5), neg(1), neg(0)], 59));
        assert!(satisfies(&actual.clause, 59));
        clean(&s);
    }
}

fn ghost_fixture() -> (Solver, ClauseRef) {
    let (mut s, _) = late_conflict_fixture(2, Reasons::Long);
    let ghost = s.new_var();
    s.ghost_guard_needed = true;
    s.var_data[ghost.index()].level = s.decision_level + 1;
    s.var_data[ghost.index()].trail_pos = u32::MAX;
    let reference = s.add_clause_db(&[neg(0), neg(1), Literal::positive(ghost)], false);
    assert_eq!(s.lit_val(Literal::positive(ghost)), 0);
    (s, ClauseRef(reference as u32))
}

#[test]
fn stale_ghost_antecedent_is_dropped_before_level_or_cursor_use_without_learning() {
    let (mut expected, reference) = ghost_fixture();
    assert!(ordinary(&mut expected, reference).is_none());
    let (mut s, reference) = ghost_fixture();
    let before = clauses(&s);
    let trace = format!("{:?}", s.clause_trace());
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert_eq!(run(&mut s, reference), Ok(None));
    assert_eq!(s.stats.trail_exhaustion_bailouts, 1);
    assert_eq!(s.search_ticks, expected.search_ticks);
    assert_eq!(clauses(&s), before);
    assert_eq!(format!("{:?}", s.clause_trace()), trace);
    clean(&s);
}

#[cfg(all(feature = "jit", target_arch = "aarch64"))]
#[test]
fn insufficient_compiled_capacity_preserves_selected_scalar_fallback() {
    let (mut s, conflict, _) = fixture(1, Reasons::Long);
    s.compile_conflict_processor();
    let capacity = s.jit_conflict_processor.as_ref().unwrap().capacity();
    while s.num_vars <= capacity {
        s.new_var();
    }
    assert!(!s.standard_native_available());
    attach(&mut s, &test_owner(100_000_000, 100_000_000));
    assert!(run(&mut s, conflict).unwrap().is_some());
    assert_eq!(s.stats.sat_conflict_analysis_native_applications, 0);
    clean(&s);
}
