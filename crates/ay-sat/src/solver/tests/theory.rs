// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory integration tests: theory lemmas, theory propagation, theory callbacks,
//! extension stop/conflict, and unknown reason classification.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;

// ========================================================================
// Theory Lemma and Propagation Tests
// ========================================================================

#[test]
fn test_add_theory_lemma_normalizes_duplicate_literals() {
    let mut solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    let clause_ref = solver
        .add_theory_lemma(vec![x0, x0, x1])
        .expect("non-tautological lemma should be added");
    let clause = solver.arena.literals(clause_ref.0 as usize);
    assert_eq!(clause.len(), 2, "duplicate literal must be removed");
    assert!(clause.contains(&x0));
    assert!(clause.contains(&x1));
    assert_eq!(
        solver.watches.count_watches_for_clause(clause_ref),
        2,
        "binary lemma must attach exactly two watches"
    );
}

#[test]
fn test_add_theory_lemma_discards_tautology_after_dedup() {
    let mut solver = Solver::new(1);
    let x0 = Literal::positive(Variable(0));

    assert!(
        solver
            .add_theory_lemma(vec![x0, x0, x0.negated()])
            .is_none(),
        "tautological lemma should be ignored"
    );
    assert_eq!(
        solver.arena.num_clauses(),
        0,
        "tautological lemma must not be added to clause DB"
    );
}

#[test]
fn test_batched_all_false_theory_lemmas_preserve_every_conflict_fifo() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    for decision in [x0, x1, x2] {
        solver.decide(decision);
        solver.qhead = solver.trail.len();
    }
    assert_eq!(solver.decision_level, 3);

    let first = solver
        .add_theory_lemma(vec![x0.negated(), x1.negated()])
        .expect("first all-false theory lemma");
    let second = solver
        .add_theory_lemma(vec![x0.negated(), x2.negated()])
        .expect("second all-false theory lemma");

    assert_eq!(
        solver.pending_theory_conflicts.len(),
        2,
        "a theory batch must not overwrite an earlier live conflict",
    );
    assert_eq!(solver.take_pending_theory_conflict(), Some(first));
    assert_eq!(solver.take_pending_theory_conflict(), Some(second));
    assert_eq!(solver.take_pending_theory_conflict(), None);
}

#[test]
fn test_all_false_unit_theory_lemma_is_queued_at_nonzero_level() {
    let mut solver = Solver::new(1);
    let x0 = Literal::positive(Variable(0));

    solver.decide(x0);
    solver.qhead = solver.trail.len();

    let conflict_ref = solver
        .add_theory_lemma(vec![x0.negated()])
        .expect("all-false unit theory lemma");

    assert_eq!(
        solver.take_live_pending_theory_conflict(),
        Some(conflict_ref),
        "a callback may ignore add_theory_lemma's return value, so every \
         immediately falsified non-root theory lemma must enter the queue",
    );
}

#[test]
fn test_unassigned_nonroot_theory_unit_is_installed_at_root_and_persists() {
    let mut solver = Solver::new(2);
    let decision = Literal::positive(Variable(0));
    let unit = Literal::positive(Variable(1));

    solver.decide(decision);
    solver.qhead = solver.trail.len();
    let unit_ref = solver
        .add_theory_lemma(vec![unit])
        .expect("unassigned non-root unit must be stored");
    assert_eq!(solver.var_level(unit.variable()), Some(1));

    assert_eq!(
        solver.take_live_pending_theory_conflict(),
        Some(unit_ref),
        "current-level enqueue alone is not durable; root work must be queued",
    );
    solver.analyze_and_backtrack(unit_ref, "unassigned queued theory unit", |_, _| {});
    assert_eq!(solver.var_level(unit.variable()), Some(0));
    assert_eq!(
        solver.search_propagate(),
        None,
        "the installed root unit must reach BCP quiescence before a decision",
    );

    solver.decide(decision);
    solver.backtrack(0);
    assert_eq!(
        solver.lit_value(unit),
        Some(true),
        "a later backtrack must preserve the root theory unit",
    );

    assert!(solver.add_clause(vec![unit.negated()]));
    assert!(
        solver.solve().into_inner().is_unsat(),
        "the installed theory unit must forbid its negation",
    );
}

#[test]
fn test_true_nonroot_theory_unit_is_stored_and_promoted_to_root() {
    let mut solver = Solver::new(2);
    let unit = Literal::positive(Variable(0));
    let later_decision = Literal::positive(Variable(1));

    solver.decide(unit);
    solver.qhead = solver.trail.len();
    let unit_ref = solver
        .add_theory_lemma(vec![unit])
        .expect("true-above-root unit must not be treated as permanently satisfied");

    assert_eq!(
        solver.take_live_pending_theory_conflict(),
        Some(unit_ref),
        "a true non-root unit remains mandatory root work",
    );
    solver.analyze_and_backtrack(unit_ref, "true non-root theory unit", |_, _| {});

    assert_eq!(solver.var_level(unit.variable()), Some(0));
    let clause_id = solver.clause_id(unit_ref);
    assert_ne!(clause_id, 0);
    assert_eq!(
        solver.unit_proof_id[unit.variable().index()],
        clause_id,
        "root promotion must preserve the arena theory clause's trace ID",
    );
    assert_eq!(
        solver.search_propagate(),
        None,
        "the promoted root unit must reach BCP quiescence before a decision",
    );

    solver.decide(later_decision);
    solver.backtrack(0);
    let model = match solver.solve().into_inner() {
        SatResult::Sat(model) => model,
        other => panic!("promoted true unit should remain SAT, got {other:?}"),
    };
    assert!(model[unit.variable().index()]);
    assert_eq!(solver.var_level(unit.variable()), Some(0));
}

#[test]
fn test_callback_false_unit_becomes_root_fact_with_or_without_chrono() {
    for chrono_enabled in [true, false] {
        let mut solver = Solver::new(2);
        let x0 = Literal::positive(Variable(0));
        let x1 = Literal::positive(Variable(1));
        assert!(solver.add_clause(vec![x0, x1]));
        solver.set_phase(x0.variable(), true);
        solver.set_phase(x1.variable(), true);
        solver.set_chrono_enabled(chrono_enabled);

        let mut injected_unit = None;
        let result = solver
            .solve_with_theory(|solver| {
                if injected_unit.is_none() && solver.current_decision_level() > 0 {
                    let assigned = *solver
                        .trail()
                        .last()
                        .expect("a non-root callback must see an assigned literal");
                    let unit = assigned.negated();
                    solver.add_theory_lemma(vec![unit]);
                    injected_unit = Some(unit);
                }
                TheoryPropResult::Continue
            })
            .into_inner();

        let unit = injected_unit.expect("the callback must inject a false unit");
        let model = match result {
            SatResult::Sat(model) => model,
            other => panic!(
                "false unit callback should re-search to SAT with chrono={chrono_enabled}, \
                 got {other:?}",
            ),
        };
        assert_eq!(
            model[unit.variable().index()],
            unit.is_positive(),
            "the returned model must satisfy the theory unit",
        );
        assert_eq!(
            solver.var_level(unit.variable()),
            Some(0),
            "a global unit theory axiom must remain fixed at level 0",
        );
    }
}

#[test]
fn test_callback_unit_theory_propagation_is_installed_at_root() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let unit = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    assert!(solver.add_clause(vec![x0, x2]));
    solver.set_phase(x0.variable(), true);

    let mut injected = false;
    let result = solver
        .solve_with_theory(|solver| {
            if !injected && solver.current_decision_level() > 0 && solver.lit_value(unit).is_none()
            {
                solver.add_theory_propagation(vec![unit], unit);
                injected = true;
            }
            TheoryPropResult::Continue
        })
        .into_inner();

    assert!(
        injected,
        "the callback must add the unit propagation above root"
    );
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("unit theory propagation should remain SAT, got {other:?}"),
    };
    assert!(model[unit.variable().index()]);
    assert_eq!(
        solver.var_level(unit.variable()),
        Some(0),
        "length-1 theory propagation must survive callback-aware backtracking",
    );
}

#[test]
fn test_false_unit_behind_earlier_conflict_is_not_discarded_after_backtrack() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    for decision in [x0, x1, x2] {
        solver.decide(decision);
        solver.qhead = solver.trail.len();
    }

    let first = solver
        .add_theory_lemma(vec![x0.negated(), x1.negated()])
        .expect("earlier all-false theory conflict");
    let unit = solver
        .add_theory_lemma(vec![x2.negated()])
        .expect("later false theory unit");

    assert_eq!(solver.take_live_pending_theory_conflict(), Some(first));
    solver.analyze_and_backtrack(first, "queued conflict before unit", |_, _| {});
    assert_eq!(
        solver.lit_value(x2),
        None,
        "the earlier conflict must retract the unit's opposite assignment",
    );

    assert_eq!(
        solver.take_live_pending_theory_conflict(),
        Some(unit),
        "an active queued unit remains actionable after becoming unassigned",
    );
    solver.analyze_and_backtrack(unit, "queued unit after conflict", |_, _| {});
    assert_eq!(solver.lit_value(x2.negated()), Some(true));
    assert_eq!(solver.var_level(x2.variable()), Some(0));
}

#[test]
fn test_solve_loop_installs_unassigned_unit_tail_after_head_backtracks_to_root() {
    let mut solver = Solver::new(3);
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    solver.set_chrono_enabled(false);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    assert!(solver.add_clause(vec![x0.negated(), x1]));
    assert!(solver.add_clause(vec![x0.negated(), x2]));
    solver.set_phase(x0.variable(), true);

    let mut injected = false;
    let result = solver
        .solve_with_theory(|solver| {
            if !injected
                && solver.current_decision_level() == 1
                && solver.lit_value(x0) == Some(true)
                && solver.lit_value(x1) == Some(true)
                && solver.lit_value(x2) == Some(true)
            {
                solver.add_theory_lemma(vec![x0.negated(), x1.negated()]);
                solver.add_theory_lemma(vec![x2.negated()]);
                injected = true;
            }
            TheoryPropResult::Continue
        })
        .into_inner();

    assert!(injected, "the callback must queue the head and unit tail");
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("root-drained unit tail must not cause false UNSAT, got {other:?}"),
    };
    assert!(!model[x0.variable().index()]);
    assert!(!model[x2.variable().index()]);
    assert_eq!(
        solver.var_level(x2.variable()),
        Some(0),
        "the unit tail must be installed directly when queue drain reaches level 0",
    );
}

#[test]
fn test_scoped_assumption_path_processes_false_unit_with_or_without_chrono() {
    for chrono_enabled in [true, false] {
        let mut solver = Solver::new(1);
        let x0 = Literal::positive(Variable(0));
        solver.push();
        assert!(solver.add_clause(vec![x0]));
        solver.set_chrono_enabled(chrono_enabled);

        let mut injected = false;
        let scoped_result = solver
            .solve_with_theory(|solver| {
                if !injected
                    && solver.current_decision_level() > 0
                    && solver.lit_value(x0) == Some(true)
                {
                    solver.add_theory_lemma(vec![x0.negated()]);
                    injected = true;
                }
                TheoryPropResult::Continue
            })
            .into_inner();

        assert!(injected, "the scoped callback must inject its global unit");
        assert!(
            scoped_result.is_unsat(),
            "the active scope requires x0 while the theory unit requires !x0 \
             (chrono={chrono_enabled})",
        );
        assert!(solver.pop());

        let base_result = solver.solve().into_inner();
        let model = match base_result {
            SatResult::Sat(model) => model,
            other => panic!(
                "after pop the base formula plus global theory unit must be SAT \
                 (chrono={chrono_enabled}), got {other:?}",
            ),
        };
        assert!(
            !model[x0.variable().index()],
            "the unscoped theory unit must survive pop (chrono={chrono_enabled})",
        );
        assert_eq!(
            solver.var_level(x0.variable()),
            Some(0),
            "the surviving theory unit must remain a root fact (chrono={chrono_enabled})",
        );
    }
}

#[test]
fn test_plain_theory_unit_and_multi_clause_survive_pop() {
    let x0 = Literal::positive(Variable(0));

    let mut unit_solver = Solver::new(1);
    unit_solver.push();
    let unit_ref = unit_solver
        .add_theory_lemma(vec![x0.negated()])
        .expect("plain theory unit");
    assert_eq!(unit_solver.arena.scope_lim(unit_ref.index()), 0);
    assert!(unit_solver.pop());
    assert!(
        unit_solver.arena.is_active(unit_ref.index()),
        "plain theory unit must not be collected with the surrounding user scope",
    );
    let unit_model = match unit_solver.solve().into_inner() {
        SatResult::Sat(model) => model,
        other => panic!("global theory unit should remain satisfiable after pop, got {other:?}"),
    };
    assert!(!unit_model[x0.variable().index()]);

    let mut clause_solver = Solver::new(2);
    let x1 = Literal::positive(Variable(1));
    clause_solver.push();
    let clause_ref = clause_solver
        .add_theory_lemma(vec![x0.negated(), x1.negated()])
        .expect("plain multi-literal theory clause");
    assert_eq!(clause_solver.arena.scope_lim(clause_ref.index()), 0);
    assert!(clause_solver.pop());
    assert!(
        clause_solver.arena.is_active(clause_ref.index()),
        "plain multi-literal theory clause must survive pop",
    );
    clause_solver.qhead = clause_solver.trail.len();
    clause_solver.decide(x0);
    assert_eq!(
        clause_solver.propagate(),
        None,
        "surviving global theory clause should propagate rather than conflict",
    );
    assert_eq!(
        clause_solver.lit_value(x1),
        Some(false),
        "the live global clause (!x0 | !x1) must propagate !x1 after deciding x0",
    );
}

#[test]
fn test_queued_theory_unit_preserves_clause_trace_id() {
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();
    let decision = Literal::positive(Variable(0));
    let unit = Literal::positive(Variable(1));
    solver.decide(decision);
    solver.qhead = solver.trail.len();

    let unit_ref = solver
        .add_theory_lemma(vec![unit])
        .expect("queued clause-trace theory unit");
    let clause_id = solver.clause_id(unit_ref);
    assert_ne!(clause_id, 0);
    assert_eq!(
        solver.unit_proof_id[unit.variable().index()],
        clause_id,
        "clause-trace mode has no separate proof-manager addition ID",
    );

    assert_eq!(solver.take_live_pending_theory_conflict(), Some(unit_ref),);
    solver.analyze_and_backtrack(unit_ref, "clause-trace theory unit", |_, _| {});
    assert_eq!(
        solver.unit_proof_id[unit.variable().index()],
        clause_id,
        "root installation must retain the arena ID recorded in the clause trace",
    );
}

#[test]
fn test_queued_theory_unit_preserves_lrat_axiom_id_fallback() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);
    let decision = Literal::positive(Variable(0));
    let unit = Literal::positive(Variable(1));
    solver.decide(decision);
    solver.qhead = solver.trail.len();

    let unit_ref = solver
        .add_theory_lemma(vec![unit])
        .expect("queued LRAT Axiom theory unit");
    let clause_id = solver.clause_id(unit_ref);
    assert_ne!(clause_id, 0);
    assert_eq!(
        solver.unit_proof_id[unit.variable().index()],
        clause_id,
        "suppressed LRAT Axiom emission returns zero, so provenance falls back to the arena ID",
    );

    assert_eq!(solver.take_live_pending_theory_conflict(), Some(unit_ref),);
    solver.analyze_and_backtrack(unit_ref, "LRAT Axiom theory unit", |_, _| {});
    assert_eq!(
        solver.unit_proof_id[unit.variable().index()],
        clause_id,
        "root installation must preserve the LRAT Axiom fallback ID",
    );
}

#[test]
fn test_queued_theory_unit_preserves_hidden_lrat_trusted_transform_id() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);
    solver.set_extension_trusted_lemmas(true);
    let decision = Literal::positive(Variable(0));
    let unit = Literal::positive(Variable(1));
    solver.decide(decision);
    solver.qhead = solver.trail.len();

    let unit_ref = solver
        .add_theory_lemma(vec![unit])
        .expect("queued LRAT TrustedTransform theory unit");
    let clause_id = solver.clause_id(unit_ref);
    let emitted_id = solver.unit_proof_id[unit.variable().index()];
    assert_ne!(clause_id, 0);
    assert_ne!(emitted_id, 0);
    assert_ne!(
        emitted_id, clause_id,
        "hidden LRAT TrustedTransform additions reserve a distinct proof-manager ID",
    );
    assert!(
        !solver.lrat_hint_id_visible(emitted_id),
        "the distinct TrustedTransform ID must remain hidden from serialized LRAT hints",
    );

    assert_eq!(solver.take_live_pending_theory_conflict(), Some(unit_ref),);
    solver.analyze_and_backtrack(unit_ref, "LRAT TrustedTransform theory unit", |_, _| {});
    assert_eq!(
        solver.unit_proof_id[unit.variable().index()],
        emitted_id,
        "root installation must not replace the hidden emitted ID with the arena ID",
    );
}

#[test]
fn test_pending_theory_conflict_tail_defers_flush_until_drained() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    for decision in [x0, x1, x2] {
        solver.decide(decision);
        solver.qhead = solver.trail.len();
    }

    let head = solver
        .add_theory_lemma(vec![x1.negated(), x2.negated()])
        .expect("head all-false theory lemma");
    let tail = solver
        .add_theory_lemma(vec![x0.negated(), x1.negated()])
        .expect("tail all-false theory lemma");
    let tail_idx = tail.index();
    let deletable_lbd = solver.tiers.tier2_lbd[0].saturating_add(1);
    solver.arena.set_lbd(head.index(), deletable_lbd);
    solver.arena.set_lbd(tail_idx, deletable_lbd);
    solver.cold.next_flush = 0;

    assert_eq!(solver.take_live_pending_theory_conflict(), Some(head));
    solver.analyze_and_backtrack(head, "queued theory head", |_, _| {});

    let reductions_before = solver.cold.num_reductions;
    assert!(!solver.should_reduce_db());
    solver.reduce_db();
    assert_eq!(
        solver.cold.num_reductions, reductions_before,
        "flush must be deferred while a queued tail owns a ClauseRef",
    );
    assert!(
        solver.arena.is_active(tail_idx),
        "the tail must survive the deferred flush",
    );
    assert_eq!(
        solver.take_live_pending_theory_conflict(),
        Some(tail),
        "the queued tail must remain available for conflict analysis",
    );
    solver.analyze_and_backtrack(tail, "queued theory tail", |_, _| {});

    solver.reduce_db();
    assert_eq!(
        solver.cold.num_reductions,
        reductions_before + 1,
        "reduction may resume after the final queued conflict is consumed",
    );
    assert!(
        solver.arena.is_active(tail_idx),
        "the analyzed tail is now a live reason and remains protected",
    );
}

#[test]
fn test_deleted_pending_ref_is_not_vacuously_live() {
    let mut solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    for decision in [x0, x1] {
        solver.decide(decision);
        solver.qhead = solver.trail.len();
    }
    let conflict_ref = solver
        .add_theory_lemma(vec![x0.negated(), x1.negated()])
        .expect("all-false theory lemma");

    // Model a stale ClauseRef left by any deletion path that bypassed the
    // queue-owner guard. ClauseArena::delete leaves an empty arena slot, and
    // `Iterator::all` over that empty literal slice must not revive it.
    solver.arena.delete(conflict_ref.index());

    assert_eq!(
        solver.take_live_pending_theory_conflict(),
        None,
        "an inactive arena slot is not a live conflict",
    );
}

#[test]
fn test_stale_pending_head_cannot_hide_a_later_live_conflict() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    for decision in [x0, x1, x2] {
        solver.decide(decision);
        solver.qhead = solver.trail.len();
    }

    let stale_after_backtrack = solver
        .add_theory_lemma(vec![x0.negated(), x2.negated()])
        .expect("conflict that becomes stale");
    let still_live = solver
        .add_theory_lemma(vec![x0.negated(), x1.negated()])
        .expect("conflict that remains live");
    assert_ne!(stale_after_backtrack, still_live);

    solver.backtrack(2);
    assert_eq!(solver.lit_value(x2), None);
    assert_eq!(solver.lit_value(x0), Some(true));
    assert_eq!(solver.lit_value(x1), Some(true));

    assert_eq!(
        solver.take_live_pending_theory_conflict(),
        Some(still_live),
        "stale queue heads must be drained before BCP or a new decision",
    );
    assert!(
        solver.pending_theory_conflicts.is_empty(),
        "the stale head and returned live conflict must both be consumed",
    );
}

#[test]
fn test_nonchrono_fifo_conflict_below_current_level_researches_safely() {
    let mut solver = Solver::new(3);
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    solver.set_chrono_enabled(false);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    assert!(solver.add_clause(vec![x0, x1, x2]));
    for lit in [x0, x1, x2] {
        solver.set_phase(lit.variable(), true);
    }

    let mut injected = false;
    let result = solver
        .solve_with_theory(|solver| {
            if !injected && solver.current_decision_level() == 3 {
                solver.add_theory_lemma(vec![x0.negated(), x1.negated()]);
                solver.add_theory_lemma(vec![x0.negated(), x2.negated()]);
                solver.add_theory_lemma(vec![x2.negated()]);
                injected = true;
            }
            TheoryPropResult::Continue
        })
        .into_inner();

    assert!(
        injected,
        "the callback must create the FIFO batch at level 3"
    );
    let model = match result {
        SatResult::Sat(model) => model,
        other => panic!("non-chrono fallback should re-search to SAT, got {other:?}"),
    };
    assert!(
        !model[0] || !model[1],
        "model must satisfy the lower-level head theory lemma",
    );
    assert!(
        !model[0] || !model[2],
        "model must satisfy the queued tail theory lemma",
    );
    assert!(
        !model[2],
        "a tail unit made unassigned by the head's root fallback must be installed, not reported UNSAT",
    );
}

#[test]
fn test_lazy_reason_materialization_rejects_literals_above_survivor_level() {
    use crate::extension::{ExtPropagateResult, Extension, SolverContext};

    struct StaleAfterBacktrackExtension {
        reason_lit: Literal,
    }

    impl Extension for StaleAfterBacktrackExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn explain_lazy_reason(
            &mut self,
            propagated: Literal,
            _reason_data: u64,
        ) -> Option<Vec<Literal>> {
            Some(vec![propagated, self.reason_lit])
        }
    }

    let mut solver = Solver::new(2);
    let propagated = Literal::positive(Variable(0));
    let higher_level_reason = Literal::negative(Variable(1));

    solver.decision_level = 1;
    solver.trail_lim.push(0);
    solver.add_lazy_theory_propagation(propagated, 7);

    solver.decision_level = 2;
    solver.trail_lim.push(solver.trail.len());
    solver.enqueue(higher_level_reason.negated(), None);

    let mut ext = StaleAfterBacktrackExtension {
        reason_lit: higher_level_reason,
    };
    solver.materialize_lazy_reasons_through_level_for_backtrack(&mut ext, 1);

    let propagated_data = solver.var_data[propagated.variable().index()];
    assert!(
        !propagated_data.is_lazy_theory_reason(),
        "failed materialization must clear the lazy reason flag"
    );
    assert_eq!(
        propagated_data.reason, NO_REASON,
        "surviving assignment must not point at a reason with level-2 literals"
    );
    assert_eq!(
        solver.arena.num_clauses(),
        0,
        "stale materialized reason clause must not enter the clause DB"
    );
    assert!(
        solver.cold.lazy_materialization_failed,
        "target-level materialization failure must force conflict analysis to bail"
    );

    solver.backtrack(1);
    assert!(solver.var_is_assigned(propagated.variable().index()));
    assert!(!solver.var_is_assigned(higher_level_reason.variable().index()));
}

#[test]
fn test_lazy_reason_materialization_rejects_literals_above_propagation_level() {
    use crate::extension::{ExtPropagateResult, Extension, SolverContext};

    struct HigherLevelReasonExtension {
        reason_lit: Literal,
    }

    impl Extension for HigherLevelReasonExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }

        fn explain_lazy_reason(
            &mut self,
            propagated: Literal,
            _reason_data: u64,
        ) -> Option<Vec<Literal>> {
            Some(vec![propagated, self.reason_lit])
        }
    }

    let mut solver = Solver::new(2);
    let propagated = Literal::positive(Variable(0));
    let higher_level_reason = Literal::negative(Variable(1));

    solver.decision_level = 1;
    solver.trail_lim.push(0);
    solver.add_lazy_theory_propagation(propagated, 7);

    solver.decision_level = 2;
    solver.trail_lim.push(solver.trail.len());
    solver.enqueue(higher_level_reason.negated(), None);

    let mut ext = HigherLevelReasonExtension {
        reason_lit: higher_level_reason,
    };
    solver.materialize_lazy_reasons_through_level_for_backtrack(&mut ext, 2);

    let propagated_data = solver.var_data[propagated.variable().index()];
    assert_eq!(
        propagated_data.reason, NO_REASON,
        "level-1 propagation must not get a reason depending on level-2 literals"
    );
    assert!(
        !solver.cold.lazy_materialization_failed,
        "lower-level demotion must not poison current level-2 analysis"
    );
    assert_eq!(solver.arena.num_clauses(), 0);
}

#[test]
fn test_add_theory_lemma_scoped_conflicts_immediately_and_pops_8785() {
    let mut solver = Solver::new(2);
    let p = Literal::positive(Variable(0));
    let q = Literal::positive(Variable(1));

    solver.push();
    assert!(solver.add_clause(vec![p.negated()]));
    assert!(solver.add_clause(vec![q]));
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));

    let added = solver
        .add_theory_lemma_scoped(vec![p, q.negated()])
        .expect("scoped theory lemma should enter the watched theory path");
    assert!(
        solver.solve().into_inner().is_unsat(),
        "already-falsified scoped theory lemma must block the cached assignment"
    );

    assert!(solver.pop());
    assert!(
        !solver.arena.is_active(added.index()),
        "the selector-guarded scoped wrapper must still be reclaimed after pop",
    );
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "scoped theory lemma must be disabled after pop"
    );
}

// =========================================================================
// Unit theory lemma regression tests (#6242)
// =========================================================================
//
// Before the fix, a unit theory lemma whose literal conflicts with a
// decision at level > 0 would falsely mark the empty clause (UNSAT).
// After the fix, it returns a conflict clause for backtracking.

/// Regression test for #6242: unit theory lemma at level > 0 conflicting
/// with current assignment must return a conflict clause, not declare UNSAT.
#[test]
fn test_unit_theory_lemma_conflict_at_nonzero_level_returns_conflict_6242() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    // Add a satisfiable formula: (x0 v x1) ^ (x0 v x2) ^ (~x1 v x2)
    assert!(solver.add_clause(vec![x0, x1]));
    assert!(solver.add_clause(vec![x0, x2]));
    assert!(solver.add_clause(vec![x1.negated(), x2]));

    // Decide x0 = true at level 1
    solver.decide(x0);
    solver.qhead = solver.trail.len();
    assert_eq!(solver.decision_level, 1, "should be at decision level 1");

    // Now add a unit theory lemma ~x0 that conflicts with the decision.
    // Before fix: mark_empty_clause() + return None (false UNSAT).
    // After fix: returns Some(clause_ref) as a conflict for backtracking.
    let result = solver.add_theory_lemma(vec![x0.negated()]);
    assert!(
        result.is_some(),
        "unit theory lemma conflicting at level > 0 must return conflict clause"
    );
    assert!(
        !solver.has_empty_clause(),
        "must NOT mark empty clause at level > 0 — backtracking should resolve the conflict"
    );
}

/// Regression test for #6242: unit theory lemma at level 0 that conflicts
/// with a root-level assignment should correctly declare UNSAT.
#[test]
fn test_unit_theory_lemma_conflict_at_level0_marks_unsat_6242() {
    let mut solver = Solver::new(1);
    let x0 = Literal::positive(Variable(0));

    // Add a unit clause that forces x0 = true at level 0
    assert!(solver.add_clause(vec![x0]));
    // Process initial clauses to propagate x0 = true at level 0
    let conflict = solver.process_initial_clauses();
    assert!(conflict.is_none(), "no conflict from initial clauses");
    assert_eq!(solver.decision_level, 0, "should be at level 0");

    // Add a contradictory unit theory lemma ~x0 at level 0
    let result = solver.add_theory_lemma(vec![x0.negated()]);
    assert!(
        result.is_none(),
        "unit theory lemma conflicting at level 0 must return None"
    );
    assert!(
        solver.has_empty_clause(),
        "must mark empty clause at level 0 — no backtracking possible"
    );
}

/// Regression test for #6242: unit theory lemma enqueued at level > 0
/// should use reason=None to avoid length-1 reason clause in conflict analysis.
#[test]
fn test_unit_theory_lemma_enqueue_uses_reason_none_6242() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    // Add clauses so we have something to work with
    assert!(solver.add_clause(vec![x0, x1]));

    // Decide x0 = true at level 1
    solver.decide(x0);
    solver.qhead = solver.trail.len();

    // Add a unit theory lemma for x1 (unassigned variable)
    let result = solver.add_theory_lemma(vec![x1]);
    assert!(
        result.is_some(),
        "unit theory lemma for unassigned var should return clause ref"
    );

    // x1 should now be on the trail
    assert_eq!(
        solver.lit_value(x1),
        Some(true),
        "x1 should be assigned true after unit theory lemma"
    );

    // The reason for x1 should be None (not the length-1 clause)
    let reason = solver.var_reason(x1.variable().index());
    assert!(
        reason.is_none(),
        "unit theory lemma must enqueue with reason=None (#6242)"
    );
}

// =========================================================================
// add_theory_propagation unit tests (P1:130)
// =========================================================================
//
// Tests for the lightweight theory propagation path that skips watch setup.
// Covers: empty clause, already-true (redundant), already-false (conflict
// fallback), normal enqueue, and propagated-literal position swap.

/// Empty clause input returns None and adds nothing.
#[test]
fn test_add_theory_propagation_empty_clause_returns_none() {
    let mut solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    assert!(
        solver.add_theory_propagation(vec![], x0).is_none(),
        "empty clause must return None"
    );
    assert_eq!(solver.trail.len(), 0, "nothing should be enqueued");
}

/// When the propagated literal is already true, propagation is redundant.
/// The method should return None without enqueuing or adding a clause.
#[test]
fn test_add_theory_propagation_already_true_is_redundant() {
    let mut solver = Solver::new(3);
    let x0_pos = Literal::positive(Variable(0));
    let x1_neg = Literal::negative(Variable(1));

    // Decide x0 = true so it's already assigned true
    solver.decide(x0_pos);
    // Advance qhead so decide's debug_assert about pending propagations is satisfied
    // for subsequent operations. In the real solver, BCP runs after decide.
    solver.qhead = solver.trail.len();

    let clauses_before = solver.arena.num_clauses();
    let result = solver.add_theory_propagation(vec![x0_pos, x1_neg], x0_pos);
    assert!(
        result.is_none(),
        "already-true literal should be skipped (redundant)"
    );
    assert_eq!(
        solver.arena.num_clauses(),
        clauses_before,
        "no clause should be added for redundant propagation"
    );
}

/// When the propagated literal is already false, the method falls back to
/// add_theory_lemma for proper conflict handling.
#[test]
fn test_add_theory_propagation_already_false_falls_back_to_lemma() {
    let mut solver = Solver::new(3);
    let x0_pos = Literal::positive(Variable(0));
    let x0_neg = Literal::negative(Variable(0));
    let x1_neg = Literal::negative(Variable(1));

    // Decide x0 = true, making x0_neg (the negation) already assigned false.
    solver.decide(x0_pos);
    solver.qhead = solver.trail.len();

    // Try to propagate x0_neg (which is false). This should fall back to
    // add_theory_lemma which handles the conflict clause properly.
    let result = solver.add_theory_propagation(vec![x0_neg, x1_neg], x0_neg);
    // add_theory_lemma returns Some for non-tautological clauses with watches
    assert!(
        result.is_some(),
        "already-false literal should fall back to add_theory_lemma (conflict)"
    );
}

/// Normal case: propagated literal is unassigned, reason literals are falsified.
/// The literal should be enqueued on the trail with a reason clause.
#[test]
fn test_add_theory_propagation_enqueues_unassigned_literal() {
    let mut solver = Solver::new(3);
    let x0_pos = Literal::positive(Variable(0));
    let x1_pos = Literal::positive(Variable(1));
    let x1_neg = Literal::negative(Variable(1));
    // Decide x1 = false (so x1_neg is true, meaning the reason ¬x1_neg = x1_pos is false).
    // Actually: we decide x1_neg (x1 = false). The reason literal in the clause
    // is ¬reason = x1_pos, which needs to be falsified. Since x1 is false, x1_pos
    // has val < 0 (false), which means it's falsified. But the convention is:
    // clause = [propagated, ¬reason1, ¬reason2, ...], and ¬reason1 must be falsified
    // under current assignment. So if we decided x1_neg, then x1_neg has val > 0
    // and x1_pos has val < 0, so x1_pos in the clause is indeed falsified.
    solver.decide(x1_neg);
    solver.qhead = solver.trail.len();

    let trail_before = solver.trail.len();
    // Clause: [x0_pos, x1_pos] means "x0 because ¬x1", reason is x1_pos (falsified).
    let result = solver.add_theory_propagation(vec![x0_pos, x1_pos], x0_pos);
    assert!(
        result.is_some(),
        "should return clause ref for successful propagation"
    );
    assert_eq!(
        solver.trail.len(),
        trail_before + 1,
        "propagated literal should be on the trail"
    );
    assert_eq!(
        solver.trail[trail_before], x0_pos,
        "enqueued literal should be the propagated one"
    );
    // Verify the literal is assigned true
    assert!(
        solver.vals[x0_pos.index()] > 0,
        "propagated literal should be assigned true"
    );
    // Verify watches ARE set up (#6262: without watches, BCP cannot
    // rediscover the clause after backtracking undoes the propagation).
    let clause_ref = result.unwrap();
    assert_eq!(
        solver.watches.count_watches_for_clause(clause_ref),
        2,
        "add_theory_propagation should set up watches on clause[0] and clause[1]"
    );
}

/// When the propagated literal is not at position 0, the method swaps it.
#[test]
fn test_add_theory_propagation_swaps_propagated_to_position_zero() {
    let mut solver = Solver::new(3);
    let x0_pos = Literal::positive(Variable(0));
    let x1_neg = Literal::negative(Variable(1));
    let x2_pos = Literal::positive(Variable(2));

    // Falsify the reason literals. Decide x1 = true (so x1_neg is falsified)
    // and decide x2 = false (so x2_pos is falsified, wait no... if x2 = false
    // then x2_pos has val < 0, which means x2_pos is falsified. But we need
    // both reason lits falsified, and x0 unassigned.)
    solver.decide(Literal::positive(Variable(1)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();

    // Clause with propagated literal NOT at position 0:
    // [x1_neg, x0_pos, x2_pos] where x0_pos is the propagated literal
    // x1_neg is falsified (x1 = true), x2_pos is falsified (x2 = false)
    let result = solver.add_theory_propagation(vec![x1_neg, x0_pos, x2_pos], x0_pos);
    assert!(
        result.is_some(),
        "should succeed after swapping propagated to position 0"
    );
    // Verify x0 was enqueued
    assert!(
        solver.vals[x0_pos.index()] > 0,
        "x0 should be assigned true after propagation"
    );
}

/// Variable out of range returns None.
#[test]
fn test_add_theory_propagation_out_of_range_variable_returns_none() {
    let mut solver = Solver::new(2);
    // Variable(5) is out of range for a 2-variable solver
    let out_of_range = Literal::positive(Variable(5));
    let x0_pos = Literal::positive(Variable(0));
    let result = solver.add_theory_propagation(vec![out_of_range, x0_pos], out_of_range);
    assert!(result.is_none(), "out-of-range variable should return None");
}

/// Duplicate literals in a theory propagation clause must be deduped (#6506).
/// Without dedup, the 2WL scheme panics on duplicate watch pointers when
/// `initialize_watches` re-attaches watches during incremental re-solves.
#[test]
fn test_add_theory_propagation_dedup_duplicate_reason_literals_6506() {
    let mut solver = Solver::new(4);
    let x0_pos = Literal::positive(Variable(0));
    let x1_pos = Literal::positive(Variable(1));
    let x2_pos = Literal::positive(Variable(2));

    // Decide x1=true and x2=true so their positive literals have val > 0.
    // The reason literals x1_pos and x2_pos in the clause must be falsified,
    // so we need x1_pos to be false. Decide x1_neg (x1=false) instead.
    // Actually: reason literals are the negated reasons. The clause format is
    // [propagated, reason1, reason2, ...] where reason_i must be falsified.
    // So we need x1_pos (val < 0) meaning x1 = false. Decide x1=true → x1_pos
    // has val > 0, x1_neg has val < 0. For x1_pos to be falsified we need x1=false.
    solver.decide(Literal::negative(Variable(1)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    // Now: x1 = false → x1_pos has val < 0 (falsified). x2 = false → x2_pos has val < 0.

    // Clause with duplicate reason literal: [x0_pos, x1_pos, x2_pos, x1_pos]
    // After dedup this should become [x0_pos, x1_pos, x2_pos] and propagate x0.
    let result = solver.add_theory_propagation(vec![x0_pos, x1_pos, x2_pos, x1_pos], x0_pos);
    assert!(
        result.is_some(),
        "clause with duplicate reason should still propagate"
    );
    // The propagated literal should be on the trail.
    assert!(
        solver.vals[x0_pos.index()] > 0,
        "propagated literal should be assigned true after dedup"
    );
}

/// Binary clause with identical literals must be handled gracefully (#6506).
#[test]
fn test_add_theory_propagation_binary_duplicate_becomes_unit_6506() {
    let mut solver = Solver::new(2);
    let x0_pos = Literal::positive(Variable(0));
    // Binary clause [x0, x0] — both literals identical.
    let result = solver.add_theory_propagation(vec![x0_pos, x0_pos], x0_pos);
    assert!(
        result.is_some(),
        "binary duplicate clause should be accepted as unit"
    );
    assert!(
        solver.vals[x0_pos.index()] > 0,
        "propagated literal should be assigned true"
    );
}

/// Theory propagations must survive reset_search_state() watch rebuilds (#6506).
#[test]
fn test_add_theory_propagation_reinitializes_distinct_watches_after_reset_6506() {
    let mut solver = Solver::new(4);
    let x0_pos = Literal::positive(Variable(0));
    let x1_pos = Literal::positive(Variable(1));
    let x2_pos = Literal::positive(Variable(2));

    // Reason literals must be falsified for direct theory propagation.
    solver.decide(Literal::negative(Variable(1)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();

    let clause_ref = solver
        .add_theory_propagation(vec![x0_pos, x1_pos, x2_pos, x1_pos], x0_pos)
        .expect("duplicate theory reasons should still yield a learned clause");
    let clause_idx = clause_ref.0 as usize;
    assert_eq!(
        solver.arena.literals(clause_idx),
        &[x0_pos, x1_pos, x2_pos],
        "the stored reason clause should be deduplicated before later watch rebuilds",
    );
    assert_watch_invariant_for_all_active_clauses(&solver, "add_theory_propagation_initial");

    solver.reset_search_state();
    solver.initialize_watches();

    assert_watch_invariant_for_all_active_clauses(&solver, "add_theory_propagation_after_reset");
}

// ========================================================================
// Theory Callback / Solve-with-Theory Tests
// ========================================================================

/// Regression test for #3343: solve_with_theory must invoke the theory callback
/// even when scope_selectors are non-empty (scoped solving via push/pop).
#[test]
fn test_solve_with_theory_invokes_callback_with_scope_selectors() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let call_count = AtomicUsize::new(0);

    let mut solver = Solver::new(2);
    // (x0 OR x1)
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.push(); // creates scope_selector, forcing assumption-based path

    let result = solver
        .solve_with_theory(|_| {
            call_count.fetch_add(1, Ordering::Relaxed);
            TheoryPropResult::Continue
        })
        .into_inner();

    assert!(
        matches!(result, SatResult::Sat(_)),
        "scoped theory solve should return SAT"
    );
    assert!(
        call_count.load(Ordering::Relaxed) > 0,
        "theory callback must be invoked at least once with active scope selectors"
    );
}

/// Regression test for #3343: theory conflict clause via solve_with_theory
/// under scoped solving causes UNSAT.
#[test]
fn test_solve_with_theory_conflict_with_scope_selectors() {
    let mut solver = Solver::new(2);
    // (x0) AND (x1)
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    solver.push();

    // Empty conflict clause => immediate UNSAT
    let mut sent_conflict = false;
    let result = solver
        .solve_with_theory(|_| {
            if !sent_conflict {
                sent_conflict = true;
                TheoryPropResult::Conflict(vec![])
            } else {
                TheoryPropResult::Continue
            }
        })
        .into_inner();

    assert!(
        matches!(result, SatResult::Unsat(_)),
        "empty theory conflict clause should produce UNSAT"
    );
}

/// Regression test for #3812: non-empty theory conflict clause must set up
/// watches via add_theory_lemma so the clause participates in BCP.
/// Before the fix, add_clause was used which skips watch setup, causing the
/// conflict clause to be silently ignored and potentially producing wrong SAT.
#[test]
fn test_theory_conflict_nonempty_clause_has_watches() {
    // Create a SAT formula: (x0 v x1) AND (x0 v x2) AND (¬x0 v x3) AND (¬x3 v x4)
    // This is satisfiable (e.g., x0=true, x3=true, x4=true).
    // The theory callback will inject a conflict clause (¬x0 v ¬x3) AND then (¬x0)
    // to force UNSAT via a non-empty conflict clause.
    let mut solver = Solver::new(5);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(3)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(4)),
    ]);

    let conflict_count = std::cell::Cell::new(0);
    let result = solver
        .solve_with_theory(|_s| {
            let count = conflict_count.get();
            conflict_count.set(count + 1);
            match count {
                0 => {
                    // First call: inject (¬x0 v ¬x3) — this clause MUST get watches
                    TheoryPropResult::Conflict(vec![
                        Literal::negative(Variable(0)),
                        Literal::negative(Variable(3)),
                    ])
                }
                1 => {
                    // Second call: inject unit clause (¬x0)
                    TheoryPropResult::Conflict(vec![Literal::negative(Variable(0))])
                }
                2 => {
                    // Third call: inject (¬x1) to block x0=false,x1=true branch
                    TheoryPropResult::Conflict(vec![Literal::negative(Variable(1))])
                }
                3 => {
                    // Fourth call: inject (¬x2) to block remaining branches
                    TheoryPropResult::Conflict(vec![Literal::negative(Variable(2))])
                }
                _ => TheoryPropResult::Continue,
            }
        })
        .into_inner();

    // The theory injected enough conflict clauses to force UNSAT.
    // Without watches, these clauses would be silently ignored and the solver
    // would incorrectly return SAT.
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "non-empty theory conflict clauses must participate in BCP; got {result:?}"
    );
}

/// Level-0 theory conflicts must preserve empty-clause resolution hints in the
/// SMT clause trace so SatProofManager can replay the contradiction.
#[test]
fn test_level0_theory_unit_conflict_trace_has_hints() {
    let mut solver = Solver::new(1);
    solver.enable_clause_trace();
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let mut sent_conflict = false;
    let result = solver
        .solve_with_theory(|_| {
            if !sent_conflict {
                sent_conflict = true;
                TheoryPropResult::Conflict(vec![Literal::negative(Variable(0))])
            } else {
                TheoryPropResult::Continue
            }
        })
        .into_inner();
    assert!(matches!(result, SatResult::Unsat(_)));

    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    let empty_entry = trace
        .entries()
        .last()
        .expect("trace has empty clause entry");
    assert!(
        empty_entry.clause.is_empty(),
        "expected final empty clause entry"
    );
    assert_eq!(
        empty_entry.resolution_hints,
        vec![2, 1],
        "empty clause must preserve theory-clause + root-fact provenance"
    );
}

// ========================================================================
// Extension Stop / Theory Stop / Unknown Reason Tests
// ========================================================================

//
// These tests verify both the `SatResult::Unknown` result and the structured
// `last_unknown_reason()` side-channel classification.
// =============================================================================

/// Verify that `last_unknown_reason()` returns `Interrupted` after the
/// interrupt callback fires during `solve_interruptible`.
#[test]
fn test_unknown_reason_interrupted_after_callback() {
    use crate::SatUnknownReason;

    const NUM_VARS: usize = 2000;
    let mut solver = Solver::new(NUM_VARS);
    solver.set_preprocess_enabled(false);
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let result = solver.solve_interruptible(|| true).into_inner();

    assert_eq!(result, SatResult::Unknown);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted),
        "solve_interruptible returning Unknown must set reason to Interrupted"
    );
}

/// Extension that returns ExtCheckResult::Unknown on final check.
/// This tests the extension-unknown path (solve.rs line 334/520).
#[test]
fn test_unknown_from_extension_check_unknown() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_unknown_extension_check.jsonl");

    struct AlwaysUndecidedExtension;
    impl Extension for AlwaysUndecidedExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult::none()
        }
        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Unknown
        }
        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            false
        }
    }

    let mut solver = Solver::new(2);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    let mut ext = AlwaysUndecidedExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert_eq!(
        result,
        SatResult::Unknown,
        "extension returning Unknown on check() must propagate to SatResult::Unknown"
    );
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ExtensionUnknown),
        "extension check Unknown must classify as ExtensionUnknown"
    );

    let events = read_diagnostic_trace(&diag_path);
    assert_single_unknown_result_summary_with_reason(&events, "extension_unknown");
}

/// Extension stop requests must produce Unknown even on the empty-formula init path.
#[test]
fn test_unknown_from_extension_stop_with_empty_formula() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};

    struct StopOnInitExtension;

    impl Extension for StopOnInitExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            ExtPropagateResult {
                clauses: vec![],
                propagations: vec![],
                lazy_propagations: vec![],
                conflict: None,
                stop: true,
                bump_vars: vec![],
            }
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir
        .path()
        .join("diag_unknown_extension_stop_empty_formula.jsonl");
    let mut solver = Solver::new(1);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();

    let mut ext = StopOnInitExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert_eq!(
        result,
        SatResult::Unknown,
        "extension stop must return Unknown even before any SAT clauses exist"
    );
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::TheoryStop),
        "extension stop must classify as TheoryStop"
    );

    let events = read_diagnostic_trace(&diag_path);
    assert_single_unknown_result_summary_with_reason(&events, "theory_stop");
}

/// Extension that returns an empty conflict clause on propagation.
/// An empty conflict clause = derivation of the empty clause = UNSAT.
/// The extension proved a genuine contradiction. Fixes #5885.
#[test]
fn test_unsat_from_extension_empty_conflict() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};

    struct EmptyConflictExtension {
        fired: bool,
    }
    impl Extension for EmptyConflictExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            if !self.fired {
                self.fired = true;
                ExtPropagateResult {
                    clauses: vec![],
                    propagations: vec![],
                    lazy_propagations: vec![],
                    conflict: Some(vec![]), // empty conflict = contradiction
                    stop: false,
                    bump_vars: vec![],
                }
            } else {
                ExtPropagateResult::none()
            }
        }
        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }
        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            !self.fired
        }
    }

    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    let mut ext = EmptyConflictExtension { fired: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        result.is_unsat(),
        "empty conflict clause from extension = UNSAT (#5885)"
    );
}

/// A level-0 contradiction found by extension lemmas must not be masked by stop.
#[test]
fn test_extension_stop_does_not_mask_level0_unsat() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};

    struct ContradictingStopExtension {
        fired: bool,
    }

    impl Extension for ContradictingStopExtension {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            if self.fired {
                return ExtPropagateResult::none();
            }
            self.fired = true;
            ExtPropagateResult {
                clauses: vec![vec![Literal::negative(Variable(0))]],
                propagations: vec![],
                lazy_propagations: vec![],
                conflict: None,
                stop: true,
                bump_vars: vec![],
            }
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            !self.fired
        }
    }

    let mut solver = Solver::new(1);
    solver.add_clause(vec![Literal::positive(Variable(0))]);

    let mut ext = ContradictingStopExtension { fired: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        result.is_unsat(),
        "extension stop must not hide a level-0 contradiction introduced by theory lemmas"
    );
    assert_eq!(
        solver.last_unknown_reason(),
        None,
        "level-0 contradiction should resolve as UNSAT, not Unknown"
    );
}

/// Theory callback returning Stop must produce SatResult::Unknown.
/// This tests the theory-stop path (solve.rs line 231).
#[test]
fn test_unknown_from_theory_stop() {
    let dir = tempfile::tempdir().expect("tempdir");
    let diag_path = dir.path().join("diag_unknown_theory_stop.jsonl");
    let mut solver = Solver::new(2);
    solver
        .enable_diagnostic_trace(diag_path.to_str().expect("utf8 path"))
        .unwrap();
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    let result = solver.solve_with_theory(|_solver| TheoryPropResult::Stop);
    assert_eq!(
        result,
        SatResult::Unknown,
        "TheoryPropResult::Stop must produce SatResult::Unknown"
    );
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::TheoryStop),
        "theory stop callback must classify as TheoryStop"
    );

    let events = read_diagnostic_trace(&diag_path);
    assert_single_unknown_result_summary_with_reason(&events, "theory_stop");
}

/// Theory callback returning empty conflict clause -> UNSAT.
/// Note: the theory path (solve_no_assumptions_with_theory) treats an empty
/// conflict as definitive UNSAT via declare_unsat(). The extension path
/// (solve_no_assumptions_with_extension) treats it as Unknown (#3826 soundness
/// guard). This asymmetry is documented here for #4622 review.
#[test]
fn test_theory_empty_conflict_declares_unsat() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);

    let fired = std::cell::Cell::new(false);
    let result = solver.solve_with_theory(|_solver| {
        if !fired.get() {
            fired.set(true);
            TheoryPropResult::Conflict(vec![]) // empty conflict -> UNSAT in theory path
        } else {
            TheoryPropResult::Continue
        }
    });
    assert!(
        result.is_unsat(),
        "empty conflict clause from theory callback declares UNSAT (not Unknown)"
    );
}

/// Regression test for #4631: probe failed-literal must store unit_proof_id
/// so that subsequent LRAT chain collection can reference the derived unit.
///
/// Exercises the exact code path in `probe()` at inprocessing.rs:1304-1312:
/// decide probe literal -> BCP conflict -> UIP -> proof_emit -> store unit_proof_id.
#[test]
fn test_probe_failed_literal_stores_unit_proof_id() {
    use crate::probe::find_failed_literal_uip;

    // Formula: (x0 | x1), (x0 | !x1)
    // Probing !x0 at level 1: x0=false falsifies first literal in both clauses,
    // BCP forces x1=true (clause 1) then x1=false (clause 2) -> conflict.
    // UIP analysis derives unit x0=true. Its proof ID must be stored.
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let x0 = Variable(0);
    let x1 = Variable(1);

    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert_eq!(solver.decision_level, 0);

    // Simulate probe: decide !x0 at level 1.
    let probe_lit = Literal::negative(x0);
    solver.decide(probe_lit);
    assert_eq!(solver.decision_level, 1);

    // BCP: should find conflict.
    let conflict_ref = solver.propagate();
    assert!(
        conflict_ref.is_some(),
        "BCP after deciding !x0 must find conflict (x1 forced both ways)"
    );
    let conflict_ref = conflict_ref.unwrap();

    // UIP analysis: find the forced unit.
    let forced = find_failed_literal_uip(
        solver.arena.literals(conflict_ref.0 as usize),
        &solver.trail,
        &solver.var_data,
        &solver.arena,
        solver.inproc.prober.uip_seen_mut(),
    );
    assert!(
        forced.forced.is_some(),
        "UIP analysis must derive a forced unit"
    );
    let unit_lit = forced.forced.unwrap();

    // Backtrack to level 0.
    solver.backtrack(0);
    assert_eq!(solver.decision_level, 0);

    // This is the #4631 fix path: emit proof and store unit_proof_id.
    // Hints are the two original clause IDs that derive the unit via RUP:
    //   Assume ~x0; hint 1=(x0|x1): forces x1; hint 2=(x0|~x1): conflict.
    let proof_id = solver
        .proof_emit_add_prechecked(&[unit_lit], &[1, 2], ProofAddKind::Derived)
        .unwrap_or(0);
    if proof_id != 0 {
        solver.record_unit_proof_id_for_lit(unit_lit, proof_id);
    }

    let _unit_idx = solver.add_clause_db(&[unit_lit], true);
    // Unit clause: reason=None (#6257). Conflict analysis requires len >= 2.
    solver.enqueue(unit_lit, None);

    // Verify: unit must be x0=true.
    assert_eq!(
        unit_lit,
        Literal::positive(x0),
        "UIP should derive x0=true from failed literal !x0"
    );

    // The unit_proof_id for x0 must be non-zero in LRAT mode (#4631).
    assert_ne!(
        solver.unit_proof_id[x0.index()],
        0,
        "probe failed-literal unit must have non-zero unit_proof_id for LRAT chain collection"
    );
}

// ========================================================================
// XOR Extension + DRAT Proof Emission Tests (#7913)
// ========================================================================

/// Verify that extension-derived clauses (simulating XOR Gauss-Jordan)
/// are emitted into the DRAT proof stream.
///
/// This test creates a minimal extension that produces theory propagations
/// and conflict clauses — the same code path used by `XorExtension`. It
/// then checks that the DRAT proof contains addition lines for the
/// extension-derived clauses and that the proof is non-empty for UNSAT.
#[test]
fn test_xor_extension_drat_proof_emission() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};
    use crate::ProofOutput;

    /// Minimal extension that mimics XOR Gauss-Jordan behavior:
    /// produces a conflict clause after observing assignments.
    struct XorLikeExtension {
        fired: bool,
    }

    impl Extension for XorLikeExtension {
        fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
            if self.fired {
                return ExtPropagateResult::none();
            }
            // Wait until we have some assignments, then fire a conflict.
            // This simulates a XOR parity conflict: x0 XOR x1 = 1 but
            // both are assigned the same polarity.
            let trail = ctx.trail();
            if trail.len() >= 2 {
                let x0_val = ctx.value(Variable(0));
                let x1_val = ctx.value(Variable(1));
                if let (Some(v0), Some(v1)) = (x0_val, x1_val) {
                    if v0 == v1 {
                        self.fired = true;
                        // Conflict: both same polarity violates x0 XOR x1 = 1
                        let conflict = vec![
                            if v0 {
                                Literal::negative(Variable(0))
                            } else {
                                Literal::positive(Variable(0))
                            },
                            if v1 {
                                Literal::negative(Variable(1))
                            } else {
                                Literal::positive(Variable(1))
                            },
                        ];
                        return ExtPropagateResult::conflict(conflict);
                    }
                }
            }
            ExtPropagateResult::none()
        }

        fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
            // XOR final check: x0 XOR x1 must be 1
            let v0 = ctx.value(Variable(0)).unwrap_or(false);
            let v1 = ctx.value(Variable(1)).unwrap_or(false);
            if v0 ^ v1 {
                ExtCheckResult::Sat
            } else {
                let conflict = vec![
                    if v0 {
                        Literal::negative(Variable(0))
                    } else {
                        Literal::positive(Variable(0))
                    },
                    if v1 {
                        Literal::negative(Variable(1))
                    } else {
                        Literal::positive(Variable(1))
                    },
                ];
                ExtCheckResult::Conflict(conflict)
            }
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            !self.fired
        }
    }

    // Formula: x0 = false AND x1 = false (both forced false).
    // XOR extension requires x0 XOR x1 = 1, which conflicts.
    // The combined system is UNSAT.
    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(2, proof_output);
    solver.add_clause(vec![Literal::negative(Variable(0))]); // x0 = false
    solver.add_clause(vec![Literal::negative(Variable(1))]); // x1 = false

    let mut ext = XorLikeExtension { fired: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(result.is_unsat(), "formula + XOR constraint must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes).expect("UTF-8 proof");

    // The DRAT proof must be non-empty: it should contain at least
    // the extension-derived conflict clause as an addition line.
    assert!(
        !proof.is_empty(),
        "DRAT proof must not be empty when extension produces conflict clauses"
    );

    // Verify the proof contains at least one addition line (non-deletion).
    // DRAT addition lines are just literal sequences ending with 0.
    // Deletion lines start with 'd'.
    let add_lines: Vec<&str> = proof
        .lines()
        .filter(|line| !line.trim_start().starts_with('d'))
        .collect();
    assert!(
        !add_lines.is_empty(),
        "DRAT proof must contain addition lines for extension-derived clauses.\n\
         Full proof:\n{proof}"
    );

    // The proof must contain the empty clause (final UNSAT derivation).
    let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
    assert!(
        has_empty_clause,
        "DRAT proof must end with empty clause derivation for UNSAT.\n\
         Full proof:\n{proof}"
    );
}

/// Verify that `solve_with_preprocessing_extension` sets the
/// `extension_trusted_lemmas` flag so that LRAT mode is not blocked
/// by extension-derived theory lemmas (#7913).
///
/// This test uses the preprocessing extension path (which consumes
/// original clauses) and verifies that:
/// 1. The extension_trusted_lemmas flag is set
/// 2. DRAT proof emission works for the extension-derived clauses
/// 3. The proof contains the empty clause for UNSAT
#[test]
fn test_xor_preprocessing_extension_drat_proof_trusted_transform() {
    use crate::extension::{
        ExtCheckResult, ExtPropagateResult, Extension, PreparedExtension, SolverContext,
    };
    use crate::ProofOutput;

    /// Extension that consumes two binary clauses encoding x0 XOR x1 = 1
    /// and produces an UNSAT conflict when combined with x0 = false, x1 = false.
    struct XorPreprocessExtension {
        fired: bool,
    }

    impl Extension for XorPreprocessExtension {
        fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
            if self.fired {
                return ExtPropagateResult::none();
            }
            let x0_val = ctx.value(Variable(0));
            let x1_val = ctx.value(Variable(1));
            if let (Some(v0), Some(v1)) = (x0_val, x1_val) {
                if v0 == v1 {
                    self.fired = true;
                    let conflict = vec![
                        if v0 {
                            Literal::negative(Variable(0))
                        } else {
                            Literal::positive(Variable(0))
                        },
                        if v1 {
                            Literal::negative(Variable(1))
                        } else {
                            Literal::positive(Variable(1))
                        },
                    ];
                    return ExtPropagateResult::conflict(conflict);
                }
                if !(v0 ^ v1) {
                    self.fired = true;
                    let conflict = vec![
                        if v0 {
                            Literal::negative(Variable(0))
                        } else {
                            Literal::positive(Variable(0))
                        },
                        if v1 {
                            Literal::negative(Variable(1))
                        } else {
                            Literal::positive(Variable(1))
                        },
                    ];
                    return ExtPropagateResult::conflict(conflict);
                }
            }
            // Propagation: if x0 is assigned, propagate x1 = !x0
            if let Some(v0) = x0_val {
                if x1_val.is_none() {
                    self.fired = true;
                    let propagated = if v0 {
                        Literal::negative(Variable(1))
                    } else {
                        Literal::positive(Variable(1))
                    };
                    let reason = vec![
                        propagated,
                        if v0 {
                            Literal::negative(Variable(0))
                        } else {
                            Literal::positive(Variable(0))
                        },
                    ];
                    return ExtPropagateResult::new(
                        vec![],
                        vec![(reason, propagated)],
                        None,
                        false,
                    );
                }
            }
            ExtPropagateResult::none()
        }

        fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
            let v0 = ctx.value(Variable(0)).unwrap_or(false);
            let v1 = ctx.value(Variable(1)).unwrap_or(false);
            if v0 ^ v1 {
                ExtCheckResult::Sat
            } else {
                let conflict = vec![
                    if v0 {
                        Literal::negative(Variable(0))
                    } else {
                        Literal::positive(Variable(0))
                    },
                    if v1 {
                        Literal::negative(Variable(1))
                    } else {
                        Literal::positive(Variable(1))
                    },
                ];
                ExtCheckResult::Conflict(conflict)
            }
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            !self.fired
        }
    }

    // Formula:
    // Clauses 0-1: x0 XOR x1 = 1 (encoded as CNF: {-x0,-x1}, {x0,x1})
    // Clause 2: x0 = false (unit)
    // Clause 3: x1 = false (unit)
    //
    // The XOR clauses (0,1) are consumed by the preprocessing extension.
    // The extension then enforces x0 XOR x1 = 1 via Gauss-Jordan.
    // Combined with x0=false, x1=false => UNSAT.
    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(2, proof_output);

    // XOR encoding: x0 XOR x1 = 1
    let x0p = Literal::positive(Variable(0));
    let x0n = Literal::negative(Variable(0));
    let x1p = Literal::positive(Variable(1));
    let x1n = Literal::negative(Variable(1));
    solver.add_clause(vec![x0n, x1n]); // clause 0: {-x0, -x1}
    solver.add_clause(vec![x0p, x1p]); // clause 1: {x0, x1}
                                       // Force both false
    solver.add_clause(vec![x0n]); // clause 2: x0 = false
    solver.add_clause(vec![x1n]); // clause 3: x1 = false

    let result = solver
        .solve_with_preprocessing_extension::<XorPreprocessExtension, _>(|clauses| {
            // Consume the first two clauses (XOR encoding), leave the units.
            // Only consume if we see both XOR clauses.
            if clauses.len() >= 2 {
                Some(PreparedExtension::new(
                    XorPreprocessExtension { fired: false },
                    vec![0, 1], // consume clauses 0 and 1
                    vec![Variable(0), Variable(1)],
                ))
            } else {
                None
            }
        })
        .into_inner();

    assert!(
        result.is_unsat(),
        "formula + XOR preprocessing extension must be UNSAT"
    );

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes).expect("UTF-8 proof");

    // DRAT proof must be non-empty
    assert!(
        !proof.is_empty(),
        "DRAT proof must not be empty for UNSAT with preprocessing extension"
    );

    // Verify the proof contains addition lines
    let add_lines: Vec<&str> = proof
        .lines()
        .filter(|line| !line.trim_start().starts_with('d'))
        .collect();
    assert!(
        !add_lines.is_empty(),
        "DRAT proof must contain addition lines for preprocessing extension.\n\
         Full proof:\n{proof}"
    );

    // The proof must contain the empty clause
    let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
    assert!(
        has_empty_clause,
        "DRAT proof must end with empty clause for UNSAT.\n\
         Full proof:\n{proof}"
    );
}

/// Verify that `set_extension_trusted_lemmas(true)` + `solve_with_extension`
/// emits DRAT proof records for extension-derived theory lemmas (#4533).
///
/// This tests the non-preprocessing extension path, which is used by:
/// - `ExtDimacsFormula::solve()` in ay-xor
/// - The DIMACS CLI XOR path (without `--proof`)
///
/// Without `set_extension_trusted_lemmas(true)`, theory lemmas would be
/// emitted as `ProofAddKind::Axiom` and LRAT would be blocked. With the
/// flag set, they are emitted as `TrustedTransform`.
#[test]
fn test_extension_trusted_lemmas_drat_proof_via_solve_with_extension() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};
    use crate::ProofOutput;

    /// Extension that enforces x0 XOR x1 = 1 (odd parity).
    /// Produces a conflict when both variables are assigned to the same value.
    struct SimpleXorExtension {
        fired: bool,
    }

    impl Extension for SimpleXorExtension {
        fn propagate(&mut self, ctx: &dyn SolverContext) -> ExtPropagateResult {
            if self.fired {
                return ExtPropagateResult::none();
            }
            let x0_val = ctx.value(Variable(0));
            let x1_val = ctx.value(Variable(1));
            if let (Some(v0), Some(v1)) = (x0_val, x1_val) {
                if !(v0 ^ v1) {
                    // XOR constraint violated: both same parity
                    self.fired = true;
                    let conflict = vec![
                        if v0 {
                            Literal::negative(Variable(0))
                        } else {
                            Literal::positive(Variable(0))
                        },
                        if v1 {
                            Literal::negative(Variable(1))
                        } else {
                            Literal::positive(Variable(1))
                        },
                    ];
                    return ExtPropagateResult::conflict(conflict);
                }
            }
            // Propagation: if x0 is assigned, propagate x1 = !x0
            if let Some(v0) = x0_val {
                if x1_val.is_none() {
                    self.fired = true;
                    let propagated = if v0 {
                        Literal::negative(Variable(1))
                    } else {
                        Literal::positive(Variable(1))
                    };
                    let reason = vec![
                        propagated,
                        if v0 {
                            Literal::negative(Variable(0))
                        } else {
                            Literal::positive(Variable(0))
                        },
                    ];
                    return ExtPropagateResult::new(
                        vec![],
                        vec![(reason, propagated)],
                        None,
                        false,
                    );
                }
            }
            ExtPropagateResult::none()
        }

        fn check(&mut self, ctx: &dyn SolverContext) -> ExtCheckResult {
            let v0 = ctx.value(Variable(0)).unwrap_or(false);
            let v1 = ctx.value(Variable(1)).unwrap_or(false);
            if v0 ^ v1 {
                ExtCheckResult::Sat
            } else {
                let conflict = vec![
                    if v0 {
                        Literal::negative(Variable(0))
                    } else {
                        Literal::positive(Variable(0))
                    },
                    if v1 {
                        Literal::negative(Variable(1))
                    } else {
                        Literal::positive(Variable(1))
                    },
                ];
                ExtCheckResult::Conflict(conflict)
            }
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            !self.fired
        }
    }

    // Formula:
    // Unit clause: x0 = false
    // Unit clause: x1 = false
    // Extension enforces: x0 XOR x1 = 1
    // Combined: UNSAT (extension conflict)
    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(2, proof_output);
    let x0n = Literal::negative(Variable(0));
    let x1n = Literal::negative(Variable(1));
    solver.add_clause(vec![x0n]); // x0 = false
    solver.add_clause(vec![x1n]); // x1 = false

    // Mark extension lemmas as trusted (#4533)
    solver.set_extension_trusted_lemmas(true);

    let mut ext = SimpleXorExtension { fired: false };
    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(result.is_unsat(), "formula + XOR extension must be UNSAT");

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes).expect("UTF-8 proof");

    // DRAT proof must be non-empty
    assert!(
        !proof.is_empty(),
        "DRAT proof must not be empty for UNSAT with trusted extension (#4533)"
    );

    // The proof should contain addition lines (extension-derived clauses)
    let add_lines: Vec<&str> = proof
        .lines()
        .filter(|line| !line.trim_start().starts_with('d'))
        .filter(|line| !line.trim().is_empty())
        .collect();
    assert!(
        !add_lines.is_empty(),
        "DRAT proof must contain addition lines for trusted extension.\n\
         Full proof:\n{proof}"
    );

    // The proof must contain the empty clause
    let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
    assert!(
        has_empty_clause,
        "DRAT proof must end with empty clause for UNSAT (#4533).\n\
         Full proof:\n{proof}"
    );
}

// ========================================================================
// Phase C: BCP-Interleaved Theory Propagation (#4919)
// ========================================================================

/// Phase C: when an extension reports `can_propagate=false` but BCP propagated
/// SAT atoms, the solver must still give the extension a force-call to catch
/// cascading work (e.g. pending implied bounds in LRA that do not manifest as
/// new theory atoms on the SAT trail).
///
/// This mirrors Z3's `propagate_core` pattern where `m_ext->unit_propagate()`
/// is called inside the BCP loop, not just after BCP exits.
/// See reference/z3/src/sat/sat_solver.cpp:961-976.
#[test]
fn test_phase_c_force_propagate_runs_when_can_propagate_returns_false_4919() {
    use crate::extension::{ExtCheckResult, ExtPropagateResult, Extension, SolverContext};
    use std::cell::Cell;

    /// Extension that:
    ///  - reports `can_propagate=false` unconditionally, so the gated
    ///    `propagate()` path always short-circuits with `Continue`.
    ///  - implements `propagate()` to record how often it ran. Phase C must
    ///    invoke `propagate_force()` after BCP propagates, which bypasses the
    ///    gate and calls `propagate()` directly.
    ///  - returns `Sat` on `check()` so the solver can finalize.
    struct ForceCallProbe {
        propagate_calls: Cell<usize>,
    }
    impl Extension for ForceCallProbe {
        fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
            self.propagate_calls.set(self.propagate_calls.get() + 1);
            ExtPropagateResult::none()
        }

        fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
            ExtCheckResult::Sat
        }

        fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
            // Phase C path: gate says "no work", but Phase C force-call should
            // still run propagate() when BCP propagated atoms.
            false
        }
    }

    // Formula with at least one binary clause so BCP propagates after a
    // decision. (x0 OR x1) AND (NOT x0 OR x2) — after deciding x0=false,
    // BCP propagates x1=true; that BCP step is the trigger for Phase C.
    let mut solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::positive(Variable(2)),
    ]);

    let probe = ForceCallProbe {
        propagate_calls: Cell::new(0),
    };
    let mut ext = probe;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(result.is_sat(), "formula is SAT");

    // Phase C must have force-called the extension at least once.
    let (force_calls, _force_hits) = solver.bcp_theory_interleaved_stats();
    assert!(
        force_calls > 0,
        "Phase C: expected at least one force-propagate call after BCP propagated, \
         got {force_calls}. ExtensionCallback.propagate ran {} times in total.",
        ext.propagate_calls.get(),
    );

    // The actual ext.propagate must have run at least once via the force path,
    // even though can_propagate always returned false.
    assert!(
        ext.propagate_calls.get() > 0,
        "Phase C: extension propagate() must have been invoked via force-call \
         even though can_propagate=false. Calls observed: {}",
        ext.propagate_calls.get(),
    );
}

// =============================================================================
// Deterministic resource budgets (#8749 `:rlimit` + #ground-determinism)
// =============================================================================

/// Pigeonhole clauses (n pigeons, m holes): UNSAT for n > m, exponentially
/// hard for resolution, so the CDCL loop must do real search (decisions AND
/// conflicts) — the budget checkpoints get exercised on the genuine paths.
fn add_pigeonhole_clauses(solver: &mut Solver, pigeons: usize, holes: usize) {
    let var = |i: usize, j: usize| Variable((i * holes + j) as u32);
    for i in 0..pigeons {
        let clause: Vec<Literal> = (0..holes).map(|j| Literal::positive(var(i, j))).collect();
        solver.add_clause(clause);
    }
    for j in 0..holes {
        for i in 0..pigeons {
            for k in (i + 1)..pigeons {
                solver.add_clause(vec![
                    Literal::negative(var(i, j)),
                    Literal::negative(var(k, j)),
                ]);
            }
        }
    }
}

/// A decision budget must stop the solve with `ResourceBudget` — the
/// decision-count companion of the `:rlimit` conflict budget for
/// decision-heavy / conflict-light regimes (#ground-determinism).
#[test]
fn test_decision_budget_stops_with_resource_budget_reason() {
    use crate::SatUnknownReason;

    let mut solver = Solver::new(8 * 7);
    solver.set_preprocess_enabled(false);
    add_pigeonhole_clauses(&mut solver, 8, 7);
    solver.set_decision_budget(Some(solver.num_decisions() + 40));

    let result = solver.solve_interruptible(|| false).into_inner();

    assert_eq!(result, SatResult::Unknown, "budget must stop the search");
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ResourceBudget),
        "a decision-budget stop must be attributed to the deterministic budget"
    );
}

/// The stop point of a deterministic budget must itself be deterministic:
/// identical inputs (formula, seed, budget) stop at identical conflict AND
/// decision counts on every run (#ground-determinism constraint (a)).
#[test]
fn test_decision_budget_stop_point_deterministic_across_runs() {
    use crate::SatUnknownReason;

    let run = || {
        let mut solver = Solver::new(8 * 7);
        solver.set_preprocess_enabled(false);
        add_pigeonhole_clauses(&mut solver, 8, 7);
        solver.set_decision_budget(Some(solver.num_decisions() + 40));
        let result = solver.solve_interruptible(|| false).into_inner();
        assert_eq!(result, SatResult::Unknown);
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::ResourceBudget)
        );
        (solver.num_conflicts(), solver.num_decisions())
    };

    let (c1, d1) = run();
    let (c2, d2) = run();
    assert_eq!(c1, c2, "conflicts at stop must be identical across runs");
    assert_eq!(d1, d2, "decisions at stop must be identical across runs");
    assert!(d1 >= 40, "the decision budget must be what stopped the run");
}

/// Clearing the decision budget restores completion: the same instance is
/// proven UNSAT (the budget only bounds work, it never changes a verdict).
#[test]
fn test_decision_budget_cleared_solves_to_completion() {
    let mut solver = Solver::new(6 * 5);
    solver.set_preprocess_enabled(false);
    add_pigeonhole_clauses(&mut solver, 6, 5);
    solver.set_decision_budget(None);

    let result = solver.solve_interruptible(|| false).into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "PHP(6,5) is UNSAT, got {result:?}"
    );
}
