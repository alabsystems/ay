// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod fixtures;
use fixtures::{fixture, open_epoch, run};

#[test]
fn borrowed_proof_and_both_inventories_preserve_the_legacy_source_rules() {
    let executor = fixture();
    let roots = &executor.ctx.assertions;
    let stamp = executor.ctx.source_context_stamp();
    let view = executor
        .exact_plain_query_proof_source_with_resource_control(roots, &stamp, &mut |_, _| true)
        .unwrap()
        .unwrap();
    assert!(std::ptr::eq(view.proof(), executor.last_proof().unwrap()));
    let source = view
        .source_closure_with_resource_control(&mut |_, _| true)
        .unwrap();
    assert_eq!(
        source,
        executor
            .exact_plain_query_source_closure(roots, &stamp)
            .unwrap()
    );
    let complete = view
        .complete_problem_with_resource_control(&mut |_, _| true)
        .unwrap();
    assert_eq!(
        complete,
        executor.complete_problem_assertions_for_strict_proof()
    );
    let provenance = executor
        .proof_problem_assertion_provenance
        .as_ref()
        .unwrap();
    let [q, q_again, false_term] = provenance.problem_assertions.as_slice() else {
        panic!("fixture rows")
    };
    assert_eq!(q, q_again);
    assert_eq!(source.iter().filter(|term| *term == q).count(), 1);
    assert_eq!(complete.iter().filter(|term| *term == q).count(), 2);
    assert!(!source.contains(false_term));
    assert!(
        complete.contains(false_term),
        "self-check freshness has its own source inventory"
    );
    let only_freshness = executor.self_check_authored_assertions.as_ref().unwrap()[0];
    assert!(!source.contains(&only_freshness));
    assert!(complete.contains(&only_freshness));
}

#[test]
fn compact_literal_false_authority_survives_disabled_surface_retention() {
    for (text, literal) in [("(assert false)", true), ("(assert (< 5 3))", false)] {
        let mut executor = Executor::new();
        executor.ctx.set_retain_parsed_assertions(false);
        executor
            .execute_all(&ay_frontend::parse(text).unwrap())
            .unwrap();
        assert!(executor.ctx.assertions_parsed().is_empty());
        assert_eq!(executor.ctx.assertions, [executor.ctx.terms.false_term()]);
        open_epoch(&mut executor, true);
        // Even a retained source flag cannot grant an assumption that the
        // authenticated plain epoch does not contain.
        executor
            .unsat_query_epoch
            .as_mut()
            .unwrap()
            .literal_false_assumption_source = true;
        let stamp = executor.ctx.source_context_stamp();
        let legacy = executor.exact_plain_query_source_closure(&executor.ctx.assertions, &stamp);
        let result = executor
            .exact_plain_query_proof_source_with_resource_control(
                &executor.ctx.assertions,
                &stamp,
                &mut |_, _| true,
            )
            .unwrap();
        assert_eq!(result.is_some(), literal);
        assert_eq!(
            result.map(|view| view
                .source_closure_with_resource_control(&mut |_, _| true)
                .unwrap()),
            legacy
        );
    }
}

#[test]
fn stale_missing_and_nonplain_epochs_never_borrow_a_proof() {
    let mutations: &[fn(&mut Executor)] = &[
        |e| e.unsat_query_epoch = None,
        |e| e.advance_query_authority_epoch(),
        |e| e.proof_problem_assertion_provenance = None,
        |e| {
            e.proof_problem_assertion_provenance
                .as_mut()
                .unwrap()
                .original_problem_assertions
                .swap(0, 1)
        },
        |e| e.ctx.assertions.pop().map(|_| ()).unwrap(),
        |e| {
            e.unsat_query_epoch
                .as_mut()
                .unwrap()
                .assertion_entries
                .pop()
                .map(|_| ())
                .unwrap()
        },
        |e| e.unsat_query_epoch.as_mut().unwrap().assumptions = None,
        |e| e.unsat_query_epoch.as_mut().unwrap().assumption_entries = None,
        |e| {
            e.unsat_query_epoch
                .as_mut()
                .unwrap()
                .declared_extension
                .push(e.ctx.terms.true_term())
        },
        |e| {
            e.unsat_query_epoch
                .as_mut()
                .unwrap()
                .declared_extension_entries
                .push(e.ctx.terms.entry_stamp(e.ctx.terms.true_term()).unwrap())
        },
        |e| {
            e.unsat_query_epoch
                .as_mut()
                .unwrap()
                .declared_extension_objectives = Some(vec![])
        },
        |e| {
            e.unsat_query_epoch
                .as_mut()
                .unwrap()
                .declared_extension_objective_entries = Some(vec![])
        },
        |e| {
            e.execute_all(&ay_frontend::parse("(declare-const later_scope Bool)").unwrap())
                .unwrap();
        },
        |e| {
            e.ctx.terms = CoreTermStore::from_entries(
                e.ctx.terms.entries_snapshot(),
                Some(e.ctx.terms.true_term()),
                Some(e.ctx.terms.false_term()),
                e.ctx.terms.var_counter(),
            );
        },
    ];
    for mutate in mutations {
        let mut executor = fixture();
        let roots = executor.ctx.assertions.clone();
        let stamp = executor.ctx.source_context_stamp();
        mutate(&mut executor);
        assert!(executor
            .exact_plain_query_proof_source_with_resource_control(&roots, &stamp, &mut |_, _| true)
            .unwrap()
            .is_none());
        assert!(executor
            .exact_plain_query_source_closure(&roots, &stamp)
            .is_none());
    }
    let mut executor = fixture();
    let other = executor.ctx.terms.true_term();
    let epoch = executor.unsat_query_epoch.as_mut().unwrap();
    epoch.assumptions = Some(vec![other]);
    epoch.assumption_entries = Some(vec![executor.ctx.terms.entry_stamp(other).unwrap()]);
    assert!(executor
        .plain_unsat_query_epoch_is_current_with_resource_control(&mut |_, _| true)
        .unwrap());
    assert!(
        run(&executor, &mut |_, _| true).unwrap().is_none(),
        "exact binding forbids nonempty assumptions"
    );
}

#[test]
fn exact_binding_rejects_foreign_context_and_changed_order_without_arena_wide_rejection() {
    let mut executor = fixture();
    let roots = executor.ctx.assertions.clone();
    let stamp = executor.ctx.source_context_stamp();
    let foreign = Executor::new().ctx.source_context_stamp();
    assert!(executor
        .exact_plain_query_proof_source_with_resource_control(&roots, &foreign, &mut |_, _| true,)
        .unwrap()
        .is_none());
    for changed in [vec![], vec![roots[0]], vec![roots[1], roots[0], roots[0]]] {
        assert!(executor
            .exact_plain_query_proof_source_with_resource_control(&changed, &stamp, &mut |_, _| {
                true
            },)
            .unwrap()
            .is_none());
    }
    executor
        .ctx
        .terms
        .mk_var("later_unused_term", CoreSort::Bool);
    // This is source/current-root access only. Whole-arena sealed evidence
    // retains its separate, stronger currentness checks at export.
    assert!(run(&executor, &mut |_, _| true).unwrap().is_some());
}

#[test]
fn public_proof_access_retains_solve_time_output_and_result_requirements() {
    for mutate in [
        (|e: &mut Executor| e.unsat_query_epoch.as_mut().unwrap().proof_output_requested = false)
            as fn(&mut Executor),
        |e| e.last_result = Some(SolveResult::Sat),
        |e| e.last_result = None,
        |e| e.last_proof = None,
        |e| e.last_unsat_proof_reconstruction_suppressed = true,
    ] {
        let mut executor = fixture();
        mutate(&mut executor);
        assert!(executor.last_proof().is_none());
        assert!(run(&executor, &mut |_, _| true).unwrap().is_none());
    }
    let mut executor = fixture();
    executor.set_produce_proofs(false);
    assert!(executor.last_proof().is_some());
    assert!(run(&executor, &mut |_, _| true).unwrap().is_some());
}

#[test]
fn epoch_progress_walks_actual_root_and_assumption_entry_vectors_without_copying() {
    let mut executor = fixture();
    let roots = executor.ctx.assertions.clone();
    let epoch = executor.unsat_query_epoch.as_mut().unwrap();
    epoch.assumptions = Some(roots.clone());
    epoch.assumption_entries = Some(
        roots
            .iter()
            .map(|&id| executor.ctx.terms.entry_stamp(id).unwrap())
            .collect(),
    );
    assert_eq!(
        executor.unsat_query_epoch_inventory_lengths_for_resource_control(),
        Some((roots.len(), roots.len()))
    );
    let mut charges = Vec::new();
    assert!(executor
        .plain_unsat_query_epoch_is_current_with_resource_control(&mut |w, b| {
            charges.push((w, b));
            true
        })
        .unwrap());
    assert_eq!(charges.first(), Some(&(0, 0)));
    assert_eq!(charges.last(), Some(&(0, 0)));
    assert_eq!(
        charges.iter().map(|&(w, _)| w).sum::<usize>(),
        roots.len() * 2
    );
    assert!(charges.iter().all(|&(_, b)| b == 0));
    for stop in 1..=charges.len() {
        let mut calls = 0;
        assert_eq!(
            executor.plain_unsat_query_epoch_is_current_with_resource_control(&mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert_eq!(calls, stop);
    }
}

#[test]
fn every_shared_checkpoint_refuses_without_mutation_and_a_fresh_retry_matches() {
    let executor = fixture();
    let before = executor.ctx.terms.entries_snapshot();
    let mut trace = Vec::new();
    let expected = run(&executor, &mut |w, b| {
        trace.push((w, b));
        true
    })
    .unwrap()
    .unwrap();
    assert!(trace.iter().any(|&(_, b)| b > 0));
    for stop in 1..=trace.len() {
        let mut actual = Vec::new();
        assert_eq!(
            run(&executor, &mut |w, b| {
                actual.push((w, b));
                actual.len() != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert_eq!(actual, trace[..stop], "no callback after refusal");
    }
    assert_eq!(executor.ctx.terms.entries_snapshot(), before);
    assert_eq!(run(&executor, &mut |_, _| true).unwrap().unwrap(), expected);
}

#[test]
fn one_aggregate_allowance_covers_authentication_and_both_distinct_copies() {
    let executor = fixture();
    let (mut work, mut bytes) = (0usize, 0usize);
    assert!(run(&executor, &mut |w, b| {
        work += w;
        bytes += b;
        true
    })
    .unwrap()
    .is_some());
    assert!(work > 1 && bytes > 1);
    for (work_cap, byte_cap, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
        (0, bytes, false),
        (work, 0, false),
    ] {
        let (mut used_work, mut used_bytes) = (0, 0);
        let mut progress = |w, b| {
            used_work += w;
            used_bytes += b;
            used_work <= work_cap && used_bytes <= byte_cap
        };
        let result = run(&executor, &mut progress);
        assert_eq!(result.is_ok(), success);
        if success {
            assert_eq!(
                run(&executor, &mut progress),
                Err(ProofCheckError::ResourceLimit),
                "no allowance reset between attempts"
            );
        } else {
            assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        }
    }
}
