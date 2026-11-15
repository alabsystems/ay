// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{CheckedPropagationDerivation, CheckedPropagationEntry};
use super::*;
use crate::executor::proof_propagated_rewrite::{PlanCx, PropagationChainPlanner};
use crate::executor::{Executor, QueryAuthorityEpoch};
use crate::preprocess::{PreprocessingPass, RecordedVariableSubstitution, VariableSubstitution};
use ay_core::kani_compat::DetHashMap as HashMap;
use std::sync::{Arc, Mutex};

mod aggregate;
mod recorded_boolean;

fn entry(terms: &mut TermStore, expr: TermId, value: TermId) -> PropagatedEntrySource {
    PropagatedEntrySource {
        expr,
        value,
        source_assertion: terms.mk_app(Symbol::named("="), [expr, value], Sort::Bool),
        stamp: 7,
    }
}

fn scalar_fixture() -> (Executor, PropagatedEntrySource) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let variable = terms.mk_var("length", Sort::bitvec(64));
    let value = terms.mk_bitvec(65.into(), 64);
    let source = entry(terms, variable, value);
    (executor, source)
}

#[test]
fn actual_recorded_scalar_licenses_replay_from_nested_authored_equalities() {
    for reversed in [false, true] {
        let mut executor = Executor::new();
        let terms = &mut executor.ctx.terms;
        let length = terms.mk_var("length", Sort::bitvec(64));
        let fill = terms.mk_var("fill", Sort::bitvec(64));
        let x = terms.mk_var("x", Sort::bitvec(64));
        let sixty_five = terms.mk_bitvec(65.into(), 64);
        let function = terms.mk_app(Symbol::named("f"), [terms.true_term(), x], Sort::bitvec(64));
        let sources: Vec<_> = [(length, sixty_five), (fill, function)]
            .into_iter()
            .map(|(a, b)| {
                let args = if reversed { [b, a] } else { [a, b] };
                terms.mk_app(Symbol::named("="), args, Sort::Bool)
            })
            .collect();
        let authored_definitions = terms.mk_app(Symbol::named("and"), &sources, Sort::Bool);
        let before = terms.mk_app(Symbol::named("p"), [length, fill], Sort::Bool);
        let originals = [authored_definitions, before];
        let mut working = sources.clone();
        working.push(before);
        let propagation = Arc::new(Mutex::new(PropagateValues::new()));
        let mut pass = RecordedVariableSubstitution::new(
            Arc::new(Mutex::new(VariableSubstitution::new())),
            Arc::clone(&propagation),
            Box::new(|_, _| true),
        );
        assert!(pass.apply(terms, &mut working));
        let target = working[2];
        assert_ne!(target, before);
        let records = propagation
            .lock()
            .unwrap()
            .take_propagation_records()
            .unwrap();
        let mut entries = HashMap::default();
        for variable in [length, fill] {
            let recorded = records.entries.iter().find(|e| e.expr == variable).unwrap();
            let (key, licensed) = CheckedPropagationEntry::seal(&executor, recorded)
                .expect("actual scalar variable license must seal")
                .into_current(&executor)
                .unwrap();
            assert_eq!(
                licensed,
                (recorded.value, recorded.source_assertion, recorded.stamp)
            );
            entries.insert(key, licensed);
        }
        let mut rewrites = HashMap::default();
        for record in &records.rewrites {
            let pair = CheckedPropagationDerivation::seal(&mut executor, record, &records.entries)
                .unwrap()
                .into_current(&executor)
                .unwrap();
            rewrites.insert(pair.0, pair.1);
        }
        let original_set = originals.into_iter().collect();
        let mut cx = PlanCx::new(&original_set, &originals, &rewrites, &entries, &[], true);
        let conclusion = PropagationChainPlanner {
            terms: &mut executor.ctx.terms,
        }
        .plan_derive_clause(&mut cx, target)
        .expect("existing replay derives exact rewritten root");
        let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            &cx.chain,
            &executor.ctx.terms,
            None,
            None,
            &originals,
            &mut |_, _| true,
        )
        .expect("unchanged strict checker validates every license and rewrite");
        assert_eq!(checked.clause(conclusion), Some([target].as_slice()));
        let unrelated_roots = [before];
        let unrelated_set = unrelated_roots.into_iter().collect();
        let mut unlicensed = PlanCx::new(
            &unrelated_set,
            &unrelated_roots,
            &rewrites,
            &entries,
            &[],
            true,
        );
        assert!(
            PropagationChainPlanner {
                terms: &mut executor.ctx.terms
            }
            .plan_derive_clause(&mut unlicensed, target)
            .is_none(),
            "a sealed shape does not authorize an unasserted defining equality"
        );
    }
}

#[test]
fn scalar_entry_rejects_unrelated_endpoints_and_non_boolean_equality() {
    let (mut executor, source) = scalar_fixture();
    let other = executor.ctx.terms.mk_bitvec(66.into(), 64);
    let mut forged = source.clone();
    forged.value = other;
    assert!(CheckedPropagationEntry::seal(&executor, &forged).is_none());
    forged = source.clone();
    forged.source_assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [source.expr, other], Sort::Bool);
    assert!(CheckedPropagationEntry::seal(&executor, &forged).is_none());
    forged.source_assertion =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("="), [source.expr, source.value], Sort::Int);
    assert!(CheckedPropagationEntry::seal(&executor, &forged).is_none());
    assert!(CheckedPropagationEntry::seal(&executor, &source).is_some());
}

#[test]
fn scalar_entry_refuses_sort_mismatches_and_unopened_aggregate_sorts() {
    let (mut executor, source) = scalar_fixture();
    let terms = &mut executor.ctx.terms;
    let narrow = terms.mk_bitvec(65.into(), 32);
    let mismatched = entry(terms, source.expr, narrow);
    assert!(CheckedPropagationEntry::seal(&executor, &mismatched).is_none());
    for sort in [
        Sort::bitvec(0),
        Sort::Datatype(ay_core::DatatypeSort::new("still unopened", vec![])),
        Sort::Seq(Box::new(Sort::Int)),
    ] {
        let terms = &mut executor.ctx.terms;
        let left = terms.mk_var("unopened left", sort.clone());
        let right = terms.mk_var("unopened right", sort);
        let unsupported = entry(terms, left, right);
        assert!(CheckedPropagationEntry::seal(&executor, &unsupported).is_none());
    }
}

#[test]
fn scalar_entry_checks_all_endpoint_ids_before_dereferencing() {
    let (executor, source) = scalar_fixture();
    for endpoint in 0..3 {
        let mut forged = source.clone();
        match endpoint {
            0 => forged.expr = TermId(u32::MAX),
            1 => forged.value = TermId(u32::MAX),
            _ => forged.source_assertion = TermId(u32::MAX),
        }
        assert!(CheckedPropagationEntry::seal(&executor, &forged).is_none());
    }
}

#[test]
fn scalar_entry_refuses_cycles_binding_forms_and_over_budget_replacements() {
    let (mut executor, source) = scalar_fixture();
    let terms = &mut executor.ctx.terms;
    let cyclic = terms.mk_app(Symbol::named("f"), [source.expr], Sort::bitvec(64));
    let record = entry(terms, source.expr, cyclic);
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_none());
    let terms = &mut executor.ctx.terms;
    let predicate = terms.mk_var("predicate", Sort::Bool);
    let body = terms.mk_var("bound", Sort::Bool);
    let binder = terms.mk_forall(vec![("bound".into(), Sort::Bool)], body);
    let record = entry(terms, predicate, binder);
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_none());
    let terms = &mut executor.ctx.terms;
    let wide = terms.mk_app(
        Symbol::named("wide"),
        vec![source.value; PLAN_NODE_BUDGET],
        Sort::bitvec(64),
    );
    let record = entry(terms, source.expr, wide);
    let before = executor.ctx.terms.len();
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_none());
    assert_eq!(
        executor.ctx.terms.len(),
        before,
        "refusal does not rewrite the arena"
    );
    assert!(CheckedPropagationEntry::seal(&executor, &source).is_some());
}

#[test]
fn scalar_entry_depth_bound_includes_shared_dag_paths() {
    let (mut executor, source) = scalar_fixture();
    let terms = &mut executor.ctx.terms;
    let mut below = source.value;
    for _ in 1..MAX_SCALAR_REPLACEMENT_DEPTH {
        below = terms.mk_app(Symbol::named("deep"), [below], Sort::bitvec(64));
    }
    let boundary = terms.mk_app(Symbol::named("deep"), [below], Sort::bitvec(64));
    let record = entry(terms, source.expr, boundary);
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_some());
    let terms = &mut executor.ctx.terms;
    // LIFO sees the shallow occurrence first; it must not suppress the later
    // deeper visit to the same subtree.
    let over = terms.mk_app(Symbol::named("deep"), [boundary], Sort::bitvec(64));
    let shared = terms.mk_app(Symbol::named("both"), [boundary, below], Sort::bitvec(64));
    let record = entry(terms, source.expr, shared);
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_none());
    let record = entry(&mut executor.ctx.terms, source.expr, over);
    assert!(CheckedPropagationEntry::seal(&executor, &record).is_none());
}

#[test]
fn actual_substitution_producer_does_not_emit_a_two_entry_cycle() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let x = terms.mk_var("cycle x", Sort::bitvec(64));
    let y = terms.mk_var("cycle y", Sort::bitvec(64));
    let xy = entry(terms, x, y).source_assertion;
    let yx = entry(terms, y, x).source_assertion;
    let query = terms.mk_app(Symbol::named("query"), [x, y], Sort::Bool);
    let mut roots = vec![xy, yx, query];
    let propagation = Arc::new(Mutex::new(PropagateValues::new()));
    let mut pass = RecordedVariableSubstitution::new(
        Arc::new(Mutex::new(VariableSubstitution::new())),
        Arc::clone(&propagation),
        Box::new(|_, _| true),
    );
    assert!(pass.apply(terms, &mut roots));
    let records = propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .unwrap();
    assert!(!records.entries.is_empty());
    assert!(!(records.entries.iter().any(|e| e.expr == x && e.value == y)
        && records.entries.iter().any(|e| e.expr == y && e.value == x)),
        "the producer's graph cycle check remains required; a local seal is not a batch graph check");
    for recorded in &records.entries {
        assert!(CheckedPropagationEntry::seal(&executor, recorded).is_some());
    }
}

#[test]
fn separately_sealed_opposing_entries_remain_bounded_checked_hints() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let x = terms.mk_var("opposing x", Sort::bitvec(64));
    let y = terms.mk_var("opposing y", Sort::bitvec(64));
    let forward = entry(terms, x, y);
    let reverse = PropagatedEntrySource {
        expr: y,
        value: x,
        source_assertion: forward.source_assertion,
        stamp: forward.stamp,
    };
    let before = terms.mk_app(Symbol::named("p"), [x], Sort::Bool);
    let after = terms.mk_app(Symbol::named("p"), [y], Sort::Bool);
    let authored = [forward.source_assertion, before];
    let original_set = authored.into_iter().collect();
    let raw = [forward, reverse];
    let mut entries = HashMap::default();
    for source in &raw {
        let (key, value) = CheckedPropagationEntry::seal(&executor, source)
            .unwrap()
            .into_current(&executor)
            .unwrap();
        entries.insert(key, value);
    }
    let rewrite = crate::preprocess::PropagatedRewriteRecord {
        before,
        after,
        stamp: raw[0].stamp,
    };
    let (key, value) = CheckedPropagationDerivation::seal(&mut executor, &rewrite, &raw)
        .expect("the actual one-hop record sealer accepts this rewrite")
        .into_current(&executor)
        .unwrap();
    let rewrites = HashMap::from_iter([(key, value)]);
    // Individual seals are not a batch cycle proof. A bounded planner may
    // refuse composition or retain a sound one-hop equality; never trust it.
    for cyclic in [true, false] {
        if !cyclic {
            entries.remove(&y);
        }
        let mut cx = PlanCx::new(&original_set, &authored, &rewrites, &entries, &[], true);
        let result = PropagationChainPlanner {
            terms: &mut executor.ctx.terms,
        }
        .plan_derive_clause(&mut cx, after);
        if !cyclic {
            assert!(result.is_some(), "fresh acyclic replay remains available");
        }
        if let Some(conclusion) = result {
            let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
                &cx.chain,
                &executor.ctx.terms,
                None,
                None,
                &authored,
                &mut |_, _| true,
            )
            .expect("every returned derivation is checked against the exact authored roots");
            assert_eq!(checked.clause(conclusion), Some([after].as_slice()));
        }
    }
}

#[test]
fn scalar_entry_tokens_preserve_query_and_source_scope_stamps() {
    let (mut executor, source) = scalar_fixture();
    let token = CheckedPropagationEntry::seal(&executor, &source).unwrap();
    executor.query_authority_epoch = QueryAuthorityEpoch::fresh();
    assert!(token.into_current(&executor).is_none());
    let token = CheckedPropagationEntry::seal(&executor, &source).unwrap();
    executor
        .ctx
        .process_command(&ay_frontend::Command::Push(1))
        .unwrap();
    assert!(token.into_current(&executor).is_none());
    let token = CheckedPropagationEntry::seal(&executor, &source).unwrap();
    assert_eq!(
        token.into_current(&executor),
        Some((
            source.expr,
            (source.value, source.source_assertion, source.stamp)
        ))
    );
}

#[test]
fn non_variable_harvest_retains_the_legacy_classifier() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let ground = terms.mk_app(Symbol::named("f"), [one], Sort::Int);
    let legacy = entry(terms, ground, two);
    assert!(CheckedPropagationEntry::seal(&executor, &legacy).is_some());
    let terms = &mut executor.ctx.terms;
    let variable = terms.mk_var("x", Sort::Int);
    let non_ground = terms.mk_app(Symbol::named("f"), [variable], Sort::Int);
    let outside_legacy = entry(terms, non_ground, two);
    assert!(CheckedPropagationEntry::seal(&executor, &outside_legacy).is_none());
    let terms = &mut executor.ctx.terms;
    let other_function = terms.mk_app(Symbol::named("g"), [variable], Sort::Int);
    let non_variable = entry(terms, non_ground, other_function);
    assert!(CheckedPropagationEntry::seal(&executor, &non_variable).is_none());
}
