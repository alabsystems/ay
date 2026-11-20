// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::collections::BTreeSet;

fn indicator_family(n: usize, k: i64) -> (Solver, Vec<Term>) {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    solver.set_timeout(Some(std::time::Duration::from_secs(60)));
    let leaves: Vec<_> = (0..n)
        .map(|i| {
            solver
                .try_declare_const(&format!("edge{i}"), Sort::Bool)
                .unwrap()
        })
        .collect();
    let one = solver.int_const(1);
    let zero = solver.int_const(0);
    let indicators: Vec<_> = leaves
        .iter()
        .map(|&leaf| solver.try_ite(leaf, one, zero).unwrap())
        .collect();
    let sum = solver.try_add_many(&indicators).unwrap();
    let threshold = solver.int_const(k);
    let bound = solver.try_ge(sum, threshold).unwrap();
    solver.try_assert_term(bound).unwrap();
    (solver, leaves)
}

#[test]
fn native_bool_enumeration_requires_original_source_strict_completeness() {
    let (solver, leaves) = indicator_family(4, 2);
    let report = solver.try_enumerate_bool(&leaves, 100).unwrap();
    eprintln!(
        "native enum outcome={:?}, stats={:?}, diagnostic={:?}",
        report.outcome(),
        report.statistics(),
        report.diagnostic()
    );
    assert_eq!(report.outcome(), Outcome::Exhaustive);
    assert_eq!(report.rows().len(), 11);
    assert_eq!(report.statistics().final_source_solve_calls, 1);
    assert!(report
        .completeness_proof()
        .unwrap()
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .is_ok());
    assert!(report.is_current_for(&solver));
    let masks: BTreeSet<_> = report
        .rows()
        .iter()
        .map(|row| {
            row.values()
                .iter()
                .enumerate()
                .fold(0u64, |mask, (i, &value)| mask | (u64::from(value) << i))
        })
        .collect();
    assert_eq!(
        masks,
        (0u64..16).filter(|mask| mask.count_ones() >= 2).collect()
    );
}

fn masks(report: &BoolEnumerationReport) -> BTreeSet<u64> {
    report
        .rows()
        .iter()
        .map(|row| {
            row.values()
                .iter()
                .enumerate()
                .fold(0, |mask, (i, &value)| mask | (u64::from(value) << i))
        })
        .collect()
}

#[test]
fn native_original_ty_family_has_exactly_848_models_and_persistent_work() {
    let (solver, leaves) = indicator_family(10, 4);
    let report = solver.try_enumerate_bool(&leaves, 1024).unwrap();
    eprintln!(
        "TY native enum outcome={:?}, stats={:?}, diagnostic={:?}",
        report.outcome(),
        report.statistics(),
        report.diagnostic()
    );
    assert_eq!(report.outcome(), Outcome::Exhaustive);
    assert_eq!(report.rows().len(), 848);
    assert_eq!(
        masks(&report),
        (0u64..1024).filter(|mask| mask.count_ones() >= 4).collect()
    );
    assert_eq!(report.statistics().candidate_solve_calls, 849);
    assert_eq!(report.statistics().final_source_solve_calls, 1);
    assert!(report
        .completeness_proof()
        .unwrap()
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .is_ok());
    let window = |start: usize| {
        report.rows()[start..start + 50]
            .iter()
            .fold(SearchWork::default(), |mut work, row| {
                work.conflicts += row.search_work().conflicts;
                work.decisions += row.search_work().decisions;
                work.propagations += row.search_work().propagations;
                work
            })
    };
    let early = window(0);
    let late = window(750);
    eprintln!(
        "TY native candidate models1..50={early:?}; models751..800={late:?}; terminal_source={:?}",
        report.statistics()
    );
    let validation = |start: usize| {
        report.rows()[start..start + 50]
            .iter()
            .map(BoolEnumerationRow::original_validation_work)
            .sum::<u64>()
    };
    eprintln!(
        "TY original validation logical work models1..50={}, models751..800={}",
        validation(0),
        validation(750)
    );
    assert_eq!(validation(0), validation(750));
    let materialization = |start: usize| {
        report.rows()[start..start + 50]
            .iter()
            .map(BoolEnumerationRow::candidate_materialization_work)
            .sum::<u64>()
    };
    eprintln!(
        "TY candidate materialization work models1..50={}, models751..800={}",
        materialization(0),
        materialization(750)
    );
    assert_eq!(materialization(0), materialization(750));
    assert!(
        late.conflicts + late.propagations <= (early.conflicts + early.propagations) * 4,
        "candidate work grew with the old assertion pile: {early:?} -> {late:?}"
    );
    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    {
        let source = report
            .completeness_proof()
            .unwrap()
            .alethe_problem_smt2
            .as_deref()
            .unwrap();
        if let Some(reference) = crate::api::solving::tactic_model::bounded_reference(
            &format!("{source}\n(check-sat)\n"),
            "native-projected-bool-TY-848-source-completeness",
        ) {
            assert!(!reference.is_empty());
            assert!(
                reference
                    .split_whitespace()
                    .all(|verdict| verdict == "unsat"),
                "{reference}"
            );
        }
    }
}

#[test]
fn partial_expression_and_unused_projections_are_independently_evaluated() {
    let (mut solver, leaves) = indicator_family(4, 2);
    let report = solver.try_enumerate_bool(&leaves[..2], 100).unwrap();
    assert_eq!(report.outcome(), Outcome::Exhaustive);
    assert_eq!(masks(&report), (0..4).collect());
    assert!(report.rows().iter().all(|row| row.witness().len() == 4
        && row.witness().iter().filter(|(_, value)| *value).count() >= 2));
    let parity = solver.try_xor(leaves[0], leaves[1]).unwrap();
    let expression = solver.try_enumerate_bool(&[parity], 2).unwrap();
    assert_eq!(expression.outcome(), Outcome::Exhaustive);
    assert_eq!(masks(&expression), BTreeSet::from([0, 1]));
    let unused = solver.try_declare_const("unused", Sort::Bool).unwrap();
    let unused = solver.try_enumerate_bool(&[unused], 2).unwrap();
    assert_eq!(unused.outcome(), Outcome::Exhaustive);
    assert_eq!(masks(&unused), BTreeSet::from([0, 1]));
}

#[test]
fn negative_alias_and_constant_projections_keep_literal_polarity() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let p = solver.try_declare_const("p", Sort::Bool).unwrap();
    solver.try_assert_term(p).unwrap();
    let negative = solver.try_not(p).unwrap();
    let truth = solver.bool_const(true);
    let report = solver.try_enumerate_bool(&[negative, truth], 2).unwrap();
    assert_eq!(
        report.outcome(),
        Outcome::Exhaustive,
        "{:?}",
        report.diagnostic()
    );
    assert_eq!(report.rows().len(), 1);
    assert_eq!(report.rows()[0].values(), &[false, true]);
}

#[test]
fn cap_empty_projection_and_original_unsat_have_exact_semantics() {
    let (solver, leaves) = indicator_family(4, 2);
    let capped = solver.try_enumerate_bool(&leaves, 3).unwrap();
    assert_eq!(capped.outcome(), Outcome::Capped);
    assert_eq!(capped.rows().len(), 3);
    assert_eq!(capped.statistics().candidate_solve_calls, 4);
    assert_eq!(capped.statistics().final_source_solve_calls, 0);
    assert!(capped.completeness_proof().is_none());
    let zero = solver.try_enumerate_bool(&leaves, 0).unwrap();
    assert_eq!(zero.outcome(), Outcome::Capped);
    assert!(zero.rows().is_empty());
    let empty = solver.try_enumerate_bool(&[], 1).unwrap();
    assert_eq!(empty.outcome(), Outcome::Exhaustive);
    assert_eq!(empty.rows().len(), 1);
    assert!(empty.rows()[0].values().is_empty());
    let (unsat, leaves) = indicator_family(4, 5);
    let empty = unsat.try_enumerate_bool(&leaves, 0).unwrap();
    assert_eq!(
        empty.outcome(),
        Outcome::Exhaustive,
        "{:?}",
        empty.diagnostic()
    );
    assert!(empty.rows().is_empty());
    assert_eq!(empty.statistics().final_source_solve_calls, 1);
}

#[test]
fn original_model_and_scope_survive_enumeration_and_binding_retires_on_mutation() {
    let (mut solver, leaves) = indicator_family(4, 2);
    solver.push();
    solver.try_assert_term(leaves[0]).unwrap();
    assert!(solver.try_check_sat().unwrap().is_sat());
    let prior = format!("{:?}", solver.executor.last_result());
    let prior_model = solver.try_get_model().unwrap();
    let prior_assertions = solver.assertions();
    let prior_scope = solver.scope_level;
    let report = solver.try_enumerate_bool(&leaves[..2], 100).unwrap();
    assert_eq!(
        report.outcome(),
        Outcome::Exhaustive,
        "{:?}",
        report.diagnostic()
    );
    assert_eq!(prior, format!("{:?}", solver.executor.last_result()));
    assert_eq!(prior_model, solver.try_get_model().unwrap());
    assert_eq!(prior_assertions, solver.assertions());
    assert_eq!(prior_scope, solver.scope_level);
    assert!(report.is_current_for(&solver));
    solver.try_declare_const("later", Sort::Bool).unwrap();
    assert!(!report.is_current_for(&solver));
    assert_eq!(report.outcome(), Outcome::Exhaustive);
    solver.try_pop().unwrap();
    assert!(!report.is_current_for(&solver));
}

#[test]
fn foreign_raw_duplicate_and_nonboolean_projection_handles_refuse() {
    let (mut solver, leaves) = indicator_family(3, 1);
    let (other, foreign) = indicator_family(3, 1);
    let original = solver.assertions();
    assert!(matches!(
        solver.try_enumerate_bool(&foreign[..1], 1),
        Err(SolverError::InvalidTermHandle { .. })
    ));
    assert!(matches!(
        solver.try_enumerate_bool(&[Term::from_raw(leaves[0].to_raw())], 1),
        Err(SolverError::InvalidTermHandle { .. })
    ));
    assert!(solver
        .try_enumerate_bool(&[leaves[0], leaves[0]], 1)
        .is_err());
    let integer = solver.int_const(1);
    assert!(solver.try_enumerate_bool(&[integer], 1).is_err());
    assert_eq!(original, solver.assertions());
    drop(other);
}

#[test]
fn finite_integer_width_exceeds_machine_words_without_wrapping() {
    use num_bigint::BigInt;
    use num_traits::One;
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let p = solver.try_declare_const("p", Sort::Bool).unwrap();
    let large = BigInt::one() << 140usize;
    let positive = solver.int_const_bigint(&large);
    let negative = solver.int_const_bigint(&-&large);
    let choice = solver.try_ite(p, positive, negative).unwrap();
    let three = solver.int_const(3);
    let product = solver.try_mul(choice, three).unwrap();
    let zero = solver.int_const(0);
    let root = solver.try_ge(product, zero).unwrap();
    solver.try_assert_term(root).unwrap();
    let report = solver.try_enumerate_bool(&[p], 2).unwrap();
    assert_eq!(report.outcome(), Outcome::Exhaustive);
    assert_eq!(masks(&report), BTreeSet::from([1]));
    assert!(report.statistics().signed_integer_width >= 143);
}

#[test]
fn unsupported_free_integer_is_refused_without_state_mutation() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.try_declare_const("x", Sort::Int).unwrap();
    let zero = solver.int_const(0);
    let root = solver.try_ge(x, zero).unwrap();
    solver.try_assert_term(root).unwrap();
    let before = solver.terms().snapshot_stamp();
    assert!(matches!(
        solver.try_enumerate_bool(&[], 100),
        Err(SolverError::InvalidArgument { .. })
    ));
    assert_eq!(before, solver.terms().snapshot_stamp());
    assert_eq!(solver.assertions(), vec![root]);
}

#[test]
fn native_cancellation_timeout_and_term_ceiling_do_not_change_prior_decision() {
    use std::time::Duration;
    for mode in 0..4 {
        let (mut solver, leaves) = indicator_family(4, 2);
        assert!(solver.try_check_sat().unwrap().is_sat());
        let prior = format!("{:?}", solver.executor.last_result());
        match mode {
            0 => solver.interrupt(),
            1 => solver.set_timeout(Some(Duration::ZERO)),
            2 => solver.set_term_memory_limit(Some(0)),
            _ => solver.set_memory_limit(Some(0)),
        }
        let expected = match mode {
            0 => UnknownReason::Interrupted,
            1 => UnknownReason::Timeout,
            _ => UnknownReason::MemoryLimit,
        };
        match solver.try_enumerate_bool(&leaves, 100) {
            Err(SolverError::BoolEnumerationStopped(reason)) => assert_eq!(reason, expected),
            Ok(report) => {
                assert_eq!(report.outcome(), Outcome::Incomplete(expected));
                assert!(report.completeness_proof().is_none());
            }
            other => panic!("unexpected resource refusal: {other:?}"),
        }
        assert_eq!(prior, format!("{:?}", solver.executor.last_result()));
    }
}

#[test]
fn deterministic_decision_allowance_is_shared_across_candidate_models() {
    let (mut solver, leaves) = indicator_family(10, 4);
    solver.executor.set_ground_budget_enabled(false);
    solver.executor.set_decision_limit(Some(120));
    let report = solver.try_enumerate_bool(&leaves, 1024).unwrap();
    assert_eq!(
        report.outcome(),
        Outcome::Incomplete(UnknownReason::ResourceLimit)
    );
    assert!(!report.rows().is_empty());
    assert!(report.rows().len() < 848);
    assert!(report.completeness_proof().is_none());
    assert_eq!(report.statistics().final_source_solve_calls, 0);
}

#[test]
fn inherited_counted_run_is_explicitly_refused_and_check_budget_is_not_renewed() {
    let (solver, leaves) = indicator_family(4, 2);
    let run = Guard::root_child(ChildSpec::new(NodeLabel::Run).with_rlimit(Some(1_000_000)));
    {
        let _scope = run.enter();
        assert!(matches!(
            solver.try_enumerate_bool(&leaves, 100),
            Err(SolverError::InvalidArgument { .. })
        ));
    }
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(500)));
    let _scope = check.enter();
    match solver.try_enumerate_bool(&leaves, 100) {
        Err(SolverError::BoolEnumerationStopped(reason)) => {
            assert_eq!(reason, UnknownReason::ResourceLimit)
        }
        Ok(report) => {
            assert_eq!(
                report.outcome(),
                Outcome::Incomplete(UnknownReason::ResourceLimit)
            );
            assert!(report.completeness_proof().is_none());
        }
        other => panic!("unexpected guard-budget result: {other:?}"),
    }
    assert!(check.remaining().unwrap() < 500);
}

fn ample_owner() -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(100_000_000, 1 << 30),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

#[test]
fn mutated_candidate_leaf_projection_or_missing_assignment_cannot_publish_a_row() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let p = solver.try_declare_const("p", Sort::Bool).unwrap();
    solver.try_assert_term(p).unwrap();
    let owner = ample_owner();
    let mapping = candidate::CandidateMap {
        projection: vec![candidate::Encoding::Bool(1)],
        leaves: vec![(p.id(), candidate::Encoding::Bool(1))],
    };
    assert!(mapping
        .validate(&solver, &[p.id()], &[p], &[true], &owner)
        .is_ok());
    let missing_leaf = candidate::CandidateMap {
        projection: vec![candidate::Encoding::Bool(1)],
        leaves: Vec::new(),
    };
    assert!(matches!(
        missing_leaf.validate(&solver, &[p.id()], &[p], &[true], &owner),
        Err(Failure::Incomplete(UnknownReason::Incomplete))
    ));
    assert!(matches!(
        mapping.validate(&solver, &[p.id()], &[p], &[false], &owner),
        Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
    ));
    let wrong_projection = candidate::CandidateMap {
        projection: vec![candidate::Encoding::Bool(-1)],
        leaves: vec![(p.id(), candidate::Encoding::Bool(1))],
    };
    assert!(matches!(
        wrong_projection.validate(&solver, &[p.id()], &[p], &[true], &owner),
        Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
    ));
    assert!(matches!(
        mapping.validate(&solver, &[p.id()], &[p], &[], &owner),
        Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
    ));
    let zero = candidate::CandidateMap {
        projection: vec![candidate::Encoding::Bool(0)],
        leaves: vec![(p.id(), candidate::Encoding::Bool(1))],
    };
    assert!(matches!(
        zero.validate(&solver, &[p.id()], &[p], &[true], &owner),
        Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
    ));
}

#[test]
fn circuit_exhaustion_cannot_replace_a_satisfiable_or_stopped_source_query() {
    use std::time::Duration;
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let p = solver.try_declare_const("p", Sort::Bool).unwrap();
    solver.try_assert_term(p).unwrap();
    let owner = ample_owner();
    let compiled = finite_bool::compile(solver.terms(), &[p.id()], &[p.id()], &owner).unwrap();
    let mut source = source::copy(solver.terms(), &[p.id()], &compiled, &owner).unwrap();
    source.solver.set_produce_proofs(true);
    source
        .solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    let mut report = solver.enumeration_report(&[p], &owner).unwrap();
    // Propose circuit exhaustion WITHOUT the necessary projection blocker.
    // The real ordinary source solver still finds the omitted original model.
    source.finish(&owner, &mut report.common).unwrap();
    assert_eq!(
        report.outcome(),
        Outcome::Incomplete(UnknownReason::SelfCheckRejected)
    );
    assert!(report.diagnostic().unwrap().contains("remains satisfiable"));
    assert!(report.completeness_proof().is_none());
    assert_eq!(report.statistics().final_source_solve_calls, 1);
    assert!(matches!(
        source.finish(&owner, &mut report.common),
        Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
    ));
    let mut stopped = source::copy(solver.terms(), &[p.id()], &compiled, &owner).unwrap();
    stopped.solver.set_timeout(Some(Duration::ZERO));
    let mut report = solver.enumeration_report(&[p], &owner).unwrap();
    stopped.finish(&owner, &mut report.common).unwrap();
    assert_eq!(
        report.outcome(),
        Outcome::Incomplete(UnknownReason::Timeout)
    );
    assert!(report.completeness_proof().is_none());
    assert_eq!(report.statistics().final_source_solve_calls, 1);
}

#[test]
fn cancellation_at_real_native_certification_withholds_exhaustiveness() {
    use std::sync::atomic::AtomicBool;
    let (solver, leaves) = indicator_family(4, 2);
    let certified = Arc::new(AtomicBool::new(false));
    let observed = certified.clone();
    let _scope = enter_check_stop(Arc::new(move || {
        if current_guard()
            .and_then(|guard| guard.nearest(NodeLabel::Certify))
            .is_some()
        {
            observed.store(true, Ordering::Relaxed);
            false
        } else {
            observed.load(Ordering::Relaxed)
        }
    }));
    let report = solver.try_enumerate_bool(&leaves, 100).unwrap();
    assert!(
        certified.load(Ordering::Relaxed),
        "the actual native certification route must have run"
    );
    assert_eq!(
        report.outcome(),
        Outcome::Incomplete(UnknownReason::Interrupted)
    );
    assert!(report.completeness_proof().is_none());
    assert_eq!(report.statistics().final_source_solve_calls, 1);
    assert_eq!(report.rows().len(), 11);
}

#[test]
fn full_reset_retires_the_report_and_projection_handles() {
    let (mut solver, leaves) = indicator_family(3, 1);
    let report = solver.try_enumerate_bool(&leaves[..1], 2).unwrap();
    assert_eq!(report.outcome(), Outcome::Exhaustive);
    solver.reset();
    let _replacement = solver.try_declare_const("replacement", Sort::Bool).unwrap();
    assert!(!report.is_current_for(&solver));
    assert!(matches!(
        solver.try_enumerate_bool(&leaves[..1], 2),
        Err(SolverError::InvalidTermHandle { .. })
    ));
}

#[test]
fn explicitly_stricter_wire_policy_does_not_receive_a_holey_completeness_artifact() {
    let (mut solver, leaves) = indicator_family(4, 5);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    solver.set_verification_level(crate::api::VerificationLevel::FullyVerified);
    solver.executor.set_self_check(true);
    let report = solver.try_enumerate_bool(&leaves, 0).unwrap();
    match report.outcome() {
        Outcome::Exhaustive => {
            let proof = report.completeness_proof().unwrap();
            assert!(proof
                .accept_for_consumer(ProofAcceptanceMode::Strict)
                .is_ok());
            assert!(!proof.alethe.contains(":rule hole"));
        }
        Outcome::Incomplete(_) => assert!(report.completeness_proof().is_none()),
        other => panic!("an inconsistent original source cannot be capped: {other:?}"),
    }
    assert!(solver.executor.ctx.check_proofs_strict_requested());
    assert_eq!(
        solver.verification_level(),
        crate::api::VerificationLevel::FullyVerified
    );
    assert!(solver.executor.self_check());
}
