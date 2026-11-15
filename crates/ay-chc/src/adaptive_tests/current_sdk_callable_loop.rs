// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The actual 87d SDK loop bug, distinct from the older component input.

use super::*;

const ORIGINAL: &str =
    include_str!("../../tests/embedded/model_checker_consumer_current_callable_loop_bug.smt2");

fn query_source(name: &str) -> String {
    assert_eq!(ORIGINAL.matches("(query error)").count(), 1);
    ORIGINAL.replace("(query error)", &format!("(query {name})"))
}

fn safe_assertion_source() -> String {
    let input = query_source("error_p32");
    let old = "(not (= |_callable_native_ownership_dual::loop_native_fnmut_borrow_bug_1| #x00000002))) error_p32))";
    assert_eq!(input.matches(old).count(), 1);
    input.replace(old, &old.replace("#x00000002", "#x00000003"))
}

fn candidate(problem: &ChcProblem) -> Option<crate::pdr::Counterexample> {
    let features = ProblemClassifier::classify(problem);
    let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::default());
    let result = adaptive
        .try_linear_bv_array_refutation(&features, Some(Instant::now() + Duration::from_secs(20)));
    result.map(|(result, evidence)| {
        assert_eq!(evidence, ValidationEvidence::BmcCounterexample);
        let PortfolioResult::Unsafe(counterexample) = result else {
            panic!("the bounded lane cannot publish safety: {result:?}");
        };
        crate::ground_derivation::validate_ground_derivation(
            problem,
            counterexample
                .ground_derivation
                .as_ref()
                .expect("retained original ground proof"),
        )
        .expect("independent original replay");
        counterexample
    })
}

#[test]
#[timeout(60_000)]
fn current_sdk_p32_replays_and_tampered_or_changed_sources_refuse() {
    let original = ChcParser::parse(&query_source("error_p32")).expect("actual p32");
    let counterexample = candidate(&original).expect("two actual loop iterations");
    let ground = counterexample
        .ground_derivation
        .expect("original ground witness");
    assert_eq!(ground.len(), 16);
    let error_step = ground
        .steps
        .iter()
        .position(|step| match &original.clauses()[step.clause_index].head {
            ClauseHead::Predicate(id, _) => original
                .get_predicate(*id)
                .is_some_and(|predicate| predicate.name == "error_p32"),
            ClauseHead::False => false,
        })
        .expect("the asserted failure is p32");
    let value_name = "_callable_native_ownership_dual::loop_native_fnmut_borrow_bug_1";
    assert_eq!(
        ground.steps[error_step].env.get(value_name),
        Some(&crate::smt::SmtValue::BitVec(3, 32))
    );
    let validates = |problem: &ChcProblem, proof: &crate::ground_derivation::GroundDerivation| {
        crate::ground_derivation::validate_ground_derivation(problem, proof).is_ok()
    };
    let mut wrong_value = ground.clone();
    wrong_value.steps[error_step]
        .env
        .insert(value_name.to_string(), crate::smt::SmtValue::BitVec(2, 32));
    assert!(!validates(&original, &wrong_value));
    let mut wrong_width = ground.clone();
    wrong_width.steps[error_step]
        .env
        .insert(value_name.to_string(), crate::smt::SmtValue::BitVec(3, 64));
    assert!(!validates(&original, &wrong_width));
    let mut missing = ground.clone();
    missing.steps[error_step].env.remove(value_name);
    assert!(!validates(&original, &missing));
    let mut cyclic = ground.clone();
    cyclic.steps[error_step].premises = vec![error_step];
    assert!(!validates(&original, &cyclic));
    let changed = ChcParser::parse(&safe_assertion_source()).expect("assert final three");
    assert!(!validates(&changed, &ground));
}

fn array_loop(index: u8, expected: u8) -> ChcProblem {
    ChcParser::parse(&format!(r#"
        (set-logic HORN)
        (declare-rel P ((Array (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8)))
        (declare-rel Q ((Array (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8)))
        (declare-rel error ())
        (declare-var a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-var i (_ BitVec 8))
        (rule (P ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x05) #x00))
        (rule (=> (and (P a i) (bvult i #x02))
            (Q (store a #x00 (bvadd #x09 i)) (bvadd i #x01))))
        (rule (=> (Q a i) (P a i)))
        (rule (=> (and (Q a i) (= i #x02) (not (= (select a #x{index:02x}) #x{expected:02x}))) error))
        (query error)
    "#)).expect("finite BV-array loop")
}

#[test]
#[timeout(60_000)]
fn committed_array_loops_keep_last_store_and_total_defaults() {
    for (index, expected, unsafe_expected) in
        [(0, 10, false), (0, 9, true), (32, 5, false), (32, 0, true)]
    {
        assert_eq!(
            candidate(&array_loop(index, expected)).is_some(),
            unsafe_expected,
            "index={index} expected={expected}"
        );
    }
}

#[test]
fn committed_query_arms_keep_safe_first_then_find_the_original_bug() {
    let input = r#"
        (set-logic HORN)
        (declare-rel P ((Array (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8)))
        (declare-rel Q ((Array (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8)))
        (declare-rel first ()) (declare-rel last ()) (declare-rel error ())
        (declare-var a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-var i (_ BitVec 8))
        (rule (P ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x05) #x00))
        (rule (=> (and (P a i) (bvult i #x02))
            (Q (store a #x00 (bvadd #x09 i)) (bvadd i #x01))))
        (rule (=> (Q a i) (P a i)))
        (rule (=> (and (Q a i) (= i #x02) (not (= (select a #x00) #x0a))) first))
        (rule (=> (and (Q a i) (= i #x02) (not (= (select a #x00) #x09))) last))
        (rule (=> first error)) (rule (=> last error)) (query error)
    "#;
    assert!(candidate(&ChcParser::parse(input).expect("safe arm precedes bug arm")).is_some());
    let safe = input.replace("#x09))) last", "#x0a))) last");
    assert_ne!(safe, input);
    assert!(candidate(&ChcParser::parse(&safe).expect("both arms safe")).is_none());
}

#[test]
#[timeout(60_000)]
fn current_sdk_safe_queries_never_propose_an_unsafe_witness() {
    for input in [query_source("error_p10"), safe_assertion_source()] {
        assert!(candidate(&ChcParser::parse(&input).expect("safe original query")).is_none());
    }
}

#[test]
fn array_refutation_respects_expiry_cancellation_and_source_envelopes() {
    let original = array_loop(0, 9);
    let features = ProblemClassifier::classify(&original);
    let adaptive = AdaptivePortfolio::new(original.clone(), AdaptiveConfig::default());
    assert!(adaptive
        .try_linear_bv_array_refutation(&features, Some(Instant::now()))
        .is_none());
    adaptive.cancellation_handle().cancel();
    assert!(adaptive
        .try_linear_bv_array_refutation(&features, None)
        .is_none());
    let oversized = ChcParser::parse(
        &query_source("error_p32").replace("error_p32", &"oversized".repeat(40_000)),
    )
    .expect("large but finite symbol");
    assert!(candidate(&oversized).is_none());
}

#[test]
fn array_refutation_closes_under_effort_without_leaking_into_ordinary_runs() {
    let problem = array_loop(0, 9);
    let features = ProblemClassifier::classify(&problem);
    let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::default());
    let solver = BmcSolver::new(problem.clone(), crate::bmc::BmcConfig::default());
    let meter = crate::run_meter::RunMeter::open(Some(1 << 40), None);
    assert!(adaptive
        .try_linear_bv_array_refutation(&features, None)
        .is_none());
    assert!(matches!(
        solver.solve_array_committed_tree_refutation(20, Duration::from_secs(2), 512),
        PortfolioResult::Unknown
    ));
    let work = meter.close().expect("this scope owns the counting run");
    assert_eq!((work.closed_route_checks, work.ticks), (2, 0));

    // Other metered engines may decide the problem. The default portfolio
    // must never obtain decisive evidence from this unmetered route here.
    let meter = crate::run_meter::RunMeter::open(Some(200), None);
    let (_, report) = AdaptivePortfolio::new(
        problem.clone(),
        AdaptiveConfig::default().with_time_budget(Duration::from_millis(30)),
    )
    .solve_with_adaptive_report();
    assert!(!report.strategy_trace().observations().iter().any(|entry| {
        entry.stage == "linear_bv_array_refutation"
            && matches!(
                entry.outcome,
                crate::AdaptiveStrategyOutcome::Unsafe | crate::AdaptiveStrategyOutcome::Safe
            )
    }));
    let _ = meter
        .close()
        .expect("the default solve preserves its caller's scope");
    assert!(
        candidate(&problem).is_some(),
        "ordinary replay remains available"
    );
}

#[test]
fn array_committed_search_cannot_promote_bounded_exhaustion() {
    let solver = BmcSolver::new(array_loop(0, 9), crate::bmc::BmcConfig::default());
    for (depth, budget, nodes) in [
        (0, Duration::from_secs(1), 512),
        (20, Duration::ZERO, 512),
        (20, Duration::from_secs(1), 0),
    ] {
        assert!(matches!(
            solver.solve_array_committed_tree_refutation(depth, budget, nodes),
            PortfolioResult::Unknown
        ));
    }
}

#[test]
fn array_committed_search_requires_ground_reconstruction() {
    let _switches = crate::ab_switches::TestOverride::set(crate::ab_switches::ChcAbSwitches {
        ground_backtranslation: false,
        ..crate::ab_switches::ChcAbSwitches::default()
    });
    assert!(candidate(&array_loop(0, 9)).is_none());
}

#[test]
#[timeout(120_000)]
fn current_sdk_callable_loop_bug_has_original_ground_refutation() {
    use sha2::{Digest, Sha256};
    assert_eq!(
        format!("{:x}", Sha256::digest(ORIGINAL.as_bytes())),
        "e2db1cec06288fcf9e25842dcf6d866ef9ec21d1d33e0d02e83e53e4400802ec"
    );
    let problem = ChcParser::parse(ORIGINAL).expect("actual SDK CHC");
    let configuration = AdaptiveConfig {
        strict_proofs: true,
        require_ground_unsafe_trace: true,
        verbose: true,
        progress_enabled: true,
        ..AdaptiveConfig::default()
    }
    .with_time_budget(Duration::from_secs(30))
    .with_memory_budget(4096 * 1024 * 1024);
    let (result, report) =
        AdaptivePortfolio::new(problem.clone(), configuration).solve_with_adaptive_report();
    for observation in report.strategy_trace().observations() {
        eprintln!("CURRENT_SDK_LOOP_STAGE {observation:?}");
    }
    assert!(
        report
            .strategy_trace()
            .observations()
            .iter()
            .any(|observation| {
                observation.stage == "linear_bv_array_refutation"
                    && observation.gate_result
                    && observation.outcome == crate::AdaptiveStrategyOutcome::Unsafe
            }),
        "the production default must select the checked array route"
    );
    let VerifiedChcResult::Unsafe(verified) = result else {
        panic!("actual current SDK assertion bug needs a checked original refutation: {result:?}");
    };
    let derivation = verified
        .counterexample()
        .ground_derivation
        .as_ref()
        .expect("a decisive bug retains its original-space ground witness");
    crate::ground_derivation::validate_ground_derivation(&problem, derivation)
        .expect("every original clause and premise must replay");
}
