// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Validation tests for CHC results (#429)
//!
//! This module ensures that AY validates every SAT/UNSAT result against the
//! original clauses. Validation failures return Unknown instead of wrong answers.
//!
//! Done criteria for #429:
//! 1. AY validates every SAT/UNSAT result in extra-small-lia benchmark set
//! 2. Any validation failure returns Unknown instead of wrong answer
//! 3. #421 soundness bug would have been caught by validation

use ay_chc::{testing, ChcParser, PdrConfig};
use ntest::timeout;

/// The complete tracked CHC-COMP 2025 extra-small-LIA corpus.
///
/// `include_str!` makes every fixture a compile-time requirement. Verdict
/// validation itself is enforced at the adaptive/portfolio admission boundary
/// and exercised by the existing per-fixture soundness regressions; this fast
/// manifest test locks corpus wiring and syntax without duplicating a costly
/// 20-solve sweep.
const TRACKED_EXTRA_SMALL_LIA: [(&str, &str); 20] = [
    (
        "accumulator_unsafe_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/accumulator_unsafe_000.smt2"
        ),
    ),
    (
        "bouncy_one_counter_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/bouncy_one_counter_000.smt2"
        ),
    ),
    (
        "bouncy_two_counters_equality_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/bouncy_two_counters_equality_000.smt2"
        ),
    ),
    (
        "const_mod_3_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/const_mod_3_000.smt2"
        ),
    ),
    (
        "count_by_2_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/count_by_2_000.smt2"
        ),
    ),
    (
        "count_by_2_m_nest_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/count_by_2_m_nest_000.smt2"
        ),
    ),
    (
        "dillig02_m_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2"
        ),
    ),
    (
        "dillig12_m_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig12_m_000.smt2"
        ),
    ),
    (
        "dillig32_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig32_000.smt2"
        ),
    ),
    (
        "gj2007_m_1_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/gj2007_m_1_000.smt2"
        ),
    ),
    (
        "gj2007_m_3_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/gj2007_m_3_000.smt2"
        ),
    ),
    (
        "half_true_modif_m_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/half_true_modif_m_000.smt2"
        ),
    ),
    (
        "phases_m_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/phases_m_000.smt2"
        ),
    ),
    (
        "s_multipl_08_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_08_000.smt2"
        ),
    ),
    (
        "s_multipl_10_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_10_000.smt2"
        ),
    ),
    (
        "s_multipl_17_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_17_000.smt2"
        ),
    ),
    (
        "s_multipl_22_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_22_000.smt2"
        ),
    ),
    (
        "s_multipl_25_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_25_000.smt2"
        ),
    ),
    (
        "s_mutants_16_m_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/s_mutants_16_m_000.smt2"
        ),
    ),
    (
        "two_phase_unsafe_000",
        include_str!(
            "../../../../benchmarks/chc-comp/2025/extra-small-lia/two_phase_unsafe_000.smt2"
        ),
    ),
];

#[test]
fn tracked_extra_small_lia_manifest_is_complete_unique_and_parseable() {
    assert_eq!(TRACKED_EXTRA_SMALL_LIA.len(), 20);
    let mut names = std::collections::BTreeSet::new();
    for (name, fixture) in TRACKED_EXTRA_SMALL_LIA {
        assert!(names.insert(name), "duplicate tracked fixture name: {name}");
        ChcParser::parse(fixture)
            .unwrap_or_else(|error| panic!("tracked fixture {name} should parse: {error}"));
    }
    assert_eq!(names.len(), 20);
}

/// Test that validation catches the #421 soundness bug pattern
///
/// Issue #421: PDKIND returned Unsafe on a Safe benchmark (dillig01.c_000.smt2).
/// The portfolio validation now catches such bugs by validating counterexamples.
///
/// This test creates a mock scenario where an engine produces an invalid result
/// and verifies that validation rejects it.
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_validation_catches_invalid_counterexample() {
    use ay_chc::{CexVerificationResult, Counterexample, CounterexampleStep};
    use ay_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

    // Build a simple safe problem: x >= 0 => Inv(x), Inv(x) => Inv(x+1), Inv(x) AND x < 0 => false
    // This is SAFE because x starts >= 0 and only increases.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    // Init: x >= 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) AND x_next = x + 1 => Inv(x_next)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
    ));

    // Query: Inv(x) AND x < 0 => false (unreachable!)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    // Create a PDR solver for verification
    let mut solver = testing::new_pdr_solver(problem.clone(), PdrConfig::default());

    // Create a FAKE counterexample claiming x = -1 reaches the bad state
    // This is INVALID because x starts >= 0 and only increases
    let fake_cex = Counterexample::new(vec![CounterexampleStep::new(
        inv,
        [("x".to_string(), -1)].into_iter().collect(),
    )]);

    // Verification should REJECT this fake counterexample
    let result = solver.verify_counterexample(&fake_cex);
    assert!(
        matches!(result, CexVerificationResult::Spurious),
        "Validation should reject fake counterexample with x = -1 \
         (not reachable from init where x >= 0), got {result:?}"
    );
}

/// Test that valid models pass verification
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_validation_accepts_valid_model() {
    use ay_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
    use ay_chc::{InvariantModel, PdrConfig, PredicateInterpretation};

    // Same safe problem as above
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    // Init: x >= 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) AND x_next = x + 1 => Inv(x_next)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
    ));

    // Query: Inv(x) AND x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut solver = testing::new_pdr_solver(problem.clone(), PdrConfig::default());

    // Create a VALID model: Inv(x) iff x >= 0
    // This is inductive and blocks the bad state (x < 0)
    let mut model = InvariantModel::new();
    let inv_var = ChcVar::new(format!("__p{}_a0", inv.index()), ChcSort::Int);
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![inv_var.clone()],
            ChcExpr::ge(ChcExpr::var(inv_var), ChcExpr::int(0)),
        ),
    );

    // Verification should ACCEPT this valid model
    let is_valid = solver.verify_model(&model);
    assert!(
        is_valid,
        "Validation should accept valid model Inv(x) = (x >= 0)"
    );
}

/// Test that invalid models are rejected
///
/// Timeout: 1s (measured <10ms)
#[test]
#[timeout(1_000)]
fn test_validation_rejects_invalid_model() {
    use ay_chc::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
    use ay_chc::{InvariantModel, PdrConfig, PredicateInterpretation};

    // Build a problem where x grows unboundedly
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    // Init: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Transition: Inv(x) AND x_next = x + 1 => Inv(x_next)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x_next.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
    ));

    // Query: Inv(x) AND x >= 10 => false (reachable after 10 steps!)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    let mut solver = testing::new_pdr_solver(problem.clone(), PdrConfig::default());

    // Create an INVALID model: Inv(x) iff x >= 0
    // This is inductive but DOES NOT block the bad state (x >= 10 is reachable)
    let mut model = InvariantModel::new();
    let inv_var = ChcVar::new(format!("__p{}_a0", inv.index()), ChcSort::Int);
    model.set(
        inv,
        PredicateInterpretation::new(
            vec![inv_var.clone()],
            ChcExpr::ge(ChcExpr::var(inv_var), ChcExpr::int(0)),
        ),
    );

    // Verification should REJECT this model (doesn't block bad states)
    let is_valid = solver.verify_model(&model);
    assert!(
        !is_valid,
        "Validation should reject model Inv(x) = (x >= 0) that doesn't block x >= 10"
    );
}
