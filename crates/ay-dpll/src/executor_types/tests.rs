// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn unknown_reason_display_matches_smtlib_style() {
    assert_eq!(UnknownReason::Timeout.to_string(), "timeout");
    assert_eq!(UnknownReason::ResourceLimit.to_string(), "resourceout");
    assert_eq!(UnknownReason::MemoryLimit.to_string(), "memout");
    assert_eq!(UnknownReason::Interrupted.to_string(), "interrupted");
    assert_eq!(UnknownReason::Incomplete.to_string(), "incomplete");
    assert_eq!(
        UnknownReason::QuantifierRoundLimit.to_string(),
        "(incomplete quantifier-round-limit)"
    );
    assert_eq!(
        UnknownReason::QuantifierDeferred.to_string(),
        "(incomplete quantifier-deferred)"
    );
    assert_eq!(
        UnknownReason::QuantifierUnhandled.to_string(),
        "(incomplete quantifier-unhandled)"
    );
    assert_eq!(
        UnknownReason::QuantifierCegqiIncomplete.to_string(),
        "(incomplete quantifier-cegqi)"
    );
    assert_eq!(
        UnknownReason::QuantifierEmatchingExistsIncomplete.to_string(),
        "(incomplete quantifier-ematching-exists)"
    );
    assert_eq!(UnknownReason::SplitLimit.to_string(), "incomplete");
    assert_eq!(UnknownReason::Unsupported.to_string(), "unsupported");
    assert_eq!(
        UnknownReason::UnsupportedArithmetic.to_string(),
        "(unsupported arithmetic)"
    );
    assert_eq!(
        UnknownReason::UnsupportedMixedCollection.to_string(),
        "(unsupported mixed-collection)"
    );
    assert_eq!(UnknownReason::Unknown.to_string(), "unknown");
}

#[test]
fn unknown_reason_code_and_name_are_stable_consumer_values() {
    let cases = [
        (UnknownReason::Timeout, "timeout", "Timeout"),
        (
            UnknownReason::ResourceLimit,
            "resource_limit",
            "Resource limit",
        ),
        (UnknownReason::MemoryLimit, "memory_limit", "Memory limit"),
        (UnknownReason::Interrupted, "interrupted", "Interrupted"),
        (UnknownReason::Incomplete, "incomplete", "Incomplete"),
        (
            UnknownReason::SelfCheckRejected,
            "self_check_rejected",
            "Self-check REJECTED a computed verdict",
        ),
        (
            UnknownReason::QuantifierRoundLimit,
            "quantifier_round_limit",
            "Quantifier round limit",
        ),
        (
            UnknownReason::QuantifierDeferred,
            "quantifier_deferred",
            "Quantifier deferred",
        ),
        (
            UnknownReason::QuantifierUnhandled,
            "quantifier_unhandled",
            "Quantifier unhandled",
        ),
        (
            UnknownReason::QuantifierCegqiIncomplete,
            "quantifier_cegqi_incomplete",
            "Quantifier CEGQI incomplete",
        ),
        (
            UnknownReason::QuantifierEmatchingExistsIncomplete,
            "quantifier_ematching_exists_incomplete",
            "Quantifier E-matching exists incomplete",
        ),
        (UnknownReason::SplitLimit, "split_limit", "Split limit"),
        (
            UnknownReason::ExpressionSplit,
            "expression_split",
            "Expression split",
        ),
        (UnknownReason::Unsupported, "unsupported", "Unsupported"),
        (
            UnknownReason::UnsupportedArithmetic,
            "unsupported_arithmetic",
            "Unsupported arithmetic",
        ),
        (
            UnknownReason::UnsupportedMixedCollection,
            "unsupported_mixed_collection",
            "Unsupported mixed collection",
        ),
        (
            UnknownReason::InternalError,
            "internal_error",
            "Internal error",
        ),
        (UnknownReason::Unknown, "unknown", "Unknown"),
        (
            UnknownReason::ProofTrusted,
            "proof_trusted",
            "Strict proofs WITHHELD a trust-bearing UNSAT",
        ),
    ];

    assert_eq!(
        UnknownReason::ALL.map(|reason| reason.code()),
        cases.map(|case| case.1)
    );

    for (reason, code, name) in cases {
        assert_eq!(reason.code(), code);
        assert_eq!(reason.name(), name);
    }
}

#[test]
fn unknown_reason_registry_is_exhaustive_and_has_unique_codes() {
    fn variant_bit(reason: UnknownReason) -> u32 {
        match reason {
            UnknownReason::Timeout => 1 << 0,
            UnknownReason::ResourceLimit => 1 << 1,
            UnknownReason::MemoryLimit => 1 << 2,
            UnknownReason::Interrupted => 1 << 3,
            UnknownReason::Incomplete => 1 << 4,
            UnknownReason::SelfCheckRejected => 1 << 5,
            UnknownReason::QuantifierRoundLimit => 1 << 6,
            UnknownReason::QuantifierDeferred => 1 << 7,
            UnknownReason::QuantifierUnhandled => 1 << 8,
            UnknownReason::QuantifierCegqiIncomplete => 1 << 9,
            UnknownReason::QuantifierEmatchingExistsIncomplete => 1 << 10,
            UnknownReason::SplitLimit => 1 << 11,
            UnknownReason::ExpressionSplit => 1 << 12,
            UnknownReason::Unsupported => 1 << 13,
            UnknownReason::UnsupportedArithmetic => 1 << 14,
            UnknownReason::UnsupportedMixedCollection => 1 << 15,
            UnknownReason::InternalError => 1 << 16,
            UnknownReason::Unknown => 1 << 17,
            UnknownReason::ProofTrusted => 1 << 18,
        }
    }

    let registered_variants = UnknownReason::ALL
        .iter()
        .copied()
        .fold(0_u32, |bits, reason| bits | variant_bit(reason));
    assert_eq!(registered_variants, (1_u32 << 19) - 1);

    let unique_codes = UnknownReason::ALL
        .iter()
        .map(UnknownReason::code)
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(unique_codes.len(), UnknownReason::ALL.len());

    assert_eq!(
        UnknownReason::ALL.map(UnknownReason::origin),
        UnknownOrigin::ALL
    );
    assert_eq!(
        UnknownOrigin::ALL.map(UnknownOrigin::reason),
        UnknownReason::ALL
    );
}

#[test]
fn unknown_origin_inventory_names_real_production_source_anchors() {
    let check_sat = include_str!("../executor/check_sat.rs");
    let result_mapping = include_str!("../executor/quantifier_loop/result_mapping.rs");
    let sources = [
        (
            UnknownOrigin::SolveDeadline,
            check_sat,
            "UnknownOrigin::SolveDeadline",
        ),
        (
            UnknownOrigin::DeterministicResourceBudget,
            include_str!("../executor/theories/model_helpers.rs"),
            "UnknownOrigin::DeterministicResourceBudget",
        ),
        (
            UnknownOrigin::MemoryBudget,
            check_sat,
            "UnknownOrigin::MemoryBudget",
        ),
        (
            UnknownOrigin::InterruptFlag,
            check_sat,
            "UnknownOrigin::InterruptFlag",
        ),
        (
            UnknownOrigin::IncompleteSolverLane,
            check_sat,
            "UnknownOrigin::IncompleteSolverLane",
        ),
        (
            UnknownOrigin::VerdictCertification,
            include_str!("../executor/unsat_cert.rs"),
            "UnknownOrigin::VerdictCertification",
        ),
        (
            UnknownOrigin::EmatchingRoundBudget,
            result_mapping,
            "UnknownReason::QuantifierRoundLimit",
        ),
        (
            UnknownOrigin::DeferredInstantiation,
            result_mapping,
            "UnknownReason::QuantifierDeferred",
        ),
        (
            UnknownOrigin::UnhandledQuantifier,
            result_mapping,
            "UnknownReason::QuantifierUnhandled",
        ),
        (
            UnknownOrigin::CegqiRefinement,
            include_str!("../executor/quantifier_loop/cegqi_refinement.rs"),
            "UnknownOrigin::CegqiRefinement",
        ),
        (
            UnknownOrigin::ExistentialEmatching,
            result_mapping,
            "UnknownOrigin::ExistentialEmatching",
        ),
        (
            UnknownOrigin::TheorySplitBudget,
            include_str!("../pipeline_incremental_split_assume_macros.rs"),
            "UnknownOrigin::TheorySplitBudget",
        ),
        (
            UnknownOrigin::UnsupportedExpressionSplit,
            include_str!("../pipeline_incremental_split_eager_shared_macros.rs"),
            "UnknownOrigin::UnsupportedExpressionSplit",
        ),
        (
            UnknownOrigin::UnsupportedFeature,
            include_str!("../executor.rs"),
            "UnknownOrigin::UnsupportedFeature",
        ),
        (
            UnknownOrigin::UnsupportedArithmeticFragment,
            check_sat,
            "UnknownOrigin::UnsupportedArithmeticFragment",
        ),
        (
            UnknownOrigin::UnsupportedMixedCollection,
            include_str!("../executor/theories/seq.rs"),
            "UnknownOrigin::UnsupportedMixedCollection",
        ),
        (
            UnknownOrigin::ExecutorFailure,
            include_str!("../api/solving/check.rs"),
            "UnknownReason::InternalError",
        ),
        (
            UnknownOrigin::UntaggedSolverUnknown,
            include_str!("../executor/lifecycle.rs"),
            "UnknownReason::Unknown",
        ),
        (
            UnknownOrigin::TerminalTrust,
            include_str!("../executor/unsat_cert.rs"),
            "UnknownOrigin::TerminalTrust",
        ),
    ];

    assert_eq!(
        sources.map(|(origin, _, _)| origin),
        UnknownOrigin::ALL,
        "source-anchor inventory must be exact and ordered"
    );
    for (origin, source, producer_marker) in sources {
        let anchor = origin
            .production_chokepoint()
            .rsplit("::")
            .next()
            .expect("chokepoint has an anchor");
        assert!(
            source.contains(anchor),
            "origin={} names missing production anchor {anchor:?}",
            origin.code()
        );
        assert!(
            source.contains(producer_marker),
            "origin={} source lacks exact producer marker {producer_marker:?}",
            origin.code()
        );
    }
}

#[test]
fn stat_value_display_formats_basic_types() {
    assert_eq!(StatValue::Int(7).to_string(), "7");
    assert_eq!(StatValue::Float(1.234).to_string(), "1.23");
    assert_eq!(StatValue::String("x".to_string()).to_string(), "\"x\"");
}

#[test]
fn statistics_get_int_reads_known_and_extra_ints() {
    let mut stats = Statistics::new();
    stats.conflicts = 3;
    stats.rlimit_count = 11;
    stats.set_int("my_stat", 9);
    stats.set_float("my_float", 1.0);

    assert_eq!(stats.get_int("conflicts"), Some(3));
    assert_eq!(stats.get_int("rlimit_count"), Some(11));
    assert_eq!(stats.get_int("rlimit-count"), Some(11));
    assert_eq!(stats.get_int("my_stat"), Some(9));
    assert_eq!(stats.get_int("my_float"), None);
    assert_eq!(stats.get_int("missing"), None);
}

#[test]
fn statistics_display_includes_core_fields_and_extra() {
    let mut stats = Statistics::new();
    stats.conflicts = 7;
    stats.time_seconds = 1.25;
    stats.memory_mb = 12.5;
    stats.max_memory_mb = 13.5;
    stats.rlimit_count = 99;
    stats.set_int("extra_int", 12);

    let s = stats.to_string();
    assert!(s.starts_with("(:statistics\n"));
    assert!(s.contains(":conflicts 7"));
    assert!(s.contains(":time 1.25"));
    assert!(s.contains(":memory 12.50"));
    assert!(s.contains(":max-memory 13.50"));
    assert!(s.contains(":rlimit-count 99"));
    assert!(s.contains(":extra_int 12"));
    assert!(s.ends_with(')'));
}

#[test]
fn test_debug_assert_consistency_passes_for_valid_stats() {
    let mut stats = Statistics::new();
    stats.conflicts = 10;
    stats.propagations = 20;
    stats.theory_conflicts = 5;
    stats.theory_propagations = 10;
    // Should not panic: theory <= SAT
    stats.debug_assert_consistency();
}

#[test]
fn test_debug_assert_consistency_passes_for_zero_stats() {
    let stats = Statistics::new();
    stats.debug_assert_consistency();
}

#[test]
fn test_debug_assert_consistency_passes_for_equal_stats() {
    let mut stats = Statistics::new();
    stats.conflicts = 5;
    stats.propagations = 5;
    stats.theory_conflicts = 5;
    stats.theory_propagations = 5;
    stats.debug_assert_consistency();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "BUG: theory_conflicts")]
fn test_debug_assert_consistency_panics_when_theory_conflicts_exceed_sat() {
    let mut stats = Statistics::new();
    stats.conflicts = 1;
    stats.propagations = 2;
    stats.theory_conflicts = 2;
    stats.theory_propagations = 2;
    stats.debug_assert_consistency();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "BUG: theory_propagations")]
fn test_debug_assert_consistency_panics_when_theory_propagations_exceed_sat() {
    let mut stats = Statistics::new();
    stats.conflicts = 2;
    stats.propagations = 1;
    stats.theory_conflicts = 2;
    stats.theory_propagations = 2;
    stats.debug_assert_consistency();
}
