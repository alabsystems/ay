// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ADT/array marker-DAG unsafe prepass on the array-chain regression.

use super::*;

/// The marker-dag prepass once produced only vacuous (all-`true`-state)
/// witnesses, whose replay validation is unsound (it reduces to query
/// satisfiability in isolation and emitted a FALSE UNSAFE on an
/// expected-safe harness); `validate_counterexample` rejects those
/// unconditionally. The route now publishes only original-clause ground
/// evidence (`adt_array_nullary::grounded`), so this genuinely unsafe
/// chain is accepted with a ground derivation that replays on the
/// original clauses, while its safe twin (the read equals the stored 64,
/// a query satisfiable in isolation) must still fail closed.
#[test]
fn adt_array_dag_prepass_accepts_only_ground_evidence_on_array_chain() {
    let source = include_str!("../../../../../tests/chc/regression/false_proof_array_chain.smt2");
    let safe_twin = source.replace(
        "(not (= (select obj_size id) 32))",
        "(not (= (select obj_size id) 64))",
    );
    assert_ne!(safe_twin, source, "the safe twin must change the query");
    for (text, reachable) in [(source.to_string(), true), (safe_twin, false)] {
        let problem = ChcParser::parse(&text).expect("false_proof_array_chain.smt2 should parse");
        let features = crate::classifier::ProblemClassifier::classify(&problem);
        assert!(!features.has_cycles);
        assert_eq!(features.num_facts, 1);
        assert_eq!(features.num_queries, 1);
        assert!(
            features.dag_depth <= SHALLOW_UNSAFE_BMC_MAX_DEPTH,
            "sample chain depth {} must be admitted by the bounded bug prepass",
            features.dag_depth
        );
        let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default());
        let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(5);
        let outcome = adaptive.try_adt_array_nullary_unsafe_prepass(Some(deadline));
        if !reachable {
            assert!(
                outcome.is_none(),
                "an unreachable query must never be Unsafe"
            );
            continue;
        }
        let Some((crate::portfolio::PortfolioResult::Unsafe(cex), evidence)) = outcome else {
            panic!("the reachable chain must be accepted with ground evidence");
        };
        assert!(matches!(
            evidence,
            ValidationEvidence::CounterexampleVerification
        ));
        assert!(
            cex.has_ground_derivation(),
            "only original-clause ground evidence, never a marker witness"
        );
        assert_eq!(cex.ground_checks_unsafe(&problem).ok(), Some(true));
    }
}
