// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Real search/validation acceptance targets. Unlike injected controls, these
//! require a nonempty original-source witness. Run under the external guard.

use super::*;

#[test]
fn scalar_and_array_reachability_require_real_original_witnesses() {
    for (fixture, text) in [("scalar", SCALAR), ("array", ARRAY)] {
        eprintln!("original Unsafe recovery fixture: {fixture}");
        assert_eq!(text.matches(SAFE_GUARD).count(), 1);
        let original = ChcParser::parse(&text.replace(SAFE_GUARD, UNSAFE_GUARD)).unwrap();
        let before = format!("{original:?}");
        let until = Instant::now() + Duration::from_secs(30);
        let _solve = crate::smt::ScopedSolveDeadline::new(Some(until));
        let _smt = crate::smt::ScopedSmtDeadline::install_until(until);
        let mut config = configured();
        config.verbose = true;
        let result = run(&original, &config, Some(until)).unwrap_or_else(|| {
            panic!("{fixture}: bounded original reachability must recover the shallow error")
        });
        let confirmed = result
            .unsafe_counterexample()
            .expect("only an actually confirmed original witness is accepted")
            .counterexample();
        assert!(
            confirmed
                .witness
                .as_ref()
                .is_some_and(|w| !w.entries.is_empty())
                || confirmed
                    .ground_derivation
                    .as_ref()
                    .is_some_and(|d| !d.is_empty()),
            "the final validator may restate a witness as its checked ground derivation"
        );
        assert!(Instant::now() < until, "original deadline expired");
        assert!(
            matches!(confirmed.ground_checks_unsafe(&original), Ok(true)),
            "returned witness must independently ground-confirm on original clauses"
        );
        assert!(
            Instant::now() < until,
            "ground confirmation exceeded deadline"
        );
        assert_eq!(format!("{original:?}"), before);

        // Same predicate/clause IDs are not authority for the changed source.
        // Disable fresh replay here: this asks about this witness, not whether
        // an unrelated new search can discover another counterexample.
        let safe = ChcParser::parse(text).unwrap();
        assert_eq!(safe.predicates().len(), original.predicates().len());
        for (a, b) in safe.predicates().iter().zip(original.predicates()) {
            assert_eq!((a.id, &a.name, &a.arg_sorts), (b.id, &b.name, &b.arg_sorts));
        }
        assert_eq!(safe.clauses().len(), original.clauses().len());
        assert!(Instant::now() < until, "safe twin exceeded deadline");
        assert!(
            !matches!(confirmed.ground_checks_unsafe(&safe), Ok(true)),
            "same IDs cannot ground-confirm this witness on the changed safe query"
        );
        assert!(
            Instant::now() < until,
            "negative ground check exceeded deadline"
        );
        let mut check = configured();
        check.disable_cex_replay = true;
        let mut verifier = crate::PdrSolver::new(safe, check);
        assert!(
            verifier.confirm_counterexample(confirmed.clone()).is_err(),
            "witness must bind to the original guard"
        );
        assert!(
            Instant::now() < until,
            "negative confirmation exceeded deadline"
        );
        drop(verifier);
        drop(result);
        drop(original);
        drop(config);
        drop(_smt);
        drop(_solve);
        assert!(Instant::now() < until, "cleanup exceeded original deadline");
    }
}

#[test]
fn both_safe_sources_refuse_original_unsafe_recovery() {
    for text in [SCALAR, ARRAY] {
        let original = ChcParser::parse(text).unwrap();
        let before = format!("{original:?}");
        assert!(run(&original, &configured(), Some(deadline())).is_none());
        assert_eq!(format!("{original:?}"), before);
    }
}

#[test]
fn forged_empty_trace_is_rejected_by_original_validator_without_recovery() {
    let original = source();
    let until = deadline();
    let _solve = crate::smt::ScopedSolveDeadline::new(Some(until));
    let _smt = crate::smt::ScopedSmtDeadline::install_until(until);
    let mut config = configured();
    config.disable_cex_replay = true;
    let mut verifier = crate::PdrSolver::new(original, config);
    assert!(verifier.confirm_counterexample(candidate()).is_err());
}
