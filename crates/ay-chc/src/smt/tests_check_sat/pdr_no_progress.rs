// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included at the original tests_check_sat module location.

/// End-to-end replay of the model-checker-consumer `looping_id` loop CHC (u64 guarded
/// counter loop, lowered by model-checker-consumer's typed CHC route). Pre-fix, a short
/// PDR run on this problem demoted THOUSANDS of SAT models to Unknown via
/// the strict re-verification fail-safe ("SAT model from DPLL(T) loop
/// violates original expression") because persistent-BV-cache reuse split
/// state variables into disconnected bit sets (see
/// `test_bv_cache_reuse_keeps_circuit_and_subterm_bits` for the mechanism).
/// A healthy solver assembles ZERO invalid models: every model the
/// DPLL(T)+bit-blast lane produces must satisfy the original expression.
#[test]
#[serial]
fn test_model_checker_consumer_looping_id_pdr_produces_no_invalid_sat_models() {
    use super::check_sat::invalid_sat_model_demotion_count_for_tests;

    reset_reuse_counters_for_tests();

    let input = include_str!("../../../examples/model_checker_consumer_looping_id_bv64.smt2");
    let problem = crate::ChcParser::parse(input).expect("fixture must parse");
    let config = crate::PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(3)),
        ..crate::PdrConfig::production(false)
    };
    // The verdict itself may be Unknown within this budget — what must NOT
    // happen is the solver assembling models that violate its own input.
    let _ = crate::engines::solve_pdr_proof(problem, config);

    assert_eq!(
        invalid_sat_model_demotion_count_for_tests(),
        0,
        "PDR on the looping_id CHC must not assemble SAT models that fail \
         strict re-verification (invalid-model demotions indicate the \
         persistent-BV-cache reuse split circuits again)"
    );
}

// ---------------------------------------------------------------------------
// No-progress circuit breaker (ny-cert JSON-serialization grind). The DPLL(T)
// loop's fail-closed "SAT model missing an assignment for a free variable in an
// evaluable theory position" Unknown was correct, but an outer CHC/PDR engine
// re-issued the identical query hundreds of times (each a full DPLL(T) solve),
// grinding past the wall-clock watchdog to a SIGKILL. These tests assert the
// breaker terminates that spin in a BOUNDED number of no-progress events and
// then short-circuits check_sat to Unknown — never converting an incomplete
// model into a proof.

use super::check_sat::unassignable_free_var_set_signature_for_tests;
use super::context::{
    no_progress_breaker_tripped, note_bv_cache_thrash_clear, note_solve_progress,
    note_unassignable_free_var_no_progress, ScopedNoProgressBreaker,
    NO_PROGRESS_BV_CACHE_CLEAR_LIMIT, NO_PROGRESS_SAME_SIG_LIMIT, NO_PROGRESS_TOTAL_LIMIT,
};

#[test]
#[serial]
fn test_no_progress_breaker_trips_on_repeated_identical_signature() {
    // Isolate + auto-restore the thread-local breaker for this test.
    let _guard = ScopedNoProgressBreaker::new();
    assert!(
        !no_progress_breaker_tripped(),
        "breaker must start un-tripped under a fresh scope"
    );

    // Re-issuing the SAME unassignable-free-variable set (identical query) must
    // trip the breaker within NO_PROGRESS_SAME_SIG_LIMIT records — BOUNDED, not
    // unbounded spinning. Exactly one record returns the trip edge.
    let sig = 0xdead_beef_u64;
    let mut trip_edges = 0usize;
    let mut records_until_trip = None;
    for i in 1..=NO_PROGRESS_SAME_SIG_LIMIT {
        let tripped_now = note_unassignable_free_var_no_progress(sig);
        if tripped_now {
            trip_edges += 1;
            records_until_trip.get_or_insert(i);
        }
    }
    assert!(
        no_progress_breaker_tripped(),
        "breaker must be tripped after {NO_PROGRESS_SAME_SIG_LIMIT} identical-signature records"
    );
    assert_eq!(trip_edges, 1, "trip edge must be reported exactly once");
    assert_eq!(
        records_until_trip,
        Some(NO_PROGRESS_SAME_SIG_LIMIT),
        "breaker must trip precisely at the same-signature limit (bounded retry)"
    );
}

#[test]
#[serial]
fn test_no_progress_breaker_reset_by_genuine_progress() {
    let _guard = ScopedNoProgressBreaker::new();
    let sig = 42u64;

    // One short of tripping...
    for _ in 1..NO_PROGRESS_SAME_SIG_LIMIT {
        assert!(!note_unassignable_free_var_no_progress(sig));
    }
    assert!(!no_progress_breaker_tripped());

    // ...a DECIDED (Sat/Unsat) result resets the streak, so the spin counter
    // does not accumulate across genuine progress. Another near-full run must
    // still not trip.
    note_solve_progress();
    for _ in 1..NO_PROGRESS_SAME_SIG_LIMIT {
        assert!(!note_unassignable_free_var_no_progress(sig));
    }
    assert!(
        !no_progress_breaker_tripped(),
        "progress must reset the streak so healthy solves never false-trip"
    );
}

#[test]
#[serial]
fn test_no_progress_breaker_bounds_varying_signature_spin() {
    let _guard = ScopedNoProgressBreaker::new();
    // Distinct signatures every time (a varying-query no-progress spin) never
    // accumulates the same-signature streak, but the TOTAL streak still bounds
    // it: the breaker trips at NO_PROGRESS_TOTAL_LIMIT.
    for i in 1..=NO_PROGRESS_TOTAL_LIMIT {
        note_unassignable_free_var_no_progress(u64::from(i));
    }
    assert!(
        no_progress_breaker_tripped(),
        "a sustained no-progress spin with varying signatures must still be bounded"
    );
}

#[test]
#[serial]
fn test_check_sat_short_circuits_to_unknown_when_breaker_tripped() {
    let _guard = ScopedNoProgressBreaker::new();
    let mut ctx = SmtContext::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(1));

    // The query is trivially SAT before the breaker trips.
    assert!(
        matches!(ctx.check_sat(&query), SmtResult::Sat(_)),
        "sanity: x = 1 must be SAT before the breaker trips"
    );

    // Force the breaker to trip (as `sat_or_unknown` would on a real spin).
    for _ in 0..NO_PROGRESS_SAME_SIG_LIMIT {
        note_unassignable_free_var_no_progress(7u64);
    }
    assert!(no_progress_breaker_tripped());

    // Now the SAME query returns Unknown immediately (fail-closed short-circuit),
    // deterministically and WITHOUT looping — never fabricating Sat/Unsat.
    assert!(
        matches!(ctx.check_sat(&query), SmtResult::Unknown),
        "check_sat must short-circuit to Unknown once the no-progress breaker is tripped"
    );
}

#[test]
#[serial]
fn test_scoped_no_progress_breaker_restores_prior_state() {
    // A tripped breaker inside a scope must not leak out to a reused thread.
    {
        let _outer = ScopedNoProgressBreaker::new();
        {
            let _inner = ScopedNoProgressBreaker::new();
            for _ in 0..NO_PROGRESS_SAME_SIG_LIMIT {
                note_unassignable_free_var_no_progress(1u64);
            }
            assert!(no_progress_breaker_tripped(), "inner scope trips");
        }
        assert!(
            !no_progress_breaker_tripped(),
            "dropping the inner scope must restore the un-tripped outer state"
        );
    }
    assert!(
        !no_progress_breaker_tripped(),
        "dropping the outer scope must restore the un-tripped baseline"
    );
}

/// FIX 2 (signature normalization): the ny-cert grind re-issues the same
/// under-assigned model shape but the engine mints a FRESH trailing id
/// (`…_196`, `…_197`, …) each time, so without suffix-normalization every spin
/// iteration is a DIFFERENT name set and the same-signature streak never
/// accumulates. `strip_fresh_id_suffix` must make those renamings share a
/// signature so the same-signature breaker trips on the observed spin.
#[test]
#[serial]
fn test_fresh_id_renaming_shares_signature() {
    let bv = ChcSort::BitVec(32);
    // The exact reported variable, re-minted with a different trailing id.
    let sig_196 = unassignable_free_var_set_signature_for_tests(&[(
        "lincon_lean_undef_field2_f2_f1_f1_196".to_string(),
        bv.clone(),
    )]);
    let sig_197 = unassignable_free_var_set_signature_for_tests(&[(
        "lincon_lean_undef_field2_f2_f1_f1_197".to_string(),
        bv.clone(),
    )]);
    let sig_2050 = unassignable_free_var_set_signature_for_tests(&[(
        "lincon_lean_undef_field2_f2_f1_f1_2050".to_string(),
        bv.clone(),
    )]);
    assert_eq!(
        sig_196, sig_197,
        "variables differing ONLY by a fresh trailing id must share a signature"
    );
    assert_eq!(
        sig_196, sig_2050,
        "fresh-id normalization must be independent of the id's magnitude/width"
    );
}

/// The suffix normalization must NOT collapse genuinely-distinct variables:
/// only the FINAL `_<digits>` run is a fresh id, so the structural field/lane
/// indices earlier in the name are preserved. Otherwise the coarser key could
/// (in principle) merge unrelated unassignable sets.
#[test]
#[serial]
fn test_structural_indices_keep_distinct_signatures() {
    let bv = ChcSort::BitVec(32);
    // Same fresh id (`_7`) but DIFFERENT structural field index (`f1` vs `f2`).
    let sig_f1 = unassignable_free_var_set_signature_for_tests(&[(
        "obj_undef_field2_f1_7".to_string(),
        bv.clone(),
    )]);
    let sig_f2 = unassignable_free_var_set_signature_for_tests(&[(
        "obj_undef_field2_f2_7".to_string(),
        bv.clone(),
    )]);
    assert_ne!(
        sig_f1, sig_f2,
        "distinct structural field indices must NOT collapse to the same signature"
    );
    // A name with no trailing `_<digits>` is untouched and distinct from one
    // whose trailing id was stripped down to a different stem.
    let sig_plain =
        unassignable_free_var_set_signature_for_tests(&[("plain_var".to_string(), bv.clone())]);
    let sig_other = unassignable_free_var_set_signature_for_tests(&[("other_var".to_string(), bv)]);
    assert_ne!(sig_plain, sig_other, "unrelated names must not collide");
}

/// FIX 2 end-to-end: a spin that re-issues the SAME structural unassignable
/// variable under a fresh trailing id every iteration must trip the breaker
/// within `NO_PROGRESS_SAME_SIG_LIMIT` records (as it now shares a signature),
/// rather than escaping the same-signature bound because each id looked new.
#[test]
#[serial]
fn test_fresh_id_spin_trips_same_sig_breaker() {
    let _guard = ScopedNoProgressBreaker::new();
    let bv = ChcSort::BitVec(32);
    for i in 0..NO_PROGRESS_SAME_SIG_LIMIT {
        // Fresh trailing id each iteration — the ny-cert renaming pattern.
        let name = format!("lincon_lean_undef_field2_f2_f1_f1_{}", 196 + i);
        let sig = unassignable_free_var_set_signature_for_tests(&[(name, bv.clone())]);
        note_unassignable_free_var_no_progress(sig);
    }
    assert!(
        no_progress_breaker_tripped(),
        "a fresh-id renaming spin must trip the same-signature breaker within \
         NO_PROGRESS_SAME_SIG_LIMIT records once suffixes are normalized"
    );
}

/// FIX 2 (bv-cache thrash bail): repeated full `PersistentBvCache` cap-clears
/// with no reuse — the strongest ny-cert pathology signal (observed ~470×) —
/// must trip the no-progress breaker within `NO_PROGRESS_BV_CACHE_CLEAR_LIMIT`
/// clears so the solve bails to Unknown instead of re-bitblasting to the SIGKILL.
#[test]
#[serial]
fn test_bv_cache_thrash_trips_breaker() {
    let _guard = ScopedNoProgressBreaker::new();
    assert!(
        !no_progress_breaker_tripped(),
        "fresh scope starts un-tripped"
    );

    let mut trip_edges = 0usize;
    let mut clears_until_trip = None;
    for i in 1..=NO_PROGRESS_BV_CACHE_CLEAR_LIMIT {
        if note_bv_cache_thrash_clear() {
            trip_edges += 1;
            clears_until_trip.get_or_insert(i);
        }
    }
    assert!(
        no_progress_breaker_tripped(),
        "repeated bv-cache cap-clears must trip the breaker within \
         NO_PROGRESS_BV_CACHE_CLEAR_LIMIT clears"
    );
    assert_eq!(trip_edges, 1, "the trip edge must be reported exactly once");
    assert_eq!(
        clears_until_trip,
        Some(NO_PROGRESS_BV_CACHE_CLEAR_LIMIT),
        "the breaker must trip precisely at the cap-clear limit"
    );
}

/// A bv-cache thrash bail must survive a DECIDED sub-query verdict: unlike the
/// missing-var streaks, `note_solve_progress` must NOT reset the clear count,
/// because a decided sub-query does not undo the fact that the solve is
/// re-blasting an oversized structure.
#[test]
#[serial]
fn test_bv_cache_thrash_not_reset_by_progress() {
    let _guard = ScopedNoProgressBreaker::new();
    for _ in 1..NO_PROGRESS_BV_CACHE_CLEAR_LIMIT {
        assert!(!note_bv_cache_thrash_clear());
    }
    // A decided sub-query in between must not rescue the thrash.
    note_solve_progress();
    assert!(
        note_bv_cache_thrash_clear(),
        "the final cap-clear must still trip despite an intervening decided verdict"
    );
    assert!(no_progress_breaker_tripped());
}
