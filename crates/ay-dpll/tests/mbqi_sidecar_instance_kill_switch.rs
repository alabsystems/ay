// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the generic-MBQI refinement instance authority
//! (#mbqi-sidecar-instance).
//!
//! The producer under test: `try_mbqi_refinement` pushes each falsifying
//! instance as its EXACT structural substitution and publishes the
//! `mbqi_refinement_instance_records` provenance BEFORE the ground re-solve,
//! so both authority consumers can see it — the consequence-replay plan
//! (`try_translate_authored_consequence_replay_unsat_with`) and the checked
//! SAT-refutation sidecar's sealed `forall_inst` derivations (the P3b
//! `bv_mbqi_false_instance_records` pattern; consumed via
//! `sealed_fragment_derivation_maps` and the c7 chain's instance roots).
//!
//! `--no-consequence-replay` disables the recording at the push site AND the
//! replay consumer, so the OFF half must restore the baseline `unknown`s
//! byte-for-byte. `--no-quant-unit-authority` starves the SIDECAR half only
//! (the replay is its own channel and still certifies this carrier); its
//! coverage is pinned by the sealed-map unit tests
//! (`derivation_evidence::tests::mbqi_refinement_record_is_starved_by_the_kill_switch`).
//!
//! This file deliberately holds ONE switch test in its own binary: it
//! installs a thread-local `MiscCliFlags` override, which must never race a
//! sibling test that could run interleaved on the same thread.

#![allow(clippy::panic)]

mod common;

/// A restore-path MBQI refinement: E-matching only adds the `n = 0` instance
/// (the trigger names `probe`), restored model validation finds the
/// falsifying `n = 5` instance, and the refinement re-solve proves UNSAT.
/// Publishing that verdict requires translated authority for the PUSHED
/// instance — exactly what the push-site provenance provides. With
/// `--no-consequence-replay` nothing is recorded and the mandatory gate must
/// restore the baseline `unknown`s; the genuinely satisfiable control must
/// stay non-unsat in every mode.
#[test]
fn mbqi_refinement_instance_authority_is_covered_by_the_replay_switch() {
    let refute_smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun probe (Int) Bool)
        (assert (probe 0))
        (assert (forall ((n Int)) (! (>= (f n) n) :pattern ((probe n)))))
        (assert (= (f 5) 0))
        (check-sat)
        (check-sat)
    "#;
    // Genuinely SAT: `f(5) = 7` is consistent with `f(n) >= n`, so a
    // certified `unsat` here would be a false Verified.
    let control_smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun probe (Int) Bool)
        (assert (probe 0))
        (assert (forall ((n Int)) (! (>= (f n) n) :pattern ((probe n)))))
        (assert (= (f 5) 7))
        (check-sat)
    "#;

    let off_replay = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_consequence_replay: true,
        ..Default::default()
    });
    let off_replay_results = common::solve_vec(refute_smt);
    let off_replay_control = common::solve_vec(control_smt);
    drop(off_replay);
    assert!(
        !off_replay_results.iter().any(|r| r == "unsat"),
        "with --no-consequence-replay no instance provenance is recorded at \
         the push site, so neither the replay nor the sidecar has anything \
         to seal and the mandatory gate must restore the baseline downgrade; \
         got {off_replay_results:?}"
    );
    assert!(
        !off_replay_control.iter().any(|r| r == "unsat"),
        "the genuinely satisfiable control must never decide unsat \
         (--no-consequence-replay); got {off_replay_control:?}"
    );

    let on_results = common::solve_vec(refute_smt);
    let on_control = common::solve_vec(control_smt);
    assert!(
        on_results.iter().all(|r| r == "unsat"),
        "with the switches on (default) the pushed n=5 instance carries \
         recorded exact provenance and the internal refutation must publish \
         unsat; got {on_results:?}"
    );
    assert!(
        !on_control.iter().any(|r| r == "unsat"),
        "the genuinely satisfiable control must never decide unsat \
         (default); got {on_control:?}"
    );
}
