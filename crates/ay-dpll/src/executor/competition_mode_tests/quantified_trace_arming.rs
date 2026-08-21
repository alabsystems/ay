// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `competition_mode_tests` to preserve test FQNs.

/// #proof-capability B3 unreachability invariant: with ANY proof demand in
/// scope — or without competition mode at all — the raw lane is dead code.
/// Each demand row runs TWIN executors, competition+demand vs demand-only,
/// and requires identical outputs and identical admission class: the
/// competition switch must be unobservable outside shedding. No row may
/// admit through `CompetitionRaw` and the `unsat_admission` statistic key
/// must never appear.
#[test]
fn competition_raw_is_dead_under_every_proof_demand() {
    const SCRIPT: &str = r"
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        (assert (not p))
        (check-sat)
    ";
    let demands: [(&str, fn(&mut Executor)); 5] = [
        ("no demand (certified default twin)", |_| {}),
        ("set_produce_proofs(true)", |exec| {
            exec.set_produce_proofs(true);
        }),
        ("in-script :produce-proofs true", |exec| {
            run(exec, "(set-option :produce-proofs true)");
        }),
        (":check-proofs-strict true", |exec| {
            run(exec, "(set-option :check-proofs-strict true)");
        }),
        ("set_self_check(true)", |exec| {
            exec.set_self_check(true);
        }),
    ];
    for (demand, arm) in demands {
        let mut certified = Executor::new();
        arm(&mut certified);
        let mut competition = Executor::new();
        competition.set_competition_mode(true);
        arm(&mut competition);
        if demand == "no demand (certified default twin)" {
            // The one row where shedding IS active on the competition twin:
            // it exercises the raw lane and is asserted separately by
            // `shed_mode_every_unsat_family_admits_competition_raw`. Here
            // only the certified twin's surface is pinned.
            let outputs = run(&mut certified, SCRIPT);
            assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
            assert_ne!(
                certified.last_command_unsat_admission,
                Some(CommandUnsatAdmission::CompetitionRaw),
                "{demand}: certified default must never admit raw"
            );
            assert_eq!(
                certified.statistics().get_string("unsat_admission"),
                None,
                "{demand}: certified statistics must not carry the raw marker"
            );
            continue;
        }
        assert!(
            !competition.competition_shedding_active(),
            "{demand}: the demand must deactivate shedding"
        );
        let certified_outputs = run(&mut certified, SCRIPT);
        let competition_outputs = run(&mut competition, SCRIPT);
        assert_eq!(
            certified_outputs, competition_outputs,
            "{demand}: with the demand in scope the competition switch must \
             be unobservable"
        );
        assert_eq!(
            certified.last_command_unsat_admission, competition.last_command_unsat_admission,
            "{demand}: both twins must publish through the same admission lane"
        );
        assert_ne!(
            competition.last_command_unsat_admission,
            Some(CommandUnsatAdmission::CompetitionRaw),
            "{demand}: the raw lane must be unreachable outside shedding"
        );
        for (twin, exec) in [("certified", &certified), ("competition", &competition)] {
            assert_eq!(
                exec.statistics().get_string("unsat_admission"),
                None,
                "{demand}: {twin} twin statistics must not carry the raw \
                 admission marker"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// #quantified-trace-arming
// ---------------------------------------------------------------------------
//
// Shedding has two jobs and they are separated for a QUANTIFIED public query.
// The ADMISSION job (`competition_shedding_active`, the B3 `CompetitionRaw`
// lane) is untouched. The COST job — recording the internal trace — yields,
// because on a quantified problem that trace is not an artifact but the
// publication mechanism: E-matching / CEGQI writers register their ground
// instances as `forall_inst` derivations and `disambiguate_cegqi_unsat`
// publishes `unsat` exactly when those derivations strict-check against the
// authored problem. Shed the trace and the route is dead, which is why
// `--rigor fast` measured strictly FEWER answers than `--rigor standard` on
// quantified inputs.

/// The FIRST pass of every public solve — quantified or not — still starts
/// shed. Arming happens only on the `Unknown` fallback, which is what makes
/// the campaign incapable of losing a verdict the shed path already produces.
#[test]
fn every_public_solve_still_starts_shed() {
    for script in [
        r"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (assert (forall ((x U)) (p x)))
        ",
        r"
        (set-logic QF_UF)
        (declare-const p Bool)
        (assert p)
        ",
    ] {
        let mut exec = Executor::new();
        exec.set_competition_mode(true);
        run(&mut exec, script);
        exec.begin_public_solve(false);
        assert!(
            !exec.proof_tracker.is_enabled(),
            "begin_public_solve must leave the recorder shed: {script}"
        );
        assert!(!exec.quantified_query_defeats_shedding);
        assert!(!exec.produce_proofs_enabled());
    }
}

/// END-TO-END, the measured behaviour this campaign exists for: a quantified
/// UNSAT whose refutation is instantiation-driven publishes in competition
/// mode. This is the minimal shape of `UFLRA/FFT/smtlib.627531` — a universal
/// that a single ground instance contradicts. With the trace shed and no
/// retry it answered `unknown (incomplete quantifier-cegqi)`.
///
/// This is also the MUTATION TEST for the barrier: the same query under
/// `--no-quantified-shedding-yield` must fail closed to the pre-campaign
/// `unknown`, so removing or short-circuiting the retry fails the first
/// assertion and breaking the kill switch fails the second.
#[test]
fn competition_mode_publishes_an_instantiation_driven_quantified_unsat() {
    const SCRIPT: &str = r"
        (set-logic UFLRA)
        (declare-fun f (Real) Real)
        (declare-fun a () Real)
        (assert (< 0.0 a))
        (assert (not (< 0.0 (f a))))
        (assert (forall ((x Real)) (=> (< 0.0 x) (< 0.0 (f x)))))
        (check-sat)
    ";
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = run(&mut exec, SCRIPT);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "competition mode must publish this instantiation-driven refutation, \
         got {outputs:?}"
    );

    // MONOTONICITY: the certified default answers the same. A rigor ladder
    // where the WEAKER level publishes less is the defect this closes, so pin
    // both ends rather than only the one that changed.
    let mut certified = Executor::new();
    let certified_outputs = run(&mut certified, SCRIPT);
    assert_eq!(
        certified_outputs.last().map(String::as_str),
        Some("unsat"),
        "certified default must agree, got {certified_outputs:?}"
    );

    let off = ay_core::MiscCliFlags {
        no_quantified_shedding_yield: true,
        ..ay_core::MiscCliFlags::default()
    };
    let _guard = ay_core::misc_test_override::set(off);
    let mut killed = Executor::new();
    killed.set_competition_mode(true);
    let killed_outputs = run(&mut killed, SCRIPT);
    assert_ne!(
        killed_outputs.last().map(String::as_str),
        Some("unsat"),
        "the kill switch must restore the pre-campaign fail-closed verdict, \
         got {killed_outputs:?}"
    );
}

/// The retry is confined to a SHED solve. A proof demand already keeps the
/// recorder armed for the whole solve, so the lane must not fire and pay for a
/// second pass there.
#[test]
fn trace_arming_retry_never_fires_when_the_recorder_is_already_armed() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_produce_proofs(true);
    run(
        &mut exec,
        r"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun p (U) Bool)
        (assert (forall ((x U)) (p x)))
        (check-sat)
        ",
    );
    assert!(
        !exec.competition_shedding_active(),
        "a proof demand must keep shedding off, which is the retry's own guard"
    );
    assert!(
        !exec.quantified_query_defeats_shedding,
        "the retry latch must be clear after a solve that never shed"
    );
}
