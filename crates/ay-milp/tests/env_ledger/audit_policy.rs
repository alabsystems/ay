// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// A WARNING IS NOT A GUARD.
///
/// `env_audit` has always found the `AY_MILP_NO_CUTZ` case; it printed a WARNING
/// line and ran anyway, inside a harness that emits hundreds of lines per instance
/// and is read by a script. The campaign then recorded a result for a configuration
/// that never existed. `is_fatal` is that report becoming a refusal.
///
/// A dead name is fatal for the same reason as an unknown one. `AY_MILP_COND_TIGHTEN`
/// is the worked example: `presolve.rs` documents it as *"kept as the explicit-on A/B
/// arm"*, no code reads it, so setting it measured the DEFAULT arm.
#[test]
fn an_unknown_or_dead_name_is_fatal() {
    // `is_fatal` READS the process environment (`ALLOW_UNKNOWN_ENV` is its
    // documented escape hatch), so this test is an env READER and has to take
    // the same lock the writers take — tests in one test binary are parallel
    // THREADS sharing one process environment. Locking only the writer is not
    // enough: while `the_override_lets_a_deliberate_run_proceed` holds
    // ALLOW_UNKNOWN_ENV set, the `typo.is_fatal()` assertion below is genuinely
    // false, so an unlocked reader fails intermittently. The race is in the
    // test, not in the guard.
    let _env_lock = ay_test_support::env::lock_env();
    let mut audit = ay_milp::EnvAudit::default();
    assert!(!audit.is_fatal(), "a clean environment must not be fatal");

    audit
        .deprecated
        .push(("AY_MILP_NO_CUTZ".into(), "--emit-witness")); // synthetic fixture name
    assert!(
        !audit.is_fatal(),
        "a deprecated name still works and must stay a note, not a refusal"
    );

    audit.known.push(("AY_MILP_TRACE".into(), "1".into()));
    assert!(
        !audit.is_fatal(),
        "a name the engine reads is not a problem"
    );

    let mut typo = ay_milp::EnvAudit::default();
    typo.unknown.push("AY_MILP_NO_CUTZ".into());
    assert!(typo.is_fatal(), "a typo must stop the run, not warn");

    let mut stale = ay_milp::EnvAudit::default();
    stale.dead.push("AY_MILP_COND_TIGHTEN".into());
    assert!(
        stale.is_fatal(),
        "a dead name is a recipe that outlived its knob; the run would not be the \
         configuration the operator asked for"
    );
}

/// The escape hatch works, and it is part of the change rather than a concession:
/// a check with no way through is a check people delete.
#[test]
fn the_override_lets_a_deliberate_run_proceed() {
    let _env_lock = ay_test_support::env::lock_env();
    let _guard = ay_test_support::env::ScopedEnvVar::set(ay_milp::ALLOW_UNKNOWN_ENV, "1");
    let mut audit = ay_milp::EnvAudit::default();
    audit.unknown.push("AY_SOMETHING_ELSE".into());
    audit.dead.push("AY_MILP_COND_TIGHTEN".into());
    assert!(
        !audit.is_fatal(),
        "{} must let a deliberate run proceed",
        ay_milp::ALLOW_UNKNOWN_ENV
    );
}
