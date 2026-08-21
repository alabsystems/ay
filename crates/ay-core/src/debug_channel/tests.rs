// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use serial_test::serial;

#[test]
fn test_debug_config_empty_by_default() {
    let cfg = DebugConfig::default();
    assert!(cfg.is_empty());
    assert!(!cfg.enabled(DebugChannel::Lia));
}

#[test]
fn test_debug_config_explicit_channel() {
    let cfg = DebugConfig::from_channels(&[DebugChannel::Lia, DebugChannel::Dpll]);
    assert!(!cfg.is_empty());
    assert!(cfg.enabled(DebugChannel::Lia));
    assert!(cfg.enabled(DebugChannel::Dpll));
    assert!(!cfg.enabled(DebugChannel::Lra));
}

#[test]
fn test_debug_config_theory_umbrella_expands() {
    let cfg = DebugConfig::from_channels(&[DebugChannel::Theory]);
    assert!(cfg.enabled(DebugChannel::Theory));
    // All theory channels should be enabled
    for &ch in DebugChannel::theory_channels() {
        assert!(cfg.enabled(ch), "Theory umbrella should enable {ch:?}");
    }
    // Non-theory channels should NOT be enabled
    assert!(!cfg.enabled(DebugChannel::Dpll));
    assert!(!cfg.enabled(DebugChannel::SatCongruence));
    assert!(!cfg.enabled(DebugChannel::Prop));
}

#[test]
fn test_debug_config_theory_umbrella_plus_extra() {
    let cfg = DebugConfig::from_channels(&[DebugChannel::Theory, DebugChannel::Dpll]);
    assert!(cfg.enabled(DebugChannel::Lia));
    assert!(cfg.enabled(DebugChannel::Dpll));
}

#[test]
fn test_proof_format_variants() {
    // Ensure all variants are distinct
    let formats = [
        ProofFormat::Drat,
        ProofFormat::Lrat,
        ProofFormat::Lean4,
        ProofFormat::Alethe,
    ];
    for (i, a) in formats.iter().enumerate() {
        for (j, b) in formats.iter().enumerate() {
            if i == j {
                assert_eq!(a, b);
            } else {
                assert_ne!(a, b);
            }
        }
    }
}

#[test]
fn test_sat_disable_flags_default_all_false() {
    let flags = SatDisableFlags::default();
    assert!(!flags.no_bve);
    assert!(!flags.no_probe);
    assert!(!flags.no_congruence);
    assert!(!flags.no_decompose);
    assert!(!flags.no_sweep);
    assert!(!flags.no_subsume);
    assert!(!flags.no_vivify);
    assert!(!flags.no_factor);
    assert!(!flags.no_bce);
    assert!(!flags.no_transred);
    assert!(!flags.no_preprocess);
    assert!(!flags.no_inprocess);
    assert!(!flags.no_cold_restart);
    assert!(!flags.no_external_codegen_backend);
}

#[test]
fn test_sat_debug_env_flags_default_all_off() {
    let flags = SatDebugEnvFlags::default();
    assert!(!flags.trace_ext_conflict);
    assert!(flags.bve_limit.is_none());
    assert!(!flags.bve_trace);
    assert!(flags.bve_max_rounds.is_none());
    assert!(!flags.log_enabled);
    assert!(!flags.dump_conflicts);
    assert!(!flags.clause_provenance);
    assert!(flags.debug_transred_clause.is_none());
}

#[test]
fn test_trace_config_default_all_none() {
    let config = TraceConfig::default();
    assert!(config.diagnostic_path.is_none());
    assert!(config.decision_trace_path.is_none());
    assert!(config.replay_trace_path.is_none());
    assert!(config.trace_file_path.is_none());
    assert!(config.solution_file_path.is_none());
    assert!(config.decision_log_path.is_none());
    assert!(config.dump_bv_cnf_path.is_none());
    assert!(config.kind_dump_dir.is_none());
    assert!(config.dump_encoding_path.is_none());
}

#[test]
fn test_chc_debug_env_flags_default_all_off() {
    let flags = ChcDebugEnvFlags::default();
    assert!(!flags.iuc_trace);
    assert!(!flags.iuc_require_farkas);
}

#[test]
#[serial(trace_file_claim)]
fn test_claim_trace_file_sets_claimed() {
    // Reset state (tests share the process-global atomic)
    release_trace_file();

    // Before claiming, the atomic should be false
    assert!(
        !TRACE_FILE_CLAIMED.load(Ordering::Acquire),
        "TRACE_FILE_CLAIMED should be false before claim"
    );

    claim_trace_file();

    assert!(
        TRACE_FILE_CLAIMED.load(Ordering::Acquire),
        "TRACE_FILE_CLAIMED should be true after claim"
    );

    // Clean up for other tests
    release_trace_file();
}

#[test]
#[serial(trace_file_claim)]
fn test_release_trace_file_clears_claim() {
    claim_trace_file();
    assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

    release_trace_file();
    assert!(
        !TRACE_FILE_CLAIMED.load(Ordering::Acquire),
        "TRACE_FILE_CLAIMED should be false after release"
    );
}

#[test]
#[serial(trace_file_claim)]
fn test_claim_trace_file_idempotent() {
    release_trace_file();

    claim_trace_file();
    claim_trace_file(); // double claim should not panic or change state
    assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

    release_trace_file();
}

/// The consumer-facing half of the measurement gap: a Rust-API caller can
/// name a diagnostic channel without naming all ~120 `MiscCliFlags` fields,
/// and building the value installs nothing.
#[test]
fn misc_cli_flags_with_applies_configuration_and_installs_nothing() {
    let base = misc_cli_flags_with(|_| {});
    assert!(
        !base.probe_cert_reject && !base.phase_trace && !base.debug_cert,
        "no AY_* fallback may resurrect a retired diagnostic carrier"
    );

    let tuned = misc_cli_flags_with(|flags| {
        flags.probe_cert_reject = true;
        flags.phase_trace = true;
    });
    assert!(tuned.probe_cert_reject, "configure must be applied");
    assert!(tuned.phase_trace, "configure must be applied");
    assert!(
        !tuned.debug_cert,
        "configure must not disturb the fields it did not name"
    );

    // Purity: building a value must not initialize (or mutate) the global.
    let before = misc_cli_flags().probe_cert_reject;
    let _ = misc_cli_flags_with(|flags| flags.probe_cert_reject = true);
    assert_eq!(
        misc_cli_flags().probe_cert_reject,
        before,
        "misc_cli_flags_with must be pure"
    );
}

#[test]
#[serial(trace_file_claim)]
fn test_trace_file_available_false_when_no_env_var() {
    // In the test environment no trace file is configured,
    // so trace_file_available() should return false regardless of claim state.
    release_trace_file();
    assert!(
        !trace_file_available(),
        "trace_file_available should be false when no trace file is configured"
    );
}

#[test]
#[serial(trace_file_claim)]
fn test_claim_release_cycle() {
    // Simulate a solver reuse scenario: claim -> solve -> release -> claim again
    release_trace_file();

    claim_trace_file();
    assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

    release_trace_file();
    assert!(!TRACE_FILE_CLAIMED.load(Ordering::Acquire));

    // Second solve can claim again
    claim_trace_file();
    assert!(TRACE_FILE_CLAIMED.load(Ordering::Acquire));

    release_trace_file();
}
