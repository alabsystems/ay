// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered Cargo steps for the local solver gate.

use super::ExternalStep;

pub(super) fn solver_gate_cargo_steps() -> Vec<ExternalStep> {
    let mut steps = Vec::with_capacity(19);
    steps.extend(quality_and_ay_debug_steps());
    steps.extend(solver_debug_canary_steps());
    steps.extend(debug_theory_packet_steps());
    steps.extend(release_library_steps());
    steps.extend(release_lra_cli_steps());
    steps.extend(release_bv_differential_steps());
    steps
}

fn quality_and_ay_debug_steps() -> [ExternalStep; 4] {
    [
        ExternalStep::new(
            "code_quality",
            "cargo",
            &[
                "run",
                "--locked",
                "-p",
                "ay-quality-gate",
                "--bin",
                "ay-quality-gate",
                "--",
            ],
        ),
        ExternalStep::new(
            "debug_ay_build_version_stamp",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--test",
                "group_misc",
                "build_version_stamp_8870",
                "--",
                "--nocapture",
            ],
        ),
        ExternalStep::new(
            "debug_ay_cli_external_codegen_consumer_canaries",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--test",
                "group_cli",
                "external_codegen_consumer_canaries_8870",
                "--",
                "--nocapture",
            ],
        ),
        ExternalStep::new(
            "debug_ay_smtlib_conformance_summary",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--test",
                "group_smt",
                "smt_lib_conformance::test_conformance_cross_logic_summary",
                "--",
                "--exact",
                "--nocapture",
            ],
        ),
    ]
}

fn solver_debug_canary_steps() -> [ExternalStep; 3] {
    [
        ExternalStep::new(
            "debug_ay_dpll_external_codegen_consumer_differential",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay-dpll",
                "--test",
                "group_differential",
                "external_codegen_consumer_differential_8870",
                "--",
                "--nocapture",
            ],
        ),
        ExternalStep::new(
            "debug_ay_dpll_external_codegen_fp_canary",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay-dpll",
                "--test",
                "group_fp",
                "external_codegen_fp16_commutativity_8870",
                "--",
                "--nocapture",
            ],
        ),
        ExternalStep::new(
            "debug_ay_sat_integration_basic",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay-sat",
                "--test",
                "integration",
                "basic::",
                "--",
                "--nocapture",
            ],
        ),
    ]
}

fn dpll_soundness_packet(name: &'static str, filter: &str) -> ExternalStep {
    ExternalStep::new(
        name,
        "cargo",
        &[
            "test",
            "--locked",
            "-p",
            "ay-dpll",
            "--test",
            "group_theory_misc",
            filter,
            "--",
            "--nocapture",
        ],
    )
}

fn debug_theory_packet_steps() -> [ExternalStep; 6] {
    [
        dpll_soundness_packet("debug_ay_dpll_qf_lia_packet", "smt_soundness_gate::lia::"),
        dpll_soundness_packet("debug_ay_dpll_qf_lra_packet", "smt_soundness_gate::lra::"),
        dpll_soundness_packet("debug_ay_dpll_qf_uf_packet", "smt_soundness_gate::uf::"),
        dpll_soundness_packet("debug_ay_dpll_qf_bv_packet", "smt_soundness_gate::bv::"),
        dpll_soundness_packet("debug_ay_dpll_qf_abv_packet", "smt_soundness_gate::abv::"),
        dpll_soundness_packet("debug_ay_dpll_qf_ax_packet", "smt_soundness_gate::ax::"),
    ]
}

fn release_library_steps() -> [ExternalStep; 3] {
    [
        ExternalStep::new(
            "release_ay_sat_soundness_regressions",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay-sat",
                "--release",
                "--test",
                "soundness_gate",
                "regression::",
                "--",
                "--nocapture",
            ],
        ),
        ExternalStep::new(
            "release_only_ay_dpll_lra_regressions",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay-dpll",
                "--release",
                "--test",
                "group_lra",
                "qf_lra_release_soundness_",
                "--",
                "--nocapture",
            ],
        ),
        // #4751 capability guard: the full dillig12_m benchmark must remain
        // provable-Safe. The test gives both profiles a generous 90s hang
        // budget for an unloaded solve measured at roughly 40s; the wall clock
        // is not a performance stopwatch. Keep it in a dedicated test binary
        // so concurrent heavy tests do not turn scheduler contention into a
        // false capability regression.
        ExternalStep::new(
            "release_ay_chc_dillig12_m_deadline_guard",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay-chc",
                "--release",
                "--test",
                "dillig12_m_deadline_4751",
                "--",
                "--nocapture",
            ],
        ),
    ]
}

fn release_lra_cli_steps() -> [ExternalStep; 3] {
    [
        ExternalStep::new(
            "debug_ay_lra_release_fixture_integrity",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--test",
                "group_lra",
                "qf_lra_release_fixture_integrity::qf_lra_release_fixtures_exist_and_match_pinned_bytes",
                "--",
                "--exact",
                "--nocapture",
            ],
        ),
        ExternalStep::new(
            "release_ay_lra_cli_mechanism_regressions",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--release",
                "--test",
                "group_lra",
                "qf_lra_cli_release_mechanism_",
                "--",
                "--nocapture",
            ],
        ),
        ExternalStep::new(
            "release_ay_lra_cli_hermetic_sweep",
            "cargo",
            &[
                "test",
                "--locked",
                "-p",
                "ay",
                "--features",
                "cli",
                "--release",
                "--test",
                "group_lra",
                "qf_lra_cli_release_sweep_6564::qf_lra_cli_release_soundness_selected_batch_6564",
                "--",
                "--exact",
                "--nocapture",
            ],
        )
        // The canonical solver gate is hermetic even when its parent shell is
        // running an opt-in full-corpus campaign. Full sweeps remain available
        // by invoking the test directly with `=1`.
        .with_env("AY_QF_LRA_RELEASE_FULL_SWEEP", "0"),
    ]
}

fn release_bv_differential_steps() -> [ExternalStep; 1] {
    [ExternalStep::new(
        "release_ay_dpll_qf_bv_differential_strict",
        "cargo",
        &[
            "test",
            "--locked",
            "-p",
            "ay-dpll",
            "--release",
            "--test",
            "group_differential",
            "differential_z3::differential_qf_bv_vs_z3",
            "--",
            "--exact",
            "--nocapture",
        ],
    )
    .with_env("Z3_DIFFERENTIAL_REQUIRED", "1")]
}
