// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Grouped CLI integration tests: CLI flags, stats, progress, tracing, startup.

#[path = "common/spawn.rs"]
pub mod spawn;

#[path = "group_cli/spawn_timeout_selftest.rs"]
mod spawn_timeout_selftest;

#[path = "group_cli/allsat_phase1_8777.rs"]
mod allsat_phase1_8777;

#[path = "group_cli/assert_soft_maxsmt.rs"]
mod assert_soft_maxsmt;

#[path = "group_cli/tutorial_solve.rs"]
mod tutorial_solve;

#[path = "group_cli/cli_env_migration_8506.rs"]
mod cli_env_migration_8506;

#[path = "group_cli/cli_debug_chc_channels_8832.rs"]
mod cli_debug_chc_channels_8832;

#[path = "group_cli/chc_bool_state_fail_closed.rs"]
mod chc_bool_state_fail_closed;

// `ay bench chc-gate` only does real work when the `bench` feature is built
// into the `ay` binary (otherwise `ay bench` bails with "built without
// benchmark support"). The `CARGO_BIN_EXE_ay` this test runs is built with the
// same feature set as the test binary, so gate the module on `bench` to keep it
// a clean skip under `--features cli` and a real run under `--features bench`.
#[cfg(all(unix, feature = "bench"))]
#[path = "group_cli/chc_gate.rs"]
mod chc_gate;

#[path = "group_cli/cli_env_migration_8726.rs"]
mod cli_env_migration_8726;

#[path = "group_cli/bv_cnf_dump_faithfulness.rs"]
mod bv_cnf_dump_faithfulness;

#[path = "group_cli/self_check_bv_drat.rs"]
mod self_check_bv_drat;

#[path = "group_cli/cli_error_fatal.rs"]
mod cli_error_fatal;

#[path = "group_cli/cli_observability_flags.rs"]
mod cli_observability_flags;

#[path = "group_cli/cli_orphan_flags_8833.rs"]
mod cli_orphan_flags_8833;

#[path = "group_cli/cli_proof_formats_5881.rs"]
mod cli_proof_formats_5881;

#[path = "group_cli/competition_jit_cli.rs"]
mod competition_jit_cli;

#[path = "group_cli/cube_and_conquer_8244.rs"]
mod cube_and_conquer_8244;

#[path = "group_cli/diagnose_wrong_answer.rs"]
mod diagnose_wrong_answer;

#[path = "group_cli/explain_phase1_8693.rs"]
mod explain_phase1_8693;

#[path = "group_cli/explain_qf_lia_8693.rs"]
mod explain_qf_lia_8693;

#[path = "group_cli/fp_check_sat_assuming_9842.rs"]
mod fp_check_sat_assuming_9842;

#[path = "group_cli/fp_reason_unknown_9842.rs"]
mod fp_reason_unknown_9842;

#[path = "group_cli/model_count_mc2026.rs"]
mod model_count_mc2026;

#[path = "group_cli/fp_signed_zero_regressions.rs"]
mod fp_signed_zero_regressions;

#[path = "group_cli/gate_cli.rs"]
mod gate_cli;

#[path = "group_cli/firewall_route_rejection.rs"]
mod firewall_route_rejection;

#[path = "group_cli/fail_closed_result_authority.rs"]
mod fail_closed_result_authority;

#[path = "group_cli/lean_verify_8773.rs"]
mod lean_verify_8773;

#[cfg(unix)]
#[path = "group_cli/launch_packet_cli.rs"]
mod launch_packet_cli;

#[path = "group_cli/rust_horn_bmc_canaries_9618.rs"]
mod rust_horn_bmc_canaries_9618;

#[path = "group_cli/lp_solve_8701.rs"]
mod lp_solve_8701;

#[path = "group_cli/lra_opt_certificates.rs"]
mod lra_opt_certificates;

#[path = "group_cli/opt_epsilon.rs"]
mod opt_epsilon;

#[path = "group_cli/opt_epsilon_differential.rs"]
mod opt_epsilon_differential;

#[path = "group_cli/pb26_sigterm.rs"]
mod pb26_sigterm;

#[path = "group_cli/pb26_cli_output.rs"]
mod pb26_cli_output;

#[path = "group_cli/progress_json_e2e_8155.rs"]
mod progress_json_e2e_8155;

#[path = "group_cli/proof_artifact_v1_8885.rs"]
mod proof_artifact_v1_8885;

#[path = "group_cli/proof_write_readonly_dir.rs"]
mod proof_write_readonly_dir;

#[path = "group_cli/startup_timing.rs"]
mod startup_timing;

#[path = "group_cli/submission_generate.rs"]
mod submission_generate;

#[path = "group_cli/stats_flag_output.rs"]
mod stats_flag_output;

#[path = "group_cli/stats_schema_contract.rs"]
mod stats_schema_contract;

#[path = "group_cli/sigterm_unknown_8674.rs"]
mod sigterm_unknown_8674;

#[path = "group_cli/solution_visualization_8702.rs"]
mod solution_visualization_8702;

#[path = "group_cli/sat_primary_path_8884.rs"]
mod sat_primary_path_8884;

#[path = "group_cli/quiet_and_dash_stdin.rs"]
mod quiet_and_dash_stdin;

#[path = "group_cli/sat_comp_repair_cli_9424.rs"]
mod sat_comp_repair_cli_9424;

#[cfg(unix)]
#[path = "group_cli/satcomp_matrix_cli.rs"]
mod satcomp_matrix_cli;

#[path = "group_cli/simplify_phase1_8696.rs"]
mod simplify_phase1_8696;

#[path = "group_cli/trace_jsonl_output.rs"]
mod trace_jsonl_output;

#[path = "group_cli/verify_proof_8771.rs"]
mod verify_proof_8771;

#[path = "group_cli/verify_proof_smt_finding_a.rs"]
mod verify_proof_smt_finding_a;

#[path = "group_cli/replay_php32_8796.rs"]
mod replay_php32_8796;

#[path = "group_cli/release_cli.rs"]
mod release_cli;

#[path = "group_cli/wrapper_crash_unknown_chc25.rs"]
mod wrapper_crash_unknown_chc25;

#[path = "group_cli/z3_compat_args.rs"]
mod z3_compat_args;

#[path = "group_cli/z3_audit_public_snapshot.rs"]
mod z3_audit_public_snapshot;
