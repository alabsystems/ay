// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::chc_runner::{portfolio_budget_from_timeout, portfolio_time_budget};
use crate::dimacs::{has_cnf_extension, is_dimacs_format};

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_string()).collect()
}

#[test]
fn decision_trace_preflight_retains_the_validated_input_bytes() {
    let temp = tempfile::tempdir().expect("tempdir");
    let path = temp.path().join("input.smt2");
    let validated = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    std::fs::write(&path, validated).expect("write input");

    let snapshot =
        preflight_decision_trace_file(path.to_str().expect("UTF-8 path")).expect("preflight input");
    std::fs::remove_file(&path).expect("unlink original name");
    std::fs::write(&path, "(set-logic QF_UF)\n(check-sat)\n(check-sat)\n")
        .expect("replace input name");

    assert_eq!(snapshot.content, validated);
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let opened_identity = snapshot
            .file
            .as_ref()
            .expect("snapshot descriptor")
            .metadata()
            .expect("snapshot metadata");
        let replacement_identity = std::fs::metadata(&path).expect("replacement metadata");
        assert_ne!(
            (opened_identity.dev(), opened_identity.ino()),
            (replacement_identity.dev(), replacement_identity.ino())
        );
    }
}

#[test]
fn decision_trace_preflight_rejects_parseable_dimacs() {
    let error = validate_decision_trace_content("input.cnf", "p cnf 1 1\n1 0\n")
        .expect_err("DIMACS decision traces are not end-to-end authenticated");
    assert!(
        error.contains("currently unsupported for DIMACS input"),
        "unexpected rejection: {error}"
    );
}

#[test]
fn z3_model_materialization_retains_source_bytes_without_a_temp_path() {
    let temp = tempfile::tempdir().expect("tempdir");
    let path = temp.path().join("input.smt2");
    let original = "(set-logic QF_UF)\n(assert false)\n(check-sat)\n";
    std::fs::write(&path, original).expect("write input");

    let materialized = materialize_z3_model_file_input(path.to_str().expect("UTF-8 path"))
        .expect("materialize model input");
    std::fs::remove_file(&path).expect("unlink original name");
    std::fs::write(&path, "(set-logic QF_UF)\n(check-sat)\n").expect("replace input name");

    assert_eq!(materialized.logical_path, path.to_string_lossy());
    assert!(materialized.content.starts_with(original));
    assert!(materialized.content.ends_with("(get-model)\n"));
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let opened = materialized
            .source_file
            .as_ref()
            .expect("source descriptor")
            .metadata()
            .expect("source metadata");
        let replacement = std::fs::metadata(&path).expect("replacement metadata");
        assert_ne!(
            (opened.dev(), opened.ino()),
            (replacement.dev(), replacement.ino())
        );
    }
}

#[test]
fn test_is_horn_logic() {
    // HORN logic
    let horn_content = "(set-logic HORN)
(declare-fun Inv (Int) Bool)
(check-sat)";
    assert!(is_horn_logic(horn_content));

    // Non-HORN logic
    let non_horn_content = "(set-logic QF_LIA)
(declare-const x Int)
(check-sat)";
    assert!(!is_horn_logic(non_horn_content));

    // No logic specified
    let no_logic = "(declare-const x Int)
(check-sat)";
    assert!(!is_horn_logic(no_logic));
}

#[test]
fn test_is_fixedpoint_format() {
    // Z3 fixedpoint script without (set-logic HORN): detected via rule/query.
    let fp = "(declare-rel p (Int))
(declare-var x Int)
(rule (=> (= x 0) (p x)))
(rule (=> (and (p x)) (p (+ x 1))))
(query (p 5))";
    assert!(is_fixedpoint_format(fp));
    // is_horn_logic must NOT claim this (no HORN logic line); the dedicated
    // fixedpoint detector is what routes it.
    assert!(!is_horn_logic(fp));

    // A query alone (with a relation) is enough to be a fixedpoint problem.
    let q_only = "(declare-rel goal ())
(rule goal)
(query goal)";
    assert!(is_fixedpoint_format(q_only));

    // declare-rel WITHOUT any rule/query is not a decidable fixedpoint problem.
    let rel_only = "(declare-rel p (Int))";
    assert!(!is_fixedpoint_format(rel_only));

    // A regular SMT script must NOT be misrouted, even when symbols are named
    // `rule`/`query` (they parse as declare-const/assert, not Rule/Query).
    let regular = "(set-logic QF_UF)
(declare-const rule Bool)
(declare-const query Bool)
(assert (and rule query))
(check-sat)";
    assert!(!is_fixedpoint_format(regular));

    // Plain arithmetic SMT is not a fixedpoint script.
    let arith = "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 5))
(check-sat)";
    assert!(!is_fixedpoint_format(arith));
}

#[test]
fn test_is_dimacs_format() {
    // Valid DIMACS
    let dimacs = "p cnf 3 2
1 -2 0
-1 2 0";
    assert!(is_dimacs_format(dimacs));

    // DIMACS with comments
    let dimacs_comments = "c A comment
c Another comment
p cnf 3 2
1 -2 0
-1 2 0";
    assert!(is_dimacs_format(dimacs_comments));

    // SMT-LIB is not DIMACS
    let smtlib = "(set-logic QF_LIA)
(declare-const x Int)
(check-sat)";
    assert!(!is_dimacs_format(smtlib));

    // Empty is not DIMACS
    assert!(!is_dimacs_format(""));

    // Comments only is not DIMACS
    assert!(!is_dimacs_format("c comment"));
}

#[test]
fn test_has_cnf_extension() {
    assert!(has_cnf_extension("test.cnf"));
    assert!(has_cnf_extension("test.CNF"));
    assert!(has_cnf_extension("/path/to/file.cnf"));
    assert!(!has_cnf_extension("test.smt2"));
    assert!(!has_cnf_extension("test.cnf.bak"));
}

#[test]
fn test_portfolio_time_budget_accounts_for_elapsed() {
    // 1000ms timeout, 200ms already elapsed => 800ms remaining => 760ms budget (95%)
    assert_eq!(
        portfolio_time_budget(1000, Duration::from_millis(200)),
        Duration::from_millis(760)
    );
}

#[test]
fn test_chc_stats_json_exports_deterministic_bv_bool_route_counters() {
    let mut run_stats =
        stats_output::RunStatistics::new(stats_output::SolveMode::Chc, "unsat", Duration::ZERO);
    let mut chc_stats = ay::chc::ChcStatistics::default();
    chc_stats.deterministic_bv_bool_transition_attempts = 1;
    chc_stats.deterministic_bv_bool_transition_recognized = 1;
    chc_stats.deterministic_bv_bool_transition_bmc_unsafe_validated = 1;
    chc_stats.deterministic_bv_bool_transition_kind_safe_validated = 2;
    chc_stats.deterministic_bv_bool_transition_kind_unsafe_validated = 3;
    chc_stats.deterministic_bv_bool_transition_bool_control_safe_validated = 4;
    chc_stats.deterministic_bv_bool_transition_validation_rejections = 5;

    insert_deterministic_bv_bool_transition_stats(&mut run_stats, &chc_stats);
    let json = chc_run_stats_json(&run_stats, "adaptive", Some(&chc_stats), None, None);
    let value: serde_json::Value = serde_json::from_str(&json).expect("valid stats json");

    assert_eq!(value["chc.deterministic_bv_bool_transition.attempts"], 1);
    assert_eq!(value["chc.deterministic_bv_bool_transition.recognized"], 1);
    assert_eq!(
        value["chc.deterministic_bv_bool_transition.bmc_unsafe_validated"],
        1
    );
    assert_eq!(
        value["chc.deterministic_bv_bool_transition.kind_safe_validated"],
        2
    );
    assert_eq!(
        value["chc.deterministic_bv_bool_transition.kind_unsafe_validated"],
        3
    );
    assert_eq!(
        value["chc.deterministic_bv_bool_transition.bool_control_safe_validated"],
        4
    );
    assert_eq!(
        value["chc.deterministic_bv_bool_transition.validation_rejections"],
        5
    );
}

#[test]
fn test_portfolio_time_budget_zero_when_no_time_left() {
    // No time remaining
    assert_eq!(
        portfolio_time_budget(1000, Duration::from_secs(1)),
        Duration::from_millis(0)
    );
    // More elapsed than timeout (saturating_sub protects us)
    assert_eq!(
        portfolio_time_budget(1000, Duration::from_secs(5)),
        Duration::from_millis(0)
    );
}

#[test]
fn test_portfolio_time_budget_no_overflow() {
    // Large timeout shouldn't overflow
    let budget = portfolio_time_budget(u64::MAX, Duration::ZERO);
    let expected_ms = u64::try_from((u128::from(u64::MAX) * 19) / 20).unwrap();
    assert_eq!(budget, Duration::from_millis(expected_ms));
}

#[test]
fn test_portfolio_budget_from_timeout_default() {
    // No CLI timeout → unlimited (Duration::ZERO sentinel)
    assert_eq!(portfolio_budget_from_timeout(None), Duration::ZERO);
}

#[test]
fn test_portfolio_budget_from_timeout_zero_override() {
    assert_eq!(portfolio_budget_from_timeout(Some(0)), Duration::ZERO);
}

#[test]
fn test_satcomp_timeout_policy_uses_unknown_success_exit() {
    assert_eq!(timeout_exit_code_for_sat_competition_wrapper(false), 124);
    assert_eq!(timeout_exit_code_for_sat_competition_wrapper(true), 0);
    assert_eq!(
        timeout_stdout_line_for_sat_competition_wrapper(false),
        b"unknown\n"
    );
    assert_eq!(
        timeout_stdout_line_for_sat_competition_wrapper(true),
        b"s UNKNOWN\n"
    );
    assert_eq!(
        timeout_stderr_line_for_sat_competition_wrapper(false),
        b"(:reason-unknown \"timeout\")\n"
    );
    assert_eq!(
        timeout_stderr_line_for_sat_competition_wrapper(true),
        b"c timeout\n"
    );
}

#[test]
fn test_satcomp_timeout_policy_requires_known_wrapper_token() {
    assert!(
        !is_sat_competition_wrapper_token("1"),
        "arbitrary non-empty wrapper env must not change timeout grammar"
    );
    assert!(!is_sat_competition_wrapper_token("not-a-real-wrapper"));
    assert!(is_sat_competition_wrapper_token(
        "main-regular-default-lrat-v1"
    ));
    assert!(is_sat_competition_wrapper_token(
        "satcomp-variant-default-lrat-v1"
    ));
}

#[test]
fn test_preprocess_preserves_key_value_after_bench_subcommand() {
    let raw = strings(&[
        "ay",
        "bench",
        "sat-delta",
        "--reference-solver",
        "kissat=reference/kissat/build/kissat",
    ]);

    let processed = preprocess_args(raw.clone());

    assert_eq!(processed, raw);
    assert!(!processed.iter().any(|arg| arg == "--unsupported-z3-param"));
}

#[test]
fn test_preprocess_argv0_z3_enables_z3_mode_for_implicit_solve() {
    let processed = preprocess_args(strings(&["/tmp/z3", "input.smt2"]));

    assert_eq!(
        processed,
        strings(&["/tmp/z3", "solve", "--z3-mode", "input.smt2"])
    );
}

#[test]
fn test_preprocess_argv0_z3_enables_z3_mode_for_explicit_solve() {
    let processed = preprocess_args(strings(&["/tmp/z3", "solve", "input.smt2"]));

    assert_eq!(
        processed,
        strings(&["/tmp/z3", "solve", "--z3-mode", "input.smt2"])
    );
}

#[test]
fn test_preprocess_argv0_z3_does_not_duplicate_explicit_z3_mode() {
    let processed = preprocess_args(strings(&["/tmp/z3", "solve", "--z3-mode", "input.smt2"]));

    assert_eq!(
        processed,
        strings(&["/tmp/z3", "solve", "--z3-mode", "input.smt2"])
    );
}

#[test]
fn test_preprocess_argv0_z3_does_not_affect_non_solve_commands() {
    for raw in [
        strings(&["ay", "input.smt2"]),
        strings(&["/tmp/z3-audit", "input.smt2"]),
        strings(&["/tmp/z3", "bench", "run", "smt-smtcomp-qf-lia"]),
        strings(&["/tmp/z3", "z3-audit"]),
    ] {
        let processed = preprocess_args(raw.clone());
        assert!(
            !processed
                .iter()
                .skip(1)
                .take_while(|arg| arg.as_str() != "--")
                .any(|arg| arg == "--z3-mode"),
            "argv0 z3 mode should not affect {raw:?}; got {processed:?}"
        );
    }
}

#[test]
fn test_preprocess_z3_in_selects_live_incremental_stdin() {
    let processed = preprocess_args(strings(&["ay", "-smt2", "-in"]));

    assert_eq!(processed, strings(&["ay", "solve", "--incremental"]));
    assert!(
        !processed.iter().any(|arg| arg == "--stdin"),
        "batch stdin waits for EOF and cannot implement Z3's live -in protocol"
    );
}

#[test]
fn test_preprocess_bare_dash_maps_to_stdin() {
    // CODE 11: a bare `-` FILE means "read from stdin" (batch), mapped to
    // `--stdin` so clap never treats `-` as a positional file (which used to
    // fail with "Error reading file '-'").
    let processed = preprocess_args(strings(&["ay", "-"]));
    assert_eq!(processed, strings(&["ay", "solve", "--stdin"]));

    // Explicit `solve -` behaves identically.
    let explicit = preprocess_args(strings(&["ay", "solve", "-"]));
    assert_eq!(explicit, strings(&["ay", "solve", "--stdin"]));
}

#[test]
fn test_preprocess_bare_dash_does_not_disturb_z3_in_or_stdin() {
    // z3's live `-in` still maps to `--incremental`, untouched by the `-` rule.
    let z3_in = preprocess_args(strings(&["ay", "-in"]));
    assert_eq!(z3_in, strings(&["ay", "solve", "--incremental"]));

    // An explicit `--stdin` passes straight through.
    let stdin = preprocess_args(strings(&["ay", "--stdin"]));
    assert_eq!(stdin, strings(&["ay", "solve", "--stdin"]));

    // A file literally named `-` after `--` is preserved verbatim (escape hatch).
    let escaped = preprocess_args(strings(&["ay", "solve", "--", "-"]));
    assert_eq!(escaped, strings(&["ay", "solve", "--", "-"]));
}

#[test]
fn test_solve_quiet_requested_detection() {
    // CODE 13: `-q`/`--quiet` on a solve invocation is detected before the
    // session supervisor forks so the pre-fork session marker is suppressed.
    assert!(solve_quiet_requested(&strings(&[
        "ay",
        "solve",
        "-q",
        "input.cnf"
    ])));
    assert!(solve_quiet_requested(&strings(&[
        "ay",
        "solve",
        "--quiet",
        "input.cnf"
    ])));
    // No flag → not requested.
    assert!(!solve_quiet_requested(&strings(&[
        "ay",
        "solve",
        "input.cnf"
    ])));
    // Only honored before `--`.
    assert!(!solve_quiet_requested(&strings(&[
        "ay", "solve", "--", "-q"
    ])));
    // Not a solve invocation → never requested.
    assert!(!solve_quiet_requested(&strings(&["ay", "bench", "-q"])));
}

#[test]
fn test_bench_run_preserves_explicit_single_run_override() {
    let cli = <Cli as Parser>::try_parse_from(strings(&[
        "ay",
        "bench",
        "run",
        "smt-smtcomp-qf-lia",
        "--runs",
        "1",
        "--reference-solver",
        "z3",
    ]))
    .expect("parse bench run command");

    match cli.command {
        Some(Command::Bench(cmd_bench::BenchCommand::Run {
            runs,
            reference_solvers,
            ..
        })) => {
            assert_eq!(runs, Some(1));
            assert_eq!(reference_solvers, vec!["z3".to_string()]);
        }
        _ => panic!("unexpected command"),
    }
}

#[test]
fn test_bench_run_omitted_runs_uses_registry_default() {
    let cli =
        <Cli as Parser>::try_parse_from(strings(&["ay", "bench", "run", "smt-smtcomp-qf-lia"]))
            .expect("parse bench run command");

    match cli.command {
        Some(Command::Bench(cmd_bench::BenchCommand::Run { runs, .. })) => {
            assert_eq!(runs, None);
        }
        _ => panic!("unexpected command"),
    }
}

#[test]
fn test_preprocess_preserves_launch_gate_subcommand() {
    let raw = strings(&[
        "ay",
        "launch-gate",
        "--launch-mode",
        "metadata-only",
        "--summary-json",
        "/tmp/ay-release-gate-summary.json",
    ]);

    let processed = preprocess_args(raw.clone());

    assert_eq!(processed, raw);
    assert!(!processed.iter().any(|arg| arg == "solve"));
}

#[test]
fn test_launch_gate_help_classifies_external_evidence() {
    let mut cmd = Cli::command();
    let help = cmd
        .find_subcommand_mut("launch-gate")
        .expect("launch-gate subcommand")
        .render_long_help()
        .to_string();

    assert!(help.contains("The native command validates launch evidence"));
    assert!(help.contains("scripts/launch_benchmark_packet.sh"));
    assert!(help.contains("ay consumer-smoke run --json"));
    assert!(help.contains("ay release generate-manifest"));
    assert!(help.contains("ay z3-audit"));
    assert!(help.contains("public_mirror blocker is publication evidence only"));
    assert!(help.contains("not classified as a solver blocker"));
}

#[test]
fn test_preprocess_preserves_z3_audit_subcommand() {
    let raw = strings(&[
        "ay",
        "z3-audit",
        "--scope",
        "cli-subset",
        "--reference-cache",
        "tests/z3-audit/reference-cache.json",
        "--summary-json",
        "/tmp/ay-z3-audit.json",
    ]);

    let processed = preprocess_args(raw.clone());

    assert_eq!(processed, raw);
    assert!(!processed.iter().any(|arg| arg == "solve"));
}

#[test]
fn test_preprocess_rejects_unknown_key_value_for_default_solve() {
    let processed = preprocess_args(strings(&["ay", "unknown_param=true", "input.smt2"]));

    assert_eq!(processed[1], "solve");
    assert!(processed.iter().any(|arg| arg == "--unsupported-z3-param"));
    assert!(processed.iter().any(|arg| arg == "unknown_param=true"));
}

#[test]
fn test_preprocess_accepts_input_path_with_equals() {
    let file = "maze-generation-width=15-height=15-density=0.01-run=1.smt2";
    let processed = preprocess_args(strings(&["ay", file]));

    assert_eq!(processed, strings(&["ay", "solve", file]));
    assert!(!processed.iter().any(|arg| arg == "--unsupported-z3-param"));
}

#[test]
fn test_preprocess_double_dash_preserves_key_value_input_path() {
    let file = "maze-generation-width=15-height=15-density=0.01-run=1.smt2";
    let processed = preprocess_args(strings(&["ay", "--", file]));

    assert_eq!(processed, strings(&["ay", "solve", "--", file]));
    assert!(!processed.iter().any(|arg| arg == "--unsupported-z3-param"));
}

#[test]
fn test_determine_execution_mode_chc_aliases_portfolio_file() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(false, Some(&file), ChcMode::Chc);
    assert_eq!(mode, ExecutionMode::PortfolioFile);
}

#[test]
fn test_determine_execution_mode_portfolio_file() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(false, Some(&file), ChcMode::Portfolio);
    assert_eq!(mode, ExecutionMode::PortfolioFile);
}

#[test]
fn test_determine_execution_mode_auto_file() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(false, Some(&file), ChcMode::None);
    assert_eq!(mode, ExecutionMode::AutoFile);
}

#[test]
fn test_determine_execution_mode_interactive_without_file() {
    let mode = determine_execution_mode(false, None, ChcMode::Portfolio);
    assert_eq!(mode, ExecutionMode::Interactive);
}

#[test]
fn test_determine_execution_mode_stdin_takes_precedence() {
    let file = String::from("input.smt2");
    let mode = determine_execution_mode(true, Some(&file), ChcMode::Portfolio);
    assert_eq!(mode, ExecutionMode::Interactive);
}

// --- default DRAT proof path selection (#8864) ---

#[test]
fn test_default_drat_proof_path_cnf_file() {
    let file = PathBuf::from("/tmp/example.cnf");
    let path = default_drat_proof_path(Some(&file)).expect("cnf file should get default path");
    assert_eq!(path, "/tmp/example.cnf.drat");
}

#[test]
fn test_default_drat_proof_path_cnf_file_case_insensitive() {
    let file = PathBuf::from("input.CNF");
    let path = default_drat_proof_path(Some(&file)).expect("CNF (uppercase) should get default");
    assert_eq!(path, "input.CNF.drat");
}

#[test]
fn test_default_drat_proof_path_dimacs_extension() {
    let file = PathBuf::from("bench/foo.dimacs");
    let path = default_drat_proof_path(Some(&file)).expect(".dimacs should get default path");
    assert_eq!(path, "bench/foo.dimacs.drat");
}

#[test]
fn test_default_drat_proof_path_smt2_returns_none() {
    // SMT-LIB files don't get a default DRAT proof — Alethe is the SMT proof
    // format and is handled separately on the SMT execution path.
    let file = PathBuf::from("/tmp/example.smt2");
    assert!(default_drat_proof_path(Some(&file)).is_none());
}

#[test]
fn test_default_drat_proof_path_no_extension_returns_none() {
    let file = PathBuf::from("/tmp/noext");
    assert!(default_drat_proof_path(Some(&file)).is_none());
}

#[test]
fn test_default_drat_proof_path_no_file_returns_none() {
    // stdin mode has no input file → no default proof path.
    assert!(default_drat_proof_path(None).is_none());
}

// --- generalized default proof path selection (proof-carrying by default) ---

#[test]
fn test_default_proof_path_cnf_is_drat() {
    let file = PathBuf::from("/tmp/example.cnf");
    let (path, format) = default_proof_path(Some(&file)).expect("cnf gets a default proof");
    assert_eq!(path, "/tmp/example.cnf.drat");
    assert_eq!(format, ProofFormat::Drat);
}

#[test]
fn test_default_proof_path_smt2_is_alethe() {
    // SMT-LIB UNSAT is proof-carrying by default: a `.smt2` input gets an
    // Alethe certificate written next to it.
    let file = PathBuf::from("/tmp/example.smt2");
    let (path, format) = default_proof_path(Some(&file)).expect("smt2 gets a default proof");
    assert_eq!(path, "/tmp/example.smt2.alethe");
    assert_eq!(format, ProofFormat::Alethe);
}

#[test]
fn test_default_proof_path_smt_extension_is_alethe() {
    let file = PathBuf::from("bench/foo.smt");
    let (path, format) = default_proof_path(Some(&file)).expect(".smt gets a default proof");
    assert_eq!(path, "bench/foo.smt.alethe");
    assert_eq!(format, ProofFormat::Alethe);
}

#[test]
fn test_default_proof_path_smt2_case_insensitive() {
    let file = PathBuf::from("Problem.SMT2");
    let (path, format) = default_proof_path(Some(&file)).expect("SMT2 (uppercase) gets a default");
    assert_eq!(path, "Problem.SMT2.alethe");
    assert_eq!(format, ProofFormat::Alethe);
}

#[test]
fn test_default_proof_path_unknown_extension_returns_none() {
    // MaxSAT/QBF/unknown inputs have no default-proof infrastructure yet.
    assert!(default_proof_path(Some(&PathBuf::from("/tmp/x.wcnf"))).is_none());
    assert!(default_proof_path(Some(&PathBuf::from("/tmp/x.qdimacs"))).is_none());
    assert!(default_proof_path(None).is_none());
}

#[test]
fn test_default_proofs_suppressed_by_no_proof_flag() {
    // --no-proof opts out of the default certificate.
    assert!(default_proofs_suppressed(true, false, false));
    // Neither flag set => proof-carrying stays on.
    assert!(!default_proofs_suppressed(false, false, false));
}

#[test]
fn test_default_proofs_suppressed_by_z3_mode() {
    // --z3-mode keeps the transcript clean: no default proof file.
    assert!(default_proofs_suppressed(false, true, false));
}

#[test]
fn test_default_proofs_suppressed_by_competition() {
    // --competition (or a competition harness env signal) is a speed opt-out.
    assert!(default_proofs_suppressed(false, false, true));
}

#[test]
fn test_firewall_emission_requires_persistent_alethe_proof() {
    assert!(firewall_emission_config_error(false, None).is_none());
    assert!(firewall_emission_config_error(true, None)
        .is_some_and(|error| error.contains("persistent Alethe proof")));

    let drat = ProofConfig::new("proof.drat".to_string(), ProofFormat::Drat, false);
    assert!(firewall_emission_config_error(true, Some(&drat))
        .is_some_and(|error| error.contains("requires an Alethe proof")));

    let temporary = ProofConfig::new_temp("proof.alethe".to_string(), ProofFormat::Alethe, false);
    assert!(firewall_emission_config_error(true, Some(&temporary))
        .is_some_and(|error| error.contains("temporary checker proof")));

    let persistent = ProofConfig::new_default("proof.alethe".to_string(), ProofFormat::Alethe);
    assert!(firewall_emission_config_error(true, Some(&persistent)).is_none());
}

#[test]
fn test_new_default_marks_synthesized_default() {
    let cfg = ProofConfig::new_default("out.alethe".to_string(), ProofFormat::Alethe);
    assert!(cfg.synthesized_default);
    assert!(!cfg.is_temp);
    assert_eq!(cfg.format, ProofFormat::Alethe);
    assert!(!cfg.binary);
}

#[test]
fn default_dimacs_status_collides_with_every_solve_path_class() {
    let temp = tempfile::tempdir().expect("tempdir");
    let input = temp.path().join("problem.cnf");
    std::fs::write(&input, b"p cnf 1 1\n1 0\n").expect("write input");
    let (proof, format) = default_proof_path(Some(&input)).expect("default DIMACS proof");
    assert_eq!(format, ProofFormat::Drat);
    let status = dimacs::dimacs_proof_status_path(&proof);
    let status_lock = dimacs::dimacs_proof_status_lock_path(&status);

    let mut read_collision = SolveArgs {
        file: Some(input.clone()),
        ..SolveArgs::default()
    };
    read_collision.solution_file = Some(status.clone());
    let message = solve_artifact_path_collision(&read_collision, None)
        .expect("validate paths")
        .expect("status must collide with read path");
    assert!(message.contains("default proof status"), "{message}");
    assert!(message.contains("solution witness"), "{message}");

    let mut output_collision = SolveArgs {
        file: Some(input.clone()),
        ..SolveArgs::default()
    };
    output_collision.progress_json = Some(status);
    let message = solve_artifact_path_collision(&output_collision, None)
        .expect("validate paths")
        .expect("status must collide with output path");
    assert!(message.contains("default proof status"), "{message}");
    assert!(message.contains("progress JSON"), "{message}");

    let mut lock_collision = SolveArgs {
        file: Some(input),
        ..SolveArgs::default()
    };
    lock_collision.diagnostic_file = Some(status_lock);
    let message = solve_artifact_path_collision(&lock_collision, None)
        .expect("validate paths")
        .expect("status lock must collide with output path");
    assert!(
        message.contains("default proof status transaction lock"),
        "{message}"
    );
    assert!(message.contains("diagnostic output"), "{message}");
}

// ---------------------------------------------------------------------------
// Proof-output flag relationships (requires/group enforcement)
// ---------------------------------------------------------------------------

#[test]
fn test_proof_format_requires_proof() {
    // Previously `--proof-format lrat foo.cnf` was silently ignored (the
    // default-certificate branch never consults it and wrote DRAT anyway);
    // now it is a loud parse-time error.
    let rejected = <Cli as Parser>::try_parse_from(strings(&[
        "ay",
        "solve",
        "--proof-format",
        "lrat",
        "foo.cnf",
    ]));
    assert!(
        rejected.is_err(),
        "--proof-format without --proof must be rejected"
    );

    let accepted = <Cli as Parser>::try_parse_from(strings(&[
        "ay",
        "solve",
        "--proof",
        "p.lrat",
        "--proof-format",
        "lrat",
        "foo.cnf",
    ]));
    assert!(accepted.is_ok(), "--proof-format with --proof must parse");
}

#[test]
fn test_proof_binary_requires_proof() {
    let rejected =
        <Cli as Parser>::try_parse_from(strings(&["ay", "solve", "--proof-binary", "foo.cnf"]));
    assert!(
        rejected.is_err(),
        "--proof-binary without --proof must be rejected"
    );

    let accepted = <Cli as Parser>::try_parse_from(strings(&[
        "ay",
        "solve",
        "--proof",
        "p.drat",
        "--proof-binary",
        "foo.cnf",
    ]));
    assert!(accepted.is_ok(), "--proof-binary with --proof must parse");
}

#[test]
fn test_proof_output_destinations_are_mutually_exclusive() {
    // `--proof` and the four hidden legacy flags share the `proof_output`
    // group: combining any two is a parse error instead of one silently
    // winning via `build_proof_config`'s fixed precedence.
    let combos: &[&[&str]] = &[
        &["--drat", "a.drat", "--lrat", "b.lrat"],
        &["--drat", "a.drat", "--proof", "b.lrat"],
        &["--lrat-binary", "a.lrat", "--proof", "b.drat"],
        &["--drat-binary", "a.drat", "--lrat-binary", "b.lrat"],
    ];
    for combo in combos {
        let mut argv = vec!["ay", "solve"];
        argv.extend_from_slice(combo);
        argv.push("foo.cnf");
        assert!(
            <Cli as Parser>::try_parse_from(strings(&argv)).is_err(),
            "proof-output combo {combo:?} must be rejected"
        );
    }

    // Each legacy flag alone still parses (backward compatibility).
    for flag in ["--drat", "--drat-binary", "--lrat", "--lrat-binary"] {
        assert!(
            <Cli as Parser>::try_parse_from(strings(&["ay", "solve", flag, "a.out", "foo.cnf"]))
                .is_ok(),
            "{flag} alone must parse"
        );
    }
}

// ---------------------------------------------------------------------------
// Solve-session crash classifier (#chc25-crash)
// ---------------------------------------------------------------------------

/// Windows: only NTSTATUS error-severity (0xC...) exits are crashes; deliberate
/// exit codes — including large/negative ones — are not.
#[cfg(windows)]
#[test]
fn test_solve_session_crash_description_windows() {
    use std::os::windows::process::ExitStatusExt;
    use std::process::ExitStatus;

    // STATUS_STACK_BUFFER_OVERRUN — Rust's fail-fast abort path (`rust_oom`,
    // `std::process::abort()`); the code observed on the chc-comp25 SLayerCF
    // tower OOM aborts.
    let oom_abort = ExitStatus::from_raw(0xC0000409);
    assert!(solve_session_crash_description(&oom_abort).is_some_and(|d| d.contains("0xC0000409")));
    // STATUS_STACK_OVERFLOW and STATUS_ACCESS_VIOLATION are crashes too.
    assert!(solve_session_crash_description(&ExitStatus::from_raw(0xC00000FD)).is_some());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(0xC0000005)).is_some());

    // Deliberate exits must never be reclassified.
    assert!(solve_session_crash_description(&ExitStatus::from_raw(0)).is_none());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(1)).is_none());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(2)).is_none());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(124)).is_none());
    // `exit(-1)` == 0xFFFFFFFF: top nibble 0xF, not NTSTATUS error severity.
    assert!(solve_session_crash_description(&ExitStatus::from_raw(0xFFFFFFFF)).is_none());
}

/// Unix: fatal crash signals are crashes; deliberate exits and external
/// control signals (SIGTERM et al.) are not.
#[cfg(unix)]
#[test]
fn test_solve_session_crash_description_unix() {
    use std::os::unix::process::ExitStatusExt;
    use std::process::ExitStatus;

    // Termination-by-signal wait statuses carry the signal number in the low
    // bits. SIGABRT is the `rust_oom`/`abort()` path.
    assert!(
        solve_session_crash_description(&ExitStatus::from_raw(nix::libc::SIGABRT))
            .is_some_and(|d| d.contains("signal"))
    );
    assert!(solve_session_crash_description(&ExitStatus::from_raw(nix::libc::SIGSEGV)).is_some());

    // External control signals keep the existing propagate behavior.
    assert!(solve_session_crash_description(&ExitStatus::from_raw(nix::libc::SIGTERM)).is_none());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(nix::libc::SIGKILL)).is_none());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(nix::libc::SIGINT)).is_none());

    // Deliberate exit codes live in the high byte of the wait status.
    assert!(solve_session_crash_description(&ExitStatus::from_raw(0)).is_none());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(1 << 8)).is_none());
    assert!(solve_session_crash_description(&ExitStatus::from_raw(124 << 8)).is_none());
}
