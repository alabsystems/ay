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

/// A deadline that fires AFTER a decisive verdict reached stdout must not
/// contradict it. Measured at build.6432 on
/// `QF_BV/…RWS__Example_11.txt.smt2` (AY decides it in 30-90s), at `-T:10`:
/// stdout `sat`, stderr `(:reason-unknown "timeout")`, exit 124 — three
/// mutually inconsistent statements, and a correct answer reported as a
/// failure. z3 on the same budget prints `unknown` and exits 0, so AY produced
/// the BETTER answer and reported it worse. Six files in the 2026-08-02
/// corpus-wide sweep carry this signature.
#[test]
fn timeout_after_a_decisive_verdict_neither_contradicts_it_nor_fails_the_run() {
    // Decisive verdict already published: neutral note, success exit.
    let (note, code) = timeout_exit_policy(true, false, false);
    assert_eq!(code, 0, "a published decisive verdict is not a failed run");
    let note = note.expect("the overrun is still worth noting");
    assert!(
        !String::from_utf8_lossy(note).contains("reason-unknown"),
        "`:reason-unknown` describes an `unknown`; emitting it over a decisive \
         verdict contradicts stdout. got {:?}",
        String::from_utf8_lossy(note)
    );

    // No decisive verdict: unchanged. This is a genuine failure to decide.
    assert_eq!(
        timeout_exit_policy(false, false, false),
        (Some(&b"(:reason-unknown \"timeout\")\n"[..]), 124)
    );
    // The SAT-competition grammar is unchanged in both directions.
    assert_eq!(
        timeout_exit_policy(false, true, false),
        (Some(&b"c timeout\n"[..]), 0)
    );
    assert_eq!(timeout_exit_policy(true, true, false).1, 0);

    // An abandoned export already printed its own `(error ...)`; a timeout note
    // on top would be a second, conflicting explanation. Exit stays non-zero
    // even when a decisive verdict was published, because the artifact the run
    // promised was not produced.
    assert_eq!(timeout_exit_policy(true, false, true), (None, 124));
    assert_eq!(timeout_exit_policy(false, false, true), (None, 124));
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
fn test_satcomp_wrapper_token_accepts_every_route_and_proof_format() {
    // The submission script composes `<route>-<proof_format>-v1` and defaults
    // to `drat`, so rejecting the drat products cost the SHIPPED submission its
    // competition timeout code (exit 0 for UNKNOWN) on every timed-out
    // instance -- it fell back to 124 exactly as if no wrapper were set.
    for route in SAT_COMPETITION_WRAPPER_ROUTES {
        for format in SAT_COMPETITION_WRAPPER_PROOF_FORMATS {
            let token = format!("{route}-{format}-v1");
            assert!(
                is_sat_competition_wrapper_token(&token),
                "{token} is composable by prepare_sat26_submission.sh"
            );
        }
    }

    // Preserved from the exact-match era: trimmed and case-insensitive.
    assert!(is_sat_competition_wrapper_token(
        "  MAIN-REGULAR-DEFAULT-DRAT-V1  "
    ));
}

#[test]
fn test_satcomp_wrapper_token_rejects_non_composable_values() {
    // Widening the predicate to a route x format product must not turn it into
    // a prefix match: each axis still has to land on a known value.
    for token in [
        "main-regular-default-v1",        // no proof format
        "main-regular-default-lrat",      // no version suffix
        "main-regular-default-lrat-v2",   // wrong version
        "main-regular-default-cdcl-v1",   // unknown proof format
        "bogus-route-default-drat-v1",    // unknown route
        "main-regular-default-drat-v1-x", // trailing junk
        "-drat-v1",                       // empty route
        "drat-v1",
        "-v1",
        "",
    ] {
        assert!(
            !is_sat_competition_wrapper_token(token),
            "{token:?} is not composable and must not change timeout grammar"
        );
    }
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
fn test_preprocess_z3_context_unknown_option_is_invalid_carrier() {
    // In a z3 invocation (argv0 `z3` or `--z3-mode`), an option z3's parser
    // does not know becomes the invalid-option carrier (z3 message, exit
    // 109) instead of reaching clap.
    let by_argv0 = preprocess_args(strings(&["/tmp/z3", "-zzz", "input.smt2"]));
    assert!(
        by_argv0
            .windows(2)
            .any(|pair| pair == ["--invalid-z3-option", "-zzz"]),
        "{by_argv0:?}"
    );
    let by_flag = preprocess_args(strings(&["ay", "--z3-mode", "-zzz"]));
    assert!(
        by_flag
            .windows(2)
            .any(|pair| pair == ["--invalid-z3-option", "-zzz"]),
        "{by_flag:?}"
    );
    // Natively, the same spelling is left for clap to diagnose.
    let native = preprocess_args(strings(&["ay", "-zzz"]));
    assert!(
        !native.iter().any(|arg| arg == "--invalid-z3-option"),
        "{native:?}"
    );
    // AY's own short flags are never "invalid", even in z3 context.
    for ok in ["-q", "-t", "-t500", "-t=500", "-h", "-V"] {
        let processed = preprocess_args(strings(&["/tmp/z3", ok, "input.smt2"]));
        assert!(
            !processed.iter().any(|arg| arg == "--invalid-z3-option"),
            "{ok} must stay valid: {processed:?}"
        );
    }
    // Unknown `--long` spellings take the same carrier in z3 context
    // (z3: `Error: invalid command line option: --zzz`, exit 109), while
    // AY's own long flags — bare or `=value`-joined — pass through.
    for bad in ["--zzz", "--zzz=1"] {
        let processed = preprocess_args(strings(&["/tmp/z3", bad, "input.smt2"]));
        assert!(
            processed
                .windows(2)
                .any(|pair| pair == ["--invalid-z3-option", bad]),
            "{bad} must be invalid: {processed:?}"
        );
    }
    let native_long = preprocess_args(strings(&["ay", "--zzz"]));
    assert!(
        !native_long.iter().any(|arg| arg == "--invalid-z3-option"),
        "{native_long:?}"
    );
    for ok in ["--z3-mode", "--timeout=500", "--help", "--version"] {
        let processed = preprocess_args(strings(&["/tmp/z3", ok, "input.smt2"]));
        assert!(
            !processed.iter().any(|arg| arg == "--invalid-z3-option"),
            "{ok} must stay valid: {processed:?}"
        );
    }
}

#[test]
fn test_preprocess_z3_context_second_input_is_duplicate_carrier() {
    // z3 warns `WARNING: input file was already specified.` and solves the
    // first file; the second becomes a carrier, never the positional FILE.
    let processed = preprocess_args(strings(&["/tmp/z3", "a.smt2", "b.smt2"]));
    assert!(
        processed
            .windows(2)
            .any(|pair| pair == ["--z3-duplicate-input", "b.smt2"]),
        "{processed:?}"
    );
    assert!(
        processed
            .iter()
            .filter(|arg| arg.as_str() == "a.smt2")
            .count()
            == 1,
        "{processed:?}"
    );
    // The `-file:` spelling counts as the input too.
    let by_file = preprocess_args(strings(&["/tmp/z3", "-file:a.smt2", "b.smt2"]));
    assert!(
        by_file
            .windows(2)
            .any(|pair| pair == ["--z3-duplicate-input", "b.smt2"]),
        "{by_file:?}"
    );
    // Files after `--` are positional for clap, so carriers must be placed
    // before the separator.
    let after_sep = preprocess_args(strings(&["/tmp/z3", "--", "a.smt2", "b.smt2"]));
    let sep = after_sep.iter().position(|arg| arg == "--").unwrap();
    assert!(
        after_sep[..sep]
            .windows(2)
            .any(|pair| pair == ["--z3-duplicate-input", "b.smt2"]),
        "{after_sep:?}"
    );
    // Natively, two files keep reaching clap (which rejects the second).
    let native = preprocess_args(strings(&["ay", "a.smt2", "b.smt2"]));
    assert!(
        !native.iter().any(|arg| arg == "--z3-duplicate-input"),
        "{native:?}"
    );
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
fn z3_optimization_input_modes_are_routed_instead_of_rejected() {
    assert_eq!(
        preprocess_args(strings(&["ay", "-wcnf", "-in"])),
        strings(&["ay", "solve", "--z3-input-mode=wcnf", "--incremental"])
    );
    assert_eq!(
        preprocess_args(strings(&["ay", "-lp", "problem.lp"])),
        strings(&["ay", "solve", "--z3-input-mode=lp", "problem.lp"])
    );
    assert_eq!(
        preprocess_args(strings(&["ay", "problem.opb"])),
        strings(&["ay", "solve", "--z3-input-mode=opb", "problem.opb"])
    );
    assert_eq!(
        preprocess_args(strings(&["ay", "-pbo", "-in"])),
        strings(&["ay", "solve", "--z3-input-mode=opb", "--incremental"])
    );
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

/// `--memory-ceiling-bytes` parses as bytes, conflicts with the `--memory`
/// override, and refuses 0, which would disable the limit (2026-09-12).
#[test]
fn test_memory_ceiling_bytes_parses_and_is_never_an_override() {
    let parse = |args: &[&str]| <Cli as Parser>::try_parse_from(strings(args));
    let cli = parse(&[
        "ay",
        "solve",
        "f.cnf",
        "--memory-ceiling-bytes",
        "32000000000",
    ])
    .expect("parse the ceiling");
    match cli.command {
        Some(Command::Solve(args)) => {
            assert_eq!(args.memory_ceiling_bytes, Some(32_000_000_000));
            assert_eq!(args.memory, None);
        }
        _ => panic!("expected a solve command"),
    }
    assert!(parse(&[
        "ay",
        "solve",
        "f.cnf",
        "--memory-ceiling-bytes",
        "1",
        "--memory",
        "4096"
    ])
    .is_err());
    assert!(parse(&["ay", "solve", "f.cnf", "--memory-ceiling-bytes", "0"]).is_err());
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
fn test_bench_run_requires_complete_shard_pair() {
    let missing_size = <Cli as Parser>::try_parse_from(strings(&[
        "ay",
        "bench",
        "run",
        "smt-smtcomp-qf-lia",
        "--shard-index",
        "0",
    ]));
    assert!(missing_size.is_err());

    let missing_index = <Cli as Parser>::try_parse_from(strings(&[
        "ay",
        "bench",
        "run",
        "smt-smtcomp-qf-lia",
        "--shard-size",
        "64",
    ]));
    assert!(missing_index.is_err());
}

#[test]
fn test_bench_run_preserves_shard_selection() {
    let cli = <Cli as Parser>::try_parse_from(strings(&[
        "ay",
        "bench",
        "run",
        "smt-smtcomp-qf-lia",
        "--shard-index",
        "7",
        "--shard-size",
        "64",
    ]))
    .expect("parse bench run shard selection");

    match cli.command {
        Some(Command::Bench(cmd_bench::BenchCommand::Run {
            shard_index,
            shard_size,
            ..
        })) => {
            assert_eq!(shard_index, Some(7));
            assert_eq!(shard_size, Some(64));
        }
        _ => panic!("unexpected command"),
    }
}

#[test]
fn test_bench_run_rejects_out_of_range_shard_size() {
    for size in ["0", "4097"] {
        let parsed = <Cli as Parser>::try_parse_from(strings(&[
            "ay",
            "bench",
            "run",
            "smt-smtcomp-qf-lia",
            "--shard-index",
            "0",
            "--shard-size",
            size,
        ]));
        assert!(parsed.is_err(), "accepted shard size {size}");
    }
}

/// clap validates a command definition only when debug assertions are on, and
/// then a malformed argument panics on EVERY parse, while release builds accept
/// it silently (`--no-probe-ite-lift-promoter` was once a positional). Check the
/// whole command tree here instead of waiting for a spawned test to crash.
#[test]
fn cli_definition_passes_clap_debug_asserts() {
    Cli::command().debug_assert();
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
    // Build the expectation through `Path` too: the certificate is a sibling of
    // the input, and `set_file_name` renders the separator in the platform's
    // own form (`bench\foo...` on Windows), which is not a behaviour difference.
    let expected = PathBuf::from("bench").join("foo.dimacs.drat");
    assert_eq!(path, expected.to_string_lossy());
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

/// `--no-proof`, `--z3-mode` and `--rigor fast` (`--competition`) shed the
/// executor's proof cycle. A PLAIN solve does NOT: batteries are on by
/// default, so a flagless run keeps the tracker armed, mints its certificate
/// and writes the sidecar.
#[test]
fn test_proof_cycle_shed_follows_the_opt_outs() {
    let bare = SolveArgs::default();
    let no_proof = SolveArgs {
        no_proof: true,
        ..SolveArgs::default()
    };
    let z3_mode = SolveArgs {
        z3_mode: true,
        ..SolveArgs::default()
    };
    let competition = SolveArgs {
        competition: true,
        ..SolveArgs::default()
    };
    let rigor_fast = SolveArgs {
        assurance: Some(CliAssuranceLevel::Fast),
        ..SolveArgs::default()
    };
    let rigor_standard = SolveArgs {
        assurance: Some(CliAssuranceLevel::Standard),
        ..SolveArgs::default()
    };
    let strict = SolveArgs {
        strict_proofs: true,
        ..SolveArgs::default()
    };
    let self_check = SolveArgs {
        self_check: true,
        ..SolveArgs::default()
    };
    let explicit_proof = SolveArgs {
        proof: Some(PathBuf::from("out.alethe")),
        ..SolveArgs::default()
    };
    let verify_proof = SolveArgs {
        verify_proof: true,
        ..SolveArgs::default()
    };
    // The env-signal leg of `competition_mode` is not exercised here; the
    // certifying expectations below hold only when no harness signal is
    // present in the test environment.
    if crate::competition_mode::competition_env_active() {
        return;
    }
    // Shed: the explicit opt-outs, and nothing else. `--rigor fast` gets
    // there through its documented projection onto `--competition`, so the
    // dial has to be resolved the way `run_solve` resolves it.
    let mut rigor_fast = rigor_fast;
    rigor_fast.resolve_assurance();
    assert!(
        rigor_fast.competition,
        "--rigor fast projects onto --competition"
    );
    for args in [&no_proof, &z3_mode, &competition, &rigor_fast] {
        assert!(proof_cycle_shed(args));
    }
    // Armed: the PLAIN default (`ay FILE.smt2` — proofs and certificates are
    // the product, not overhead) and every explicit certification request.
    for args in [
        &bare,
        &rigor_standard,
        &strict,
        &self_check,
        &explicit_proof,
        &verify_proof,
    ] {
        assert!(!proof_cycle_shed(args));
    }
    // A certification request combined with an opt-out still sheds at the CLI
    // latch; executor-side precedence (`competition_shedding_active`) is what
    // keeps the certified lanes armed for the demand itself.
    let strict_no_proof = SolveArgs {
        strict_proofs: true,
        no_proof: true,
        ..SolveArgs::default()
    };
    assert!(proof_cycle_shed(&strict_no_proof));
}

/// A memout names the ceiling's origin (2026-09-12): the govern default is
/// called out as a machine guard with the setting that raises both bounds, an
/// explicit flag is credited as such, the unarmed default names RAM, and
/// `--memory 0` (the ceiling off) never claims the flag.
#[test]
fn test_memory_limit_origin_names_the_posture() {
    let gib3 = Some(3072usize * 1024 * 1024);
    let guard = memory_limit_origin(None, gib3);
    assert!(guard.starts_with("90% of the kernel-held govern budget of 3072 MiB"));
    assert!(guard.contains("physical RAM / 16 as a machine guard"));
    // The setting that moves BOTH bounds: `--memory` alone would sit above
    // the kernel's kill line wherever the solve runs unsupervised.
    assert!(guard.contains("raise both with GOVERN_AY_MB=<MiB>"));
    assert_eq!(memory_limit_origin(Some(32768), gib3), "--memory flag");
    assert_eq!(memory_limit_origin(Some(32768), None), "--memory flag");
    assert!(memory_limit_origin(None, None).starts_with("85% of physical RAM"));
    assert_ne!(memory_limit_origin(Some(0), gib3), "--memory flag");
    assert_ne!(memory_limit_origin(Some(0), None), "--memory flag");
}

/// The note states the ceiling in MiB as one `c` line, and is written only in
/// the SAT-competition grammar outside Z3 mode.
#[test]
fn test_memory_limit_note_is_one_sat_comment_line_outside_z3_mode() {
    let note = memory_limit_note(2764 * 1024 * 1024, "origin text");
    assert_eq!(
        note,
        "c memout: process memory limit 2764 MiB (origin text)\n"
    );
    assert!(memory_limit_note_applies(
        MEMOUT_STDERR_SAT_COMPETITION,
        false
    ));
    assert!(!memory_limit_note_applies(
        MEMOUT_STDERR_SAT_COMPETITION,
        true
    ));
    assert!(!memory_limit_note_applies(MEMOUT_STDERR_SMTLIB, false));
}

/// The allocator ceiling's breach action carries the note after the
/// SAT-competition reason line, keeps the verdict and exit code, and is the
/// untouched static action in Z3 mode, on the SMT-LIB grammar, or with no
/// note set — the burst path is the one a big formula's memout takes.
#[test]
fn test_hard_ceiling_action_bakes_in_the_note_only_where_it_applies() {
    let note = "c memout: process memory limit 2764 MiB (origin)\n";
    let sat = &HARD_CEILING_SAT_COMPETITION;
    let with = hard_ceiling_action_with_note(sat, Some(note), false);
    assert_eq!(with.stdout_line, MEMOUT_STDOUT_SAT_COMPETITION);
    assert_eq!(with.exit_code, sat.exit_code);
    assert_eq!(
        with.stderr_line,
        b"c memout\nc memout: process memory limit 2764 MiB (origin)\n".as_slice()
    );
    assert!(std::ptr::eq(
        hard_ceiling_action_with_note(sat, Some(note), true),
        sat
    ));
    assert!(std::ptr::eq(
        hard_ceiling_action_with_note(sat, None, false),
        sat
    ));
    let smt = &HARD_CEILING_SMTLIB;
    assert!(std::ptr::eq(
        hard_ceiling_action_with_note(smt, Some(note), false),
        smt
    ));
}

/// The memory-budget verdict LINES follow the input format at every posture;
/// the EXIT CODE keeps the wrapper/competition conventions.
#[test]
fn test_memout_verdict_lines_follow_the_input_format_not_the_posture() {
    use VerdictGrammarRoute::*;
    let sat_lines = |v: MemoutVerdict| v.sat_competition_lines;
    // SMT-LIB: never the SAT-competition grammar, whatever the posture.
    for (wrapper, competition) in [(false, false), (false, true), (true, false), (true, true)] {
        let verdict = memout_verdict_for(SmtLib, wrapper, competition);
        assert!(!sat_lines(verdict), "SMT-LIB memout must print `unknown`");
        assert_eq!(verdict.stdout_line(), MEMOUT_STDOUT_SMTLIB);
        assert_eq!(verdict.stderr_line(), MEMOUT_STDERR_SMTLIB);
        // Exit code: 0 only under the submission wrapper, like an SMT timeout.
        assert_eq!(
            verdict.exit_code,
            if wrapper {
                SAT_COMPETITION_UNKNOWN_EXIT_CODE
            } else {
                DEFAULT_TIMEOUT_EXIT_CODE
            }
        );
    }
    // DIMACS: always the SAT-competition lines (as the DIMACS timeout path
    // prints); exit 0 under the wrapper OR competition mode, else 124.
    for (wrapper, competition) in [(false, false), (false, true), (true, false), (true, true)] {
        let verdict = memout_verdict_for(Dimacs, wrapper, competition);
        assert!(sat_lines(verdict), "DIMACS memout must print `s UNKNOWN`");
        assert_eq!(verdict.stdout_line(), MEMOUT_STDOUT_SAT_COMPETITION);
        assert_eq!(
            verdict.exit_code,
            if wrapper || competition {
                SAT_COMPETITION_UNKNOWN_EXIT_CODE
            } else {
                DEFAULT_TIMEOUT_EXIT_CODE
            }
        );
    }
    // Route not yet known: the legacy heuristic (posture-keyed) stands.
    assert!(!sat_lines(memout_verdict_for(Undecided, false, false)));
    assert!(sat_lines(memout_verdict_for(Undecided, false, true)));
    assert!(sat_lines(memout_verdict_for(Undecided, true, false)));
    assert_eq!(
        memout_verdict_for(Undecided, false, false).exit_code,
        DEFAULT_TIMEOUT_EXIT_CODE
    );
    assert_eq!(
        memout_verdict_for(Undecided, false, true).exit_code,
        SAT_COMPETITION_UNKNOWN_EXIT_CODE
    );
    // Every (lines, exit) pair maps to a static whose bytes agree with it, so
    // the allocator-time breach prints exactly what the watchdog would.
    for route in [SmtLib, Dimacs, Undecided] {
        for (wrapper, competition) in [(false, false), (false, true), (true, false)] {
            let verdict = memout_verdict_for(route, wrapper, competition);
            let action = verdict.hard_ceiling_action();
            assert_eq!(action.stdout_line, verdict.stdout_line());
            assert_eq!(action.stderr_line, verdict.stderr_line());
            assert_eq!(action.exit_code, verdict.exit_code);
        }
    }
}

#[test]
fn test_verdict_grammar_route_from_input_extension() {
    use VerdictGrammarRoute::*;
    let route = |p: &str| VerdictGrammarRoute::from_input_path(Some(FsPath::new(p)));
    assert_eq!(route("a.smt2"), SmtLib);
    assert_eq!(route("dir/b.SMT"), SmtLib);
    assert_eq!(route("c.cnf"), Dimacs);
    assert_eq!(route("d.DIMACS"), Dimacs);
    assert_eq!(route("e.wcnf"), Undecided);
    assert_eq!(route("noext"), Undecided);
    assert_eq!(VerdictGrammarRoute::from_input_path(None), Undecided);
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

/// The memory watchdog polls until the budget is breached, then signals the
/// cooperative stop and waits out the grace period before its caller
/// hard-exits. This is the escalation that makes `--memory` enforceable when
/// no solver thread reaches a cancellation checkpoint.
#[test]
fn memory_watchdog_signals_then_waits_out_the_grace_period() {
    let mut polls = 0_u32;
    let mut slept: Vec<Duration> = Vec::new();
    let breached = std::cell::Cell::new(false);

    run_memory_watchdog(
        || {
            polls += 1;
            polls > 3
        },
        || false,
        Duration::from_millis(500),
        Duration::from_secs(2),
        || breached.set(true),
        |waited| slept.push(waited),
    );

    assert!(
        breached.get(),
        "the cooperative stop must fire on the first breach"
    );
    assert_eq!(polls, 4, "the watchdog polls until the budget is breached");
    assert_eq!(
        slept,
        vec![Duration::from_millis(500); 7],
        "one sleep per under-budget poll, then the grace period in poll steps"
    );
}

/// Past the breach, pressure at the critical share ends the grace at once:
/// the process is about to be killed from outside, which would lose the
/// verdict line.
#[test]
fn memory_watchdog_cuts_the_grace_short_at_critical_pressure() {
    let mut slept: Vec<Duration> = Vec::new();
    let mut checks = 0_u32;

    run_memory_watchdog(
        || true,
        || {
            checks += 1;
            checks > 2
        },
        Duration::from_millis(10),
        Duration::from_secs(2),
        || {},
        |waited| slept.push(waited),
    );

    assert_eq!(slept, vec![Duration::from_millis(10); 2]);
}

/// A run that is already over budget when the watchdog arms escalates without
/// waiting a full poll interval first.
#[test]
fn memory_watchdog_escalates_immediately_when_already_over_budget() {
    let mut slept: Vec<Duration> = Vec::new();
    let breached = std::cell::Cell::new(false);

    run_memory_watchdog(
        || true,
        || false,
        Duration::from_secs(1),
        Duration::from_secs(2),
        || breached.set(true),
        |waited| slept.push(waited),
    );

    assert!(breached.get());
    assert_eq!(
        slept,
        vec![Duration::from_secs(1); 2],
        "no poll sleep before the breach is observed"
    );
}

/// A memout and a timeout both emit the required `unknown` verdict, but carry
/// distinct markers so a harness can tell them apart. The DIMACS memout
/// additionally carries its `c memout` marker on STDOUT: wrapper scripts
/// (~/ay-bench/bin/ay-proofmode) forward only stdout plus an exit code that is
/// 0 for every competition unknown, so a stderr-only marker made a memout
/// unscoreable through them.
///
/// The memout lines are now selected by the INPUT ROUTE, so this pairs each
/// route with the timeout grammar that route's timeout path already prints:
/// DIMACS with the SAT-competition lines, SMT-LIB with z3's.
#[test]
fn memout_and_timeout_share_the_verdict_but_not_the_reason() {
    for (route, sat_lines) in [
        (VerdictGrammarRoute::SmtLib, false),
        (VerdictGrammarRoute::Dimacs, true),
    ] {
        let memout = memout_verdict_for(route, sat_lines, false);
        assert_eq!(memout.sat_competition_lines, sat_lines);
        assert!(
            memout
                .stdout_line()
                .ends_with(timeout_stdout_line_for_sat_competition_wrapper(sat_lines)),
            "resource exhaustion must end in the same unknown verdict grammar"
        );
        assert_ne!(
            memout.stderr_line(),
            timeout_stderr_line_for_sat_competition_wrapper(sat_lines),
            "a memout must be distinguishable from a timeout"
        );
    }
    assert_eq!(
        memout_verdict_for(VerdictGrammarRoute::Dimacs, false, false).stdout_line(),
        b"c memout\ns UNKNOWN\n",
        "DIMACS memouts must carry the marker on stdout for \
         stdout-only wrappers"
    );
    assert_eq!(
        memout_verdict_for(VerdictGrammarRoute::SmtLib, false, false).stdout_line(),
        b"unknown\n",
        "the SMT-LIB verdict stream stays a bare verdict"
    );
    assert_eq!(
        memout_verdict_for(VerdictGrammarRoute::SmtLib, false, false).stderr_line(),
        b"(:reason-unknown \"memout\")\n",
        "SMT-LIB runs report Z3's memout reason"
    );
}

/// The Z3-compatible path must be supervised. It is the path every benchmark
/// harness drives, and while it was excluded it was the one path on which a
/// crashing solve produced no verdict at all. Its empty-stderr contract is kept
/// by suppressing the session markers instead — see `eprint_session_marker`.
#[test]
fn z3_mode_solves_are_supervised() {
    assert!(solve_session_needs_wrapper(&strings(&[
        "ay",
        "solve",
        "--z3-mode",
        "in.smt2"
    ])));
    assert!(solve_session_needs_wrapper(&strings(&[
        "ay",
        "solve",
        "--z3-mode",
        "--memory",
        "8576",
        "--incremental"
    ])));
}

/// The exclusions that remain are the ones the supervisor genuinely cannot
/// honor: an in-flight CNF export whose generation it cannot authenticate after
/// an abort, and the flags whose machine-readable stderr it would corrupt.
#[test]
fn export_and_machine_readable_paths_stay_unsupervised() {
    for flag in [
        "--dump-bv-cnf",
        "--features",
        "--stats-json",
        "--z3-parameter-request",
        "--z3-catalog-request",
        "--unsupported-z3-option",
    ] {
        assert!(
            !solve_session_needs_wrapper(&strings(&["ay", "solve", flag, "in.smt2"])),
            "{flag} must stay unsupervised"
        );
    }
}

/// `--z3-mode` has to be visible to `main` *before* the fork, or the pre-fork
/// `c ay.session.start` marker escapes onto a transcript that must be empty.
/// That includes the flag being injected because argv[0] was `z3`.
#[test]
fn z3_mode_is_detected_before_the_fork_including_argv0_injection() {
    assert!(solve_z3_mode_requested(&strings(&[
        "ay",
        "solve",
        "--z3-mode",
        "in.smt2"
    ])));
    assert!(!solve_z3_mode_requested(&strings(&[
        "ay", "solve", "in.smt2"
    ])));

    // argv[0] of `z3` injects the flag during preprocessing; the pre-fork check
    // reads the PREPROCESSED args, so an injected flag counts like an explicit
    // one and the marker is suppressed on that path too.
    let processed = preprocess_args(strings(&["/usr/local/bin/z3", "in.smt2"]));
    assert!(
        solve_z3_mode_requested(&processed),
        "argv0-injected --z3-mode must be seen pre-fork, got {processed:?}"
    );

    // Past `--`, a literal `--z3-mode` is an operand, not a flag.
    assert!(!solve_z3_mode_requested(&strings(&[
        "ay",
        "solve",
        "--",
        "--z3-mode"
    ])));
}

/// T8 (the development design notes): the executors ay-chc builds for its
/// SEARCH queries inherit the CLI executor's EFFECTIVE proof-cycle posture —
/// shed under `--competition` / `--no-proof` / `--z3-mode`, never under a proof
/// or certificate demand, never on a plain solve.
#[test]
fn test_search_executor_sheds_proof_cycle_mirrors_the_cli_executor() {
    let sheds = |extra: &[&str]| -> bool {
        let mut argv = vec!["ay", "solve", "f.smt2"];
        argv.extend_from_slice(extra);
        match <Cli as Parser>::try_parse_from(strings(&argv))
            .expect("parse solve args")
            .command
        {
            Some(Command::Solve(args)) => {
                competition_mode::search_executor_sheds_proof_cycle(&args)
            }
            _ => panic!("expected a solve command"),
        }
    };
    // A plain solve is proof-carrying; the three opt-outs shed.
    assert!(!sheds(&[]));
    assert!(sheds(&["--competition"]));
    assert!(sheds(&["--no-proof"]));
    assert!(sheds(&["--z3-mode"]));
    // Every proof / certificate demand keeps the default posture, exactly as
    // executor-side precedence does for the CLI's own executor.
    assert!(!sheds(&["--competition", "--strict-proofs"]));
    assert!(!sheds(&["--competition", "--self-check"]));
    assert!(!sheds(&["--competition", "--proof", "out.chccert"]));
    assert!(!sheds(&["--competition", "--verify-firewall"]));
    assert!(!sheds(&[
        "--competition",
        "--emit-firewall-lean",
        "lean-out"
    ]));
    assert!(!sheds(&["--competition", "--verify-proof"]));
    // The opt-in checked replay re-executes certificate obligations on a
    // fresh search executor, so a positive budget is a demand too.
    assert!(!sheds(&["--competition", "--chc-checked-replay", "5"]));
    assert!(sheds(&["--competition", "--chc-checked-replay", "0"]));
}
