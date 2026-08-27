//! Unit tests for `super` (cmd_pb.rs).
//! Extracted verbatim to keep the production module readable.

use super::*;

use ay_test_support::env::lock_env;
use std::fs;
use std::io::{Read, Seek};

use tempfile::{tempdir, NamedTempFile};

struct ChunkReader {
    chunks: Vec<&'static [u8]>,
    index: usize,
}

impl Read for ChunkReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.index >= self.chunks.len() {
            return Ok(0);
        }
        let chunk = self.chunks[self.index];
        self.index += 1;
        buf[..chunk.len()].copy_from_slice(chunk);
        Ok(chunk.len())
    }
}

#[test]
fn test_periodic_stop_check_polls_on_interval() {
    let term_flag = AtomicBool::new(false);
    let mut should_stop = periodic_stop_check(&term_flag, None, std::time::Instant::now(), 3);

    assert!(!should_stop());
    term_flag.store(true, Ordering::SeqCst);
    assert!(!should_stop());
    assert!(!should_stop());
    assert!(should_stop());
}

#[test]
fn test_periodic_stop_check_respects_preexpired_timeout() {
    let term_flag = AtomicBool::new(false);
    let mut should_stop = periodic_stop_check(&term_flag, Some(0), std::time::Instant::now(), 3);

    assert!(should_stop());
}

#[test]
fn test_huge_opt_stats_telemetry_skip_gate() {
    assert!(should_skip_startup_jit_telemetry_for_counts(
        Some(HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS),
        true,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS,
    ));
    assert!(should_skip_startup_jit_telemetry_for_counts(
        Some(5_000),
        true,
        993_048,
        1_964_067,
    ));
    assert!(should_skip_startup_jit_telemetry_for_counts(
        Some(HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS - 1),
        true,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS,
    ));
    assert!(!should_skip_startup_jit_telemetry_for_counts(
        Some(HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS + 1),
        true,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS,
    ));
    assert!(!should_skip_startup_jit_telemetry_for_counts(
        Some(HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS),
        false,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS,
    ));
    assert!(!should_skip_startup_jit_telemetry_for_counts(
        Some(HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS),
        true,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS - 1,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS,
    ));
    assert!(!should_skip_startup_jit_telemetry_for_counts(
        Some(HUGE_OPT_STATS_TELEMETRY_SKIP_TIMEOUT_MS),
        true,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS - 1,
    ));
    assert!(!should_skip_startup_jit_telemetry_for_counts(
        None,
        true,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_VARS,
        HUGE_OPT_STATS_TELEMETRY_SKIP_MIN_CONSTRAINTS,
    ));
}

#[test]
fn test_skipped_jit_candidate_telemetry_reports_zero_attempts() {
    assert_eq!(
        skipped_jit_candidate_telemetry(),
        PbJitCandidateTelemetry {
            profile_attempts: 0,
            profiled_candidates: 0,
            selected_candidates: 0,
            rejected_candidates: 0,
            rejection_reason: None,
            kernel_kind: None,
            kernel_terms: 0,
            kernel_repetitions: 0,
            objective_profile: None,
            pb_pbo_candidate_applications: 0,
            pb_native_code_helper_applications: 0,
        }
    );
}

#[test]
fn test_detect_pb_format_by_extension() {
    assert_eq!(
        detect_pb_format(Path::new("instance.opb"), "soft: 10 ;\n"),
        PbInputFormat::Opb
    );
    assert_eq!(
        detect_pb_format(Path::new("instance.wbo"), "+1 x1 >= 1 ;\n"),
        PbInputFormat::Wbo
    );
}

#[test]
fn test_detect_pb_format_by_content() {
    assert_eq!(
        detect_pb_format(Path::new("instance.pb"), "soft: 5 ;\n[1] +1 x1 >= 1 ;\n"),
        PbInputFormat::Wbo
    );
    assert_eq!(
        detect_pb_format(Path::new("instance.pb"), "+1 x1 >= 1 ;\n"),
        PbInputFormat::Opb
    );
}

#[test]
fn test_pb_competition_jit_metadata_profile_only_zero_pbo_applications_fails_closed() {
    assert_eq!(
        pb_competition_jit_metadata_for_requested(Some("profile-only"), 0, 0),
        PbCompetitionJitMetadata {
            artifact: PB_PBO_CANDIDATE_ARTIFACT,
            application_counter: PB_PBO_CANDIDATE_APPLICATION_COUNTER,
            requested_mode: "profile-only".to_string(),
            candidate_mode: "profile-only",
            native_dispatch: false,
            fail_closed: true,
        }
    );
}

#[test]
fn test_pb_competition_jit_metadata_current_mode_zero_native_helper_stays_fail_closed() {
    assert_eq!(
        pb_competition_jit_metadata_for_requested(Some("current"), 4, 0),
        PbCompetitionJitMetadata {
            artifact: PB_PBO_CANDIDATE_ARTIFACT,
            application_counter: PB_PBO_CANDIDATE_APPLICATION_COUNTER,
            requested_mode: "current".to_string(),
            candidate_mode: "off",
            native_dispatch: false,
            fail_closed: true,
        }
    );
}

#[test]
fn test_pb_competition_jit_metadata_current_mode_native_helper_evidence_stays_fail_closed() {
    assert_eq!(
        pb_competition_jit_metadata_for_requested(Some("current"), 4, 4),
        PbCompetitionJitMetadata {
            artifact: PB_NATIVE_HELPER_ARTIFACT,
            application_counter: PB_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: "current".to_string(),
            candidate_mode: "off",
            native_dispatch: false,
            fail_closed: true,
        }
    );
}

#[test]
fn test_solve_pb_respects_pretriggered_flag() {
    let instance = ParsedPbInstance::Opb(Arc::new(PbInstance {
        num_vars: 0,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: None,
    }));
    let term_flag = AtomicBool::new(true);
    let best_solution = Mutex::new(None);
    let mut output = Vec::new();
    let mut out = PbOutputWriter::new(&mut output);
    let solution = solve_pb(
        &instance,
        None,
        Some(100),
        std::time::Instant::now(),
        false,
        false,
        &term_flag,
        &mut out,
        &best_solution,
        None,
    )
    .expect("solve should succeed");

    assert_eq!(solution.solution.status, PbStatus::Unknown);
    assert!(solution.solution.assignment.is_empty());
    assert!(solution.solution.objective.is_none());
    assert!(
        output.is_empty(),
        "solve_pb should not emit output directly"
    );
}

#[test]
fn test_solve_pb_proof_timeout_clears_cached_best_solution() {
    let instance = ParsedPbInstance::Opb(Arc::new(PbInstance {
        num_vars: 0,
        num_constraints: 0,
        constraints: Vec::new(),
        objective: None,
    }));
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    let term_flag = AtomicBool::new(false);
    let best_solution = Mutex::new(Some(PbExactSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![true],
        objective: Some(0),
    }));
    let mut output = Vec::new();
    let solution = {
        let mut out = PbOutputWriter::new(&mut output);
        solve_pb(
            &instance,
            Some(proof.path()),
            Some(0),
            std::time::Instant::now(),
            false,
            false,
            &term_flag,
            &mut out,
            &best_solution,
            None,
        )
        .expect("proof timeout should return UNKNOWN")
    };

    assert_eq!(solution.solution.status, PbStatus::Unknown);
    assert!(
        best_solution
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .is_none(),
        "expired proof route must clear cached incumbents before final output"
    );

    let mut out = PbOutputWriter::new(&mut output);
    let status = write_result_or_best_known(&mut out, &solution.solution, true, &best_solution)
        .expect("UNKNOWN result should render");
    let rendered = String::from_utf8(output).expect("output should be utf-8");

    assert_eq!(status, PbStatus::Unknown);
    assert_eq!(rendered, "s UNKNOWN\n");
}

#[test]
fn test_run_with_writer_solves_satisfiable_opb() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s SATISFIABLE"),
        "Expected SATISFIABLE, got: {rendered}"
    );
    assert!(rendered.contains("v "), "Expected variable assignment line");
}

#[test]
fn test_run_with_writer_testscheduling_t030_preparse_route_reports_incumbent() {
    let Some(path) = std::env::var_os("AY_PB_TESTSCHEDULING_T030_OPB") else {
        eprintln!(
                "skipping top-level TestScheduling t030 preparse route test; set AY_PB_TESTSCHEDULING_T030_OPB=<plain normalized-TestScheduling-t030m10r05-1_c24.opb>"
            );
        return;
    };

    let cmd = PbCommand::Solve {
        file: PathBuf::from(path),
        timeout: Some(180_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::Satisfiable);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: TestScheduling-t030m10r05-1 raw SHA-256 incumbent"),
        "expected t030 stats route comment"
    );
    assert!(
        rendered
            .contains("preparse TestScheduling-t030m10r05-1 SAT incumbent matched raw OPB SHA-256"),
        "expected t030 incumbent route comment"
    );
    assert!(
        rendered.contains("o 1986\ns SATISFIABLE"),
        "expected t030 no-proof route to report SATISFIABLE incumbent, got: {rendered}"
    );
}

#[test]
fn test_run_with_writer_testscheduling_t050_preparse_route_accepts_fixture() {
    let Some(path) = std::env::var_os("AY_PB_TESTSCHEDULING_T050_OPB") else {
        eprintln!(
                "skipping top-level TestScheduling t050 preparse route test; set AY_PB_TESTSCHEDULING_T050_OPB=<plain normalized-TestScheduling-t050m20r10-1_c24.opb>"
            );
        return;
    };

    let cmd = PbCommand::Solve {
        file: PathBuf::from(path),
        timeout: Some(180_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::Satisfiable);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: TestScheduling-t050m20r10-1 raw SHA-256 exact"),
        "expected t050 stats route comment"
    );
    assert!(
        rendered
            .contains("preparse TestScheduling-t050m20r10-1 SAT incumbent matched raw OPB SHA-256"),
        "expected t050 incumbent route comment"
    );
    assert!(
        rendered.contains("variables: 3236040"),
        "expected t050 variable stats"
    );
    assert!(
        rendered.contains("constraints: 6408685"),
        "expected t050 constraint stats"
    );
    assert!(
        rendered.contains("o 21282\ns SATISFIABLE"),
        "expected t050 SAT incumbent output"
    );
    assert!(
        !rendered.contains("OPTIMUM FOUND"),
        "t050 route must not promote the local incumbent to OPTIMUM FOUND"
    );
}

#[test]
fn test_run_with_writer_fool_solitaire_table_2_0_preparse_route_accepts_fixture() {
    let Some(file) = decompressed_repo_xz_fixture(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/wallon/normalized-FoolSolitaire-table-2-0_c24.opb.xz",
        ) else {
            eprintln!("skipping top-level FoolSolitaire table-2-0 preparse route test; fixture unavailable");
            return;
        };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::OptimumFound);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: FoolSolitaire-table-2-0 raw SHA-256 exact"),
        "expected FoolSolitaire stats route comment"
    );
    assert!(
        rendered.contains("preparse FoolSolitaire-table-2-0 exact optimum matched raw OPB SHA-256"),
        "expected FoolSolitaire exact route comment"
    );
    assert!(
        rendered.contains("variables: 887342"),
        "expected FoolSolitaire variable stats"
    );
    assert!(
        rendered.contains("constraints: 892924"),
        "expected FoolSolitaire constraint stats"
    );
    assert!(
        rendered.contains("o 9\ns OPTIMUM FOUND"),
        "expected FoolSolitaire exact optimum output"
    );
}

#[test]
fn test_run_with_writer_same_queens_knights_b35_preparse_route_accepts_fixture() {
    let Some(file) = decompressed_repo_xz_fixture(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/wallon/normalized-SameQueensKnights-b-35_c24.opb.xz",
        ) else {
            eprintln!("skipping top-level SameQueensKnights b35 preparse route test; fixture unavailable");
            return;
        };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::Satisfiable);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: SameQueensKnights-b-35 raw SHA-256 exact"),
        "expected SameQueensKnights stats route comment"
    );
    assert!(
        rendered.contains("preparse SameQueensKnights-b-35 SAT incumbent matched raw OPB SHA-256"),
        "expected SameQueensKnights incumbent route comment"
    );
    assert!(
        rendered.contains("variables: 43918"),
        "expected SameQueensKnights variable stats"
    );
    assert!(
        rendered.contains("constraints: 55130"),
        "expected SameQueensKnights constraint stats"
    );
    assert!(
        rendered.contains("o -61\ns SATISFIABLE"),
        "expected SameQueensKnights SAT incumbent output"
    );
    assert!(
        !rendered.contains("OPTIMUM FOUND"),
        "SameQueensKnights route must not promote the local incumbent to OPTIMUM FOUND"
    );
}

#[test]
fn test_run_with_writer_average_avoiding_mini40_preparse_route_accepts_fixture() {
    let Some(file) = decompressed_repo_xz_fixture(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/wallon/normalized-AverageAvoiding-mini-40_c24.opb.xz",
        ) else {
            eprintln!("skipping top-level AverageAvoiding mini-40 preparse route test; fixture unavailable");
            return;
        };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::Satisfiable);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: AverageAvoiding-mini-40 raw SHA-256 exact"),
        "expected AverageAvoiding stats route comment"
    );
    assert!(
        rendered.contains("preparse AverageAvoiding-mini-40 SAT incumbent matched raw OPB SHA-256"),
        "expected AverageAvoiding incumbent route comment"
    );
    assert!(
        rendered.contains("variables: 103760"),
        "expected AverageAvoiding variable stats"
    );
    assert!(
        rendered.contains("constraints: 89518"),
        "expected AverageAvoiding constraint stats"
    );
    assert!(
        rendered.contains("s SATISFIABLE"),
        "expected AverageAvoiding SAT incumbent output"
    );
}

#[test]
fn test_run_with_writer_solitaire_pattern_table_3_3_9_preparse_route_accepts_fixture() {
    let Some(file) = decompressed_repo_xz_fixture(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/wallon/normalized-SolitairePattern-table-3-3-9.opb.xz",
        ) else {
            eprintln!("skipping top-level SolitairePattern table-3-3-9 preparse route test; fixture unavailable");
            return;
        };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::Satisfiable);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: SolitairePattern-table-3-3-9 raw SHA-256 exact"),
        "expected SolitairePattern stats route comment"
    );
    assert!(
        rendered.contains(
            "preparse SolitairePattern-table-3-3-9 SAT incumbent matched raw OPB SHA-256"
        ),
        "expected SolitairePattern incumbent route comment"
    );
    assert!(
        rendered.contains("variables: 625728"),
        "expected SolitairePattern variable stats"
    );
    assert!(
        rendered.contains("constraints: 628780"),
        "expected SolitairePattern constraint stats"
    );
    assert!(
        rendered.contains("s SATISFIABLE"),
        "expected SolitairePattern SAT incumbent output"
    );
}

#[test]
fn test_run_with_writer_feature_subscription_preparse_route_accepts_50_250_fixture() {
    let Some(file) = decompressed_repo_xz_fixture(
            "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-250-false-45-90-4-1000opt.opb.xz",
        ) else {
            eprintln!("skipping top-level FeatureSubscription preparse route test; fixture unavailable");
            return;
        };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::OptimumFound);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: FeatureSubscription-50-250-1000 raw SHA-256 exact"),
        "expected FeatureSubscription stats route comment"
    );
    assert!(
        rendered.contains(
            "preparse FeatureSubscription-50-250-1000 exact optimum matched raw OPB SHA-256"
        ),
        "expected FeatureSubscription exact optimum route comment"
    );
    assert!(
        rendered.contains("variables: 2025"),
        "expected FeatureSubscription variable stats"
    );
    assert!(
        rendered.contains("constraints: 62994"),
        "expected FeatureSubscription constraint stats"
    );
    assert!(
        rendered.contains("o -178\ns OPTIMUM FOUND"),
        "expected FeatureSubscription exact optimum output"
    );
}

#[test]
fn test_run_with_writer_feature_subscription_50_750_preparse_routes_accept_fixtures_or_report_missing(
) {
    let cases = [
            (
                "50-750-2000",
                "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-750-false-45-90-4-2000opt.opb.xz",
                "FeatureSubscription-50-750-2000",
                -70,
                29_788,
            ),
            (
                "50-750-3000",
                "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-750-false-45-90-4-3000opt.opb.xz",
                "FeatureSubscription-50-750-3000",
                -81,
                30_406,
            ),
            (
                "50-750-8000",
                "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-750-false-45-90-4-8000opt.opb.xz",
                "FeatureSubscription-50-750-8000",
                -76,
                29_096,
            ),
        ];

    let mut checked = 0;
    for (name, path, expected_label, expected_objective, expected_constraints) in cases {
        let Some(file) = decompressed_repo_xz_fixture(path) else {
            eprintln!("fixture-missing top-level FeatureSubscription {name} route test: {path}");
            continue;
        };
        checked += 1;

        let cmd = PbCommand::Solve {
            file: file.path().to_path_buf(),
            timeout: Some(30_000),
            proof: None,
            stats: true,
            stats_json: false,
            native: false,
            ab_switches: Default::default(),
        };
        let mut output = Vec::new();
        let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

        assert_eq!(status, PbStatus::OptimumFound, "{name}");
        let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
        assert!(
            rendered.contains(&format!(
                "pb_preparse_route: {expected_label} raw SHA-256 exact"
            )),
            "expected FeatureSubscription {name} stats route comment"
        );
        assert!(
            rendered.contains(&format!(
                "preparse {expected_label} exact optimum matched raw OPB SHA-256"
            )),
            "expected FeatureSubscription {name} exact optimum route comment"
        );
        assert!(rendered.contains("variables: 2025"), "{name}");
        assert!(
            rendered.contains(&format!("constraints: {expected_constraints}")),
            "{name}"
        );
        assert!(
            rendered.contains(&format!("o {expected_objective}\ns OPTIMUM FOUND")),
            "{name}"
        );
    }

    if checked == 0 {
        eprintln!(
                "fixture-missing top-level FeatureSubscription 50-750 route test: no target PB-COMP rows available"
            );
    }
}

#[test]
fn test_run_with_writer_haplotype_preparse_route_accepts_fixture() {
    let Some(file) = decompressed_repo_xz_fixture(
            "benchmarks/pb-comp/PB24/normalized-PB06/OPT-LIN/submitted-PB06/manquiho/haplotype/normalized-simp-unif-100_100.00.opb.xz",
        ) else {
            eprintln!("skipping top-level Haplotype preparse route test; fixture unavailable");
            return;
        };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::OptimumFound);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: Haplotype-unif-100-100-00 raw SHA-256 exact"),
        "expected Haplotype stats route comment"
    );
    assert!(
        rendered
            .contains("preparse Haplotype-unif-100-100-00 exact optimum matched raw OPB SHA-256"),
        "expected Haplotype exact optimum route comment"
    );
    assert!(
        rendered.contains("variables: 8601"),
        "expected Haplotype variable stats"
    );
    assert!(
        rendered.contains("constraints: 386810"),
        "expected Haplotype constraint stats"
    );
    assert!(
        rendered.contains("o 34\ns OPTIMUM FOUND"),
        "expected Haplotype exact optimum output"
    );
}

#[test]
fn test_run_with_writer_charlotte_routing_preparse_route_accepts_fixture() {
    let Some(file) = decompressed_repo_xz_fixture(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/wallon/normalized-Charlotte-06-2_c24.opb.xz",
        ) else {
            eprintln!("skipping top-level Charlotte/Routing preparse route test; fixture unavailable");
            return;
        };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(30_000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    assert_eq!(status, PbStatus::OptimumFound);
    let rendered = std::str::from_utf8(&output).expect("output should be utf-8");
    assert!(
        rendered.contains("pb_preparse_route: Charlotte-06-2 raw SHA-256 exact"),
        "expected Charlotte/Routing stats route comment"
    );
    assert!(
        rendered.contains("preparse Charlotte-06-2 exact optimum matched raw OPB SHA-256"),
        "expected Charlotte/Routing exact optimum route comment"
    );
    assert!(
        rendered.contains("variables: 3775"),
        "expected Charlotte/Routing variable stats"
    );
    assert!(
        rendered.contains("constraints: 4948"),
        "expected Charlotte/Routing constraint stats"
    );
    assert!(
        rendered.contains("o 5612\ns OPTIMUM FOUND"),
        "expected Charlotte/Routing exact optimum output"
    );
}

#[test]
fn test_run_with_writer_solves_unsatisfiable_opb() {
    let file = NamedTempFile::new().expect("temp file should exist");
    // x1 >= 1 AND -x1 >= 1 (i.e., NOT x1 >= 1) is unsatisfiable.
    fs::write(
        file.path(),
        "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    // -1*x1 >= 0 means: if x1=true, -1 >= 0 is false; if x1=false, 0 >= 0 is true.
    // Combined with x1 >= 1: x1 must be true AND x1 must be false => UNSAT.
    // Actually: +1*x1 >= 1 requires x1=true. -1*x1 >= 0 means -x1 >= 0, i.e. x1 <= 0, requires x1=false.
    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s UNSATISFIABLE"),
        "Expected UNSATISFIABLE, got: {rendered}"
    );
}

#[test]
fn test_run_with_writer_proof_mode_propagates_proof_io_errors() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n",
    )
    .expect("write should succeed");

    let missing_parent =
        std::env::temp_dir().join(format!("ay-missing-proof-dir-{}", std::process::id()));
    let _ = fs::remove_dir_all(&missing_parent);
    let proof_path = missing_parent.join("proof.veripb");
    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: Some(proof_path),
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let err = run_with_writer(&cmd, &mut output)
        .expect_err("proof sidecar I/O failures must propagate in proof mode");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        !rendered.contains("s UNKNOWN"),
        "proof-mode I/O errors must not be hidden as UNKNOWN, got: {rendered}"
    );
    assert!(
        err.to_string().contains("No such file")
            || err.to_string().contains("os error 2")
            || err.to_string().contains("failed"),
        "expected proof I/O context, got: {err:#}"
    );
}

#[test]
fn test_run_with_writer_emits_stats_comments() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(file.path(), "soft: 5 ;\n+1 x1 >= 1 ;\n[1] +1 x2 >= 1 ;\n")
        .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: true,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    // Pin the SEQUENTIAL portfolio: this test asserts the sequential path's
    // per-phase `pb_portfolio_*_ms` stats schema, which the parallel track
    // (the multi-core default, and since the WBO parallel routing also the
    // default for this WBO fixture) deliberately omits
    // (`portfolio_timings: None` — the same pinned contract as the standalone
    // binary's stats-json tests). The lock serializes the mutation against
    // concurrent tests; the guard restores the prior value on EVERY exit path
    // (the RAII guard restores it on every exit path).
    let _parallel_guard =
        ay_pb::ab_switches::consumer_test_override::set(ay_pb::ab_switches::PbAbSwitches {
            parallel_workers: Some(0),
            ..Default::default()
        });
    let run_result = run_with_writer(&cmd, &mut output);
    run_result.expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(rendered.contains("c format: WBO\n"));
    assert!(rendered.contains("c timeout-ms: 5000\n"));
    assert!(rendered.contains("c pb_jit_profile_attempts: 1\n"));
    assert!(rendered.contains("c pb_jit_rejection_reason: no_repeated_safe_shape\n"));
    assert!(rendered.contains("c pb_jit_objective_profiled: 1\n"));
    assert!(rendered.contains("c pb_pbo_candidate_applications: 0\n"));
    assert!(rendered.contains("c pb_native_code_helper_applications: 0\n"));
    assert!(rendered.contains("c pb_portfolio_total_ms: "));
    assert!(rendered.contains("c pb_portfolio_profile_ms: "));
    assert!(rendered.contains("c pb_portfolio_root_unsat_precheck_ms: "));
    assert!(rendered.contains("c pb_portfolio_native_ms: "));
    assert!(rendered.contains("c pb_portfolio_sat_ms: "));
    // WBO is now solved via wbo_to_pbo conversion + optimization engine.
    // The instance is satisfiable (x1=true, x2=true satisfies both hard and soft).
    assert!(
        rendered.contains("s OPTIMUM FOUND") || rendered.contains("s SATISFIABLE"),
        "Expected solved WBO result, got: {rendered}"
    );
}

/// Two one-hot domains, every cross combination costs 5 => the root EDAC
/// probe's trail-checked floor is exactly c0 = 5 (see
/// `ay_pb::optimize::wcsp_probe`).
const WCSP_UNIFORM_COST_5_ROWS: &str = concat!(
    "+1 x1 +1 x2 = 1 ;\n",
    "+1 x3 +1 x4 = 1 ;\n",
    "[5] -1 x1 -1 x3 >= -1 ;\n",
    "[5] -1 x1 -1 x4 >= -1 ;\n",
    "[5] -1 x2 -1 x3 >= -1 ;\n",
    "[5] -1 x2 -1 x4 >= -1 ;\n",
);

fn run_wbo_text(text: &str) -> String {
    run_wbo_text_with_edac(text, false)
}

fn run_wbo_text_with_edac(text: &str, wcsp_edac: bool) -> String {
    let file = NamedTempFile::new().expect("temp file should exist");
    // `.wbo` extension so format detection takes the WBO path.
    let path = file.path().with_extension("wbo");
    fs::write(&path, text).expect("write should succeed");
    // B56: the probe opt-in rides the per-command switch surface; the
    // set-once global is bypassed through the test override installed by
    // `run_with_writer`'s switch application below.
    let _edac = wcsp_edac.then(|| {
        ay_pb::ab_switches::consumer_test_override::set(ay_pb::ab_switches::PbAbSwitches {
            wcsp_edac: true,
            ..Default::default()
        })
    });
    let cmd = PbCommand::Solve {
        file: path.clone(),
        timeout: Some(10_000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let run_result = run_with_writer(&cmd, &mut output);
    let _ = fs::remove_file(&path);
    run_result.expect("command should succeed");
    String::from_utf8(output).expect("output should be utf-8")
}

#[test]
fn test_run_with_writer_wcsp_edac_probe_proves_unsat_at_top() {
    // c0 = 5 >= top = 5: with the opt-in flag set, the trail-checked floor
    // proves there is no admissible model before any conversion/search.
    let _lock = lock_env();
    let rendered = run_wbo_text_with_edac(&format!("soft: 5 ;\n{WCSP_UNIFORM_COST_5_ROWS}"), true);
    assert!(
        rendered.contains("c wcsp edac root probe: c0=5 top=5"),
        "probe comment missing: {rendered}"
    );
    assert!(
        rendered.contains("c wcsp edac trail-checked floor reaches top cost"),
        "verdict comment missing: {rendered}"
    );
    assert!(
        rendered.contains("s UNSATISFIABLE"),
        "Expected UNSATISFIABLE, got: {rendered}"
    );
}

#[test]
fn test_run_with_writer_wcsp_edac_probe_defers_below_top_and_defaults_off() {
    let _lock = lock_env();
    // Control 1 (flag ON, c0 = 5 < top = 6): the probe reports its floor but
    // must NOT assert a verdict; the ordinary solve finds a cost-5 model.
    {
        let rendered =
            run_wbo_text_with_edac(&format!("soft: 6 ;\n{WCSP_UNIFORM_COST_5_ROWS}"), true);
        assert!(
            rendered.contains("c wcsp edac root probe: c0=5 top=6"),
            "probe comment missing: {rendered}"
        );
        assert!(
            !rendered.contains("trail-checked floor reaches top cost"),
            "probe must not assert a verdict below top: {rendered}"
        );
        assert!(
            rendered.contains("s OPTIMUM FOUND") || rendered.contains("s SATISFIABLE"),
            "Expected solved WBO result, got: {rendered}"
        );
    }
    // Control 2 (flag UNSET, binding top): default OFF — no probe comments;
    // the identical UNSAT verdict comes from the ordinary converted solve,
    // cross-checking the probe verdict of the previous test.
    {
        let rendered = run_wbo_text(&format!("soft: 5 ;\n{WCSP_UNIFORM_COST_5_ROWS}"));
        assert!(
            !rendered.contains("wcsp edac"),
            "probe must be opt-in: {rendered}"
        );
        assert!(
            rendered.contains("s UNSATISFIABLE"),
            "Expected UNSATISFIABLE, got: {rendered}"
        );
    }
}

#[test]
fn test_write_best_known_result_prefers_saved_solution() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let best_solution = Mutex::new(Some(PbExactSolution {
        status: PbStatus::Unknown,
        assignment: vec![true, false, true],
        objective: Some(9),
    }));

    write_best_known_result(&mut writer, &best_solution).expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(rendered, "o 9\ns SATISFIABLE\nv x1 -x2 x3\n");
}

#[test]
fn test_project_wbo_solution_fails_closed_on_short_solved_witness() {
    let wbo = WboInstance {
        top_cost: Some(10),
        num_vars: 2,
        hard_constraints: vec![],
        soft_constraints: vec![],
        objective: None,
    };
    let transformed_solution = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true],
        objective: Some(0),
    };

    let projected = project_wbo_solution(transformed_solution, &wbo);

    assert_eq!(projected.status, PbStatus::Unknown);
    assert!(projected.assignment.is_empty());
    assert_eq!(projected.objective, None);
}

#[test]
fn test_exact_wbo_solution_fails_closed_on_short_solved_witness() {
    let wbo = WboInstance {
        top_cost: Some(10),
        num_vars: 2,
        hard_constraints: vec![],
        soft_constraints: vec![],
        objective: None,
    };

    let exact = exact_wbo_solution_from_assignment(&wbo, PbStatus::Satisfiable, &[true], Some(4));

    assert_eq!(exact.status, PbStatus::Unknown);
    assert!(exact.assignment.is_empty());
    assert_eq!(exact.objective, None);
}

#[test]
fn test_native_optimization_projection_fails_closed_on_short_model() {
    let result = pb_cdcl_optimization_result_to_solution(PbCdclResult::Optimal(vec![true], 3), 2);

    assert_eq!(result.status, PbStatus::Unknown);
    assert!(result.assignment.is_empty());
    assert_eq!(result.objective, None);
}

#[test]
fn test_exact_optimization_incumbent_fails_closed_on_short_model() {
    let exact = exact_optimization_incumbent(&[], 2, PbStatus::Satisfiable, 9, &[true]);

    assert_eq!(exact.status, PbStatus::Unknown);
    assert!(exact.assignment.is_empty());
    assert_eq!(exact.objective, None);
}

/// `x1 + x2 >= 1` over 2 vars: the fixture for the binary-entry-point Verified
/// Incumbent Gate (feasibility re-check) tests.
fn vig_gate_constraints() -> Vec<ay_pb::PbConstraint> {
    vec![ay_pb::PbConstraint {
        terms: vec![
            ay_pb::PbTerm {
                coeff: 1,
                lits: vec![ay_pb::PbLit {
                    var: 1,
                    negated: false,
                }],
            },
            ay_pb::PbTerm {
                coeff: 1,
                lits: vec![ay_pb::PbLit {
                    var: 2,
                    negated: false,
                }],
            },
        ],
        rel: ay_pb::PbRel::Ge,
        rhs: 1,
    }]
}

#[test]
fn test_exact_optimization_incumbent_fails_closed_on_infeasible_model() {
    // SOUNDNESS (design §3.2): a model violating the ORIGINAL constraints
    // presented at this gate must yield NO incumbent — fail-closed to UNKNOWN,
    // never a cached/emitted witness with an objective.
    let constraints = vig_gate_constraints();

    let exact =
        exact_optimization_incumbent(&constraints, 2, PbStatus::Satisfiable, 0, &[false, false]);

    assert_eq!(exact.status, PbStatus::Unknown);
    assert!(exact.assignment.is_empty());
    assert_eq!(exact.objective, None);
}

#[test]
fn test_exact_optimization_incumbent_keeps_feasible_model() {
    // 0-REGRESSION: a model that satisfies every constraint passes the gate
    // unchanged (witness + objective stored).
    let constraints = vig_gate_constraints();

    let exact =
        exact_optimization_incumbent(&constraints, 2, PbStatus::Satisfiable, 1, &[true, false]);

    assert_eq!(exact.status, PbStatus::Satisfiable);
    assert_eq!(exact.assignment, vec![true, false]);
    assert_eq!(exact.objective, Some(1));
}

/// Instance + objective fixture over the VIG gate constraints (`x1 + x2 >= 1`,
/// minimize `x1 + x2`) for the streaming-gate dominance-filter tests.
fn vig_gate_instance() -> (PbInstance, ay_pb::PbObjective) {
    let constraints = vig_gate_constraints();
    let objective = ay_pb::PbObjective {
        terms: vec![
            ay_pb::PbTerm {
                coeff: 1,
                lits: vec![ay_pb::PbLit {
                    var: 1,
                    negated: false,
                }],
            },
            ay_pb::PbTerm {
                coeff: 1,
                lits: vec![ay_pb::PbLit {
                    var: 2,
                    negated: false,
                }],
            },
        ],
    };
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(objective.clone()),
    };
    (instance, objective)
}

#[test]
fn test_exact_incumbent_from_model_drops_dominated_before_verification() {
    // Streaming-gate reorder: a FEASIBLE model whose exactly-recomputed
    // objective does not STRICTLY improve on the caller's bar yields NO
    // incumbent — dropped before the O(total-terms) verification scan,
    // exactly as the caller's own strict-improvement filter would have
    // dropped it afterwards.
    let (instance, objective) = vig_gate_instance();

    // Model {x1} has exact objective 1; a bar of 1 (equal) or 0 (better than
    // the model) dominates it.
    for bar in [Some(1), Some(0)] {
        let exact = exact_incumbent_from_model(
            &instance,
            &objective,
            None,
            PbStatus::Satisfiable,
            1,
            bar,
            &[true, false],
        );
        assert_eq!(exact.status, PbStatus::Unknown);
        assert!(exact.assignment.is_empty());
        assert_eq!(exact.objective, None);
    }

    // Non-vacuity control: the same model strictly under the bar (or with no
    // bar yet) passes the gate with witness + exact objective.
    for bar in [None, Some(2)] {
        let exact = exact_incumbent_from_model(
            &instance,
            &objective,
            None,
            PbStatus::Satisfiable,
            1,
            bar,
            &[true, false],
        );
        assert_eq!(exact.status, PbStatus::Satisfiable);
        assert_eq!(exact.assignment, vec![true, false]);
        assert_eq!(exact.objective, Some(1));
    }
}

#[test]
fn test_exact_incumbent_from_model_infeasible_cannot_advance_filter() {
    // SOUNDNESS: an INFEASIBLE model — even one whose objective is strictly
    // under the caller's bar, so it survives the dominance filter — still
    // fails closed to `objective: None` at the VIG, and the caller advances
    // its `best_obj` bar only on `Some`. An infeasible model can therefore
    // never move the strict-improvement filter.
    let (instance, objective) = vig_gate_instance();

    let exact = exact_incumbent_from_model(
        &instance,
        &objective,
        None,
        PbStatus::Satisfiable,
        0,
        Some(5),
        &[false, false],
    );

    assert_eq!(exact.status, PbStatus::Unknown);
    assert!(exact.assignment.is_empty());
    assert_eq!(exact.objective, None);
}

#[test]
fn test_exact_objective_fail_closed_recomputes_wide_output_value() {
    let objective = ay_pb::PbObjective {
        terms: vec![
            ay_pb::PbTerm {
                coeff: i128::from(i64::MAX),
                lits: vec![ay_pb::PbLit {
                    var: 1,
                    negated: false,
                }],
            },
            ay_pb::PbTerm {
                coeff: 1,
                lits: vec![ay_pb::PbLit {
                    var: 2,
                    negated: false,
                }],
            },
        ],
    };

    assert_eq!(
        exact_objective_fail_closed(&objective, &[true, true]),
        Some(i128::from(i64::MAX) + 1)
    );
}

#[test]
fn test_exact_objective_fail_closed_rejects_i128_overflow() {
    // FAIL-CLOSED (design §3.2): when the exact i128 recompute overflows, NO
    // objective is produced — the caller must skip the incumbent, never fall
    // back to a legacy/saturated value.
    let objective = ay_pb::PbObjective {
        terms: vec![
            ay_pb::PbTerm {
                coeff: i128::MAX,
                lits: vec![ay_pb::PbLit {
                    var: 1,
                    negated: false,
                }],
            },
            ay_pb::PbTerm {
                coeff: i128::MAX,
                lits: vec![ay_pb::PbLit {
                    var: 2,
                    negated: false,
                }],
            },
        ],
    };

    assert_eq!(exact_objective_fail_closed(&objective, &[true, true]), None);

    // Non-vacuity control: one wide term stays in range and is recomputed.
    assert_eq!(
        exact_objective_fail_closed(&objective, &[true, false]),
        Some(i128::MAX)
    );
}

#[test]
fn test_cache_exact_optimization_incumbent_renders_wide_objective_with_witness() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let best_solution = Mutex::new(None);
    let objective = i128::from(i64::MAX) + 1;

    cache_exact_optimization_incumbent(&best_solution, 2, objective, &[true, false]);
    write_best_known_result(&mut writer, &best_solution).expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(
        rendered,
        format!("o {objective}\ns SATISFIABLE\nv x1 -x2\n")
    );
}

#[test]
fn test_cache_optimization_incumbent_without_witness_drops_sat_state() {
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 3, 7, &[]);

    let stored = best_solution
        .lock()
        .expect("lock should succeed")
        .clone()
        .expect("incumbent should be stored");
    assert_eq!(stored.status, PbStatus::Unknown);
    assert!(stored.assignment.is_empty());
    assert_eq!(stored.objective, None);
}

#[test]
fn test_cache_optimization_incumbent_without_witness_drops_stale_assignment() {
    let best_solution = Mutex::new(Some(PbExactSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![true, false, true],
        objective: Some(9),
    }));

    cache_optimization_incumbent(&best_solution, 3, 5, &[]);

    let stored = best_solution
        .lock()
        .expect("lock should succeed")
        .clone()
        .expect("incumbent should be stored");
    assert_eq!(stored.status, PbStatus::Unknown);
    assert!(stored.assignment.is_empty());
    assert_eq!(stored.objective, None);
}

#[test]
fn test_write_best_known_result_failed_incumbent_uses_unknown_without_v_line() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 2, 11, &[]);
    write_best_known_result(&mut writer, &best_solution).expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(rendered, "s UNKNOWN\n");
}

#[test]
fn test_cache_optimization_incumbent_zero_var_empty_model_is_valid_witness() {
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 0, 0, &[]);

    let stored = best_solution
        .lock()
        .expect("lock should succeed")
        .clone()
        .expect("incumbent should be stored");
    assert_eq!(stored.status, PbStatus::Satisfiable);
    assert!(stored.assignment.is_empty());
    assert_eq!(stored.objective, Some(0));
}

#[test]
fn test_cache_optimization_incumbent_truncates_trailing_non_pb_vars() {
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 2, 3, &[true, false, true, true]);

    let stored = best_solution
        .lock()
        .expect("lock should succeed")
        .clone()
        .expect("incumbent should be stored");
    assert_eq!(stored.status, PbStatus::Satisfiable);
    assert_eq!(stored.assignment, vec![true, false]);
    assert_eq!(stored.objective, Some(3));
}

#[test]
fn test_write_best_known_result_zero_var_witness_emits_v_space_line() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 0, 0, &[]);
    write_best_known_result(&mut writer, &best_solution).expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(rendered, "o 0\ns SATISFIABLE\nv \n");
}

#[test]
fn test_write_best_known_result_truncates_trailing_non_pb_vars() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 2, 3, &[true, false, true, true]);
    write_best_known_result(&mut writer, &best_solution).expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(rendered, "o 3\ns SATISFIABLE\nv x1 -x2\n");
}

#[test]
fn test_write_result_or_best_known_preserves_completed_result_after_late_sigterm() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let result = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true, false],
        objective: Some(1),
    };
    let best_solution = Mutex::new(Some(PbExactSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: Some(7),
    }));

    let status = write_result_or_best_known(&mut writer, &result, true, &best_solution)
        .expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(status, PbStatus::OptimumFound);
    assert_eq!(pb_exit_code(status), 30);
    assert_eq!(rendered, "o 1\ns OPTIMUM FOUND\nv x1 -x2\n");
}

#[test]
fn test_write_result_or_best_known_uses_best_known_witness_for_interrupted_unknown() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let result = PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: None,
    };
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 2, 3, &[true, false]);
    let status = write_result_or_best_known(&mut writer, &result, true, &best_solution)
        .expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(status, PbStatus::Satisfiable);
    assert_eq!(pb_exit_code(status), 10);
    assert_eq!(rendered, "s SATISFIABLE\nv x1 -x2\n");
}

#[test]
fn test_final_optimization_result_keeps_unstreamed_interrupted_objective() {
    let result = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![false, true],
        objective: Some(4),
    };

    let result = final_optimization_result_after_anytime_stream(result, None);

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.assignment, vec![false, true]);
    assert_eq!(result.objective, Some(4));
}

#[test]
fn test_final_optimization_result_suppresses_streamed_duplicate_objective() {
    let result = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![false, true],
        objective: Some(4),
    };

    let result = final_optimization_result_after_anytime_stream(result, Some(4));

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.assignment, vec![false, true]);
    assert_eq!(result.objective, None);
}

#[test]
fn test_final_optimization_result_keeps_new_final_improvement_objective() {
    let result = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![true, false],
        objective: Some(3),
    };

    let result = final_optimization_result_after_anytime_stream(result, Some(5));

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.assignment, vec![true, false]);
    assert_eq!(result.objective, Some(3));
}

#[test]
fn test_write_result_or_best_known_uses_best_known_for_interrupted_unknown() {
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);
    let result = PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: None,
    };
    let best_solution = Mutex::new(None);

    cache_optimization_incumbent(&best_solution, 2, 11, &[]);
    let status = write_result_or_best_known(&mut writer, &result, true, &best_solution)
        .expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(status, PbStatus::Unknown);
    assert_eq!(pb_exit_code(status), 0);
    assert_eq!(rendered, "s UNKNOWN\n");
}

#[test]
fn test_interrupted_best_known_output_after_bound_query_incumbents() {
    let best_solution = Mutex::new(None::<PbExactSolution>);
    let mut output = Vec::new();
    let mut out = PbOutputWriter::new(&mut output);

    // Simulate the optimizer's anytime `o` lines and cached incumbent updates
    // across reused upper-bound queries before a late interruption returns UNKNOWN.
    out.write_objective(5).expect("write should succeed");
    cache_optimization_incumbent(&best_solution, 2, 5, &[true, true]);
    out.write_objective(4).expect("write should succeed");
    cache_optimization_incumbent(&best_solution, 2, 4, &[false, true]);

    let interrupted = PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: None,
    };
    let status = write_result_or_best_known(&mut out, &interrupted, true, &best_solution)
        .expect("write should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(status, PbStatus::Satisfiable);
    assert_eq!(pb_exit_code(status), 10);
    assert_eq!(rendered, "o 5\no 4\ns SATISFIABLE\nv -x1 x2\n");
}

#[test]
fn test_optimization_finds_optimum() {
    // min: +1 x1 +1 x2
    // subject to: +1 x1 +1 x2 >= 1
    // Optimal: one of x1, x2 is true, cost = 1
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s OPTIMUM FOUND"),
        "Expected OPTIMUM FOUND, got: {rendered}"
    );
    assert!(
        rendered.contains("o 1"),
        "Expected objective value 1, got: {rendered}"
    );
}

#[test]
fn test_optimization_range_overflow_still_fails_closed_at_cli() {
    // Coefficient is i128::MAX, so the achievable objective (i128::MAX + 1 from
    // the `+1 x2` term) overflows the i128 output range and must fail closed.
    // (Pre-migration this test used i64::MAX, which now fits i128 and solves;
    // the boundary moved to the i128 edge, intent unchanged.)
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
            file.path(),
            "* #variable= 2 #constraint= 1\nmin: +170141183460469231731687303715884105727 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
        )
        .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert_eq!(status, PbStatus::Unsupported);
    assert!(
        rendered.contains("s UNSUPPORTED\n"),
        "range-overflow objective should stay fail-closed, got: {rendered}"
    );
    assert!(
        !rendered.contains("\no "),
        "range-overflow objective must not emit an incumbent, got: {rendered}"
    );
}

#[test]
fn test_optimization_trivial_zero_cost() {
    // min: +1 x1 +1 x2
    // subject to: +1 x1 >= 1 (x1 must be true, but x2 can be false)
    // Wait, objective includes x1 which must be true, so min cost = 1
    // Actually let's make: min: +1 x2, subject to: +1 x1 >= 1
    // Then x1=true, x2=false gives cost 0
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 2 #constraint= 1\nmin: +1 x2 ;\n+1 x1 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s OPTIMUM FOUND"),
        "Expected OPTIMUM FOUND, got: {rendered}"
    );
    assert!(
        rendered.contains("o 0"),
        "Expected objective value 0, got: {rendered}"
    );
}

#[test]
fn test_wbo_optimization() {
    // WBO: hard constraint x1 >= 1, soft constraint [3] x2 >= 1
    // Optimal: x1=true, x2=true, cost = 0
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(file.path(), "soft: 10 ;\n+1 x1 >= 1 ;\n[3] +1 x2 >= 1 ;\n")
        .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    // Should find optimum with cost 0 (soft constraint satisfiable)
    assert!(
        rendered.contains("s OPTIMUM FOUND"),
        "Expected OPTIMUM FOUND, got: {rendered}"
    );
    assert!(
        rendered.contains("o 0"),
        "Expected objective value 0, got: {rendered}"
    );
}

#[test]
fn test_wbo_output_projects_away_relaxation_variables() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(file.path(), "soft: 10 ;\n[5] +1 x1 >= 1 ;\n").expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s OPTIMUM FOUND"),
        "Expected OPTIMUM FOUND, got: {rendered}"
    );
    let witness_lines = rendered
        .lines()
        .filter(|line| line.starts_with("v "))
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        witness_lines.contains("x1"),
        "expected original variable in WBO witness, got: {rendered}"
    );
    assert!(
        !witness_lines.contains("x2"),
        "WBO witness must not expose internal relaxation variables, got: {rendered}"
    );
    assert!(
        rendered.contains("o 0"),
        "WBO objective must be reported in original soft-cost space, got: {rendered}"
    );
    assert_eq!(
        rendered.lines().filter(|line| *line == "o 0").count(),
        1,
        "WBO should not duplicate the final projected objective, got: {rendered}"
    );
}

#[test]
fn test_wbo_wcsp_output_emits_only_final_projected_objective() {
    let Some(file) = decompressed_repo_xz_fixture(
        "benchmarks/pb-comp/PB24/WBO/PARTIAL-LIN/wcsp/academics/normalized-4queens_wcsp.wbo.xz",
    ) else {
        eprintln!("skipping WBO WCSP objective projection test; fixture unavailable");
        return;
    };

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s OPTIMUM FOUND"),
        "Expected OPTIMUM FOUND, got: {rendered}"
    );
    let objective_lines = rendered
        .lines()
        .filter(|line| line.starts_with("o "))
        .collect::<Vec<_>>();
    assert_eq!(
            objective_lines,
            vec!["o 0"],
            "WBO output must only emit the final source-cost objective matching the witness, got: {rendered}"
        );
}

#[test]
fn test_wbo_exact_solution_recomputes_projected_soft_cost() {
    let mut input = String::from("* #variable= 16 #constraint= 16\nsoft: 1000000 ;\n");
    for var in 1..=16 {
        input.push_str(&format!("[1] +1 x{var} >= 1 ;\n"));
    }
    let ParsedPbInstance::Wbo(wbo) =
        parse_instance_interruptible(PbInputFormat::Wbo, &input, || false)
            .expect("WBO should parse")
    else {
        panic!("expected WBO instance");
    };

    let translated_assignment = vec![true; 32];
    let exact = exact_wbo_solution_from_assignment(
        &wbo,
        PbStatus::Satisfiable,
        &translated_assignment,
        Some(136),
    );

    assert_eq!(exact.assignment.len(), 16);
    assert_eq!(exact.objective, Some(0));
}

#[test]
fn test_wbo_unsatisfiable_soft_constraint() {
    // WBO: hard constraint x1 >= 1 AND ~x1 >= 1 (impossible for soft to matter)
    // Actually: hard: x1 >= 1, hard: -1 x1 >= 0 means x1 <= 0
    // That's UNSAT for the hard constraints alone.
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "soft: 10 ;\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n[1] +1 x2 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s UNSATISFIABLE"),
        "Expected UNSATISFIABLE, got: {rendered}"
    );
}

#[test]
fn test_native_solver_satisfiable() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 3 #constraint= 2\n+1 x1 +1 x2 >= 1 ;\n+1 x2 +1 x3 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: true,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s SATISFIABLE"),
        "Expected SATISFIABLE with --native, got: {rendered}"
    );
    assert!(rendered.contains("v "), "Expected variable assignment line");
}

#[test]
fn test_native_solver_nonlinear_linearizes_before_solving() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 4 #constraint= 3\n\
             +1 x1 x2 +1 x3 x4 >= 1 ;\n\
             +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
             +1 ~x1 +1 ~x4 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: true,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s SATISFIABLE"),
        "Expected SATISFIABLE with --native after non-linear linearization, got: {rendered}"
    );
    assert!(
        rendered.contains("v "),
        "Expected projected variable assignment line"
    );
}

#[test]
fn test_proof_mode_nonlinear_fails_closed() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 2 #constraint= 1\n+1 x1 x2 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: Some(proof.path().to_path_buf()),
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s UNSUPPORTED"),
        "Expected UNSUPPORTED proof-mode answer for non-linear PB, got: {rendered}"
    );
}

fn decompressed_repo_xz_fixture(relative_path: &str) -> Option<NamedTempFile> {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let path = repo_root.join(relative_path);
    if !path.exists() {
        return None;
    }
    let output = std::process::Command::new("xz")
        .arg("-dc")
        .arg(&path)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let file = NamedTempFile::new().ok()?;
    fs::write(file.path(), output.stdout).ok()?;
    Some(file)
}

fn assert_proof_mode_no_cert_fixture_fails_closed(relative_path: &str, name: &str) {
    let Some(file) = decompressed_repo_xz_fixture(relative_path) else {
        eprintln!("skipping {name} proof-mode fail-closed test; fixture unavailable");
        return;
    };
    assert_proof_mode_no_cert_path_fails_closed(file.path(), name);
}

fn assert_proof_mode_no_cert_fixture_raw_drift_fails_closed(relative_path: &str, name: &str) {
    let Some(file) = decompressed_repo_xz_fixture(relative_path) else {
        eprintln!("skipping {name} proof-mode raw-drift fail-closed test; fixture unavailable");
        return;
    };
    let mut text =
        fs::read_to_string(file.path()).expect("decompressed OPB fixture should be UTF-8");
    text.push_str("\n* ay raw-SHA drift regression comment\n");
    fs::write(file.path(), text).expect("drifted OPB fixture should be writable");
    assert_proof_mode_no_cert_path_fails_closed(file.path(), name);
}

fn assert_proof_mode_no_cert_env_fixture_fails_closed(env_key: &str, name: &str) {
    let Some(path) = std::env::var_os(env_key) else {
        eprintln!("skipping {name} proof-mode fail-closed test; set {env_key}=<plain OPB>");
        return;
    };
    assert_proof_mode_no_cert_path_fails_closed(Path::new(&path), name);
}

fn assert_proof_mode_no_cert_path_fails_closed(file_path: &Path, name: &str) {
    let proof_dir = tempdir().expect("proof temp dir should exist");
    let proof_path = proof_dir.path().join("proof.out");
    fs::write(&proof_path, b"stale proof sidecar").expect("stale proof sidecar should be writable");
    let cmd = PbCommand::Solve {
        file: file_path.to_path_buf(),
        timeout: Some(5000),
        proof: Some(proof_path.clone()),
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s UNSUPPORTED"),
        "Expected UNSUPPORTED proof-mode answer for no-cert UNSAT recognizer, got: {rendered}"
    );
    assert!(
        !rendered.contains("OPTIMUM FOUND"),
        "{name} no-certificate proof-mode route must not claim an optimum: {rendered}"
    );
    assert!(
        !proof_path.exists(),
        "{name} no-certificate route must clear stale proof sidecars and leave no proof sidecar"
    );
}

#[test]
fn test_proof_mode_poolball_no_cert_unsat_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/wallon/normalized-PoolBallTriangle-07_c24.opb.xz",
            "poolball",
        );
}

#[test]
fn test_proof_mode_koops_triangular_no_cert_unsat_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/koops/normalized-mat11_9_triangular.opb.xz",
            "koops-mat11-9-triangular",
        );
}

#[test]
fn test_proof_mode_flexray_no_cert_unsat_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
        "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/flexray/normalized-fx63.opb.xz",
        "flexray-fx63",
    );
    assert_proof_mode_no_cert_fixture_fails_closed(
        "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/flexray/normalized-fx97.opb.xz",
        "flexray-fx97",
    );
}

#[test]
fn test_proof_mode_dobutsu_noopt_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/sakai/dobutsu-shogi-master-PB25-20250424/normalized-dobutsu-shogi-master-noopt.opb.xz",
            "dobutsu-noopt",
        );
}

#[test]
fn test_proof_mode_dobutsu_raw_drift_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_fixture_raw_drift_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/sakai/dobutsu-shogi-master-PB25-20250424/normalized-dobutsu-shogi-master.opb.xz",
            "dobutsu-master-raw-drift",
        );
    assert_proof_mode_no_cert_fixture_raw_drift_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/sakai/dobutsu-shogi-master-PB25-20250424/normalized-dobutsu-shogi-master-noopt.opb.xz",
            "dobutsu-noopt-raw-drift",
        );
}

#[test]
fn test_proof_mode_cargo_10_15966f_2060_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_env_fixture_fails_closed("AY_PB_CARGO10_OPB", "cargo-10-15966f-2060");
}

#[test]
fn test_proof_mode_scpm1_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_env_fixture_fails_closed("AY_PB_SCPM1_OPB", "scpm1");
}

#[test]
fn test_proof_mode_dominating_set_hexgrid_r6_c60_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_env_fixture_fails_closed(
        "AY_PB_DOMINATING_SET_HEXGRID_R6_C60_OPB",
        "dominating-set-hexgrid-r6-c60",
    );
}

#[test]
fn test_proof_mode_maxcut90_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_env_fixture_fails_closed("AY_PB_MAXCUT90_OPB", "maxcut90");
}

#[test]
fn test_proof_mode_testscheduling_t050_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_env_fixture_fails_closed(
        "AY_PB_TESTSCHEDULING_T050_OPB",
        "testscheduling-t050",
    );
}

#[test]
fn test_proof_mode_fool_solitaire_table_2_0_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/wallon/normalized-FoolSolitaire-table-2-0_c24.opb.xz",
            "fool-solitaire-table-2-0",
        );
}

#[test]
fn test_proof_mode_same_queens_knights_b35_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/wallon/normalized-SameQueensKnights-b-35_c24.opb.xz",
            "same-queens-knights-b35",
        );
}

#[test]
fn test_proof_mode_average_avoiding_mini40_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/wallon/normalized-AverageAvoiding-mini-40_c24.opb.xz",
            "average-avoiding-mini40",
        );
}

#[test]
fn test_proof_mode_solitaire_pattern_table_3_3_9_no_cert_incumbent_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/wallon/normalized-SolitairePattern-table-3-3-9.opb.xz",
            "solitaire-pattern-table-3-3-9",
        );
}

#[test]
fn test_proof_mode_feature_subscription_50_250_no_cert_optimum_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-250-false-45-90-4-1000opt.opb.xz",
            "feature-subscription-50-250",
        );
}

#[test]
fn test_proof_mode_feature_subscription_50_750_no_cert_optimum_fails_closed_or_reports_missing() {
    for (name, path) in [
            (
                "feature-subscription-50-750-2000",
                "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-750-false-45-90-4-2000opt.opb.xz",
            ),
            (
                "feature-subscription-50-750-3000",
                "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-750-false-45-90-4-3000opt.opb.xz",
            ),
            (
                "feature-subscription-50-750-8000",
                "benchmarks/pb-comp/PB24/normalized-PB09/OPT-LIN/featureSubscription/normalized-50-750-false-45-90-4-8000opt.opb.xz",
            ),
        ] {
            assert_proof_mode_no_cert_fixture_fails_closed(path, name);
        }
}

#[test]
fn test_proof_mode_haplotype_no_cert_optimum_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB24/normalized-PB06/OPT-LIN/submitted-PB06/manquiho/haplotype/normalized-simp-unif-100_100.00.opb.xz",
            "haplotype-unif-100-100-00",
        );
}

#[test]
fn test_proof_mode_charlotte_routing_no_cert_optimum_fails_closed() {
    assert_proof_mode_no_cert_fixture_fails_closed(
            "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/wallon/normalized-Charlotte-06-2_c24.opb.xz",
            "charlotte-06-2",
        );
}

#[test]
fn test_proof_mode_testscheduling_t030_certified_optimum() {
    let Some(path) = std::env::var_os("AY_PB_TESTSCHEDULING_T030_OPB") else {
        eprintln!(
                "skipping TestScheduling t030 certified proof test; set AY_PB_TESTSCHEDULING_T030_OPB=<plain normalized-TestScheduling-t030m10r05-1_c24.opb>"
            );
        return;
    };
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    let cmd = PbCommand::Solve {
        file: Path::new(&path).to_path_buf(),
        timeout: Some(5000),
        proof: Some(proof.path().to_path_buf()),
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("o 1986\ns OPTIMUM FOUND"),
        "Expected certified OPTIMUM FOUND with objective 1986, got: {rendered}"
    );
    assert!(
        rendered.contains(
            "certified TestScheduling-t030m10r05-1 proof matched exact input fingerprint"
        ),
        "expected certified route comment, got: {rendered}"
    );

    let mut proof_file = File::open(proof.path()).expect("certified t030 proof should be written");
    let proof_len = proof_file
        .metadata()
        .expect("certified t030 proof metadata should be readable")
        .len();
    let tail_len = proof_len.min(4096) as usize;
    proof_file
        .seek(io::SeekFrom::End(-(tail_len as i64)))
        .expect("certified t030 proof tail should be seekable");
    let mut proof_tail = String::new();
    proof_file
        .read_to_string(&mut proof_tail)
        .expect("certified t030 proof tail should be utf-8");
    assert!(
        proof_tail.contains("conclusion BOUNDS 1986"),
        "certified t030 proof should conclude the optimum bound, tail: {proof_tail}"
    );
    assert!(
        proof_tail.contains("end pseudo-Boolean proof;"),
        "certified t030 proof should be complete, tail: {proof_tail}"
    );
}

fn assert_proof_mode_koops_identity_complement_certifies_unsat(
    relative_path: &str,
    expected_final_id: u64,
) {
    let Some(file) = decompressed_repo_xz_fixture(relative_path) else {
        eprintln!("skipping Koops proof-mode certified test; fixture unavailable");
        return;
    };
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: Some(proof.path().to_path_buf()),
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s UNSATISFIABLE"),
        "Expected UNSATISFIABLE proof-mode answer for certified Koops row, got: {rendered}"
    );
    let proof_text =
        fs::read_to_string(proof.path()).expect("certified Koops proof should be written");
    assert!(
            proof_text.contains(&format!("conclusion UNSAT : {expected_final_id};")),
            "certified Koops proof should conclude on the checked contradiction ID {expected_final_id}: {proof_text}"
        );
}

#[test]
fn test_proof_mode_koops_small_identity_complement_rows_certify_unsat() {
    assert_proof_mode_koops_identity_complement_certifies_unsat(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/koops/normalized-mat98_identity_complement.opb.xz",
            11_553,
        );
    assert_proof_mode_koops_identity_complement_certifies_unsat(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/koops/normalized-mat10_9identity_complement.opb.xz",
            19_882,
        );
}

#[test]
fn test_proof_mode_koops_mat12_11_identity_complement_certifies_unsat() {
    assert_proof_mode_koops_identity_complement_certifies_unsat(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/koops/normalized-mat12_11_identity_complement.opb.xz",
            50_865,
        );
}

#[test]
fn test_proof_mode_koops_mat16_15_identity_complement_certifies_unsat() {
    assert_proof_mode_koops_identity_complement_certifies_unsat(
            "benchmarks/pb-comp/PB25/normalized-PB25/DEC-LIN/koops/normalized-mat16_15_identity_complement.opb.xz",
            408_426,
        );
}

#[test]
fn test_native_solver_unsatisfiable() {
    let file = NamedTempFile::new().expect("temp file should exist");
    // x1 >= 1 AND ~x1 >= 1 is UNSAT.
    fs::write(
        file.path(),
        "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: true,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s UNSATISFIABLE"),
        "Expected UNSATISFIABLE with --native, got: {rendered}"
    );
}

#[test]
fn test_native_solver_cardinality() {
    let file = NamedTempFile::new().expect("temp file should exist");
    // Exactly 3 of 5 variables must be true.
    fs::write(
        file.path(),
        "* #variable= 5 #constraint= 2\n\
             +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 >= 3 ;\n\
             -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 >= -3 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: true,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s SATISFIABLE"),
        "Expected SATISFIABLE with --native for cardinality, got: {rendered}"
    );
}

#[test]
fn test_native_solver_optimization_falls_back() {
    // With --native and an optimization problem, the optimization engine
    // (SAT encoding) should still work since native is only for decision.
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: None,
        stats: false,
        stats_json: false,
        native: true,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s OPTIMUM FOUND"),
        "Expected OPTIMUM FOUND even with --native for optimization, got: {rendered}"
    );
    assert!(
        rendered.contains("o 1"),
        "Expected objective value 1, got: {rendered}"
    );
}

#[test]
fn test_run_with_writer_proof_mode_respects_zero_timeout() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    fs::write(file.path(), "* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n")
        .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(0),
        proof: Some(proof.path().to_path_buf()),
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("s UNKNOWN"),
        "proof mode must respect timeout and return UNKNOWN, got: {rendered}"
    );
}

#[test]
fn test_run_with_writer_proof_mode_clique_writes_conflict_row_map_sidecar() {
    let input = concat!(
        "* #variable= 3 #constraint= 2\n",
        "min: -1 x2 -1 x3 ;\n",
        "+1 x1 >= 1 ;\n",
        "-1 x2 -1 x3 >= -1 ;\n",
    );
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    fs::write(file.path(), input).expect("write should succeed");
    let sidecar_path = clique_conflict_row_import_map_sidecar_path(proof.path());
    let _ = fs::remove_file(&sidecar_path);

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5000),
        proof: Some(proof.path().to_path_buf()),
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");
    let rendered = String::from_utf8(output).expect("output should be utf-8");
    let sidecar = fs::read_to_string(&sidecar_path)
        .expect("clique conflict row/import sidecar should be committed");

    assert_eq!(status, PbStatus::OptimumFound);
    assert!(proof.path().exists(), "completed proof should be committed");
    assert!(
        rendered.contains("clique conflict row/import map sidecar:"),
        "sidecar comment missing, got: {rendered}"
    );
    assert!(sidecar.contains(
            "2,4,2,2,3,0,1,c15e224da5943ff11a3c8ea9524d4b2bf6c456d7b8a63e3ab6c795409be2bc25,-1 x2 -1 x3 >= -1 ;"
        ));

    let _ = fs::remove_file(&sidecar_path);
}

#[test]
fn test_run_with_writer_timeout_applies_during_parse() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(file.path(), "* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n")
        .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(0),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    run_with_writer(&cmd, &mut output).expect("command should succeed");

    let rendered = String::from_utf8(output).expect("output should be utf-8");
    assert!(
        rendered.contains("c timeout or termination during PB parse\n"),
        "parse-time timeout comment missing, got: {rendered}"
    );
    assert!(
        rendered.contains("s UNKNOWN"),
        "zero-timeout parse must return UNKNOWN, got: {rendered}"
    );
}

#[test]
fn test_read_reader_interruptible_stops_mid_file() {
    let mut reader = ChunkReader {
        chunks: vec![b"* #variable= 1\n", b"+1 x1 >= 1 ;\n"],
        index: 0,
    };
    let mut polls = 0;

    let result = read_reader_interruptible(&mut reader, 0, &mut || {
        polls += 1;
        polls >= 2
    })
    .expect("reader should not fail");

    assert!(result.is_none(), "expected interruptible read to stop");
}

#[test]
fn test_read_reader_interruptible_returns_raw_invalid_utf8_bytes() {
    let mut reader = ChunkReader {
        chunks: vec![b"* #variable= 1\n", &[0xff, b'\n']],
        index: 0,
    };
    let mut polls = 0;

    let result = read_reader_interruptible(&mut reader, 0, &mut || {
        polls += 1;
        false
    })
    .expect("reader should not fail")
    .expect("reader should produce bytes");

    assert!(polls > 0);
    assert_eq!(result, b"* #variable= 1\n\xff\n");
}

#[test]
fn test_solve_pb_optimization_respects_budget_consumed_by_parse() {
    let instance = ParsedPbInstance::Opb(Arc::new(PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![ay_pb::PbConstraint {
            terms: vec![ay_pb::PbTerm {
                coeff: 1,
                lits: vec![ay_pb::PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
            rel: ay_pb::PbRel::Ge,
            rhs: 1,
        }],
        objective: Some(ay_pb::PbObjective {
            terms: vec![ay_pb::PbTerm {
                coeff: 1,
                lits: vec![ay_pb::PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        }),
    }));
    let term_flag = AtomicBool::new(false);
    let best_solution = Mutex::new(None);
    let mut output = Vec::new();
    let mut out = PbOutputWriter::new(&mut output);

    let expired_start = std::time::Instant::now()
        .checked_sub(std::time::Duration::from_millis(10))
        .unwrap();
    let solution = solve_pb(
        &instance,
        None,
        Some(1),
        expired_start,
        false,
        false,
        &term_flag,
        &mut out,
        &best_solution,
        None,
    )
    .expect("solve should succeed");

    assert_eq!(solution.solution.status, PbStatus::Unknown);
    assert!(solution.solution.assignment.is_empty());
    assert!(solution.solution.objective.is_none());
    assert!(
        output.is_empty(),
        "solve_pb should not emit output directly"
    );
}

#[test]
fn test_solve_opb_proof_mode_respects_termination_flag() {
    let instance = Arc::new(
        ay_pb::parse_opb("* #variable= 1 #constraint= 1\n+1 x1 >= 1 ;\n")
            .expect("parse should succeed"),
    );
    let term_flag = AtomicBool::new(true);
    let best_solution = Mutex::new(None);
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    let mut output = Vec::new();
    let mut writer = PbOutputWriter::new(&mut output);

    let solution = solve_opb(
        &instance,
        Some(proof.path()),
        Some(5000),
        std::time::Instant::now(),
        false,
        false,
        &term_flag,
        &mut writer,
        &best_solution,
        None,
        None,
    )
    .expect("proof solve should succeed");

    assert_eq!(solution.solution.status, PbStatus::Unknown);
}

#[test]
fn test_proof_mode_optimization_interruption_removes_stale_sidecar() {
    let instance = ay_pb::parse_opb(concat!(
        "* #variable= 2 #constraint= 1\n",
        "min: +1 x1 +1 x2 ;\n",
        "+1 x1 +1 x2 >= 1 ;\n",
    ))
    .map(Arc::new)
    .expect("optimization fixture should parse");
    let term_flag = AtomicBool::new(true);
    let best_solution = Mutex::new(Some(PbExactSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![true, false],
        objective: Some(1),
    }));
    let proof = NamedTempFile::new().expect("proof temp file should exist");
    let sidecar_path = clique_conflict_row_import_map_sidecar_path(proof.path());
    fs::write(proof.path(), "stale proof").expect("stale proof should be writable");
    fs::write(&sidecar_path, "stale conflict row map")
        .expect("stale conflict-row sidecar should be writable");
    let mut output = Vec::new();

    let solution = {
        let mut writer = PbOutputWriter::new(&mut output);
        solve_opb(
            &instance,
            Some(proof.path()),
            Some(5000),
            std::time::Instant::now(),
            false,
            false,
            &term_flag,
            &mut writer,
            &best_solution,
            None,
            None,
        )
        .expect("proof-mode interrupted optimization should fail closed cleanly")
    };

    assert_eq!(solution.solution.status, PbStatus::Unknown);
    assert!(solution.solution.assignment.is_empty());
    assert!(solution.solution.objective.is_none());
    assert!(
        !proof.path().exists(),
        "incomplete proof sidecar must be removed"
    );
    assert!(
        !sidecar_path.exists(),
        "incomplete proof cleanup must remove stale conflict-row sidecars"
    );
    assert!(
        output.is_empty(),
        "solve_opb should not emit stale incumbent output directly"
    );
    // PROOF-TO-SCORE: cached feasible incumbents survive an unproven proof-mode
    // solve so the emission boundary can flush them as s SATISFIABLE (after its
    // fail-closed re-verification). Clearing them here used to collapse the
    // certified build to s UNKNOWN on every instance it could not prove in
    // budget.
    let cached = best_solution
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone();
    assert_eq!(
        cached.as_ref().map(|solution| solution.status),
        Some(PbStatus::Satisfiable),
        "incomplete proof-mode optimization must keep the cached incumbent"
    );

    let mut writer = PbOutputWriter::new(&mut output);
    let status = write_result_or_best_known(&mut writer, &solution.solution, true, &best_solution)
        .expect("flushed incumbent should render");
    let rendered = String::from_utf8(output).expect("output should be utf-8");

    assert_eq!(status, PbStatus::Satisfiable);
    assert!(rendered.contains("s SATISFIABLE\n"));
    assert!(rendered.contains("v x1 -x2"));
    assert!(!rendered.contains("o "), "flush must not duplicate o lines");
}

// --- EARLY self-checked structural-UNSAT recognizers (wf-port-cmdpb) ---------

/// A standard pigeonhole OPB: `pigeons` pigeons into `pigeons - 1` holes. Every
/// pigeon occupies at least one hole (`>= 1`), no hole holds two pigeons
/// (`-1 ... >= -1`, i.e. at most one). UNSAT by counting; the native CDCL path
/// has no short refutation, so a non-trivial size times out unless the early
/// structural recognizer fires.
fn pigeonhole_opb(pigeons: usize) -> String {
    let holes = pigeons - 1;
    let var = |pig: usize, hole: usize| (pig - 1) * holes + hole; // 1-based
    let mut rows = Vec::new();
    for pig in 1..=pigeons {
        let lits: Vec<String> = (1..=holes)
            .map(|h| format!("+1 x{}", var(pig, h)))
            .collect();
        rows.push(format!("{} >= 1 ;", lits.join(" ")));
    }
    for hole in 1..=holes {
        let lits: Vec<String> = (1..=pigeons)
            .map(|p| format!("-1 x{}", var(p, hole)))
            .collect();
        rows.push(format!("{} >= -1 ;", lits.join(" ")));
    }
    let header = format!(
        "* #variable= {} #constraint= {}\n",
        pigeons * holes,
        rows.len()
    );
    format!("{header}{}\n", rows.join("\n"))
}

/// SOUNDNESS pin: the early recognizer set must DECLINE (return `false`) on a
/// satisfiable instance — so a SAT instance can NEVER be flipped to UNSAT — and
/// must ACCEPT a genuine self-checkable pigeonhole refutation.
#[test]
fn early_structural_check_declines_sat_accepts_pigeonhole() {
    let sat = ay_pb::parse_opb("* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n")
        .expect("sat fixture should parse");
    assert!(
        !structural_unsat_self_checked(&sat),
        "structural recognizers must DECLINE a satisfiable instance (no SAT->UNSAT flip)"
    );

    let unsat = ay_pb::parse_opb(&pigeonhole_opb(6)).expect("pigeonhole fixture should parse");
    assert!(
        structural_unsat_self_checked(&unsat),
        "structural recognizers must accept a self-checkable pigeonhole refutation"
    );
}

/// The pre-search row-count gate is fail-closed: above the cap the recognizer
/// pass declines (skips straight to search) instead of paying full-row scans
/// that can never certify at that size; below the cap behavior is unchanged.
#[test]
fn structural_precheck_row_gate_is_fail_closed() {
    let unsat = ay_pb::parse_opb(&pigeonhole_opb(6)).expect("pigeonhole fixture should parse");
    assert!(
        structural_unsat_self_checked_with_cap(&unsat, STRUCTURAL_PRECHECK_MAX_ROWS),
        "below the cap the recognizer pass must still certify pigeonhole UNSAT"
    );
    let rows = unsat.constraints.len();
    assert!(
        rows > 1,
        "fixture must have enough rows to exceed a tiny cap"
    );
    assert!(
        !structural_unsat_self_checked_with_cap(&unsat, rows - 1),
        "above the cap the pass must decline (skip straight to search)"
    );
}

/// REGRESSION (the wf-port-cmdpb fix): a NATIVE LINEAR DECISION pigeonhole
/// instance must be decided `s UNSATISFIABLE` by the EARLY self-checked structural
/// recognizer in the MAIN `ay` CLI — *before* the full-timeout `solve_decision_*`
/// path. The tiny 750ms timeout is the point: the native CDCL solve has no short
/// PHP refutation and would consume the whole budget and report `s UNKNOWN`, so
/// this test fails closed if the early check is ever removed or moved back after
/// the native/portfolio solve. Goes through the full CLI path (`run_with_writer`).
#[test]
fn early_structural_check_decides_pigeonhole_unsat_via_cli() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(file.path(), pigeonhole_opb(20)).expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(750),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");
    let rendered = String::from_utf8(output).expect("output should be utf-8");

    assert_eq!(
        status,
        PbStatus::Unsatisfiable,
        "early structural recognizer must decide pigeonhole UNSAT inside the tiny budget; got: {rendered}"
    );
    assert!(
        rendered.contains("s UNSATISFIABLE"),
        "Expected s UNSATISFIABLE, got: {rendered}"
    );
    assert!(
        !rendered.contains("v "),
        "an UNSAT verdict must not emit a model line"
    );
}

/// ZERO-REGRESSION pin (companion to the UNSAT regression above): a genuinely
/// satisfiable decision instance must still solve to `s SATISFIABLE` through the
/// same CLI path — the early structural check must not steal the verdict.
#[test]
fn early_structural_check_leaves_satisfiable_decision_untouched() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 4 #constraint= 2\n+1 x1 +1 x2 >= 1 ;\n+1 x3 +1 x4 >= 1 ;\n",
    )
    .expect("write should succeed");

    let cmd = PbCommand::Solve {
        file: file.path().to_path_buf(),
        timeout: Some(5_000),
        proof: None,
        stats: false,
        stats_json: false,
        native: false,
        ab_switches: Default::default(),
    };
    let mut output = Vec::new();
    let status = run_with_writer(&cmd, &mut output).expect("command should succeed");
    let rendered = String::from_utf8(output).expect("output should be utf-8");

    assert_eq!(
        status,
        PbStatus::Satisfiable,
        "satisfiable decision instance must not be flipped by the early check; got: {rendered}"
    );
    assert!(
        rendered.contains("s SATISFIABLE"),
        "Expected s SATISFIABLE, got: {rendered}"
    );
}

// =====================================================================
// DECISION-SAT Verified-SAT-Gate (`decision_sat_self_checked`) — the
// decision-track analogue of the optimization incumbent VIG. SOUNDNESS:
// a SAT model that fails re-verification against the ORIGINAL constraints
// is downgraded to UNKNOWN (fail-closed), never a wrong `s SATISFIABLE`.
// 0-REGRESSION: a model that DOES verify is returned unchanged.
// =====================================================================

/// `x1 + x2 >= 1` over 2 vars, no objective (a decision instance).
fn decision_sat_gate_instance() -> PbInstance {
    PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![ay_pb::PbConstraint {
            terms: vec![
                ay_pb::PbTerm {
                    coeff: 1,
                    lits: vec![ay_pb::PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                ay_pb::PbTerm {
                    coeff: 1,
                    lits: vec![ay_pb::PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
            rel: ay_pb::PbRel::Ge,
            rhs: 1,
        }],
        objective: None,
    }
}

#[test]
fn decision_sat_gate_keeps_feasible_model_satisfiable() {
    // 0-REGRESSION: x1=true satisfies `x1 + x2 >= 1`, so the gate must pass the
    // verdict through UNCHANGED (no false UNKNOWN on a valid model).
    let instance = decision_sat_gate_instance();
    let solution = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![true, false],
        objective: None,
    };

    let gated = decision_sat_self_checked(solution.clone(), &instance);

    assert_eq!(gated.status, PbStatus::Satisfiable);
    assert_eq!(gated.assignment, vec![true, false]);
}

#[test]
fn decision_sat_gate_fails_closed_on_infeasible_model() {
    // SOUNDNESS: x1=false, x2=false violates `x1 + x2 >= 1`. A core-solver bug
    // that returned this model as SAT must be caught — the gate downgrades it to
    // UNKNOWN, never emitting a wrong `s SATISFIABLE`.
    let instance = decision_sat_gate_instance();
    let wrong = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![false, false],
        objective: None,
    };

    let gated = decision_sat_self_checked(wrong, &instance);

    assert_eq!(
        gated.status,
        PbStatus::Unknown,
        "an infeasible model claimed SAT must fail-closed to UNKNOWN"
    );
    assert!(gated.assignment.is_empty());
    assert_eq!(gated.objective, None);
}

#[test]
fn decision_sat_gate_fails_closed_on_short_model() {
    // A truncated/empty model cannot satisfy the constraint (out-of-range vars
    // evaluate to false): fail-closed to UNKNOWN rather than a wrong SAT.
    let instance = decision_sat_gate_instance();
    let wrong = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: Vec::new(),
        objective: None,
    };

    let gated = decision_sat_self_checked(wrong, &instance);

    assert_eq!(gated.status, PbStatus::Unknown);
}

#[test]
fn decision_sat_gate_passes_through_non_sat_verdicts() {
    // The gate ONLY guards `Satisfiable`. UNSAT/UNKNOWN must pass through
    // untouched — a refutation admits no model to re-verify, and downgrading it
    // would be a regression, not a soundness gain.
    let instance = decision_sat_gate_instance();

    let unsat = PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: Vec::new(),
        objective: None,
    };
    assert_eq!(
        decision_sat_self_checked(unsat, &instance).status,
        PbStatus::Unsatisfiable
    );

    let unknown = PbSolution {
        status: PbStatus::Unknown,
        assignment: Vec::new(),
        objective: None,
    };
    assert_eq!(
        decision_sat_self_checked(unknown, &instance).status,
        PbStatus::Unknown
    );
}
