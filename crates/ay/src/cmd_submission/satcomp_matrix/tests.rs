//! Unit tests for `super` (satcomp_matrix.rs).
//! Extracted verbatim to keep the production module readable.

use super::*;

struct EvidenceFixture {
    _dir: tempfile::TempDir,
    scoreboard: PathBuf,
    current_stats: PathBuf,
}

struct FmlaPostcheckFixture {
    _dir: tempfile::TempDir,
    solver_root: PathBuf,
    case_dir: PathBuf,
    cnf: PathBuf,
    proof: PathBuf,
    external: ProofEvidence,
    args_log: PathBuf,
}

impl FmlaPostcheckFixture {
    fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let solver_root = dir.path().join("solver");
        let case_dir = dir.path().join("case");
        fs::create_dir_all(&solver_root).unwrap();
        fs::create_dir_all(&case_dir).unwrap();
        let args_log = dir.path().join("fake-ay-args.jsonl");
        write_fake_fmla_postcheck_ay(&solver_root, &args_log);
        let cnf = case_dir.join("FmlaEquivChain_4_6_6.cnf");
        let proof = case_dir.join("proof.out");
        fs::write(&cnf, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
        fs::write(&proof, "stub proof\n").unwrap();
        let checker = case_dir.join("cake_lpr");
        fs::write(&checker, "checker\n").unwrap();
        let run = ExternalCheckerRunEvidence {
            checker_path: checker.clone(),
            checker_argv: vec![
                path_string(&checker),
                path_string(&cnf),
                path_string(&proof),
            ],
            checker_exit_code: 0,
            checker_stdout: "s VERIFIED UNSAT\n".to_string(),
            checker_stderr: "c checker comment\n".to_string(),
        };
        let mut external = ProofEvidence::default();
        write_external_checker_artifact(&cnf, &proof, &run, &mut external).unwrap();
        external.proof_status = "valid".to_string();
        external.ay_lrat_status = "ok".to_string();
        external.proof_checker_status = "ok".to_string();
        Self {
            _dir: dir,
            solver_root,
            case_dir,
            cnf,
            proof,
            external,
            args_log,
        }
    }
}

fn write_fake_fmla_postcheck_ay(solver_root: &Path, args_log: &Path) {
    let ay = solver_root.join("ay");
    let args_log_json = serde_json::to_string(&path_string(args_log)).unwrap();
    fs::write(
            &ay,
            format!(
                r#"#!/usr/bin/env python3
import hashlib
import json
import os
import sys

args_log = {args_log_json}
args = sys.argv[1:]
with open(args_log, "a", encoding="utf-8") as handle:
    handle.write(json.dumps(args) + "\n")

if args[:2] != ["check", "fmla-postcheck-admission"]:
    sys.exit(2)

def value_after(flag):
    return args[args.index(flag) + 1]

replay_artifact = value_after("--replay-artifact")
summary_tsv = value_after("--summary-tsv")
proof_out = value_after("--proof-out")
external_artifact = value_after("--external-checker-artifact")
external_artifact_sha256 = value_after("--external-checker-artifact-sha256")
os.makedirs(os.path.dirname(replay_artifact), exist_ok=True)
with open(proof_out, "rb") as handle:
    proof_sha = hashlib.sha256(handle.read()).hexdigest()
with open(external_artifact, "r", encoding="utf-8") as handle:
    checker_artifact = json.load(handle)
payload = {{
    "schema": "ay.fmla-main-lrat-postcheck-admission-replay/v1",
    "status": "committed_checker_backed_admission",
    "proof_obligation_rows": 2,
    "external_proof_checker_verdict_artifact_rows": 2,
    "external_proof_checker_verdict_artifact": external_artifact,
    "external_proof_checker_verdict_artifact_sha256": external_artifact_sha256,
    "external_proof_checker_verdict_artifact_schema": "ay.fmla-main-lrat-external-checker-verdict/v1",
    "external_proof_checker_verdict_artifact_runtime_field": "external_proof_checker_verdict_artifact",
    "post_replay_preprocess_tx_committed": 0,
    "learned_lrat_main_proof_authority_status": "authorized",
    "learned_lrat_main_proof_authority_external_checker_verified": True,
    "learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment": True,
    "learned_lrat_main_proof_authority_authorizes_main_proof_out": True,
    "external_proof_checker_verdict": "VERIFIED_UNSAT",
    "external_proof_checker_path": checker_artifact["checker_path"],
    "external_proof_checker_sha256": checker_artifact["checker_sha256"],
    "external_proof_checker_command": checker_artifact["checker_command"],
    "external_proof_checker_argv": checker_artifact["checker_argv"],
    "external_proof_checker_dimacs_path": checker_artifact["checked_dimacs_path"],
    "external_proof_checker_dimacs_sha256": checker_artifact["checked_dimacs_sha256"],
    "checker_exit_code": 0,
    "learned_lrat_main_proof_authority_proof_out_path": proof_out,
    "learned_lrat_main_proof_authority_proof_out_sha256": proof_sha,
}}
with open(replay_artifact, "w", encoding="utf-8") as handle:
    handle.write(json.dumps(payload) + "\n")
with open(replay_artifact, "rb") as handle:
    replay_sha = hashlib.sha256(handle.read()).hexdigest()
with open(summary_tsv, "w", encoding="utf-8") as handle:
    handle.write(
        "committed_checker_backed_admission\t"
        + replay_artifact
        + "\t"
        + replay_sha
        + "\t2\t2\t0\n"
    )
print(json.dumps(payload))
"#
            ),
        )
        .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(&ay).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&ay, permissions).unwrap();
    }
}

fn write_fmla_learned_lrat_dry_run_artifact(path: &Path) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    write_json_pretty(
        path,
        &json!({
            "schema": FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA,
            "retained_fixture": true,
        }),
    )
    .unwrap();
}

fn fmla_postcheck_test_counters() -> BTreeMap<String, String> {
    BTreeMap::from([
        (
            FMLA_MATERIALIZER_ATTEMPTS_COUNTER.to_string(),
            "1".to_string(),
        ),
        (
            FMLA_MATERIALIZER_PROOF_EMIT_RECORDS_SEEN_COUNTER.to_string(),
            "2".to_string(),
        ),
        (
            FMLA_MATERIALIZER_RECORDS_COUNTER.to_string(),
            "2".to_string(),
        ),
        (
            FMLA_MATERIALIZER_FAIL_CLOSED_COUNTER.to_string(),
            "1".to_string(),
        ),
        (
            FMLA_MATERIALIZER_MISSING_RUNTIME_RECORDS_COUNTER.to_string(),
            "0".to_string(),
        ),
        (
            FMLA_PREPROCESS_TX_FAIL_CLOSED_COUNTER.to_string(),
            "1".to_string(),
        ),
        (
            FMLA_PREPROCESS_TX_COMMITTED_COUNTER.to_string(),
            "0".to_string(),
        ),
    ])
}

fn read_fake_ay_args(args_log: &Path) -> Vec<String> {
    let text = fs::read_to_string(args_log).unwrap();
    serde_json::from_str(text.lines().last().expect("fake ay args")).unwrap()
}

#[test]
fn csv_parser_handles_quotes_and_commas() {
    assert_eq!(
        parse_csv_line("local_path,result,family\n").len(),
        3,
        "header fields"
    );
    assert_eq!(
        parse_csv_line("a,\"b,c\",\"d\"\"e\""),
        vec!["a", "b,c", "d\"e"]
    );
}

#[test]
fn official_mirror_limit_requires_allow_smoke() {
    let mut opts = test_run_opts();
    opts.suite = "sat-main-2026-official-mirror".to_string();
    opts.limit = Some(1);
    opts.allow_smoke = false;

    let err = validate_limit_policy(&opts).unwrap_err();
    assert!(
        err.to_string()
            .contains("official mirror gate must not use --limit unless --allow-smoke is set"),
        "{err}"
    );

    opts.allow_smoke = true;
    validate_limit_policy(&opts).unwrap();
}

#[test]
fn proof_checker_output_rejects_mixed_verdict_lines() {
    assert!(proof_checker_output_is_verified(
        "s VERIFIED UNSAT\n",
        "c checker comment\n"
    ));
    assert!(proof_checker_output_is_verified(
        "VERIFIED\n",
        "c VERIFIED\n"
    ));
    assert!(proof_checker_output_is_verified("c VERIFIED\n", ""));
    assert!(proof_checker_output_is_verified(
        "c checker banner\nc VERIFIED\n",
        ""
    ));
    assert!(proof_checker_output_is_verified("s VERIFIED\n", "c\n"));
    assert!(!proof_checker_output_is_verified(
        "s NOT VERIFIED\ns VERIFIED UNSAT\n",
        ""
    ));
    assert!(!proof_checker_output_is_verified(" s VERIFIED UNSAT\n", ""));
    assert!(!proof_checker_output_is_verified("s VERIFIED UNSAT \n", ""));
    assert!(!proof_checker_output_is_verified(
        "s VERIFIED UNSAT\n",
        "cVERIFIED\n"
    ));
}

#[test]
fn external_proof_checker_path_resolves_before_solver_root_chdir() {
    let dir = tempfile::tempdir().unwrap();
    let invocation_cwd = dir.path().join("repo");
    let solver_root = dir.path().join("repo").join("package").join("repo");
    fs::create_dir_all(&solver_root).unwrap();

    let resolved = resolve_external_proof_checker_path(
        "cache/tools/sat26-checkers/bin/cake_lpr",
        &invocation_cwd,
    )
    .expect("external checker path");

    assert_eq!(
        resolved,
        invocation_cwd
            .join("cache")
            .join("tools")
            .join("sat26-checkers")
            .join("bin")
            .join("cake_lpr")
    );
    assert!(
        !resolved.starts_with(&solver_root),
        "relative checker paths must not be re-rooted under packaged solver root"
    );
    assert!(resolve_external_proof_checker_path("none", &invocation_cwd).is_none());
    assert!(resolve_external_proof_checker_path("auto", &invocation_cwd).is_none());
    assert!(resolve_external_proof_checker_path("/tmp/ay", &invocation_cwd).is_none());
}

#[test]
fn official_mirror_suite_loads_manifest_from_root() {
    let dir = tempfile::tempdir().unwrap();
    let suite_dir = dir
        .path()
        .join("benchmarks")
        .join("sat")
        .join("satcomp2026-main");
    fs::create_dir_all(&suite_dir).unwrap();
    let sat = suite_dir.join("tiny-sat.cnf");
    let unsat = suite_dir.join("tiny-unsat.cnf");
    fs::write(&sat, "p cnf 1 1\n1 0\n").unwrap();
    fs::write(&unsat, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
    fs::write(
        suite_dir.join("manifest.csv"),
        format!(
            "local_path,result,family,category\n{},sat,unit,sanity\n{},unsat,unit,sanity\n",
            path_string(&sat),
            path_string(&unsat)
        ),
    )
    .unwrap();

    let mut opts = test_run_opts();
    opts.suite = "sat-main-2026-official-mirror".to_string();
    opts.official_mirror_root = Some(dir.path().to_path_buf());

    let benches = load_benchmarks(&opts).unwrap();
    assert_eq!(benches.len(), 2);
    assert_eq!(benches[0].expected, "sat");
    assert_eq!(benches[1].expected, "unsat");
    check_official_mirror(&opts, &benches).unwrap();
}

#[test]
fn official_mirror_suite_accepts_python_manifest_layouts() {
    for candidate in OFFICIAL_MIRROR_MANIFEST_CANDIDATES {
        let dir = tempfile::tempdir().unwrap();
        let manifest = dir.path().join(candidate);
        let suite_dir = manifest.parent().expect("manifest parent");
        write_manifest_mirror_case(suite_dir, &manifest);

        let opts = official_mirror_test_opts(dir.path());
        let benches = load_benchmarks(&opts).unwrap();

        assert_eq!(
            benches.len(),
            2,
            "layout {candidate} should load both manifest rows"
        );
        assert_eq!(benches[0].expected, "sat");
        assert_eq!(benches[1].expected, "unsat");
        check_official_mirror(&opts, &benches).unwrap();
    }
}

#[test]
fn official_mirror_suite_accepts_python_directory_layouts_recursively() {
    for candidate in OFFICIAL_MIRROR_DIR_CANDIDATES {
        let dir = tempfile::tempdir().unwrap();
        let suite_dir = dir.path().join(candidate);
        write_recursive_directory_mirror_case(&suite_dir);

        let opts = official_mirror_test_opts(dir.path());
        let benches = load_benchmarks(&opts).unwrap();

        assert_eq!(
            benches.len(),
            2,
            "layout {candidate} should recursively load both DIMACS files"
        );
        assert!(
            benches
                .iter()
                .any(|bench| bench.path.ends_with("nested/tiny-unsat.cnf")),
            "layout {candidate} should recurse into nested DIMACS files"
        );
        check_official_mirror(&opts, &benches).unwrap();
    }
}

#[test]
fn official_mirror_suite_discovers_unique_recursive_manifest() {
    let dir = tempfile::tempdir().unwrap();
    let suite_dir = dir
        .path()
        .join("mirror-copy")
        .join("sat")
        .join("2026")
        .join("main");
    let manifest = suite_dir.join("manifest.csv");
    write_manifest_mirror_case(&suite_dir, &manifest);

    let opts = official_mirror_test_opts(dir.path());
    let benches = load_benchmarks(&opts).unwrap();

    assert_eq!(benches.len(), 2);
    assert_eq!(benches[0].family, "unit");
    assert_eq!(benches[1].category, "sanity");
    check_official_mirror(&opts, &benches).unwrap();
}

#[test]
fn filter_family_expresses_official_multiplier_equivalence_gate_rows() {
    let dir = tempfile::tempdir().unwrap();
    let suite_dir = dir
        .path()
        .join("benchmarks")
        .join("sat")
        .join("satcomp2026-main");
    fs::create_dir_all(&suite_dir).unwrap();

    let mut manifest = String::from("local_path,result,family,category\n");
    for idx in 0..12 {
        let path = suite_dir.join(format!("multiplier-equiv-{idx:02}.cnf"));
        fs::write(&path, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
        manifest.push_str(&format!(
            "{},unsat,multiplier-equivalence,crafted\n",
            path_string(&path)
        ));
    }
    let other = suite_dir.join("other-family.cnf");
    fs::write(&other, "p cnf 1 1\n1 0\n").unwrap();
    manifest.push_str(&format!(
        "{},sat,other-family,crafted\n",
        path_string(&other)
    ));
    fs::write(suite_dir.join("manifest.csv"), manifest).unwrap();

    let mut opts = official_mirror_test_opts(dir.path());
    opts.filter_family = vec!["multiplier-equivalence".to_string()];
    opts.require_total = Some(12);

    let mut benches = load_benchmarks(&opts).unwrap();
    apply_benchmark_filters(&opts, &mut benches).unwrap();
    check_official_mirror(&opts, &benches).unwrap();

    assert_eq!(benches.len(), opts.require_total.unwrap());
    assert!(benches
        .iter()
        .all(|bench| bench.family == "multiplier-equivalence"));
}

#[test]
fn summary_counts_wrong_invalid_and_par2() {
    let mut solved = BTreeMap::new();
    insert(&mut solved, "actual", "sat");
    insert(&mut solved, "expected", "sat");
    insert(&mut solved, "model_status", "valid");
    insert(&mut solved, "wrong", "0");
    insert(&mut solved, "invalid", "0");
    insert(&mut solved, "par2_s", "1.25");
    insert(&mut solved, "family", "unit");

    let mut invalid = BTreeMap::new();
    insert(&mut invalid, "actual", "unsat");
    insert(&mut invalid, "expected", "unsat");
    insert(&mut invalid, "proof_status", "valid");
    insert(&mut invalid, "ay_lrat_status", "ok");
    insert(&mut invalid, "proof_checker_status", "ok");
    insert(&mut invalid, "wrong", "0");
    insert(&mut invalid, "invalid", "1");
    insert(&mut invalid, "par2_s", "10");
    insert(&mut invalid, "family", "unit");

    let summary = summarize_records(
        &[Record { fields: solved }, Record { fields: invalid }],
        5.0,
        true,
    );
    assert_eq!(summary.total, 2);
    assert_eq!(summary.solved, 1);
    assert_eq!(summary.expected_sat, 1);
    assert_eq!(summary.expected_unsat, 1);
    assert_eq!(summary.invalid, 1);
    assert_eq!(summary.par2_total, 11.25);
}

#[test]
fn summary_counts_model_and_proof_validity() {
    let rows = [
        evidence_record(&[
            ("actual", "sat"),
            ("expected", "sat"),
            ("model_status", "valid"),
            ("par2_s", "1"),
            ("family", "sat-family"),
        ]),
        evidence_record(&[
            ("actual", "sat"),
            ("expected", "sat"),
            ("model_status", "unchecked"),
            ("par2_s", "2"),
            ("family", "sat-family"),
        ]),
        evidence_record(&[
            ("actual", "unsat"),
            ("expected", "unsat"),
            ("proof_status", "valid"),
            ("ay_lrat_status", "ok"),
            ("proof_checker_status", "ok"),
            ("par2_s", "3"),
            ("family", "unsat-family"),
        ]),
        evidence_record(&[
            ("actual", "unsat"),
            ("expected", "unsat"),
            ("proof_status", "valid"),
            ("ay_lrat_status", "ok"),
            ("proof_checker_status", "unchecked"),
            ("par2_s", "4"),
            ("family", "unsat-family"),
        ]),
    ];

    let summary = summarize_records(&rows, 5.0, true);
    assert_eq!(summary.sat_model_valid, 1);
    assert_eq!(summary.sat_model_invalid, 1);
    assert_eq!(summary.unsat_proof_valid, 1);
    assert_eq!(summary.unsat_proof_invalid, 1);

    let summary_json = summary_json(&summary);
    assert_eq!(summary_json["sat_model_valid"], JsonValue::from(1));
    assert_eq!(summary_json["sat_model_invalid"], JsonValue::from(1));
    assert_eq!(summary_json["unsat_proof_valid"], JsonValue::from(1));
    assert_eq!(summary_json["unsat_proof_invalid"], JsonValue::from(1));
    assert_eq!(
        summary_json["families"]["sat-family"]["sat_model_valid"],
        JsonValue::from(1)
    );
    assert_eq!(
        summary_json["families"]["sat-family"]["sat_model_invalid"],
        JsonValue::from(1)
    );
    assert_eq!(
        summary_json["families"]["unsat-family"]["unsat_proof_valid"],
        JsonValue::from(1)
    );
    assert_eq!(
        summary_json["families"]["unsat-family"]["unsat_proof_invalid"],
        JsonValue::from(1)
    );
}

#[test]
fn status_parser_rejects_duplicate_status_under_strict_gate() {
    let dir = tempfile::tempdir().unwrap();
    let stdout = dir.path().join("stdout.txt");
    fs::write(&stdout, "s SATISFIABLE\ns SATISFIABLE\nv 1 0\n").unwrap();
    let parsed = parse_solver_output_file(&stdout, Some(10), true).unwrap();
    assert_eq!(parsed.actual, "sat");
    assert_eq!(parsed.invalid_reason.as_deref(), Some("duplicate-status"));
    assert!(parsed.has_model_lines);
}

#[test]
fn status_parser_rejects_model_before_status_under_strict_gate() {
    let dir = tempfile::tempdir().unwrap();
    let stdout = dir.path().join("stdout.txt");
    fs::write(&stdout, "v 1 0\ns SATISFIABLE\n").unwrap();
    let parsed = parse_solver_output_file(&stdout, Some(10), true).unwrap();
    assert_eq!(parsed.actual, "sat");
    assert_eq!(
        parsed.invalid_reason.as_deref(),
        Some("model-before-status:1")
    );
    assert!(parsed.has_model_lines);
}

#[test]
fn evidence_summary_emits_current_candidate_packet() {
    let fixture = evidence_fixture(false);
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };
    let payload = build_evidence_summary(&opts, &fixture.scoreboard).unwrap();

    assert_eq!(payload["schema"], STATS_JSON_SCHEMA);
    assert_eq!(
        payload["competition_jit"]["candidate_mode"],
        JsonValue::String("current".to_string())
    );
    assert_eq!(
        payload["competition_jit"]["application_counter"]["value"],
        JsonValue::from(2)
    );
    assert_eq!(payload["totals"]["solved"], JsonValue::from(2));
    assert_eq!(payload["totals"]["wrong_answers"], JsonValue::from(0));
    assert_eq!(payload["totals"]["sat_model_valid"], JsonValue::from(1));
    assert_eq!(payload["totals"]["sat_model_invalid"], JsonValue::from(0));
    assert_eq!(payload["totals"]["unsat_proof_valid"], JsonValue::from(1));
    assert_eq!(payload["totals"]["unsat_proof_invalid"], JsonValue::from(0));
    assert_eq!(
        payload["satcomp_matrix"]["schema_version"],
        SATCOMP_MATRIX_EVIDENCE_SCHEMA
    );
    assert_eq!(
        payload["satcomp_matrix"]["stats_json_count"],
        JsonValue::from(2)
    );
}

#[test]
fn evidence_summary_rejects_limited_scoreboard() {
    let fixture = evidence_fixture(true);
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };
    let err = build_evidence_summary(&opts, &fixture.scoreboard).unwrap_err();
    assert!(err.to_string().contains("must not use --limit"), "{err}");
}

#[test]
fn evidence_summary_accepts_missing_score_bearing_validation_summary_fields() {
    let fixture = evidence_fixture(false);
    let mut scoreboard = load_json_object(&fixture.scoreboard).unwrap();
    scoreboard["variants"]["default"]["summary"]
        .as_object_mut()
        .unwrap()
        .remove("sat_model_valid");
    scoreboard["variants"]["default"]["summary"]
        .as_object_mut()
        .unwrap()
        .remove("unsat_proof_valid");
    write_json_pretty(&fixture.scoreboard, &scoreboard).unwrap();
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };

    let payload = build_evidence_summary(&opts, &fixture.scoreboard).unwrap();
    assert_eq!(payload["totals"]["sat_model_valid"], JsonValue::from(1));
    assert_eq!(payload["totals"]["unsat_proof_valid"], JsonValue::from(1));
}

#[test]
fn evidence_summary_rejects_score_bearing_validation_summary_mismatch() {
    let fixture = evidence_fixture(false);
    let mut scoreboard = load_json_object(&fixture.scoreboard).unwrap();
    scoreboard["variants"]["default"]["summary"]["unsat_proof_valid"] = JsonValue::from(0);
    write_json_pretty(&fixture.scoreboard, &scoreboard).unwrap();
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };

    let err = build_evidence_summary(&opts, &fixture.scoreboard).unwrap_err();
    assert!(
        err.to_string()
            .contains("unsat_proof_valid=0 does not match raw TSV count 1"),
        "{err}"
    );
}

#[test]
fn evidence_summary_rejects_dirty_source_scoreboard() {
    let fixture = evidence_fixture(false);
    let mut scoreboard = load_json_object(&fixture.scoreboard).unwrap();
    scoreboard["source_dirty"] = JsonValue::Bool(true);
    write_json_pretty(&fixture.scoreboard, &scoreboard).unwrap();
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };

    let err = build_evidence_summary(&opts, &fixture.scoreboard).unwrap_err();
    assert!(err.to_string().contains("source_dirty=false"), "{err}");
}

#[test]
fn evidence_summary_rejects_bad_binary_provenance() {
    let fixture = evidence_fixture(false);
    let scoreboard = load_json_object(&fixture.scoreboard).unwrap();
    let raw_tsv = PathBuf::from(
        scoreboard["variants"]["default"]["raw_tsv"]
            .as_str()
            .expect("raw_tsv path"),
    );
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[0].fields, "binary_sha256", &"0".repeat(64));
    insert(&mut rows[0].fields, "ay_sha256", &"0".repeat(64));
    write_raw_tsv(&raw_tsv, &rows).unwrap();
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };

    let err = build_evidence_summary(&opts, &fixture.scoreboard).unwrap_err();
    assert!(err.to_string().contains("binary_sha256 mismatch"), "{err}");
}

#[test]
fn retain_model_checker_artifact_records_checker_command_and_exit() {
    let dir = tempfile::tempdir().unwrap();
    let artifact = dir.path().join(SAT_MODEL_CHECK_ARTIFACT);
    let command = vec![
        "ay".to_string(),
        "check".to_string(),
        "model".to_string(),
        "input.cnf".to_string(),
        "stdout.txt".to_string(),
        "--json".to_string(),
    ];
    let mut evidence = ModelEvidence::default();
    retain_model_checker_artifact(
        &mut evidence,
        &artifact,
        &json!({
            "schema": SAT_MODEL_CHECK_ARTIFACT_SCHEMA,
            "formula": "input.cnf",
            "stdout": "stdout.txt",
            "model_status": "valid",
            "valid": true,
        }),
        &command,
        Some(0),
    )
    .unwrap();

    let payload = load_json_object(&artifact).unwrap();
    assert_eq!(payload["checker_command_json"], json!(command));
    assert_eq!(payload["checker_exit_status"], JsonValue::from(0));
    assert_eq!(evidence.artifact_schema, SAT_MODEL_CHECK_ARTIFACT_SCHEMA);
}

#[test]
fn evidence_summary_rejects_sat_model_artifact_exit_status_drift() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    let artifact = PathBuf::from(rows[0].get("model_checker_artifact"));
    let mut payload = load_json_object(&artifact).unwrap();
    payload["checker_exit_status"] = JsonValue::from(1);
    write_json_pretty(&artifact, &payload).unwrap();
    insert(
        &mut rows[0].fields,
        "model_checker_artifact_sha256",
        &sha256_file(&artifact).unwrap(),
    );
    write_raw_tsv(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    let message = err.to_string();
    assert!(
        message.contains("model_checker_artifact requires checker_exit_status=0"),
        "{message}"
    );
    assert!(
        message.contains("model_checker_artifact checker_exit_status does not match raw TSV"),
        "{message}"
    );
}

#[test]
fn evidence_summary_rejects_sat_model_artifact_command_drift() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    let artifact = PathBuf::from(rows[0].get("model_checker_artifact"));
    let mut payload = load_json_object(&artifact).unwrap();
    let mut command: Vec<String> =
        serde_json::from_str(rows[0].get("model_checker_command_json")).unwrap();
    command[4].push_str(".stale");
    payload["checker_command_json"] = json!(command);
    write_json_pretty(&artifact, &payload).unwrap();
    insert(
        &mut rows[0].fields,
        "model_checker_artifact_sha256",
        &sha256_file(&artifact).unwrap(),
    );
    write_raw_tsv(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    assert!(
        err.to_string()
            .contains("model_checker_artifact checker_command_json does not match raw TSV"),
        "{err}"
    );
}

#[test]
fn evidence_summary_rejects_sat_model_checker_command_extra_args() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    let mut command: Vec<String> =
        serde_json::from_str(rows[0].get("model_checker_command_json")).unwrap();
    command.push("--json".to_string());
    insert(
        &mut rows[0].fields,
        "model_checker_command_json",
        &serde_json::to_string(&command).unwrap(),
    );
    write_raw_tsv(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    assert!(
        err.to_string().contains(
            "model_checker_command_json must invoke ay check model <formula> <stdout> --json"
        ),
        "{err}"
    );
}

#[test]
fn external_checker_artifact_records_checker_command_output_and_hashes() {
    let dir = tempfile::tempdir().unwrap();
    let cnf = dir.path().join("tiny-unsat.cnf");
    let proof = dir.path().join("proof.out");
    let checker = dir.path().join("cake_lpr");
    fs::write(&cnf, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
    fs::write(&proof, "stub proof\n").unwrap();
    fs::write(&checker, "checker\n").unwrap();
    let run = ExternalCheckerRunEvidence {
        checker_path: checker.clone(),
        checker_argv: vec![
            path_string(&checker),
            path_string(&cnf),
            path_string(&proof),
        ],
        checker_exit_code: 0,
        checker_stdout: "s VERIFIED UNSAT\n".to_string(),
        checker_stderr: "c checker comment\n".to_string(),
    };
    let mut evidence = ProofEvidence::default();

    write_external_checker_artifact(&cnf, &proof, &run, &mut evidence).unwrap();

    let payload = load_json_object(&PathBuf::from(&evidence.external_artifact)).unwrap();
    assert_eq!(payload["checker_argv"], json!(run.checker_argv.clone()));
    assert_eq!(
        payload["checker_command"],
        JsonValue::String(shell_join(&run.checker_argv))
    );
    assert_eq!(payload["checker_exit_code"], JsonValue::from(0));
    assert_eq!(payload["checker_stdout"], "s VERIFIED UNSAT\n");
    assert_eq!(payload["checker_stderr"], "c checker comment\n");
    assert_eq!(
        payload["proof_out_sha256"],
        JsonValue::String(sha256_file(&proof).unwrap())
    );
    assert_eq!(
        payload["checked_dimacs_sha256"],
        JsonValue::String(sha256_file(&cnf).unwrap())
    );
}

#[test]
fn fmla_learned_lrat_dry_run_artifact_discovery_requires_retained_stats_field() {
    let dir = tempfile::tempdir().unwrap();
    let case_dir = dir.path().join("case");
    fs::create_dir_all(&case_dir).unwrap();
    let stderr = case_dir.join("stderr.txt");
    let inside = case_dir.join("custom-learned-dry-run.json");
    write_fmla_learned_lrat_dry_run_artifact(&inside);
    fs::write(
        &stderr,
        format!(
            "{}\n",
            json!({
                "fmla_learned_lrat_dry_run_artifact_path": path_string(&inside),
            })
        ),
    )
    .unwrap();

    let retained = find_retained_fmla_learned_lrat_dry_run_artifact(&case_dir, &stderr)
        .unwrap()
        .expect("retained artifact");
    assert_eq!(retained.path, inside);
    assert_eq!(
        retained.schema,
        FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA
    );

    let outside_dir = dir.path().join("outside");
    fs::create_dir_all(&outside_dir).unwrap();
    let outside = outside_dir.join("custom-learned-dry-run.json");
    write_fmla_learned_lrat_dry_run_artifact(&outside);
    fs::write(
        &stderr,
        format!(
            "{}\n",
            json!({
                "fmla_learned_lrat_dry_run_artifact_path": path_string(&outside),
            })
        ),
    )
    .unwrap();
    assert!(
        find_retained_fmla_learned_lrat_dry_run_artifact(&case_dir, &stderr)
            .unwrap()
            .is_none()
    );
}

#[test]
fn fmla_postcheck_admission_passes_retained_learned_lrat_artifact() {
    let fixture = FmlaPostcheckFixture::new();
    let stderr = fixture.case_dir.join("stderr.txt");
    let learned = fixture
        .case_dir
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");
    write_fmla_learned_lrat_dry_run_artifact(&learned);
    fs::write(
        &stderr,
        format!(
            "{}\n",
            json!({
                "fmla_learned_lrat_dry_run_artifact_path": path_string(&learned),
            })
        ),
    )
    .unwrap();
    let retained = find_retained_fmla_learned_lrat_dry_run_artifact(&fixture.case_dir, &stderr)
        .unwrap()
        .expect("retained learned LRAT dry-run artifact");

    let evidence = run_fmla_postcheck_admission_replay(
        &fixture.solver_root,
        &fixture.cnf,
        &fixture.proof,
        &fixture.case_dir,
        &fixture.external,
        &fmla_postcheck_test_counters(),
        Some(&retained),
        1.0,
    )
    .unwrap();

    assert_eq!(evidence.status, "committed_checker_backed_admission");
    assert_eq!(evidence.materializer_records, "2");
    assert_eq!(evidence.external_checker_artifact_rows, "2");
    assert_eq!(evidence.preprocess_tx_committed, "0");
    assert_eq!(
        evidence.learned_lrat_dry_run_artifact,
        path_string(&learned)
    );
    assert_eq!(
        evidence.learned_lrat_dry_run_artifact_schema,
        FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA
    );
    assert_eq!(
        evidence.main_lrat_authority_replay_env,
        FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_ENV
    );
    assert_eq!(
        evidence.main_lrat_authority_replay_env_value,
        path_string(
            &fixture
                .case_dir
                .join(FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_ARTIFACT)
        )
    );
    assert_eq!(
        evidence.main_lrat_authority_replay_env_status,
        "authorized_handoff"
    );
    let args = read_fake_ay_args(&fixture.args_log);
    assert!(args
        .windows(2)
        .any(|window| window[0] == "--learned-lrat-dry-run-artifact"
            && window[1] == path_string(&learned)));
}

#[test]
fn fmla_postcheck_admission_omits_unretained_learned_lrat_artifact() {
    let fixture = FmlaPostcheckFixture::new();
    let outside_dir = fixture._dir.path().join("outside");
    fs::create_dir_all(&outside_dir).unwrap();
    let outside = outside_dir.join("learned-lrat-dry-run-proof-artifact.json");
    write_fmla_learned_lrat_dry_run_artifact(&outside);
    let candidates = vec![outside];
    let retained =
        retained_fmla_learned_lrat_dry_run_artifact(&fixture.case_dir, candidates.iter()).unwrap();
    assert!(retained.is_none());

    let evidence = run_fmla_postcheck_admission_replay(
        &fixture.solver_root,
        &fixture.cnf,
        &fixture.proof,
        &fixture.case_dir,
        &fixture.external,
        &fmla_postcheck_test_counters(),
        retained.as_ref(),
        1.0,
    )
    .unwrap();

    assert_eq!(evidence.status, "committed_checker_backed_admission");
    assert!(evidence.learned_lrat_dry_run_artifact.is_empty());
    let args = read_fake_ay_args(&fixture.args_log);
    assert!(!args
        .iter()
        .any(|arg| arg == "--learned-lrat-dry-run-artifact"));
}

#[test]
fn evidence_summary_rejects_external_checker_artifact_proof_hash_drift() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    let artifact = PathBuf::from(rows[1].get("external_proof_checker_verdict_artifact"));
    let mut payload = load_json_object(&artifact).unwrap();
    payload["proof_out_sha256"] = JsonValue::String("0".repeat(64));
    write_json_pretty(&artifact, &payload).unwrap();
    insert(
        &mut rows[1].fields,
        "external_proof_checker_verdict_artifact_sha256",
        &sha256_file(&artifact).unwrap(),
    );
    write_raw_tsv(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    let message = err.to_string();
    assert!(
        message.contains(
            "external checker verdict artifact proof_out_sha256 does not match proof_sha256"
        ),
        "{message}"
    );
    assert!(
        message.contains(
            "external checker verdict artifact proof_out_sha256 does not match retained proof.out"
        ),
        "{message}"
    );
}

#[test]
fn evidence_summary_rejects_external_checker_artifact_dirty_stdout() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    let artifact = PathBuf::from(rows[1].get("external_proof_checker_verdict_artifact"));
    let mut payload = load_json_object(&artifact).unwrap();
    payload["checker_stdout"] = JsonValue::String("s NOT VERIFIED\ns VERIFIED UNSAT\n".into());
    write_json_pretty(&artifact, &payload).unwrap();
    insert(
        &mut rows[1].fields,
        "external_proof_checker_verdict_artifact_sha256",
        &sha256_file(&artifact).unwrap(),
    );
    write_raw_tsv(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    assert!(
            err.to_string().contains(
                "external checker verdict artifact checker_stdout/checker_stderr do not contain a clean VERIFIED verdict"
            ),
            "{err}"
        );
}

#[test]
fn evidence_summary_accepts_fmla_w132_packet_and_restricted_subset_preprocess_tx() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[0].fields, "instance", "FmlaEquivChain_4_6_6.cnf");
    add_valid_fmla_w132_packet(&mut rows[0], fixture._dir.path());
    add_clean_fmla_preprocess_tx(&mut rows[0]);
    write_raw_tsv_all_fields(&raw_tsv, &rows).unwrap();

    build_fixture_evidence_summary(&fixture).unwrap();
}

#[test]
fn evidence_summary_rejects_fmla_sat_missing_w132_packet() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[0].fields, "instance", "FmlaEquivChain_4_6_6.cnf");
    write_raw_tsv_all_fields(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    assert!(
        err.to_string()
            .contains("requires W132 original-DIMACS reconstructed-model validation packet"),
        "{err}"
    );
}

#[test]
fn evidence_summary_rejects_fmla_w132_stdout_hash_drift() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[0].fields, "instance", "FmlaEquivChain_4_6_6.cnf");
    add_valid_fmla_w132_packet(&mut rows[0], fixture._dir.path());
    insert(
        &mut rows[0].fields,
        "reconstructed_original_dimacs_model_stdout_sha256",
        &"b".repeat(64),
    );
    write_raw_tsv_all_fields(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    assert!(
        err.to_string().contains("solver_stdout_sha256 must match"),
        "{err}"
    );
}

#[test]
fn evidence_summary_rejects_fmla_w132_bad_sha_and_packet_status() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[0].fields, "instance", "FmlaEquivChain_4_6_6.cnf");
    add_valid_fmla_w132_packet(&mut rows[0], fixture._dir.path());
    insert(
        &mut rows[0].fields,
        "reconstructed_original_dimacs_model_original_sha256",
        "not-a-sha256",
    );
    insert(
        &mut rows[0].fields,
        "reconstructed_original_dimacs_model_packet_status",
        "invalid",
    );
    insert(
        &mut rows[0].fields,
        "reconstructed_original_dimacs_model_packet_invalid_reason",
        "stale-report",
    );
    write_raw_tsv_all_fields(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    let message = err.to_string();
    assert!(
        message.contains("must be a 64-character hex SHA256"),
        "{message}"
    );
    assert!(
        message.contains("reconstructed_original_dimacs_model_packet_status=\"invalid\""),
        "{message}"
    );
    assert!(
        message.contains("packet_invalid_reason=\"stale-report\""),
        "{message}"
    );
}

#[test]
fn evidence_summary_rejects_fmla_w132_wrong_checker_and_duplicate_flag() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[0].fields, "instance", "FmlaEquivChain_4_6_6.cnf");
    add_valid_fmla_w132_packet(&mut rows[0], fixture._dir.path());
    let original = rows[0]
        .get("reconstructed_original_dimacs_model_original_path")
        .to_string();
    let stdout = rows[0]
        .get("reconstructed_original_dimacs_model_stdout")
        .to_string();
    let verdict = rows[0]
        .get("reconstructed_original_dimacs_model_verdict")
        .to_string();
    insert(
        &mut rows[0].fields,
        "reconstructed_original_dimacs_model_check_command",
        &json!([
            "python3",
            "scripts/not-the-w132-checker.py",
            "--original-dimacs",
            original,
            "--original-dimacs",
            original,
            "--check-reconstructed-model",
            stdout,
            "--verdict-out",
            verdict,
        ])
        .to_string(),
    );
    write_raw_tsv_all_fields(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    let message = err.to_string();
    assert!(
        message.contains("must invoke the W132 reconstructed-model checker"),
        "{message}"
    );
    assert!(
        message.contains("has duplicate --original-dimacs flags"),
        "{message}"
    );
}

#[test]
fn evidence_summary_rejects_fmla_destructive_missing_preprocess_tx() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[1].fields, "instance", "FmlaEquivChain_4_6_6.cnf");
    insert(&mut rows[1].fields, "sat.preprocess_tx_started", "1");
    write_raw_tsv_all_fields(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    assert!(
        err.to_string()
            .contains("missing required preprocess transaction counters"),
        "{err}"
    );
}

#[test]
fn evidence_summary_rejects_fmla_destructive_pending_preprocess_tx() {
    let fixture = evidence_fixture(false);
    let raw_tsv = fixture_raw_tsv_path(&fixture);
    let mut rows = read_tsv_records(&raw_tsv).unwrap();
    insert(&mut rows[1].fields, "instance", "FmlaEquivChain_4_6_6.cnf");
    add_clean_fmla_preprocess_tx(&mut rows[1]);
    insert(
        &mut rows[1].fields,
        "sat.preprocess_tx_proof_obligation_pending",
        "1",
    );
    write_raw_tsv_all_fields(&raw_tsv, &rows).unwrap();

    let err = build_fixture_evidence_summary(&fixture).unwrap_err();
    assert!(
        err.to_string()
            .contains("pending/rejected/missing preprocess transaction obligations"),
        "{err}"
    );
}

#[test]
fn evidence_summary_rejects_missing_per_row_stats_json() {
    let fixture = evidence_fixture(false);
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.join("stats-0.json")],
    };

    let err = build_evidence_summary(&opts, &fixture.scoreboard).unwrap_err();
    assert!(
        err.to_string().contains(
            "requires one stats JSON per scored row, got 1 stats JSON artifact(s) for 2 row(s)"
        ),
        "{err}"
    );
}

#[test]
fn evidence_summary_rejects_unknown_with_retained_proof_out() {
    let fixture = evidence_fixture(false);
    let mut scoreboard = load_json_object(&fixture.scoreboard).unwrap();
    let raw_tsv = PathBuf::from(
        scoreboard["variants"]["default"]["raw_tsv"]
            .as_str()
            .expect("raw_tsv path"),
    );
    let official_root = PathBuf::from(
        scoreboard["official_mirror_root"]
            .as_str()
            .expect("official mirror root"),
    );
    let bench_dir = official_root.join("benchmarks/sat/satcomp2026-main");
    let sat_path = bench_dir.join("tiny-sat.cnf");
    let unsat_path = bench_dir.join("tiny-unsat.cnf");

    let unknown_proof = fixture
        ._dir
        .path()
        .join("runs/default/tiny-sat/proof/proof.out");
    fs::create_dir_all(unknown_proof.parent().unwrap()).unwrap();
    fs::write(&unknown_proof, "partial stale proof\n").unwrap();
    let unknown_proof_s = path_string(&unknown_proof);
    let unknown_proof_sha = sha256_file(&unknown_proof).unwrap();

    let unsat_proof = fixture._dir.path().join("proof.out");
    let unsat_proof_s = path_string(&unsat_proof);
    let artifact = fixture._dir.path().join(EXTERNAL_CHECKER_VERDICT_ARTIFACT);
    let artifact_s = path_string(&artifact);
    let artifact_sha = sha256_file(&artifact).unwrap();
    let proof_sha = "c".repeat(64);
    let sat_path_s = path_string(&sat_path);
    let unsat_path_s = path_string(&unsat_path);
    let binary = fixture._dir.path().join("solver/ay");
    let binary_s = path_string(&binary);
    let binary_sha = sha256_file(&binary).unwrap();
    let binary_size = fs::metadata(&binary).unwrap().len().to_string();

    write_raw_tsv(
        &raw_tsv,
        &[
            evidence_record(&[
                ("suite", "sat-main-2026-official-mirror"),
                ("track", "main"),
                ("ai_class", "regular"),
                ("variant", "default"),
                ("instance", "tiny-sat.cnf"),
                ("path", sat_path_s.as_str()),
                ("expected", "sat"),
                ("actual", "unknown"),
                ("family", "unit"),
                ("category", "sanity"),
                ("elapsed_s", "5000.0"),
                ("par2_s", "10000.0"),
                ("exit_code", "0"),
                ("wrong", "0"),
                ("invalid", "0"),
                ("proof_status", "n/a"),
                ("ay_lrat_status", "ok"),
                ("proof_checker_status", "ok"),
                (
                    "external_proof_checker_verdict_artifact",
                    artifact_s.as_str(),
                ),
                (
                    "external_proof_checker_verdict_artifact_sha256",
                    artifact_sha.as_str(),
                ),
                (
                    "external_proof_checker_verdict_artifact_schema",
                    EXTERNAL_CHECKER_VERDICT_SCHEMA,
                ),
                ("external_proof_checker_verdict", "VERIFIED_UNSAT"),
                (
                    "external_proof_checker_proof_out_path",
                    unknown_proof_s.as_str(),
                ),
                ("proof_path", unknown_proof_s.as_str()),
                ("proof_bytes", "20"),
                ("proof_sha256", unknown_proof_sha.as_str()),
                ("model_status", "n/a"),
                ("binary_path", binary_s.as_str()),
                ("binary_sha256", binary_sha.as_str()),
                ("binary_size_bytes", binary_size.as_str()),
                ("binary_executable", "1"),
                ("ay", binary_s.as_str()),
                ("ay_sha256", binary_sha.as_str()),
            ]),
            evidence_record(&[
                ("suite", "sat-main-2026-official-mirror"),
                ("track", "main"),
                ("ai_class", "regular"),
                ("variant", "default"),
                ("instance", "tiny-unsat.cnf"),
                ("path", unsat_path_s.as_str()),
                ("expected", "unsat"),
                ("actual", "unsat"),
                ("family", "unit"),
                ("category", "sanity"),
                ("elapsed_s", "10.0"),
                ("par2_s", "10.0"),
                ("exit_code", "20"),
                ("wrong", "0"),
                ("invalid", "0"),
                ("proof_status", "valid"),
                ("ay_lrat_status", "ok"),
                ("proof_checker_status", "ok"),
                (
                    "external_proof_checker_verdict_artifact",
                    artifact_s.as_str(),
                ),
                (
                    "external_proof_checker_verdict_artifact_sha256",
                    artifact_sha.as_str(),
                ),
                (
                    "external_proof_checker_verdict_artifact_schema",
                    EXTERNAL_CHECKER_VERDICT_SCHEMA,
                ),
                ("external_proof_checker_verdict", "VERIFIED_UNSAT"),
                (
                    "external_proof_checker_proof_out_path",
                    unsat_proof_s.as_str(),
                ),
                ("proof_path", unsat_proof_s.as_str()),
                ("proof_bytes", "10"),
                ("proof_sha256", proof_sha.as_str()),
                ("model_status", "n/a"),
                ("binary_path", binary_s.as_str()),
                ("binary_sha256", binary_sha.as_str()),
                ("binary_size_bytes", binary_size.as_str()),
                ("binary_executable", "1"),
                ("ay", binary_s.as_str()),
                ("ay_sha256", binary_sha.as_str()),
            ]),
        ],
    )
    .unwrap();

    scoreboard["variants"]["default"]["summary"]["solved"] = JsonValue::from(1);
    scoreboard["variants"]["default"]["summary"]["solved_sat"] = JsonValue::from(0);
    scoreboard["variants"]["default"]["summary"]["unknown"] = JsonValue::from(1);
    scoreboard["variants"]["default"]["summary"]["sat_model_valid"] = JsonValue::from(0);
    scoreboard["variants"]["default"]["summary"]["par2_total"] = JsonValue::from(10010.0);
    scoreboard["variants"]["default"]["summary"]["par2_avg"] = JsonValue::from(5005.0);
    write_json_pretty(&fixture.scoreboard, &scoreboard).unwrap();

    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };
    let err = build_evidence_summary(&opts, &fixture.scoreboard).unwrap_err();
    let message = err.to_string();
    assert!(
        message.contains("retained proof.out must be marked stale_non_authoritative"),
        "{message}"
    );
    assert!(
        message.contains("must not record proof_checker_status=ok"),
        "{message}"
    );
    assert!(
        message.contains("must not record external proof checker authority"),
        "{message}"
    );
}

#[test]
fn official_mirror_row_gate_resolves_dotdot_escape() {
    let dir = tempfile::tempdir().unwrap();
    let official_root = dir.path().join("mirror");
    let outside_root = dir.path().join("outside");
    fs::create_dir_all(&official_root).unwrap();
    fs::create_dir_all(&outside_root).unwrap();
    let outside = outside_root.join("escaped.cnf");
    fs::write(&outside, "p cnf 1 0\n").unwrap();

    let escaped = official_root.join("../outside/escaped.cnf");
    assert!(
        !reported_path_is_inside_root(&path_string(&escaped), &official_root),
        "dotdot path resolved outside the official mirror should fail containment"
    );
}

#[test]
fn runtime_provenance_uses_solver_binary_not_run_wrapper() {
    let dir = tempfile::tempdir().unwrap();
    let run_sh = dir.path().join("run.sh");
    let solver = dir.path().join("ay");
    fs::write(&run_sh, "wrapper\n").unwrap();
    fs::write(&solver, "solver\n").unwrap();

    let binary = solver_binary_path(dir.path());
    let fields = runtime_provenance(binary.as_deref(), 2.0).unwrap();

    assert_eq!(fields.get("binary_path"), Some(&path_string(&solver)));
    assert_eq!(
        fields.get("binary_sha256"),
        Some(&sha256_file(&solver).unwrap())
    );
    assert_ne!(
        fields.get("binary_sha256"),
        Some(&sha256_file(&run_sh).unwrap())
    );
    assert_eq!(
        fields.get("binary_executable").map(String::as_str),
        Some("1")
    );
}

#[test]
fn run_wrapper_passes_fmla_learned_lrat_artifact_env_only_when_requested() {
    let dir = tempfile::tempdir().unwrap();
    let solver_root = dir.path().join("solver");
    let case_dir = dir.path().join("case");
    fs::create_dir_all(&solver_root).unwrap();
    fs::create_dir_all(&case_dir).unwrap();
    let run_sh = solver_root.join("run.sh");
    let env_log = dir.path().join("env-log.jsonl");
    let env_log_json = serde_json::to_string(&path_string(&env_log)).unwrap();
    fs::write(
        &run_sh,
        format!(
            r#"#!/usr/bin/env python3
import json
import os
import sys

with open({env_log_json}, "a", encoding="utf-8") as handle:
    handle.write(json.dumps({{
        "argv": sys.argv[1:],
        "matrix": os.environ.get("AY_SATCOMP_MATRIX"),
        "learned": os.environ.get("AY_SAT_FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT"),
        "replay": os.environ.get("AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY"),
        "current_proof": os.environ.get("AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT"),
    }}) + "\n")
print("s UNKNOWN")
"#
        ),
    )
    .unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(&run_sh).unwrap().permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&run_sh, permissions).unwrap();
    }

    let input = case_dir.join("FmlaEquivChain_4_6_6.cnf");
    fs::write(&input, "p cnf 1 0\n").unwrap();
    let stdout_path = case_dir.join("stdout.txt");
    let stderr_path = case_dir.join("stderr.txt");
    let learned_artifact = case_dir.join("fmla-learned-lrat-dry-run-proof-artifact.json");
    let replay_artifact = case_dir.join("fmla-main-lrat-postcheck-admission-replay.json");
    let proof_path = case_dir.join("proof.out");
    let (status, timed_out) = run_wrapper(
        &run_sh,
        &solver_root,
        &input,
        &case_dir,
        &stdout_path,
        &stderr_path,
        Some(&learned_artifact),
        None,
        &proof_path,
        1.0,
    )
    .unwrap();
    assert_eq!(status, Some(0));
    assert!(!timed_out);

    let handoff = FmlaMainLratAuthorityReplayHandoff {
        replay_artifact: replay_artifact.clone(),
        replay_artifact_sha256: "0".repeat(64),
    };
    let (status, timed_out) = run_wrapper(
        &run_sh,
        &solver_root,
        &input,
        &case_dir,
        &stdout_path,
        &stderr_path,
        None,
        Some(&handoff),
        &proof_path,
        1.0,
    )
    .unwrap();
    assert_eq!(status, Some(0));
    assert!(!timed_out);

    let logs: Vec<serde_json::Value> = fs::read_to_string(&env_log)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert_eq!(logs.len(), 2);
    assert_eq!(logs[0]["matrix"].as_str(), Some("1"));
    assert_eq!(
        logs[0]["learned"].as_str(),
        Some(path_string(&learned_artifact).as_str())
    );
    assert_eq!(logs[1]["matrix"].as_str(), Some("1"));
    assert_eq!(logs[1]["learned"].as_str(), None);
    assert_eq!(logs[0]["replay"].as_str(), None);
    assert_eq!(logs[0]["current_proof"].as_str(), None);
    assert_eq!(
        logs[1]["replay"].as_str(),
        Some(path_string(&replay_artifact).as_str())
    );
    assert_eq!(
        logs[1]["current_proof"].as_str(),
        Some(path_string(&proof_path).as_str())
    );
}

fn evidence_fixture(limited: bool) -> EvidenceFixture {
    let dir = tempfile::tempdir().unwrap();
    let official_root = dir.path().join("win-all-software-proof-competitions");
    let bench_dir = official_root.join("benchmarks/sat/satcomp2026-main");
    fs::create_dir_all(&bench_dir).unwrap();
    let sat_path = bench_dir.join("tiny-sat.cnf");
    let unsat_path = bench_dir.join("tiny-unsat.cnf");
    fs::write(&sat_path, "p cnf 1 1\n1 0\n").unwrap();
    fs::write(&unsat_path, "p cnf 1 2\n1 0\n-1 0\n").unwrap();

    let proof = dir.path().join("proof.out");
    fs::write(&proof, "stub proof\n").unwrap();
    let artifact = dir.path().join(EXTERNAL_CHECKER_VERDICT_ARTIFACT);
    let artifact_s = path_string(&artifact);
    let proof_s = path_string(&proof);
    let proof_sha = sha256_file(&proof).unwrap();
    let sat_path_s = path_string(&sat_path);
    let unsat_path_s = path_string(&unsat_path);
    let checked_dimacs_sha = sha256_file(&unsat_path).unwrap();
    let checker_s = "/fixture/cake_lpr";
    let checker_argv = json!([checker_s, unsat_path_s.clone(), proof_s.clone()]);
    write_json_pretty(
        &artifact,
        &json!({
            "schema": EXTERNAL_CHECKER_VERDICT_SCHEMA,
            "runtime_field": "external_proof_checker_verdict_artifact",
            "verdict": "VERIFIED_UNSAT",
            "artifact_path": artifact_s.clone(),
            "checker_path": checker_s,
            "checker_sha256": "",
            "checker_command": format!("{checker_s} {unsat_path_s} {proof_s}"),
            "checker_argv": checker_argv,
            "checker_exit_code": 0,
            "checker_stdout": "s VERIFIED UNSAT\n",
            "checker_stderr": "c checker comment\n",
            "proof_out_path": proof_s.clone(),
            "proof_out_sha256": proof_sha.clone(),
            "checked_dimacs_path": unsat_path_s.clone(),
            "checked_dimacs_sha256": checked_dimacs_sha,
        }),
    )
    .unwrap();
    let artifact_sha = sha256_file(&artifact).unwrap();
    let binary = dir.path().join("solver/ay");
    fs::create_dir_all(binary.parent().unwrap()).unwrap();
    fs::write(&binary, "fixture ay binary\n").unwrap();
    let binary_s = path_string(&binary);
    let binary_sha = sha256_file(&binary).unwrap();
    let binary_size = fs::metadata(&binary).unwrap().len().to_string();
    let sat_model_stdout = dir.path().join("tiny-sat.stdout");
    fs::write(&sat_model_stdout, "s SATISFIABLE\nv 1 0\n").unwrap();
    let sat_model_stdout_s = path_string(&sat_model_stdout);
    let sat_model_command_json = json!([
        binary_s,
        "check",
        "model",
        sat_path_s,
        sat_model_stdout_s,
        "--json",
    ]);
    let sat_model_command = sat_model_command_json.to_string();
    let sat_model_artifact = dir.path().join(SAT_MODEL_CHECK_ARTIFACT);
    write_json_pretty(
        &sat_model_artifact,
        &json!({
            "schema": SAT_MODEL_CHECK_ARTIFACT_SCHEMA,
            "formula": sat_path_s,
            "stdout": sat_model_stdout_s,
            "model_status": "valid",
            "valid": true,
            "checker_command_json": sat_model_command_json,
            "checker_exit_status": 0,
        }),
    )
    .unwrap();
    let sat_model_artifact_s = path_string(&sat_model_artifact);
    let sat_model_artifact_sha = sha256_file(&sat_model_artifact).unwrap();

    let raw_tsv = dir.path().join("default-raw.tsv");
    write_raw_tsv(
        &raw_tsv,
        &[
            evidence_record(&[
                ("suite", "sat-main-2026-official-mirror"),
                ("track", "main"),
                ("ai_class", "regular"),
                ("variant", "default"),
                ("instance", "tiny-sat.cnf"),
                ("path", sat_path_s.as_str()),
                ("expected", "sat"),
                ("actual", "sat"),
                ("family", "unit"),
                ("category", "sanity"),
                ("elapsed_s", "8.0"),
                ("par2_s", "8.0"),
                ("exit_code", "10"),
                ("wrong", "0"),
                ("invalid", "0"),
                ("proof_status", "n/a"),
                ("ay_lrat_status", "n/a"),
                ("proof_checker_status", "n/a"),
                ("proof_bytes", "0"),
                ("model_status", "valid"),
                ("model_checker_artifact", sat_model_artifact_s.as_str()),
                (
                    "model_checker_artifact_sha256",
                    sat_model_artifact_sha.as_str(),
                ),
                (
                    "model_checker_artifact_schema",
                    SAT_MODEL_CHECK_ARTIFACT_SCHEMA,
                ),
                ("model_checker_formula", sat_path_s.as_str()),
                ("model_checker_stdout", sat_model_stdout_s.as_str()),
                ("model_checker_command_json", sat_model_command.as_str()),
                ("model_checker_exit_status", "0"),
                ("binary_path", binary_s.as_str()),
                ("binary_sha256", binary_sha.as_str()),
                ("binary_size_bytes", binary_size.as_str()),
                ("binary_executable", "1"),
                ("ay", binary_s.as_str()),
                ("ay_sha256", binary_sha.as_str()),
            ]),
            evidence_record(&[
                ("suite", "sat-main-2026-official-mirror"),
                ("track", "main"),
                ("ai_class", "regular"),
                ("variant", "default"),
                ("instance", "tiny-unsat.cnf"),
                ("path", unsat_path_s.as_str()),
                ("expected", "unsat"),
                ("actual", "unsat"),
                ("family", "unit"),
                ("category", "sanity"),
                ("elapsed_s", "10.0"),
                ("par2_s", "10.0"),
                ("exit_code", "20"),
                ("wrong", "0"),
                ("invalid", "0"),
                ("proof_status", "valid"),
                ("ay_lrat_status", "ok"),
                ("proof_checker_status", "ok"),
                (
                    "external_proof_checker_verdict_artifact",
                    artifact_s.as_str(),
                ),
                (
                    "external_proof_checker_verdict_artifact_sha256",
                    artifact_sha.as_str(),
                ),
                (
                    "external_proof_checker_verdict_artifact_schema",
                    EXTERNAL_CHECKER_VERDICT_SCHEMA,
                ),
                ("external_proof_checker_verdict", "VERIFIED_UNSAT"),
                ("external_proof_checker_proof_out_path", proof_s.as_str()),
                ("proof_path", proof_s.as_str()),
                ("proof_bytes", "10"),
                ("proof_sha256", proof_sha.as_str()),
                ("model_status", "n/a"),
                ("binary_path", binary_s.as_str()),
                ("binary_sha256", binary_sha.as_str()),
                ("binary_size_bytes", binary_size.as_str()),
                ("binary_executable", "1"),
                ("ay", binary_s.as_str()),
                ("ay_sha256", binary_sha.as_str()),
            ]),
        ],
    )
    .unwrap();

    let scoreboard = dir.path().join("scoreboard.json");
    let variant_summary = json!({
        "total": 2,
        "solved": 2,
        "solved_sat": 1,
        "solved_unsat": 1,
        "expected_sat": 1,
        "expected_unsat": 1,
        "sat_model_valid": 1,
        "sat_model_invalid": 0,
        "unsat_proof_valid": 1,
        "unsat_proof_invalid": 0,
        "unknown": 0,
        "timeout": 0,
        "error": 0,
        "wrong": 0,
        "invalid": 0,
        "disqualified": false,
        "par2_total": 18.0,
        "par2_avg": 9.0,
        "timeout_sec": 5000.0,
    });
    let mut variants = serde_json::Map::new();
    variants.insert(
        "default".to_string(),
        json!({
            "raw_tsv": path_string(&raw_tsv),
            "summary": variant_summary,
        }),
    );
    write_json_pretty(
        &scoreboard,
        &json!({
            "suite": "sat-main-2026-official-mirror",
            "track": "main",
            "ai_class": "regular",
            "submission_root": "/fixture/submission",
            "benchmark_source": "official-mirror",
            "official_mirror_required": true,
            "official_mirror_root": path_string(&official_root),
            "timeout_sec": 5000.0,
            "expected_total": 2,
            "limited": limited,
            "allow_smoke": false,
            "soundness": true,
            "fail_on_wrong": true,
            "proof_checker": "/fixture/cake_lpr",
            "manifest": path_string(&bench_dir.join("manifest.csv")),
            "corpus_fingerprint": "sha256:fixture-satcomp-corpus",
            "source_commit": "abc123",
            "source_dirty": false,
            "output_dir": path_string(dir.path()),
            "variants": JsonValue::Object(variants),
        }),
    )
    .unwrap();

    let current_stats = dir.path().join("current-stats");
    fs::create_dir_all(&current_stats).unwrap();
    for index in 0..2 {
        write_json_pretty(
            &current_stats.join(format!("stats-{index}.json")),
            &json!({
                "schema": STATS_JSON_SCHEMA,
                "mode": "dimacs-sat",
                "competition_jit": {
                    "application_counter": {
                        "key": SAT_NATIVE_HELPER_COUNTER,
                        "value": 1,
                    }
                },
                "counters": {
                    "sat_native_code_helper_applications": 1,
                    "sat.conflict_analysis_native_applications": 1,
                    "sat.subsumption_native_applications": 0,
                    "sat_learned_clause_candidate_applications": 0,
                    "solver_program.sat_whole_loop.applies": 0,
                    "solver_program.sat_whole_loop.installs": 0,
                }
            }),
        )
        .unwrap();
    }

    EvidenceFixture {
        _dir: dir,
        scoreboard,
        current_stats,
    }
}

fn evidence_record(pairs: &[(&str, &str)]) -> Record {
    let mut fields = BTreeMap::new();
    for &column in TSV_COLUMNS {
        insert(&mut fields, column, "");
    }
    for (key, value) in pairs {
        insert(&mut fields, key, value);
    }
    Record { fields }
}

fn official_mirror_test_opts(root: &Path) -> SatCompMatrixRunOptions {
    let mut opts = test_run_opts();
    opts.suite = "sat-main-2026-official-mirror".to_string();
    opts.official_mirror_root = Some(root.to_path_buf());
    opts
}

fn write_manifest_mirror_case(suite_dir: &Path, manifest: &Path) {
    fs::create_dir_all(suite_dir).unwrap();
    let sat = suite_dir.join("tiny-sat.cnf");
    let unsat = suite_dir.join("tiny-unsat.cnf");
    fs::write(&sat, "p cnf 1 1\n1 0\n").unwrap();
    fs::write(&unsat, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
    fs::write(
        manifest,
        format!(
            "local_path,result,family,category\n{},sat,unit,sanity\n{},unsat,unit,sanity\n",
            path_string(&sat),
            path_string(&unsat)
        ),
    )
    .unwrap();
}

fn write_recursive_directory_mirror_case(suite_dir: &Path) {
    let nested = suite_dir.join("nested");
    fs::create_dir_all(&nested).unwrap();
    fs::write(suite_dir.join("tiny-sat.cnf"), "p cnf 1 1\n1 0\n").unwrap();
    fs::write(nested.join("tiny-unsat.cnf"), "p cnf 1 2\n1 0\n-1 0\n").unwrap();
}

fn fixture_raw_tsv_path(fixture: &EvidenceFixture) -> PathBuf {
    let scoreboard = load_json_object(&fixture.scoreboard).unwrap();
    PathBuf::from(
        scoreboard["variants"]["default"]["raw_tsv"]
            .as_str()
            .expect("raw_tsv path"),
    )
}

fn build_fixture_evidence_summary(fixture: &EvidenceFixture) -> Result<JsonValue> {
    let opts = SatCompMatrixEvidenceSummaryOptions {
        scoreboard: fixture.scoreboard.clone(),
        output: fixture._dir.path().join("candidate-current.json"),
        variant: "default".to_string(),
        candidate_mode: EvidenceCandidateMode::Current,
        stats_json: vec![fixture.current_stats.clone()],
    };
    build_evidence_summary(&opts, &fixture.scoreboard)
}

fn add_valid_fmla_w132_packet(row: &mut Record, root: &Path) {
    let artifact_dir = root.join("w132");
    fs::create_dir_all(&artifact_dir).unwrap();
    let original = artifact_dir.join("FmlaEquivChain_4_6_6.cnf");
    let stdout = artifact_dir.join("reconstructed-original-dimacs-model.stdout");
    let verdict = artifact_dir.join("reconstructed-model-checker-verdict.json");
    fs::write(&original, "p cnf 1 1\n1 0\n").unwrap();
    fs::write(&stdout, "s SATISFIABLE\nv 1 0\n").unwrap();
    write_json_pretty(
        &verdict,
        &json!({
            "schema": "ay.w132-fmla-reconstructed-model-checker-verdict/v1",
            "status": "valid",
        }),
    )
    .unwrap();

    let original_s = path_string(&original);
    let stdout_s = path_string(&stdout);
    let verdict_s = path_string(&verdict);
    let stdout_sha = sha256_file(&stdout).unwrap();
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_original_path",
        &original_s,
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_original_sha256",
        &sha256_file(&original).unwrap(),
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_solver_stdout",
        &stdout_s,
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_solver_stdout_sha256",
        &stdout_sha,
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_stdout",
        &stdout_s,
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_stdout_sha256",
        &stdout_sha,
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_stdout_present",
        "1",
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_stdout_matches_solver_stdout",
        "1",
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_reconstruction_source",
        "finalize_sat_model -> emit_dimacs_sat_model",
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_check_command",
        &json!([
            "python3",
            FMLA_RECONSTRUCTED_MODEL_CHECKER,
            "--original-dimacs",
            original_s,
            "--check-reconstructed-model",
            stdout_s,
            "--verdict-out",
            verdict_s,
        ])
        .to_string(),
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_checker_exit_code",
        "0",
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_verdict",
        &verdict_s,
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_verdict_written",
        "1",
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_packet_status",
        "valid",
    );
    insert(
        &mut row.fields,
        "reconstructed_original_dimacs_model_packet_invalid_reason",
        "",
    );
}

fn add_clean_fmla_preprocess_tx(row: &mut Record) {
    for field in PREPROCESS_TX_COUNTER_FIELDS {
        insert(&mut row.fields, field, "0");
    }
    insert(&mut row.fields, "sat.preprocess_tx_started", "1");
    insert(&mut row.fields, "sat.preprocess_tx_attempted", "1");
    insert(&mut row.fields, "sat.preprocess_tx_committed", "1");
    insert(
        &mut row.fields,
        "sat.preprocess_tx_proof_obligation_satisfied",
        "1",
    );
    insert(
        &mut row.fields,
        "sat.preprocess_tx_reconstruction_witness_present",
        "1",
    );
}

fn write_raw_tsv_all_fields(path: &Path, records: &[Record]) -> Result<()> {
    let mut columns: Vec<String> = TSV_COLUMNS
        .iter()
        .map(|column| (*column).to_string())
        .collect();
    for row in records {
        for key in row.fields.keys() {
            if !columns.iter().any(|column| column == key) {
                columns.push(key.clone());
            }
        }
    }
    let mut file = File::create(path).with_context(|| format!("creating {}", path.display()))?;
    writeln!(file, "{}", columns.join("\t"))?;
    for row in records {
        let values: Vec<String> = columns
            .iter()
            .map(|column| escape_cell(row.get(column), "\t"))
            .collect();
        writeln!(file, "{}", values.join("\t"))?;
    }
    Ok(())
}

fn test_run_opts() -> SatCompMatrixRunOptions {
    SatCompMatrixRunOptions {
        suite: "custom".to_string(),
        track: "main".to_string(),
        ai_class: "regular".to_string(),
        variants: "default".to_string(),
        proof_format: "lrat".to_string(),
        submission_root: PathBuf::from("target/sat26-submission"),
        run_sh: None,
        output: PathBuf::from("target/satcomp-matrix"),
        manifest: None,
        benchmarks_dir: None,
        filter_family: Vec::new(),
        instance: None,
        expected: "unknown".to_string(),
        family: "ad-hoc".to_string(),
        category: "ad-hoc".to_string(),
        timeout_sec: None,
        limit: None,
        soundness: false,
        fail_on_wrong: false,
        proof_checker: "none".to_string(),
        require_total: None,
        official_mirror_root: None,
        require_official_mirror: false,
        allow_smoke: false,
        fmla_main_lrat_authority_replay_two_pass: false,
    }
}
