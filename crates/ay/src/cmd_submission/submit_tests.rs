//! Unit tests for the submission pipeline (`super` = cmd_submission).
//! Extracted verbatim from cmd_submission.rs to keep the module readable.

use super::chc_worker::{chc_worker_benchmark_plan, ChcWorkerBenchmarkPlan};
use super::*;

#[cfg(feature = "submission-live")]
fn chc_zenodo_submit_test_options() -> ChcCompZenodoSubmitOptions {
    ChcCompZenodoSubmitOptions {
        dry_run: false,
        allow_dirty: false,
        skip_build: false,
        build_tool: "zigbuild".to_string(),
        ay_bin: PathBuf::from("target/x86_64-unknown-linux-musl/release/ay"),
        host_ay: None,
        package_dir: PathBuf::from("target/submission-packages/chc-comp-2026"),
        report_dir: PathBuf::from(CHC_ZENODO_DEFAULT_REPORT_DIR),
        tracks: CHC_DEFAULT_TRACKS.to_string(),
        skip_pr: false,
        no_publish: false,
        env_file: PathBuf::from("~/.env"),
        zenodo_token_env: "ZENODO_API_KEY".to_string(),
        zenodo_base_url: "https://zenodo.org".to_string(),
        zenodo_timeout_seconds: 180,
        zenodo_title: None,
        creator_name: "Yates, Andrew".to_string(),
        source_url: "https://github.com/alabsystems/ay".to_string(),
        chc_repo_url: CHC_ZENODO_DEFAULT_REPO.to_string(),
        chc_checkout: PathBuf::from(CHC_ZENODO_DEFAULT_CHECKOUT),
        fork_repo_url: None,
        fork_ssh_key: PathBuf::from(CHC_ZENODO_DEFAULT_FORK_SSH_KEY),
        pr_title: "Add ay CHC-COMP 2026 verifier".to_string(),
    }
}

#[test]
fn dotenv_parser_reads_quoted_zenodo_key() {
    let dir = make_temp_dir("ay-submit-dotenv-test").expect("temp dir");
    let path = dir.join(".env");
    fs::write(
        &path,
        "# comment\nZENODO_API_KEY='secret-token'\nOTHER=\"value\"\n",
    )
    .expect("write dotenv");

    let values = parse_dotenv_file(&path).expect("parse dotenv");

    assert!(values
        .iter()
        .any(|(key, value)| key == "ZENODO_API_KEY" && value == "secret-token"));
    assert!(values
        .iter()
        .any(|(key, value)| key == "OTHER" && value == "value"));
}

#[test]
fn makefile_patch_adds_ay_dependency_and_is_idempotent() {
    let makefile = "download-verifiers: \\\n\t$(TOOLS_DIRECTORY)/golem \\\n\t$(TOOLS_DIRECTORY)/loat\n\n$(TOOLS_DIRECTORY)/theta:\n\ttrue\n";
    let fragment = "# generated\n$(TOOLS_DIRECTORY)/ay:\n\twget \"https://zenodo.org/records/123/files/ay.tar.gz?download=1\" -O $(TOOLS_DIRECTORY)/ay.tar.gz\n";

    let patched = patch_chc_submit_makefile(makefile, fragment).expect("patch makefile");
    let patched_again =
        patch_chc_submit_makefile(&patched, fragment).expect("patch makefile again");

    assert!(patched.contains("\t$(TOOLS_DIRECTORY)/loat \\\n\t$(TOOLS_DIRECTORY)/ay"));
    assert_eq!(patched.matches("$(TOOLS_DIRECTORY)/ay:").count(), 1);
    assert!(patched.contains("https://zenodo.org/records/123/files/ay.tar.gz?download=1"));
    assert_eq!(
        patched.matches("$(TOOLS_DIRECTORY)/ay").count(),
        patched_again.matches("$(TOOLS_DIRECTORY)/ay").count()
    );
}

#[test]
fn url_redaction_hides_access_token_query() {
    let redacted = redact_submit_url("https://zenodo.org/api/x?access_token=abc&download=1");

    assert!(!redacted.contains("abc"));
    assert!(redacted.contains("access_token=REDACTED"));
    assert!(redacted.contains("download=1"));
}

#[test]
fn chc_zenodo_github_policy_requires_operator() {
    require_submission_github_owner(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY, "operator")
        .expect("operator owner is accepted");

    let err = require_submission_github_owner(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY, "example-login")
        .expect_err("nonmatching owner is rejected");
    assert!(err.to_string().contains("operator"));
    assert!(err.to_string().contains("example-login"));
}

#[test]
fn github_account_policy_message_prompts_login_check() {
    let warning = submission_github_account_policy_message(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY);

    assert!(warning.contains("gh api user --jq .login"));
    assert!(warning.contains("account-specific GitHub auth"));
    assert!(warning.contains("operator"));
    assert!(warning.contains("example-login"));

    let err = submission_github_login_error(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY, "example-login")
        .expect("nonmatching login rejected");
    assert!(err.contains("refusing"));
    assert!(err.contains("operator"));
    assert!(err.contains("example-login"));
    assert!(
        submission_github_login_error(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY, "operator").is_none()
    );
}

#[test]
fn chc_expected_status_ignores_auto_added_placeholder_verdict() {
    let yml = "\
format_version: '2.0'\n\
input_files: smoke.smt2\n\
properties:\n\
- property_file: ../properties/check-sat.prp\n\
  expected_verdict: true\n\
  # placeholder verdict (auto-added)\n";

    assert_eq!(chc_expected_status_from_yml(yml), None);
}

#[test]
fn chc_expected_status_prefers_majority_vote_over_placeholder_comment() {
    let yml = "\
format_version: '2.0'\n\
input_files: smoke.smt2\n\
properties:\n\
- expected_verdict: true\n\
  majority_vote_verdict: sat\n\
  property_file: ../properties/check-sat.prp\n\
  # placeholder verdict (auto-added)\n";

    assert_eq!(chc_expected_status_from_yml(yml).as_deref(), Some("sat"));
}

#[test]
fn chc_submit_pr_list_finds_existing_pr_by_owner_and_branch() {
    let output = r#"
        [
          {
            "number": 18,
            "url": "https://github.com/chc-comp/chc-comp-2026/pull/18",
            "state": "OPEN",
            "headRefName": "ay-chccomp-2026-submit",
            "headRepositoryOwner": {"login": "someone-else"}
          },
          {
            "number": 17,
            "url": "https://github.com/chc-comp/chc-comp-2026/pull/17",
            "state": "OPEN",
            "headRefName": "ay-chccomp-2026-submit",
            "headRepositoryOwner": {"login": "operator"}
          },
          {
            "number": 14,
            "url": "https://github.com/chc-comp/chc-comp-2026/pull/14",
            "state": "MERGED",
            "headRefName": "ay-submission-2026",
            "headRepositoryOwner": {"login": "operator"}
          }
        ]
        "#;

    let pr = parse_chc_submit_pr_list(output, "operator", "ay-chccomp-2026-submit")
        .expect("PR list parses")
        .expect("matching PR exists");

    assert_eq!(pr.number, Some(17));
    assert_eq!(pr.selector(), "17");
    assert_eq!(pr.url, "https://github.com/chc-comp/chc-comp-2026/pull/17");
}

#[test]
fn chc_submit_pr_list_accepts_flattened_head_owner_shape() {
    let output = r#"
        [
          {
            "number": 17,
            "url": "https://github.com/chc-comp/chc-comp-2026/pull/17",
            "state": "OPEN",
            "headRefName": "ay-chccomp-2026-submit",
            "headOwner": "operator"
          }
        ]
        "#;

    let pr = parse_chc_submit_pr_list(output, "operator", "ay-chccomp-2026-submit")
        .expect("PR list parses")
        .expect("matching PR exists");

    assert_eq!(pr.number, Some(17));
}

#[test]
fn chc_submit_pr_list_rejects_ambiguous_matches() {
    let output = r#"
        [
          {
            "number": 17,
            "url": "https://github.com/chc-comp/chc-comp-2026/pull/17",
            "state": "OPEN",
            "headRefName": "ay-chccomp-2026-submit",
            "headRepositoryOwner": {"login": "operator"}
          },
          {
            "number": 19,
            "url": "https://github.com/chc-comp/chc-comp-2026/pull/19",
            "state": "OPEN",
            "headRefName": "ay-chccomp-2026-submit",
            "headRepositoryOwner": {"login": "operator"}
          }
        ]
        "#;

    let err = parse_chc_submit_pr_list(output, "operator", "ay-chccomp-2026-submit")
        .expect_err("duplicate matching PRs are unsafe");

    assert!(err.to_string().contains("multiple PRs"));
}

#[test]
fn chc_submit_pr_create_already_exists_output_is_detectable() {
    let stderr = "a pull request for branch \"operator:ay-chccomp-2026-submit\" \
                      into branch \"chc-comp:main\" already exists: \
                      https://github.com/chc-comp/chc-comp-2026/pull/17";

    let url = extract_github_pr_url(stderr).expect("existing PR URL is extracted");

    assert_eq!(url, "https://github.com/chc-comp/chc-comp-2026/pull/17");
    assert_eq!(github_pr_number_from_url(&url), Some(17));
}

#[test]
fn chc_submit_pr_selector_falls_back_to_url_without_number() {
    let pr = ExistingChcSubmitPr {
        number: None,
        url: "https://github.com/chc-comp/chc-comp-2026/pull/17".to_string(),
        state: Some("OPEN".to_string()),
    };

    assert_eq!(
        pr.selector(),
        "https://github.com/chc-comp/chc-comp-2026/pull/17"
    );
}

#[test]
fn dry_run_github_account_check_records_policy_without_gh_probe() {
    let mut report = ChcZenodoSubmitReport::new(true);

    require_submission_github_account(
        &CHC_ZENODO_GITHUB_ACCOUNT_POLICY,
        "operator",
        false,
        None,
        Path::new("."),
        &mut report,
    )
    .expect("dry-run account warning succeeds");

    assert!(report.commands.is_empty());
    assert!(report.steps.iter().any(|step| step["name"]
        .as_str()
        .is_some_and(|name| name == "github_account_policy")));
    assert_eq!(
        report.outputs["github_account_policy"]["required_login"].as_str(),
        Some("operator")
    );
}

#[test]
fn github_submission_git_ssh_command_ignores_global_ssh_config() {
    let command = submission_git_ssh_command(Path::new(
        "/tmp/submission-keys/id_ed25519_operator_chc_comp_2026",
    ));

    assert!(command.contains("-F /dev/null"));
    assert!(command.contains("IdentitiesOnly=yes"));
    assert!(command.contains("BatchMode=yes"));
    assert!(command.contains("id_ed25519_operator_chc_comp_2026"));
}

#[test]
fn chc_submit_generates_fresh_branch_from_startup_source_pin() {
    let mut report = ChcZenodoSubmitReport::new(false);
    report.started_at_unix = 12345;
    let pin = SubmissionSourcePin {
        commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
    };

    let branch = resolve_chc_submit_branch(&pin, &mut report).expect("fresh branch");

    assert_eq!(
        branch,
        format!(
            "{}-0123456789ab-12345-{}",
            CHC_ZENODO_BRANCH_PREFIX,
            std::process::id()
        )
    );
    assert_eq!(
        report.outputs["submit_branch"]["policy"].as_str(),
        Some("fresh branch per live CHC-COMP submit; existing branches and PRs are rejected")
    );
}

#[test]
fn chc_submit_branch_validation_rejects_unsafe_names() {
    validate_chc_submit_branch_name("ay-chccomp-2026-submit-c00cc1171a")
        .expect("simple branch is valid");

    for branch in [
        "",
        "/bad",
        "bad/",
        "bad lock",
        "bad..name",
        "bad.lock",
        "bad@{x",
    ] {
        validate_chc_submit_branch_name(branch).expect_err("unsafe branch name should be rejected");
    }
}

#[cfg(feature = "submission-live")]
#[test]
fn chc_zenodo_metadata_uses_startup_source_pin() {
    let dir = make_temp_dir("ay-chc-zenodo-metadata-pin-test").expect("temp dir");
    let artifact = dir.join(CHC_ZENODO_ARTIFACT_NAME);
    let linux_ay = dir.join("ay");
    fs::write(&artifact, b"archive").expect("write artifact");
    fs::write(&linux_ay, b"binary").expect("write binary");
    let pin = SubmissionSourcePin {
        commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
    };

    let metadata = chc_zenodo_metadata(
        &chc_zenodo_submit_test_options(),
        &pin,
        &artifact,
        &linux_ay,
    )
    .expect("metadata");

    assert!(metadata["title"]
        .as_str()
        .expect("title")
        .contains("0123456789ab"));
    assert!(metadata["description"]
        .as_str()
        .expect("description")
        .contains("0123456789abcdef0123456789abcdef01234567"));
}

#[test]
fn chc_submit_git_default_bypasses_path_wrapper_when_system_git_exists() {
    if Path::new("/usr/bin/git").is_file() {
        assert_eq!(default_submission_git_program(), "/usr/bin/git");
    }

    let command =
        submission_git_command(["checkout", "-B", "ay-chccomp-2026-submit", "origin/main"]);
    if Path::new("/usr/bin/git").is_file() {
        assert_eq!(command[0], "/usr/bin/git");
    }
    assert_eq!(
        &command[1..],
        ["checkout", "-B", "ay-chccomp-2026-submit", "origin/main"]
    );
}

#[test]
fn chc_default_tracks_cover_all_comp26_set_files() {
    let expected = vec![
        "BOOL",
        "BV",
        "BV-Lin",
        "LRA-Lin",
        "LIA-Lin",
        "LIA",
        "LIA-Arrays",
        "LIA-Lin-Arrays",
        "ADT-LIA",
        "ADT-LIA-Arrays",
        "mixed_LIA_LRA",
    ];

    assert_eq!(CHC_ALLOWED_TRACKS, expected.as_slice());
    assert_eq!(
        split_tracks(CHC_DEFAULT_TRACKS).expect("default tracks should parse"),
        expected
    );
    assert_eq!(CHC_OFFICIAL_2026_TRACKS.len(), 9);
    assert_eq!(CHC_ALLOWED_TRACKS.len(), 11);
    let track_model = chc_track_model_json();
    assert_eq!(track_model["official_track_count"], 9);
    assert_eq!(track_model["local_set_file_category_count"], 11);
    assert_eq!(
        track_model["claim_policy"].as_str(),
        Some(CHC_TRACK_MODEL_CLAIM_POLICY)
    );

    let xml = chc_benchmark_xml(
        &CHC_ALLOWED_TRACKS
            .iter()
            .map(|track| (*track).to_string())
            .collect::<Vec<_>>(),
    );
    for track in CHC_ALLOWED_TRACKS {
        assert!(
            xml.contains(&format!("../chc-comp26-benchmarks/{track}.set")),
            "missing includesfile for {track}"
        );
    }
}

#[test]
fn chc_track_requirement_rejects_missing_comp26_set_file() {
    let tracks = chc_test_tracks_without("BOOL");

    let err = split_required_chc_tracks(&tracks).expect_err("missing BOOL must reject submission");

    assert!(err.to_string().contains("must include exactly all current"));
    assert!(err.to_string().contains("BOOL"));
}

#[test]
fn chc_generate_rejects_missing_comp26_set_file_category() {
    let dir = make_temp_dir("ay-chc-generate-missing-track-test").expect("temp dir");
    let output = dir.join("pr");
    let tracks = chc_test_tracks_without("mixed_LIA_LRA");

    let err = generate_chc(&output, CHC_DEFAULT_ARCHIVE_URL, &tracks)
        .expect_err("missing mixed_LIA_LRA must reject generated CHC PR files");

    assert!(err.to_string().contains("mixed_LIA_LRA"));
    assert!(!output
        .join("benchmark-defs")
        .join("ay.xml.template")
        .exists());
}

#[test]
fn chc_package_rejects_missing_comp26_set_file_category() {
    let dir = make_temp_dir("ay-chc-package-missing-track-test").expect("temp dir");
    let output = dir.join("package");
    let tracks = chc_test_tracks_without("BOOL");

    let err = package_chc(&output, None, CHC_DEFAULT_ARCHIVE_URL, &tracks)
        .expect_err("missing BOOL must reject generated CHC package");

    assert!(err.to_string().contains("BOOL"));
    assert!(
        !output.exists(),
        "package_chc should validate CHC tracks before creating output"
    );
}

#[test]
fn chc_verify_xml_tracks_rejects_missing_comp26_set_file_category() {
    let dir = make_temp_dir("ay-chc-verify-missing-track-test").expect("temp dir");
    let xml_path = dir.join("ay.xml.template");
    let tracks = CHC_ALLOWED_TRACKS
        .iter()
        .copied()
        .filter(|track| *track != "BOOL")
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();
    fs::write(&xml_path, chc_benchmark_xml(&tracks)).expect("write xml");

    let mut checks = Vec::new();
    let expected = CHC_ALLOWED_TRACKS
        .iter()
        .map(|track| (*track).to_string())
        .collect::<Vec<_>>();
    verify_chc_xml_tracks(&mut checks, &xml_path, &expected);

    assert_eq!(checks.len(), 1);
    assert_eq!(checks[0]["name"].as_str(), Some("xml:track_includes"));
    assert_eq!(checks[0]["status"].as_str(), Some("fail"));
    assert!(checks[0]["detail"]
        .as_str()
        .expect("detail")
        .contains("BOOL"));
}

#[test]
fn chc_worker_named_lanes_select_fixed_competition_cases() {
    let tracks = split_tracks(CHC_DEFAULT_TRACKS).expect("tracks");

    let triangle =
        chc_worker_benchmark_plan("triangle-location", &tracks, 1).expect("triangle plan");
    assert_eq!(
        triangle,
        ChcWorkerBenchmarkPlan::FixedCases(vec![
            ChcCompBenchmarkCase::new(
                "BV",
                "./eldarica-misc/BV/Consistency/ch-triangle-location-nr.1-bv_000.yml",
            ),
            ChcCompBenchmarkCase::new(
                "LIA",
                "./eldarica-misc/LIA/Consistency/ch-triangle-location-nr.1_000.yml",
            ),
        ])
    );

    let arrays = chc_worker_benchmark_plan("o0-arrays", &tracks, 1).expect("array plan");
    assert_eq!(
        arrays,
        ChcWorkerBenchmarkPlan::FixedCases(vec![
            ChcCompBenchmarkCase::new(
                "LIA-Arrays",
                "./hcai-bench/svcomp/O0/O0_eureka_01_true-unreach-call_000.yml",
            ),
            ChcCompBenchmarkCase::new(
                "LIA-Lin-Arrays",
                "./hcai-bench/svcomp/O0/O0_compact_false-unreach-call_000.yml",
            ),
        ])
    );

    let recursive = chc_worker_benchmark_plan("recursive-adt", &tracks, 1).expect("recursive plan");
    assert_eq!(
        recursive,
        ChcWorkerBenchmarkPlan::FixedCases(vec![ChcCompBenchmarkCase::new(
            "ADT-LIA",
            "./ADTRem/clam/goal21_000.yml",
        )])
    );
}

#[test]
fn chc_worker_track_lanes_only_sample_the_named_track() {
    let tracks = split_tracks(CHC_DEFAULT_TRACKS).expect("tracks");

    let plan = chc_worker_benchmark_plan("track-BV", &tracks, 2).expect("track plan");

    assert_eq!(
        plan,
        ChcWorkerBenchmarkPlan::TrackSamples {
            tracks: vec!["BV".to_string()],
            samples_per_track: 2,
        }
    );
}

#[test]
fn chc_worker_package_lanes_do_not_expand_to_all_track_smoke() {
    let tracks = split_tracks(CHC_DEFAULT_TRACKS).expect("tracks");

    let plan = chc_worker_benchmark_plan("package-preflight", &tracks, 1).expect("package plan");

    assert!(matches!(plan, ChcWorkerBenchmarkPlan::PackageOnly(_)));
}

fn chc_test_tracks_without(missing: &str) -> String {
    CHC_ALLOWED_TRACKS
        .iter()
        .copied()
        .filter(|track| *track != missing)
        .collect::<Vec<_>>()
        .join(",")
}
