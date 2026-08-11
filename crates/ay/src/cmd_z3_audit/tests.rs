//! Unit tests for `super` (cmd_z3_audit.rs).
//! Extracted verbatim to keep the production module readable.

use super::*;

#[test]
fn z3_audit_requests_the_native_chc_certificate_format() {
    assert!(
        CHC_CERTIFICATE_FILENAME.ends_with(".chccert"),
        "the CHC solver rejects generic .smt2 proof output"
    );
}

#[test]
fn portfolio_mode_is_a_valid_chc_stats_envelope() {
    let payload = serde_json::to_vec(&json!({
        "mode": "portfolio",
        "chc_evidence_manifest": {}
    }))
    .expect("serialize stats envelope");
    let parsed = unique_chc_stats_json(&[], &payload).expect("accept CHC portfolio stats");
    assert_eq!(parsed["mode"], "portfolio");
}

#[test]
fn embedded_compatibility_inventory_is_complete_and_honestly_scoped() {
    let inventory = load_compatibility_inventory().expect("embedded compatibility inventory");

    assert_eq!(inventory.schema, COMPATIBILITY_INVENTORY_SCHEMA);
    assert_eq!(inventory.cli_subset.len(), 3);
    assert_eq!(
        inventory.full_replacement.len(),
        BROADER_SURFACE_SPECS.len() + 1,
        "the extra row is the UNSAT proof surface"
    );
    assert!(!inventory.claims.universal_drop_in_replacement);
    assert!(!inventory.claims.full_z3_cli_compatibility);

    let checks = check_compatibility_inventory(&inventory, Z3AuditScope::CliSubset);
    assert!(
        checks.iter().all(|check| check.status == CheckStatus::Pass),
        "embedded inventory should pass the scoped audit: {:?}",
        checks
            .iter()
            .map(|check| (check.id, check.finding.as_str()))
            .collect::<Vec<_>>()
    );
}

#[test]
fn missing_private_docs_do_not_fail_compatibility_checks() {
    let inventory = load_compatibility_inventory().expect("embedded compatibility inventory");
    let dir = tempfile::tempdir().expect("tempdir");

    let compatibility = check_private_compatibility_doc(
        &dir.path().join("the development design notes"),
        &inventory,
    );
    let cli_reference = check_cli_reference(&dir.path().join("the development design notes"));

    assert_eq!(compatibility.status, CheckStatus::Pass);
    assert_eq!(cli_reference.status, CheckStatus::Pass);
    assert!(compatibility.finding.contains("not shipped"));
    assert!(cli_reference.finding.contains("not shipped"));
}

#[test]
fn workspace_root_marker_does_not_require_private_docs() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("Cargo.toml"), "[workspace]\n").expect("workspace manifest");
    fs::create_dir_all(dir.path().join("crates/ay")).expect("crate directory");
    fs::write(
        dir.path().join(WORKSPACE_MARKER),
        "[package]\nname = \"ay\"\n",
    )
    .expect("ay manifest");

    assert!(is_ay_workspace_root(dir.path()));
    assert!(!dir.path().join("docs").exists());
}

#[test]
fn matrix_parser_reads_only_requested_section_rows() {
    let doc = "# Z3 Compatibility\n\
                   ## Release-Gated Compatibility Surface\n\
                   | Surface | Status | What |\n\
                   |---|---|---|\n\
                   | CLI invocation | Ready | ok |\n\
                   ## Broader Z3 Compatibility Honesty Ledger\n\
                   | Surface | Status | What |\n\
                   |---|---|---|\n\
                   | SMT-LIB input | Partial | gap |\n";

    let launch = matrix_rows(doc, LAUNCH_GATED_HEADING);
    assert_eq!(launch.len(), 1);
    assert_eq!(launch[0].surface, "CLI invocation");
    assert_eq!(launch[0].status, "Ready");

    let broader = matrix_rows(doc, BROADER_LEDGER_HEADING);
    assert_eq!(broader.len(), 1);
    assert_eq!(broader[0].surface, "SMT-LIB input");
    assert_eq!(broader[0].status, "Partial");
}

#[test]
fn non_ready_rows_names_statuses() {
    let rows = vec![
        MatrixRow {
            surface: "CLI invocation".to_string(),
            status: "Ready".to_string(),
        },
        MatrixRow {
            surface: "SMT-LIB input".to_string(),
            status: "Partial".to_string(),
        },
    ];

    assert_eq!(non_ready_rows(&rows), vec!["SMT-LIB input=Partial"]);
}

#[test]
fn non_ready_rows_fail_full_replacement_audit() {
    let rows = vec![
        MatrixRow {
            surface: "Lean4 proof replay".to_string(),
            status: "Not Ready".to_string(),
        },
        MatrixRow {
            surface: "CHC certificate replay".to_string(),
            status: "Partial".to_string(),
        },
    ];

    assert_eq!(
        non_ready_rows(&rows),
        vec![
            "Lean4 proof replay=Not Ready",
            "CHC certificate replay=Partial"
        ]
    );
    assert_eq!(
        non_passing_rows(&rows),
        vec![
            "Lean4 proof replay=Not Ready",
            "CHC certificate replay=Partial"
        ]
    );
    assert!(!status_is_audit_pass(Some("Not Ready")));
}

#[test]
fn non_ready_surface_does_not_make_full_replacement_ready() {
    let surfaces = vec![AuditSurface {
        id: "lean_replay",
        surface: "Lean4 proof replay".to_string(),
        status: CheckStatus::Fail,
        current: "0/1 Ready in embedded compatibility inventory (inventory status: Not Ready)"
            .to_string(),
        goal: "1/1 external replay runner implemented".to_string(),
        missing: "external replay runner evidence; inventory status is Not Ready".to_string(),
        command: None,
        source: None,
        source_status: Some("Not Ready".to_string()),
    }];

    assert!(!full_replacement_ready(
        Z3AuditScope::FullReplacement,
        0,
        &surfaces
    ));
    assert!(!full_replacement_ready(
        Z3AuditScope::CliSubset,
        0,
        &surfaces
    ));
    assert!(!full_replacement_ready(
        Z3AuditScope::FullReplacement,
        1,
        &surfaces
    ));
}

#[test]
fn public_source_failure_blocks_full_replacement_ready() {
    let surfaces = vec![AuditSurface {
        id: "public_source_build",
        surface: "Public-source build".to_string(),
        status: CheckStatus::Fail,
        current: "0/1 public-source build packet passed".to_string(),
        goal: "1/1 public-source build packet passed".to_string(),
        missing: "public-source packet is missing".to_string(),
        command: None,
        source: None,
        source_status: None,
    }];
    assert!(!full_replacement_ready(
        Z3AuditScope::FullReplacement,
        0,
        &surfaces
    ));
}

#[test]
fn broader_surface_fails_when_not_ready() {
    let rows = vec![MatrixRow {
        surface: "Rust embedding".to_string(),
        status: "Not Ready".to_string(),
    }];
    let spec = BROADER_SURFACE_SPECS
        .iter()
        .find(|spec| spec.id == "rust_embedding")
        .expect("rust embedding spec");

    let surface = broader_surface(spec, &rows, None, None);

    assert_eq!(surface.status, CheckStatus::Fail);
    assert_eq!(
        surface.current,
        "0/1 Ready in embedded compatibility inventory (inventory status: Not Ready)"
    );
    assert_eq!(
        surface.missing,
        "downstream consumer build/test evidence from public source; inventory status is Not Ready"
    );
}

#[test]
fn broader_surface_uses_cached_baseline_evidence_over_doc_status() {
    let rows = vec![MatrixRow {
        surface: "DIMACS CNF input".to_string(),
        status: "Not Ready".to_string(),
    }];
    let spec = surface_spec("dimacs_cnf_input").expect("DIMACS spec");
    let evidence = CachedSurfaceEvidence {
        status: CheckStatus::Pass,
        current: "1/1 scoreboard; total=5; wrong=0; invalid=0".to_string(),
        goal: spec.goal.to_string(),
        missing: "none".to_string(),
        command: spec.command.to_string(),
        source: "the development design notes".to_string(),
    };

    let surface = broader_surface(spec, &rows, None, Some(&evidence));

    assert_eq!(surface.status, CheckStatus::Pass);
    assert_eq!(
        surface.current,
        "1/1 scoreboard; total=5; wrong=0; invalid=0"
    );
    assert_eq!(surface.missing, "none");
    assert_eq!(surface.source_status.as_deref(), Some("Not Ready"));
}

#[test]
fn unsat_proof_surface_passes_from_live_rows_not_doc_status() {
    let broader_rows = vec![MatrixRow {
        surface: "UNSAT proofs".to_string(),
        status: "Not Ready".to_string(),
    }];
    let proof_inventory = vec![ProofInventoryRow::pass(
        "dimacs_drat_external",
        "DIMACS DRAT external replay",
        "1/1 external DRAT replay command passed",
        "1/1 external DRAT replay command passes with drat-trim",
        "cargo test -p ay-sat --test integration test_drat",
        "command passed",
    )];

    let surface = unsat_proof_surface(&broader_rows, &proof_inventory);

    assert_eq!(surface.status, CheckStatus::Pass);
    assert_eq!(surface.missing, "none");
    assert_eq!(surface.source_status.as_deref(), Some("Not Ready"));
}

#[test]
fn public_clone_log_requires_full_public_build_pass() {
    let dir = tempfile::tempdir().expect("tempdir");
    let pass_log = dir.path().join("public-clone-check.log");
    fs::write(
        &pass_log,
        "public-clone-check: PASS cargo_metadata_locked\n\
             public-clone-check: PASS release_build\n\
             public-clone-check: version ay test\n\
             public-clone-check: overall PASS\n",
    )
    .unwrap();
    let fail_log = dir.path().join("public-clone-check-fail.log");
    fs::write(
        &fail_log,
        "public-clone-check: PASS cargo_metadata_locked\n\
             public-clone-check: FAIL release_build\n\
             public-clone-check: overall PASS\n",
    )
    .unwrap();

    assert!(public_clone_log_passes(&pass_log));
    assert!(!public_clone_log_passes(&fail_log));
}

#[test]
fn public_clone_log_current_for_head_rejects_stale_public_build() {
    let dir = tempfile::tempdir().expect("tempdir");
    let pass_log = dir.path().join("public-clone-check.log");
    fs::write(
            &pass_log,
            "public-clone-check: provenance requested_url=https://example.invalid/ay.git origin=https://example.invalid/ay.git requested_ref=default commit=abcdef1234567890 short=abcdef1 mode=build\n\
             public-clone-check: PASS cargo_metadata_locked\n\
             public-clone-check: PASS release_build\n\
             public-clone-check: version ay test\n\
             public-clone-check: overall PASS\n",
        )
        .unwrap();

    assert!(public_clone_log_current_for_head(
        &pass_log,
        Some("abcdef1234567890ffff")
    ));
    assert!(!public_clone_log_current_for_head(
        &pass_log,
        Some("1234567890abcdef")
    ));
}

#[test]
fn scoreboard_current_for_head_rejects_stale_scoreboard() {
    let current = json!({
        "source_commit": "abcdef1234567890",
        "soundness": true,
        "variants": {
            "default": {
                "summary": {
                    "total": 5,
                    "wrong": 0,
                    "invalid": 0
                }
            }
        }
    });
    let stale = json!({
        "source_commit": "1234567890abcdef",
        "soundness": true,
        "variants": {
            "default": {
                "summary": {
                    "total": 5,
                    "wrong": 0,
                    "invalid": 0
                }
            }
        }
    });

    assert!(scoreboard_current_for_head(
        &current,
        Some("abcdef1234567890ffff")
    ));
    assert!(scoreboard_passes(&current));
    assert!(!scoreboard_current_for_head(
        &stale,
        Some("abcdef1234567890ffff")
    ));
}

#[test]
fn commit_matches_audited_tree_allows_evidence_only_descendant() {
    fn git(repo: &Path, args: &[&str]) -> String {
        let output = ProcessCommand::new("git")
            .args(args)
            .current_dir(repo)
            .output()
            .unwrap_or_else(|error| panic!("failed to run git {args:?}: {error}"));
        assert!(
            output.status.success(),
            "git {args:?} failed\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stdout).trim().to_string()
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo = dir.path();
    git(repo, &["init"]);
    git(repo, &["config", "user.email", "ay-audit@example.invalid"]);
    git(repo, &["config", "user.name", "AY Audit Test"]);
    git(repo, &["config", "commit.gpgsign", "false"]);
    fs::write(repo.join("src.txt"), "base\n").unwrap();
    git(repo, &["add", "src.txt"]);
    git(repo, &["commit", "-m", "base"]);
    let base = git(repo, &["rev-parse", "HEAD"]);

    fs::create_dir_all(repo.join("the development design notes")).unwrap();
    fs::write(repo.join("the development design notes"), "{}\n").unwrap();
    git(repo, &["add", "the development design notes"]);
    git(repo, &["commit", "-m", "evidence"]);
    let evidence_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(commit_matches_audited_tree(repo, &base, &evidence_head));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &evidence_head
    ));

    fs::create_dir_all(repo.join("crates/ay/src")).unwrap();
    fs::write(repo.join("crates/ay/src/cmd_z3_audit.rs"), "audit only\n").unwrap();
    git(repo, &["add", "crates/ay/src/cmd_z3_audit.rs"]);
    git(repo, &["commit", "-m", "audit cli only"]);
    let audit_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(commit_matches_audited_tree(repo, &base, &audit_head));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &audit_head
    ));

    fs::write(
        repo.join("crates/ay/src/cmd_consumer_smoke.rs"),
        "consumer smoke cli only\n",
    )
    .unwrap();
    git(repo, &["add", "crates/ay/src/cmd_consumer_smoke.rs"]);
    git(repo, &["commit", "-m", "consumer smoke cli only"]);
    let consumer_smoke_cli_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(
        repo,
        &base,
        &consumer_smoke_cli_head
    ));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &consumer_smoke_cli_head
    ));

    fs::create_dir_all(repo.join("crates/ay/tests/group_cli")).unwrap();
    fs::write(
        repo.join("crates/ay/tests/group_cli.rs"),
        "mod group_cli;\n",
    )
    .unwrap();
    fs::write(
        repo.join("crates/ay/tests/group_cli/consumer_smoke_cli.rs"),
        "consumer smoke cli regression tests\n",
    )
    .unwrap();
    git(
        repo,
        &[
            "add",
            "crates/ay/tests/group_cli.rs",
            "crates/ay/tests/group_cli/consumer_smoke_cli.rs",
        ],
    );
    git(repo, &["commit", "-m", "consumer smoke tests"]);
    let consumer_smoke_tests_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(
        repo,
        &base,
        &consumer_smoke_tests_head
    ));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &consumer_smoke_tests_head
    ));

    fs::create_dir_all(repo.join("scripts")).unwrap();
    fs::write(
        repo.join("scripts/model-checker-consumer-smoke-check.sh"),
        "#!/bin/sh\n",
    )
    .unwrap();
    git(
        repo,
        &["add", "scripts/model-checker-consumer-smoke-check.sh"],
    );
    git(repo, &["commit", "-m", "downstream smoke wrapper"]);
    let downstream_smoke_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(
        repo,
        &base,
        &downstream_smoke_head
    ));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &downstream_smoke_head
    ));

    fs::write(repo.join("scripts/consumer-smoke-lib.sh"), "#!/bin/sh\n").unwrap();
    git(repo, &["add", "scripts/consumer-smoke-lib.sh"]);
    git(repo, &["commit", "-m", "downstream smoke lib"]);
    let downstream_smoke_lib_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(
        repo,
        &base,
        &downstream_smoke_lib_head
    ));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &downstream_smoke_lib_head
    ));

    fs::write(repo.join("scripts/consumer-smoke-check.sh"), "#!/bin/sh\n").unwrap();
    git(repo, &["add", "scripts/consumer-smoke-check.sh"]);
    git(repo, &["commit", "-m", "downstream smoke orchestrator"]);
    let downstream_smoke_orchestrator_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(
        repo,
        &base,
        &downstream_smoke_orchestrator_head
    ));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &downstream_smoke_orchestrator_head
    ));

    fs::write(
        repo.join("scripts/quantifier_consumer-smoke-check.sh"),
        "#!/bin/sh\n",
    )
    .unwrap();
    git(repo, &["add", "scripts/quantifier_consumer-smoke-check.sh"]);
    git(repo, &["commit", "-m", "quantifier_consumer smoke wrapper"]);
    let quantifier_consumer_smoke_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(
        repo,
        &base,
        &quantifier_consumer_smoke_head
    ));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &quantifier_consumer_smoke_head
    ));

    fs::write(
        repo.join("scripts/certificate_consumer-smoke-check.sh"),
        "#!/bin/sh\n",
    )
    .unwrap();
    git(
        repo,
        &["add", "scripts/certificate_consumer-smoke-check.sh"],
    );
    git(
        repo,
        &["commit", "-m", "certificate_consumer smoke wrapper"],
    );
    let certificate_consumer_smoke_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(
        repo,
        &base,
        &certificate_consumer_smoke_head
    ));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &certificate_consumer_smoke_head
    ));

    fs::write(repo.join("scripts/tla2-smoke-check.sh"), "#!/bin/sh\n").unwrap();
    git(repo, &["add", "scripts/tla2-smoke-check.sh"]);
    git(repo, &["commit", "-m", "tla2 smoke wrapper"]);
    let tla2_smoke_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(repo, &base, &tla2_smoke_head));
    assert!(commit_matches_solver_evidence_tree(
        repo,
        &base,
        &tla2_smoke_head
    ));

    fs::write(repo.join("src.txt"), "changed\n").unwrap();
    git(repo, &["add", "src.txt"]);
    git(repo, &["commit", "-m", "code"]);
    let code_head = git(repo, &["rev-parse", "HEAD"]);
    assert!(!commit_matches_audited_tree(repo, &base, &code_head));
    assert!(!commit_matches_solver_evidence_tree(
        repo, &base, &code_head
    ));
}

#[test]
fn artifact_scan_skips_nested_repo_clones() {
    let dir = tempfile::tempdir().expect("tempdir");
    let reports = dir.path().join("reports");
    let nested_repo = reports.join("clean-origin-main");
    fs::create_dir_all(nested_repo.join(".git")).unwrap();
    fs::write(reports.join("public-clone-check.log"), "root\n").unwrap();
    fs::write(nested_repo.join("public-clone-check.log"), "nested\n").unwrap();

    let files = find_named_files(&reports, "public-clone-check", ".log", 20);

    assert_eq!(files, vec![reports.join("public-clone-check.log")]);
}

#[test]
fn downstream_smoke_packet_uses_schema_launch_candidate_field() {
    let pass = json!({
        "overall": {"status": "PASS", "exit_code": 0},
        "evidence": {"launch_candidate": true},
    });
    let not_launch = json!({
        "overall": {"status": "PASS", "exit_code": 0},
        "evidence": {"launch_candidate": false},
    });

    assert!(downstream_smoke_packet_passes(&pass));
    assert!(!downstream_smoke_packet_passes(&not_launch));
}

#[test]
fn downstream_smoke_evidence_must_match_current_head_when_known() {
    let current = "abcdef1234567890";
    let current_packet = json!({
        "ay": {
            "commit": "abcdef12",
            "commit_full": current,
        }
    });
    let stale_packet = json!({
        "evidence": {
            "ay": {
                "commit": "12345678",
                "commit_full": "1234567890abcdef",
            }
        }
    });

    assert!(downstream_smoke_packet_current_for_head(
        &current_packet,
        Some(current)
    ));
    assert!(!downstream_smoke_packet_current_for_head(
        &stale_packet,
        Some(current)
    ));
    assert!(commit_matches_head("abcdef12", current));
    assert!(!commit_matches_head("12345678", current));
}

#[test]
fn downstream_log_commit_parser_detects_stale_smoke_logs() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("downstream-smoke.log");
    fs::write(
        &path,
        "consumer-smoke-check: mode=full ay_commit=57dfb72b63\n",
    )
    .unwrap();

    assert_eq!(downstream_log_commit(&path).as_deref(), Some("57dfb72b63"));
    assert!(downstream_log_current_for_head(
        &path,
        Some("57dfb72b63000000000000000000000000000000")
    ));
    assert!(!downstream_log_current_for_head(
        &path,
        Some("dc1cb66aba000000000000000000000000000000")
    ));
}

#[test]
fn model_checker_consumer_failure_parser_reports_expectation_mismatch_without_ansi() {
    let line = "Testing: chained_store_same_block.rs::test_two_stores_same_block ... \u{1b}[0;31mFAIL\u{1b}[0m (expected PROOF, got CTREX)";

    assert_eq!(
        parse_model_checker_consumer_failure_line(line),
        Some(
            "chained_store_same_block.rs::test_two_stores_same_block (expected PROOF, got CTREX)"
                .to_string()
        )
    );
}

#[test]
fn model_checker_consumer_failure_parser_classifies_stronger_unknown_proof() {
    let line =
        "Testing: probe.rs::case ... \u{1b}[0;31mFAIL\u{1b}[0m (expected UNKNOWN, got PROOF)";

    assert_eq!(parse_model_checker_consumer_failure_line(line), None);
    assert_eq!(
        parse_model_checker_consumer_stronger_unknown_proof_line(line),
        Some("probe.rs::case".to_string())
    );
}

#[test]
fn model_validation_packet_requires_zero_invalid_and_checked_models() {
    let pass = json!({
        "status": "pass",
        "invalid_model_count": 0,
        "model_checked_count": 12,
    });
    let unchecked = json!({
        "status": "pass",
        "invalid_model_count": 0,
        "model_checked_count": 0,
    });
    let invalid = json!({
        "status": "pass",
        "invalid_model_count": 1,
        "model_checked_count": 12,
    });

    assert!(model_validation_packet_passes(&pass));
    assert!(!model_validation_packet_passes(&unchecked));
    assert!(!model_validation_packet_passes(&invalid));
}

#[test]
fn latest_eval_result_with_reference_filters_solver_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    let older = repo_root.join("evals/results/chccomp-2025-extra-small-lia/2026-01-01T00-00-00Z");
    let newer = repo_root.join("evals/results/chccomp-2025-extra-small-lia/2026-01-02T00-00-00Z");
    fs::create_dir_all(&older).unwrap();
    fs::create_dir_all(&newer).unwrap();
    fs::write(
        older.join("results.json"),
        serde_json::to_string(&json!({"comparison": {"reference_solver": "z3"}})).unwrap(),
    )
    .unwrap();
    fs::write(
        newer.join("results.json"),
        serde_json::to_string(&json!({"comparison": {"reference_solver": "golem"}})).unwrap(),
    )
    .unwrap();

    let (path, value) =
        latest_eval_result_with_reference(repo_root, "chccomp-2025-extra-small-lia", "z3")
            .expect("z3 packet");

    assert!(path.ends_with("2026-01-01T00-00-00Z/results.json"));
    assert_eq!(
        value
            .pointer("/comparison/reference_solver")
            .and_then(Value::as_str),
        Some("z3")
    );
}

#[test]
fn chc_surface_rejects_empty_or_reference_error_packets() {
    fn write_chc_packet(
        repo_root: &Path,
        eval_id: &str,
        run_id: &str,
        reference_solver: &str,
        benchmark_count: u64,
        ref_result: &str,
    ) {
        let dir = repo_root.join("evals/results").join(eval_id).join(run_id);
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": benchmark_count},
                "environment": {"git_commit": "current", "git_dirty": false},
                "comparison": {
                    "reference_solver": reference_solver,
                    "disagree": 0,
                },
                "comparisons": [{
                    "ay_result": "sat",
                    "ref_result": ref_result,
                    "agreement": if ref_result == "error" { "both_unknown" } else { "agree" },
                }]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    let verify_path = repo_root.join("the development design notes");
    fs::create_dir_all(verify_path.parent().unwrap()).unwrap();
    fs::write(
        verify_path,
        serde_json::to_string(&json!({
            "total": 1,
            "matches": 1,
            "sound_bugs": 0,
            "incomplete": 0,
            "reference_unknown": 0,
            "both_unknown": 0,
            "no_baseline": 0,
        }))
        .unwrap(),
    )
    .unwrap();

    write_chc_packet(
        repo_root,
        "chccomp-2025-extra-small-lia",
        "2026-01-01-z3",
        "z3",
        1,
        "sat",
    );
    write_chc_packet(
        repo_root,
        "chccomp-2025-extra-small-lia",
        "2026-01-02-golem",
        "golem",
        1,
        "sat",
    );
    write_chc_packet(
        repo_root,
        "chccomp-2025-lia-lin",
        "2026-01-03-z3",
        "z3",
        0,
        "sat",
    );
    write_chc_packet(
        repo_root,
        "chccomp-2025-lia-lin",
        "2026-01-04-golem",
        "golem",
        1,
        "error",
    );

    let evidence = chc_surface_evidence(repo_root, 3);

    assert_eq!(
        evidence.pointer("/status").and_then(Value::as_str),
        Some("fail_error")
    );
    let current = evidence
        .pointer("/current")
        .and_then(Value::as_str)
        .expect("current text");
    assert!(current.contains("z3_spacer_benchmarks=1"));
    assert!(current.contains("golem_reference_errors=1"));
    let missing = evidence
        .pointer("/missing")
        .and_then(Value::as_str)
        .expect("missing text");
    assert!(missing.contains("current Z3 Spacer packets with zero benchmarks"));
    assert!(missing.contains("golem_reference_errors=1"));
}

#[test]
fn chc_surface_rejects_all_unknown_comparison_packets() {
    fn write_all_unknown_packet(
        repo_root: &Path,
        eval_id: &str,
        run_id: &str,
        reference_solver: &str,
        benchmark_count: u64,
    ) {
        let dir = repo_root.join("evals/results").join(eval_id).join(run_id);
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": benchmark_count},
                "environment": {"git_commit": "current", "git_dirty": false},
                "comparison": {
                    "reference_solver": reference_solver,
                    "agree": 0,
                    "disagree": 0,
                    "both_solved": 0,
                },
                "comparisons": [{
                    "ay_result": "timeout",
                    "ref_result": "timeout",
                    "agreement": "both_unknown",
                }]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    let verify_path = repo_root.join("the development design notes");
    fs::create_dir_all(verify_path.parent().unwrap()).unwrap();
    fs::write(
        verify_path,
        serde_json::to_string(&json!({
            "total": 1,
            "matches": 1,
            "sound_bugs": 0,
            "incomplete": 0,
            "reference_unknown": 0,
            "both_unknown": 0,
            "no_baseline": 0,
        }))
        .unwrap(),
    )
    .unwrap();

    write_all_unknown_packet(
        repo_root,
        "chccomp-2025-extra-small-lia",
        "2026-01-01-z3",
        "z3",
        55,
    );
    write_all_unknown_packet(
        repo_root,
        "chccomp-2025-extra-small-lia",
        "2026-01-02-golem",
        "golem",
        55,
    );
    write_all_unknown_packet(
        repo_root,
        "chccomp-2025-lia-lin",
        "2026-01-03-z3",
        "z3",
        542,
    );
    write_all_unknown_packet(
        repo_root,
        "chccomp-2025-lia-lin",
        "2026-01-04-golem",
        "golem",
        542,
    );

    let evidence = chc_surface_evidence(repo_root, 3);

    assert_eq!(
        evidence.pointer("/status").and_then(Value::as_str),
        Some("fail_timeout")
    );
    let current = evidence
        .pointer("/current")
        .and_then(Value::as_str)
        .expect("current text");
    assert!(current.contains("z3_spacer_agree=0"));
    assert!(current.contains("golem_agree=0"));
    let missing = evidence
        .pointer("/missing")
        .and_then(Value::as_str)
        .expect("missing text");
    assert!(missing.contains("current Z3 Spacer packets with no concrete agreements"));
    assert!(missing.contains("golem_agree=0"));
}

#[test]
fn chc_surface_reports_ref_only_timeout_as_fail_timeout() {
    fn write_ref_only_packet(
        repo_root: &Path,
        eval_id: &str,
        run_id: &str,
        reference_solver: &str,
    ) {
        let dir = repo_root.join("evals/results").join(eval_id).join(run_id);
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": 2},
                "environment": {"git_commit": "current", "git_dirty": false},
                "comparison": {
                    "reference_solver": reference_solver,
                    "agree": 1,
                    "disagree": 0,
                    "both_solved": 1,
                    "ref_only": 1,
                },
                "comparisons": [
                    {
                        "benchmark": "agree.smt2",
                        "ay_result": "sat",
                        "ref_result": "sat",
                        "agreement": "agree",
                    },
                    {
                        "benchmark": "timeout.smt2",
                        "ay_result": "timeout",
                        "ref_result": "sat",
                        "agreement": "ref_only",
                    }
                ]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    let verify_path = repo_root.join("the development design notes");
    fs::create_dir_all(verify_path.parent().unwrap()).unwrap();
    fs::write(
        verify_path,
        serde_json::to_string(&json!({
            "total": 4,
            "matches": 4,
            "sound_bugs": 0,
            "incomplete": 0,
            "reference_unknown": 0,
            "both_unknown": 0,
            "no_baseline": 0,
        }))
        .unwrap(),
    )
    .unwrap();

    write_ref_only_packet(
        repo_root,
        "chccomp-2025-extra-small-lia",
        "2026-01-01-z3",
        "z3",
    );
    write_ref_only_packet(
        repo_root,
        "chccomp-2025-extra-small-lia",
        "2026-01-02-golem",
        "golem",
    );
    write_ref_only_packet(repo_root, "chccomp-2025-lia-lin", "2026-01-03-z3", "z3");
    write_ref_only_packet(
        repo_root,
        "chccomp-2025-lia-lin",
        "2026-01-04-golem",
        "golem",
    );

    let evidence = chc_surface_evidence(repo_root, 3);

    assert_eq!(
        evidence.pointer("/status").and_then(Value::as_str),
        Some("fail_timeout")
    );
    let current = evidence
        .pointer("/current")
        .and_then(Value::as_str)
        .expect("current text");
    assert!(current.contains("z3_spacer_reference_solved_missing=2"));
    assert!(current.contains("z3_spacer_reference_solved_missing_ay_results=timeout:2"));
    assert!(current.contains("golem_reference_solved_missing=2"));
    assert!(current.contains("golem_reference_solved_missing_ay_results=timeout:2"));
    let missing = evidence
        .pointer("/missing")
        .and_then(Value::as_str)
        .expect("missing text");
    assert!(missing.contains("z3_spacer_reference_solved_missing=2"));
    assert!(missing.contains("golem_reference_solved_missing=2"));
}

#[test]
fn reference_solved_missing_failure_status_classifies_ay_outcomes() {
    let mut counts = BTreeMap::new();
    counts.insert("unknown".to_string(), 3);
    assert_eq!(
        reference_solved_missing_failure_status(&counts),
        CheckStatus::FailUnknown
    );

    counts.insert("timeout".to_string(), 1);
    assert_eq!(
        reference_solved_missing_failure_status(&counts),
        CheckStatus::FailTimeout
    );

    counts.insert("error".to_string(), 1);
    assert_eq!(
        reference_solved_missing_failure_status(&counts),
        CheckStatus::FailError
    );
}

#[test]
fn eval_result_current_for_head_rejects_stale_clean_packets() {
    let current_head = "abcdef1234567890";
    let current = json!({
        "environment": {
            "git_commit": "abcdef12",
            "git_dirty": false,
        }
    });
    let stale = json!({
        "environment": {
            "ay_build_commit": "1234567890abcdef",
            "git_dirty": false,
        }
    });
    let missing = json!({
        "environment": {
            "git_dirty": false,
        }
    });

    assert!(eval_result_current_for_head(&current, Some(current_head)));
    assert!(!eval_result_current_for_head(&stale, Some(current_head)));
    assert!(!eval_result_current_for_head(&missing, Some(current_head)));
    assert!(eval_result_current_for_head(&missing, None));
}

#[test]
fn smt_refresh_plan_selects_missing_stale_and_dirty_packets() {
    fn write_packet(repo_root: &Path, eval_id: &str, commit: &str, dirty: bool) {
        let dir = repo_root
            .join("evals/results")
            .join(eval_id)
            .join("2026-01-01T00-00-00Z");
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": 1},
                "environment": {"git_commit": commit, "git_dirty": dirty},
                "comparison": {"agree": 1, "disagree": 0},
                "comparisons": [{
                    "benchmark": "case.smt2",
                    "ay_result": "sat",
                    "ref_result": "sat",
                    "agreement": "agree",
                }]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    write_packet(repo_root, "smt-local-suite", "current", false);
    write_packet(repo_root, "smt-smtcomp-qf-bv", "stale", false);
    write_packet(repo_root, "smt-smtcomp-qf-abv", "current", true);
    let evals = vec![
        "smt-local-suite".to_string(),
        "smt-smtcomp-qf-bv".to_string(),
        "smt-smtcomp-qf-abv".to_string(),
        "smt-smtcomp-qf-uf".to_string(),
    ];

    let plan = smt_evidence_refresh_plan(
        repo_root,
        Path::new("./target/release/ay"),
        Some("current"),
        &evals,
        SmtRefreshPolicy::StaleOrMissing,
        Some(7.0),
        Some(2),
        "z3",
    )
    .expect("refresh plan");

    assert_eq!(
        plan.evals_to_run,
        vec![
            "smt-smtcomp-qf-bv".to_string(),
            "smt-smtcomp-qf-abv".to_string(),
            "smt-smtcomp-qf-uf".to_string(),
        ]
    );
    assert_eq!(plan.skipped, vec!["smt-local-suite:current"]);
    assert_eq!(
        plan.selected,
        vec![
            "smt-smtcomp-qf-bv:stale",
            "smt-smtcomp-qf-abv:dirty",
            "smt-smtcomp-qf-uf:missing",
        ]
    );
    assert_eq!(
            plan.command.as_deref(),
            Some("./target/release/ay bench run smt-smtcomp-qf-bv smt-smtcomp-qf-abv smt-smtcomp-qf-uf --ay ./target/release/ay --timeout 7 --runs 2 --reference-solver z3")
        );
}

#[test]
fn smtlib_surface_rejects_execution_errors_and_empty_packets() {
    fn write_smt_packet(
        repo_root: &Path,
        eval_id: &str,
        benchmark_count: u64,
        ay_result: &str,
        ref_result: &str,
    ) {
        let dir = repo_root
            .join("evals/results")
            .join(eval_id)
            .join("2026-01-01T00-00-00Z");
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": benchmark_count},
                "environment": {"git_commit": "current", "git_dirty": false},
                "comparison": {
                    "agree": 1,
                    "disagree": 0,
                    "ay_only": 0,
                    "ref_only": 0,
                    "both_solved": 1,
                },
                "comparisons": [{
                    "benchmark": "case.smt2",
                    "ay_result": ay_result,
                    "ref_result": ref_result,
                    "agreement": "agree",
                }]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    for eval_id in [
        "smt-local-suite",
        "smt-smtcomp-qf-lia",
        "smt-smtcomp-qf-lra",
        "smt-smtcomp-qf-bv",
        "smt-smtcomp-qf-abv",
        "smt-smtcomp-qf-uf",
        "smt-smtcomp-qf-alia",
        "smt-smtcomp-qf-auflia",
    ] {
        write_smt_packet(repo_root, eval_id, 1, "sat", "sat");
    }
    write_smt_packet(repo_root, "smt-smtcomp-qf-lra", 0, "sat", "sat");
    write_smt_packet(repo_root, "smt-smtcomp-qf-abv", 1, "error", "sat");

    let evidence = smtlib_surface_evidence(repo_root);

    assert_eq!(
        evidence.pointer("/status").and_then(Value::as_str),
        Some("fail_error")
    );
    let current = evidence
        .pointer("/current")
        .and_then(Value::as_str)
        .expect("current text");
    assert!(current.contains("8/8 current-code eval packets"));
    assert!(
        current.contains("eval_statuses=pass:6,fail:1,fail_timeout:0,fail_unknown:0,fail_error:1")
    );
    assert!(current.contains("smt-smtcomp-qf-abv{status=fail_error"));
    assert!(current.contains("ay_errors=1"));
    assert!(current.contains("ref_errors=0"));
    let missing = evidence
        .pointer("/missing")
        .and_then(Value::as_str)
        .expect("missing text");
    assert!(missing.contains("zero-benchmark eval packets: smt-smtcomp-qf-lra"));
    assert!(missing.contains("1 AY execution errors"));
}

#[test]
fn latest_eval_result_ignores_scorecard_only_outputs() {
    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    let eval_dir = repo_root.join("evals/results/smt-local-suite");
    let scorecard_dir = eval_dir.join("z3-audit-current");
    let raw_dir = eval_dir.join("2026-01-01T00-00-00Z");
    fs::create_dir_all(&scorecard_dir).unwrap();
    fs::create_dir_all(&raw_dir).unwrap();
    fs::write(
        scorecard_dir.join("results.json"),
        serde_json::to_string_pretty(&json!({
            "environment": {"git_commit": "current", "git_dirty": false},
            "mode": "dev",
            "results": [{
                "eval_id": "smt-local-suite",
                "score": {"total": 1, "solved": 1}
            }]
        }))
        .unwrap(),
    )
    .unwrap();
    fs::write(
        raw_dir.join("results.json"),
        serde_json::to_string_pretty(&json!({
            "settings": {"benchmark_count": 1},
            "environment": {"git_commit": "current", "git_dirty": false},
            "comparison": {
                "agree": 1,
                "disagree": 0,
                "ay_only": 0,
                "ref_only": 0,
                "both_solved": 1
            },
            "comparisons": [{
                "benchmark": "case.smt2",
                "ay_result": "sat",
                "ref_result": "sat",
                "agreement": "agree"
            }]
        }))
        .unwrap(),
    )
    .unwrap();

    let (path, value) = latest_eval_result(repo_root, "smt-local-suite").expect("raw packet");

    assert!(path.to_string_lossy().contains("2026-01-01T00-00-00Z"));
    assert_eq!(value_u64(&value, "/settings/benchmark_count"), 1);
}

#[test]
fn smtlib_surface_command_uses_native_bench_run_for_qf_abv() {
    let command = surface_spec("smtlib_input").expect("SMT-LIB spec").command;

    assert!(command.contains("cargo build --release --locked -p ay --features bench --bin ay"));
    assert!(command.contains("./target/release/ay bench run smt-local-suite"));
    assert!(command.contains("smt-smtcomp-qf-abv"));
    assert!(command.contains("--reference-solver z3"));
    assert!(!command.contains("for eval"));
    assert!(!command.contains("scripts/"));
}

#[test]
fn smt_refresh_plan_selects_stale_dirty_and_missing_packets() {
    fn write_packet(repo_root: &Path, eval_id: &str, commit: &str, dirty: bool) {
        let dir = repo_root
            .join("evals/results")
            .join(eval_id)
            .join("2026-01-01T00-00-00Z");
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": 1},
                "environment": {"git_commit": commit, "git_dirty": dirty},
                "comparison": {
                    "agree": 1,
                    "disagree": 0,
                    "ay_only": 0,
                    "ref_only": 0,
                    "both_solved": 1
                },
                "comparisons": [{
                    "benchmark": "case.smt2",
                    "ay_result": "sat",
                    "ref_result": "sat",
                    "agreement": "agree"
                }]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    write_packet(repo_root, "smt-local-suite", "current", false);
    write_packet(repo_root, "smt-smtcomp-qf-lia", "old", false);
    write_packet(repo_root, "smt-smtcomp-qf-bv", "current", true);
    write_packet(repo_root, "smt-smtcomp-qf-auflia", "old", true);
    let evals = vec![
        "smt-local-suite".to_string(),
        "smt-smtcomp-qf-lia".to_string(),
        "smt-smtcomp-qf-bv".to_string(),
        "smt-smtcomp-qf-abv".to_string(),
        "smt-smtcomp-qf-auflia".to_string(),
    ];

    let plan = smt_evidence_refresh_plan(
        repo_root,
        Path::new("/tmp/ay"),
        Some("current"),
        &evals,
        SmtRefreshPolicy::StaleOrMissing,
        Some(7.5),
        Some(2),
        "z3",
    )
    .expect("plan");

    assert_eq!(
        plan.evals_to_run,
        vec![
            "smt-smtcomp-qf-lia",
            "smt-smtcomp-qf-bv",
            "smt-smtcomp-qf-abv",
            "smt-smtcomp-qf-auflia",
        ]
    );
    assert_eq!(
            plan.selected.join(","),
            "smt-smtcomp-qf-lia:stale,smt-smtcomp-qf-bv:dirty,smt-smtcomp-qf-abv:missing,smt-smtcomp-qf-auflia:stale_dirty"
        );
    assert_eq!(plan.skipped.join(","), "smt-local-suite:current");
    let command = plan.command.expect("planned command");
    assert!(command.contains("/tmp/ay bench run smt-smtcomp-qf-lia smt-smtcomp-qf-bv smt-smtcomp-qf-abv smt-smtcomp-qf-auflia"));
    assert!(command.contains("--ay /tmp/ay"));
    assert!(command.contains("--timeout 7.5"));
    assert!(command.contains("--runs 2"));
    assert!(command.contains("--reference-solver z3"));
}

#[test]
fn smt_refresh_missing_policy_does_not_run_stale_packets() {
    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    let stale_dir = repo_root.join("evals/results/smt-smtcomp-qf-lia/2026-01-01T00-00-00Z");
    fs::create_dir_all(&stale_dir).unwrap();
    fs::write(
        stale_dir.join("results.json"),
        serde_json::to_string_pretty(&json!({
            "settings": {"benchmark_count": 1},
            "environment": {"git_commit": "old", "git_dirty": false},
            "comparison": {"agree": 1},
        }))
        .unwrap(),
    )
    .unwrap();
    let evals = vec![
        "smt-smtcomp-qf-lia".to_string(),
        "smt-smtcomp-qf-abv".to_string(),
    ];

    let plan = smt_evidence_refresh_plan(
        repo_root,
        Path::new("/tmp/ay"),
        Some("current"),
        &evals,
        SmtRefreshPolicy::Missing,
        None,
        None,
        "z3",
    )
    .expect("plan");

    assert_eq!(plan.evals_to_run, vec!["smt-smtcomp-qf-abv"]);
    assert_eq!(plan.selected.join(","), "smt-smtcomp-qf-abv:missing");
    assert_eq!(plan.skipped.join(","), "smt-smtcomp-qf-lia:stale");
}

#[test]
fn smtlib_surface_reports_ref_only_timeout_as_fail_timeout() {
    fn write_ref_only_packet(repo_root: &Path, eval_id: &str) {
        let dir = repo_root
            .join("evals/results")
            .join(eval_id)
            .join("2026-01-01T00-00-00Z");
        fs::create_dir_all(&dir).unwrap();
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": 1},
                "environment": {"git_commit": "current", "git_dirty": false},
                "comparison": {
                    "agree": 0,
                    "disagree": 0,
                    "ay_only": 0,
                    "ref_only": 1,
                    "both_solved": 0,
                },
                "comparisons": [{
                    "benchmark": "case.smt2",
                    "ay_result": "timeout",
                    "ref_result": "sat",
                    "agreement": "ref_only",
                }]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    for eval_id in [
        "smt-local-suite",
        "smt-smtcomp-qf-lia",
        "smt-smtcomp-qf-lra",
        "smt-smtcomp-qf-bv",
        "smt-smtcomp-qf-abv",
        "smt-smtcomp-qf-uf",
        "smt-smtcomp-qf-alia",
        "smt-smtcomp-qf-auflia",
    ] {
        write_ref_only_packet(repo_root, eval_id);
    }

    let evidence = smtlib_surface_evidence(repo_root);

    assert_eq!(
        evidence.pointer("/status").and_then(Value::as_str),
        Some("fail_timeout")
    );
    let current = evidence
        .pointer("/current")
        .and_then(Value::as_str)
        .expect("current text");
    assert!(current.contains("reference_solved_missing=8"));
    assert!(current.contains("reference_solved_missing_ay_results=timeout:8"));
    assert!(
        current.contains("eval_statuses=pass:0,fail:0,fail_timeout:8,fail_unknown:0,fail_error:0")
    );
    assert!(current.contains("smt-smtcomp-qf-abv{status=fail_timeout"));
    assert!(current
        .contains("top_reference_solved_missing=case.smt2:ay=timeout,ref=sat,ay_time=0.000s"));
    let missing = evidence
        .pointer("/missing")
        .and_then(Value::as_str)
        .expect("missing text");
    assert!(missing.contains("reference_solved_missing=8"));
}

#[test]
fn smtlib_surface_reports_ref_only_unknown_with_benchmark_examples() {
    fn write_packet(repo_root: &Path, eval_id: &str, ay_result: &str, agreement: &str) {
        let dir = repo_root
            .join("evals/results")
            .join(eval_id)
            .join("2026-01-01T00-00-00Z");
        fs::create_dir_all(&dir).unwrap();
        let ref_only = if agreement == "ref_only" { 1 } else { 0 };
        let agree = if agreement == "agree" { 1 } else { 0 };
        fs::write(
            dir.join("results.json"),
            serde_json::to_string_pretty(&json!({
                "settings": {"benchmark_count": 1},
                "environment": {"git_commit": "current", "git_dirty": false},
                "comparison": {
                    "agree": agree,
                    "disagree": 0,
                    "ay_only": 0,
                    "ref_only": ref_only,
                    "both_solved": agree,
                },
                "comparisons": [{
                    "file": "benchmarks/smtcomp/QF_ABV/bubble_sort22.c.smt2",
                    "ay_result": ay_result,
                    "ay_time_sec": 2.75,
                    "ref_result": "unsat",
                    "agreement": agreement,
                }]
            }))
            .unwrap(),
        )
        .unwrap();
    }

    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    for eval_id in [
        "smt-local-suite",
        "smt-smtcomp-qf-lia",
        "smt-smtcomp-qf-lra",
        "smt-smtcomp-qf-bv",
        "smt-smtcomp-qf-uf",
        "smt-smtcomp-qf-alia",
        "smt-smtcomp-qf-auflia",
    ] {
        write_packet(repo_root, eval_id, "sat", "agree");
    }
    write_packet(repo_root, "smt-smtcomp-qf-abv", "unknown", "ref_only");

    let evidence = smtlib_surface_evidence(repo_root);

    assert_eq!(
        evidence.pointer("/status").and_then(Value::as_str),
        Some("fail_unknown")
    );
    let current = evidence
        .pointer("/current")
        .and_then(Value::as_str)
        .expect("current text");
    assert!(
        current.contains("eval_statuses=pass:7,fail:0,fail_timeout:0,fail_unknown:1,fail_error:0")
    );
    assert!(current.contains("smt-smtcomp-qf-abv{status=fail_unknown"));
    assert!(current.contains("reference_solved_missing_ay_results=unknown:1"));
    assert!(current.contains(
        "top_reference_solved_missing=bubble_sort22.c.smt2:ay=unknown,ref=unsat,ay_time=2.750s"
    ));
    let missing = evidence
        .pointer("/missing")
        .and_then(Value::as_str)
        .expect("missing text");
    assert!(missing.contains("reference_solved_missing=1"));
}

#[test]
fn dimacs_surface_reports_reference_only_as_fail_timeout() {
    let dir = tempfile::tempdir().expect("tempdir");
    let repo_root = dir.path();
    let scoreboard = repo_root.join("the development design notes");
    fs::create_dir_all(scoreboard.parent().unwrap()).unwrap();
    fs::write(
        &scoreboard,
        serde_json::to_string_pretty(&json!({
            "source_commit": "current",
            "source_dirty": false,
            "soundness": true,
            "variants": {
                "default": {
                    "summary": {
                        "total": 2,
                        "solved": 1,
                        "solved_sat": 1,
                        "solved_unsat": 0,
                        "unknown": 1,
                        "wrong": 0,
                        "invalid": 0,
                        "par2_total": 60.5,
                        "timeout_sec": 30.0
                    }
                }
            },
            "reference_comparison": {
                "default": {
                    "cadical": {
                        "definitive_disagree": 0,
                        "reference_only_solved": 1
                    }
                }
            }
        }))
        .unwrap(),
    )
    .unwrap();

    let evidence = dimacs_surface_evidence(repo_root);

    assert_eq!(
        evidence.pointer("/status").and_then(Value::as_str),
        Some("fail_timeout")
    );
    let current = evidence
        .pointer("/current")
        .and_then(Value::as_str)
        .expect("current text");
    assert!(current.contains("reference_only_solved=1"));
    let missing = evidence
        .pointer("/missing")
        .and_then(Value::as_str)
        .expect("missing text");
    assert!(missing.contains("reference_only_solved=1"));
}

#[test]
fn surface_summary_expands_partial_rows_with_numbers() {
    let launch_rows = vec![MatrixRow {
        surface: "CLI invocation".to_string(),
        status: "Ready".to_string(),
    }];
    let broader_rows = vec![
        MatrixRow {
            surface: "SMT-LIB input".to_string(),
            status: "Partial".to_string(),
        },
        MatrixRow {
            surface: "UNSAT proofs".to_string(),
            status: "Partial".to_string(),
        },
    ];
    let checks = vec![
        AuditCheck::pass("basic_smt_transcript", "ok"),
        AuditCheck::pass("z3_param_discovery_smoke", "ok"),
        AuditCheck::pass("z3_tactic_catalog_smoke", "ok"),
    ];
    let proof_inventory = vec![ProofInventoryRow::fail(
        "smt_alethe_external_replay",
        "SMT Alethe external replay",
        "0/1 external Alethe replay command run by this audit",
        "1/1 SMT Alethe proof emitted and accepted by an external checker",
        "ay z3-audit --scope full-replacement",
        "inventory-only mode suppressed execution",
    )];

    let surfaces = build_surface_summary(
        Z3AuditScope::FullReplacement,
        &launch_rows,
        &broader_rows,
        &proof_inventory,
        &checks,
        &BTreeMap::new(),
    );

    let smtlib = surfaces
        .iter()
        .find(|surface| surface.id == "smtlib_input")
        .expect("SMT-LIB surface");
    assert_eq!(smtlib.status, CheckStatus::Fail);
    assert!(smtlib.current.contains("0/1 Ready"));
    assert!(smtlib.goal.contains("1/1 current-code differential packet"));
    assert!(smtlib.missing.contains("inventory status is Partial"));

    let proofs = surfaces
        .iter()
        .find(|surface| surface.id == "unsat_proofs")
        .expect("proof surface");
    assert_eq!(
        proofs.current,
        "0/1 proof/certificate rows pass in this audit; 1/1 fail"
    );
    assert!(proofs.goal.contains("1/1 proof/certificate rows pass"));
}

#[test]
fn c_api_ffi_surface_reports_native_smoke_without_overclaiming() {
    let launch_rows = vec![MatrixRow {
        surface: "CLI invocation".to_string(),
        status: "Ready".to_string(),
    }];
    let broader_rows = vec![MatrixRow {
        surface: "C API / FFI".to_string(),
        status: "Experimental".to_string(),
    }];
    let checks = vec![
        AuditCheck::pass("basic_smt_transcript", "ok"),
        AuditCheck::pass("z3_param_discovery_smoke", "ok"),
        AuditCheck::pass("z3_tactic_catalog_smoke", "ok"),
        AuditCheck::pass(C_API_FFI_SMOKE_ID, "command passed"),
    ];
    let proof_inventory = Vec::new();

    let surfaces = build_surface_summary(
        Z3AuditScope::FullReplacement,
        &launch_rows,
        &broader_rows,
        &proof_inventory,
        &checks,
        &BTreeMap::new(),
    );

    let ffi = surfaces
        .iter()
        .find(|surface| surface.id == "c_api_ffi")
        .expect("C API / FFI surface");
    assert_eq!(ffi.status, CheckStatus::Pass);
    assert_eq!(
        ffi.current,
        "1/1 ay-ffi ABI/API consumer/header smoke passed in this audit"
    );
    assert_eq!(ffi.missing, "none");
}

#[test]
fn models_surface_uses_default_model_validation_smoke() {
    let launch_rows = vec![MatrixRow {
        surface: "CLI invocation".to_string(),
        status: "Ready".to_string(),
    }];
    let broader_rows = vec![MatrixRow {
        surface: "Models".to_string(),
        status: "Not Ready".to_string(),
    }];
    let checks = vec![
            AuditCheck::pass("basic_smt_transcript", "ok"),
            AuditCheck::pass("z3_param_discovery_smoke", "ok"),
            AuditCheck::pass("z3_tactic_catalog_smoke", "ok"),
            AuditCheck::fail(
                SMT_MODEL_VALIDATION_SMOKE_ID,
                "model_validation_tests_passed=15/16; failed=1; model_checked_count=15; invalid_model_count=0; capability_failures=1; failing_tests=smt_soundness_gate::auflira::test_gate_qf_auflira_sat_validates_model",
            ),
        ];

    let surfaces = build_surface_summary(
        Z3AuditScope::FullReplacement,
        &launch_rows,
        &broader_rows,
        &Vec::new(),
        &checks,
        &BTreeMap::new(),
    );

    let models = surfaces
        .iter()
        .find(|surface| surface.id == "models")
        .expect("Models surface");
    assert_eq!(models.status, CheckStatus::Fail);
    assert!(models.current.contains("15/16"));
    assert!(models.missing.contains("auflira"));
}

#[test]
fn cargo_test_summary_parser_reads_failed_model_validation_counts() {
    let text = "\
test smt_soundness_gate::uf::test_gate_qf_uf_sat_validates_model ... ok\n\
test smt_soundness_gate::auflira::test_gate_qf_auflira_sat_validates_model ... FAILED\n\
test result: FAILED. 15 passed; 1 failed; 0 ignored; 0 measured; 186 filtered out; finished in 13.40s\n";

    let summary = parse_cargo_test_summary(text).expect("summary");
    assert_eq!(summary.passed_tests, 15);
    assert_eq!(summary.failed_tests, 1);
    assert_eq!(summary.filtered_out, 186);
    assert_eq!(
        failing_cargo_tests(text),
        vec!["smt_soundness_gate::auflira::test_gate_qf_auflira_sat_validates_model"]
    );
    assert!(
        model_validation_finding(Some(summary), &failing_cargo_tests(text))
            .contains("capability_failures=1")
    );
}

#[test]
fn rendered_repo_command_forces_live_cargo_run() {
    assert_eq!(
        rendered_repo_command(
            "cargo",
            "cargo test -p ay --features=\"cli\" --test group_cli z3_compat_args"
        ),
        "CARGO_SKIP_CACHE=1 cargo test -p ay --features=\"cli\" --test group_cli z3_compat_args"
    );
    assert_eq!(
        rendered_repo_command(
            "cargo",
            "CARGO_SKIP_CACHE=1 cargo test -p ay --features=\"cli\""
        ),
        "CARGO_SKIP_CACHE=1 cargo test -p ay --features=\"cli\""
    );
    assert_eq!(
        rendered_repo_command("bash", "bash scripts/check_doc_reality.sh"),
        "bash scripts/check_doc_reality.sh"
    );
}

#[test]
fn strip_shell_quotes_dequotes_argv_tokens() {
    // The bug: splitting `--features="cli"` and passing it as raw argv made
    // cargo see the feature name `"cli"` (with quotes), which does not exist.
    assert_eq!(strip_shell_quotes("--features=\"cli\""), "--features=cli");
    assert_eq!(strip_shell_quotes("\"cli\""), "cli");
    assert_eq!(strip_shell_quotes("--features=cli"), "--features=cli");
    assert_eq!(strip_shell_quotes("group_cli"), "group_cli");
    assert_eq!(strip_shell_quotes("cargo"), "cargo");
    // Full split of the audit command yields valid argv tokens.
    let argv = "cargo test -p ay --features=\"cli\" --test group_cli verify_proof_8771"
        .split_whitespace()
        .map(strip_shell_quotes)
        .collect::<Vec<_>>();
    assert_eq!(
        argv,
        vec![
            "cargo",
            "test",
            "-p",
            "ay",
            "--features=cli",
            "--test",
            "group_cli",
            "verify_proof_8771",
        ]
    );
}

#[test]
fn proof_inventory_commands_are_native_not_legacy_shell_authority() {
    let args = Z3AuditArgs {
        repo_root: None,
        ay: None,
        z3: "z3".to_string(),
        reference_cache: PathBuf::from(DEFAULT_REFERENCE_CACHE),
        write_reference_cache: None,
        refresh_smt_evidence: false,
        smt_refresh_dry_run: false,
        smt_refresh_policy: SmtRefreshPolicy::StaleOrMissing,
        smt_eval: Vec::new(),
        smt_timeout: None,
        smt_runs: None,
        smt_reference_solver: None,
        scope: Z3AuditScope::FullReplacement,
        run_doc_reality: false,
        run_cli_tests: false,
        run_proof_tests: false,
        run_alethe_replay: false,
        inventory_only: true,
        alethe_checker: "carcara".to_string(),
        alethe_problem: PathBuf::from("problem.smt2"),
        proof_work_dir: None,
        summary_json: None,
    };

    let rows = build_proof_inventory(
        &args,
        Path::new("."),
        Path::new("ay"),
        None,
        None,
        Path::new(DEFAULT_REFERENCE_CACHE),
        false,
        false,
    );
    assert!(!rows.is_empty());
    assert!(rows
        .iter()
        .all(|row| !row.command.contains("verify_proofs.sh")));
    assert!(rows.iter().any(|row| row.id == "ay_sat_lrat_text_packet"
        && row.command == "CARGO_SKIP_CACHE=1 cargo test -p ay-sat --test integration test_lrat"));
    assert!(rows.iter().any(|row| row.id == "lrat_binary_external"
            && row.command
                == "CARGO_SKIP_CACHE=1 cargo build -p ay-lrat-check --bin ay-lrat-check && CARGO_SKIP_CACHE=1 cargo test -p ay-sat --test group_drat lrat_binary_external_php32"));
    assert!(rows.iter().all(|row| row.current.contains('/')));
    assert!(rows.iter().all(|row| row.goal.contains('/')));
}

#[test]
fn reference_cache_loads_checked_schema_and_hashes() {
    let repo_root = resolve_repo_root(None).expect("repo root");
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("reference-cache.json");
    let value = valid_reference_cache_value(&repo_root);
    fs::write(&path, serde_json::to_string_pretty(&value).unwrap()).unwrap();

    let cache = load_reference_cache(&repo_root, &path).expect("load reference cache");

    assert_eq!(cache.z3_version, "Z3 version 4.test");
    assert_eq!(
        cache.basic_smt_transcript.input_sha256,
        sha256_hex(BASIC_SMT_TRANSCRIPT_INPUT.as_bytes())
    );
    assert_eq!(cache.chc_obligations.obligations.len(), 1);
    assert_eq!(
        cache
            .surface_evidence
            .get("dimacs_cnf_input")
            .expect("surface evidence")
            .status,
        CheckStatus::Pass
    );
}

#[test]
fn reference_cache_rejects_wrong_schema() {
    let repo_root = resolve_repo_root(None).expect("repo root");
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("reference-cache.json");
    fs::write(&path, r#"{"schema":"wrong"}"#).unwrap();

    let error = load_reference_cache(&repo_root, &path).unwrap_err();

    assert!(error.to_string().contains("schema mismatch"));
}

#[test]
fn reference_cache_rejects_stale_basic_transcript_input() {
    let repo_root = resolve_repo_root(None).expect("repo root");
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("reference-cache.json");
    let mut value = valid_reference_cache_value(&repo_root);
    value["basic_smt_transcript"]["input_sha256"] = json!("stale");
    fs::write(&path, serde_json::to_string_pretty(&value).unwrap()).unwrap();

    let error = load_reference_cache(&repo_root, &path).unwrap_err();

    assert!(error
        .to_string()
        .contains("basic SMT transcript input hash mismatch"));
}

#[test]
fn cached_chc_validation_rejects_missing_obligation_hash() {
    let repo_root = resolve_repo_root(None).expect("repo root");
    let dir = tempfile::tempdir().expect("tempdir");
    let obligation = dir.path().join("obligation.smt2");
    fs::write(&obligation, "(assert false)\n(check-sat)\n").unwrap();
    let mut obligations = BTreeMap::new();
    obligations.insert(
        "cached-but-not-emitted".to_string(),
        CachedObligation {
            name: "cached.smt2".to_string(),
            status_code: Some(0),
            stdout_first_line: "unsat".to_string(),
        },
    );
    let cache = ReferenceCache {
        path: dir.path().join("reference-cache.json"),
        z3_version: "Z3 version 4.test".to_string(),
        basic_smt_transcript: CachedTranscript {
            input_sha256: sha256_hex(BASIC_SMT_TRANSCRIPT_INPUT.as_bytes()),
            status_code: Some(0),
            stdout: "sat\n((x 1))\n".to_string(),
            stderr: String::new(),
        },
        chc_obligations: CachedChcObligations {
            problem_sha256: sha256_file(&repo_root.join(CHC_CANARY_PROBLEM)).unwrap(),
            obligations,
        },
        surface_evidence: BTreeMap::new(),
    };
    let bytes = fs::read(&obligation).expect("read obligation");
    let authenticated = AuthenticatedChcArtifact {
        path: fs::canonicalize(&obligation).expect("canonical obligation"),
        sha256: sha256_hex(&bytes),
        bytes,
    };

    let error = validate_cached_chc_obligations(
        &cache,
        &repo_root.join(CHC_CANARY_PROBLEM),
        &[authenticated],
    )
    .unwrap_err();

    assert!(error.to_string().contains("absent from cache"));
}

fn chc_manifest_artifact(path: &Path, role: &str) -> Value {
    let physical_path = fs::canonicalize(path).expect("canonical artifact path");
    let mut artifact = json!({
        "schema": "ay.chc-proof-artifact-digest/v1",
        "schema_version": 1,
        "role": role,
        "sha256": sha256_file(&physical_path).expect("artifact digest"),
        "bytes": fs::metadata(&physical_path).expect("artifact metadata").len(),
        "path": physical_path,
    });
    if role == "replay-obligation" {
        artifact["kind"] = json!("safety");
    }
    artifact
}

fn chc_stats_json(certificate: &Path, obligations: &[&Path]) -> Value {
    json!({
        "mode": "chc",
        "result": "unsat",
        "chc_evidence_manifest": {
            "schema": "ay.chc-evidence-manifest/v1",
            "artifacts": {
                "proof": {
                    "status": "hash-bound",
                    "artifact": chc_manifest_artifact(certificate, "proof-certificate"),
                },
                "replay_obligations": {
                    "status": "hash-bound",
                    "artifacts": obligations
                        .iter()
                        .map(|path| chc_manifest_artifact(path, "replay-obligation"))
                        .collect::<Vec<_>>(),
                },
            },
        },
    })
}

#[test]
fn chc_manifest_artifacts_ignore_planted_legacy_obligation_directory() {
    let dir = tempfile::tempdir().expect("tempdir");
    let certificate = dir.path().join("chc-certificate.smt2");
    fs::write(&certificate, "(set-logic HORN)\n; certificate\n").expect("certificate");
    let obligations_dir = dir
        .path()
        .join("chc-certificate.smt2.chc-obligations-123-0");
    fs::create_dir(&obligations_dir).expect("unique obligations directory");
    let obligation = obligations_dir.join("000-safety.smt2");
    fs::write(
        &obligation,
        "(set-logic HORN)\n(assert false)\n(check-sat)\n",
    )
    .expect("obligation");

    let stale_dir = dir.path().join("chc-obligations");
    fs::create_dir(&stale_dir).expect("legacy stale directory");
    let stale = stale_dir.join("stale.smt2");
    fs::write(&stale, "(check-sat)\n").expect("stale obligation");

    let stats =
        serde_json::to_vec(&chc_stats_json(&certificate, &[&obligation])).expect("serialize stats");
    let emitted = emitted_chc_artifacts_from_streams(b"unsat\n", &stats, &certificate)
        .expect("authenticate manifest artifacts");

    assert_eq!(
        emitted.certificate.path,
        fs::canonicalize(&certificate).expect("physical certificate")
    );
    assert_eq!(
        emitted
            .obligations
            .iter()
            .map(|artifact| artifact.path.clone())
            .collect::<Vec<_>>(),
        vec![fs::canonicalize(&obligation).expect("physical obligation")]
    );
    assert!(!emitted
        .obligations
        .iter()
        .any(|artifact| artifact.path == stale));
    assert_eq!(
        emitted.obligations[0].bytes,
        fs::read(&obligation).expect("read obligation bytes")
    );
}

#[test]
fn cached_chc_validation_uses_authenticated_bytes_after_path_replacement() {
    let repo_root = resolve_repo_root(None).expect("repo root");
    let dir = tempfile::tempdir().expect("tempdir");
    let certificate = dir.path().join("chc-certificate.smt2");
    fs::write(&certificate, "certificate\n").expect("certificate");
    let obligations_dir = dir
        .path()
        .join("chc-certificate.smt2.chc-obligations-123-5");
    fs::create_dir(&obligations_dir).expect("obligations directory");
    let obligation = obligations_dir.join("000-safety.smt2");
    let original = b"(assert false)\n(check-sat)\n";
    fs::write(&obligation, original).expect("obligation");

    let stats =
        serde_json::to_vec(&chc_stats_json(&certificate, &[&obligation])).expect("serialize stats");
    let emitted = emitted_chc_artifacts_from_streams(b"", &stats, &certificate)
        .expect("authenticate same-run artifacts");
    let original_sha256 = sha256_hex(original);

    fs::rename(
        &obligation,
        obligations_dir.join("authenticated-original.smt2"),
    )
    .expect("move authenticated inode");
    fs::write(&obligation, "(check-sat)\n").expect("plant replacement");

    let mut cached_obligations = BTreeMap::new();
    cached_obligations.insert(
        original_sha256,
        CachedObligation {
            name: "000-safety.smt2".to_string(),
            status_code: Some(0),
            stdout_first_line: "unsat".to_string(),
        },
    );
    let cache = ReferenceCache {
        path: dir.path().join("reference-cache.json"),
        z3_version: "Z3 version 4.test".to_string(),
        basic_smt_transcript: CachedTranscript {
            input_sha256: sha256_hex(BASIC_SMT_TRANSCRIPT_INPUT.as_bytes()),
            status_code: Some(0),
            stdout: "sat\n((x 1))\n".to_string(),
            stderr: String::new(),
        },
        chc_obligations: CachedChcObligations {
            problem_sha256: sha256_file(&repo_root.join(CHC_CANARY_PROBLEM)).unwrap(),
            obligations: cached_obligations,
        },
        surface_evidence: BTreeMap::new(),
    };

    assert_eq!(
        validate_cached_chc_obligations(
            &cache,
            &repo_root.join(CHC_CANARY_PROBLEM),
            &emitted.obligations,
        )
        .expect("validate captured evidence"),
        1
    );
    assert_eq!(emitted.obligations[0].bytes, original);
}

#[test]
fn command_capture_with_stdin_passes_exact_authenticated_bytes() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = b"(assert false)\n(check-sat)\n";
    let output = run_command_capture_with_stdin(dir.path(), Path::new("sh"), &["-c", "cat"], input)
        .expect("run stdin echo helper");

    assert!(output.status.success());
    assert_eq!(output.stdout, input);
    assert!(output.stderr.is_empty());
}

#[test]
fn chc_manifest_artifacts_reject_digest_or_length_mismatch() {
    let dir = tempfile::tempdir().expect("tempdir");
    let certificate = dir.path().join("chc-certificate.smt2");
    fs::write(&certificate, "certificate\n").expect("certificate");
    let obligations_dir = dir
        .path()
        .join("chc-certificate.smt2.chc-obligations-123-1");
    fs::create_dir(&obligations_dir).expect("unique obligations directory");
    let obligation = obligations_dir.join("000-safety.smt2");
    fs::write(&obligation, "(assert false)\n(check-sat)\n").expect("obligation");

    let mut bad_digest = chc_stats_json(&certificate, &[&obligation]);
    bad_digest["chc_evidence_manifest"]["artifacts"]["replay_obligations"]["artifacts"][0]
        ["sha256"] = json!("0".repeat(64));
    let stderr = serde_json::to_vec(&bad_digest).expect("serialize bad digest stats");
    let error = emitted_chc_artifacts_from_streams(b"", &stderr, &certificate)
        .expect_err("digest mismatch must fail closed");
    assert!(error.to_string().contains("digest mismatch"), "{error:#}");

    let mut bad_length = chc_stats_json(&certificate, &[&obligation]);
    bad_length["chc_evidence_manifest"]["artifacts"]["proof"]["artifact"]["bytes"] = json!(1);
    let stderr = serde_json::to_vec(&bad_length).expect("serialize bad length stats");
    let error = emitted_chc_artifacts_from_streams(b"", &stderr, &certificate)
        .expect_err("length mismatch must fail closed");
    assert!(
        error.to_string().contains("byte length mismatch"),
        "{error:#}"
    );

    let mut missing_kind = chc_stats_json(&certificate, &[&obligation]);
    missing_kind["chc_evidence_manifest"]["artifacts"]["replay_obligations"]["artifacts"][0]
        ["kind"] = json!("");
    let stderr = serde_json::to_vec(&missing_kind).expect("serialize empty-kind stats");
    let error = emitted_chc_artifacts_from_streams(b"", &stderr, &certificate)
        .expect_err("empty obligation kind must fail closed");
    assert!(
        error.to_string().contains("empty obligation kind"),
        "{error:#}"
    );
}

#[test]
fn chc_manifest_artifacts_require_one_unique_physical_obligation_parent() {
    let dir = tempfile::tempdir().expect("tempdir");
    let certificate = dir.path().join("chc-certificate.smt2");
    fs::write(&certificate, "certificate\n").expect("certificate");
    let first_dir = dir
        .path()
        .join("chc-certificate.smt2.chc-obligations-123-2");
    let second_dir = dir
        .path()
        .join("chc-certificate.smt2.chc-obligations-123-3");
    fs::create_dir(&first_dir).expect("first obligations directory");
    fs::create_dir(&second_dir).expect("second obligations directory");
    let first = first_dir.join("000-initiation.smt2");
    let second = second_dir.join("001-safety.smt2");
    fs::write(&first, "(assert false)\n(check-sat)\n").expect("first obligation");
    fs::write(&second, "(assert false)\n(check-sat)\n").expect("second obligation");

    let stats = serde_json::to_vec(&chc_stats_json(&certificate, &[&first, &second]))
        .expect("serialize mixed-parent stats");
    let error = emitted_chc_artifacts_from_streams(b"", &stats, &certificate)
        .expect_err("mixed same-run directories must fail closed");
    assert!(
        error
            .to_string()
            .contains("mixes replay obligation directories"),
        "{error:#}"
    );
}

#[test]
fn chc_manifest_artifacts_require_the_requested_certificate_path() {
    let dir = tempfile::tempdir().expect("tempdir");
    let certificate = dir.path().join("chc-certificate.smt2");
    let planted = dir.path().join("other-certificate.smt2");
    fs::write(&certificate, "same-run certificate\n").expect("certificate");
    fs::write(&planted, "stale certificate\n").expect("planted certificate");
    let obligations_dir = dir
        .path()
        .join("chc-certificate.smt2.chc-obligations-123-4");
    fs::create_dir(&obligations_dir).expect("obligations directory");
    let obligation = obligations_dir.join("000-safety.smt2");
    fs::write(&obligation, "(assert false)\n(check-sat)\n").expect("obligation");

    let stats = serde_json::to_vec(&chc_stats_json(&planted, &[&obligation]))
        .expect("serialize wrong-proof stats");
    let error = emitted_chc_artifacts_from_streams(b"", &stats, &certificate)
        .expect_err("manifest proof must match requested path");
    assert!(
        error
            .to_string()
            .contains("not the requested same-run certificate"),
        "{error:#}"
    );
}

fn valid_reference_cache_value(repo_root: &Path) -> Value {
    json!({
        "schema": REFERENCE_CACHE_SCHEMA,
        "generated_at_unix_seconds": 1,
        "generator": {
            "z3_command": "z3",
            "z3_version": "Z3 version 4.test",
            "ay": "ay",
            "ay_version": "ay test",
        },
        "basic_smt_transcript": {
            "id": BASIC_SMT_TRANSCRIPT_ID,
            "input_sha256": sha256_hex(BASIC_SMT_TRANSCRIPT_INPUT.as_bytes()),
            "status_code": 0,
            "stdout": "sat\n((x 1))\n",
            "stderr": "",
        },
        "chc_certificate_obligations": {
            "problem": CHC_CANARY_PROBLEM,
            "problem_sha256": sha256_file(&repo_root.join(CHC_CANARY_PROBLEM)).unwrap(),
            "count": 1,
            "obligations": [
                {
                    "name": "obligation-000.smt2",
                    "sha256": "cached-obligation",
                    "status_code": 0,
                    "stdout_first_line": "unsat",
                    "stdout": "unsat\n",
                    "stderr": "",
                }
            ],
        },
        (SURFACE_EVIDENCE_KEY): {
            "schema": SURFACE_EVIDENCE_SCHEMA,
            "surfaces": [
                {
                    "id": "dimacs_cnf_input",
                    "status": "pass",
                    "current": "1/1 scoreboard",
                    "goal": "goal",
                    "missing": "none",
                    "command": "ay bench run sat",
                    "source": "the development design notes",
                }
            ],
        },
    })
}

#[cfg(unix)]
fn write_executable(dir: &Path, name: &str, body: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = dir.join(name);
    fs::write(&path, body).expect("write mock checker");
    let mut perms = fs::metadata(&path).expect("metadata").permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&path, perms).expect("chmod mock checker");
    path
}

#[test]
fn drat_trim_candidates_exclude_repo_bin_mock() {
    // The checked-in bin/drat-trim shim was a `#!/bin/bash; exit 0` no-op and
    // a documented soundness liability. It must never be a discovery candidate.
    let candidates = drat_trim_candidates();
    assert!(
        candidates.iter().all(|p| p != Path::new("bin/drat-trim")),
        "bin/drat-trim must not be a drat-trim discovery candidate: {candidates:?}"
    );
}

#[cfg(unix)]
#[test]
fn exit_zero_mock_is_not_a_genuine_drat_trim() {
    let dir = env::temp_dir().join(format!(
        "ay-audit-drat-genuine-exit0-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create probe dir");
    let mock = write_executable(&dir, "drat-trim", "#!/bin/sh\nexit 0\n");
    assert!(
        !drat_trim_is_genuine(&mock),
        "an exit-0 no-op must be rejected: it never reports `s VERIFIED`"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn external_tool_inventory_lists_all_audit_dependencies() {
    let repo = env::temp_dir();
    let inv = external_tool_inventory(&repo, "z3", "carcara");
    let names: Vec<&str> = inv.iter().map(|t| t.name).collect();
    assert_eq!(
        names,
        vec!["z3", "drat-trim", "carcara", "lean", "cadical", "golem"],
        "inventory must list every external full-replacement dependency"
    );
    for tool in &inv {
        assert!(!tool.purpose.is_empty(), "{} missing purpose", tool.name);
        assert!(
            !tool.install_hint.is_empty(),
            "{} missing install hint",
            tool.name
        );
        // Every entry must serialize to JSON for the machine-readable summary.
        assert!(tool.to_json().is_object());
    }
    // drat-trim carries a genuineness verdict (it has a no-op-mock control);
    // the rest are presence-only.
    let drat = inv
        .iter()
        .find(|t| t.name == "drat-trim")
        .expect("drat-trim");
    assert!(drat.genuine.is_some());
    let z3 = inv.iter().find(|t| t.name == "z3").expect("z3");
    assert!(z3.genuine.is_none());
}

#[cfg(unix)]
#[test]
fn always_verified_mock_is_not_a_genuine_drat_trim() {
    // Passes the positive control but must be caught by the negative control:
    // a real checker reports `s NOT VERIFIED` for a bogus refutation.
    let dir = env::temp_dir().join(format!(
        "ay-audit-drat-genuine-always-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create probe dir");
    let mock = write_executable(&dir, "drat-trim", "#!/bin/sh\necho 's VERIFIED'\n");
    assert!(
        !drat_trim_is_genuine(&mock),
        "an always-VERIFIED mock must be rejected by the negative control"
    );
    let _ = fs::remove_dir_all(&dir);
}
