// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_cli::launch_packet_cli` to preserve test FQNs.

#[test]
#[timeout(30_000)]
fn launch_packet_dry_run_writes_metadata_sidecars() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &launch_eval_ids());
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--dry-run", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--exclude-eval", "sat-par2-dev", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --dry-run");

    assert!(
        output.status.success(),
        "dry-run should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    for file in [
        "commands.log",
        "input_inventory.jsonl",
        "planned_evals.tsv",
        "provenance.json",
        "provenance.txt",
        "summary.json",
        "summary.md",
    ] {
        assert!(out_dir.join(file).is_file(), "missing sidecar {file}");
    }
    let summary = read_json(&out_dir.join("summary.json"));
    assert_eq!(summary["schema"], "ay-launch-benchmark-packet/v1");
    assert_eq!(summary["mode"], "dry-run");
    assert_eq!(summary["benchmarks_executed"], false);
    assert_eq!(summary["planned_eval_count"], 7);
    assert_eq!(
        summary["artifact_index"]["schema"],
        "ay-launch-benchmark-artifact-index/v1"
    );
    assert_eq!(summary["self_validation"]["status"], "pass");
}

#[test]
#[timeout(30_000)]
fn launch_packet_quotes_commands_across_sidecars() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-smtcomp-qf-lia"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet with space");
    let ay_with_space = repo.path().join("bin dir").join("ay tool");
    fs::create_dir_all(ay_with_space.parent().expect("ay parent")).expect("mkdir ay parent");
    fs::copy(ay_binary(), &ay_with_space).expect("copy ay");
    make_executable(&ay_with_space);
    let reference_solver = write_fake_reference_solver(&repo, "ref solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--dry-run", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(&ay_with_space)
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-smtcomp-qf-lia", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --dry-run");

    assert_success(&output, "quoted dry run should succeed");
    let command_line = fs::read_to_string(out_dir.join("commands.log"))
        .expect("read commands.log")
        .lines()
        .next()
        .expect("commands.log row")
        .to_string();
    assert!(
        command_line.starts_with("$ '"),
        "path with spaces should be shell-quoted: {command_line}"
    );
    assert!(
        command_line.contains("--reference-solver '"),
        "reference solver path should be shell-quoted: {command_line}"
    );

    let provenance = read_json(&out_dir.join("provenance.json"));
    let summary = read_json(&out_dir.join("summary.json"));
    assert_eq!(
        provenance["selection"]["active_evals"][0]["command"],
        command_line
    );
    assert_eq!(summary["planned_evals"][0]["command"], command_line);
    assert_eq!(summary["commands"][0], command_line);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("dry-run: '"),
        "dry-run stderr should be shell-quoted:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_inventory_matches_shell_metadata_contract() {
    let repo = TempDir::new().expect("temp repo");
    write_eval_registry(
        repo.path(),
        "smt-smtcomp-qf-lia",
        r#"
id: smt-smtcomp-qf-lia
inputs:
  benchmarks_dir: benchmarks/smtcomp/QF_LIA
  timeout_sec: 30
setup:
  download: scripts/download_smtcomp_benchmarks.sh --logic QF_LIA
  note: >
    Run scripts/download_smtcomp_benchmarks.sh --logic QF_LIA to populate
    benchmarks/smtcomp/QF_LIA/ from the Zenodo SMT-LIB 2024 release.
"#,
    );
    let benchmark_dir = repo.path().join("benchmarks/smtcomp/QF_LIA");
    fs::create_dir_all(&benchmark_dir).expect("mkdir benchmarks");
    fs::write(benchmark_dir.join("sample.smt2"), "(check-sat)\n").expect("write smt2");
    fs::write(repo.path().join("Cargo.toml"), "[workspace]\n").expect("write Cargo.toml");
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-smtcomp-qf-lia", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let inventory = read_jsonl_first(&out_dir.join("input_inventory.jsonl"));
    assert_eq!(
        inventory["registry"],
        "evals/registry/smt-smtcomp-qf-lia.yaml"
    );
    assert_eq!(inventory["registry_exists"], true);
    assert_eq!(inventory["benchmarks_dir"], "benchmarks/smtcomp/QF_LIA");
    assert_eq!(
        inventory["setup_download"],
        "scripts/download_smtcomp_benchmarks.sh --logic QF_LIA"
    );
    assert!(inventory["setup_note"]
        .as_str()
        .expect("setup note")
        .contains("Zenodo SMT-LIB 2024 release"));
    assert_eq!(
        inventory["public_source"],
        "https://zenodo.org/api/records/11061097/files/QF_LIA.tar.zst/content"
    );
    assert_eq!(inventory["benchmarks_dir_exists"], true);
    assert_eq!(inventory["file_count"], 1);
    assert_eq!(inventory["smt2_count"], 1);
    assert_eq!(inventory["input_dirs"][0]["role"], "benchmarks_dir");

    let provenance = read_json(&out_dir.join("provenance.json"));
    assert_eq!(
        provenance["selection"]["registry_validation"]["status"],
        "pass"
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_inventory_records_suite_dirs() {
    let repo = TempDir::new().expect("temp repo");
    write_eval_registry(
        repo.path(),
        "smt-local-suite",
        r#"
id: smt-local-suite
inputs:
  benchmarks_dir: benchmarks/smt
  suite_dirs:
    - QF_LIA
    - QF_BV
  timeout_sec: 30
"#,
    );
    let qf_lia_dir = repo.path().join("benchmarks/smt/QF_LIA");
    let qf_bv_dir = repo.path().join("benchmarks/smt/QF_BV");
    fs::create_dir_all(&qf_lia_dir).expect("mkdir QF_LIA");
    fs::create_dir_all(&qf_bv_dir).expect("mkdir QF_BV");
    fs::write(qf_lia_dir.join("lia.smt2"), "(check-sat)\n").expect("write lia smt2");
    fs::write(qf_bv_dir.join("bv.smt2"), "(check-sat)\n").expect("write bv smt2");
    fs::write(repo.path().join("Cargo.toml"), "[workspace]\n").expect("write Cargo.toml");
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-local-suite", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let inventory = read_jsonl_first(&out_dir.join("input_inventory.jsonl"));
    assert_eq!(inventory["benchmarks_dir"], "benchmarks/smt");
    assert_eq!(
        inventory["suite_dirs"],
        serde_json::json!(["QF_LIA", "QF_BV"])
    );
    assert_eq!(inventory["benchmarks_dir_exists"], true);
    assert_eq!(inventory["file_count"], 2);
    assert_eq!(inventory["smt2_count"], 2);
    assert_eq!(
        inventory["input_dirs"]
            .as_array()
            .expect("input dirs")
            .len(),
        3
    );
    assert_eq!(inventory["input_dirs"][0]["role"], "benchmarks_dir");
    assert_eq!(inventory["input_dirs"][0]["path"], "benchmarks/smt");
    assert_eq!(inventory["input_dirs"][1]["role"], "suite_dir");
    assert_eq!(inventory["input_dirs"][1]["path"], "benchmarks/smt/QF_LIA");
    assert_eq!(inventory["input_dirs"][1]["file_count"], 1);
    assert_eq!(inventory["input_dirs"][1]["smt2_count"], 1);
    assert_eq!(inventory["input_dirs"][2]["role"], "suite_dir");
    assert_eq!(inventory["input_dirs"][2]["path"], "benchmarks/smt/QF_BV");
    assert_eq!(inventory["input_dirs"][2]["file_count"], 1);
    assert_eq!(inventory["input_dirs"][2]["smt2_count"], 1);
}

#[test]
#[timeout(30_000)]
fn launch_packet_bench_progress_every_is_numeric() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args([
            "launch-packet",
            "--progress-every",
            "7",
            "--metadata-only",
            "--repo-root",
        ])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-local-suite", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let provenance = read_json(&out_dir.join("provenance.json"));
    assert_eq!(provenance["parameters"]["bench_progress_every"], 7);
}

#[test]
#[timeout(30_000)]
fn launch_packet_rejects_invalid_bench_progress_every_like_shell() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args([
            "launch-packet",
            "--progress-every",
            "0",
            "--metadata-only",
            "--repo-root",
        ])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-local-suite", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert!(
        !output.status.success(),
        "invalid progress interval should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--progress-every must be a positive integer"),
        "stderr should explain the invalid progress interval:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_rejects_eval_missing_from_ay_bench_list() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-smtcomp-qf-lia", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert!(
        !output.status.success(),
        "unregistered eval should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("eval not registered"),
        "stderr should explain registry failure:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_resolves_reference_solver_relative_to_repo_root() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = repo.path().join("tools/ref-solver");
    write_executable(
        &reference_solver,
        "#!/usr/bin/env sh\nif [ \"$1\" = \"--version\" ]; then echo repo-ref 1.0; exit 0; fi\nexit 0\n",
    );

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .args([
            "--reference-solver",
            "tools/ref-solver",
            "--eval",
            "smt-local-suite",
            "--out-dir",
        ])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let provenance = read_json(&out_dir.join("provenance.json"));
    assert_eq!(
        provenance["tools"]["reference_solver"]["resolved_path"],
        reference_solver
            .canonicalize()
            .expect("canonical ref solver")
            .display()
            .to_string()
    );
    assert_eq!(
        provenance["tools"]["reference_solver"]["version"]["output"][0],
        "repo-ref 1.0"
    );
}
