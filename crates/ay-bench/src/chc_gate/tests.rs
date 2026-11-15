// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use tempfile::TempDir;

/// Pins the expected-verdict precedence shared by the CSV and JSON
/// manifest loaders: a valid sidecar verdict, then an invalid sidecar
/// (`unknown`), then the manifest's label, then `unknown`/`none`.
#[test]
fn manifest_expected_verdict_precedence() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let tmp = TempDir::new()?;
    let dir = tmp.path();
    let smt2 = "(set-logic HORN)\n(check-sat)\n";
    let sidecar_sat = dir.join("sidecar_sat.smt2");
    let sidecar_bad = dir.join("sidecar_bad.smt2");
    let sidecar_empty = dir.join("sidecar_empty.smt2");
    let manifest_only = dir.join("manifest_only.smt2");
    let unlabeled = dir.join("unlabeled.smt2");
    for path in [
        &sidecar_sat,
        &sidecar_bad,
        &sidecar_empty,
        &manifest_only,
        &unlabeled,
    ] {
        fs::write(path, smt2)?;
    }
    fs::write(sidecar_sat.with_extension("yml"), "expected_verdict: sat\n")?;
    fs::write(
        sidecar_bad.with_extension("yml"),
        "expected_verdict: maybe\n",
    )?;
    fs::write(
        sidecar_empty.with_extension("yml"),
        "format_version: '2.0'\n",
    )?;

    let rows = [
        (&sidecar_sat, "unsat"),
        (&sidecar_bad, "sat"),
        (&sidecar_empty, "unsat"),
        (&manifest_only, "unsat"),
        (&unlabeled, ""),
    ];
    let sidecar_sat_source = format!(
        "sidecar:{}",
        display_path(&sidecar_sat.with_extension("yml"))
    );
    let sidecar_bad_source = format!(
        "sidecar-invalid:{}",
        display_path(&sidecar_bad.with_extension("yml"))
    );
    let expected = [
        ("sat", sidecar_sat_source.as_str()),
        ("unknown", sidecar_bad_source.as_str()),
        ("unsat", "manifest"),
        ("unsat", "manifest"),
        ("unknown", "none"),
    ];

    let mut csv = String::from("path,expected_status\n");
    let mut json_rows = Vec::new();
    for (path, label) in rows {
        csv.push_str(&format!("{},{label}\n", path.display()));
        json_rows.push(serde_json::json!({
            "path": path.display().to_string(),
            "expected_status": label,
        }));
    }
    let csv_path = dir.join("manifest.csv");
    fs::write(&csv_path, csv)?;
    let json_path = dir.join("manifest.json");
    fs::write(&json_path, serde_json::to_string(&json_rows)?)?;

    for cases in [
        load_csv_manifest(&csv_path, Some("LIA-Lin"))?,
        load_json_manifest(&json_path, Some("LIA-Lin"))?,
    ] {
        let actual = cases
            .iter()
            .map(|case| (case.expected_status.as_str(), case.expected_source.as_str()))
            .collect::<Vec<_>>();
        if actual != expected {
            return Err(format!("expected {expected:?}, got {actual:?}").into());
        }
    }
    Ok(())
}

fn write_case(dir: &Path, rel: &str, sidecar: &str) -> PathBuf {
    let path = dir.join(rel);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(&path, "(set-logic HORN)\n(check-sat)\n").unwrap();
    fs::write(path.with_extension("yml"), sidecar).unwrap();
    path
}

/// Gate arguments with every option at its default and dirty evidence
/// allowed; a test overrides what it exercises.
fn test_args(out_dir: PathBuf, ay: PathBuf, timeout_sec: f64) -> ChcGateArgs {
    ChcGateArgs {
        manifest: None,
        roots: Vec::new(),
        sample: false,
        out_dir,
        ay,
        timeout_sec,
        baseline: None,
        category: None,
        require_all_categories: false,
        require_route_counters: Vec::new(),
        allow_dirty: true,
        fail_on_wrong: false,
        fail_on_invalid: false,
        min_solved_delta: 0,
        max_par2_regression_pct: 0.0,
    }
}

#[cfg(unix)]
#[test]
#[cfg(any(
    target_os = "android",
    target_os = "freebsd",
    target_os = "haiku",
    all(target_os = "linux", not(target_env = "uclibc"))
))]
fn chc_gate_executes_one_pinned_snapshot_with_exact_recorded_environment() {
    use sha2::Digest as _;
    use std::os::unix::fs::PermissionsExt as _;

    assert!(std::env::var_os("HOME").is_some());
    let tmp = TempDir::new().expect("tempdir");
    let input = tmp.path().join("case.smt2");
    let original_input = "(set-logic HORN)\n; ORIGINAL_TOKEN\n(check-sat)\n";
    fs::write(&input, original_input).expect("write input");
    let solver = tmp.path().join("fake-ay.sh");
    fs::write(
        &solver,
        format!(
            "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then printf 'fake-ay 1\\n'; exit 0; fi\nif [ \"${{HOME+x}}\" = x ]; then printf 'inherited HOME\\n' >&2; exit 71; fi\nprintf '(set-logic HORN)\\n; MUTATED_SOURCE\\n(check-sat)\\n' > '{}'\nfor argument in \"$@\"; do solver_input=$argument; done\nif grep -q ORIGINAL_TOKEN \"$solver_input\"; then printf 'sat\\n'; else printf 'unsat\\n'; fi\n",
            input.display()
        ),
    )
    .expect("write solver");
    let mut permissions = fs::metadata(&solver)
        .expect("solver metadata")
        .permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&solver, permissions).expect("chmod solver");
    let resources =
        crate::resource::PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
    let pinned = crate::environment::PinnedSolver::capture(
        &solver,
        &resources,
        "CHC pinned snapshot regression",
    )
    .expect("pin solver");
    fs::write(&solver, "#!/bin/sh\nprintf 'unsat\\n'\n").expect("mutate source");
    let args = ChcGateArgs {
        fail_on_wrong: true,
        ..test_args(tmp.path().join("out"), solver, 5.0)
    };
    let run_root = tmp.path().join("runs");
    fs::create_dir(&run_root).expect("run root");
    let record = run_case(
        &ManifestCase {
            case_id: "case".to_string(),
            path: input.clone(),
            category: "LIA".to_string(),
            family: "test".to_string(),
            expected_status: "sat".to_string(),
            expected_source: "sidecar".to_string(),
            source: "test".to_string(),
            required_route_counters: Vec::new(),
        },
        &args,
        &run_root,
        &resources,
        pinned.execution_path(),
    )
    .expect("run pinned CHC solver");

    assert_eq!(record.status, "sat");
    assert!(record.command_argv[0].contains("ay-solver-pin-"));
    assert_eq!(record.path, display_path(&input));
    assert_ne!(record.solver_input_path, record.path);
    assert_eq!(
        record.command_argv.last().map(String::as_str),
        Some(record.solver_input_path.as_str())
    );
    assert_eq!(record.input_size_bytes, original_input.len() as u64);
    assert_eq!(
        record.input_sha256,
        format!(
            "sha256:{:x}",
            sha2::Sha256::digest(original_input.as_bytes())
        )
    );
    assert_eq!(
        fs::read_to_string(&record.solver_input_path).expect("read solver input snapshot"),
        original_input
    );
    assert!(
        fs::read_to_string(&input)
            .expect("read replaced source")
            .contains("MUTATED_SOURCE"),
        "the solver must mutate the original pathname before reading its argument"
    );
    assert!(!record.command_env.contains_key("HOME"));
    assert_eq!(
        record.command_env.get("LC_ALL").map(String::as_str),
        Some("C")
    );
    assert_eq!(
        record.command_env.get("MEMLIMIT").map(String::as_str),
        Some("4096")
    );
    assert!(pinned.verify_source().is_err());
}

#[cfg(unix)]
#[test]
fn chc_gate_rejects_symlink_input_before_snapshotting() {
    use std::os::unix::fs::symlink;

    let tmp = TempDir::new().expect("tempdir");
    let target = tmp.path().join("target.smt2");
    fs::write(&target, "(check-sat)\n").expect("write target");
    let link = tmp.path().join("link.smt2");
    symlink(&target, &link).expect("create input symlink");
    let case = ManifestCase {
        case_id: "linked".to_string(),
        path: link.clone(),
        category: "LIA".to_string(),
        family: "test".to_string(),
        expected_status: "sat".to_string(),
        expected_source: "manifest".to_string(),
        source: "test".to_string(),
        required_route_counters: Vec::new(),
    };
    let validation_error = validate_manifest_cases(&[case])
        .expect_err("manifest validation must reject a symlink input")
        .to_string();
    assert!(
        validation_error.contains("not a non-symlink regular file"),
        "{validation_error}"
    );

    let case_dir = tmp.path().join("run");
    fs::create_dir(&case_dir).expect("case dir");
    assert!(
        snapshot_case_input(&link, &case_dir).is_err(),
        "the authoritative snapshot open must independently reject symlinks"
    );
}

#[test]
fn chc_gate_normalizes_core_categories() {
    assert_eq!(normalize_category_name("lia-lin-arrays"), "LIA-Lin-Arrays");
    assert_eq!(normalize_category_name("mixed-lia-lra"), "mixed_LIA_LRA");
    assert_eq!(normalize_category_name("BOOL"), "BOOL");
}

#[test]
fn chc_gate_json_manifest_uses_sidecar_expected_and_route_counters() {
    let tmp = TempDir::new().unwrap();
    let bench = write_case(
        tmp.path(),
        "family/case.smt2",
        "properties:\n- expected_verdict: false\n  majority_vote_verdict: false\n",
    );
    let manifest = tmp.path().join("manifest.json");
    fs::write(
        &manifest,
        serde_json::json!({
            "benchmarks": [{
                "id": "case-a",
                "path": bench,
                "category": "lia-lin",
                "expected_status": "sat",
                "route_counters_expected": ["chc.route.demo"]
            }]
        })
        .to_string(),
    )
    .unwrap();

    let cases = load_manifest_spec(manifest.to_str().unwrap(), None).unwrap();
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].case_id, "case-a");
    assert_eq!(cases[0].category, "LIA-Lin");
    assert_eq!(cases[0].expected_status, "unsat");
    assert!(cases[0].expected_source.starts_with("sidecar:"));
    assert_eq!(cases[0].required_route_counters, vec!["chc.route.demo"]);
}

#[test]
fn chc_gate_sidecar_expected_keys_are_exact_unique_and_consistent() {
    let tmp = TempDir::new().unwrap();
    let unrelated = write_case(
        tmp.path(),
        "unrelated.smt2",
        "not_expected_verdict: true\nmajority_vote_verdict_note: false\n",
    );
    assert_eq!(
        read_sidecar_expected(&unrelated).origin,
        ExpectedOrigin::None
    );

    let duplicate = write_case(
        tmp.path(),
        "duplicate.smt2",
        "expected_verdict: true\n- expected_verdict: true\n",
    );
    assert_eq!(
        read_sidecar_expected(&duplicate).origin,
        ExpectedOrigin::SidecarInvalid
    );

    let conflicting = write_case(
        tmp.path(),
        "conflicting.smt2",
        "expected_verdict: true\nmajority_vote_verdict: false\n",
    );
    assert_eq!(
        read_sidecar_expected(&conflicting).origin,
        ExpectedOrigin::SidecarInvalid
    );
}

#[test]
fn chc_gate_result_parser_requires_one_authoritative_stdout_line() {
    assert_eq!(extract_solver_result("sat\n"), "sat");
    assert_eq!(
        extract_solver_result("diagnostic: expected unsat\n"),
        "error"
    );
    assert_eq!(extract_solver_result("sat\nsat\n"), "error");
    assert_eq!(extract_solver_result("sat\nunsat\n"), "error");
    assert_eq!(
        solver_status_from_process(false, false, false, false, "sat\n"),
        "error",
        "a process abort after emitting a verdict is not solved"
    );
}

#[test]
fn chc_gate_rejects_duplicate_and_colliding_case_ids() {
    let tmp = TempDir::new().unwrap();
    let first_path = write_case(tmp.path(), "first.smt2", "expected_verdict: true\n");
    let second_path = write_case(tmp.path(), "second.smt2", "expected_verdict: true\n");
    let make = |case_id: &str, path: &Path, source: &str| ManifestCase {
        case_id: case_id.to_string(),
        path: path.to_path_buf(),
        category: "LIA".to_string(),
        family: "test".to_string(),
        expected_status: "sat".to_string(),
        expected_source: "manifest".to_string(),
        source: source.to_string(),
        required_route_counters: Vec::new(),
    };
    let cases = vec![
        make("a/b", &first_path, "first-source"),
        make("a_b", &second_path, "second-source"),
        make("a/b", &second_path, "duplicate-source"),
    ];
    let error = validate_manifest_cases(&cases)
        .expect_err("duplicate and colliding IDs must be rejected")
        .to_string();
    assert!(error.contains("duplicate CHC case ID"), "{error}");
    assert!(error.contains("collide at output directory"), "{error}");
    assert!(error.contains("first-source"), "{error}");
    assert!(error.contains("second-source"), "{error}");
}

#[test]
fn chc_gate_root_discovery_enforces_case_cap() {
    let tmp = TempDir::new().unwrap();
    for name in ["a.smt2", "b.smt2", "c.smt2"] {
        fs::write(tmp.path().join(name), "(set-logic HORN)\n").unwrap();
    }
    let mut cases = Vec::new();
    let error = collect_smt2_cases_with_limits(tmp.path(), None, &mut cases, 100, 100, 2)
        .expect_err("root discovery must enforce its case cap");
    assert!(error.to_string().contains("2-case cap"));
    assert!(cases.len() <= 2);
}

#[test]
fn chc_gate_set_manifest_resolves_sidecar_input_file() {
    let tmp = TempDir::new().unwrap();
    let bench_dir = tmp.path().join("bench");
    let family = bench_dir.join("family");
    fs::create_dir_all(&family).unwrap();
    fs::write(family.join("actual.smt2"), "(check-sat)\n").unwrap();
    fs::write(
        family.join("case.yml"),
        "input_files: actual.smt2\nproperties:\n- expected_verdict: true\n",
    )
    .unwrap();
    let set = bench_dir.join("LIA.set");
    fs::write(&set, "family/case.yml\n").unwrap();

    let cases = load_manifest_spec(&format!("LIA-Lin={}", set.display()), None).unwrap();
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].path, family.join("actual.smt2"));
    assert_eq!(cases[0].category, "LIA-Lin");
    assert_eq!(cases[0].expected_status, "sat");
}

mod scoring;
