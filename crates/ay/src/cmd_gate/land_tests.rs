// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    plan,
    process::{Runner, Step, StepKind},
};
use std::path::PathBuf;

#[test]
fn repository_publication_lease_is_shared_by_linked_worktrees_and_released_on_drop() {
    let directory = tempfile::tempdir().unwrap();
    let mut first = Runner::new(directory.path().to_path_buf());
    first.git(&["init", "--quiet"]).unwrap();
    let hooks = directory.path().join("empty-hooks");
    std::fs::create_dir(&hooks).unwrap();
    first
        .git(&["config", "core.hooksPath", hooks.to_str().unwrap()])
        .unwrap();
    first
        .git(&[
            "-c",
            "user.name=AY test",
            "-c",
            "user.email=test@example.invalid",
            "commit",
            "--quiet",
            "--no-gpg-sign",
            "--allow-empty",
            "-m",
            "fixture",
        ])
        .unwrap();
    let peer_path = directory.path().join("peer");
    first
        .git(&[
            "worktree",
            "add",
            "--quiet",
            "--detach",
            peer_path.to_str().unwrap(),
        ])
        .unwrap();
    let mut peer = Runner::new(peer_path);
    let held = super::publication_lock(&mut first).unwrap();
    // Model a concurrent fork's inherited open description, kept alive beyond
    // owner release. This copy must not extend the lander's ownership.
    let inherited = held.0.try_clone().unwrap();
    let waiting = super::publication_lock_file(&mut peer).unwrap();
    assert!(waiting.try_lock().is_err(), "another worktree must wait");
    drop(held);
    waiting.try_lock().unwrap();
    drop(inherited);
    drop(waiting);
    // No PID file, stale-owner recovery or persistent locked state remains.
    super::publication_lock(&mut first).unwrap();
}

#[test]
fn package_root_narrowing_keeps_compilation_settings_and_all_declared_bins() {
    let old = r#"
[workspace]
members = ["crates/one", "crates/two"]
[workspace.metadata.atpkg]
expose = ["one", "two"]
build-args = ["--workspace", "--features", "one/cli"]
"#;
    let selected = old.replace(
        "[\"--workspace\", \"--features\", \"one/cli\"]",
        "[\"--workspace\", \"--features\", \"one/cli\", \"--bin\", \"one\", \"--bin=two\"]",
    );
    let narrows = super::scope::only_narrows_package_bins;
    assert!(narrows(old, &selected));
    for changed in [
        selected.replace("one/cli", "one/other"),
        selected.replace("\"--bin=two\"", "\"--bin=hidden\""),
        selected.replace(", \"--bin=two\"", ""),
        selected.replace("expose = [\"one\", \"two\"]", "expose = [\"one\"]"),
        format!("{selected}\n[profile.release]\nopt-level = 1\n"),
        format!("{selected}\n[workspace.dependencies]\nlib = \"1\"\n"),
        format!("{selected}\n[workspace.package]\nversion = \"1.0.0\"\n"),
        format!("{selected}\n[trust]\nbackstop = 10\n"),
        "[malformed".into(),
    ] {
        assert!(
            !narrows(old, &changed),
            "must retain ordinary compilation: {changed}"
        );
    }
    let one = selected.replace(", \"--bin=two\"", "");
    assert!(
        !narrows(&one, &selected),
        "adding a previously excluded binary is not narrowing"
    );
    for flag in [
        "--all-targets",
        "--bins",
        "--lib",
        "--tests",
        "--examples",
        "--benches",
        "--test=hidden",
        "--example=hidden",
        "--bench=hidden",
        "--",
    ] {
        let replacement = format!("\"--workspace\", \"{flag}\"");
        let old = old.replace("\"--workspace\"", &replacement);
        let new = selected.replace("\"--workspace\"", &replacement);
        assert!(
            !narrows(&old, &new),
            "nondefault target selection stays conservative: {flag}"
        );
    }
}

#[test]
fn a_narrowed_recipe_keeps_cli_provenance_and_explicit_manifest_consumers() {
    let scope = super::scope::RustScope {
        narrowed_package_recipe: true,
        ..Default::default()
    };
    let selected = plan::select(
        "/repo".as_ref(),
        &metadata(),
        vec!["Cargo.toml".into()],
        None,
        &scope,
    )
    .unwrap();
    assert!(!selected.broad_compile);
    assert_eq!(
        selected.steps.len(),
        1,
        "the existing CLI provenance build still runs"
    );
    assert!(selected.steps[0].args.iter().any(|arg| arg == "build"));
    let mut consumed = metadata();
    consumed.packages[1].metadata = serde_json::json!({
        "ay-provenance": {"inputs": ["../../Cargo.toml"]}
    });
    let selected = plan::select(
        "/repo".as_ref(),
        &consumed,
        vec!["Cargo.toml".into()],
        None,
        &scope,
    )
    .unwrap();
    assert!(
        selected
            .steps
            .iter()
            .any(|step| step.kind == super::process::StepKind::RustTests
                && step.args.iter().any(|arg| arg == "ay-core")),
        "a declared runtime input must retain its consumer tests"
    );
    let conservative = plan::select(
        "/repo".as_ref(),
        &metadata(),
        vec!["Cargo.toml".into()],
        None,
        &Default::default(),
    )
    .unwrap();
    assert!(conservative.broad_compile);
}

#[test]
fn compiler_replacements_are_rejected_without_rejecting_resource_caps() {
    assert!(super::is_policy_override("RUSTC"));
    assert!(super::is_policy_override("RUSTC_WRAPPER"));
    assert!(super::is_policy_override(
        "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS"
    ));
    assert!(!super::is_policy_override("CARGO_BUILD_JOBS"));
    assert!(!super::is_policy_override("BUILD_SLOT_HELD"));
}

#[test]
fn zero_tests_and_ignored_tests_are_not_runtime_coverage() {
    use super::process::passed_tests;
    assert_eq!(
        passed_tests(b"test result: ok. 0 passed; 0 failed; 4 ignored;"),
        0
    );
    assert_eq!(passed_tests(b"test result: FAILED. 4 passed; 1 failed;"), 0);
    assert_eq!(
        passed_tests(b"test result: ok. 3 passed; 0 failed;\ntest result: ok. 2 passed; 0 failed;"),
        5
    );
}

#[test]
fn cli_module_changes_do_not_select_unrelated_external_checker_suites() {
    let mut scope = super::scope::RustScope::default();
    scope
        .cli_modules
        .insert("src/cmd_gate.rs".into(), "cmd_gate".into());
    scope
        .production_modules
        .extend(["cmd_gate".into(), "maxsat_proof".into()]);
    let plan = plan::select(
        "/repo".as_ref(),
        &metadata(),
        vec![
            "crates/ay/src/cmd_gate/land.rs".into(),
            "crates/ay/src/main.rs".into(),
        ],
        None,
        &scope,
    )
    .unwrap();
    let tests: Vec<_> = plan
        .steps
        .iter()
        .filter(|step| {
            step.compiler_payload()
                .is_some_and(|args| args.first().is_some_and(|arg| arg == "test"))
        })
        .collect();
    assert_eq!(tests.len(), 1);
    assert!(!tests
        .iter()
        .any(|s| s.args.windows(2).any(|a| a == ["--skip", "cmd_gate::"])));
    assert!(tests
        .iter()
        .any(|s| s.args.windows(2).any(|a| a == ["--skip", "maxsat_proof::"])));
    assert!(!tests.iter().any(|s| s.args.iter().any(|a| a == "--bins")));
    assert!(plan
        .steps
        .iter()
        .filter(|s| s.args.iter().any(|a| a == "build"))
        .all(|s| s.args.windows(2).any(|a| a == ["--profile", "test"])));
}

#[test]
fn grouped_integration_edits_keep_unchanged_checker_and_benchmark_modules_out() {
    let temp = tempfile::tempdir().unwrap();
    let mut metadata = metadata();
    for package in &mut metadata.packages {
        package.manifest_path = temp
            .path()
            .join(package.manifest_path.strip_prefix("/repo").unwrap());
        for target in &mut package.targets {
            target.src_path = temp
                .path()
                .join(target.src_path.strip_prefix("/repo").unwrap());
        }
    }
    let directory = temp.path().join("crates/ay/tests");
    std::fs::create_dir_all(directory.join("group_cli")).unwrap();
    std::fs::write(directory.join("group_cli.rs"),
        "#[path=\"group_cli/changed.rs\"] mod changed; #[path=\"group_cli/checker.rs\"] mod checker;").unwrap();
    std::fs::write(
        directory.join("group_cli/changed.rs"),
        "#[test] fn check() {}",
    )
    .unwrap();
    let mut scope = super::scope::RustScope::default();
    scope.module_lists.insert(directory.join("group_cli.rs"));
    let plan = plan::select(
        temp.path(),
        &metadata,
        vec![
            "crates/ay/tests/group_cli.rs".into(),
            "crates/ay/tests/group_cli/changed.rs".into(),
        ],
        None,
        &scope,
    )
    .unwrap();
    let test = plan
        .steps
        .iter()
        .find(|step| {
            step.kind == StepKind::RustTests
                && step
                    .args
                    .windows(2)
                    .any(|args| args == ["--test", "group_cli"])
        })
        .unwrap();
    assert!(test.args.windows(2).any(|a| a == ["--skip", "checker::"]));
    assert!(!test.args.windows(2).any(|a| a == ["--skip", "changed::"]));
    assert!(!plan
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "group_smt")));
    let conservative = plan::select(
        temp.path(),
        &metadata,
        vec!["crates/ay/tests/group_cli.rs".into()],
        None,
        &Default::default(),
    )
    .unwrap();
    assert!(!conservative
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "--skip")));
}

fn metadata() -> plan::Metadata {
    serde_json::from_value(serde_json::json!({
        "workspace_members": ["ay", "ay-core"],
        "packages": [
            {"id": "ay", "name": "ay", "edition": "2021", "manifest_path": "/repo/crates/ay/Cargo.toml",
             "targets": [
                {"name": "ay", "kind": ["lib"], "src_path": "/repo/crates/ay/src/lib.rs"},
                {"name": "ay", "kind": ["bin"], "src_path": "/repo/crates/ay/src/main.rs"},
                {"name": "group_cli", "kind": ["test"], "src_path": "/repo/crates/ay/tests/group_cli.rs", "required-features": ["cli"]},
                {"name": "group_smt", "kind": ["test"], "src_path": "/repo/crates/ay/tests/group_smt.rs"}]},
            {"id": "ay-core", "name": "ay-core", "edition": "2024", "manifest_path": "/repo/crates/ay-core/Cargo.toml",
             "targets": [
                 {"name": "ay_core", "kind": ["lib"], "src_path": "/repo/crates/ay-core/src/lib.rs"},
                 {"name": "group_core", "kind": ["test"], "src_path": "/repo/crates/ay-core/tests/group_core.rs"}]}
        ]
    })).unwrap()
}

#[test]
fn removing_a_standalone_test_compiles_survivors_without_running_them() {
    let temp = tempfile::tempdir().unwrap();
    let mut metadata = metadata();
    for package in &mut metadata.packages {
        package.manifest_path = temp
            .path()
            .join(package.manifest_path.strip_prefix("/repo").unwrap());
        for target in &mut package.targets {
            target.src_path = temp
                .path()
                .join(target.src_path.strip_prefix("/repo").unwrap());
        }
    }
    let retired = PathBuf::from("crates/ay-core/tests/retired.rs");
    let select = || {
        plan::select(
            temp.path(),
            &metadata,
            vec![retired.clone()],
            None,
            &Default::default(),
        )
        .unwrap()
    };
    let removed = select();
    assert!(removed.steps.iter().any(|step| {
        step.args.iter().any(|arg| arg == "check") && step.args.iter().any(|arg| arg == "--tests")
    }));
    assert!(!removed
        .steps
        .iter()
        .any(|step| step.kind == super::process::StepKind::RustTests));

    // A live shared helper retains conservative runtime ownership.
    let live = temp.path().join(&retired);
    std::fs::create_dir_all(live.parent().unwrap()).unwrap();
    std::fs::write(&live, "pub fn helper() {}\n").unwrap();
    assert!(select()
        .steps
        .iter()
        .any(|step| step.kind == super::process::StepKind::RustTests));

    // Default test compilation does not cover a gated survivor.
    std::fs::remove_file(live).unwrap();
    metadata.packages[1].targets[1]
        .required_features
        .push("gated".into());
    let gated = plan::select(
        temp.path(),
        &metadata,
        vec![retired],
        None,
        &Default::default(),
    )
    .unwrap();
    assert!(gated
        .steps
        .iter()
        .any(|step| step.kind == super::process::StepKind::RustTests));
}

#[test]
fn documentation_and_grouped_tests_select_only_relevant_work() {
    let metadata = metadata();
    let docs = plan::select(
        "/repo".as_ref(),
        &metadata,
        vec!["the development design notes".into()],
        None,
        &Default::default(),
    )
    .unwrap();
    assert_eq!(docs.steps.as_slice(), &[] as &[Step]);
    let tests = plan::select(
        "/repo".as_ref(),
        &metadata,
        vec!["crates/ay/tests/group_cli/land.rs".into()],
        None,
        &Default::default(),
    )
    .unwrap();
    let runtime: Vec<_> = tests
        .steps
        .iter()
        .filter(|step| step.kind == StepKind::RustTests)
        .collect();
    assert_eq!(runtime.len(), 1);
    assert!(runtime[0].args.iter().any(|arg| arg == "group_cli"));
    assert!(tests
        .steps
        .iter()
        .all(|step| !step.args.iter().any(|arg| arg == "group_smt")));
    let library = plan::select(
        "/repo".as_ref(),
        &metadata,
        vec!["crates/ay-core/src/term.rs".into()],
        None,
        &Default::default(),
    )
    .unwrap();
    assert!(!library.broad_compile);
    assert!(library
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "ay-core")));
    assert!(!library
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "--test")));
}

#[test]
fn declared_document_inputs_and_package_editions_are_build_inputs() {
    let mut metadata = metadata();
    metadata.packages[1].metadata = serde_json::json!({
        "ay-provenance": {"inputs": ["../../docs/build.md"]}
    });
    let docs = plan::select(
        "/repo".as_ref(),
        &metadata,
        vec!["the development design notes".into()],
        None,
        &Default::default(),
    )
    .unwrap();
    assert!(docs
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "ay-core")));
    let temp = tempfile::tempdir().unwrap();
    for package in &mut metadata.packages {
        package.manifest_path = temp
            .path()
            .join(package.manifest_path.strip_prefix("/repo").unwrap());
        for target in &mut package.targets {
            target.src_path = temp
                .path()
                .join(target.src_path.strip_prefix("/repo").unwrap());
        }
    }
    let path = temp.path().join("crates/ay-core/src/lib.rs");
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, "pub fn value() {}\n").unwrap();
    let plan = plan::select(
        temp.path(),
        &metadata,
        vec!["crates/ay-core/src/lib.rs".into()],
        None,
        &Default::default(),
    )
    .unwrap();
    let format = plan.steps.iter().find(|s| s.program == "trustfmt").unwrap();
    assert!(format.args.windows(2).any(|a| a == ["--edition", "2024"]));
}

#[test]
fn internal_lock_edges_are_local_but_external_checksums_broaden_compilation() {
    let temp = tempfile::tempdir().unwrap();
    let metadata = metadata();
    let before =
        "version = 4\n[[package]]\nname = \"ay-core\"\nversion = \"1.0.0\"\ndependencies = []\n";
    let after = before.replace("dependencies = []", "dependencies = [\"ay\"]");
    std::fs::write(temp.path().join("Cargo.lock"), after).unwrap();
    let local = plan::select(
        temp.path(),
        &metadata,
        vec!["Cargo.lock".into()],
        Some(before),
        &Default::default(),
    )
    .unwrap();
    assert!(!local.broad_compile);
    assert!(local
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "ay-core")));
    assert!(!local
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "group_smt")));
    assert!(!local
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "--test")));
    let external = "\n[[package]]\nname = \"serde\"\nversion = \"1.0.0\"\nsource = \"registry+example\"\nchecksum = \"abc\"\n";
    let old = format!("{before}{external}");
    std::fs::write(temp.path().join("Cargo.lock"), old.replace("abc", "def")).unwrap();
    let broad = plan::select(
        temp.path(),
        &metadata,
        vec!["Cargo.lock".into()],
        Some(&old),
        &Default::default(),
    )
    .unwrap();
    assert!(broad.broad_compile);
    assert!(broad
        .steps
        .iter()
        .any(|s| s.args.iter().any(|a| a == "--all-targets")));
}

const BUMP_MANIFEST: &str = r#"[workspace]
members = ["crates/ay", "crates/ay-core"]

[workspace.package]
version = "0.28.1"
edition = "2021"

[workspace.dependencies]
ay = { version = "0.28.1", path = "crates/ay" }
ay-core = { version = "0.28.1", path = "crates/ay-core", default-features = false }
serde = "1"

[profile.release]
opt-level = 3
"#;

const BUMP_LOCK: &str = r#"version = 4

[[package]]
name = "ay"
version = "0.28.1"
dependencies = [
 "ay-core",
 "serde",
]

[[package]]
name = "ay-core"
version = "0.28.1"

[[package]]
name = "serde"
version = "1.0.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
checksum = "abc"
"#;

/// Plan a change of the fixture workspace from `BUMP_MANIFEST`/`BUMP_LOCK`
/// to these files (as `pub bump` writes them), plus any other changed paths.
fn plan_bump(manifest: &str, lock: &str, other: &[&str]) -> plan::Plan {
    let temp = tempfile::tempdir().unwrap();
    let mut metadata = metadata();
    for package in &mut metadata.packages {
        package.version = Some("0.28.2".into());
        package.manifest_path = temp
            .path()
            .join(package.manifest_path.strip_prefix("/repo").unwrap());
        for target in &mut package.targets {
            target.src_path = temp
                .path()
                .join(target.src_path.strip_prefix("/repo").unwrap());
        }
    }
    std::fs::write(temp.path().join("Cargo.toml"), manifest).unwrap();
    std::fs::write(temp.path().join("Cargo.lock"), lock).unwrap();
    let scope = super::scope::RustScope {
        base_workspace_manifest: Some(BUMP_MANIFEST.into()),
        ..Default::default()
    };
    let mut paths: Vec<PathBuf> = vec!["Cargo.lock".into(), "Cargo.toml".into()];
    paths.extend(other.iter().map(PathBuf::from));
    plan::select(temp.path(), &metadata, paths, Some(BUMP_LOCK), &scope).unwrap()
}

fn is_narrow_bump_plan(plan: &plan::Plan) -> bool {
    !plan.broad_compile
        && !plan
            .steps
            .iter()
            .any(|step| step.kind == super::process::StepKind::RustTests || step.needs_quiet_host())
}

#[test]
fn a_version_only_bump_plans_the_metadata_check_and_the_cli_build_only() {
    let plan = plan_bump(
        &BUMP_MANIFEST.replace("0.28.1", "0.28.2"),
        &BUMP_LOCK.replace("0.28.1", "0.28.2"),
        &[],
    );
    assert!(!plan.broad_compile);
    assert_eq!(plan.steps.len(), 2, "{:?}", plan.steps);
    // Resolution with the checked-in lockfile and no network, outside the
    // native fixed admission that compiler work takes.
    assert_eq!(plan.steps[0].program, "targo");
    assert_eq!(
        plan.steps[0].args,
        ["metadata", "--locked", "--offline", "--format-version", "1"]
    );
    // The ordinary CLI build, shared with every other landing plan.
    let build = &plan.steps[1];
    assert_eq!(build.kind, super::process::StepKind::Command);
    assert!(build
        .compiler_payload()
        .is_some_and(|args| args.first().is_some_and(|arg| arg == "build")));
    assert!(build.args.windows(2).any(|a| a == ["-p", "ay"]));
    assert!(build
        .args
        .windows(2)
        .any(|a| a == ["--features", "cli,bench"]));
    assert!(build.args.windows(2).any(|a| a == ["--bin", "ay"]));
    assert!(is_narrow_bump_plan(&plan));
}

#[test]
fn a_version_bump_with_another_hunk_plans_as_before() {
    let manifest = BUMP_MANIFEST.replace("0.28.1", "0.28.2");
    let lock = BUMP_LOCK.replace("0.28.1", "0.28.2");
    assert!(is_narrow_bump_plan(&plan_bump(&manifest, &lock, &[])));
    let other_dependency =
        "name = \"ay-core\"\nversion = \"0.28.2\"\ndependencies = [\n \"serde\",\n]\n";
    let variants: [(String, String, &[&str]); 6] = [
        // A compilation setting.
        (
            manifest.replace("opt-level = 3", "opt-level = 1"),
            lock.clone(),
            &[],
        ),
        // An external requirement is not a path dependency into the workspace.
        (
            manifest.replace("serde = \"1\"", "serde = \"1.0.1\""),
            lock.clone(),
            &[],
        ),
        // An external lock entry.
        (manifest.clone(), lock.replace("\"abc\"", "\"def\""), &[]),
        // A local lock entry changes more than its version.
        (
            manifest.clone(),
            lock.replace(
                "name = \"ay-core\"\nversion = \"0.28.2\"\n",
                other_dependency,
            ),
            &[],
        ),
        // A local package moves to a version other than the workspace's.
        (manifest.clone(), lock.replacen("0.28.2", "0.29.0", 1), &[]),
        // Another changed path.
        (
            manifest.clone(),
            lock.clone(),
            &["crates/ay-core/src/lib.rs"],
        ),
    ];
    for (manifest, lock, other) in variants {
        let plan = plan_bump(&manifest, &lock, other);
        assert!(plan.broad_compile, "{manifest}\n{lock}\n{other:?}");
        assert!(plan
            .steps
            .iter()
            .any(|step| step.args.iter().any(|arg| arg == "--all-targets")));
        assert!(plan
            .steps
            .iter()
            .any(|step| step.kind == super::process::StepKind::RustTests
                && step.args.windows(2).any(|a| a == ["-p", "ay-core"])));
    }
}

fn fixture() -> (tempfile::TempDir, Runner, PathBuf) {
    let temp = tempfile::tempdir().unwrap();
    let remote = temp.path().join("origin.git");
    std::fs::create_dir(&remote).unwrap();
    let mut origin = Runner::new(remote.clone());
    origin
        .git(&["init", "--bare", "--initial-branch=main"])
        .unwrap();
    let local = temp.path().join("work");
    std::fs::create_dir(&local).unwrap();
    let mut runner = Runner::new(local);
    runner.git(&["init", "--initial-branch=topic"]).unwrap();
    runner
        .git(&["config", "user.name", "Landing test"])
        .unwrap();
    runner
        .git(&["config", "user.email", "landing@example.invalid"])
        .unwrap();
    runner.git(&["config", "commit.gpgsign", "false"]).unwrap();
    runner
        .git(&[
            "-c",
            "core.hooksPath=/dev/null",
            "commit",
            "--allow-empty",
            "-m",
            "base",
        ])
        .unwrap();
    runner
        .git(&["remote", "add", "origin", remote.to_str().unwrap()])
        .unwrap();
    runner.git(&["push", "origin", "HEAD:main"]).unwrap();
    runner.fetch().unwrap();
    (temp, runner, remote)
}

#[test]
fn dirty_or_stale_head_cannot_be_pushed() {
    let (_temp, mut runner, remote) = fixture();
    let head = runner.head().unwrap();
    let base = runner.git(&["rev-parse", "origin/main"]).unwrap();
    let seal = runner.validate(&[], &head).unwrap();
    std::fs::write(runner.root.join("untracked"), "not validated").unwrap();
    assert!(runner.push_validated(&seal, &base).is_err());
    std::fs::remove_file(runner.root.join("untracked")).unwrap();
    runner
        .git(&[
            "-c",
            "core.hooksPath=/dev/null",
            "commit",
            "--allow-empty",
            "-m",
            "new head",
        ])
        .unwrap();
    assert!(runner.push_validated(&seal, &base).is_err());
    // A local branch must not impersonate the fetched remote authority.
    runner.git(&["branch", "origin/main", "HEAD"]).unwrap();
    let error = super::make_plan(&mut runner, "HEAD").err().unwrap();
    assert!(error.to_string().contains("--base must be an ancestor"));
    assert_eq!(
        Runner::new(remote)
            .git(&["rev-parse", "main"])
            .unwrap()
            .trim(),
        head
    );
}

#[test]
fn failed_validation_stops_before_push_and_remote_movement_requires_new_round() {
    let (_temp, mut runner, remote) = fixture();
    let head = runner.head().unwrap();
    let base = runner.git(&["rev-parse", "origin/main"]).unwrap();
    let failed = runner
        .validate(&[Step::new("git", &["not-a-real-subcommand"])], &head)
        .and_then(|seal| runner.push_validated(&seal, &base));
    assert!(failed.is_err());
    assert_eq!(
        Runner::new(remote)
            .git(&["rev-parse", "main"])
            .unwrap()
            .trim(),
        head
    );
    runner
        .git(&[
            "-c",
            "core.hooksPath=/dev/null",
            "commit",
            "--allow-empty",
            "-m",
            "advance",
        ])
        .unwrap();
    let advanced = runner.head().unwrap();
    runner.git(&["push", "origin", "HEAD:main"]).unwrap();
    runner.git(&["reset", "--hard", &head]).unwrap();
    let seal = runner.validate(&[], &head).unwrap();
    assert!(!runner.push_validated(&seal, &base).unwrap());
    assert_eq!(
        runner.git(&["rev-parse", "origin/main"]).unwrap().trim(),
        advanced
    );
    runner.git(&["merge", "--no-edit", "origin/main"]).unwrap();
    let refreshed = runner.git(&["rev-parse", "origin/main"]).unwrap();
    runner
        .git(&[
            "-c",
            "core.hooksPath=/dev/null",
            "commit",
            "--allow-empty",
            "-m",
            "validated change",
        ])
        .unwrap();
    let head = runner.head().unwrap();
    let seal = runner.validate(&[], &head).unwrap();
    assert!(runner.push_validated(&seal, &refreshed).unwrap());
    assert_eq!(
        runner
            .git(&["ls-remote", "origin", "refs/heads/main"])
            .unwrap()
            .split_whitespace()
            .next(),
        Some(head.as_str())
    );
}

#[test]
fn explicit_agh_is_same_absolute_provider_for_fetch_and_push() {
    let directory = tempfile::tempdir().unwrap();
    let executable = std::env::current_exe().unwrap();
    let mut runner = Runner::new(directory.path().to_path_buf());
    runner.select_agh(&executable).unwrap();
    for args in [
        vec!["repo", "fetch-main", "owner/repo", "checkout"],
        vec!["repo", "push", "owner/repo", "checkout", "--dry-run"],
    ] {
        let step = runner.agh_step(&args);
        assert_eq!(std::path::Path::new(&step.program), executable);
        assert_eq!(step.args, args);
        // The selector records a command; it supplies no child PATH overlay.
        // Fetch, validation and push retain their ordinary owning boundaries.
        assert_eq!(runner.agh_program(), executable.to_str().unwrap());
    }
}

#[test]
fn explicit_agh_rejects_path_search_and_non_executable_objects_before_transport() {
    let directory = tempfile::tempdir().unwrap();
    let mut runner = Runner::new(directory.path().to_path_buf());
    assert!(runner.select_agh(std::path::Path::new("agh")).is_err());
    assert!(runner.select_agh(directory.path()).is_err());
    let data = directory.path().join("data");
    std::fs::write(&data, b"not a program").unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&data, std::fs::Permissions::from_mode(0o600)).unwrap();
        assert!(runner.select_agh(&data).is_err());
    }
    // Rejected candidates never replace the ordinary selection.
    assert_eq!(runner.agh_program(), "agh");
}
