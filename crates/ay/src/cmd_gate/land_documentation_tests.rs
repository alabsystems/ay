// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::cmd_gate::land::process::Step;

struct Repository {
    _directory: tempfile::TempDir,
    runner: Runner,
}

impl Repository {
    fn new() -> Self {
        let directory = tempfile::tempdir().unwrap();
        let mut runner = Runner::new(directory.path().to_path_buf());
        runner.git(&["init", "--quiet"]).unwrap();
        runner.git(&["config", "user.name", "AY test"]).unwrap();
        runner
            .git(&["config", "user.email", "test@example.invalid"])
            .unwrap();
        runner.git(&["config", "commit.gpgsign", "false"]).unwrap();
        runner.git(&["config", "core.filemode", "true"]).unwrap();
        let hooks = directory.path().join("empty-hooks");
        std::fs::create_dir(&hooks).unwrap();
        runner
            .git(&["config", "core.hooksPath", hooks.to_str().unwrap()])
            .unwrap();
        let repository = Self {
            _directory: directory,
            runner,
        };
        repository.write(
            "Cargo.toml",
            "[package]\nname='fixture'\nversion='0.1.0'\nedition='2021'\n",
        );
        repository.write("src/lib.rs", "pub fn value() -> u32 { 1 }\n");
        repository.write("the development design notes", "Initial documentation.\n");
        let mut repository = repository;
        repository.commit("initial");
        repository
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.runner.root.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, contents).unwrap();
    }

    fn commit(&mut self, message: &str) -> String {
        self.runner.git(&["add", "--all"]).unwrap();
        self.runner
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
                message,
            ])
            .unwrap();
        self.runner.head().unwrap()
    }

    fn metadata(&self, package_metadata: serde_json::Value) -> plan::Metadata {
        serde_json::from_value(serde_json::json!({
            "workspace_members": ["fixture"],
            "packages": [{
                "id": "fixture", "name": "fixture", "version": "0.1.0",
                "manifest_path": self.runner.root.join("Cargo.toml"),
                "edition": "2021", "source": null,
                "targets": [{"name": "fixture", "kind": ["lib"],
                    "src_path": self.runner.root.join("src/lib.rs")}],
                "metadata": package_metadata,
            }],
            "resolve": {"nodes": [{"id": "fixture", "dependencies": []}]},
        }))
        .unwrap()
    }

    fn validate(&mut self) -> ValidatedHead {
        let head = self.runner.head().unwrap();
        // This real subprocess leaves a measurable effect outside the source
        // tree. Composition must not run completed checks a second time.
        self.runner
            .validate(
                &[Step::new(
                    "git",
                    &["config", "--add", "ay.validation-run", "passed"],
                )],
                &head,
            )
            .unwrap()
    }

    fn compose(
        &mut self,
        seal: &ValidatedHead,
        head: &str,
        package_metadata: serde_json::Value,
    ) -> Result<Option<ValidatedHead>> {
        let Some(changes) = self.runner.documentation_delta(seal, head)? else {
            return Ok(None);
        };
        // Only Cargo resolution is injected. Tree identity, ancestry, modes,
        // policy selection and clean-worktree checks use the real Git repo.
        let metadata = self.metadata(package_metadata);
        self.runner
            .compose_documentation_checked(seal, head, changes, &metadata)
    }

    fn check_runs(&mut self) -> usize {
        self.runner
            .git(&["config", "--get-all", "ay.validation-run"])
            .unwrap()
            .lines()
            .count()
    }
}

#[test]
fn real_documentation_merge_preserves_original_checks_and_artifact_provenance() {
    let mut repository = Repository::new();
    let base = repository.runner.head().unwrap();
    repository
        .runner
        .git(&["checkout", "--quiet", "-b", "candidate"])
        .unwrap();
    repository.write("src/lib.rs", "pub fn value() -> u32 { 2 }\n");
    repository.commit("candidate source");
    let seal = repository.validate();
    let checked = seal.checked_head.clone();
    let checked_tree = seal.checked_tree.clone();
    repository
        .runner
        .git(&["checkout", "--quiet", "-b", "upstream", &base])
        .unwrap();
    repository.write(
        "the development design notes",
        "Upstream evidence ledger.\n",
    );
    repository.commit("upstream documentation");
    repository
        .runner
        .git(&["checkout", "--quiet", "candidate"])
        .unwrap();
    repository
        .runner
        .git(&["merge", "--no-edit", "upstream"])
        .unwrap();
    let head = repository.runner.head().unwrap();
    let composed = repository
        .compose(&seal, &head, serde_json::json!({}))
        .unwrap()
        .unwrap();
    assert_eq!(composed.head, head);
    assert_eq!(composed.checked_head, checked);
    assert_eq!(composed.checked_tree, checked_tree);
    assert_eq!(repository.check_runs(), 1);
    assert_eq!(composed.documentation.len(), 1);
    repository.write(
        "competition/division/LEDGER.md",
        "Another source-neutral ledger.\n",
    );
    let head = repository.commit("second documentation change");
    let composed = repository
        .compose(&composed, &head, serde_json::json!({}))
        .unwrap()
        .unwrap();
    assert_eq!(composed.checked_head, checked);
    assert_eq!(composed.checked_tree, checked_tree);
    assert_eq!(repository.check_runs(), 1);
    assert_eq!(composed.documentation.len(), 2);
}

#[test]
fn source_policy_and_unknown_documentation_data_require_fresh_validation() {
    for (path, contents) in [
        (
            "src/lib.rs",
            "// Comment-only Rust still needs the native Rust plan.\npub fn value() -> u32 { 1 }\n",
        ),
        (".cargo/config.toml", "[build]\nincremental=false\n"),
        ("Cargo.lock", "version = 4\n"),
        ("the development design notes", "{}\n"),
        (
            "scripts/bump_codegen_pins.py",
            "# A tooling input is not inert documentation.\n",
        ),
    ] {
        let mut repository = Repository::new();
        let seal = repository.validate();
        repository.write(path, contents);
        let head = repository.commit("non-documentation input");
        assert!(
            repository
                .compose(&seal, &head, serde_json::json!({}))
                .unwrap()
                .is_none(),
            "{path}"
        );
        assert_eq!(repository.check_runs(), 1);
    }
}

#[test]
fn actual_post_merge_source_delta_cannot_hide_behind_incoming_documentation() {
    let mut repository = Repository::new();
    let base = repository.runner.head().unwrap();
    repository
        .runner
        .git(&["checkout", "--quiet", "-b", "candidate"])
        .unwrap();
    let seal = repository.validate();
    repository
        .runner
        .git(&["checkout", "--quiet", "-b", "upstream", &base])
        .unwrap();
    repository.write(
        "the development design notes",
        "Only upstream documentation.\n",
    );
    repository.commit("upstream ledger");
    repository
        .runner
        .git(&["checkout", "--quiet", "candidate"])
        .unwrap();
    repository
        .runner
        .git(&["merge", "--no-edit", "--no-ff", "--no-commit", "upstream"])
        .unwrap();
    repository.write("src/lib.rs", "pub fn value() -> u32 { 99 }\n");
    let head = repository.commit("merge also changed source");
    assert!(repository
        .compose(&seal, &head, serde_json::json!({}))
        .unwrap()
        .is_none());
}

#[test]
fn registered_runtime_documentation_and_unresolved_inputs_are_not_inert() {
    for inputs in [
        serde_json::json!(["the development design notes"]),
        serde_json::json!(["docs"]),
        serde_json::json!(["missing-runtime-input"]),
        serde_json::json!([123]),
    ] {
        let mut repository = Repository::new();
        let seal = repository.validate();
        repository.write("the development design notes", "Changed runtime data.\n");
        let head = repository.commit("documentation input");
        assert!(repository
            .compose(
                &seal,
                &head,
                serde_json::json!({"ay-provenance": {"inputs": inputs}})
            )
            .unwrap()
            .is_none());
    }
}

#[test]
fn dirty_worktrees_and_nonancestor_identical_trees_cannot_reuse_evidence() {
    let mut repository = Repository::new();
    let seal = repository.validate();
    repository.write(
        "the development design notes",
        "Uncommitted documentation.\n",
    );
    assert!(repository
        .compose(&seal, &seal.head, serde_json::json!({}))
        .is_err());
    repository
        .runner
        .git(&["checkout", "--", "the development design notes"])
        .unwrap();
    repository
        .runner
        .git(&["checkout", "--quiet", "--orphan", "unrelated"])
        .unwrap();
    let head = repository.commit("unrelated history with identical files");
    assert!(repository
        .compose(&seal, &head, serde_json::json!({}))
        .unwrap()
        .is_none());
}

#[cfg(unix)]
#[test]
fn symlink_and_executable_markdown_cannot_carry_a_validation_seal() {
    use std::os::unix::fs::{symlink, PermissionsExt};
    for executable in [false, true] {
        let mut repository = Repository::new();
        let seal = repository.validate();
        let path = repository.runner.root.join("the development design notes");
        if executable {
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        } else {
            std::fs::remove_file(&path).unwrap();
            symlink("../src/lib.rs", &path).unwrap();
        }
        let head = repository.commit("non-regular documentation");
        assert!(repository
            .compose(&seal, &head, serde_json::json!({}))
            .unwrap()
            .is_none());
    }
}

#[cfg(unix)]
#[test]
fn unchanged_configuration_alias_keeps_its_markdown_target_live() {
    use std::os::unix::fs::symlink;
    let mut repository = Repository::new();
    repository.write(
        "the development design notes",
        "[build]\nincremental=false\n",
    );
    std::fs::create_dir(repository.runner.root.join(".cargo")).unwrap();
    symlink(
        "../docs/policy.md",
        repository.runner.root.join(".cargo/config.toml"),
    )
    .unwrap();
    repository.commit("configuration alias");
    let seal = repository.validate();
    repository.write(
        "the development design notes",
        "[build]\nincremental=true\n",
    );
    let head = repository.commit("policy change through Markdown");
    assert!(repository
        .compose(&seal, &head, serde_json::json!({}))
        .unwrap()
        .is_none());
    std::fs::remove_file(repository.runner.root.join("the development design notes")).unwrap();
    let head = repository.commit("deleted alias target");
    assert!(repository
        .compose(&seal, &head, serde_json::json!({}))
        .unwrap()
        .is_none());
}

#[test]
fn cargo_target_named_markdown_is_automatic_source_input() {
    let mut repository = Repository::new();
    repository.write(
        "the development design notes",
        "pub fn value() -> u32 { 1 }\n",
    );
    repository.write("Cargo.toml", "[package]\nname='fixture'\nversion='0.1.0'\nedition='2021'\n[lib]\npath='the development design notes'\n");
    repository.commit("target with nonstandard extension");
    let seal = repository.validate();
    repository.write(
        "the development design notes",
        "pub fn value() -> u32 { 2 }\n",
    );
    let head = repository.commit("target source changed");
    let changes = repository
        .runner
        .documentation_delta(&seal, &head)
        .unwrap()
        .unwrap();
    let mut metadata = repository.metadata(serde_json::json!({}));
    metadata.packages[0].targets[0].src_path =
        repository.runner.root.join("the development design notes");
    assert!(repository
        .runner
        .compose_documentation_checked(&seal, &head, changes, &metadata)
        .unwrap()
        .is_none());
}

#[cfg(unix)]
#[test]
fn unrelated_resolved_alias_does_not_invalidate_inert_documentation() {
    use std::os::unix::fs::symlink;
    let mut repository = Repository::new();
    repository.write("LICENSE", "Fixture license.\n");
    symlink("LICENSE", repository.runner.root.join("linked-license")).unwrap();
    repository.commit("unrelated alias");
    let seal = repository.validate();
    repository.write(
        "the development design notes",
        "Only documentation changed.\n",
    );
    let head = repository.commit("documentation");
    assert!(repository
        .compose(&seal, &head, serde_json::json!({}))
        .unwrap()
        .is_some());
    assert_eq!(repository.check_runs(), 1);
}
