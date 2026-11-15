// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct Repository {
    _directory: tempfile::TempDir,
    runner: Runner,
    base: String,
    metadata: plan::Metadata,
}

impl Repository {
    fn new(consumer: Option<(&str, &str)>) -> Self {
        let directory = tempfile::tempdir().unwrap();
        let mut runner = Runner::new(directory.path().to_path_buf());
        runner.git(&["init", "--quiet"]).unwrap();
        runner
            .git(&["config", "core.hooksPath", "/dev/null"])
            .unwrap();
        std::fs::create_dir(runner.root.join("scripts")).unwrap();
        std::fs::create_dir(runner.root.join("publish")).unwrap();
        std::fs::write(runner.root.join(INDEX), "schema_version=1\n[[script]]\nname='retained'\npath='scripts/retained.sh'\npublish='internal'\n[[script]]\nname='retired-command'\npath='scripts/old_module.py'\npublish='internal'\n").unwrap();
        std::fs::write(runner.root.join("scripts/old_module.py"), "exit 0\n").unwrap();
        std::fs::write(runner.root.join("scripts/retained.sh"), "exit 0\n").unwrap();
        std::fs::write(
            runner.root.join(MANIFEST),
            "scripts\n!scripts/old_module.py\n",
        )
        .unwrap();
        if let Some((path, content)) = consumer {
            std::fs::write(runner.root.join(path), content).unwrap();
        }
        commit(&mut runner);
        let base = runner.head().unwrap();
        std::fs::remove_file(runner.root.join("scripts/old_module.py")).unwrap();
        std::fs::write(runner.root.join(INDEX), "schema_version=1\n[[script]]\nname='retained'\npath='scripts/retained.sh'\npublish='internal'\n").unwrap();
        std::fs::write(runner.root.join(MANIFEST), "scripts\n").unwrap();
        commit(&mut runner);
        Self {
            _directory: directory,
            runner,
            base,
            metadata: serde_json::from_value(
                serde_json::json!({"packages":[], "workspace_members":[]}),
            )
            .unwrap(),
        }
    }

    fn owned(&mut self) -> BTreeSet<PathBuf> {
        owned_removals(
            &mut self.runner,
            &self.base,
            &[
                INDEX.into(),
                MANIFEST.into(),
                "scripts/old_module.py".into(),
            ],
            &self.metadata,
        )
        .unwrap()
    }
}

fn commit(runner: &mut Runner) {
    runner.git(&["add", "-A"]).unwrap();
    runner
        .git(&[
            "-c",
            "user.name=AY test",
            "-c",
            "user.email=test@example.invalid",
            "commit",
            "--quiet",
            "--no-gpg-sign",
            "-m",
            "fixture",
        ])
        .unwrap();
}

#[test]
fn real_tree_retirement_has_native_owner_and_retained_consumers_refuse() {
    assert_eq!(Repository::new(None).owned().len(), 3);
    for consumer in [
        ("consumer.rs", "include_str!(\"scripts/old_module.py\");"),
        ("consumer.sh", "ay scripts run retired-command"),
        ("consumer.py", "import old_module"),
        ("consumer.bin", "\0old_module.py\0"),
    ] {
        assert!(Repository::new(Some(consumer)).owned().is_empty());
    }
}

#[test]
fn declared_runtime_inputs_and_unrelated_manifest_edits_refuse() {
    let mut repository = Repository::new(None);
    repository.metadata.packages = serde_json::from_value(serde_json::json!([{
        "id":"owner", "name":"owner", "manifest_path":repository.runner.root.join("Cargo.toml"),
        "edition":"2021", "targets":[], "metadata":{"ay-provenance":{"inputs":["scripts/old_module.py"]}}
    }])).unwrap();
    assert!(repository.owned().is_empty());
    repository.metadata.packages.clear();
    std::fs::write(repository.runner.root.join(MANIFEST), "other-export\n").unwrap();
    commit(&mut repository.runner);
    assert!(repository.owned().is_empty());
}

#[test]
fn removing_only_the_catalog_entry_does_not_retire_a_live_script() {
    let mut repository = Repository::new(None);
    std::fs::write(
        repository.runner.root.join("scripts/old_module.py"),
        "exit 0\n",
    )
    .unwrap();
    commit(&mut repository.runner);
    assert!(repository.owned().is_empty());
}

#[cfg(unix)]
#[test]
fn retained_symlink_cannot_hide_a_deleted_consumer() {
    let mut repository = Repository::new(None);
    std::os::unix::fs::symlink(
        "scripts/old_module.py",
        repository.runner.root.join("alias"),
    )
    .unwrap();
    commit(&mut repository.runner);
    assert!(repository.owned().is_empty());
}
