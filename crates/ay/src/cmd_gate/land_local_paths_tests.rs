// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cmd_gate::land::plan::{self, Metadata};
use crate::cmd_gate::land::scope::RustScope;

fn fixture() -> (tempfile::TempDir, Metadata) {
    let root = tempfile::tempdir().expect("source tree");
    for directory in ["consumer", "unrelated", "imports/leaf", "imports/bridge"] {
        std::fs::create_dir_all(root.path().join(directory).join("src")).unwrap();
        let independent = directory.starts_with("imports/");
        let name = directory.rsplit('/').next().unwrap();
        std::fs::write(
            root.path().join(directory).join("Cargo.toml"),
            format!(
                "{}[package]\nname = '{name}'\nversion = '1.0.0'\nedition = '2024'\n",
                if independent { "[workspace]\n" } else { "" }
            ),
        )
        .unwrap();
        std::fs::write(
            root.path().join(directory).join("src/lib.rs"),
            "pub fn value() -> u32 { 1 }\n",
        )
        .unwrap();
    }
    let packages: Vec<_> = ["consumer", "unrelated", "imports/leaf", "imports/bridge"].iter().map(|directory| {
        let name = directory.rsplit('/').next().unwrap();
        serde_json::json!({"id": name, "name": name, "version": "1.0.0", "source": null,
            "edition": "2024", "manifest_path": root.path().join(directory).join("Cargo.toml"),
            "targets": [{"name": name, "kind": ["lib"], "src_path": root.path().join(directory).join("src/lib.rs")}]})
    }).collect();
    let metadata = serde_json::from_value(serde_json::json!({"packages": packages,
        "workspace_members": ["consumer", "unrelated"],
        "resolve": {"nodes": [
            {"id": "consumer", "dependencies": ["bridge"]},
            {"id": "bridge", "dependencies": ["leaf"]},
            {"id": "leaf", "dependencies": []},
            {"id": "unrelated", "dependencies": []}]}}))
    .unwrap();
    (root, metadata)
}

fn runtime_packages(plan: &plan::Plan) -> BTreeSet<&str> {
    plan.steps
        .iter()
        .filter(|step| step.kind == crate::cmd_gate::land::process::StepKind::RustTests)
        .flat_map(|step| {
            step.args
                .windows(2)
                .filter(|args| args[0] == "-p")
                .map(|args| args[1].as_str())
        })
        .collect()
}

#[test]
fn independent_source_keeps_its_owner_edition_and_checks_the_real_importer() {
    let (root, metadata) = fixture();
    let graph = Graph::read(root.path(), &metadata).unwrap();
    let owner = graph
        .foreign_owner(&root.path().join("imports/leaf/src/lib.rs"), &[])
        .unwrap();
    assert_eq!(
        (owner.name.as_str(), owner.edition.as_str()),
        ("leaf", "2024")
    );
    let plan = plan::select(
        root.path(),
        &metadata,
        vec!["imports/leaf/src/lib.rs".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(!plan.broad_compile);
    assert_eq!(runtime_packages(&plan), BTreeSet::from(["consumer"]));
    assert!(
        !plan.steps.iter().any(|step| step.program == "trustfmt"),
        "foreign workspace source is not reformatted as importing-workspace code"
    );
}

#[test]
fn declared_foreign_provenance_keeps_its_consumer_even_for_document_inputs() {
    let (root, mut metadata) = fixture();
    metadata
        .packages
        .iter_mut()
        .find(|package| package.name == "leaf")
        .unwrap()
        .metadata = serde_json::json!({"ay-provenance":{"inputs":["../../shared/schema.md"]}});
    let plan = plan::select(
        root.path(),
        &metadata,
        vec!["shared/schema.md".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(!plan.broad_compile);
    assert_eq!(runtime_packages(&plan), BTreeSet::from(["consumer"]));
}

#[test]
fn in_tree_lock_additions_are_local_but_registry_and_unknown_entries_are_broad() {
    let (root, metadata) = fixture();
    let before = "version = 4\npackage = []\n";
    let after = "version = 4\n[[package]]\nname = 'leaf'\nversion = '1.0.0'\n";
    std::fs::write(root.path().join("Cargo.lock"), after).unwrap();
    let local = plan::select(
        root.path(),
        &metadata,
        vec!["Cargo.lock".into()],
        Some(before),
        &RustScope::default(),
    )
    .unwrap();
    assert!(!local.broad_compile);
    assert_eq!(runtime_packages(&local), BTreeSet::from(["consumer"]));
    for entry in [
        after.replace("'leaf'", "'unknown'"),
        format!("{after}source = 'registry+example'\nchecksum = 'abc'\n"),
        after.replace("'1.0.0'", "'2.0.0'"),
    ] {
        std::fs::write(root.path().join("Cargo.lock"), entry).unwrap();
        assert!(
            plan::select(
                root.path(),
                &metadata,
                vec!["Cargo.lock".into()],
                Some(before),
                &RustScope::default()
            )
            .unwrap()
            .broad_compile
        );
    }
}

#[test]
fn missing_resolution_or_unconnected_local_source_cannot_claim_scoped_coverage() {
    let (root, mut metadata) = fixture();
    for missing in [false, true] {
        if missing {
            metadata.resolve = None;
        } else {
            metadata
                .resolve
                .as_mut()
                .unwrap()
                .nodes
                .iter_mut()
                .find(|node| node.id == "bridge")
                .unwrap()
                .dependencies
                .clear();
        }
        assert!(
            plan::select(
                root.path(),
                &metadata,
                vec!["imports/leaf/src/lib.rs".into()],
                None,
                &RustScope::default()
            )
            .unwrap()
            .broad_compile
        );
    }
}

#[test]
fn only_new_independent_exclusions_with_unchanged_configuration_can_narrow() {
    let (root, metadata) = fixture();
    let old = "[workspace]\nmembers = ['consumer', 'unrelated']\n";
    let new = format!("{old}exclude = ['imports/leaf']\n");
    let base = BTreeSet::from([
        PathBuf::from("consumer/Cargo.toml"),
        PathBuf::from("unrelated/Cargo.toml"),
    ]);
    std::fs::write(root.path().join("Cargo.toml"), &new).unwrap();
    let graph = Graph::read(root.path(), &metadata).unwrap();
    assert!(graph
        .only_adds_independent_exclusions(Some(old), Some(&base))
        .unwrap());
    let mut existed = base.clone();
    existed.insert("imports/leaf/Cargo.toml".into());
    assert!(!graph
        .only_adds_independent_exclusions(Some(old), Some(&existed))
        .unwrap());
    for changed in [
        new.replace("'imports/leaf'", "'consumer'"),
        new.replace("'imports/leaf'", "'imports/*'"),
        format!("{new}\n[profile.release]\nopt-level=1\n"),
        new.replace("'consumer', 'unrelated'", "'consumer'"),
    ] {
        std::fs::write(root.path().join("Cargo.toml"), changed).unwrap();
        assert!(!graph
            .only_adds_independent_exclusions(Some(old), Some(&base))
            .unwrap());
    }
}

#[test]
fn out_of_tree_or_registry_sources_cannot_become_local_owners() {
    let (root, mut metadata) = fixture();
    for registry in [false, true] {
        let leaf = metadata
            .packages
            .iter_mut()
            .find(|package| package.name == "leaf")
            .unwrap();
        leaf.manifest_path = root.path().join("imports/leaf/Cargo.toml");
        if registry {
            leaf.source = Some("registry+example".into());
        } else {
            leaf.manifest_path = root.path().parent().unwrap().join("outside/Cargo.toml");
        }
        let graph = Graph::read(root.path(), &metadata).unwrap();
        assert!(graph
            .foreign_owner(&root.path().join("imports/leaf/src/lib.rs"), &[])
            .is_none());
    }
}

#[test]
fn resolved_ids_and_development_cycles_keep_the_actual_consumer_identity() {
    let (root, mut metadata) = fixture();
    let id = "path+file:///native#leaf@1.0.0";
    metadata
        .packages
        .iter_mut()
        .find(|package| package.name == "leaf")
        .unwrap()
        .id = id.into();
    let nodes = &mut metadata.resolve.as_mut().unwrap().nodes;
    nodes
        .iter_mut()
        .find(|node| node.id == "bridge")
        .unwrap()
        .dependencies = vec![id.into()];
    let leaf = nodes.iter_mut().find(|node| node.id == "leaf").unwrap();
    leaf.id = id.into();
    leaf.dependencies = vec!["bridge".into()];
    let plan = plan::select(
        root.path(),
        &metadata,
        vec!["imports/leaf/src/lib.rs".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(!plan.broad_compile);
    assert_eq!(runtime_packages(&plan), BTreeSet::from(["consumer"]));
}

#[test]
fn a_binary_only_cli_importer_gets_actual_runtime_selection() {
    let (root, mut metadata) = fixture();
    let consumer = metadata
        .packages
        .iter_mut()
        .find(|package| package.name == "consumer")
        .unwrap();
    consumer.name = "ay".into();
    consumer.targets[0].name = "ay".into();
    consumer.targets[0].kind = vec!["bin".into()];
    let plan = plan::select(
        root.path(),
        &metadata,
        vec!["imports/leaf/src/lib.rs".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(!plan.broad_compile);
    assert_eq!(runtime_packages(&plan), BTreeSet::from(["ay"]));
}

#[test]
fn foreign_provenance_does_not_hide_the_physical_workspace_owner() {
    let (root, mut metadata) = fixture();
    metadata
        .packages
        .iter_mut()
        .find(|package| package.name == "leaf")
        .unwrap()
        .metadata = serde_json::json!({"ay-provenance":{"inputs":["../../consumer/src/lib.rs"]}});
    let nodes = &mut metadata.resolve.as_mut().unwrap().nodes;
    nodes
        .iter_mut()
        .find(|node| node.id == "consumer")
        .unwrap()
        .dependencies
        .clear();
    nodes
        .iter_mut()
        .find(|node| node.id == "unrelated")
        .unwrap()
        .dependencies = vec!["bridge".into()];
    let plan = plan::select(
        root.path(),
        &metadata,
        vec!["consumer/src/lib.rs".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(!plan.broad_compile);
    assert_eq!(
        runtime_packages(&plan),
        BTreeSet::from(["consumer", "unrelated"])
    );
    assert!(plan.steps.iter().any(|step| step.program == "trustfmt"));
}

#[test]
fn all_declared_importers_of_one_shared_input_are_retained() {
    let (root, mut metadata) = fixture();
    for package in metadata
        .packages
        .iter_mut()
        .filter(|package| matches!(package.name.as_str(), "leaf" | "bridge"))
    {
        package.metadata =
            serde_json::json!({"ay-provenance":{"inputs":["../../shared/schema.md"]}});
    }
    let nodes = &mut metadata.resolve.as_mut().unwrap().nodes;
    nodes
        .iter_mut()
        .find(|node| node.id == "consumer")
        .unwrap()
        .dependencies = vec!["leaf".into()];
    nodes
        .iter_mut()
        .find(|node| node.id == "unrelated")
        .unwrap()
        .dependencies = vec!["bridge".into()];
    nodes
        .iter_mut()
        .find(|node| node.id == "bridge")
        .unwrap()
        .dependencies
        .clear();
    let plan = plan::select(
        root.path(),
        &metadata,
        vec!["shared/schema.md".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(!plan.broad_compile);
    assert_eq!(
        runtime_packages(&plan),
        BTreeSet::from(["consumer", "unrelated"])
    );
}

#[test]
fn independent_source_keeps_formatting_ownership_inside_a_root_package() {
    let (root, mut metadata) = fixture();
    std::fs::write(
        root.path().join("Cargo.toml"),
        "[package]\nname='consumer'\nversion='1.0.0'\n",
    )
    .unwrap();
    metadata
        .packages
        .iter_mut()
        .find(|package| package.name == "consumer")
        .unwrap()
        .manifest_path = root.path().join("Cargo.toml");
    let plan = plan::select(
        root.path(),
        &metadata,
        vec!["imports/leaf/src/lib.rs".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(!plan.broad_compile);
    assert!(!plan.steps.iter().any(|step| step.program == "trustfmt"));
    assert_eq!(runtime_packages(&plan), BTreeSet::from(["consumer"]));
}

#[test]
fn declared_data_provenance_cannot_hide_workspace_compiler_configuration() {
    let (root, mut metadata) = fixture();
    metadata
        .packages
        .iter_mut()
        .find(|package| package.name == "leaf")
        .unwrap()
        .metadata = serde_json::json!({"ay-provenance":{"inputs":["../../.cargo/config.toml"]}});
    metadata
        .packages
        .iter_mut()
        .find(|package| package.name == "consumer")
        .unwrap()
        .metadata = serde_json::json!({"ay-provenance":{"inputs":["../.cargo/config.toml"]}});
    let plan = plan::select(
        root.path(),
        &metadata,
        vec![".cargo/config.toml".into()],
        None,
        &RustScope::default(),
    )
    .unwrap();
    assert!(plan.broad_compile);
    assert!(runtime_packages(&plan).contains("consumer"));
}
