// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The stamp decision of `build_support/provenance.rs` (G9) for this
//! repository's own stamping crates.

use super::cargo;
use super::provenance::{decide_stamp, StampRequest};
use ntest::timeout;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The four stamping crates of this repository, decided exactly as their
/// build scripts decide: nothing they watch is, or holds, documentation; no
/// stamp watches any git metadata, the index or HEAD included; and a crate
/// ay-dpll is not built from (ay-cp) is not in its closure, so editing it does
/// not restamp ay-dpll and recompile its twelve dependents.
#[test]
#[timeout(300_000)]
fn this_repositorys_stamping_crates_watch_only_their_inputs() {
    let root = std::fs::canonicalize(Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."))
        .expect("canonical repository root");
    let git = |args: &[&str]| -> String {
        let output = Command::new("git")
            .current_dir(&root)
            .env("GIT_OPTIONAL_LOCKS", "0")
            .arg("--no-optional-locks")
            .args(args)
            .output()
            .expect("run git");
        assert!(output.status.success(), "git {args:?}");
        String::from_utf8(output.stdout).expect("git prints UTF-8")
    };
    let documentation: BTreeSet<PathBuf> = git(&["ls-files", "-z", "--", "docs", ":(glob)*.md"])
        .split('\0')
        .filter(|doc| !doc.is_empty())
        .flat_map(|doc| {
            root.join(doc)
                .ancestors()
                .map(Path::to_path_buf)
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(documentation.len() > 10);
    let git_dirs: Vec<PathBuf> = ["--absolute-git-dir", "--git-common-dir"]
        .iter()
        .map(|flag| {
            std::fs::canonicalize(root.join(git(&["rev-parse", flag]).trim()))
                .expect("canonical git directory")
        })
        .collect();
    for package in ["ay", "ay-dpll", "ay-pb", "ay-ffi"] {
        let decision = decide_stamp(&StampRequest {
            package_dir: &root.join("crates").join(package),
            version: "0.0.0",
            cargo: &cargo(),
            commit_override: None,
            source_date_epoch: Some(0),
        });
        let scope = decision.scope.as_ref().expect("a git checkout has a scope");
        assert_eq!(scope.derivation.name(), "cargo-metadata", "{package}");
        assert!(scope.packages.contains(package), "{package}");
        assert!(decision.watched.len() > 100, "{package} watches too little");
        for path in &decision.watched {
            let shown = path.display();
            assert!(
                !documentation.contains(path),
                "{package} watches documentation: {shown}"
            );
            assert!(path.exists(), "{package} watches a missing path: {shown}");
            assert!(
                !git_dirs.iter().any(|dir| path.starts_with(dir)),
                "the stamp of {package} watches git metadata: {shown}"
            );
        }
    }
    let dpll = decide_stamp(&StampRequest {
        package_dir: &root.join("crates/ay-dpll"),
        version: "0.0.0",
        cargo: &cargo(),
        commit_override: None,
        source_date_epoch: Some(0),
    });
    let packages = &dpll.scope.as_ref().expect("scope").packages;
    assert!(
        packages.contains("ay-sat") && !packages.contains("ay-cp"),
        "{packages:?}"
    );
}
