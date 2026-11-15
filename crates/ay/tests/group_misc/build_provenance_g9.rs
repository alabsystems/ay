// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Build-provenance rebuild contract.
//!
//! The provenance build scripts of `ay`, `ay-dpll`, `ay-pb` and `ay-ffi` used
//! to watch every tracked file under docs/, scripts/, benchmarks/ and crates/,
//! and `.git/index`. A documentation edit recompiled thirteen crates, and the
//! scripts' own `git status` rewrote the index they watched, so the next build
//! did it again. Cargo reruns a build script, and recompiles its crate and
//! every dependent, only when a path the script watches changes, and recompiles
//! a crate when a file rustc read for it changes. These tests read both records
//! for the `ay` binary under test: the `cargo:rerun-if-changed` lines its build
//! script left in its native run stdout, and rustc's dep-info for the binary and the
//! workspace libraries it links. `build_provenance_logic_g9.rs` checks the
//! other three stamping crates' watch lists on this repository.

use ntest::timeout;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path, PathBuf};
use std::process::Command;

fn repository_root() -> PathBuf {
    canonical(&Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."))
}

fn lexically_normal(path: &Path) -> PathBuf {
    let mut normal = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normal.pop();
            }
            other => normal.push(other),
        }
    }
    normal
}

fn canonical(path: &Path) -> PathBuf {
    let normal = lexically_normal(path);
    std::fs::canonicalize(&normal).unwrap_or(normal)
}

fn git(args: &[&str]) -> String {
    let output = Command::new("git")
        .current_dir(repository_root())
        .env("GIT_OPTIONAL_LOCKS", "0")
        .arg("--no-optional-locks")
        .args(args)
        .output()
        .expect("run git");
    assert!(
        output.status.success(),
        "git {args:?} failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("git prints UTF-8")
}

fn nul_separated(text: &str) -> Vec<String> {
    text.split('\0')
        .filter(|entry| !entry.is_empty())
        .map(str::to_string)
        .collect()
}

fn ay_binary() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_ay"))
}

/// `<target>/<profile>`, where the binary under test was built.
fn profile_dir() -> PathBuf {
    let binary = canonical(&ay_binary());
    binary
        .ancestors()
        .find(|directory| directory.join("ay.d").is_file())
        .expect("the native binary has a profile dep-info record")
        .to_path_buf()
}

/// The git directories of the checkout: its own, and the common one.
fn git_dirs() -> Vec<PathBuf> {
    let root = repository_root();
    ["--absolute-git-dir", "--git-common-dir"]
        .iter()
        .map(|flag| canonical(&root.join(git(&["rev-parse", flag]).trim())))
        .collect()
}

/// Tracked documentation, and every directory above a document: a watched
/// directory is scanned recursively, so watching one of those covers it.
fn documentation_and_its_directories() -> BTreeSet<PathBuf> {
    let root = repository_root();
    let docs = nul_separated(&git(&["ls-files", "-z", "--", "docs", ":(glob)*.md"]));
    assert!(
        docs.len() > 10,
        "the checkout should track documentation to measure against"
    );
    docs.iter()
        .flat_map(|doc| {
            root.join(doc)
                .ancestors()
                .map(Path::to_path_buf)
                .collect::<Vec<_>>()
        })
        .collect()
}

/// What Cargo recorded the `ay` build script as watching in this build: the
/// `rerun-if-changed` lines of its last run, stored in the original run stdout.
fn ay_build_script_watch_list() -> Vec<PathBuf> {
    let out_dir = Path::new(env!("OUT_DIR"));
    let output = out_dir
        .parent()
        .expect("OUT_DIR lives in the build script's run directory")
        .join("run/stdout");
    let text = std::fs::read_to_string(&output)
        .unwrap_or_else(|error| panic!("read {}: {error}", output.display()));
    let package = Path::new(env!("CARGO_MANIFEST_DIR"));
    let watched: Vec<PathBuf> = text
        .lines()
        .filter_map(|line| {
            line.strip_prefix("cargo:rerun-if-changed=")
                .or_else(|| line.strip_prefix("cargo::rerun-if-changed="))
        })
        .map(|path| canonical(&package.join(path)))
        .collect();
    assert!(!watched.is_empty(), "{} watches nothing", output.display());
    watched
}

/// What the `ay` build script recorded about the stamp it took.
struct StampRecord {
    commit: String,
    packages: Vec<String>,
    inputs: Vec<String>,
}

fn stamp_record() -> StampRecord {
    let path = Path::new(env!("OUT_DIR")).join("ay-build-provenance.txt");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "the ay build script records its stamp decision in {}: {error}",
            path.display()
        )
    });
    let mut fields: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for line in text.lines() {
        if let Some((key, value)) = line.split_once('=') {
            fields.entry(key).or_default().push(value.to_string());
        }
    }
    let single = |key: &str| {
        fields
            .get(key)
            .and_then(|values| values.first())
            .cloned()
            .unwrap_or_else(|| panic!("{} has no {key}=: {text}", path.display()))
    };
    StampRecord {
        commit: single("commit"),
        packages: fields.get("package").cloned().unwrap_or_default(),
        inputs: fields.get("input").cloned().unwrap_or_default(),
    }
}

/// One rustc dep-info file: the artifacts it describes and the files read.
struct DepInfo {
    outputs: Vec<PathBuf>,
    inputs: Vec<PathBuf>,
}

/// `<target>: <input> <input> ...` lines; a space inside a path is `\ `.
fn parse_dep_info(text: &str) -> DepInfo {
    let mut outputs = Vec::new();
    let mut inputs = Vec::new();
    for line in text.lines().filter(|line| !line.starts_with('#')) {
        let Some((target, dependencies)) = line.split_once(": ") else {
            continue;
        };
        outputs.push(PathBuf::from(target));
        if inputs.is_empty() {
            let mut current = String::new();
            let mut chars = dependencies.trim().chars().peekable();
            while let Some(character) = chars.next() {
                match character {
                    '\\' if chars.peek() == Some(&' ') => {
                        current.push(' ');
                        chars.next();
                    }
                    ' ' => inputs.push(PathBuf::from(std::mem::take(&mut current))),
                    _ => current.push(character),
                }
            }
            inputs.push(PathBuf::from(current));
            inputs.retain(|input| !input.as_os_str().is_empty());
        }
    }
    DepInfo { outputs, inputs }
}

/// Every file rustc read to compile the `ay` binary under test and the
/// workspace libraries in its stamp's closure, from the dep-info rustc wrote
/// beside each native unit artifact. The binary record must describe the actual
/// binary bytes; other build profiles and test harnesses cannot substitute for it.
fn rustc_inputs_of_the_ay_binary(packages: &[String]) -> BTreeSet<PathBuf> {
    let crates: BTreeSet<String> = packages.iter().map(|name| name.replace('-', "_")).collect();
    let binary = std::fs::read(ay_binary()).expect("read the binary under test");
    let root = repository_root();
    let profile = profile_dir();
    let mut records = Vec::new();
    for package in packages {
        let directory = profile.join("build").join(package);
        let units = match std::fs::read_dir(&directory) {
            Ok(units) => units,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => panic!("read {}: {error}", directory.display()),
        };
        for unit in units {
            let output = unit.expect("read native unit entry").path().join("out");
            let entries = match std::fs::read_dir(&output) {
                Ok(entries) => entries,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => panic!("read {}: {error}", output.display()),
            };
            records.extend(entries.map(|entry| entry.expect("read native output entry").path()));
        }
    }
    let mut inputs = BTreeSet::new();
    let mut found_binary = false;
    for path in records {
        let Some(stem) = path
            .file_name()
            .and_then(|name| name.to_str())
            .and_then(|name| name.strip_suffix(".d"))
        else {
            continue;
        };
        let crate_name = stem.rsplit_once('-').map_or(stem, |(name, _)| name);
        if !crates.contains(crate_name) {
            continue;
        }
        let dep_info = parse_dep_info(&std::fs::read_to_string(&path).expect("read dep-info"));
        // Only a library the binary can link: an `.rlib` that exists. A shared
        // target directory also keeps the dep-info of `cargo check --tests`
        // runs, whose only output is a `lib*.rmeta` compiled under
        // `cfg(test)` (often since deleted), and of test harnesses. Their
        // inputs include `include_str!` test fixtures that no build of the
        // binary reads, and the binary links no `.rmeta`.
        let library = dep_info.outputs.iter().any(|output| {
            let name = output
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            name.starts_with("lib") && name.ends_with(".rlib") && output.is_file()
        });
        let the_binary = !library
            && crate_name == "ay"
            && dep_info.outputs.iter().any(|output| {
                std::fs::metadata(output).is_ok_and(|meta| meta.len() == binary.len() as u64)
                    && std::fs::read(output).is_ok_and(|bytes| bytes == binary)
            });
        found_binary |= the_binary;
        if library || the_binary {
            inputs.extend(
                dep_info
                    .inputs
                    .iter()
                    .map(|input| canonical(&root.join(input))),
            );
        }
    }
    assert!(
        found_binary,
        "no native dep-info in {} describes the binary under test",
        profile.display()
    );
    inputs
}

#[test]
#[timeout(120_000)]
fn a_docs_only_change_reruns_no_build_script_and_rebuilds_nothing() {
    let documentation = documentation_and_its_directories();
    let watched: Vec<PathBuf> = ay_build_script_watch_list()
        .into_iter()
        .filter(|path| documentation.contains(path))
        .collect();
    assert!(
        watched.is_empty(),
        "a docs-only change reruns the ay build script, and so recompiles ay: it \
         watches {} tracked documents or directories holding them, e.g. {:?}",
        watched.len(),
        &watched[..watched.len().min(5)]
    );
    let compiled: Vec<PathBuf> = rustc_inputs_of_the_ay_binary(&stamp_record().packages)
        .into_iter()
        .filter(|path| documentation.contains(path))
        .collect();
    assert!(
        compiled.is_empty(),
        "the ay binary compiles documentation in: {compiled:?}"
    );
}

#[test]
#[timeout(60_000)]
fn the_build_scripts_never_watch_the_git_index() {
    let git_dirs = git_dirs();
    let in_git_dirs: Vec<PathBuf> = ay_build_script_watch_list()
        .into_iter()
        .filter(|entry| git_dirs.iter().any(|dir| entry.starts_with(dir)))
        .collect();
    // `git status` rewrites the index; a script that watches it reruns on the
    // build after its own run, and after any git command anywhere.
    let index: Vec<&PathBuf> = in_git_dirs
        .iter()
        .filter(|entry| entry.file_name().is_some_and(|name| name == "index"))
        .collect();
    assert!(
        index.is_empty(),
        "a build script watches the git index: {index:?}"
    );
    // No stamp follows HEAD, in any profile: a commit or checkout that leaves
    // every input alone reruns no build script and rebuilds nothing (DR-48).
    assert!(
        in_git_dirs.is_empty(),
        "a build script watches git metadata, so a commit or checkout reruns it and \
         recompiles its crate and every dependent: {in_git_dirs:?}"
    );
}

#[test]
#[timeout(60_000)]
fn every_path_the_ay_build_script_watches_exists() {
    // Cargo reruns a build script on every build while a path it watches is missing.
    let missing: Vec<PathBuf> = ay_build_script_watch_list()
        .into_iter()
        .filter(|entry| !entry.exists())
        .collect();
    assert!(
        missing.is_empty(),
        "missing watched paths rerun the build script on every build: {missing:?}"
    );
}

#[test]
#[timeout(120_000)]
fn every_file_the_ay_binary_is_built_from_is_an_input_of_its_stamp() {
    let root = repository_root();
    let target = profile_dir()
        .parent()
        .expect("the profile directory lives in the target directory")
        .to_path_buf();
    let record = stamp_record();
    let inputs: Vec<PathBuf> = record.inputs.iter().map(|input| root.join(input)).collect();
    assert!(!inputs.is_empty(), "the ay stamp names no inputs");
    let compiled = rustc_inputs_of_the_ay_binary(&record.packages);
    assert!(
        compiled.len() > 1_000,
        "rustc dep-info names only {} files",
        compiled.len()
    );
    let uncovered: Vec<&PathBuf> = compiled
        .iter()
        .filter(|path| path.starts_with(&root) && !path.starts_with(&target))
        .filter(|path| !inputs.iter().any(|input| path.starts_with(input)))
        .collect();
    // An uncovered file could change without the stamp saying `-dirty`. A
    // source that embeds a file from outside `src/` declares it in its
    // manifest: `[package.metadata.ay-provenance] inputs = [...]`.
    assert!(
        uncovered.is_empty(),
        "the ay binary is built from files its stamp does not vouch for: {uncovered:?}"
    );
}

fn version_fields() -> BTreeMap<String, String> {
    let output = Command::new(ay_binary())
        .arg("--version")
        .env_remove("CARGO")
        .env_remove("CARGO_TARGET_TMPDIR")
        .output()
        .expect("spawn ay --version");
    assert!(output.status.success(), "ay --version: {:?}", output.status);
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| line.split_once('='))
        .map(|(key, value)| (key.to_string(), value.trim().to_string()))
        .collect()
}

#[test]
#[timeout(60_000)]
fn the_ay_binary_stamp_names_a_commit_whose_inputs_it_was_built_from() {
    let fields = version_fields();
    let commit = fields
        .get("build.commit")
        .unwrap_or_else(|| panic!("ay --version reports no build.commit: {fields:?}"));
    let record = stamp_record();
    assert_eq!(
        &record.commit, commit,
        "--version and the build record disagree"
    );
    let (base, dirty) = commit
        .strip_suffix("-dirty")
        .map_or((commit.as_str(), false), |base| (base, true));
    git(&["cat-file", "-e", &format!("{base}^{{commit}}")]);
    if !dirty {
        // A clean stamp, in any profile, vouches that every input equals C's.
        let mut diff = vec!["diff", "--name-only", base, "--"];
        diff.extend(record.inputs.iter().map(String::as_str));
        let mut untracked = vec!["ls-files", "--others", "--exclude-standard", "--"];
        untracked.extend(record.inputs.iter().map(String::as_str));
        assert_eq!(
            (git(&diff), git(&untracked)),
            (String::new(), String::new()),
            "a clean stamp names {base}, whose inputs differ from the tree"
        );
    }
}
