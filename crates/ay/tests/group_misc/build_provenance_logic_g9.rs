// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The stamp decision of `build_support/provenance.rs` (G9), on a small
//! workspace in its own git repository: which files a stamp vouches for and
//! watches, when it says `-dirty`, that a commit leaving every input alone
//! keeps it, and that taking it never writes the git index.

#[allow(dead_code)]
#[path = "../../../../build_support/provenance.rs"]
mod provenance;

use ntest::timeout;
use provenance::json::{self, Value};
use provenance::scope::outermost;
use provenance::{decide_stamp, CommitSource, StampDecision, StampRequest};
use std::path::{Path, PathBuf};
use std::process::Command;

#[path = "build_provenance_repo_g9.rs"]
mod repository;

/// A workspace in its own repository: `app` depends on `dep`, dev-depends on
/// `other`, and embeds `data/embedded.txt`; `docs/` and `README.md` are not
/// built into anything.
struct Fixture {
    root: PathBuf,
}

const FIXTURE_FILES: [(&str, &str); 11] = [
    (
        "Cargo.toml",
        "[workspace]\nresolver = \"2\"\nmembers = [\"crates/app\", \"crates/dep\", \"crates/other\"]\n",
    ),
    (
        "crates/app/Cargo.toml",
        "[package]\nname = \"app\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n\
         [dependencies]\ndep = { path = \"../dep\" }\n\n\
         [dev-dependencies]\nother = { path = \"../other\" }\n\n\
         [package.metadata.ay-provenance]\ninputs = [\"../../data/embedded.txt\"]\n",
    ),
    ("crates/app/src/lib.rs", "pub fn app() {}\n"),
    ("crates/app/tests/app.rs", "#[test]\nfn t() {}\n"),
    (
        "crates/dep/Cargo.toml",
        "[package]\nname = \"dep\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    ),
    ("crates/dep/src/lib.rs", "pub fn dep() {}\n"),
    (
        "crates/other/Cargo.toml",
        "[package]\nname = \"other\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    ),
    ("crates/other/src/lib.rs", "pub fn other() {}\n"),
    ("data/embedded.txt", "embedded\n"),
    ("the development design notes", "# Guide\n"),
    ("README.md", "# Fixture\n"),
];

impl Fixture {
    fn new(name: &str) -> Self {
        let root = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("g9-provenance-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let fixture = Self { root };
        for (path, content) in FIXTURE_FILES {
            fixture.write(path, content);
        }
        fixture.git(&["init", "-q"]);
        fixture.git(&["add", "-A"]);
        fixture.commit("initial");
        fixture
    }

    fn write(&self, path: &str, content: &str) {
        let path = self.root.join(path);
        std::fs::create_dir_all(path.parent().expect("fixture paths have a parent"))
            .expect("create fixture directory");
        std::fs::write(&path, content).expect("write fixture file");
    }

    fn remove(&self, path: &str) {
        std::fs::remove_file(self.root.join(path)).expect("remove fixture file");
    }

    fn git(&self, args: &[&str]) -> String {
        let output = Command::new("git")
            .current_dir(&self.root)
            .env_remove("GIT_DIR")
            .env_remove("GIT_WORK_TREE")
            .env_remove("GIT_INDEX_FILE")
            .args(args)
            .output()
            .expect("run git");
        assert!(
            output.status.success(),
            "git {args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).expect("git prints UTF-8")
    }

    fn commit(&self, message: &str) {
        self.git(&[
            "-c",
            "user.name=fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "-c",
            "commit.gpgsign=false",
            "commit",
            "-q",
            "--no-verify",
            "--allow-empty",
            "-m",
            message,
        ]);
    }

    fn head(&self) -> String {
        self.git(&["rev-parse", "HEAD"]).trim().to_string()
    }

    fn index(&self) -> Vec<u8> {
        std::fs::read(self.root.join(".git/index")).expect("read the fixture index")
    }

    fn decide(&self) -> StampDecision {
        self.decide_with(None)
    }

    fn decide_with(&self, commit_override: Option<String>) -> StampDecision {
        decide_stamp(&StampRequest {
            package_dir: &self.root.join("crates/app"),
            version: "0.1.0",
            cargo: &cargo(),
            commit_override,
            source_date_epoch: Some(0),
        })
    }

    /// Watched paths, relative to the fixture root.
    fn watched(&self, decision: &StampDecision) -> Vec<String> {
        let root = std::fs::canonicalize(&self.root).expect("canonical fixture root");
        decision
            .watched
            .iter()
            .map(|path| {
                path.strip_prefix(&root)
                    .unwrap_or_else(|_| panic!("{} is outside the fixture", path.display()))
                    .to_string_lossy()
                    .replace('\\', "/")
            })
            .collect()
    }
}

/// The cargo running these tests, for `cargo metadata`.
pub(crate) fn cargo() -> PathBuf {
    std::env::var_os("CARGO")
        .map(PathBuf::from)
        .or_else(|| option_env!("CARGO").map(PathBuf::from))
        .unwrap_or_else(|| PathBuf::from("cargo"))
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.root);
    }
}

#[test]
#[timeout(120_000)]
fn a_stamp_covers_the_build_closure_and_nothing_else() {
    let fixture = Fixture::new("closure");
    let decision = fixture.decide();
    let scope = decision
        .scope
        .as_ref()
        .expect("a git checkout has an input scope");
    assert_eq!(scope.derivation.name(), "cargo-metadata");
    assert_eq!(
        scope
            .packages
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        ["app", "dep"],
        "a dev-dependency is not built into the crate"
    );
    assert_eq!(
        scope.pathspecs,
        [
            ".cargo/config.toml",
            "Cargo.lock",
            "Cargo.toml",
            "build_support",
            "crates/app/Cargo.toml",
            "crates/app/src",
            "crates/dep/Cargo.toml",
            "crates/dep/src",
            "data/embedded.txt",
            "rust-toolchain.toml",
        ],
        "the workspace build files, then each package's manifest, target source \
         directories and declared embeds"
    );
    assert_eq!(
        fixture.watched(&decision),
        [
            "Cargo.toml",
            "crates/app/Cargo.toml",
            "crates/app/src/lib.rs",
            "crates/dep/Cargo.toml",
            "crates/dep/src/lib.rs",
            "data/embedded.txt",
        ],
        "a stamp watches its input files and nothing else"
    );
    assert_eq!(decision.source, CommitSource::Git);
    assert_eq!(decision.provenance.commit, fixture.head());
    assert_eq!(
        decision.provenance.stamp,
        format!("0.1.0+build.1.{}@1970-01-01T00:00:00Z", fixture.head())
    );
}

#[test]
#[timeout(120_000)]
fn only_a_change_to_an_input_dirties_the_stamp() {
    let fixture = Fixture::new("dirty");
    let head = fixture.head();
    let commit = |fixture: &Fixture| fixture.decide().provenance.commit;
    let dirty = format!("{head}-dirty");

    for (path, content) in [
        ("the development design notes", "# Guide, edited\n"),
        ("README.md", "# Fixture, edited\n"),
        ("crates/other/src/lib.rs", "pub fn other() -> u8 { 1 }\n"),
        ("crates/app/tests/app.rs", "#[test]\nfn edited() {}\n"),
        ("the development design notes", "# New\n"),
    ] {
        fixture.write(path, content);
        assert_eq!(commit(&fixture), head, "{path} is not an input");
    }
    for (path, edited, original) in [
        ("crates/dep/src/lib.rs", "pub fn dep() -> u8 { 1 }\n", "pub fn dep() {}\n"),
        ("crates/app/src/lib.rs", "pub fn app() -> u8 { 1 }\n", "pub fn app() {}\n"),
        ("data/embedded.txt", "changed\n", "embedded\n"),
        ("Cargo.toml", "[workspace]\nresolver = \"2\"\nmembers = [\"crates/app\", \"crates/dep\", \"crates/other\"]\n# edited\n", FIXTURE_FILES[0].1),
    ] {
        fixture.write(path, edited);
        assert_eq!(commit(&fixture), dirty, "{path} is an input");
        fixture.write(path, original);
        assert_eq!(commit(&fixture), head, "{path} restored");
    }
    // An untracked file among the inputs can be compiled (`mod new;`).
    fixture.write("crates/dep/src/new.rs", "pub fn new() {}\n");
    assert_eq!(
        commit(&fixture),
        dirty,
        "an untracked input is a difference"
    );
    fixture.remove("crates/dep/src/new.rs");
    // So is a deleted one, and the nearest directory that exists is watched
    // in its place: Cargo reruns on every build while a watched path is missing.
    fixture.remove("crates/dep/src/lib.rs");
    let decision = fixture.decide();
    assert_eq!(decision.provenance.commit, dirty);
    assert!(fixture
        .watched(&decision)
        .contains(&"crates/dep/src".to_string()));
}

#[test]
#[timeout(120_000)]
fn no_stamp_follows_head_so_a_docs_only_commit_keeps_it() {
    let fixture = Fixture::new("head");
    let git_dir = std::fs::canonicalize(fixture.root.join(".git")).expect("fixture git dir");
    let in_git_dir = |decision: &StampDecision| -> Vec<String> {
        decision
            .watched
            .iter()
            .filter_map(|path| path.strip_prefix(&git_dir).ok())
            .map(|path| path.to_string_lossy().replace('\\', "/"))
            .collect()
    };

    let stamp = fixture.decide();
    assert!(
        in_git_dir(&stamp).is_empty(),
        "a stamp must not watch git metadata, in any profile (DR-48): {:?}",
        in_git_dir(&stamp)
    );

    // A docs-only commit moves HEAD and no input: nothing the stamp watches
    // changed, so Cargo keeps it, and the commit it names still has the
    // inputs that were compiled.
    let before = fixture.head();
    fixture.write("the development design notes", "# Guide, committed\n");
    fixture.git(&["add", "-A"]);
    fixture.commit("docs only");
    assert_ne!(fixture.head(), before);
    assert_eq!(
        fixture.git(&[
            "diff",
            "--name-only",
            &before,
            "--",
            "crates/app/src",
            "crates/dep/src"
        ]),
        ""
    );
    let watched_before = fixture.watched(&stamp);
    assert_eq!(
        fixture.watched(&fixture.decide()),
        watched_before,
        "the commit changed what the stamp watches"
    );
}

#[test]
#[timeout(120_000)]
fn taking_a_stamp_never_writes_the_git_index() {
    let fixture = Fixture::new("index");
    // Rewrite a tracked input with the same bytes a moment later: its cached
    // stat data is stale, so a plain `git status` refreshes and rewrites the index.
    std::thread::sleep(std::time::Duration::from_millis(1_100));
    fixture.write("crates/dep/src/lib.rs", "pub fn dep() {}\n");
    let before = fixture.index();
    let decision = fixture.decide();
    assert_eq!(
        decision.provenance.commit,
        fixture.head(),
        "same bytes, clean stamp"
    );
    assert!(
        fixture.index() == before,
        "taking a stamp rewrote the index"
    );
    // The control: the fixture does provoke the write the stamp avoids.
    let output = Command::new("git")
        .current_dir(&fixture.root)
        .env_remove("GIT_OPTIONAL_LOCKS")
        .args(["status", "--porcelain"])
        .output()
        .expect("run git status");
    assert!(output.status.success());
    assert!(
        fixture.index() != before,
        "plain `git status` should have refreshed the index, or this test proves nothing"
    );
}

#[test]
#[timeout(120_000)]
fn an_environment_commit_watches_no_files() {
    let fixture = Fixture::new("environment");
    let decision = fixture.decide_with(Some("0123abcd-dirty".to_string()));
    assert_eq!(decision.source, CommitSource::Environment);
    assert_eq!(decision.provenance.commit, "0123abcd-dirty");
    assert!(decision.scope.is_none());
    assert!(decision.watched.is_empty(), "{:?}", decision.watched);
}

#[test]
fn outermost_pathspecs_drop_the_nested_and_the_repeated() {
    assert_eq!(
        outermost(
            [
                "crates/ay/src",
                "crates/ay-cp/src",
                "crates/ay/src/bin",
                "crates/ay/src",
                "crates/ay"
            ]
            .map(str::to_string)
        ),
        ["crates/ay", "crates/ay-cp/src"]
    );
    assert_eq!(outermost(["crates", "."].map(str::to_string)), ["."]);
}

#[test]
fn the_metadata_reader_parses_json_and_refuses_what_is_not() {
    let value = json::parse(
        r#" {"a": [1, -2.5e3, true, false, null], "s": "q\"\\\/\b\f\n\r\t\u00e9\ud83d\ude00", "o": {}} "#,
    )
    .expect("valid JSON");
    assert_eq!(
        value.get("a").and_then(Value::as_array).map(<[Value]>::len),
        Some(5)
    );
    assert_eq!(
        value.get("s").and_then(Value::as_str),
        Some("q\"\\/\u{8}\u{c}\n\r\t\u{e9}\u{1f600}")
    );
    assert_eq!(value.get("o"), Some(&Value::Object(Vec::new())));
    for malformed in [
        "",
        "{",
        "[1,]",
        "{\"a\" 1}",
        "\"\\ud800\"",
        "\"\\x\"",
        "\"raw\ncontrol\"",
        "[] []",
        "tru",
    ] {
        assert_eq!(json::parse(malformed), None, "{malformed:?}");
    }
    let deep = format!("{}{}", "[".repeat(200), "]".repeat(200));
    assert_eq!(
        json::parse(&deep),
        None,
        "nesting past the limit is refused"
    );
}
