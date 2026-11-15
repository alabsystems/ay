// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fixture resolution for CLI soundness tests: an absent input is never a verdict.
//!
//! # The defect this closes
//!
//! `group_soundness/uart_23_8758.rs` (#8758, a false UNSAT that "has regressed
//! three times") answered a missing benchmark with the string `"unknown"`, and
//! its oracle is `assert_ne!(result, "unsat")`. `unknown` satisfies that, so
//! wherever the gitignored corpus was absent the guard PASSED having run
//! nothing — and on 2026-09-23 the file existed nowhere on m16. (6a14e726d
//! then vendored that benchmark, so uart_23 now uses [`tracked_fixture`].)
//! Its siblings in the same target had the same shape:
//! `qf_lra_finalize_sat_fail_poison_8754`,
//! `qf_lra_model_validation_5534`, `qf_lra_rebuild_8256`, `qf_lra_stale_reason_8764`
//! and `qf_auflia_storecomm_8785` returned `"unknown"`, and
//! `qf_uf_hwbench_soundness` returned a synthetic `"missing"` that its oracle
//! listed as acceptable. (The storecomm and hwbench benchmarks, and the
//! `ay-dpll` horner canary's, are vendored now too and read through
//! [`tracked_fixture`].) Committed fixtures had the milder form: a silent skip
//! (`qf_lia_puzzles_8762`, `qf_slia_8779`), so a broken tree would also read as
//! a pass. (`qf_auflia_storeinv_8804` had no check at all; `ay` prints nothing
//! on stdout for a missing file, so its two-sided oracle did fail, but as an
//! "unexpected AY output" rather than as a missing fixture.)
//!
//! # The two kinds of input, and what absence means for each
//!
//! * A **tracked fixture** (committed, and shipped by `publish/manifest.txt`) is
//!   part of the test. Absence means the tree is broken, so [`tracked_fixture`]
//!   fails the test.
//! * An **optional corpus file** (gitignored — `benchmarks/.gitignore` keeps
//!   `smtcomp/**/*.smt2` out — or excluded from the public export) may be
//!   absent. [`optional_corpus_file`] returns `None` and announces the skip,
//!   and the caller must return WITHOUT a verdict. Under `AY_REQUIRE_CORPUS=1`
//!   the absence fails instead, through [`corpus_skip_allowed`] — the same gate
//!   `crates/ay-dpll/tests/common/mod.rs` gives its corpus tests (#8529
//!   `synched.base.smt2`, `cooking12`), with the same contract, so the one
//!   variable covers the gated tests of both crates.
//!
//! Optional corpus files resolve like `ay-dpll`'s `workspace_path`: the tree
//! that compiled the test first, then the checkout that owns `.git`, so a git
//! worktree sees the main checkout's gitignored corpus instead of skipping.
//! Tracked fixtures resolve in the compiling tree only.

#![allow(dead_code)]

use std::io::Write;
use std::path::{Path, PathBuf};

/// A workspace-relative path, resolved against the tree that compiled this
/// test, then (for a git worktree, which never holds gitignored corpora) the
/// checkout that owns the repository's `.git`.
pub fn workspace_path(relative: impl AsRef<Path>) -> PathBuf {
    let relative = relative.as_ref();
    let local = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative);
    if local.exists() {
        return local;
    }
    if let Some(main) = git_common_checkout() {
        let shared = main.join(relative);
        if shared.exists() {
            return shared;
        }
    }
    local
}

/// The checkout that owns this repository's `.git` — for a worktree, the main
/// checkout. `None` when git is unavailable or does not answer.
fn git_common_checkout() -> Option<PathBuf> {
    let out = std::process::Command::new("git")
        .args(["rev-parse", "--git-common-dir"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    let dir = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim().to_string());
    let dir = if dir.is_absolute() {
        dir
    } else {
        Path::new(env!("CARGO_MANIFEST_DIR")).join(dir)
    };
    dir.parent().map(Path::to_path_buf)
}

/// Whether an optional corpus file may be skipped. Panics when
/// `AY_REQUIRE_CORPUS` is set, so a bisect, attribution or A/B run can never
/// read a vacuous pass as a good end; otherwise `true`.
///
/// Same contract as `crates/ay-dpll/tests/common/mod.rs::corpus_skip_allowed`.
pub fn corpus_skip_allowed(path: &Path) -> bool {
    assert!(
        std::env::var_os("AY_REQUIRE_CORPUS").is_none(),
        "AY_REQUIRE_CORPUS is set but the corpus file is missing: {}\n\
         This run would otherwise PASS VACUOUSLY. If you are bisecting or \
         attributing, point the worktree at the corpus (symlink \
         benchmarks/smtcomp) rather than trusting this result.",
        path.display()
    );
    true
}

/// An optional (gitignored or export-excluded) corpus file, or `None` when it
/// is absent and skipping is allowed.
///
/// `None` is not a verdict: the caller returns without asserting anything. The
/// skip is written to the raw stderr handle rather than through `eprintln!`,
/// which libtest captures, so a default run still shows which guard did not
/// run. Under `AY_REQUIRE_CORPUS=1` absence panics instead.
pub fn optional_corpus_file(test: &str, relative: &str) -> Option<PathBuf> {
    let path = workspace_path(relative);
    if path.is_file() {
        return Some(path);
    }
    if corpus_skip_allowed(&path) {
        let _ = writeln!(
            std::io::stderr().lock(),
            "AY-TEST-SKIP suite={test} input={} reason=corpus-file-absent \
             (set AY_REQUIRE_CORPUS=1 to fail instead)",
            path.display()
        );
    }
    None
}

/// A committed fixture. Its absence is a broken tree, never a skip and never a
/// verdict, so this fails the test.
///
/// Resolved in the tree that compiled the test ONLY — never through
/// [`workspace_path`]'s fallback to the main checkout, whose copy belongs to a
/// different commit and would hide exactly the broken tree this reports.
pub fn tracked_fixture(relative: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative);
    assert!(
        path.is_file(),
        "tracked fixture missing: {} — it is committed to the repository, so its \
         absence means this tree is broken, not that the guard may be skipped",
        path.display()
    );
    path
}
