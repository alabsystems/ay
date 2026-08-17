// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cardinal soundness guard: the AUFLIA Rodin wrong REFUTATION
//! (#auflia-rodin-false-unsat).
//!
//! `non-incremental__AUFLIA__20170829-Rodin__smt4579745768945200905.smt2` is
//! SAT — z3 4.15.4 and the benchmark's own `(set-info :status sat)` agree — and
//! AY answers `unsat`. Re-confirmed live at 0.4.0+build.5825 (`2068d68d`) on
//! 2026-07-26 as one of the 8 still-live disagreements out of the 13 recorded in
//! the development design notes.
//!
//! This is the DANGEROUS direction. A wrong `sat` produces a witness a consumer
//! can (in principle) re-check; a wrong `unsat` silently discharges a
//! verification obligation that is actually satisfiable, and nothing downstream
//! can detect it. It is the only wrong refutation in the corpus set, and it is
//! the highest-severity known defect on the advertised surface.
//!
//! Root cause found and fixed in `832c8861ba`: E-matching was instantiating a
//! bare `Exists` and conjoining the instance as a fact. See the minimal,
//! license-clean companion `false_unsat_auflia_exists_eq.rs` for the mechanism.
//! This file is the end-to-end guard on the real benchmark, kept because the
//! reduced fixture cannot prove the original file is decided soundly.
//!
//! The input is NOT vendored: it is licensed CC BY-NC 4.0
//! (`https://creativecommons.org/licenses/by-nc/4.0/`), which does not fit this
//! Apache-2.0 workspace. The test follows the repo's existing corpus convention
//! (`benchmarks/…` + skip when absent). Fetch it with:
//!
//! ```text
//! cargo build --release -p ay-z3-parity
//! ./target/release/ay-z3-parity fetch benchmarks/smtlib-all --divisions AUFLIA
//! ```

use std::path::PathBuf;

/// Corpus-relative location, as laid down by `ay-z3-parity fetch`.
fn rodin_benchmark() -> PathBuf {
    crate::common::workspace_path(
        "benchmarks/smtlib-all/AUFLIA/\
         non-incremental__AUFLIA__20170829-Rodin__smt4579745768945200905.smt2",
    )
}

/// THE guard: AY must never answer `unsat` on this satisfiable benchmark.
/// `sat` is the right answer; `unknown` is a sound incompleteness. `unsat` is a
/// wrong refutation.
#[test]
fn auflia_rodin_smt4579745768945200905_is_never_unsat() {
    let path = rodin_benchmark();
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!(
            "SKIP: corpus benchmark absent at {}. Fetch with \
             `ay-z3-parity fetch benchmarks/smtlib-all --divisions AUFLIA`.",
            path.display()
        );
        return;
    }
    let smt =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));

    // Guard against a silently-changed corpus file: the ground truth this test
    // asserts against must be the file's own declaration.
    assert!(
        smt.contains("(set-info :status sat)"),
        "corpus file at {} no longer declares `:status sat` — re-derive the \
         ground truth before trusting this guard",
        path.display()
    );

    let results = crate::common::solve_vec(&smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "WRONG REFUTATION: this AUFLIA benchmark is SAT (z3 4.15.4 and its own \
         `:status sat` agree) — answering `unsat` silently discharges a \
         satisfiable obligation. `sat` or `unknown` are both acceptable; got \
         {results:?}"
    );
}
