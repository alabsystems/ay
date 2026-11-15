// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WRONG-`unsat` canaries — the files that began REFINING when the Horner
//! fail-open was closed (568f1160d, 2026-08-05).
//!
//! # Why these files, and why now
//!
//! `check_monomial_consistency` is the only thing tying `nra_check_loop`'s linear
//! abstraction back to reality: every nonlinear product is a free opaque LRA
//! column, and nothing else forces that column to equal the product it denotes.
//! It resolved each factor with `lra.get_value` and, on `None`, returned `true`
//! — "consistent" — having checked nothing.
//!
//! MetiTarski emits Taylor polynomials in HORNER form, so every product nests a
//! compound `+` as its last factor. A `(+ ...)` node is a linear combination,
//! not a tableau column, so `get_value` returns `None`. MEASURED on
//! `sqrt-1mcosq-7-chunk-0170`: **all 30 monomials fail-opened**, so
//! `has_inconsistent_monomials()` was false VACUOUSLY and `Sat` returned at
//! **iteration 0** with zero nonlinear reasoning.
//!
//! # The exposure this pins, which is NOT the defect that was fixed
//!
//! Closing the fail-open makes the `Sat` exit harder to reach, so these 12 files
//! iterate past iteration 0 **for the first time**. Past iteration 0
//! `nra_check_loop` can return a genuine `TheoryResult::Unsat`
//! (`check_loop.rs`), and `try_tentative_patch` keeps its patch cuts active when
//! it succeeds with divisions still inconsistent, falling through toward that
//! same branch. The fix also makes `compute_monomial_product` resolve Horner
//! factors, so strictly MORE monomials now reach the patch planner.
//!
//! Empirically this cost nothing — zero `unsat` across all 936 MV QF_NRA files,
//! the 8 `wrong_unsat_metitarski_exp` canaries and the 4 `f2_rw361` variants —
//! but none of these 12 was covered by any existing canary. A verifier flagged
//! that gap; this file closes it. The point is not that a wrong `unsat` was
//! observed. It is that these files newly execute code that can produce one, and
//! **a wrong `unsat` cannot be caught by any gate AY has**: every gate validates
//! a MODEL, and a model exists only on the `sat` side.
//!
//! # One-sided, deliberately
//!
//! Asserted as `!= unsat`, never `== sat`. All 12 answer `unknown` today and
//! that is the honest fail-closed answer. Tightening to `== sat` is welcome the
//! day the engine earns it — but never weaken this to allow `unsat`.
//!
//! # Why this lives here, on committed fixtures
//!
//! 1c83f0a26 put this canary in `crates/ay-dpll/tests/`, reading the five
//! benchmarks from the gitignored `benchmarks/smtlib-all` corpus and driving
//! `common::workspace_path("target/release/ay")`. Neither input was the one
//! the canary meant:
//!
//! * On 2026-09-24 the benchmarks existed on no host, so every run skipped
//!   (`AY-TEST-SKIP ... reason=corpus-file-absent`) and checked nothing.
//! * `target/release/ay` is not the binary under test. A lane whose
//!   `CARGO_TARGET_DIR` is outside the tree never has one there, and in a git
//!   worktree `workspace_path` falls back to the main checkout, whose
//!   `target/release/ay` belongs to another commit — from this host's
//!   worktrees, `ay 0.22.0+build.9127.c93a232b2`, built 2026-08-30. With the
//!   corpus supplied, the canary would have reported on that binary.
//!
//! So the benchmarks are committed under `benchmarks/smt/regression/
//! horner_refining/` and read through `tracked_fixture`, and the solver is
//! `CARGO_BIN_EXE_ay`, which cargo builds from this tree for this test. They
//! are not force-added under `benchmarks/smtlib-all`: `.gitignore` keeps that
//! tree out by policy, gate scripts replace it with a symlink to a shared
//! corpus, and `ay-z3-parity fetch` swaps its division directories wholesale.
//! A sound tree has both inputs, so neither is a skip.
//!
//! Under `debug_assertions` `nra_check_loop` stops at 15 iterations (500 in
//! release), so a debug lane runs iterations 1..=15 of the path this pins and
//! `cargo test --release` the full range.
//!
//! Provenance: SMT-LIB release 2025 (non-incremental), Zenodo record 15493090,
//! `QF_NRA.tar.zst`, CC BY 4.0. Each fixture is, byte for byte, the archive
//! member its flattened name spells (`non-incremental__QF_NRA__meti-tarski__
//! sqrt__1mcosq__7__...` is `non-incremental/QF_NRA/meti-tarski/sqrt/1mcosq/7/
//! ...`). Every one declares `(set-info :status sat)` and z3 4.8.12 answers
//! `sat` on each. The full list of 12 is
//! the development design notes.

use ntest::timeout;
use std::io::ErrorKind;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::corpus::tracked_fixture;
use crate::spawn::OutputTimeout;

/// The canaries' committed home (see the module docs for why it is not
/// `benchmarks/smtlib-all`).
const DIR: &str = "benchmarks/smt/regression/horner_refining";

/// A representative subset of the 12, one per distinct family, under their
/// flattened SMT-LIB names.
///
/// Not all twelve: seven are `sqrt-1mcosq-7` chunks that share one mechanism and
/// one code path, so gating on all of them costs wall-clock without adding
/// signal. The full list lives in
/// the development design notes and is swept
/// differentially; this gate is the cheap always-on guard.
const CANARIES: &[&str] = &[
    "non-incremental__QF_NRA__meti-tarski__sqrt__1mcosq__7__sqrt-1mcosq-7-chunk-0170.smt2",
    "non-incremental__QF_NRA__meti-tarski__heartdipole__heartdipole-chunk-0047.smt2",
    "non-incremental__QF_NRA__meti-tarski__Chua__2__IL__L__Chua-2-IL-L-chunk-0107.smt2",
    "non-incremental__QF_NRA__meti-tarski__atan__vega__3__atan-vega-3-chunk-0298.smt2",
    "non-incremental__QF_NRA__meti-tarski__sin__problem__7__weak2__sin-problem-7-weak2-chunk-0099.smt2",
];

/// Short on purpose: these are fail-closed and burn their whole deadline before
/// answering `unknown`, while the failure this pins would announce itself
/// immediately.
const BUDGET_SECS: u64 = 10;

/// The last `sat`/`unsat`/`unknown` line `ay --competition` prints on `path`.
///
/// Driven as a killable child: the in-process cancellation signals are not
/// polled on the NRA path — `set_interrupt` and `set_deadline` were measured
/// overshooting a 10 s budget by more than 10x — so the only reliable bound is
/// a process group this test can kill. A killed child yields no verdict, which
/// this one-sided gate reads as "not unsat".
fn verdict(path: &Path) -> String {
    let output = match Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--competition")
        .arg(format!("-T:{BUDGET_SECS}"))
        .arg(path)
        .output_timeout(Duration::from_secs(BUDGET_SECS + 20))
    {
        Ok(output) => output,
        Err(err) if err.kind() == ErrorKind::TimedOut => return "unknown".to_string(),
        Err(err) => panic!("failed to run ay on {}: {err}", path.display()),
    };
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .rfind(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .unwrap_or("unknown")
        .to_string()
}

#[test]
#[timeout(300_000)]
fn horner_refining_files_are_never_unsat() {
    let mut tripped: Vec<&str> = Vec::new();
    for &name in CANARIES {
        // Committed: a missing file is a broken tree, never a skip.
        let path = tracked_fixture(&format!("{DIR}/{name}"));
        if verdict(&path) == "unsat" {
            tripped.push(name);
        }
    }

    assert!(
        tripped.is_empty(),
        "WRONG-UNSAT REGRESSION: {tripped:?} answered `unsat`. These benchmarks are \
         satisfiable, and they newly execute the post-iteration-0 path in \
         `nra_check_loop` that can return Unsat. A wrong `unsat` is a false theorem \
         and no model gate can catch it."
    );
    eprintln!(
        "horner-refining wrong-unsat canaries: {} checked, none unsat",
        CANARIES.len()
    );
}
