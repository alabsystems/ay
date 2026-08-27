// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WRONG-`unsat` canaries — the files that began REFINING when the Horner
//! fail-open was closed (2026-08-05).
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
//! Asserted as `!= Unsat`, never `== Sat`. All 12 answer `unknown` today and
//! that is the honest fail-closed answer. Tightening to `== Sat` is welcome the
//! day the engine earns it — but never weaken this to allow `unsat`.
//!
//! Sources: the development design notes (the list),
//! the development design notes.

mod common;

use ntest::timeout;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

/// Drive the built CLI in a killable child.
///
/// Same reasoning as `soundness_canary_metitarski_scaled_monomial.rs`: the
/// in-process cancellation signals are not polled on the NRA path — both
/// `set_interrupt` and `set_deadline` were measured overshooting a 10 s budget
/// by more than 10x — so the only reliable bound is a process we can kill.
fn solve_via_cli(path: &Path, budget_secs: u64) -> Option<String> {
    let bin = common::workspace_path("target/release/ay");
    if !bin.is_file() {
        return None;
    }
    let mut child = Command::new(&bin)
        .arg("--competition")
        .arg(format!("-T:{budget_secs}"))
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", bin.display()));

    if child
        .wait_timeout(Duration::from_secs(budget_secs + 20))
        .expect("failed waiting for ay")
        .is_none()
    {
        let _ = child.kill();
        let _ = child.wait();
        // A killed child yields no verdict, which this gate treats as "not unsat".
        return Some("unknown".to_string());
    }

    let mut out = String::new();
    if let Some(mut h) = child.stdout.take() {
        let _ = h.read_to_string(&mut out);
    }
    Some(
        out.lines()
            .map(str::trim)
            .rfind(|l| matches!(*l, "sat" | "unsat" | "unknown"))
            .unwrap_or("unknown")
            .to_string(),
    )
}

/// A representative subset of the 12, one per distinct family.
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

const DIR: &str = "benchmarks/smtlib-all/QF_NRA";

/// Short on purpose: these are fail-closed and burn their whole deadline before
/// answering `unknown`, while the failure this pins would announce itself
/// immediately.
const BUDGET_SECS: u64 = 10;

#[test]
#[timeout(300_000)]
fn horner_refining_files_are_never_unsat() {
    let mut checked = 0usize;
    let mut tripped: Vec<String> = Vec::new();

    for name in CANARIES {
        let path = common::workspace_path(&format!("{DIR}/{name}"));
        if !path.is_file() {
            eprintln!(
                "skipping wrong-UNSAT canary, benchmark not present: {}",
                path.display()
            );
            continue;
        }
        let Some(verdict) = solve_via_cli(&path, BUDGET_SECS) else {
            eprintln!("skipping wrong-UNSAT canary, target/release/ay not built");
            continue;
        };
        checked += 1;
        if verdict == "unsat" {
            tripped.push((*name).to_string());
        }
    }

    assert!(
        tripped.is_empty(),
        "WRONG-UNSAT REGRESSION: {tripped:?} answered `unsat`. These benchmarks are \
         satisfiable, and they newly execute the post-iteration-0 path in \
         `nra_check_loop` that can return Unsat. A wrong `unsat` is a false theorem \
         and no model gate can catch it."
    );
    eprintln!("horner-refining wrong-unsat canaries: {checked} checked, none unsat");
}
