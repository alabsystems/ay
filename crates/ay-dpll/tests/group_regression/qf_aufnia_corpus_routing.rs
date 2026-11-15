// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #qf-aufnia-array-drop, pinned on the SMT-LIB files it was written for.
//!
//! `executor/logic_detect.rs` re-derives a DECLARED `QF_AUFNIA` whose live
//! window carries arrays and no genuine nonlinear arithmetic from the
//! array-LESS `QfUfnia` category to the array-aware `QfAuflia` route. The
//! routing block already has eight synthetic guard pins
//! (`executor_tests/qf_aufnia_array_routing.rs`); nothing pinned it on a real
//! benchmark, so a feature-detection change that stopped recognising the
//! `(* v 4294967296)` window as linear — or a `from_logic` edit — would move
//! all 17 division files back to the array-less lane with every unit test
//! still green.
//!
//! What the array-less lane does with these files is measured, not assumed.
//! 2026-09-17, build 10126 at `7c84c9044d` against the same tree with the
//! routing block reverted, `-T:10`, default posture: the reverted binary
//! prints `--f1-diag: route_to_solver(QfUfnia) -> Sat model_present=true` on
//! 6 of the 10 census gap files — **four of them declared `:status unsat` and
//! z3-unsat** — and each candidate model is then refused by the strict
//! model-validation oracle (`arrays rejected assertion N`), so the file
//! publishes `unknown (incomplete)`. `select`/`store` reaching the search as
//! bare uninterpreted functions is a relaxation of the array axioms: sound for
//! `unsat`, never for `sat`. The model gate was the only thing between AY and
//! a wrong `sat` on an unsat file, and the routing removes the class at its
//! source.
//!
//! These two pins therefore assert exactly two things per file: the lane the
//! window reaches, and that neither posture publishes the wrong verdict. They
//! deliberately do NOT assert a verdict: on today's binary the AUFLIA lane's
//! lazy arm runs both files to the deadline (115 refinement rounds / 370 k
//! decisions on `blast.10` where z3 needs 4 conflicts). That throughput is the
//! array lane's own lever; asserting `unsat` here would pin this guard to a
//! gap that is not this block's to close.
//!
//! Corpus-backed, following the workspace convention: skip when the gitignored
//! corpus is absent, and fail under `AY_REQUIRE_CORPUS=1` so a vacuous run
//! cannot pass as a pass.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

use crate::common;

/// z3 5.1.0 `unsat` in 0.03 s (4 conflicts, 295 array axioms); `:status unsat`.
const BLAST_10_UNSAT: &str = "benchmarks/smtlib-all/QF_AUFNIA/\
non-incremental__QF_AUFNIA__UltimateAutomizer__\
s3_srvr.blast.10_true-unreach-call.i.cil.c_0.smt2";

/// z3 5.1.0 `sat` in 0.77 s; `:status sat`.
const BLAST_11_SAT: &str = "benchmarks/smtlib-all/QF_AUFNIA/\
non-incremental__QF_AUFNIA__UltimateAutomizer__\
s3_srvr.blast.11_false-unreach-call.i.cil.c_0.smt2";

/// Route the file and report the lane it reached plus the published verdict.
///
/// The budget is deliberately small: the assertion is about ROUTING and about
/// the absence of a wrong verdict, and `solver.logic_category` is recorded
/// whether or not the lane finishes.
fn route_and_verdict(relative: &str, declared_status: &str) -> Option<(String, String)> {
    let path = common::workspace_path(relative);
    let Ok(smt) = std::fs::read_to_string(&path) else {
        assert!(
            std::env::var_os("AY_REQUIRE_CORPUS").is_none(),
            "AY_REQUIRE_CORPUS=1 is set and {relative} is not on disk — this \
             guard checked NOTHING. Fetch with `ay-z3-parity fetch \
             benchmarks/smtlib-all --divisions QF_AUFNIA`."
        );
        eprintln!("SKIP: {relative} is not present.");
        return None;
    };
    // The ground truth is the file's own declaration; z3 5.1.0 agrees on both
    // (measured 2026-09-17).
    assert!(
        smt.contains(declared_status),
        "corpus file no longer declares `{declared_status}` — re-derive the \
         ground truth before trusting this guard."
    );
    let commands = parse(&smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(5)));
    // A runaway fails this test instead of the machine, as the shared timeout
    // helper installs elsewhere in this suite.
    exec.set_memory_limit(Some(8 << 30));
    let lines = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    let verdict = lines.last().cloned().unwrap_or_default();
    let category = exec
        .statistics()
        .get_string("solver.logic_category")
        .map(str::to_owned)
        .unwrap_or_default();
    Some((category, verdict))
}

#[test]
fn qf_aufnia_unsat_benchmark_reaches_the_array_lane_and_never_answers_sat() {
    let Some((category, verdict)) = route_and_verdict(BLAST_10_UNSAT, "(set-info :status unsat)")
    else {
        return;
    };
    assert_eq!(
        category, "QfAuflia",
        "declared QF_AUFNIA with linear content must reach the array-aware lane"
    );
    assert_ne!(
        verdict, "sat",
        "the benchmark declares :status unsat and z3 5.1.0 refutes it in 0.03 s"
    );
}

#[test]
fn qf_aufnia_sat_benchmark_reaches_the_array_lane_and_never_answers_unsat() {
    let Some((category, verdict)) = route_and_verdict(BLAST_11_SAT, "(set-info :status sat)")
    else {
        return;
    };
    assert_eq!(
        category, "QfAuflia",
        "declared QF_AUFNIA with linear content must reach the array-aware lane"
    );
    assert_ne!(
        verdict, "unsat",
        "the benchmark declares :status sat and z3 5.1.0 satisfies it in 0.77 s"
    );
}
