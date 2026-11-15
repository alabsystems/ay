// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #quantifier-ce-free-resolve (stage 4 of the quantifier-instantiation plan):
//! a CEGQI-forall refutation the disambiguation apparatus cannot attribute is
//! re-derived from the counterexample-free consequence set instead of failing
//! closed.
//!
//! Measured 2026-09-12 on `UFLIA simplify2 javafe.ast.BranchStmt.002` (build
//! 9660 / `b03981ee9b`, `--z3-mode -T:10`): the ground solve over 2,794
//! E-matched instances plus nine counterexample conjuncts refutes, the live
//! strict proof is a lone `trust` step in the default posture and absent in
//! the campaign posture, the authored consequence replay declines (124 roots
//! against its budget of 64), the verdict-only consequence certificate is
//! firewalled for every public query, and the file publishes
//! `unknown (incomplete quantifier-cegqi)`. z3 5.1.0 answers `unsat`. With the
//! nine conjuncts removed from the exact pre-dispatch vector the same lane
//! refutes in 0.2 s, and the verdict is classified as an E-matching-only
//! refutation.
//!
//! Corpus-backed, following the workspace convention (skip when absent, fail
//! under `AY_REQUIRE_CORPUS=1` through `common::corpus_skip_allowed` so a
//! vacuous run cannot pass as a pass).

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

use crate::common;

const BRANCH_STMT_002: &str = "benchmarks/smtlib-all/UFLIA/\
non-incremental__UFLIA__simplify2__front_end_suite__javafe.ast.BranchStmt.002.smt2";

struct Run {
    verdict: String,
    ce_lemmas: u64,
    resolves: u64,
    refutations: u64,
}

fn solve(smt: &str, timeout: Duration) -> Run {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(timeout));
    // The default posture. The refutation publishes with an honest holey
    // certificate (`unproved_steps=1 ay_self_checkable=no`, admission
    // `discharged-trust`). This used to run under `--z3-mode`
    // (`set_competition_mode(true)`), the capability measurement's posture;
    // there the quantifier preprocessing pipeline now refutes the file before
    // CEGQI runs (its window already holds a literal `false`: 0.10 s, no
    // counterexample lemma), so the mechanism is exercised where the pipeline
    // refuses its unjustified passes. Measured 2026-09-30 on d7090ae8b0:
    // default posture 8 ce-lemmas, 1 re-solve, `unsat`; with the switch off,
    // 7 ce-lemmas and `unknown`.
    exec.set_memory_limit(Some(8 << 30));
    let lines = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    let verdict = lines
        .iter()
        .map(|l| l.trim().to_string())
        .find(|l| matches!(l.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "none".to_string());
    let stats = exec.statistics();
    Run {
        verdict,
        ce_lemmas: stats.get_int("quantifier.cegqi.ce_lemmas").unwrap_or(0),
        resolves: stats
            .get_int("quantifier.cegqi.ce_free_resolves")
            .unwrap_or(0),
        refutations: stats
            .get_int("quantifier.cegqi.ce_free_resolve_refutations")
            .unwrap_or(0),
    }
}

#[test]
fn branchstmt_002_refutes_through_the_ce_free_resolve() {
    let path = common::workspace_path(BRANCH_STMT_002);
    let Ok(smt) = std::fs::read_to_string(&path) else {
        // Under `AY_REQUIRE_CORPUS=1` this asserts instead of skipping, so a
        // vacuous run cannot pass as a pass. Fetch with `ay-z3-parity fetch
        // benchmarks/smtlib-all --divisions UFLIA`.
        assert!(common::corpus_skip_allowed(&path));
        eprintln!("SKIP: {BRANCH_STMT_002} is not present.");
        return;
    };
    assert!(
        smt.contains("(set-info :status unsat)"),
        "corpus file no longer declares `:status unsat` — re-derive the ground \
         truth before trusting this guard"
    );

    // Ground-first scheduling (#qe-ground-first) refutes this file's
    // axiom-free remainder before the CEGQI round mints its counterexample
    // lemma, so the re-solve this guard pins is measured with it switched off:
    // the mechanism still decides whenever that pass declines.
    //
    // Control: with the re-solve off, the base tree's fail-closed verdict.
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quantifier_ce_free_resolve: true,
        no_ground_first: true,
        ..Default::default()
    });
    let off = solve(&smt, Duration::from_secs(60));
    drop(guard);
    assert!(
        off.ce_lemmas >= 1,
        "the fixture no longer mints a counterexample lemma (ce_lemmas={}); it has \
         stopped exercising the mechanism and this guard needs a new one",
        off.ce_lemmas
    );
    assert_eq!(
        off.resolves, 0,
        "the switch must keep the re-solve from running"
    );
    assert_eq!(
        off.verdict, "unknown",
        "control: BranchStmt.002 with the re-solve off must still fail closed"
    );

    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_ground_first: true,
        ..Default::default()
    });
    let on = solve(&smt, Duration::from_secs(60));
    drop(guard);
    assert_eq!(
        on.resolves, 1,
        "exactly one re-solve (verdict={})",
        on.verdict
    );
    assert_eq!(on.refutations, 1, "the CE-free re-solve must refute");
    assert_eq!(on.verdict, "unsat");

    // And with every pass on, the file publishes the same refutation.
    assert_eq!(solve(&smt, Duration::from_secs(60)).verdict, "unsat");
}
