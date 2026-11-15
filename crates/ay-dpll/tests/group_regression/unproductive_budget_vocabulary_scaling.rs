// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #unproductive-budget-scales-with-vocabulary: the lazy split loop's
//! unproductive-round budget (#7956) must not stop a converging refutation
//! whose theory-atom vocabulary is large.
//!
//! Measured 2026-09-12 on the AUFDTLIRA `spark2014bench string_search.ads_35_14`
//! refutation: with `--quantifier-guarded-enumerative` the ground problem grows
//! from 24 to 524 guarded instance clauses and 7,618 theory atoms, and the
//! refutation needs a 357-round run of theory-conflict rounds with zero
//! propositional conflicts before the lazy AUFLIRA loop reaches `unsat` at
//! round 594. The fixed 128-round budget stopped it at round 131 with
//! `SplitLimit`, the DT lane deepened and repeated the same exit, and the
//! solver published `unknown` after 56 s — no theory returned `Unknown`, no
//! resource budget fired. Scaling both bounds with the vocabulary keeps the
//! calibrated constants exact below 1,024 atoms and lets this refutation
//! finish.
//!
//! Corpus-backed, following the workspace convention (skip when absent, fail
//! under `AY_REQUIRE_CORPUS=1` so a vacuous run cannot pass as a pass).

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

use crate::common;

const STRING_SEARCH_35_14: &str = "benchmarks/smtlib-all/AUFDTLIRA/\
non-incremental__AUFDTLIRA__20200306-Kanig__spark2014bench__string_search__\
string_search.ads_35_14_postcondition___00.smt2";

/// Verdict line plus the two budget counters the fix exports.
struct Run {
    verdict: String,
    budget_hits: u64,
    legacy_rule_hits: u64,
}

fn solve_with_counters(smt: &str, timeout: Duration) -> Run {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(timeout));
    // The campaign posture (`--z3-mode`, and equally `--no-proof`): the
    // internal proof cycle is shed. It is not a convenience here, it is the
    // only posture in which this file's verdict is observable at all.
    // MEASURED 2026-09-12 on build 9609 AND on build 9605, so it is
    // not this change. (9605 is `198f6f0332`, the A/B base binary; this
    // branch's own base commit is `15a25227b8` = build 9607, and the two
    // differ only under `reports/` -- no `crates/` or `scripts/` path -- so
    // 9605 is a valid stand-in for the branch base and is what every A/B in
    // the report was run against.) With the proof cycle ON, `string_search.ads_35_14`
    // publishes `unknown (incomplete quantifier-unhandled)` on BOTH binaries,
    // in BOTH the gated and the lane-forced arm, even though the ground
    // refutation is reached (153 round trips against the gated 37). Shedding
    // it, the same file refutes in 0.62 s gated and 23.4 s with the lane on.
    // That withholding is a separate defect in the certificate path (a
    // ground-core re-solve exits `ExtensionUnknown` silently); asserting
    // around it here would make this guard about that defect instead of about
    // the budget.
    exec.set_competition_mode(true);
    // Same backstop the shared timeout helper installs: a runaway fails this
    // test instead of the machine.
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
        budget_hits: stats
            .get_int("split_loop.unproductive_budget_hits")
            .unwrap_or(0),
        legacy_rule_hits: stats
            .get_int("split_loop.unproductive_legacy_rule_hits")
            .unwrap_or(0),
    }
}

#[test]
fn guarded_enumerative_lane_does_not_trip_the_unproductive_budget_on_a_large_vocabulary() {
    let path = common::workspace_path(STRING_SEARCH_35_14);
    let Ok(smt) = std::fs::read_to_string(&path) else {
        assert!(
            std::env::var_os("AY_REQUIRE_CORPUS").is_none(),
            "AY_REQUIRE_CORPUS=1 is set and {STRING_SEARCH_35_14} is not on disk — \
             this guard checked NOTHING. Fetch with `ay-z3-parity fetch \
             benchmarks/smtlib-all --divisions AUFDTLIRA`."
        );
        eprintln!("SKIP: {STRING_SEARCH_35_14} is not present.");
        return;
    };
    // The ground truth this test asserts against is the file's own declaration
    // (z3 5.1.0 agrees, measured 2026-09-12).
    assert!(
        smt.contains("(set-info :status unsat)"),
        "corpus file no longer declares `:status unsat` — re-derive the ground \
         truth before trusting this guard"
    );

    // Control: the lane-off solve refutes.
    let off = solve_with_counters(&smt, Duration::from_secs(120));
    assert_eq!(
        off.verdict, "unsat",
        "control: string_search.ads_35_14 must refute with the enumerative lane off"
    );
    assert_eq!(
        off.budget_hits, 0,
        "control: the scaled budget must not fire on the lane-off refutation"
    );

    // The lane forced on. Before the scaling, this published `unknown` because
    // the lazy AUFLIRA split loop stopped at 128 consecutive zero-conflict
    // theory-conflict rounds (`[split-exit] AUFLIRA-lazy unproductive-budget`),
    // once per DT-lane deepening round. The legacy counter records that the
    // unscaled rule would still stop it, which is what makes the verdict
    // assertion below a test of the scaling and not of an unrelated change.
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        quantifier_guarded_enumerative: true,
        ..Default::default()
    });
    let on = solve_with_counters(&smt, Duration::from_secs(180));
    drop(guard);
    assert!(
        on.legacy_rule_hits >= 1,
        "the lane-on refutation no longer reaches the unscaled rule's threshold \
         (legacy_rule_hits={}); the fixture has stopped exercising the budget and \
         this guard needs a new one",
        on.legacy_rule_hits
    );
    assert_eq!(
        on.budget_hits, 0,
        "the vocabulary-scaled budget fired on a converging refutation over \
         ~7,600 atoms"
    );
    assert_eq!(
        on.verdict, "unsat",
        "string_search.ads_35_14 with the enumerative lane forced on must still \
         refute (budget_hits={}, legacy_rule_hits={})",
        on.budget_hits, on.legacy_rule_hits
    );
}
