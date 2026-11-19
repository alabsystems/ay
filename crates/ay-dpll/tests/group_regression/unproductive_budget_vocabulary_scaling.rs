// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #unproductive-budget-scales-with-vocabulary: the lazy split loop's
//! unproductive-round budget (#7956) must not stop a converging refutation
//! whose theory-atom vocabulary is large.
//!
//! The budget is `unproductive_round_limits(atoms)` =
//! `(max(128, atoms / 8), max(1024, atoms))`; the legacy counter
//! (`split_loop.unproductive_legacy_rule_hits`) counts split-loop invocations
//! the unscaled `(128, 1024)` rule would have stopped. This guard needs a
//! refutation that crosses the unscaled rule (`legacy_rule_hits >= 1`), stays
//! inside the scaled one (`budget_hits == 0`) and reaches `unsat`.
//!
//! Fixture: AUFDTLIRA `spark2014bench N624-020 perm_rem
//! perm.adb_31_51_range_check___00`, declared `:status unsat` (z3 5.3.3
//! agrees). Measured 2026-11-18 on build 16451 (`bef5b14a1`) through the CLI
//! (`--z3-mode --no-ground-first --debug-split-exit --stats-full`, release
//! build):
//!
//! * lane off: `unsat` in 0.19 s, `legacy_rule_hits 0`, `budget_hits 0`;
//! * `--quantifier-guarded-enumerative` on: one lazy AUFLIRA invocation over
//!   5,489 theory atoms whose longest zero-conflict run is 235 rounds and whose
//!   cumulative count is 510, refuting at round 514 — `unsat` in 11.7-15.1 s,
//!   `legacy_rule_hits 1`, `budget_hits 0`. The unscaled consecutive bound
//!   (128) would stop it; the scaled one (5,489 / 8 = 686) does not.
//!
//! What changed. The guard's first fixture, AUFDTLIRA `string_search.ads_35_14`
//! (2026-09-12: a 357-round run over 7,618 atoms), stopped crossing the
//! unscaled rule. Measured on main's history with the lane on and ground-first
//! off, in two steps. Between builds 13347 and 13505 `legacy_rule_hits` went
//! 2 -> 1 and `split_loop.carried_conflicts 236` appeared: the ground-solve
//! carry (`9690cc622`, landed by `c34968a4d` at build 13452; the only commit
//! in that range that introduces those counters) replays the first re-solve's theory
//! conflicts into the second, which then needs no long run. Then `f4d1b5de9`
//! (fix/stalls-2, build 13567: `solve_auflira` rewrites its window over the
//! representatives of its root congruence classes when no proof is
//! published) shrinks the remaining invocation from 7,220 atoms and a
//! 219-round run to 2,229 atoms and a 29-round run (`legacy_rule_hits` 1 ->
//! 0; `unsat` in 0.39 s against 6.56 s on its parent `24dadd896`). The
//! verdict stayed `unsat` throughout and z3 agrees, so that file no longer
//! exercises this budget because the refutation got shorter, not because a
//! path was lost.
//!
//! Ground-first is switched off in both arms. Its probe decides the query
//! without its axioms on a disposable executor under a 1 s wall cap and
//! exports none of its split-loop counters. On the old fixture it refuted
//! inside the cap on build 13505 and ran out of it on build 13181, and when it
//! refutes, its verdict is published and the pipeline whose counters this
//! guard reads does not run; the outcome depends on the wall clock. With it off, the counters below are the
//! quantifier pipeline's own.
//!
//! Corpus-backed, following the workspace convention (skip when absent, fail
//! under `AY_REQUIRE_CORPUS=1` so a vacuous run cannot pass as a pass).

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

use crate::common;

const PERM_31_51: &str = "benchmarks/smtlib-all/AUFDTLIRA/\
non-incremental__AUFDTLIRA__20200306-Kanig__spark2014bench__N624-020__\
perm_rem__perm.adb_31_51_range_check___00.smt2";

/// Verdict line plus the two budget counters the fix exports.
struct Run {
    verdict: String,
    budget_hits: u64,
    legacy_rule_hits: u64,
}

/// Solve `smt` in the campaign posture with ground-first off and the
/// guarded-enumerative lane set to `lane`.
fn solve_with_counters(smt: &str, lane: bool, timeout: Duration) -> Run {
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        quantifier_guarded_enumerative: lane,
        no_ground_first: true,
        ..Default::default()
    });
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(timeout));
    // The campaign posture (`--z3-mode`, and equally `--no-proof`): the
    // internal proof cycle is shed. The budget's legacy and scaled counters
    // were measured in this posture, and `solve_auflira`'s root-class window
    // (the change that retired the previous fixture) is gated on it.
    exec.set_competition_mode(true);
    // Same backstop the shared timeout helper installs: a runaway fails this
    // test instead of the machine.
    exec.set_memory_limit(Some(8 << 30));
    let lines = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    drop(guard);
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
    let path = common::workspace_path(PERM_31_51);
    let Ok(smt) = std::fs::read_to_string(&path) else {
        assert!(
            std::env::var_os("AY_REQUIRE_CORPUS").is_none(),
            "AY_REQUIRE_CORPUS=1 is set and {PERM_31_51} is not on disk — \
             this guard checked NOTHING. Fetch with `ay-z3-parity fetch \
             benchmarks/smtlib-all --divisions AUFDTLIRA`."
        );
        eprintln!("SKIP: {PERM_31_51} is not present.");
        return;
    };
    // The ground truth this test asserts against is the file's own declaration
    // (z3 5.3.3 agrees, measured 2026-11-18).
    assert!(
        smt.contains("(set-info :status unsat)"),
        "corpus file no longer declares `:status unsat` — re-derive the ground \
         truth before trusting this guard"
    );

    // Control: the lane-off solve refutes.
    let off = solve_with_counters(&smt, false, Duration::from_secs(120));
    assert_eq!(
        off.verdict, "unsat",
        "control: perm.adb_31_51 must refute with the enumerative lane off"
    );
    assert_eq!(
        off.budget_hits, 0,
        "control: the scaled budget must not fire on the lane-off refutation"
    );

    // The lane forced on. The legacy counter records that the unscaled rule
    // would stop this refutation (measured: a 235-round zero-conflict run),
    // which is what makes the verdict assertion below a test of the scaling
    // and not of an unrelated change.
    let on = solve_with_counters(&smt, true, Duration::from_secs(180));
    eprintln!(
        "perm.adb_31_51 lane on: verdict={} legacy_rule_hits={} budget_hits={}",
        on.verdict, on.legacy_rule_hits, on.budget_hits
    );
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
         ~5,500 atoms"
    );
    assert_eq!(
        on.verdict, "unsat",
        "perm.adb_31_51 with the enumerative lane forced on must still refute \
         (budget_hits={}, legacy_rule_hits={})",
        on.budget_hits, on.legacy_rule_hits
    );
}
