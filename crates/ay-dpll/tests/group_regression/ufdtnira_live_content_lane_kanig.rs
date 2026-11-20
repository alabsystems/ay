// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #ufdtnira-live-content-lane on the corpus: the SPARK/Why3 `UFDTNIRA`
//! acceptance files of the 2026-09-16 gap census (road rank 4, lane-less L1).
//!
//! Each file declares `UFDTNIRA`, so `LogicCategory::from_logic` answers
//! `Ufdtnira` — the category whose two dispatch tables used to return a bare
//! `unknown` without ever running a theory solver. Their live windows are
//! Real-free and array-free (the Why3 prelude's `real__ref : Real` is declared
//! and never asserted), so they are exactly the windows the lane now hands to
//! `solve_dt_uf_nia`. z3 5.1.0 refutes all five in under 0.05 s.
//!
//! What this guard pins, and why it is shaped this way:
//!
//! * that these corpus files really do reach the CHANGED arm — the recorded
//!   `solver.logic_category` is `Ufdtnira`, not a narrowed category. Without
//!   this the rest of the guard could pass while exercising nothing.
//! * that the lane never answers `sat` on them. That is the direction a wrong
//!   lane fails in: `solve_uf_nia` has no array theory, so a read-over-write
//!   relaxed to congruence would satisfy an unsatisfiable window.
//!
//! It deliberately does NOT pin `unsat`. Measured 2026-09-17 (base
//! `3e57b1f4b2`): through the CLI, two of these files (`why_6f5421`,
//! `why_8bb8b3`) refute on the lane in 0.8–2.0 s whenever proofs are shed
//! (`--z3-mode`, `--no-proof`), and six more `:status unknown` siblings of the
//! same R509-011 family do too. Through this crate's `Executor` API they all
//! stay `unknown`, and setting the CLI's shed posture on the executor
//! (`set_strict_logic_compliance(false)`, `set_produce_proofs(false)`,
//! `set_retain_parsed_assertions(false)` with the definitional budget, a 20 s
//! `set_timeout`, a 64 MB stack) did not reproduce it. Pinning `unsat` here
//! would pin an outcome this entry point does not deliver; the CLI-level
//! numbers live in
//! the development design notes at `9598c4206`,
//! which also records the unexplained divergence as open.
//!
//! Corpus-backed, following the workspace convention (skip when absent, fail
//! under `AY_REQUIRE_CORPUS=1` so a vacuous run cannot pass as a pass).

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;

use crate::common;

const DIR: &str = "benchmarks/smtlib-all/UFDTNIRA";
const STEM: &str =
    "non-incremental__UFDTNIRA__20200306-Kanig__spark2014bench__R509-011__higher_order_proof__why_";
const TAIL: &str = "_sparkmnhigher_ordermnfold-T-defqtvc__00.smt2";

/// The five `:status unsat` acceptance files of the census gap set. z3 refutes
/// every one of them; two of them refute on the lane through the CLI.
const ACCEPTANCE: &[&str] = &["2926ab", "2cf381", "6f5421", "8bb8b3", "93a57d"];

/// Solve one acceptance file on a bounded budget, returning `(verdict,
/// logic category)`.
fn solve(smt: &str) -> (String, Option<String>) {
    let commands = parse(smt).expect("corpus file must parse");
    let mut exec = Executor::new();
    // The CLI turns SMT-LIB's execution-mode preconditions off for every
    // invocation; keep the guard on the same footing. The budget keeps an
    // undecided file from holding the suite open — the lane replaces an
    // instant refusal with a real solve, so these files now use their time.
    exec.context_mut().set_strict_logic_compliance(false);
    exec.set_timeout(Some(Duration::from_secs(5)));
    let outputs = exec.execute_all(&commands).expect("corpus file must run");
    // The corpus file ends in `(exit)`, so the verdict is the last VERDICT
    // line, not the last line.
    let verdict = outputs
        .iter()
        .rev()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_default();
    let category = exec
        .statistics()
        .get_string("solver.logic_category")
        .map(str::to_owned);
    (verdict, category)
}

/// Read one acceptance file, checking the two `set-info` facts the guard rests
/// on. `None` means "not on disk", a pass only without `AY_REQUIRE_CORPUS`.
fn acceptance_file(hash: &str) -> Option<String> {
    let rel = format!("{DIR}/{STEM}{hash}{TAIL}");
    let path = common::workspace_path(&rel);
    let Ok(smt) = std::fs::read_to_string(&path) else {
        assert!(
            std::env::var_os("AY_REQUIRE_CORPUS").is_none(),
            "AY_REQUIRE_CORPUS=1 is set and {rel} is not on disk — this guard checked \
             NOTHING for it. Fetch with `ay-z3-parity fetch benchmarks/smtlib-all \
             --divisions UFDTNIRA`."
        );
        eprintln!("SKIP: {rel} is not present.");
        return None;
    };
    assert!(
        smt.contains("(set-logic UFDTNIRA)"),
        "{rel} no longer declares UFDTNIRA — the guard exercises the declared-NIRA \
         category and must be re-derived"
    );
    assert!(
        smt.contains("(set-info :status unsat)"),
        "{rel} no longer declares `:status unsat` — re-derive the ground truth before \
         trusting this guard"
    );
    Some(smt)
}

#[test]
fn kanig_ufdtnira_acceptance_files_reach_the_changed_arm_and_are_never_satisfied() {
    for hash in ACCEPTANCE {
        let Some(smt) = acceptance_file(hash) else {
            continue;
        };
        let (verdict, category) = solve(&smt);
        assert_eq!(
            category.as_deref(),
            Some("Ufdtnira"),
            "why_{hash} no longer routes through `Ufdtnira`, so this guard would check \
             nothing about the live-content lane"
        );
        assert_ne!(
            verdict, "sat",
            "why_{hash} is `:status unsat` and z3 refutes it; a `sat` here would mean \
             the lane relaxed a theory the live window actually uses"
        );
    }
}
