// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression: incremental QF_LRA (`#lra-inc-engine`) published a false
//! `unsat` after a run of push/pop scopes (found 2026-09-18 by the CHC
//! query-replay microbenchmark; `repros/lra-pushpop-false-unsat-2026-09-18/`,
//! the development design notes).
//!
//! Root cause: the split loop seeded its fresh SAT-variable cursor as
//! `user_num_vars() + scope_depth()`, which counts only LIVE scope selectors.
//! On the session-persistent solver every `pop()` leaves a DEAD selector
//! (forced TRUE at level 0 by the `[+selector]` unit) above `user_num_vars`,
//! so once enough scopes had been popped the disequality split
//! `(not (= O1 P1))` -> `O1<P1 \/ O1>P1` minted its two atoms onto two dead
//! selectors — TRUE and TRUE — and the LRA theory "refuted" the scope. The
//! cursor is now floored at `total_num_vars()` at every minting site
//! (`split_incremental::fresh_sat_var_floor`).
//!
//! These tests pin the exact verdict sequence z3 gives, in BOTH the
//! proof-shedding posture the CLI selects for `--competition` / `--no-proof`
//! / `--rigor fast` (where the wrong `unsat` shipped) and the default
//! proof-carrying posture (where it was only masked as `unknown`).

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Execute through the CLI's authored boundary; `competition` selects the
/// proof-shedding posture (`Executor::set_competition_mode`).
fn verdicts(smt: &str, competition: bool) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(competition);
    let mut out = Vec::new();
    for command in &commands {
        if let Some(line) = exec
            .execute_authored(command)
            .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
        {
            let line = line.trim().to_owned();
            if matches!(line.as_str(), "sat" | "unsat" | "unknown") {
                out.push(line);
            }
        }
    }
    out
}

fn all_sat(n: usize) -> Vec<String> {
    vec!["sat".to_owned(); n]
}

/// 3 reals, 6 scopes: scope 1 forces a disequality split (allocating split
/// atoms), scopes 2-5 each push+pop a scope (leaving dead selectors), scope 6
/// repeats scope 1. Every scope is satisfiable; the buggy lane answered
/// `unsat` on scope 6.
const MIN_3VARS_6SCOPES: &str = r#"
(set-logic QF_LRA)
(declare-const S1 Real)
(declare-const O1 Real)
(declare-const P1 Real)
(push 1)
(assert (not (= O1 P1)))
(assert (<= 3 S1))
(check-sat)
(pop 1)
(push 1)
(assert (= S1 0))
(check-sat)
(pop 1)
(push 1)
(check-sat)
(pop 1)
(push 1)
(assert (= S1 0))
(check-sat)
(pop 1)
(push 1)
(assert (= S1 0))
(check-sat)
(pop 1)
(push 1)
(assert (not (= O1 P1)))
(assert (<= 3 S1))
(check-sat)
(pop 1)
"#;

/// Same, with the empty scope replaced by a fourth `S1 = 0` scope: the empty
/// scope is not essential, the number of popped scopes is.
const NO_EMPTY_SCOPE: &str = r#"
(set-logic QF_LRA)
(declare-const S1 Real)
(declare-const O1 Real)
(declare-const P1 Real)
(push 1)
(assert (not (= O1 P1)))
(assert (<= 3 S1))
(check-sat)
(pop 1)
(push 1)
(assert (= S1 0))
(check-sat)
(pop 1)
(push 1)
(assert (= S1 0))
(check-sat)
(pop 1)
(push 1)
(assert (= S1 0))
(check-sat)
(pop 1)
(push 1)
(assert (= S1 0))
(check-sat)
(pop 1)
(push 1)
(assert (not (= O1 P1)))
(assert (<= 3 S1))
(check-sat)
(pop 1)
"#;

#[test]
#[timeout(30_000)]
fn min_3vars_6scopes_all_sat_in_competition_posture() {
    assert_eq!(verdicts(MIN_3VARS_6SCOPES, true), all_sat(6));
}

#[test]
#[timeout(30_000)]
fn min_3vars_6scopes_all_sat_in_default_posture() {
    assert_eq!(verdicts(MIN_3VARS_6SCOPES, false), all_sat(6));
}

#[test]
#[timeout(30_000)]
fn no_empty_scope_variant_all_sat_in_competition_posture() {
    assert_eq!(verdicts(NO_EMPTY_SCOPE, true), all_sat(6));
}

#[test]
#[timeout(30_000)]
fn no_empty_scope_variant_all_sat_in_default_posture() {
    assert_eq!(verdicts(NO_EMPTY_SCOPE, false), all_sat(6));
}

/// Many popped scopes before the split: the cursor must clear ALL dead
/// selectors, not just two.
#[test]
#[timeout(60_000)]
fn many_popped_scopes_before_split_all_sat() {
    let mut smt = String::from(
        "(set-logic QF_LRA)\n(declare-const S1 Real)\n(declare-const O1 Real)\n(declare-const P1 Real)\n\
         (push 1)\n(assert (not (= O1 P1)))\n(assert (<= 3 S1))\n(check-sat)\n(pop 1)\n",
    );
    for _ in 0..40 {
        smt.push_str("(push 1)\n(assert (= S1 0))\n(check-sat)\n(pop 1)\n");
    }
    smt.push_str("(push 1)\n(assert (not (= O1 P1)))\n(assert (<= 3 S1))\n(check-sat)\n(pop 1)\n");
    assert_eq!(verdicts(&smt, true), all_sat(42));
    assert_eq!(verdicts(&smt, false), all_sat(42));
}

/// The original extract of the om1_with_relays PDR query stream (6 scopes):
/// z3 answers `sat sat unsat unsat unsat sat`; the buggy lane answered `unsat`
/// on scope 6 in the competition posture and `unknown` in the default one.
#[test]
#[timeout(60_000)]
fn om1_query_stream_extract_exact_verdicts() {
    let path = crate::common::workspace_path(
        "repros/lra-pushpop-false-unsat-2026-09-18/om1_pushpop_wrong_unsat_min_small.smt2",
    );
    let smt = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("repro {} must be present: {err}", path.display()));
    let expected: Vec<String> = ["sat", "sat", "unsat", "unsat", "unsat", "sat"]
        .iter()
        .map(|s| (*s).to_owned())
        .collect();
    assert_eq!(verdicts(&smt, true), expected, "competition posture");
    assert_eq!(verdicts(&smt, false), expected, "default posture");
}

/// Every kept shrunk variant in the repro directory answers exactly what z3
/// answers (all `sat`).
#[test]
#[timeout(60_000)]
fn shrunk_repro_variants_all_sat() {
    for (file, scopes) in [
        ("om1_pushpop_wrong_unsat_ddmin_6scopes.smt2", 6usize),
        ("pushpop_selector_alias_min_3vars_6scopes.smt2", 6),
        ("pushpop_selector_alias_no_empty_scope.smt2", 6),
        ("pushpop_selector_alias_7scopes.smt2", 7),
    ] {
        let path = crate::common::workspace_path(format!(
            "repros/lra-pushpop-false-unsat-2026-09-18/{file}"
        ));
        let smt = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("repro {} must be present: {err}", path.display()));
        assert_eq!(
            verdicts(&smt, true),
            all_sat(scopes),
            "{file} (competition posture)"
        );
        assert_eq!(
            verdicts(&smt, false),
            all_sat(scopes),
            "{file} (default posture)"
        );
    }
}
