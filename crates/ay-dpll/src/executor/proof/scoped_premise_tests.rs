// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The strict checker's premise scope is the LIVE assertion stack of the
//! query being certified (VC-context design step 5, D-VC-4).
//!
//! A push/pop session carries solver state from one check to the next. What
//! it may never carry is proof AUTHORITY: a refutation minted while a scope
//! was open assumes that scope's assertions, and once the scope is popped the
//! same document must be refused by the next query's strict check. The
//! adversarial control below replays exactly that document; the positive
//! halves pin that outer-scope assertions stay authorized.

use ay_frontend::parse;

use super::*;

fn run(executor: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).expect("script parses");
    executor
        .execute_all(&commands)
        .expect("script executes")
        .into_iter()
        .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .collect()
}

const HEADER: &str = "(set-option :produce-proofs true)
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
";

/// A refutation that needs a popped assertion is REJECTED by a later query's
/// strict check, while that query's own refutation is accepted.
#[test]
fn a_proof_needing_a_popped_assertion_is_rejected_by_a_later_query() {
    let mut executor = Executor::new();
    let first = run(
        &mut executor,
        &format!("{HEADER}(push 1)\n(assert p)\n(assert (not p))\n(check-sat)\n"),
    );
    assert_eq!(first, vec!["unsat"]);
    let popped = executor
        .last_proof
        .clone()
        .expect("the first refutation retains its proof");
    assert!(
        executor
            .check_proof_strict_with_datatypes(&popped)
            .is_ok_and(|quality| quality.is_complete()),
        "the refutation is strictly valid in the scope it was minted in"
    );

    let second = run(
        &mut executor,
        "(pop 1)\n(push 1)\n(assert q)\n(assert (not q))\n(check-sat)\n",
    );
    assert_eq!(second, vec!["unsat"]);
    let refused = executor
        .check_proof_strict_with_datatypes(&popped)
        .expect_err("a popped assertion is outside the live premise scope");
    assert!(
        refused
            .to_string()
            .contains("outside the supplied problem obligation"),
        "refused for the premise, not for anything else: {refused}"
    );
    let live = executor
        .last_proof
        .clone()
        .expect("the second refutation retains its proof");
    assert!(executor
        .check_proof_strict_with_datatypes(&live)
        .is_ok_and(|quality| quality.is_complete()));
}

/// An assertion made two scopes out is a live premise of an inner check.
#[test]
fn an_outer_scope_assertion_is_a_live_premise_of_an_inner_check() {
    let mut executor = Executor::new();
    let verdicts = run(
        &mut executor,
        &format!(
            "{HEADER}(push 1)\n(assert (=> p q))\n(push 1)\n(assert p)\n(push 1)\n\
             (assert (not q))\n(check-sat)\n"
        ),
    );
    assert_eq!(verdicts, vec!["unsat"]);
    let proof = executor.last_proof.clone().expect("proof retained");
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
}

/// Popping BELOW a premise's scope revokes it even when the later query is
/// refuted by the assertions that remain: the old document is refused, the
/// new one is not.
#[test]
fn popping_below_a_premise_scope_revokes_it() {
    let mut executor = Executor::new();
    let first = run(
        &mut executor,
        &format!(
            "{HEADER}(push 1)\n(assert (=> p r))\n(push 1)\n(assert p)\n(assert (not r))\n\
             (check-sat)\n"
        ),
    );
    assert_eq!(first, vec!["unsat"]);
    let inner = executor.last_proof.clone().expect("proof retained");

    let second = run(
        &mut executor,
        "(pop 1)\n(push 1)\n(assert (not r))\n(assert r)\n(check-sat)\n",
    );
    assert_eq!(second, vec!["unsat"]);
    assert!(
        executor.check_proof_strict_with_datatypes(&inner).is_err(),
        "the popped `p` may not stand as a premise of the later query"
    );
}

/// The unrewritten authored replay is bounded by what bounds the query — its
/// deadline and the deterministic effort allowances the probe inherits —
/// never by the consequence-replay WALL envelope: deductive-checksgen's coroutine
/// row certifies through the replay (with the replay off it is withheld)
/// without claiming a single envelope grant. The envelope's fixed total,
/// floor and deadline share used to decide this row's verdict by the clock.
#[test]
fn the_unrewritten_replay_certifies_without_claiming_the_wall_envelope() {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/deductive_checksgen_reach_encoding")
        .join("coroutine_resume_saturated_unreachable.smt2");
    let row = std::fs::read_to_string(&path).expect("read the coroutine row fixture");

    let mut flags = ay_core::misc_cli_flags().clone();
    flags.no_consequence_replay = true;
    let replay_off = ay_core::misc_test_override::set(flags);
    let mut withheld = Executor::new();
    assert_eq!(
        run(&mut withheld, &row),
        vec!["unknown"],
        "without the replay the row's refutation is withheld"
    );
    drop(replay_off);

    let mut executor = Executor::new();
    assert_eq!(run(&mut executor, &row), vec!["unsat"]);
    assert_eq!(
        executor.consequence_replay_probe_claims(),
        0,
        "the replay must not draw on the wall-clock probe envelope"
    );
}
