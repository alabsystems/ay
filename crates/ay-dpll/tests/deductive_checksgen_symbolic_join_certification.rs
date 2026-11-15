// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #chained-entry-seal / #identity-drop-bridge — the symbolic two-`next` join
//! that was DECIDED and then WITHHELD.
//!
//! THE DEFECT, in two halves, both on the same obligation.
//!
//! deductive-checksgen's `escaped_local_seam_realmir ::
//! a5_the_symbolic_two_next_join_proves_under_the_guard` asks the in-process
//! `ay` lane for the `SliceBoundsCheck` row of `a5_two_next_if_ok_sym`. `ay`
//! computed UNSAT and then withdrew it:
//!
//! ```text
//! computed UNSAT rejected by mandatory strict certification: strict UNSAT
//!   proof validation failed: step t0 uses unverified trust rule
//! ```
//!
//! which trust reports as `Unknown { reason: "in-process ay returned unknown:
//! (incomplete self-check-rejected)" }`. Underneath, the whole assertion was
//! ONE unauthenticated original clause — `--probe-cert-reject` named it
//! `original clause 44 has no exact proof authority` — because the two lanes
//! that should have carried it to the authored term both declined:
//!
//! 1. **The seal.** `VariableSubstitution` minted the `before -> after`
//!    record for the `(or …)` conjunct, but `CheckedPropagationDerivation::seal`
//!    replayed it through `PropagateValues::rewrite_seeded`, which returns a
//!    map hit VERBATIM. The producer's `substitute_term` applies its map to
//!    FIXPOINT, so the recorded CHAIN (`n |-> a__slice_len` and
//!    `_5 |-> (< n m)`) reconstructed `(= (< n m) (< a__slice_len m))` where
//!    the pass had written `true`. Seal refused, record dropped, planner
//!    never saw the pair.
//!
//! 2. **The bridge.** With the record sealed, `plan_record_bridge` still
//!    could not reach the recorded `after`: the pass rebuilds through
//!    `mk_and`, which DROPS the two conjuncts that folded to `true`, while
//!    the reorder bridge admitted only argument-set EQUALITY and so declined
//!    the identity drop (its own module doc called that out as out of scope).
//!    The chain reached `(and true true …)` against a recorded 11-ary `and`.
//!
//! WHAT IS PINNED HERE. The captured query certifies `unsat` under the
//! consumer's posture — never the DECIDED-then-WITHHELD class — and the
//! SATISFIABLE mutant twin on the same recorded-rewrite shape still answers
//! `sat`. Neither lane can mint authority (records are hints; every emitted
//! step is re-derived by the untouched strict checker), and the twin is the
//! measurement that says so rather than the argument.
//!
//! POSTURE. The fixture is the byte-exact `problem_smt2` transcript of the
//! `AYProgram` trust's `in_process_ay_backend` executes for that obligation,
//! with the option block that lane asks for through the API. It is a ground
//! QF_LIA query that solves in milliseconds; a `Timeout` here would be a cost
//! regression, not this class.

use std::path::PathBuf;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `UnknownReason` spellings that mean ay DECIDED and then WITHHELD.
const DECIDED_THEN_WITHHELD: &[&str] = &["SelfCheckRejected", "ProofTrusted", "InternalError"];

fn fixture(name: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/deductive_checksgen_symbolic_join")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn solve(name: &str) -> (String, Option<String>) {
    let script = format!("(set-option :timeout 60000)\n{}", fixture(name));
    let commands = parse(&script).unwrap_or_else(|e| panic!("parse {name}: {e}"));
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("execute {name}: {e}"));
    let verdict = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| "<no verdict>".into());
    let reason = executor.unknown_reason().map(|r| format!("{r:?}"));
    (verdict, reason)
}

/// The obligation certifies: the chained-entry seal hands the record over and
/// the identity-drop bridge reaches the recorded `after`, so the mandatory
/// certification funnel publishes `unsat` instead of withdrawing it.
#[test]
#[timeout(120_000)]
fn the_symbolic_two_next_join_certifies_as_unsat() {
    let (verdict, reason) = solve("a5_two_next_if_ok_sym.smt2");
    let withheld = verdict == "unknown"
        && reason
            .as_deref()
            .is_some_and(|r| DECIDED_THEN_WITHHELD.iter().any(|w| r.contains(w)));
    assert!(
        !withheld,
        "a5_two_next_if_ok_sym was DECIDED and then WITHHELD ({reason:?}): the recorded \
         `VariableSubstitution` rewrite lost its proof authority again — see \
         `CheckedPropagationDerivation::close_seeded_substitution` and the identity-drop \
         half of `plan_connective_reorder_fold`"
    );
    assert_eq!(
        verdict, "unsat",
        "a5_two_next_if_ok_sym must certify as unsat; got {verdict} ({reason:?})"
    );
}

/// THE MUTANT TWIN. The same shape with the bounds guard flipped so the
/// violation is reachable. Neither new lane may turn a satisfiable query into
/// a refutation: an `unsat` here would mean the identity-drop bridge or the
/// closed seal map licensed a rewrite the producer never performed.
#[test]
#[timeout(120_000)]
fn the_satisfiable_mutant_twin_is_never_refuted() {
    let (verdict, reason) = solve("a5_two_next_if_ok_sym_sat_mutant.smt2");
    assert_ne!(
        verdict, "unsat",
        "the satisfiable mutant twin was REFUTED ({reason:?}): a certification lane minted \
         authority instead of replaying it"
    );
    assert_eq!(
        verdict, "sat",
        "the satisfiable mutant twin must be decided sat; got {verdict} ({reason:?})"
    );
}
