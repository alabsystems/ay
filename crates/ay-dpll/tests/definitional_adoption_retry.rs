// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The check-sat-time definitional-forall pass (#defmacro-named-preuse) must
//! never turn a query the raw stack decides into `unknown`.
//!
//! Measured on a random definitional-forall family under `:produce-proofs
//! true` (800 scripts) against the pre-pass solver: thirteen scripts that
//! were `unsat` came back `unknown` after the pass, for two reasons the
//! module docs of `ay_frontend`'s `definitional_check_sat` describe — the
//! certification funnel refusing the refutation of the EXPANDED problem
//! where it accepted the instantiation refutation of the raw one (`step t0
//! uses unsupported hole rule`, `assumes term t1 outside the supplied
//! problem obligation`, a `Generic` theory lemma in strict mode), and a head
//! with two candidate definitions whose first adoption left the quantifier
//! engines a problem they could not refute. Each fixture below is one of
//! those scripts verbatim (z3: `unsat` on all of them); the pass now either
//! declines the contested head or leaves the executor a raw stack to solve
//! again when the expanded one decides `unknown`.

use std::time::{Duration, Instant};

use ay_dpll::Executor;
use ay_frontend::{parse, Command, CHECK_SAT_ADOPTION_MAX_RETAINED_NODES};
use ntest::timeout;

const WALL: Duration = Duration::from_mins(1);

/// Run a fixture through the command route with a wall, dropping any
/// trailing `(get-model)` (the fuzz scripts end with one that errors on an
/// `unsat` verdict, exactly as z3's does).
fn run(script: &str, configure: impl FnOnce(&mut Executor)) -> (Executor, Vec<String>) {
    let commands: Vec<Command> = parse(script)
        .expect("fixture parses")
        .into_iter()
        .filter(|command| !matches!(command, Command::GetModel))
        .collect();
    let mut executor = Executor::new();
    executor.set_timeout(Some(WALL));
    configure(&mut executor);
    let started = Instant::now();
    let outputs = executor.execute_all(&commands).expect("script executes");
    let elapsed = started.elapsed();
    assert!(
        elapsed < WALL,
        "verdict must arrive inside the wall, took {elapsed:?}"
    );
    (executor, outputs)
}

fn assert_unsat(name: &str, outputs: &[String], executor: &Executor) {
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{name}: expected unsat (reason {:?}), got {outputs:?}",
        executor.unknown_reason()
    );
}

/// `dm_1_0018`: two definitions asserted AFTER uses of their heads; the
/// expanded problem's refutation is a single `hole` the strict checker
/// refuses, so the raw stack (refuted by instantiation in milliseconds) is
/// solved again.
#[test]
#[timeout(300_000)]
fn a_post_use_definition_whose_expansion_cannot_be_certified_still_decides_unsat() {
    let (executor, outputs) = run(
        include_str!("fixtures/defmacro_postuse_hole_certification.smt2"),
        |_| {},
    );
    assert_unsat("hole", &outputs, &executor);
}

/// `dm_1_0079`: the same shape where the strict checker refuses a `Generic`
/// theory lemma of the expanded refutation.
#[test]
#[timeout(300_000)]
fn a_post_use_definition_whose_expanded_lemma_is_refused_still_decides_unsat() {
    let (executor, outputs) = run(
        include_str!("fixtures/defmacro_postuse_generic_lemma_certification.smt2"),
        |_| {},
    );
    assert_unsat("generic-lemma", &outputs, &executor);
}

/// `p3_core`: a `:named` post-use definition under `:produce-unsat-cores`
/// and `:produce-proofs`; the expanded refutation's assumption step falls
/// outside the supplied problem obligation, and the raw retry reports the
/// authored core.
#[test]
#[timeout(300_000)]
fn a_named_post_use_definition_under_cores_and_proofs_decides_unsat_with_its_core() {
    let (executor, outputs) = run(
        include_str!("fixtures/defmacro_postuse_named_core_proofs.smt2"),
        |_| {},
    );
    assert_unsat("named-core", &outputs, &executor);
    let core = &outputs[1];
    assert!(
        core.contains('u') && core.contains('d'),
        "the core must name the use and the definition: {core}"
    );
}

/// `dm_2_0158`: `g` has two `:named` candidate definitions after a use —
/// a contested head the pass must not adopt; the remaining adoption (`f`)
/// is retried raw when the expanded problem is undecided.
#[test]
#[timeout(300_000)]
fn a_contested_head_asserted_after_its_use_decides_unsat() {
    let (executor, outputs) = run(
        include_str!("fixtures/defmacro_contested_head_postuse_named.smt2"),
        |_| {},
    );
    assert_unsat("contested-post-use", &outputs, &executor);
    assert!(!outputs[1].is_empty(), "a core is reported: {outputs:?}");
}

/// The same three definitions asserted FIRST: the assert-time finder adopts
/// `g`'s first definition (it cannot see the second) and the raw solver
/// had refuted the stack in milliseconds; the check-sat pass rolls the
/// contested adoption back before solving.
#[test]
#[timeout(300_000)]
fn a_contested_head_adopted_at_assert_time_is_rolled_back_and_decides_unsat() {
    let (executor, outputs) = run(
        include_str!("fixtures/defmacro_contested_head_definitions_first_named.smt2"),
        |_| {},
    );
    assert_unsat("contested-definitions-first", &outputs, &executor);
}

/// The CLI's no-proof posture (proof-surface retention OFF, the pass's own
/// parsed copy budgeted at its node limit) reaches the pass on deductive-checks's
/// captured `proof_in_spec` query — a post-use `:named` definition whose
/// expansion is ground LIA — and decides `sat` with the adopted definition
/// in the model, exactly as a library embedder with retention does.
#[test]
#[timeout(300_000)]
fn the_pass_own_parsed_copy_reaches_it_on_the_cli_posture() {
    let (mut executor, outputs) = run(
        include_str!("fixtures/deductive_checks_proof_in_spec_preuse_named_core.smt2"),
        |executor| {
            executor.set_retain_parsed_assertions(false);
            executor.set_definitional_pass_parsed_budget(CHECK_SAT_ADOPTION_MAX_RETAINED_NODES);
        },
    );
    assert_eq!(outputs, vec!["sat"], "z3 agrees: sat");
    let model = executor
        .execute(&Command::GetModel)
        .expect("get-model executes")
        .expect("get-model prints");
    assert!(
        model.contains("(define-fun proof_in_spec_successor"),
        "the model must carry the adopted definition:\n{model}"
    );
}

/// `dm_1_0290`: `f` has two CONSISTENT post-use definitions (`f(x) = c`,
/// `f(x) = -5`) and the assert-time finder adopted the first; the contested
/// rollback leaves a raw quantifier pair the engines do not decide, so the
/// fallback chain's last stack — the assert-time one, which the solver
/// decided before this pass existed — must still be solved.
#[test]
#[timeout(300_000)]
fn a_contested_head_whose_assert_time_adoption_decided_the_query_still_decides_it() {
    let (executor, outputs) = run(
        include_str!("fixtures/defmacro_contested_consistent_assert_time.smt2"),
        |_| {},
    );
    assert_unsat("contested-consistent", &outputs, &executor);
}

/// `dm_2_0222`: a `:named` definition asserted FIRST (adopted by the
/// assert-time finder, which the pre-fix solver refused for the `:named`
/// wrapper) beside a later two-binder quantified fact over the same head;
/// the expanded stack is undecided and the raw stack — the pre-fix
/// solver's — refutes it in milliseconds.
#[test]
#[timeout(300_000)]
fn a_named_definition_asserted_first_falls_back_to_the_raw_stack() {
    let (executor, outputs) = run(
        include_str!("fixtures/defmacro_named_definition_first_raw_refutation.smt2"),
        |_| {},
    );
    assert_unsat("named-definition-first", &outputs, &executor);
}
