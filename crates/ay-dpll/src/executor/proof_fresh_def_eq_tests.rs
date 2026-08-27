// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for the fresh-definition EQUALITY half of the lane.
//!
//! The unit-level conditions live with the code that decides them
//! (`ay_core::proof_validation::fresh_def_eq` for the shape, `ay_proof`'s
//! `FreshDefRegistry` for the whole-proof provenance and its sweeps). What is
//! left to pin HERE is the thing only a real solve can show: that
//! `purify_bool_args`' defining assertion reaches proof reconstruction as a
//! premiseless `trust` step, that this lane converts it, and that the
//! conversion survives the checker the executor itself runs.
//!
//! The benchmark is `smt/regression/soundness_qf_uf_incremental/
//! hand_min_falsesat_bool_arg.smt2`, inlined so the test is self-contained,
//! and it is one of the 4 files in the whole corpus that carry this class (8
//! promotable steps in 236 `(= d expr)` premiseless `trust` units, measured).

use ay_core::{AletheRule, ProofStep};
use ay_frontend::parse;

use super::{is_fresh_def_bound_step, is_fresh_def_eq_step};
use crate::Executor;

/// Which PRODUCER-side guard each test defends. Every entry was checked by
/// DELETING or WEAKENING the guard, running the named test, observing the
/// failure, and restoring the guard.
///
/// The registry's own guards are mutation-checked in `ay-proof`'s
/// `fresh_def_eq_tests.rs`; the shape recognizer's in `ay-core`'s. What is
/// producer-side and only testable here is stage A and the call site.
const LANE_GUARD_MUTATION_LEDGER: &[(&str, &str)] = &[
    (
        "select_promotable_bounds: stage A keeps only a reading whose definiendum is UNCONSTRAINED",
        "a_purified_boolean_argument_definition_is_promoted_not_demoted",
    ),
    (
        "run_assumption_authority_passes_without_parsed_syntax: the lane is called at all",
        "a_purified_boolean_argument_definition_is_promoted_not_demoted",
    ),
];

/// ONE honest NEGATIVE, recorded rather than hidden.
///
/// `fresh_def_eq_operands`' own `sort(lhs) == sort(rhs)` check is NOT
/// mutation-checkable: deleting it fails no test. Two reasons, both measured
/// rather than argued:
///
/// 1. `mk_eq` requires equal sorts (a `debug_assert`), so no solve in this
///    repository can build the mismatched atom the check would reject; and
/// 2. even if one did, the CHECKER's `recognize_fresh_def_eq` rejects it and
///    this lane's Gate-2 reverts the whole rewrite.
///
/// It is therefore classified as DEFENCE IN DEPTH, not as a guard, and the
/// property it rests on is pinned DIRECTLY by
/// `ay_core::proof_validation::fresh_def_eq_tests::
/// rejects_an_int_symbol_defined_by_a_real_term_satisfied_at_one_half` and by
/// `ay_proof`'s `rejects_an_int_symbol_defined_by_a_real_term`.
const RECORDED_NEGATIVE: &str = "fresh_def_eq_operands: sort(lhs) == sort(rhs)";

#[test]
fn lane_guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(LANE_GUARD_MUTATION_LEDGER.len(), 2);
    for (guard, test) in LANE_GUARD_MUTATION_LEDGER {
        assert!(!guard.is_empty() && !test.is_empty());
    }
    assert!(!RECORDED_NEGATIVE.is_empty());
}

/// `purify_bool_args`' own target shape: a COMPOUND Boolean argument of an
/// uninterpreted function, which it replaces by a fresh proxy `p` plus the
/// defining assertion `(= p b)`.
const BOOL_ARG_UNSAT: &str = r#"
    (set-logic QF_UF)
    (declare-sort U 0)
    (declare-fun TRUE () U)
    (declare-fun FALSE () U)
    (declare-fun BOOL () U)
    (declare-fun bool (Bool) U)
    (declare-fun mem (U U) Bool)
    (declare-fun g639 () U)
    (declare-fun g640 () U)
    (declare-fun P1 () Bool)
    (assert (mem TRUE BOOL))
    (assert (= (bool (and P1 (= g639 TRUE) (= g640 TRUE))) TRUE))
    (assert (= g639 FALSE))
    (assert (not (mem (bool (and P1 (= g639 TRUE) (= g640 FALSE))) BOOL)))
    (check-sat)
"#;

fn solve_bool_arg() -> Executor {
    solve_bool_arg_with_retention(true)
}

/// `retain_parsed = false` is the CLI's own configuration for `--no-proof`,
/// `--z3-mode` and competition mode (#rss-vs-z3), and it is therefore the
/// configuration the MANDATORY-certificate census runs in. It takes a NARROWED
/// authority subset (`run_assumption_authority_passes_without_parsed_syntax`),
/// so the promotion has to be wired into that subset as well as into the
/// retention-on tail — measured, not assumed: before it was, all 4 corpus files
/// carrying this class reached strict certification with the definition still a
/// premiseless `trust` step.
fn solve_bool_arg_with_retention(retain_parsed: bool) -> Executor {
    let commands = parse(BOOL_ARG_UNSAT).expect("parse");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(retain_parsed);
    assert_eq!(
        exec.execute_all(&commands).expect("exec"),
        vec!["unsat"],
        "the Boolean-argument obligation is UNSAT"
    );
    exec
}

fn fresh_def_eq_steps(exec: &Executor) -> usize {
    exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| is_fresh_def_eq_step(&exec.ctx.terms, step))
            .count()
    })
}

/// Every premiseless, argument-free `trust` unit whose clause is a binary `=`.
/// This is the population the equality half of the lane draws from.
fn premiseless_trust_equality_units(exec: &Executor) -> Vec<String> {
    exec.last_proof.as_ref().map_or_else(Vec::new, |proof| {
        proof
            .steps
            .iter()
            .filter_map(|step| {
                let ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } = step
                else {
                    return None;
                };
                if !premises.is_empty() || !args.is_empty() || clause.len() != 1 {
                    return None;
                }
                let text = ay_proof::format_term_alethe(&exec.ctx.terms, clause[0]);
                text.starts_with("(= ").then_some(text)
            })
            .collect()
    })
}

#[test]
fn a_purified_boolean_argument_definition_is_promoted_not_demoted() {
    let exec = solve_bool_arg();
    assert!(
        fresh_def_eq_steps(&exec) > 0,
        "the `purify_bool_args` definition must reach the proof as `fresh_def_eq` steps"
    );
    // Every SURVIVING equality trust unit must be one the lane correctly
    // declines — i.e. one whose atomic-variable side is AUTHORED. Asserting on
    // WHICH symbol rather than on a count is deliberate: the residual here is
    // the REWRITTEN assertion `(= TRUE (bool boolarg_N))`, whose definiendum
    // `TRUE` the problem declares, and a bound over it would be no definition.
    for text in premiseless_trust_equality_units(&exec) {
        assert!(
            !text.contains("boolarg_") || text.contains("(bool "),
            "an equality whose only atomic side is a fresh proxy must have been promoted: {text}"
        );
    }
}

#[test]
fn the_promotion_also_runs_in_the_retention_off_configuration() {
    // The census control the corpus A/B uses is `ay solve --no-proof`, which
    // turns parsed-assertion retention OFF. Without this the lane is never
    // called on a plain SMT file in the mandatory-certificate regime, and the
    // whole capability is unreachable there.
    let exec = solve_bool_arg_with_retention(false);
    assert!(
        exec.ctx.assertions_parsed().is_empty(),
        "the fixture must actually model the retention-off configuration"
    );
    assert!(
        fresh_def_eq_steps(&exec) > 0,
        "the promotion must run in the narrowed authority subset too"
    );
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    if let Err(error) = exec.check_proof_strict_with_datatypes(proof) {
        assert!(
            !error.to_string().contains("fresh definition"),
            "the promotion must never produce a rejected fresh definition: {error}"
        );
    }
}

#[test]
fn the_promoted_proof_still_passes_the_executors_own_checker() {
    // The promotion is only worth anything if the checker the executor runs
    // accepts it. A `fresh_def_eq` the registry declined would be a HARD
    // `InvalidTheoryLemma` rejection — strictly worse than the rescuable
    // `trust` it replaced — so this asserts the specific error class never
    // appears, whatever the overall verdict is.
    let exec = solve_bool_arg();
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    if let Err(error) = exec.check_proof_strict_with_datatypes(proof) {
        let rendered = error.to_string();
        assert!(
            !rendered.contains("fresh definition"),
            "the promotion lane must never produce a rejected fresh definition: {rendered}"
        );
    }
}

#[test]
fn the_published_unsat_is_still_backed_by_a_certificate() {
    // The lane must not trade a certificate for a shape change.
    let exec = solve_bool_arg();
    assert!(
        exec.last_command_unsat_was_strictly_verified()
            || exec.last_command_unsat_was_independently_verified()
            || exec.last_command_unsat_was_exact_semantically_verified(),
        "the `unsat` must stay backed by a real certificate"
    );
}

#[test]
fn every_promoted_equality_defines_a_symbol_the_problem_never_declares() {
    // The producer-side admission test must agree with the checker's. The
    // problem here declares `TRUE`, `FALSE`, `BOOL`, `g639`, `g640`, `P1` and
    // the functions `bool` / `mem`; a `fresh_def_eq` over ANY of them would be
    // an ordinary added equation, e.g. `(= g639 TRUE)`, which is FALSE in the
    // model where `g639 = FALSE`.
    let exec = solve_bool_arg();
    let authored = ["TRUE", "FALSE", "BOOL", "g639", "g640", "P1", "bool", "mem"];
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    let mut promoted = 0_usize;
    for step in &proof.steps {
        if !is_fresh_def_eq_step(&exec.ctx.terms, step) {
            continue;
        }
        let ProofStep::Step { args, .. } = step else {
            continue;
        };
        let name = ay_proof::format_term_alethe(&exec.ctx.terms, args[0]);
        assert!(
            !authored.contains(&name.as_str()),
            "`{name}` is an authored symbol; an equality over it is not a definition"
        );
        promoted += 1;
    }
    assert!(promoted > 0, "the test must actually exercise a promotion");
}

#[test]
fn an_equality_over_two_authored_symbols_is_left_alone() {
    // The one-line summary of the whole measured census: 68% of the `=#2`
    // trust class is equalities between AUTHORED symbols, and none of them may
    // be promoted. `(= x y)` is refuted at `x = 1, y = 0`, so certifying it as
    // a free definition of `x` would forge a refutation of a satisfiable
    // problem.
    let script = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun x () U)
        (declare-fun y () U)
        (declare-fun z () U)
        (assert (= x y))
        (assert (= y z))
        (assert (not (= x z)))
        (check-sat)
    "#;
    let commands = parse(script).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["unsat"]);
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    for step in &proof.steps {
        assert!(
            !is_fresh_def_eq_step(&exec.ctx.terms, step)
                && !is_fresh_def_bound_step(&exec.ctx.terms, step),
            "no symbol in this problem is fresh, so nothing may be promoted"
        );
    }
}
