// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The z3 model-replay oracle behind the strongest SAT pins of
//! `auflia_verification_consumer_9185_reducers`, and the negative twins that hold the
//! oracle itself to account.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

/// The strongest SAT pin available from an integration test: AY must answer
/// `sat`, also in `--self-check` mode; the quantified publication gate must
/// record a CERTIFICATE behind that `sat` ([`quantified_gate_record`]); and
/// the model AY publishes must satisfy the AUTHORED assertions when replayed
/// through z3.
///
/// Use this — never a bare [`super::expect_sat`] — wherever a pin previously
/// demanded `unknown` "for want of a materialized and rechecked model".
/// Flipping such a pin to `expect_sat` alone would trade a fail-closed guard
/// for a weaker one; this trades it for a stronger one, because it fails on a
/// `sat` that has no model behind it, on one the gate recorded no certificate
/// for, and on one whose model is wrong. Of these checks only the z3 replay
/// is independent of AY: `--self-check` trusts the same certificate grant the
/// gate records (measured: a model check that mis-decides a universal
/// publishes the same wrong `sat` under `--self-check`).
///
/// Replay mechanics: AY's `(get-model)` block is spliced into the replay file
/// verbatim as `define-fun` commands — ordinary SMT-LIB macro definitions — so
/// z3 evaluates the authored formula UNDER exactly the interpretation AY
/// published instead of re-deciding the problem. Any symbol AY omits keeps its
/// `declare-fun`, so a `sat` here proves AY's published interpretation EXTENDS
/// to a total model; it can never be rescued by reinterpreting a symbol AY
/// pinned. `decls` is required to hold one declaration per line so the splice
/// can drop exactly the ones the model defines. Elements of uninterpreted
/// sorts are handled by [`abstract_value_declarations`]. Because the universe
/// is extended rather than closed, a quantifier of `asserts` that binds an
/// uninterpreted sort is checked over z3's choice of universe, not AY's: the
/// replay certifies AY's model for it only when the published functions treat
/// every element of that sort alike (as the seq-concat caller's
/// `logic_bucket__ix := λ_ _. 0` does); otherwise z3 could satisfy it with a
/// universe AY's model does not have.
///
/// The replay file is emitted under `(set-logic ALL)` for the same reason the
/// parent module's `arbitrary_seq_quantifier_is_sat_by_constant_interpretation`
/// cross-check is: z3 rejects the `(Seq Int)` sort under `AUFLIA` and would
/// answer `sat` for a vacuously empty problem, which is not a check of
/// anything.
pub(super) fn expect_sat_with_model_replayed_through_z3(decls: &str, asserts: &str, label: &str) {
    let problem = format!("(set-logic AUFLIA)\n{decls}\n{asserts}\n(check-sat)\n");
    expect_original_problem_with_model_replayed_through_z3(&problem, decls, asserts, label);
}

/// Preserve the complete original reducer, including its authored logic,
/// through all native solves. Only the independent reference replay uses ALL
/// so Z3 accepts the original native sequence sorts.
pub(super) fn expect_original_fixture_with_model_replayed_through_z3(input: &str, label: &str) {
    let (preamble, assertions) = input.split_once("(assert ").expect("original assertions");
    let assertions = format!("(assert {assertions}");
    let assertions = assertions
        .strip_suffix("(check-sat)\n")
        .expect("original final query");
    let declarations = preamble
        .lines()
        .filter(|line| !line.trim_start().starts_with("(set-logic "))
        .collect::<Vec<_>>()
        .join("\n");
    expect_original_problem_with_model_replayed_through_z3(input, &declarations, assertions, label);
}

fn expect_original_problem_with_model_replayed_through_z3(
    problem: &str,
    decls: &str,
    asserts: &str,
    label: &str,
) {
    let result = run_executor_smt_with_timeout(problem, 30).expect("execution should succeed");
    assert_eq!(result, SolverOutcome::Sat, "{label}: expected SAT");

    // `--self-check` must not degrade it either. That mode is NOT an
    // independent check of a quantified model-check certificate (it trusts
    // the same grant), so it is asserted, never relied on.
    let self_checked = crate::common::solve_selfcheck_vec(problem);
    assert_eq!(
        crate::common::sat_result(&self_checked.join("\n")),
        Some("sat"),
        "{label}: AY's own fail-closed self-check must confirm this SAT, not degrade it:\n{self_checked:?}"
    );

    // The verdict must also REST ON a certificate, not merely be right: a
    // `sat` the quantified publication gate let through uncertified is what
    // the retired `unknown` pins stopped, and neither the self-check nor a
    // replay of a correct model can see one.
    let (authored, gate) = quantified_gate_record(problem);
    assert_eq!(
        crate::common::sat_result(&authored.join("\n")),
        Some("sat"),
        "{label}: the authored solve must answer `sat`:\n{authored:?}"
    );
    assert!(
        gate.as_deref().is_some_and(
            |record| record == "confirmed" || record.starts_with("deferred-certified-")
        ),
        "{label}: the quantified model gate recorded no certificate behind this SAT: {gate:?}"
    );

    let with_model = format!("{problem}\n(get-model)\n");
    let output = crate::common::solve(&with_model);
    let model = output
        .split_once("(model")
        .map(|(_, rest)| rest.trim_end().trim_end_matches(')').to_string())
        .unwrap_or_else(|| panic!("{label}: a certified SAT must publish a model:\n{output}"));

    if !crate::common::z3::check_z3_or_skip() {
        return;
    }
    let replay = model_replay_script(decls, &model, asserts)
        .unwrap_or_else(|| panic!("{label}: the published model defines no symbol:\n{output}"));
    assert_eq!(
        z3_replay_outcome(&replay),
        SolverOutcome::Sat,
        "{label}: AY's published model does not satisfy the authored assertions (z3):\n{replay}"
    );
}

/// The output of the authored solve of `problem` (the CLI's boundary) and the
/// `model_check_gate.quantified` record its `check-sat` left: what the
/// published `sat` rests on. `confirmed` is the gate's own evaluation of every
/// quantified conjunct against the emitted model, and each
/// `deferred-certified-*` record names a checked whole-snapshot certificate.
/// Every other record is refused by the caller, including the gate's
/// fail-closed records and every record that discloses a refutation only a
/// fresh executor running the same code re-decided (`discharged-trust`, a
/// disclosed hole rather than a check): `confirmed-discharged-trust` (one of
/// the gate's own confirming refutations) and each
/// `deferred-discharged-trust-*` (a certificate minted on one). The model
/// check's grant never rests on that class.
fn quantified_gate_record(problem: &str) -> (Vec<String>, Option<String>) {
    let commands = ay_frontend::parse(problem).expect("parse");
    let mut executor = ay_dpll::Executor::new();
    let mut output = Vec::new();
    for command in &commands {
        if let Some(line) = executor
            .execute_authored(command)
            .expect("execution should succeed")
        {
            output.push(line);
        }
    }
    let record = executor
        .statistics()
        .get_string("model_check_gate.quantified")
        .map(str::to_owned);
    (output, record)
}

/// The z3 replay file for `model` (the body of AY's `(model ...)` block), or
/// `None` when the model defines no symbol. See
/// [`expect_sat_with_model_replayed_through_z3`] for the splice.
fn model_replay_script(decls: &str, model: &str, asserts: &str) -> Option<String> {
    let defined: Vec<&str> = model
        .lines()
        .filter_map(|line| line.trim().strip_prefix("(define-fun "))
        .filter_map(|rest| rest.split_whitespace().next())
        .collect();
    if defined.is_empty() {
        return None;
    }
    let kept_decls: String = decls
        .lines()
        .filter(|line| {
            let name = line
                .trim()
                .trim_start_matches('(')
                .split_whitespace()
                .nth(1)
                .unwrap_or_default();
            !defined.contains(&name)
        })
        .collect::<Vec<_>>()
        .join("\n");
    let elements = abstract_value_declarations(model);
    Some(format!(
        "(set-logic ALL)\n{kept_decls}\n{elements}{model}\n{asserts}\n(check-sat)\n"
    ))
}

/// AY prints an element of an uninterpreted sort as the abstract value
/// `(as @S!n S)`, a name z3 does not know. Each distinct one is declared as a
/// constant of its sort (quoted, so `(as @S!n S)` resolves to it), and the
/// constants of one sort are pairwise `distinct`, because two abstract values
/// name two elements. They are otherwise free, which is the helper's "extends
/// to a total model" reading once more: z3 may neither merge two of AY's
/// elements nor re-point a symbol AY pinned to one of them.
fn abstract_value_declarations(model: &str) -> String {
    let mut sorts: Vec<(&str, Vec<&str>)> = Vec::new();
    for (start, _) in model.match_indices("(as @") {
        let body = &model[start + "(as ".len()..];
        let mut depth = 1_usize;
        let Some(end) = body.find(|c: char| {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            depth == 0
        }) else {
            continue;
        };
        let Some((name, sort)) = body[..end].split_once(char::is_whitespace) else {
            continue;
        };
        let sort = sort.trim();
        match sorts.iter_mut().find(|(known, _)| *known == sort) {
            Some((_, names)) if names.contains(&name) => {}
            Some((_, names)) => names.push(name),
            None => sorts.push((sort, vec![name])),
        }
    }
    let mut declarations = String::new();
    for (sort, names) in &sorts {
        for name in names {
            declarations.push_str(&format!("(declare-fun |{name}| () {sort})\n"));
        }
        if names.len() > 1 {
            let quoted: Vec<String> = names.iter().map(|name| format!("|{name}|")).collect();
            declarations.push_str(&format!("(assert (distinct {}))\n", quoted.join(" ")));
        }
    }
    declarations
}

/// z3's verdict on one replay file. Each call gets its own file: the tests of
/// this crate run concurrently in one process.
fn z3_replay_outcome(replay: &str) -> SolverOutcome {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let path = std::env::temp_dir().join(format!(
        "ay_9185_model_replay_{}_{}.smt2",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::write(&path, replay).expect("write replay file");
    let outcome = crate::common::z3::run_z3_file(&path, 20).expect("run z3");
    let _ = std::fs::remove_file(&path);
    outcome
}

#[test]
#[timeout(120_000)]
fn theory_program_original_has_value_publishes_a_replayed_model() {
    expect_original_fixture_with_model_replayed_through_z3(
        include_str!(
            "../../fixtures/verification_consumer_9185/slice_index_has_value_usize_sat.smt2"
        ),
        "original has_value_usize",
    );
}

#[test]
#[timeout(120_000)]
fn theory_program_original_in_bounds_usize_publishes_a_replayed_model() {
    expect_original_fixture_with_model_replayed_through_z3(
        include_str!(
            "../../fixtures/verification_consumer_9185/slice_index_in_bounds_usize_sat.smt2"
        ),
        "original in_bounds_usize",
    );
}

#[test]
#[timeout(120_000)]
fn theory_program_original_inclusive_range_publishes_a_replayed_model() {
    expect_original_fixture_with_model_replayed_through_z3(
        include_str!("../../fixtures/verification_consumer_9185/slice_index_in_bounds_range_inclusive_sat.smt2"),
        "original in_bounds_range_inclusive",
    );
}

/// The abstract-value splice is new acceptance in the replay oracle, so it is
/// held to its negative twins: a published element assignment that falsifies
/// the assertions must replay `unsat`, including when the falsity rests only
/// on two abstract values being DIFFERENT elements, or on a symbol the model
/// omits being unable to tell apart two names AY bound to ONE element.
#[test]
#[timeout(30_000)]
fn model_replay_of_abstract_values_rejects_a_falsifying_model() {
    if !crate::common::z3::check_z3_or_skip() {
        return;
    }
    let decls =
        "(declare-sort U 0)\n(declare-fun a () U)\n(declare-fun b () U)\n(declare-fun p (U) Bool)";
    let two = "\n  (define-fun a () U (as @U!0 U))\n  (define-fun b () U (as @U!1 U))\n";
    let one = "\n  (define-fun a () U (as @U!0 U))\n  (define-fun b () U (as @U!0 U))\n";
    let cases = [
        (two, "(distinct a b)", SolverOutcome::Sat),
        (two, "(= a b)", SolverOutcome::Unsat),
        (one, "(distinct a b)", SolverOutcome::Unsat),
        (one, "(and (p a) (not (p b)))", SolverOutcome::Unsat),
    ];
    for (model, assertion, expected) in cases {
        let asserts = format!("(assert {assertion})");
        let replay =
            model_replay_script(decls, model, &asserts).expect("the model defines a and b");
        assert_eq!(
            z3_replay_outcome(&replay),
            expected,
            "{assertion}:\n{replay}"
        );
    }
}
