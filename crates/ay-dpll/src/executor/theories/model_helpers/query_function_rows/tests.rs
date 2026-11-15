// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Query row cleanup observes the same source window as model certification.
//! Parsed declarations and real solve/scope commands own all query snapshots.
//! Hand-built rows below are candidate DATA only, never source or SAT authority.

use super::*;
use crate::executor_types::SolveResult;
use ay_core::{Sort, Symbol, TermData, TermId};
use ay_euf::EufModel;

fn commands(exec: &mut Executor, source: &str) -> Vec<String> {
    let mut output = Vec::new();
    for command in ay_frontend::parse(source).expect("well-formed native input") {
        if let Some(value) = exec
            .execute_authored(&command)
            .expect("native command succeeds")
        {
            output.push(value);
        }
    }
    output
}

fn fixture() -> Executor {
    let mut exec = Executor::new();
    assert!(commands(
        &mut exec,
        "(set-option :produce-models true) (set-logic QF_UFLIA)
        (declare-const x Int) (declare-fun f (Int) Int) (declare-fun p (Int) Bool)"
    )
    .is_empty());
    exec
}

fn application(exec: &mut Executor, name: &str, value: i32, sort: Sort) -> TermId {
    // The matching function is an actual declaration in this current context.
    assert!(exec.ctx.symbol_info_by_identity(name).is_some());
    let argument = exec.ctx.terms.mk_int(value.into());
    exec.ctx
        .terms
        .mk_app(Symbol::named(name), vec![argument], sort)
}

fn rows(name: &str, entries: &[(TermId, &str, &str)]) -> EufModel {
    let mut model = EufModel::default();
    model.function_tables.insert(
        name.into(),
        entries
            .iter()
            .map(|(_, arg, result)| (vec![(*arg).into()], (*result).into()))
            .collect(),
    );
    model.function_table_terms.insert(
        name.into(),
        entries.iter().map(|(source, _, _)| *source).collect(),
    );
    model
}

fn sources<'a>(model: &'a EufModel, name: &str) -> &'a [TermId] {
    model
        .function_table_terms
        .get(name)
        .map_or(&[], Vec::as_slice)
}

fn apps(exec: &Executor, roots: &[TermId], name: &str) -> Vec<TermId> {
    let mut stack = roots.to_vec();
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut found = Vec::new();
    while let Some(term) = stack.pop() {
        assert!(seen.len() < 4096, "bounded component fixture");
        if !seen.insert(term) {
            continue;
        }
        match exec.ctx.terms.get(term) {
            TermData::App(symbol, arguments) => {
                if symbol == &Symbol::named(name) {
                    found.push(term);
                }
                stack.extend(arguments.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, yes, no) => stack.extend([*condition, *yes, *no]),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, value)| *value));
                stack.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                stack.extend(triggers.iter().flatten().copied());
            }
            _ => {}
        }
    }
    found.sort_by_key(|term| term.index());
    found
}

#[test]
fn native_rewritten_original_point_survives_cleanup_and_the_public_gate() {
    let mut exec = fixture();
    commands(
        &mut exec,
        "(assert (= x 0)) (assert (= (f (+ x 1)) 10)) (assert (= (f 2) 20))",
    );
    let original = exec.ctx.assertions.clone();
    let original_apps = apps(&exec, &original, "f");
    assert_eq!(original_apps.len(), 2);
    let original_expression = original_apps.iter().copied().find(|&term| {
        let TermData::App(_, arguments) = exec.ctx.terms.get(term) else { return false };
        matches!(exec.ctx.terms.get(arguments[0]), TermData::App(symbol, _) if symbol == &Symbol::named("+"))
    }).expect("the actual unfurled source application");
    let rewritten = application(&mut exec, "f", 1, Sort::Int);
    assert_ne!(original_expression, rewritten);
    assert!(!original_apps.contains(&rewritten));
    assert!(exec.independent_gate_authored_assertions.is_none());
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    assert_eq!(exec.ctx.assertions, original);
    assert!(
        exec.independent_gate_authored_assertions.is_none(),
        "the real solve restored its snapshot owner"
    );
    let model = exec
        .last_model
        .as_ref()
        .expect("a native candidate passed every gate");
    let euf = model.euf_model.as_ref().expect("UF model");
    assert!(
        sources(euf, "f").contains(&original_expression),
        "dedup's original source must not be dropped at storage"
    );
    assert_eq!(euf.function_tables["f"].len(), sources(euf, "f").len());
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
    let values = commands(&mut exec, "(get-value ((f 1) (f 2)))");
    assert_eq!(values.len(), 1);
    assert!(
        values[0].contains("10") && values[0].contains("20"),
        "{values:?}"
    );
}

#[test]
fn equal_argument_dedup_does_not_make_the_original_source_a_dead_row() {
    let mut exec = fixture();
    commands(
        &mut exec,
        "(assert (= x 0)) (assert (= (f (+ x 1)) 10)) (assert (= (f 1) 10))",
    );
    let original_apps = apps(&exec, &exec.ctx.assertions, "f");
    assert_eq!(original_apps.len(), 2);
    let first = original_apps[0];
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    let euf = exec
        .last_model
        .as_ref()
        .unwrap()
        .euf_model
        .as_ref()
        .unwrap();
    assert_eq!(
        euf.function_tables["f"].len(),
        1,
        "same current typed point is deduplicated"
    );
    assert_eq!(
        sources(euf, "f"),
        [first],
        "dedup's first genuine source remains retained"
    );
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
}

#[test]
fn truly_unasserted_applications_still_lose_their_candidate_rows() {
    let mut exec = fixture();
    commands(&mut exec, "(assert (= (f 1) 10))");
    let live = application(&mut exec, "f", 1, Sort::Int);
    let dead = application(&mut exec, "f", 99, Sort::Int);
    let mut candidate = rows("f", &[(dead, "99", "990"), (live, "1", "10")]);
    exec.retain_query_function_table_rows(&mut candidate)
        .unwrap();
    assert_eq!(sources(&candidate, "f"), [live]);
    assert_eq!(
        candidate.function_tables["f"],
        [(vec!["1".to_string()], "10".to_string())]
    );
}

#[test]
fn reset_assertions_and_a_new_real_query_do_not_keep_old_sources() {
    let mut exec = fixture();
    commands(&mut exec, "(assert (= (f 1) 10)) (check-sat)");
    let old = application(&mut exec, "f", 1, Sort::Int);
    commands(&mut exec, "(reset-assertions)");
    assert!(exec.last_model.is_none());
    assert!(exec.independent_gate_authored_assertions.is_none());
    assert!(exec.last_assumptions.is_none());
    commands(&mut exec, "(assert (= (f 2) 20))");
    let current = application(&mut exec, "f", 2, Sort::Int);
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    let mut candidate = rows("f", &[(old, "1", "10"), (current, "2", "20")]);
    exec.retain_query_function_table_rows(&mut candidate)
        .unwrap();
    assert_eq!(sources(&candidate, "f"), [current]);
}

#[test]
fn actual_temporary_assumptions_are_kept_only_for_their_own_query() {
    let mut exec = fixture();
    let assumption = application(&mut exec, "p", 3, Sort::Bool);
    assert_eq!(
        exec.check_sat_assuming(&[assumption]).unwrap(),
        SolveResult::Sat
    );
    assert_eq!(exec.last_assumptions.as_deref(), Some(&[assumption][..]));
    assert!(exec.independent_gate_authored_assertions.is_none());
    let mut candidate = rows("p", &[(assumption, "3", "true")]);
    exec.retain_query_function_table_rows(&mut candidate)
        .unwrap();
    assert_eq!(sources(&candidate, "p"), [assumption]);
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    assert!(exec.last_assumptions.is_none());
    exec.retain_query_function_table_rows(&mut candidate)
        .unwrap();
    assert!(candidate.function_tables.is_empty());
    assert!(candidate.function_table_terms.is_empty());
}

#[test]
fn push_pop_restores_query_rows_instead_of_reusing_the_inner_snapshot() {
    let mut exec = fixture();
    commands(
        &mut exec,
        "(assert (= (f 1) 10)) (push 1) (assert (= (f 2) 20))",
    );
    let outer = application(&mut exec, "f", 1, Sort::Int);
    let inner = application(&mut exec, "f", 2, Sort::Int);
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    commands(&mut exec, "(pop 1)");
    assert!(exec.independent_gate_authored_assertions.is_none());
    assert!(exec.last_model.is_none());
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    let mut candidate = rows("f", &[(inner, "2", "20"), (outer, "1", "10")]);
    exec.retain_query_function_table_rows(&mut candidate)
        .unwrap();
    assert_eq!(sources(&candidate, "f"), [outer]);
}

#[test]
fn reset_retires_the_model_assumptions_and_all_captured_root_windows() {
    let mut exec = fixture();
    let assumption = application(&mut exec, "p", 3, Sort::Bool);
    assert_eq!(
        exec.check_sat_assuming(&[assumption]).unwrap(),
        SolveResult::Sat
    );
    commands(&mut exec, "(reset)");
    assert!(exec.last_model.is_none());
    assert!(exec.last_assumptions.is_none());
    assert!(exec.independent_gate_authored_assertions.is_none());
    assert!(exec.function_row_roots.is_empty());
    assert!(exec.ctx.assertions.is_empty());
    commands(&mut exec, "(set-option :produce-models true) (set-logic QF_UFLIA) (declare-fun fresh (Int) Int) (assert (= (fresh 4) 40))");
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    let public = commands(&mut exec, "(get-model)");
    assert_eq!(public.len(), 1);
    assert!(
        public[0].contains("fresh") && !public[0].contains("define-fun f "),
        "{public:?}"
    );
}

#[test]
fn a_preprocessed_authored_quantifier_preserves_the_existing_instance_policy() {
    let mut exec = Executor::new();
    commands(
        &mut exec,
        "(set-option :produce-models true) (set-logic UFLIA)
        (declare-fun f (Bool) Int)
        (assert (forall ((b Bool)) (= (f b) (ite b 1 0))))",
    );
    let original = exec.ctx.assertions.clone();
    assert!(matches!(
        exec.ctx.terms.get(original[0]),
        TermData::Forall(..)
    ));
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    assert_eq!(exec.ctx.assertions, original);
    assert!(exec.independent_gate_authored_assertions.is_none());
    let yes = exec.ctx.terms.true_term();
    let no = exec.ctx.terms.false_term();
    let app_yes = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![yes], Sort::Int);
    let app_no = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![no], Sort::Int);
    assert!(!apps(&exec, &original, "f").contains(&app_yes));
    let mut candidate = rows("f", &[(app_yes, "true", "1"), (app_no, "false", "0")]);
    let before = format!("{candidate:?}");
    exec.retain_query_function_table_rows(&mut candidate)
        .unwrap();
    assert_eq!(
        format!("{candidate:?}"),
        before,
        "quantified query keeps the old instance-row policy"
    );
    // Direct quantified confirmation is a one-gate handoff consumed by
    // the first native check. Re-enter the real publication path; a bare
    // second gate call cannot reuse that already-consumed confirmation.
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    assert_eq!(exec.ctx.assertions, original);
    assert!(exec.independent_gate_authored_assertions.is_none());
}

#[test]
fn malformed_source_alignment_keeps_the_existing_refusal_policy() {
    let exec = fixture();
    let mut candidate = rows("f", &[(TermId(u32::MAX), "1", "10")]);
    candidate.function_table_terms.get_mut("f").unwrap().clear();
    let before = format!("{candidate:?}");
    exec.retain_query_function_table_rows(&mut candidate)
        .unwrap();
    assert_eq!(
        format!("{candidate:?}"),
        before,
        "mismatched row/source lengths are unchanged, not repaired or accepted here"
    );
}

#[test]
fn row_retention_never_turns_an_incorrect_public_witness_into_sat_authority() {
    let mut exec = fixture();
    commands(
        &mut exec,
        "(assert (= x 0)) (assert (= (f (+ x 1)) 10)) (assert (= (f 2) 20))",
    );
    assert_eq!(commands(&mut exec, "(check-sat)"), ["sat"]);
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Sat
    );
    let euf = exec
        .last_model
        .as_mut()
        .unwrap()
        .euf_model
        .as_mut()
        .unwrap();
    let table = euf.function_tables.get_mut("f").unwrap();
    assert!(!table.is_empty());
    // Candidate DATA corruption changes only the published UF interpretation.
    // Its old pins remain intact to detect a hybrid pin-preference waiver.
    for (_, result) in table {
        *result = "999".into();
    }
    crate::executor::model::eval_memo_clear();
    assert_eq!(
        exec.apply_independent_model_gate(SolveResult::Sat),
        SolveResult::Unknown
    );
}
