// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Evidence rules for a universal equated with an authored fact
//! (#iff-split-implied-authority): the implied-universal lane publishes
//! `unsat` only beside the document a consumer receives, assuming the
//! input's own assertions, and hole-free where the posture demands it.
//! Fixtures and ground truth: `quantifier_under_boolean_equality.rs`.

use super::quantifier_under_boolean_equality::{
    z3_mode_verdicts, W1_IMPLIED, W1_ITE_COEFFICIENT, W1_MOD_COEFFICIENT, W1_WITH_SECOND_UNIVERSAL,
};

/// The implication form is never refuted wrongly and never answered `sat`;
/// the shed posture, which owes no document, still refutes it.
#[test]
fn the_implication_form_is_refuted_where_no_document_is_owed() {
    assert!(
        z3_mode_verdicts(W1_IMPLIED).iter().any(|r| r == "unsat"),
        "the implication's instance at -2 refutes the query"
    );
    for results in [
        crate::common::solve_authored_vec(W1_IMPLIED),
        crate::common::solve_authored_selfcheck_vec(W1_IMPLIED),
    ] {
        assert!(
            !results.iter().any(|r| r == "sat"),
            "WRONG ANSWER: the query is UNSATISFIABLE; got {results:?}"
        );
    }
}

/// #iff-split-implied-authority: `--self-check` publishes this lane's `unsat`
/// only beside a document an external checker can check end to end — every
/// premise the input's own, no unproved step. At 36d936e62 all three
/// published under `--self-check` while the certificate line read
/// `ay_self_checkable=no foreign_assumes=yes`. The fixture whose document is
/// clean (the second-universal file; carcara `valid`) still publishes.
#[test]
fn self_check_publishes_an_equated_universal_only_with_a_checkable_document() {
    for (name, smt) in [
        ("ite coefficient", W1_ITE_COEFFICIENT),
        ("mod coefficient", W1_MOD_COEFFICIENT),
        ("second universal", W1_WITH_SECOND_UNIVERSAL),
    ] {
        let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse: {err}"));
        // The CLI's `--self-check`: fail-closed self-check plus the
        // synthesized best-effort certificate it publishes beside the verdict.
        let mut exec = ay_dpll::Executor::new();
        exec.set_self_check(true);
        exec.set_best_effort_produce_proofs(1_000_000);
        let mut results = Vec::new();
        for command in &commands {
            if let Some(line) = exec
                .execute_authored(command)
                .unwrap_or_else(|err| panic!("{name}: execution failed: {err}"))
            {
                results.push(line);
            }
        }
        assert!(
            !results.iter().any(|r| r == "sat"),
            "WRONG ANSWER ({name}): the query is UNSATISFIABLE; got {results:?}"
        );
        if name == "second universal" {
            assert!(
                results.iter().any(|r| r == "unsat"),
                "{name}: its certificate is clean, so --self-check publishes; got {results:?}"
            );
        }
        if !results.iter().any(|r| r == "unsat") {
            continue;
        }
        let mut document = Vec::new();
        let rendered = exec.try_export_last_proof_alethe_for_problem_scope_to(&mut document);
        assert!(
            matches!(rendered, Some(Ok(()))),
            "{name}: a published --self-check unsat renders its document"
        );
        let document = String::from_utf8(document).expect("utf-8 document");
        assert!(
            !document.contains(":rule hole")
                && !document.contains("((v_")
                && !document.contains(" v_"),
            "{name}: --self-check published unsat beside an uncheckable document:\n{document}"
        );
    }
}
