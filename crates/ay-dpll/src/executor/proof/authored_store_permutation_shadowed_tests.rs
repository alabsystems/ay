// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn run(problem: &str, name: &str, expected: &str) {
    let script = format!(
        "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n{problem}"
    );
    let mut executor = Executor::new();
    let results = executor
        .execute_all(&ay_frontend::parse(&script).unwrap())
        .unwrap();
    if results != [expected] {
        if let Some(proof) = executor.last_proof.as_ref() {
            eprintln!(
                "{name}: native check={:?}",
                executor.check_proof_strict_with_datatypes(proof)
            );
            let overrides = executor.proof_export_term_overrides();
            for (term, surface) in overrides.iter().flatten() {
                let canonical = ay_proof::render_term_canonical(&executor.ctx.terms, *term);
                eprintln!(
                    "{name}: {term:?} surface={} canonical={} identical={} prefix={:?}",
                    surface.len(),
                    canonical.len(),
                    *surface == canonical,
                    surface.chars().take(160).collect::<String>()
                );
            }
            let effective = ay_proof::effective_wire_term_overrides_for_proof(
                proof,
                &executor.ctx.terms,
                overrides.as_ref(),
            );
            eprintln!(
                "{name}: effective overrides={:?}",
                effective
                    .as_ref()
                    .map(|map| map.as_ref().map(|map| map.len()))
            );
        }
    }
    assert_eq!(
        results,
        [expected],
        "{name}: {:?}",
        executor.unknown_reason()
    );
    if expected == "unsat" {
        let proof = executor.last_proof.as_ref().unwrap();
        assert!(executor
            .check_proof_strict_with_datatypes(proof)
            .unwrap()
            .is_complete());
        assert!(!executor.proof_has_known_wire_gap(proof));
        let exports = executor
            .execute_all(&ay_frontend::parse("(get-proof)").unwrap())
            .unwrap();
        assert_eq!(exports.len(), 1);
        assert!(exports[0].contains(":rule arrays_ext"), "{}", exports[0]);
        let scoped = executor
            .try_export_last_proof_alethe_for_problem_scope()
            .expect("authenticated problem scope")
            .unwrap_or_else(|error| {
                let overrides = executor.proof_export_term_overrides().unwrap_or_default();
                let identities: Vec<_> = overrides
                    .iter()
                    .map(|(term, surface)| {
                        let canonical = ay_proof::render_term_canonical(&executor.ctx.terms, *term);
                        (term, surface.len(), canonical.len(), *surface == canonical)
                    })
                    .collect();
                panic!("{name}: scoped export failed: {error}; surface identities={identities:?}")
            });
        let mut streamed = Vec::new();
        executor
            .try_export_last_proof_alethe_for_problem_scope_to(&mut streamed)
            .expect("authenticated streaming scope")
            .expect("checked streaming export");
        assert_eq!(streamed, scoped.as_bytes());
        assert!(!scoped.contains(":rule hole") && !scoped.contains(":rule trust"));
        let path = std::env::temp_dir().join(format!(
            "ay-shadow-solver-{name}-{}.json",
            std::process::id()
        ));
        std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":script,"proof":scoped})).unwrap()).unwrap();
        println!("independent replay certificate: {}", path.display());
    }
}

#[test]
fn shadowed_stores_solver_proves_callback_projections_with_original_guards() {
    for (name, problem) in [
        ("cell32", include_str!("../../../../ay-proof/src/alethe_printer/shadowed_stores_fixtures/cell32-public-input.smt2")),
        ("cell64", include_str!("../../../../ay-proof/src/alethe_printer/shadowed_stores_fixtures/cell64-public-input.smt2")),
    ] {
        run(&problem.replace("(exit)", ""), name, "unsat");
    }
}

#[test]
fn shadowed_stores_solver_handles_symbolic_aliasing_and_rejects_changed_last_writes() {
    let prefix = "(set-logic QF_AUFLIA)\n(declare-fun a () (Array Int Int))\n(declare-fun i () Int)\n(declare-fun j () Int)\n(declare-fun u () Int)\n(declare-fun v () Int)\n(declare-fun w () Int)\n";
    for (label, right, expected) in [
        ("symbolic", "(store (store a j v) i w)", "unsat"),
        ("changed-value", "(store (store a j v) i u)", "sat"),
        ("changed-order", "(store (store a i w) j v)", "sat"),
        ("missing-write", "(store a i w)", "sat"),
    ] {
        let problem = format!(
            "{prefix}(assert (not (= (store (store (store a i u) j v) i w) {right})))\n(check-sat)"
        );
        run(&problem, label, expected);
    }
}

#[test]
fn shadowed_stores_solver_keeps_choice_capture_outside_strict_wire_subset() {
    let input = "(set-logic QF_AUFLIA) (declare-fun a () (Array Int Int)) (declare-fun x () Int) (declare-fun j () Int) (declare-fun u () Int) (declare-fun v () Int) (declare-fun w () Int) (assert (not (= (store (store (store a x u) j v) x w) (store (store a j v) x w)))) (check-sat)";
    run(input, "capture", "unknown");
}

#[test]
fn shadowed_stores_solver_publishes_original_callback_queries_with_definitions() {
    for (name, problem) in [
        ("authored-cell32", include_str!("../../../../ay-proof/src/alethe_printer/shadowed_stores_fixtures/cell32-public-input-authored.smt2")),
        ("authored-cell64", include_str!("../../../../ay-proof/src/alethe_printer/shadowed_stores_fixtures/cell64-public-input-authored.smt2")),
    ] {
        run(&problem.replace("(exit)", ""), name, "unsat");
    }
}

#[test]
fn shadowed_stores_solver_preserves_definition_bodies_and_changed_last_values() {
    let prefix = "(set-logic QF_ABV)\n(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))\n(declare-fun i () (_ BitVec 8))\n(declare-fun u () (_ BitVec 8))\n(declare-fun v () (_ BitVec 8))\n(define-fun index () (_ BitVec 8) (bvadd i (_ bv0 8)))\n";
    let mut left = "a".to_string();
    for position in 0..80 {
        let value = if position == 79 { "v" } else { "u" };
        left = format!("(store {left} index {value})");
    }
    for (name, value, expected) in [
        ("deep-definition", "v", "unsat"),
        ("changed-definition", "u", "sat"),
    ] {
        let problem = format!("{prefix}(define-fun left () (Array (_ BitVec 8) (_ BitVec 8)) {left})\n(define-fun right () (Array (_ BitVec 8) (_ BitVec 8)) (store a index {value}))\n(assert (not (= left right)))\n(check-sat)");
        run(&problem, name, expected);
    }
}
