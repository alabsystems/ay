// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mechanism controls for exact native roots and authored-unit propagation.
use super::*;
use ay_frontend::command::Command;

fn declarations() -> Executor {
    let mut exec = Executor::new();
    let input = "(set-logic ALL) (declare-sort Carrier 0) \
        (declare-const a Carrier) (declare-const b Carrier) \
        (declare-const ready Bool) (declare-const unrelated Bool) \
        (declare-const aux Int) (declare-fun f (Carrier) Int) \
        (declare-fun g (Carrier) Int)";
    exec.execute_all(&parse(input).expect("declarations parse"))
        .expect("declarations execute");
    exec
}

fn typed_term(exec: &mut Executor, input: &str) -> TermId {
    let commands = parse(&format!("(assert {input})")).expect("native fixture parses");
    let Command::Assert(surface) = &commands[0] else {
        panic!("assertion")
    };
    exec.ctx
        .elaborate_surface_subterm(surface)
        .expect("typed native term")
}

fn native(exec: &mut Executor, input: &str) -> TermId {
    let root = typed_term(exec, input);
    exec.ctx.add_assertion_with_parsed(
        root,
        FrontendTerm::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.into()),
    );
    root
}

fn guarded(unit: Option<&str>, pin: &str, clause: &str) -> Executor {
    let mut exec = declarations();
    let _ = native(&mut exec, pin);
    let _ = native(&mut exec, clause);
    if let Some(unit) = unit {
        let _ = native(&mut exec, unit);
    }
    let _ = native(&mut exec, "(= (f b) aux)");
    let _ = native(&mut exec, "(not (= 0 aux))");
    exec
}

fn refuses(exec: &mut Executor) {
    let mut proof = placeholder();
    let before = format!("{:?}", proof.steps);
    assert!(!exec.rescue_fold_with_raw_ground_closure(&mut proof));
    assert_eq!(format!("{:?}", proof.steps), before);
    assert!(exec.last_proof_raw_original_assertions.is_empty());
}

#[test]
fn authored_native_clause_propagates_a_guard_into_checked_uf_congruence() {
    for clause in ["(or (not ready) (= a b))", "(=> ready (= a b))"] {
        let mut exec = guarded(Some("ready"), "(= 0 (f a))", clause);
        let roots = exec.ground_closure_roots().expect("exact native roots");
        assert!(
            roots.raw.is_empty(),
            "native terms never widen the raw premise ledger"
        );
        let mut proof = placeholder();
        assert!(exec.rescue_fold_with_raw_ground_closure(&mut proof));
        assert!(exec
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete()));
        ay_proof::validate_reachable_assumes_in_problem_scope(
            &proof,
            &exec.exact_concrete_authored_scope(),
        )
        .expect("exact source authority");
        assert!(
            lemma_count(&proof, |kind, _| matches!(
                kind,
                TheoryLemmaKind::EufCongruent
            )) > 0
        );
    }
}

#[test]
fn authored_native_clause_requires_the_correct_guard_and_function() {
    for unit in [None, Some("unrelated"), Some("(not ready)")] {
        refuses(&mut guarded(
            unit,
            "(= 0 (f a))",
            "(or (not ready) (= a b))",
        ));
    }
    refuses(&mut guarded(
        Some("ready"),
        "(= 0 (g a))",
        "(or (not ready) (= a b))",
    ));
    refuses(&mut guarded(
        Some("ready"),
        "(= 0 (f a))",
        "(or ready (= a b))",
    ));
}

#[test]
fn authored_native_clause_does_not_use_a_popped_or_generated_unit() {
    let mut exec = guarded(None, "(= 0 (f a))", "(or (not ready) (= a b))");
    exec.execute_all(&parse("(push 1)").unwrap()).unwrap();
    let ready = native(&mut exec, "ready");
    exec.execute_all(&parse("(pop 1)").unwrap()).unwrap();
    assert!(!exec.exact_concrete_authored_scope().contains(&ready));
    refuses(&mut exec);
    // Solver-generated stack contents have no immutable source authority.
    exec.ctx.assertions.push(ready);
    refuses(&mut exec);
}

#[test]
fn authored_native_clause_does_not_capture_a_shadowed_guard() {
    let mut exec = guarded(None, "(= 0 (f a))", "(or (not ready) (= a b))");
    let _ = native(&mut exec, "(forall ((ready Bool)) (or ready (not ready)))");
    let _ = native(&mut exec, "(let ((ready true)) ready)");
    refuses(&mut exec);
}

#[test]
fn authored_native_roots_bound_rows_and_deduplicate_before_search() {
    let mut exec = declarations();
    for _ in 0..70 {
        let _ = native(&mut exec, "ready");
    }
    let roots = exec
        .ground_closure_roots()
        .expect("bounded repeated native rows");
    assert_eq!(roots.search.len(), 1);
    assert!(roots.raw.is_empty());
    for _ in 70..=MAX_NATIVE_AUTHORED_ROWS {
        let _ = native(&mut exec, "ready");
    }
    assert!(
        exec.ground_closure_roots().is_none(),
        "row budget is finite"
    );
}

#[test]
fn authored_native_clause_respects_the_frozen_problem_epoch() {
    let mut exec = guarded(Some("ready"), "(= 0 (f a))", "(or (not ready) (= a b))");
    let mut roots = exec.ctx.concrete_authored_assertion_terms();
    let ready = exec
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol("ready".into()))
        .unwrap();
    roots.retain(|root| *root != ready);
    exec.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: roots.clone(),
            problem_assertions: roots,
            assertion_sources: Default::default(),
        },
    );
    refuses(&mut exec);
}

#[test]
fn authored_native_clause_emission_rejects_a_source_epoch_drift() {
    let mut exec = guarded(Some("ready"), "(= 0 (f a))", "(or (not ready) (= a b))");
    let roots = exec.ground_closure_roots().unwrap();
    let mut search = GroundSearch::default();
    let conflict = exec
        .saturate_ground_search(&mut search, &roots.search, &[])
        .unwrap();
    exec.proof_problem_assertion_provenance = Some(
        crate::executor::theories::solve_harness::ProofProblemAssertionProvenance {
            original_problem_assertions: Vec::new(),
            problem_assertions: Vec::new(),
            assertion_sources: Default::default(),
        },
    );
    assert!(
        exec.emit_ground_closure_refutation(&search, conflict)
            .is_none(),
        "new Boolean propagation cannot invent raw premise authority"
    );
}

fn raw_implication(unit: Option<&str>) -> Executor {
    let mut exec = declarations();
    let _ = native(&mut exec, "(= 0 (f a))");
    let ready = typed_term(&mut exec, "ready");
    let equality = typed_term(&mut exec, "(= a b)");
    // Bypass frontend implication-to-or normalization. This must exercise
    // the actual native core shape whose former `Implies` rule was refused.
    let implication =
        exec.ctx
            .terms
            .mk_app_structural(Symbol::named("=>"), [ready, equality], Sort::Bool);
    assert!(matches!(exec.ctx.terms.get(implication),
        TermData::App(head, _) if head.name() == "=>"));
    exec.ctx.add_assertion_with_parsed(
        implication,
        FrontendTerm::Symbol(crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER.into()),
    );
    if let Some(unit) = unit {
        let _ = native(&mut exec, unit);
    }
    let _ = native(&mut exec, "(= (f b) aux)");
    let _ = native(&mut exec, "(not (= 0 aux))");
    exec
}

#[test]
fn authored_native_raw_implication_uses_checked_positive_clausification() {
    let mut exec = raw_implication(Some("ready"));
    let mut proof = placeholder();
    assert!(exec.rescue_fold_with_raw_ground_closure(&mut proof));
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::ImpliesPos,
            ..
        }
    )));
    assert!(!proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Implies,
            ..
        }
    )));
}

#[test]
fn authored_native_raw_implication_requires_the_exact_positive_guard() {
    for unit in [None, Some("unrelated"), Some("(not ready)")] {
        refuses(&mut raw_implication(unit));
    }
}
