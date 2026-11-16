// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn bounded_authored_canonical_render_projects_and_instantiates_quantifiers() {
    for (label, declarations, body, ground) in [
        (
            "predicate",
            "(declare-const c Int) (declare-fun P (Int) Bool)",
            "(forall ((x Int)) (P x))",
            "(P c)",
        ),
        (
            "array",
            "(declare-const c (_ BitVec 64)) (declare-const a (Array (_ BitVec 64) (_ BitVec 8))) (declare-fun P ((_ BitVec 8)) Bool)",
            "(forall ((x (_ BitVec 64))) (P (select (store a #x0000000000000000 #x01) x)))",
            "(P (select (store a #x0000000000000000 #x01) c))",
        ),
    ] {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        let input = format!(
            "(set-logic ALL) (declare-const p Bool) {declarations} \
             (assert (and p {body})) (assert (not {ground}))"
        );
        executor
            .execute_all(&ay_frontend::parse(&input).unwrap())
            .unwrap();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let roots = executor.ctx.assertions.clone();
        let TermData::App(_, operands) = executor.ctx.terms.get(roots[0]) else {
            panic!("fixture keeps its conjunction");
        };
        let (index, &quantifier) = operands
            .iter()
            .enumerate()
            .find(|(_, term)| matches!(executor.ctx.terms.get(**term), TermData::Forall(..)))
            .unwrap();
        let TermData::Not(instance) = executor.ctx.terms.get(roots[1]) else {
            panic!("fixture keeps its negative instance");
        };
        let instance = *instance;
        let witness = executor
            .ctx
            .elaborate_surface_subterm(&FrontendTerm::Symbol("c".to_string()))
            .unwrap();
        let negated_source = executor.ctx.terms.mk_not_raw(roots[0]);
        let not_forall = executor.ctx.terms.mk_not_raw(quantifier);
        let implication = executor.ctx.terms.mk_app(
            Symbol::named("or"),
            [not_forall, instance],
            Sort::Bool,
        );
        let mut proof = Proof::new();
        let source = proof.add_assume(roots[0], None);
        let negative = proof.add_assume(roots[1], None);
        let projection = proof.add_rule_step(
            AletheRule::AndPos(u32::try_from(index).unwrap()),
            vec![negated_source, quantifier],
            vec![],
            vec![],
        );
        let universal = proof.add_resolution(vec![quantifier], roots[0], source, projection);
        let instantiated = proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            vec![],
            vec![witness],
        );
        let disjunction = proof.add_rule_step(
            AletheRule::Or,
            vec![not_forall, instance],
            vec![instantiated],
            vec![],
        );
        let positive = proof.add_resolution(vec![instance], quantifier, universal, disjunction);
        proof.add_resolution(vec![], instance, positive, negative);
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .unwrap()
            .is_complete());
        executor.restore_reachable_authored_assume_surface_overrides(&proof);
        assert!(!executor.last_unsat_proof_reconstruction_suppressed);
        let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &executor.ctx.terms,
            &roots,
            executor.last_proof_term_overrides.as_ref(),
        )
        .unwrap();
        assert!(wire.contains(".qr (cl (= (forall"), "{wire}");
        assert!(wire.contains(":rule forall_inst"));
        assert!(!wire.contains(":rule hole"));
        write_projected_quantifier_certificate(label, &input, &wire);
    }
}

fn write_projected_quantifier_certificate(label: &str, input: &str, wire: &str) {
    let packet = std::env::temp_dir().join(format!(
        "ay-authored-projected-quantifier-{label}-{}.json",
        std::process::id(),
    ));
    std::fs::write(
        &packet,
        serde_json::to_vec(&serde_json::json!({
            "type": "alethe_certificate", "version": "1.0",
            "problem": format!("{input} (check-sat)"), "proof": wire,
        }))
        .unwrap(),
    )
    .unwrap();
    println!(
        "independent projected quantifier certificate: {}",
        packet.display()
    );
}

#[test]
fn bounded_authored_canonical_render_exports_quantified_conjunctions() {
    for (label, body) in [("predicate", "(P x)"), ("comparison", "(> (f x) 0)")] {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        let input = format!(
            "(set-logic ALL) (declare-const p Bool) (declare-fun P (Int) Bool) \
             (declare-fun f (Int) Int) (assert (and p (forall ((x Int)) {body}))) \
             (assert (not p))"
        );
        executor
            .execute_all(&ay_frontend::parse(&input).unwrap())
            .unwrap();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let roots = executor.ctx.assertions.clone();
        let TermData::App(_, operands) = executor.ctx.terms.get(roots[0]) else {
            panic!("fixture keeps its conjunction");
        };
        let pivot = operands[0];
        let negated_source = executor.ctx.terms.mk_not_raw(roots[0]);
        let mut proof = Proof::new();
        let source = proof.add_assume(roots[0], None);
        let negative = proof.add_assume(roots[1], None);
        let projection = proof.add_rule_step(
            AletheRule::AndPos(0),
            vec![negated_source, pivot],
            vec![],
            vec![],
        );
        let positive = proof.add_resolution(vec![pivot], roots[0], source, projection);
        proof.add_resolution(vec![], pivot, positive, negative);
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .unwrap()
            .is_complete());
        assert!(executor.candidate_authored_surface_is_available(&proof));
        executor.restore_reachable_authored_assume_surface_overrides(&proof);
        assert!(!executor.last_unsat_proof_reconstruction_suppressed);
        let wire = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &executor.ctx.terms,
            &roots,
            executor.last_proof_term_overrides.as_ref(),
        )
        .unwrap();
        assert!(!wire.contains(":rule hole"));
        let packet = std::env::temp_dir().join(format!(
            "ay-authored-render-{label}-{}.json",
            std::process::id(),
        ));
        std::fs::write(
            &packet,
            serde_json::to_vec(&serde_json::json!({
                "type": "alethe_certificate", "version": "1.0",
                "problem": format!("{input} (check-sat)"), "proof": wire,
            }))
            .unwrap(),
        )
        .unwrap();
        println!(
            "independent authored rendering certificate: {}",
            packet.display()
        );
    }
}

#[test]
fn replacement_preflight_preserves_state_with_available_or_missing_source() {
    for (first, conjunction) in [
        ("p", false),
        ("(and p (forall ((x Int)) (> (f x) 0)))", true),
    ] {
        let mut executor = Executor::new();
        executor.set_produce_proofs(true);
        let input = format!(
            "(declare-const p Bool) (declare-fun f (Int) Int) (assert {first}) (assert (not p))"
        );
        executor
            .execute_all(&ay_frontend::parse(&input).unwrap())
            .unwrap();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        let roots = executor.ctx.assertions.clone();
        let mut proof = Proof::new();
        let source = proof.add_assume(roots[0], None);
        let negative = proof.add_assume(roots[1], None);
        let (positive, pivot) = if !conjunction {
            (source, roots[0])
        } else {
            let TermData::App(_, operands) = executor.ctx.terms.get(roots[0]) else {
                panic!("quantified fixture keeps its conjunction");
            };
            let pivot = operands[0];
            let negated_source = executor.ctx.terms.mk_not_raw(roots[0]);
            let projection = proof.add_rule_step(
                AletheRule::AndPos(0),
                vec![negated_source, pivot],
                vec![],
                vec![],
            );
            let positive = proof.add_resolution(vec![pivot], roots[0], source, projection);
            (positive, pivot)
        };
        proof.add_resolution(vec![], pivot, positive, negative);
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .unwrap()
            .is_complete());
        assert!(executor.candidate_authored_surface_is_available(&proof));
        assert!(!executor.last_unsat_proof_reconstruction_suppressed);
        assert!(executor.last_proof.is_none());
        assert_eq!(executor.ctx.assertions, roots);

        // Rendering a supported binder never grants missing source authority.
        executor.ctx.set_retain_parsed_assertions(false);
        assert!(!executor.candidate_authored_surface_is_available(&proof));
        assert!(!executor.last_unsat_proof_reconstruction_suppressed);
        assert!(executor.last_proof.is_none());
        assert_eq!(executor.ctx.assertions, roots);
    }
}
