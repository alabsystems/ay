// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[cfg(test)]
fn ground_substitution_wire_fixture(integer_shift: bool) -> (Executor, TermId) {
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    let x = exec.ctx.terms.mk_var("ground_x", Sort::Int);
    let y = exec.ctx.terms.mk_var("ground_y", Sort::Int);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    let pin = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [x, one], Sort::Bool);
    let source = exec
        .ctx
        .terms
        .mk_app(Symbol::named("<"), [y, x], Sort::Bool);
    let target = if integer_shift {
        exec.ctx
            .terms
            .mk_app(Symbol::named("<="), [y, zero], Sort::Bool)
    } else {
        exec.ctx
            .terms
            .mk_app(Symbol::named("<"), [y, one], Sort::Bool)
    };
    let negative_pin = exec.ctx.terms.mk_not_raw(pin);
    let negative_source = exec.ctx.terms.mk_not_raw(source);
    let negative_target = exec.ctx.terms.mk_not_raw(target);
    let mut proof = Proof::new();
    let a = proof.add_assume(pin, None);
    let b = proof.add_assume(source, None);
    let c = proof.add_assume(negative_target, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "uf",
        vec![negative_pin, negative_source, target],
        TheoryLemmaKind::GroundEqualitySubstitution,
    );
    let conditional = proof.add_resolution(vec![negative_source, target], pin, a, lemma);
    let result = proof.add_resolution(vec![target], source, b, conditional);
    proof.add_resolution(vec![], target, result, c);
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms).unwrap();
    exec.last_proof = Some(proof);
    (exec, x)
}

#[test]
fn ground_substitution_wire_gate_matches_exact_renderer_and_surface() {
    let (mut exec, x) = ground_substitution_wire_fixture(false);
    assert!(!exec.unsat_proof_has_known_wire_gap());
    let text = export_executor_proof(&exec);
    assert!(text.contains(":rule subproof") && !text.contains(":rule hole"));
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(x, "ground_y".to_owned());
    exec.last_proof_term_overrides = Some(overrides);
    assert!(exec.unsat_proof_has_known_wire_gap());
    assert!(ground_substitution_wire_fixture(true)
        .0
        .unsat_proof_has_known_wire_gap());
}

#[test]
fn ground_substitution_wire_gate_shares_work_across_all_lemmas() {
    let (mut exec, _) = ground_substitution_wire_fixture(false);
    let proof = exec.last_proof.as_mut().unwrap();
    let lemma = proof.steps[3].clone();
    for _ in 0..48 {
        proof.add_step(lemma.clone());
    }
    assert!(exec.unsat_proof_has_known_wire_gap());
}
