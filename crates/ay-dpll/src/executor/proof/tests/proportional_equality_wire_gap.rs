// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

fn proportional_screen_fixture(
    exec: &mut Executor,
    target: i64,
    kind: TheoryLemmaKind,
) -> (Proof, Vec<TermId>) {
    let t = &mut exec.ctx.terms;
    let x = t.mk_var("screen_proportional_x", Sort::Int);
    let two = t.mk_int(2.into());
    let lhs = t.mk_app_structural(Symbol::named("*"), [x, two], Sort::Int);
    let n42 = t.mk_int(42.into());
    let p = t.mk_app_structural(Symbol::named("="), [lhs, n42], Sort::Bool);
    let target = t.mk_int(target.into());
    let q = t.mk_app_structural(Symbol::named("="), [x, target], Sort::Bool);
    let not_p = t.mk_not_raw(p);
    let not_q = t.mk_not_raw(q);
    let scope = vec![p, not_q];
    add_authored_roots(exec, &scope);
    let mut proof = Proof::new();
    let a = proof.add_assume(p, None);
    let b = proof.add_assume(not_q, None);
    let lemma = proof.add_theory_lemma_with_kind("arith", vec![not_p, q], kind);
    let q_step = proof.add_resolution(vec![q], p, lemma, a);
    proof.add_resolution(Vec::new(), q, q_step, b);
    (proof, scope)
}

#[test]
fn proportional_equality_wire_screen_uses_the_same_checked_lowering() {
    let mut exec = Executor::new();
    let (proof, scope) =
        proportional_screen_fixture(&mut exec, 21, TheoryLemmaKind::ArithClauseTautology);
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let wire = arith_chain_wire(&exec, &proof, &scope);
    assert!(!wire.contains(":rule hole"), "{wire}");
    assert!(wire.contains(":rule la_disequality"), "{wire}");
    assert!(!exec.proof_has_known_wire_gap(&proof));
}

#[test]
fn proportional_equality_wire_screen_refuses_forged_targets_and_generic_credit() {
    for (target, kind) in [
        (22, TheoryLemmaKind::ArithClauseTautology),
        (21, TheoryLemmaKind::Generic),
    ] {
        let mut exec = Executor::new();
        let (proof, scope) = proportional_screen_fixture(&mut exec, target, kind);
        let checked = exec.check_proof_strict_with_datatypes(&proof);
        if target == 22 {
            assert!(
                checked.is_err(),
                "forged target must not pass native checking"
            );
        } else {
            // The existing equality-span checker independently validates this
            // true clause. A Generic label still licenses no checked lowering
            // through the narrower arithmetic exporter added here.
            let quality = checked.expect("true Generic equality-span clause is natively checked");
            assert_eq!(
                quality.trust_count, 1,
                "the producer tag still counts as trust"
            );
            assert!(
                !quality.is_complete(),
                "native validity is not complete wire credit"
            );
        }
        assert!(exec.proof_has_known_wire_gap(&proof));
        assert!(arith_chain_wire(&exec, &proof, &scope).contains(":rule hole"));
    }
}
