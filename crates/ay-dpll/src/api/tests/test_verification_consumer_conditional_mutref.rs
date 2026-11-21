// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The first native query for verification-consumer's conditional mutable-reference return.
//! Preserve declaration, term construction, assertion and scope order: an SMT
//! frontend reparse, or a second solve, avoids the original arithmetic-labelled
//! congruence leaves and would hide this exporter gap.

use crate::api::{Logic, ProofAcceptanceMode, Solver, Sort};

fn conditional_mutref_query() -> Solver {
    let mut s = Solver::try_new(Logic::Uflia).expect("native solver");
    s.set_produce_proofs(true);
    s.try_set_option(":check-proofs-strict", "true")
        .expect("strict policy");
    s.set_timeout(Some(std::time::Duration::from_secs(5)));
    let t3 = s.declare_const(
        "__verification_consumer_source_var_v1_b_ma",
        Sort::Uninterpreted("__verification_consumer_mutref::int".into()),
    );
    let t4 = s.declare_const(
        "__verification_consumer_source_var_v1_b_mb",
        Sort::Uninterpreted("__verification_consumer_mutref::int".into()),
    );
    let t5 = s.declare_const(
        "__verification_consumer_source_var_v1_b_result",
        Sort::Uninterpreted("__verification_consumer_mutref::int".into()),
    );
    let t6 = s.declare_const(
        "__verification_consumer_source_var_v1_b_ma_current",
        Sort::Int,
    );
    let t7 = s.declare_const(
        "__verification_consumer_source_var_v1_b_mb_current",
        Sort::Int,
    );
    let t9 = s.declare_const(
        "__verification_consumer_source_var_v1_b_mb_final",
        Sort::Int,
    );
    let t10 = s.try_eq_no_ite_expand(t7, t9).unwrap();
    let t8 = s.le(t7, t6);
    let t11 = s.not(t8);
    let t12 = s.or_many(&[t10, t11]);
    s.try_assert_named(t12, "__verification_consumer_precondition_0")
        .unwrap();
    let t13 = s.declare_const(
        "__verification_consumer_source_var_v1_b_ma_final",
        Sort::Int,
    );
    let t14 = s.try_eq_no_ite_expand(t6, t13).unwrap();
    let t15 = s.or_many(&[t8, t14]);
    s.try_assert_named(t15, "__verification_consumer_precondition_1")
        .unwrap();
    let t17 = s.try_eq_no_ite_expand(t3, t5).unwrap();
    let t18 = s.try_eq_no_ite_expand(t4, t5).unwrap();
    let t19 = s.ite(t8, t17, t18);
    s.assert_term(t19);
    let t20 = s.declare_const("__verification_consumer_num_coerce_0", Sort::Int);
    let t21 = s.declare_const("__verification_consumer_num_coerce_1", Sort::Int);
    let t23 = s.declare_const(
        "__verification_consumer_source_var_v1_b_result_current",
        Sort::Int,
    );
    let t22 = s.le(t21, t20);
    let t25 = s.try_eq_no_ite_expand(t6, t23).unwrap();
    let t26 = s.try_eq_no_ite_expand(t7, t23).unwrap();
    let t27 = s.ite(t22, t25, t26);
    s.assert_term(t27);
    let t28 = s.declare_const(
        "__verification_consumer_source_var_v1_b_result_final",
        Sort::Int,
    );
    let t30 = s.try_eq_no_ite_expand(t13, t28).unwrap();
    let t31 = s.try_eq_no_ite_expand(t9, t28).unwrap();
    let t32 = s.ite(t22, t30, t31);
    s.assert_term(t32);
    let t33 = s.declare_const("__verification_consumer_source_var_v1_b_ma_id", Sort::Int);
    let t34 = s.declare_const("__verification_consumer_source_var_v1_b_mb_id", Sort::Int);
    let t35 = s.declare_const(
        "__verification_consumer_source_var_v1_b_result_id",
        Sort::Int,
    );
    let t37 = s.try_eq_no_ite_expand(t33, t35).unwrap();
    let t38 = s.try_eq_no_ite_expand(t34, t35).unwrap();
    let t39 = s.ite(t22, t37, t38);
    s.assert_term(t39);
    let f0 = s.declare_fun(
        "__verification_consumer_mk_mut_ref_3876140fd76a6650",
        &[Sort::Int, Sort::Int, Sort::Int],
        Sort::Uninterpreted("__verification_consumer_mutref::int".into()),
    );
    let f1 = s.declare_fun(
        "__verification_consumer_mut_ref_current_3876140fd76a6650",
        &[Sort::Uninterpreted(
            "__verification_consumer_mutref::int".into(),
        )],
        Sort::Int,
    );
    let f2 = s.declare_fun(
        "__verification_consumer_mut_ref_final_3876140fd76a6650",
        &[Sort::Uninterpreted(
            "__verification_consumer_mutref::int".into(),
        )],
        Sort::Int,
    );
    let f3 = s.declare_fun(
        "__verification_consumer_mut_ref_id_3876140fd76a6650",
        &[Sort::Uninterpreted(
            "__verification_consumer_mutref::int".into(),
        )],
        Sort::Int,
    );
    let t40 = s.apply(&f0, &[t23, t28, t35]);
    let t41 = s.try_eq_no_ite_expand(t5, t40).unwrap();
    s.assert_term(t41);
    let t42 = s.apply(&f1, &[t5]);
    let t43 = s.try_eq_no_ite_expand(t23, t42).unwrap();
    s.assert_term(t43);
    let t44 = s.apply(&f2, &[t5]);
    let t45 = s.try_eq_no_ite_expand(t28, t44).unwrap();
    s.assert_term(t45);
    let t46 = s.apply(&f3, &[t5]);
    let t47 = s.try_eq_no_ite_expand(t35, t46).unwrap();
    s.assert_term(t47);
    s.push();
    s.assert_term(t41);
    s.assert_term(t43);
    s.assert_term(t45);
    s.assert_term(t47);
    let t48 = s.apply(&f0, &[t6, t13, t33]);
    let t49 = s.try_eq_no_ite_expand(t3, t48).unwrap();
    s.assert_term(t49);
    let t50 = s.apply(&f1, &[t3]);
    let t51 = s.try_eq_no_ite_expand(t6, t50).unwrap();
    s.assert_term(t51);
    let t52 = s.apply(&f2, &[t3]);
    let t53 = s.try_eq_no_ite_expand(t13, t52).unwrap();
    s.assert_term(t53);
    let t54 = s.apply(&f3, &[t3]);
    let t55 = s.try_eq_no_ite_expand(t33, t54).unwrap();
    s.assert_term(t55);
    s.assert_term(t41);
    s.assert_term(t43);
    s.assert_term(t45);
    s.assert_term(t47);
    let t62 = s.apply(&f0, &[t7, t9, t34]);
    let t63 = s.try_eq_no_ite_expand(t4, t62).unwrap();
    s.assert_term(t63);
    let t64 = s.apply(&f1, &[t4]);
    let t65 = s.try_eq_no_ite_expand(t7, t64).unwrap();
    s.assert_term(t65);
    let t66 = s.apply(&f2, &[t4]);
    let t67 = s.try_eq_no_ite_expand(t9, t66).unwrap();
    s.assert_term(t67);
    let t68 = s.apply(&f3, &[t4]);
    let t69 = s.try_eq_no_ite_expand(t34, t68).unwrap();
    s.assert_term(t69);
    s.push();
    let t79 = s.not(t10);
    let t56 = s.try_eq_no_ite_expand(t42, t50).unwrap();
    let t80 = s.not(t56);
    let t57 = s.try_eq_no_ite_expand(t44, t52).unwrap();
    let t81 = s.not(t57);
    let t58 = s.try_eq_no_ite_expand(t46, t54).unwrap();
    let t82 = s.not(t58);
    let t83 = s.or_many(&[t79, t80, t81, t82]);
    let t84 = s.and_many(&[t8, t83]);
    let t85 = s.not(t14);
    let t70 = s.try_eq_no_ite_expand(t42, t64).unwrap();
    let t86 = s.not(t70);
    let t71 = s.try_eq_no_ite_expand(t44, t66).unwrap();
    let t87 = s.not(t71);
    let t72 = s.try_eq_no_ite_expand(t46, t68).unwrap();
    let t88 = s.not(t72);
    let t89 = s.or_many(&[t85, t86, t87, t88]);
    let t90 = s.and_many(&[t11, t89]);
    let t91 = s.or_many(&[t84, t90]);
    s.assert_term(t91);
    s
}

#[test]
fn conditional_mutref_first_query_has_checked_unary_congruence_wire() {
    let mut solver = conditional_mutref_query();
    // Mandatory first solve: a repeated solve changes the produced proof.
    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:#?}");
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "{details:#?}"
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("retained first-query artifact");
    artifact
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .expect("strict consumer authority");
    assert!(artifact.quality.is_complete(), "{}", artifact.quality);
    assert!(
        !artifact.alethe.contains(":rule hole"),
        "{}",
        artifact.alethe
    );
    assert!(
        artifact.alethe.contains(":rule eq_congruent"),
        "{}",
        artifact.alethe
    );
    let proof = solver.last_proof().expect("first proof retained");
    assert!(proof.steps.iter().any(|step| {
        matches!(step, ay_core::ProofStep::TheoryLemma {kind: ay_core::TheoryLemmaKind::LiaGeneric, clause, ..}
            if ay_proof::checked_unary_congruence_lowering_supported(solver.terms(), &ay_core::TheoryLemmaKind::LiaGeneric, clause, None))
    }), "first-query producer must exercise the independently reconstructed lowering");
}

#[test]
fn conditional_mutref_unrelated_function_twin_stays_satisfiable() {
    let mut solver = Solver::try_new(Logic::Uflia).expect("native solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict policy");
    let sort = Sort::Uninterpreted("Ref".into());
    let a = solver.declare_const("a", sort.clone());
    let b = solver.declare_const("b", sort.clone());
    let f = solver.declare_fun("f", std::slice::from_ref(&sort), Sort::Int);
    let g = solver.declare_fun("g", std::slice::from_ref(&sort), Sort::Int);
    let guard = solver.eq(a, b);
    solver.assert_term(guard);
    let fa = solver.apply(&f, &[a]);
    let gb = solver.apply(&g, &[b]);
    let goal = solver.eq(fa, gb);
    let negative = solver.not(goal);
    solver.assert_term(negative);
    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat(), "{details:#?}");
    assert!(details.verification.sat_model_validated, "{details:#?}");
}
