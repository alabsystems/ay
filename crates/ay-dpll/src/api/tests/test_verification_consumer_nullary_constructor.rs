// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact native first query for the typed nullary-constructor composition.
//! Keep construction/assertion/scope order. The proof reconstructs the UF
//! branch contradiction from authored roots without datatype proof lemmas.

use crate::api::{
    DatatypeConstructor, DatatypeField, DatatypeSort, Logic, ProofAcceptanceMode, Solver, Sort,
};

#[test]
fn authored_native_nullary_constructor_first_query_is_strictly_certified() {
    let mut s = Solver::try_new(Logic::All).expect("native solver");
    s.set_produce_proofs(true);
    s.try_set_option(":check-proofs-strict", "true")
        .expect("strict policy");
    s.set_timeout(Some(std::time::Duration::from_secs(5)));
    let t0 = s.bool_const(true);
    let _t2 = s.declare_const("heap", Sort::array(Sort::Int, Sort::Int));
    let _t3 = s.declare_const("domain", Sort::array(Sort::Int, Sort::Int));
    let _t4 = s.declare_const("perms", Sort::array(Sort::Int, Sort::Int));
    let dt = DatatypeSort {
        name: "OptionInt".into(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".into(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".into(),
                fields: vec![DatatypeField {
                    name: "option_some_value".into(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    s.try_declare_datatype(&dt).unwrap();
    let f0 = s.declare_fun(
        "method_discriminant_1_d4f7074696f6e496e74",
        &[Sort::Datatype(dt.clone())],
        Sort::Int,
    );
    let t5 = s.try_datatype_constructor(&dt, "None", &[]).unwrap();
    let t6 = s.int_const(0);
    let t7 = s.apply(&f0, &[t5]);
    let t8 = s.try_eq_no_ite_expand(t6, t7).unwrap();
    s.assert_term(t8);
    let t9 = s.int_const(1);
    let t10 = s.declare_const(
        "__verification_consumer_source_var_v1_b_call_2",
        Sort::Uninterpreted("OptionInt".into()),
    );
    let t11 = s.declare_const(
        "__verification_consumer_source_var_v1_b_result",
        Sort::Uninterpreted("OptionInt".into()),
    );
    let t12 = s.declare_const("__verification_consumer_source_var_v1_b_empty", Sort::Bool);
    s.try_assert_named(t0, "__verification_consumer_precondition_0")
        .unwrap();
    let t13 = s.not(t12);
    let t14 = s.try_eq_no_ite_expand(t5, t10).unwrap();
    let t15 = s.or_many(&[t13, t14]);
    s.try_assert_named(t15, "__verification_consumer_precondition_1")
        .unwrap();
    s.try_assert_named(t12, "__verification_consumer_precondition_2")
        .unwrap();
    let t16 = s.apply(&f0, &[t10]);
    let t17 = s.declare_const("__uf_int_aux_0", Sort::Int);
    let t18 = s.try_eq_no_ite_expand(t16, t17).unwrap();
    s.assert_term(t18);
    let t19 = s.try_datatype_tester("None", t10).unwrap();
    let t20 = s.try_eq_no_ite_expand(t6, t17).unwrap();
    let t21 = s.not(t19);
    let t22 = s.or_many(&[t20, t21]);
    s.assert_term(t22);
    let t23 = s.try_datatype_tester("Some", t10).unwrap();
    let t24 = s.try_eq_no_ite_expand(t9, t17).unwrap();
    let t25 = s.not(t23);
    let t26 = s.or_many(&[t24, t25]);
    s.assert_term(t26);
    s.assert_term(t0);
    let t27 = s.not(t20);
    let t28 = s.try_eq_no_ite_expand(t5, t11).unwrap();
    let t29 = s.or_many(&[t27, t28]);
    s.assert_term(t29);
    s.assert_term(t0);
    s.assert_term(t0);
    let t30 = s.try_datatype_constructor(&dt, "Some", &[t9]).unwrap();
    let t31 = s.try_eq_no_ite_expand(t5, t30).unwrap();
    let t32 = s.not(t31);
    s.assert_term(t32);
    let t33 = s.try_eq_no_ite_expand(t11, t30).unwrap();
    let t34 = s.or_many(&[t20, t33]);
    s.assert_term(t34);
    let t35 = s.try_datatype_tester("None", t11).unwrap();
    let t36 = s.not(t35);
    let t37 = s.or_many(&[t20, t36]);
    s.assert_term(t37);
    let t38 = s.try_datatype_tester("Some", t11).unwrap();
    let t39 = s.not(t38);
    let t40 = s.or_many(&[t27, t39]);
    s.assert_term(t40);
    let t41 = s
        .try_datatype_selector("option_some_value", t11, Sort::Int)
        .unwrap();
    let t42 = s.try_eq_no_ite_expand(t9, t41).unwrap();
    let t43 = s.or_many(&[t39, t42]);
    s.assert_term(t43);
    let t44 = s.or_many(&[t13, t28]);
    s.assert_term(t44);
    s.push();
    s.push();
    s.assert_term(t27);

    let details = s.check_sat_with_details();
    assert!(details.result.is_unsat(), "{details:#?}");
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "{details:#?}"
    );
    let artifact = s.export_last_unsat_artifact().expect("first-query proof");
    artifact
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .expect("strict consumer authority");
    assert!(artifact.quality.is_complete());
    assert!(
        !artifact.alethe.contains(":rule hole"),
        "{}",
        artifact.alethe
    );
    assert!(artifact.alethe.contains(":rule or"), "{}", artifact.alethe);
    assert!(
        artifact.alethe.contains(":rule eq_transitive"),
        "{}",
        artifact.alethe
    );
}
