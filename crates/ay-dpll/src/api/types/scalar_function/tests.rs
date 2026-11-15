// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn retained_models_preserve_complete_source_order_and_canonical_roundtrip() {
    let byte = Sort::bitvec(8);
    let wide = Sort::bitvec(136);
    let args = [Sort::Bool, byte.clone()];
    let expected = [
        ("f", args.as_slice(), &byte),
        ("unused wide", &[][..], &wide),
    ];
    let text = "(model
      (define-fun |unused wide| () (_ BitVec 136) (_ bv1 136))
      (define-fun f ((flag Bool) (x (_ BitVec 8))) (_ BitVec 8)
        (let ((saved x)) (ite flag saved (bvadd saved #x01)))))";
    let models = ScalarFunctionModel::decode_smtlib(text, &expected).expect("complete data");
    assert_eq!(models.len(), 2);
    assert_eq!(models[0].name(), "f");
    assert_eq!(models[0].arg_sorts(), args);
    assert_eq!(models[0].result_sort(), &byte);
    assert_eq!(models[1].name(), "unused wide");
    assert_eq!(models[1].result_sort(), &wide);
    assert!(models[1].arg_sorts().is_empty());
    let canonical = format!(
        "(model {})",
        models
            .iter()
            .map(ScalarFunctionModel::definition_smtlib)
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert_eq!(
        ScalarFunctionModel::decode_smtlib(&canonical, &expected).expect("canonical roundtrip"),
        models
    );
    assert!(ay_frontend::parse(models[0].definition_smtlib()).is_ok());
}

#[test]
fn retained_inventory_is_exact_even_for_unused_and_empty_source_declarations() {
    let byte = Sort::bitvec(8);
    let expected = [("f", &[][..], &byte)];
    let complete = "(model (define-fun f () (_ BitVec 8) #x00))";
    assert!(ScalarFunctionModel::decode_smtlib(complete, &expected).is_ok());
    for text in [
        "(model)",
        "(model (define-fun other () (_ BitVec 8) #x00))",
        "(model (define-fun f () (_ BitVec 8) #x00) (define-fun other () (_ BitVec 8) #x01))",
        "(model (define-fun f () (_ BitVec 8) #x00) (define-fun f () (_ BitVec 8) #x00))",
        "(model (define-fun f () (_ BitVec 8) #x00)) (check-sat)",
        "(model (define-fun f () (_ BitVec 8) #x00) (assert true))",
        "(define-fun f () (_ BitVec 8) #x00)",
    ] {
        assert_eq!(
            ScalarFunctionModel::decode_smtlib(text, &expected),
            Err(ScalarFunctionModelDecodeError),
            "{text}"
        );
    }
    assert!(ScalarFunctionModel::decode_smtlib(complete, &[]).is_err());
    assert!(ScalarFunctionModel::decode_smtlib("(model)", &[])
        .expect("empty exact inventory")
        .is_empty());
    assert!(ScalarFunctionModel::decode_smtlib(
        complete,
        &[("f", &[][..], &byte), ("unused", &[][..], &byte)]
    )
    .is_err());
}

#[test]
fn exact_ingress_does_not_change_native_whole_model_subset_extraction() {
    let byte = Sort::bitvec(8);
    let expected = [("f", &[][..], &byte)];
    let text = "(model (define-fun f () (_ BitVec 8) #x00)
      (define-fun unrelated () Bool true))";
    let native = crate::api::model_parse::parse_scalar_function_models(text, &expected)
        .expect("native getter may select source functions from the complete model");
    assert_eq!(native.len(), 1);
    assert_eq!(native[0].name(), "f");
    assert!(ScalarFunctionModel::decode_smtlib(text, &expected).is_err());
}

#[test]
fn retained_bodies_cannot_hide_open_or_ill_typed_unused_branches() {
    let byte = Sort::bitvec(8);
    let args = [byte.clone()];
    let expected = [("f", args.as_slice(), &byte)];
    for body in [
        "free_global",
        "(g x)",
        "(f x)",
        "(ite true x free_global)",
        "(ite true x false)",
        "(ite true x #x0000)",
        "(let ((y x) (z y)) z)",
        "((_ extract 8 0) x)",
        "(select x #x00)",
    ] {
        let text = format!("(model (define-fun f ((x (_ BitVec 8))) (_ BitVec 8) {body}))");
        assert!(
            ScalarFunctionModel::decode_smtlib(&text, &expected).is_err(),
            "{body}"
        );
    }
    let input = "(model (define-fun f ((x (_ BitVec 8))) (_ BitVec 8)
      (let ((y x)) (let ((z y)) z))))";
    assert!(ScalarFunctionModel::decode_smtlib(input, &expected).is_ok());
}

#[test]
fn retained_signature_inventory_is_caller_bound_and_fully_validated() {
    let byte = Sort::bitvec(8);
    let text = "(model (define-fun f ((flag Bool) (x (_ BitVec 8))) (_ BitVec 8) x))";
    let good = [Sort::Bool, byte.clone()];
    assert!(ScalarFunctionModel::decode_smtlib(text, &[("f", &good, &byte)]).is_ok());
    for args in [
        vec![],
        vec![byte.clone(), Sort::Bool],
        vec![Sort::Bool, Sort::bitvec(9)],
        vec![Sort::Bool, byte.clone(), Sort::Bool],
        vec![Sort::array(byte.clone(), byte.clone())],
    ] {
        assert!(ScalarFunctionModel::decode_smtlib(text, &[("f", &args, &byte)]).is_err());
    }
    for result in [Sort::Bool, Sort::bitvec(0), Sort::bitvec(9), Sort::Int] {
        assert!(ScalarFunctionModel::decode_smtlib(text, &[("f", &good, &result)]).is_err());
    }
    assert!(
        ScalarFunctionModel::decode_smtlib(text, &[("f", &good, &byte), ("f", &good, &byte)])
            .is_err()
    );
}

#[test]
fn public_retained_data_refusal_is_bounded_atomic_and_retryable() {
    let byte = Sort::bitvec(8);
    let expected = [("f", &[][..], &byte)];
    let body = format!("{}#x00{}", "(ite true #x00 ".repeat(130), ")".repeat(130));
    let text = format!("(model (define-fun f () (_ BitVec 8) {body}))");
    assert!(ScalarFunctionModel::decode_smtlib(&text, &expected).is_err());
    let text = format!("(model);{}", "x".repeat(8 * 1024 * 1024));
    assert!(ScalarFunctionModel::decode_smtlib(&text, &[]).is_err());
    let oversized = vec![("f", &[][..], &byte); 1025];
    assert!(ScalarFunctionModel::decode_smtlib("(model)", &oversized).is_err());
    assert!(ScalarFunctionModel::decode_smtlib(
        "(model (define-fun f () (_ BitVec 8) #x00))",
        &expected
    )
    .is_ok());
}
