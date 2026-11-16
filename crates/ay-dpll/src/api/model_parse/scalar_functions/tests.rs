// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::unwrap_used)]

use super::*;

mod resources;
mod retained;
mod semantics;

fn bv(width: u32) -> Sort {
    Sort::bitvec(width)
}

fn one(body: &str, parameters: &str, args: &[Sort], width: u32) -> Option<ScalarFunctionModel> {
    let output = format!("(model (define-fun f ({parameters}) (_ BitVec {width}) {body}))");
    parse_scalar_function_models(&output, &[("f", args, &bv(width))])?.pop()
}

#[test]
fn full_inventory_preserves_request_order_and_unused_nullary_functions() {
    let output = "(model
      (define-fun unused ((irrelevant Bool)) (_ BitVec 8) #x01)
      (define-fun |function with space| () (_ BitVec 136) (_ bv1 136))
      (define-fun f ((input (_ BitVec 8))) (_ BitVec 8) input))";
    let args = [bv(8)];
    let bools = [Sort::Bool];
    let result = bv(8);
    let wide = bv(136);
    let expected = [
        ("f", args.as_slice(), &result),
        ("function with space", &[][..], &wide),
        ("unused", bools.as_slice(), &result),
    ];
    let models = parse_scalar_function_models(output, &expected).unwrap();
    assert_eq!(
        models
            .iter()
            .map(ScalarFunctionModel::name)
            .collect::<Vec<_>>(),
        ["f", "function with space", "unused"]
    );
    assert_eq!(models[0].arg_sorts(), args);
    assert_eq!(models[0].result_sort(), &result);
    assert_eq!(
        models[0].definition_smtlib(),
        "(define-fun f ((ay_uf_v0 (_ BitVec 8))) (_ BitVec 8) ay_uf_v0)"
    );
    assert_eq!(
        models[1].definition_smtlib(),
        format!(
            "(define-fun |function with space| () (_ BitVec 136) #x{:0>34})",
            "1"
        )
    );
    assert!(!models[2].definition_smtlib().ends_with('\n'));
    // Full closed definitions can be parsed without any original UF bindings.
    let definitions = models
        .iter()
        .map(ScalarFunctionModel::definition_smtlib)
        .collect::<Vec<_>>()
        .join("\n");
    ay_frontend::parse(&definitions).unwrap();
}

#[test]
fn malformed_or_incomplete_model_envelopes_never_return_a_prefix() {
    let sort = bv(8);
    let expected = [("f", &[][..], &sort), ("unused", &[][..], &sort)];
    for output in [
        "", "sat", "(error \"missing\")", "(model)",
        "(model (define-fun f () (_ BitVec 8) #x01))",
        "(model (define-fun f () (_ BitVec 8) #x01) (define-fun f () (_ BitVec 8) #x01) (define-fun unused () (_ BitVec 8) #x00))",
        "(model (define-fun f () (_ BitVec 8) #x01) (define-fun unused () (_ BitVec 8) #x00) (assert true))",
        "(model (define-fun f () (_ BitVec 8) #x01) (define-fun unused () (_ BitVec 8) #x00)) (model)",
    ] { assert!(parse_scalar_function_models(output, &expected).is_none(), "{output}"); }
    let output = "(model (define-fun f () (_ BitVec 8) #x00))";
    assert!(
        parse_scalar_function_models(output, &[("f", &[], &sort), ("f", &[], &sort)]).is_none()
    );
    assert_eq!(
        parse_scalar_function_models("(model)", &[]).unwrap(),
        [] as [ScalarFunctionModel; 0]
    );
}

#[test]
fn signatures_and_every_recorded_parameter_are_exact() {
    let args = [Sort::Bool, bv(8)];
    assert!(one("x", "(flag Bool) (x (_ BitVec 8))", &args, 8).is_some());
    for parameters in [
        "",
        "(flag Bool)",
        "(flag Bool) (x (_ BitVec 9))",
        "(flag (_ BitVec 1)) (x (_ BitVec 8))",
        "(x Bool) (x (_ BitVec 8))",
        "(flag Bool) (x (_ BitVec 8)) (unused Bool)",
    ] {
        assert!(one("#x00", parameters, &args, 8).is_none(), "{parameters}");
    }
    assert!(one("#x00", "", &[], 9).is_none());
    assert!(parse_scalar_function_models(
        "(model (define-fun f () Bool true))",
        &[("f", &[], &Sort::Bool)]
    )
    .is_none());
    assert!(parse_scalar_function_models(
        "(model)",
        &[("f", &[Sort::array(bv(8), bv(8))], &bv(8))]
    )
    .is_none());
    assert!(parse_scalar_function_models("(model)", &[("f", &[], &bv(0))]).is_none());
    assert!(parse_scalar_function_models(
        "(model)",
        &[("f", &[], &bv(crate::api::MAX_API_BITVECTOR_WIDTH + 1))]
    )
    .is_none());
}

#[test]
fn all_branches_and_aliases_must_be_closed_and_scalar() {
    for body in [
        "missing",
        "(f #x00)",
        "(g #x00)",
        "(as #x00 (_ BitVec 8))",
        "(ite true #x00 missing)",
        "(ite true #x00 false)",
        "(let ((x #x00) (x #x01)) x)",
        "(let ((x #x00) (y x)) y)",
        "(let ((unused unknown)) #x00)",
        "(let () #x00)",
        "(forall ((i (_ BitVec 8))) #x00)",
        "(select unknown #x00)",
        "(! #x00 :named a)",
        "(bvadd #x00 #x00 #x00)",
    ] {
        assert!(one(body, "", &[], 8).is_none(), "{body}");
    }
    let output = "(model (define-fun constant () (_ BitVec 8) #x01) (define-fun f () (_ BitVec 8) constant))";
    assert!(parse_scalar_function_models(output, &[("f", &[], &bv(8))]).is_none());
}

#[test]
fn literal_width_range_and_sign_are_never_repaired() {
    for body in [
        "(_ bv256 8)",
        "(_ bv-1 8)",
        "(- (_ bv1 8))",
        "#b1",
        "#x0000",
        "(_ bv1 9)",
        "(_ bv1 0)",
        "1",
        "-1",
    ] {
        assert!(one(body, "", &[], 8).is_none(), "{body}");
    }
    assert_eq!(
        one("(_ bv255 8)", "", &[], 8).unwrap().definition_smtlib(),
        "(define-fun f () (_ BitVec 8) #xff)"
    );
    let high = format!("#x8{}", "0".repeat(33));
    assert!(one(&high, "", &[], 136)
        .unwrap()
        .definition_smtlib()
        .ends_with(&format!("{high})")));
    assert!(one("x", "(x (_ BitVec 136))", &[bv(136)], 136).is_some());
}

#[test]
fn standard_bv_operations_and_indexed_result_widths_are_authenticated() {
    let parameters = "(x (_ BitVec 8)) (y (_ BitVec 8))";
    let args = [bv(8), bv(8)];
    for operator in [
        "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvand",
        "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvshl", "bvlshr", "bvashr",
    ] {
        assert!(one(&format!("({operator} x y)"), parameters, &args, 8).is_some());
    }
    for body in [
        "(ite (bvult x y) x y)",
        "(ite (and (= x y) (not false)) x y)",
        "((_ rotate_left 9) x)",
        "((_ extract 7 0) x)",
    ] {
        assert!(one(body, parameters, &args, 8).is_some(), "{body}");
    }
    assert!(one("((_ zero_extend 128) x)", "(x (_ BitVec 8))", &[bv(8)], 136).is_some());
    assert!(one("(concat x y)", parameters, &args, 16).is_some());
    assert!(one("((_ repeat 2) x)", parameters, &args, 16).is_some());
    for body in [
        "((_ extract 8 0) x)",
        "((_ extract 1 2) x)",
        "((_ repeat 0) x)",
        "((_ zero_extend 1048576) x)",
        "(ite x x y)",
        "(bvadd x true)",
        "(bvadd x #b1)",
        "(and x y)",
        "(= x y x)",
        "((_ unsupported 1) x)",
    ] {
        assert!(one(body, parameters, &args, 8).is_none(), "{body}");
    }
}

#[test]
fn lexical_names_cannot_launder_builtin_heads_or_hostile_symbols() {
    for name in ["and", "bvadd", "let", "forall", "Bool", "a|b", "a\\b"] {
        let text = format!("(model (define-fun |{name}| () (_ BitVec 8) #x00))");
        assert!(parse_scalar_function_models(&text, &[(name, &[], &bv(8))]).is_none());
    }
    assert!(one("|and|", "(|and| (_ BitVec 8))", &[bv(8)], 8).is_none());
    assert!(one("(let ((|bvadd| #x00)) |bvadd|)", "", &[], 8).is_none());
    assert!(one("(|ite| true #x00 #x01)", "", &[], 8).is_none());
    assert!(one("(|let| ((x #x00)) x)", "", &[], 8).is_none());
    assert!(one("(_ |bv1| 8)", "", &[], 8).is_none());
    // Generated slots may coincide with an input spelling without capturing it.
    let value = one("(let ((ay_uf_v0 #x01)) x)", "(x (_ BitVec 8))", &[bv(8)], 8).unwrap();
    assert!(value
        .definition_smtlib()
        .contains("(let ((ay_uf_v1 #x01)) ay_uf_v0)"));
}
