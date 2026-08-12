// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::expr::eval_array_select;
use crate::{ChcDtConstructor, ChcDtSelector, ChcSort, ChcVar};
use std::sync::Arc;

/// Test helper: call term_body_to_smt_value with empty DT ctor set.
fn tv(term: &ay_frontend::Term) -> Option<SmtValue> {
    term_body_to_smt_value(term, &FxHashSet::default())
}

/// Test helper: call parse_model_into with empty DT ctor set.
fn pm(model: &mut FxHashMap<String, SmtValue>, s: &str) {
    parse_model_into(model, s, &FxHashSet::default());
}

/// Verify that `quote_symbol` (now delegating to `ay_core::quote_symbol`)
/// correctly quotes reserved words like "true", "false", "let", "assert".
#[test]
fn test_quote_symbol_matches_ay_core_on_reserved_words() {
    let reserved = ["true", "false", "let", "forall", "exists", "assert"];
    for name in &reserved {
        let local = quote_symbol(name);
        let core = ay_core::quote_symbol(name);
        assert_eq!(
            local, core,
            "quote_symbol should match ay_core for reserved word '{name}'"
        );
        // Reserved words must be pipe-quoted.
        assert!(
            local.starts_with('|') && local.ends_with('|'),
            "reserved word '{name}' should be pipe-quoted: got {local:?}"
        );
    }
}

/// Verify that `quote_symbol` (delegating to `ay_core::quote_symbol`) renders
/// pipe- and backslash-containing names LOSSLESSLY.
///
/// This used to pin `"|a_b|"` — substitution — which CONFLATES distinct user
/// symbols: `a|b` and `a_b` both become `a_b`, so two different predicates
/// print as one. `ay_core` switched to escaping, which AY's own reader accepts
/// (verified round-trip) and which Z3 accepts; the test was not updated with
/// it and pinned the abandoned contract.
///
/// What matters here is the property, not the spelling: the rendering must be
/// pipe-quoted and INJECTIVE, so assert that distinct names stay distinct
/// rather than re-hardcoding one expected string.
#[test]
fn test_quote_symbol_matches_ay_core_on_pipe_chars() {
    for name in ["a|b", "a\\b", "a\\|b"] {
        assert_eq!(
            quote_symbol(name),
            ay_core::quote_symbol(name),
            "quote_symbol should delegate to ay_core for {name:?}"
        );
        let quoted = quote_symbol(name);
        assert!(
            quoted.starts_with('|') && quoted.ends_with('|'),
            "{name:?} needs quoting: got {quoted:?}"
        );
    }
    // Injectivity is the load-bearing property: the previous underscore
    // substitution collapsed these two onto the same rendering.
    assert_ne!(
        quote_symbol("a|b"),
        quote_symbol("a_b"),
        "distinct symbols must not render identically"
    );
    assert_ne!(
        quote_symbol("a|b"),
        quote_symbol("a\\b"),
        "distinct symbols must not render identically"
    );
}

/// Verify BV operations produce correct SMT-LIB names.
/// Previously (#6047 W3:1873), the wildcard arm used `{op:?}` which
/// produced Rust enum variant names (BvAdd) instead of SMT-LIB (bvadd).
#[test]
fn test_bv_op_serialization_produces_correct_smtlib() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let y = ChcVar::new("y", ChcSort::BitVec(8));
    let bvadd = ChcExpr::Op(
        crate::ChcOp::BvAdd,
        vec![ChcExpr::var(x).into(), ChcExpr::var(y).into()],
    );
    let smtlib = InvariantModel::expr_to_smtlib(&bvadd);
    assert_eq!(smtlib, "(bvadd x y)");
}

/// Verify indexed BV operations produce correct `(_ op params)` syntax.
/// Previously used Debug format producing `(BvExtract(7, 0) x)`.
#[test]
fn test_bv_indexed_op_serialization_produces_correct_smtlib() {
    let x = ChcVar::new("x", ChcSort::BitVec(16));
    let extract = ChcExpr::Op(crate::ChcOp::BvExtract(7, 0), vec![ChcExpr::var(x).into()]);
    let smtlib = InvariantModel::expr_to_smtlib(&extract);
    assert_eq!(smtlib, "((_ extract 7 0) x)");
}

// ========================================================================
// detect_logic tests — covers all 7 match arms
// ========================================================================

#[test]
fn test_detect_logic_array_bv() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8))),
        ),
        ChcVar::new("x", ChcSort::BitVec(32)),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFBV");
}

#[test]
fn test_detect_logic_array_int_real() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        ),
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("r", ChcSort::Real),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLIRA");
}

#[test]
fn test_detect_logic_array_real_only() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::Real), Box::new(ChcSort::Real)),
        ),
        ChcVar::new("r", ChcSort::Real),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLRA");
}

#[test]
fn test_detect_logic_array_int_only() {
    let vars = vec![
        ChcVar::new(
            "a",
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        ),
        ChcVar::new("x", ChcSort::Int),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLIA");
}

#[test]
fn test_detect_logic_array_only_bool() {
    // Array with Bool indices and values — no Int, Real, or BV vars.
    let vars = vec![ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Bool), Box::new(ChcSort::Bool)),
    )];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AX");
}

#[test]
fn test_detect_logic_bv_no_array() {
    let vars = vec![
        ChcVar::new("x", ChcSort::BitVec(32)),
        ChcVar::new("y", ChcSort::BitVec(32)),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_UFBV");
}

#[test]
fn test_detect_logic_array_bv_mixed_with_int_uses_content_routing() {
    let vars = vec![
        ChcVar::new(
            "heap",
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::BitVec(8))),
        ),
        ChcVar::new("index", ChcSort::Int),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "ALL");
}

#[test]
fn test_detect_logic_bv_mixed_with_real_uses_content_routing() {
    let vars = vec![
        ChcVar::new("bits", ChcSort::BitVec(32)),
        ChcVar::new("real", ChcSort::Real),
    ];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "ALL");
}

#[test]
fn test_detect_logic_default_int_only() {
    // Int without arrays — falls through to default QF_AUFLIA.
    let vars = vec![ChcVar::new("x", ChcSort::Int)];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLIA");
}

#[test]
fn test_detect_logic_linear_int_product_stays_lia() {
    let x = ChcVar::new("x", ChcSort::Int);
    let vars = vec![x.clone()];
    let expr = ChcExpr::ge(
        ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(x)),
        ChcExpr::int(0),
    );
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFLIA");
}

#[test]
fn test_detect_logic_nonlinear_int_product_uses_nia_9004() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let vars = vec![x.clone(), y.clone()];
    let expr = ChcExpr::ge(
        ChcExpr::mul(ChcExpr::var(x), ChcExpr::var(y)),
        ChcExpr::int(0),
    );
    assert_eq!(detect_logic(&vars, &expr), "QF_NIA");
}

#[test]
fn test_detect_logic_array_nonlinear_int_product_uses_aufnia_9004() {
    let arr = ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let vars = vec![arr.clone(), x.clone(), y.clone()];
    let expr = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(arr), ChcExpr::var(x.clone())),
        ChcExpr::mul(ChcExpr::var(x), ChcExpr::var(y)),
    );
    assert_eq!(detect_logic(&vars, &expr), "QF_AUFNIA");
}

#[test]
fn test_detect_logic_array_from_expr_ops() {
    // No array-sorted variables, but the expression contains array ops.
    let vars = vec![ChcVar::new("x", ChcSort::Int)];
    let store_expr = ChcExpr::Op(
        crate::ChcOp::Store,
        vec![
            ChcExpr::var(ChcVar::new(
                "arr",
                ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
            ))
            .into(),
            ChcExpr::Bool(true).into(),
            ChcExpr::Int(42).into(),
        ],
    );
    // Should detect array from expr ops even without array-sorted vars.
    let logic = detect_logic(&vars, &store_expr);
    assert!(
        logic.contains("AU") || logic == "QF_AX",
        "should detect array logic from expr ops: got {logic}"
    );
}

#[test]
fn test_detect_logic_nested_datatype_selector_bv() {
    let inner = ChcSort::Datatype {
        name: "Inner".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-inner".to_string(),
            selectors: vec![ChcDtSelector {
                name: "payload".to_string(),
                sort: ChcSort::BitVec(32),
            }],
        }]),
    };
    let wrapper = ChcSort::Datatype {
        name: "Wrapper".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-wrapper".to_string(),
            selectors: vec![ChcDtSelector {
                name: "inner".to_string(),
                sort: inner,
            }],
        }]),
    };

    let vars = vec![ChcVar::new("w", wrapper)];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "_DT_AUFBV");
}

#[test]
fn test_detect_logic_datatype_bv_mixed_with_arithmetic_uses_content_routing() {
    let carrier = ChcSort::Datatype {
        name: "BvCarrier".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-bv-carrier".to_string(),
            selectors: vec![ChcDtSelector {
                name: "payload".to_string(),
                sort: ChcSort::BitVec(32),
            }],
        }]),
    };
    let expr = ChcExpr::Bool(true);

    let int_vars = vec![
        ChcVar::new("carrier", carrier.clone()),
        ChcVar::new("arithmetic", ChcSort::Int),
    ];
    assert_eq!(detect_logic(&int_vars, &expr), "QF_AUFBVLIA");

    let real_vars = vec![
        ChcVar::new("carrier", carrier),
        ChcVar::new("arithmetic", ChcSort::Real),
    ];
    assert_eq!(detect_logic(&real_vars, &expr), "QF_AUFBVLIRA");
}

#[test]
fn test_detect_logic_array_of_datatype_activates_dt_logic() {
    let pair = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-pair".to_string(),
            selectors: vec![ChcDtSelector {
                name: "fst".to_string(),
                sort: ChcSort::Int,
            }],
        }]),
    };

    let vars = vec![ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(pair), Box::new(ChcSort::Int)),
    )];
    let expr = ChcExpr::Bool(true);
    assert_eq!(detect_logic(&vars, &expr), "_DT_AUFLIA");
}

// ========================================================================
// sort_to_smtlib tests
// ========================================================================

#[test]
fn test_sort_to_smtlib_basic() {
    assert_eq!(sort_to_smtlib(&ChcSort::Bool), "Bool");
    assert_eq!(sort_to_smtlib(&ChcSort::Int), "Int");
    assert_eq!(sort_to_smtlib(&ChcSort::Real), "Real");
    assert_eq!(sort_to_smtlib(&ChcSort::BitVec(32)), "(_ BitVec 32)");
}

#[test]
fn test_sort_to_smtlib_array() {
    let sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    assert_eq!(sort_to_smtlib(&sort), "(Array Int Int)");
}

#[test]
fn test_sort_to_smtlib_nested_array() {
    // Array(Int, Array(Int, Bool))
    let inner = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool));
    let outer = ChcSort::Array(Box::new(ChcSort::Int), Box::new(inner));
    assert_eq!(sort_to_smtlib(&outer), "(Array Int (Array Int Bool))");
}

// ========================================================================
// term_body_to_smt_value tests
// ========================================================================

#[test]
fn test_term_body_to_smt_value_bool_true() {
    let term = ay_frontend::Term::Const(ay_frontend::Constant::True);
    assert_eq!(tv(&term), Some(SmtValue::Bool(true)));
}

#[test]
fn test_term_body_to_smt_value_bool_false() {
    let term = ay_frontend::Term::Const(ay_frontend::Constant::False);
    assert_eq!(tv(&term), Some(SmtValue::Bool(false)));
}

#[test]
fn test_term_body_to_smt_value_numeral() {
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("42".to_string()));
    assert_eq!(tv(&term), Some(SmtValue::Int(42)));
}

/// #6180: Numeral exceeding i64 range returns None (not silent drop).
#[test]
fn test_term_body_to_smt_value_numeral_overflow_returns_none() {
    // i128-lockstep: 2^63 now parses exactly into the widened Int lane.
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Numeral(
        "9223372036854775808".to_string(),
    ));
    assert_eq!(tv(&term), Some(SmtValue::Int(i128::from(i64::MAX) + 1)));

    // Phase-2 BigInt escape: 2^127 exceeds i128::MAX — preserved exactly as
    // canonical SmtValue::BigInt (never wrapped, no longer dropped).
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Numeral(
        "170141183460469231731687303715884105728".to_string(),
    ));
    let two_127: num_bigint::BigInt = num_bigint::BigInt::from(1u8) << 127;
    assert_eq!(
        tv(&term),
        Some(SmtValue::int_from_bigint(two_127)),
        "beyond-i128 numeral must be preserved exactly"
    );
}

/// #6180: Negation of an overflowing numeral returns None.
#[test]
fn test_term_body_to_smt_value_neg_overflow_returns_none() {
    // i128-lockstep: -(2^63 + 1) is representable in the widened lane.
    let inner = ay_frontend::Term::Const(ay_frontend::Constant::Numeral(
        "9223372036854775809".to_string(),
    ));
    let term = ay_frontend::Term::App("-".to_string(), vec![inner]);
    assert_eq!(tv(&term), Some(SmtValue::Int(-(i128::from(i64::MAX) + 2))));

    // Phase-2 BigInt escape: negation of a beyond-i128 numeral is exact.
    let inner = ay_frontend::Term::Const(ay_frontend::Constant::Numeral(
        "170141183460469231731687303715884105729".to_string(),
    ));
    let term = ay_frontend::Term::App("-".to_string(), vec![inner]);
    let two_127: num_bigint::BigInt = num_bigint::BigInt::from(1u8) << 127;
    let expected: num_bigint::BigInt = -(two_127 + num_bigint::BigInt::from(1u8));
    assert_eq!(
        tv(&term),
        Some(SmtValue::int_from_bigint(expected)),
        "negated beyond-i128 numeral must be preserved exactly"
    );
}

#[test]
fn test_term_body_to_smt_value_negation() {
    let inner = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("7".to_string()));
    let term = ay_frontend::Term::App("-".to_string(), vec![inner]);
    assert_eq!(tv(&term), Some(SmtValue::Int(-7)));
}

#[test]
fn test_term_body_to_smt_value_hex_bv() {
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Hexadecimal("FF".to_string()));
    assert_eq!(tv(&term), Some(SmtValue::BitVec(255, 8)));
}

#[test]
fn test_term_body_to_smt_value_wide_hex_bv_truncation_7040() {
    // 192-bit hex (48 hex digits): truncates to low 128 bits
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Hexadecimal(
        "000000000000000100000000000000020000000000000003".to_string(),
    ));
    assert_eq!(
        tv(&term),
        Some(SmtValue::BitVec(0x00000000000000020000000000000003, 192))
    );
}

#[test]
fn test_term_body_to_smt_value_wide_bin_bv_truncation_7040() {
    // 192-bit binary: truncates to low 128 bits (all ones)
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Binary("1".repeat(192)));
    assert_eq!(tv(&term), Some(SmtValue::BitVec(u128::MAX, 192)));
}

#[test]
fn test_term_body_to_smt_value_binary_bv() {
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Binary("1010".to_string()));
    assert_eq!(tv(&term), Some(SmtValue::BitVec(10, 4)));
}

#[test]
fn test_term_body_to_smt_value_decimal() {
    use num_rational::BigRational;
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Decimal("1.5".to_string()));
    let result = tv(&term);
    let expected = BigRational::new(3.into(), 2.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_decimal_zero() {
    use num_rational::BigRational;
    let term = ay_frontend::Term::Const(ay_frontend::Constant::Decimal("0.0".to_string()));
    let result = tv(&term);
    let expected = BigRational::new(0.into(), 1.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_negation_real() {
    use num_rational::BigRational;
    // (- 1.5) should produce Real(-3/2)
    let inner = ay_frontend::Term::Const(ay_frontend::Constant::Decimal("1.5".to_string()));
    let term = ay_frontend::Term::App("-".to_string(), vec![inner]);
    let result = tv(&term);
    let expected = BigRational::new((-3).into(), 2.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_rational_division() {
    use num_rational::BigRational;
    // (/ 3 2) should produce Real(3/2)
    let num = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("3".to_string()));
    let den = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("2".to_string()));
    let term = ay_frontend::Term::App("/".to_string(), vec![num, den]);
    let result = tv(&term);
    let expected = BigRational::new(3.into(), 2.into());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_term_body_to_smt_value_div_by_zero_returns_none() {
    let num = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("5".to_string()));
    let den = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("0".to_string()));
    let term = ay_frontend::Term::App("/".to_string(), vec![num, den]);
    assert_eq!(tv(&term), None);
}

// ========================================================================
// parse_model_into tests
// ========================================================================

#[test]
fn test_parse_model_into_empty_string() {
    let mut model = FxHashMap::default();
    pm(&mut model, "");
    assert!(model.is_empty());
}

#[test]
fn test_parse_model_into_define_fun_int() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun x () Int 42)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(42)));
}

#[test]
fn test_parse_model_into_define_fun_bool() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun b () Bool true)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("b"), Some(&SmtValue::Bool(true)));
}

#[test]
fn test_parse_model_into_define_fun_negint() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun x () Int (- 5))\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(-5)));
}

#[test]
fn test_parse_model_into_multiple_entries() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun x () Int 1)\n  (define-fun y () Int 2)\n  (define-fun b () Bool false)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(1)));
    assert_eq!(model.get("y"), Some(&SmtValue::Int(2)));
    assert_eq!(model.get("b"), Some(&SmtValue::Bool(false)));
}

#[test]
fn test_parse_model_into_skips_parameterized_funs() {
    let mut model = FxHashMap::default();
    // define-fun with parameters should be skipped (not a 0-arity constant).
    let model_str = "(model\n  (define-fun f ((x Int)) Int x)\n  (define-fun c () Int 7)\n)";
    pm(&mut model, model_str);
    assert!(
        !model.contains_key("f"),
        "parameterized fun should be skipped"
    );
    assert_eq!(model.get("c"), Some(&SmtValue::Int(7)));
}

#[test]
fn test_parse_model_into_preserves_existing_entries() {
    let mut model = FxHashMap::default();
    model.insert("existing".to_string(), SmtValue::Int(99));
    let model_str = "(model\n  (define-fun x () Int 1)\n)";
    pm(&mut model, model_str);
    assert_eq!(model.get("existing"), Some(&SmtValue::Int(99)));
    assert_eq!(model.get("x"), Some(&SmtValue::Int(1)));
}

/// #6180 → Phase-2 BigInt escape: large numerals are preserved EXACTLY.
/// In-i128 values stay `SmtValue::Int`; beyond-i128 values become canonical
/// `SmtValue::BigInt` (they used to be dropped fail-closed, which demoted
/// verified Sat verdicts to Unknown downstream).
#[test]
fn test_parse_model_into_large_int_dropped() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun big () Int 9223372036854775808)\n  (define-fun huge () Int 170141183460469231731687303715884105728)\n  (define-fun ok () Int 1)\n)";
    pm(&mut model, model_str);
    assert_eq!(
        model.get("big"),
        Some(&SmtValue::Int(i128::from(i64::MAX) + 1)),
        "beyond-i64 in-i128 numeral should be preserved exactly"
    );
    let huge: num_bigint::BigInt = num_bigint::BigInt::from(1u8) << 127;
    assert_eq!(
        model.get("huge"),
        Some(&SmtValue::int_from_bigint(huge)),
        "beyond-i128 numeral should be preserved exactly as SmtValue::BigInt"
    );
    assert_eq!(
        model.get("ok"),
        Some(&SmtValue::Int(1)),
        "non-overflowing entry should be preserved"
    );
}

// ========================================================================
// parse_decimal_to_rational tests
// ========================================================================

#[test]
fn test_parse_decimal_to_rational_simple() {
    use num_rational::BigRational;
    let r = parse_decimal_to_rational("1.5").unwrap();
    assert_eq!(r, BigRational::new(3.into(), 2.into()));
}

#[test]
fn test_parse_decimal_to_rational_integer() {
    use num_rational::BigRational;
    let r = parse_decimal_to_rational("42").unwrap();
    assert_eq!(r, BigRational::from_integer(42.into()));
}

#[test]
fn test_parse_decimal_to_rational_trailing_zeros() {
    use num_rational::BigRational;
    // "3.0" -> 30/10 = 3/1
    let r = parse_decimal_to_rational("3.0").unwrap();
    assert_eq!(r, BigRational::from_integer(3.into()));
}

#[test]
fn test_parse_decimal_to_rational_precise() {
    use num_rational::BigRational;
    // "0.125" -> 125/1000 = 1/8
    let r = parse_decimal_to_rational("0.125").unwrap();
    assert_eq!(r, BigRational::new(1.into(), 8.into()));
}

// ========================================================================
// #6047: Array model parsing tests
// ========================================================================

#[test]
fn test_term_body_to_smt_value_const_array() {
    // ((as const (Array Int Int)) 0) -> ConstArray(Int(0))
    let inner = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("0".to_string()));
    let sort = ay_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            ay_frontend::command::Sort::Simple("Int".to_string()),
            ay_frontend::command::Sort::Simple("Int".to_string()),
        ],
    );
    let term = ay_frontend::Term::QualifiedApp(
        ay_frontend::QualifiedIdentifier::Symbol("const".to_string()),
        sort,
        vec![inner],
    );
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ConstArray(Box::new(SmtValue::Int(0))))
    );
}

#[test]
fn test_term_body_to_smt_value_const_array_bv() {
    // ((as const (Array (_ BitVec 32) (_ BitVec 8))) #x42) -> ConstArray(BitVec(0x42, 8))
    let inner = ay_frontend::Term::Const(ay_frontend::Constant::Hexadecimal("42".to_string()));
    let sort = ay_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            ay_frontend::command::Sort::Indexed(
                "BitVec".to_string(),
                vec![ay_frontend::Index::Numeral("32".to_string())],
            ),
            ay_frontend::command::Sort::Indexed(
                "BitVec".to_string(),
                vec![ay_frontend::Index::Numeral("8".to_string())],
            ),
        ],
    );
    let term = ay_frontend::Term::QualifiedApp(
        ay_frontend::QualifiedIdentifier::Symbol("const".to_string()),
        sort,
        vec![inner],
    );
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ConstArray(Box::new(SmtValue::BitVec(0x42, 8))))
    );
}

#[test]
fn test_term_body_to_smt_value_store_on_const_array() {
    // (store ((as const (Array Int Int)) 0) 1 42)
    // -> ArrayMap { default: Int(0), entries: [(Int(1), Int(42))] }
    let sort = ay_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            ay_frontend::command::Sort::Simple("Int".to_string()),
            ay_frontend::command::Sort::Simple("Int".to_string()),
        ],
    );
    let const_arr = ay_frontend::Term::QualifiedApp(
        ay_frontend::QualifiedIdentifier::Symbol("const".to_string()),
        sort,
        vec![ay_frontend::Term::Const(ay_frontend::Constant::Numeral(
            "0".to_string(),
        ))],
    );
    let term = ay_frontend::Term::App(
        "store".to_string(),
        vec![
            const_arr,
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("1".to_string())),
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("42".to_string())),
        ],
    );
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(1), SmtValue::Int(42))],
        })
    );
}

#[test]
fn test_term_body_to_smt_value_nested_store() {
    // (store (store ((as const (Array Int Int)) 0) 1 10) 2 20)
    // -> ArrayMap { default: Int(0), entries: [(1,10), (2,20)] }
    let sort = ay_frontend::command::Sort::Parameterized(
        "Array".to_string(),
        vec![
            ay_frontend::command::Sort::Simple("Int".to_string()),
            ay_frontend::command::Sort::Simple("Int".to_string()),
        ],
    );
    let const_arr = ay_frontend::Term::QualifiedApp(
        ay_frontend::QualifiedIdentifier::Symbol("const".to_string()),
        sort,
        vec![ay_frontend::Term::Const(ay_frontend::Constant::Numeral(
            "0".to_string(),
        ))],
    );
    let inner_store = ay_frontend::Term::App(
        "store".to_string(),
        vec![
            const_arr,
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("1".to_string())),
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("10".to_string())),
        ],
    );
    let term = ay_frontend::Term::App(
        "store".to_string(),
        vec![
            inner_store,
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("2".to_string())),
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("20".to_string())),
        ],
    );
    let result = tv(&term);
    assert_eq!(
        result,
        Some(SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![
                (SmtValue::Int(1), SmtValue::Int(10)),
                (SmtValue::Int(2), SmtValue::Int(20)),
            ],
        })
    );
}

#[test]
fn test_parse_model_into_const_array() {
    // Full round-trip: parse model output with constant array.
    let mut model = FxHashMap::default();
    let model_str =
        "(model\n  (define-fun arr () (Array Int Int)\n    ((as const (Array Int Int)) 0))\n)";
    pm(&mut model, model_str);
    assert_eq!(
        model.get("arr"),
        Some(&SmtValue::ConstArray(Box::new(SmtValue::Int(0))))
    );
}

#[test]
fn test_parse_model_into_store_array() {
    // Full round-trip: parse model output with store chain.
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun arr () (Array Int Int)\n    (store ((as const (Array Int Int)) 0) 5 99))\n)";
    pm(&mut model, model_str);
    assert_eq!(
        model.get("arr"),
        Some(&SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(5), SmtValue::Int(99))],
        })
    );
}

#[test]
fn test_term_body_store_array_preserves_symbolic_base_as_opaque_1753() {
    let term = ay_frontend::Term::App(
        "store".to_string(),
        vec![
            ay_frontend::Term::Symbol("A!0".to_string()),
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("5".to_string())),
            ay_frontend::Term::Const(ay_frontend::Constant::Numeral("99".to_string())),
        ],
    );
    let result = tv(&term).expect("store over symbolic base should still parse");

    assert_eq!(
        eval_array_select(&result, &SmtValue::Int(5)),
        Some(SmtValue::Int(99))
    );
    assert!(
        matches!(
            eval_array_select(&result, &SmtValue::Int(6)),
            Some(SmtValue::Opaque(_))
        ),
        "unstored indices should fall back to an opaque base: {result:?}"
    );
}

#[test]
fn test_parse_model_into_store_array_with_symbolic_base_1753() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  (define-fun arr () (Array Int Int)\n    (store A!0 5 99))\n)";
    pm(&mut model, model_str);
    let arr = model
        .get("arr")
        .expect("store over symbolic base should not be dropped");

    assert_eq!(
        eval_array_select(arr, &SmtValue::Int(5)),
        Some(SmtValue::Int(99))
    );
    assert!(
        matches!(
            eval_array_select(arr, &SmtValue::Int(6)),
            Some(SmtValue::Opaque(_))
        ),
        "unstored indices should keep an opaque symbolic default: {arr:?}"
    );
}

// ========================================================================
// SmtValue::Datatype model parsing tests
// ========================================================================

#[test]
fn test_parse_model_dt_nullary_constructor() {
    let mut model = FxHashMap::default();
    let dt_ctors: FxHashSet<String> = ["Green", "Red", "Yellow"]
        .iter()
        .map(ToString::to_string)
        .collect();
    let model_str = "(model\n  (define-fun color () Color Green)\n)";
    parse_model_into(&mut model, model_str, &dt_ctors);
    assert_eq!(
        model.get("color"),
        Some(&SmtValue::Datatype("Green".to_string(), vec![]))
    );
}

#[test]
fn test_parse_model_dt_constructor_with_fields() {
    let mut model = FxHashMap::default();
    let dt_ctors: FxHashSet<String> = ["mkpair"].iter().map(ToString::to_string).collect();
    let model_str = "(model\n  (define-fun p () Pair (mkpair 42 7))\n)";
    parse_model_into(&mut model, model_str, &dt_ctors);
    assert_eq!(
        model.get("p"),
        Some(&SmtValue::Datatype(
            "mkpair".to_string(),
            vec![SmtValue::Int(42), SmtValue::Int(7)]
        ))
    );
}

#[test]
fn test_term_body_dt_nullary_app() {
    let dt_ctors: FxHashSet<String> = ["None_"].iter().map(ToString::to_string).collect();
    let term = ay_frontend::Term::App("None_".to_string(), vec![]);
    assert_eq!(
        term_body_to_smt_value(&term, &dt_ctors),
        Some(SmtValue::Datatype("None_".to_string(), vec![]))
    );
}

#[test]
fn test_term_body_dt_constructor_app() {
    let dt_ctors: FxHashSet<String> = ["Some_"].iter().map(ToString::to_string).collect();
    let arg = ay_frontend::Term::Const(ay_frontend::Constant::Numeral("99".to_string()));
    let term = ay_frontend::Term::App("Some_".to_string(), vec![arg]);
    assert_eq!(
        term_body_to_smt_value(&term, &dt_ctors),
        Some(SmtValue::Datatype(
            "Some_".to_string(),
            vec![SmtValue::Int(99)]
        ))
    );
}

#[test]
fn test_term_body_unknown_app_returns_none_without_dt_ctors() {
    // Without DT constructor names, unknown App returns None.
    let term = ay_frontend::Term::App(
        "mkpair".to_string(),
        vec![ay_frontend::Term::Const(ay_frontend::Constant::Numeral(
            "1".to_string(),
        ))],
    );
    assert_eq!(tv(&term), None);
}

// ========================================================================
// parse_simple_value tests (fallback parser)
// ========================================================================

#[test]
fn test_parse_simple_value_int_positive() {
    assert_eq!(parse_simple_value("Int 42)"), Some(SmtValue::Int(42)));
}

#[test]
fn test_parse_simple_value_int_negative() {
    assert_eq!(parse_simple_value("Int (- 7))"), Some(SmtValue::Int(-7)));
}

#[test]
fn test_parse_simple_value_bool_true() {
    assert_eq!(parse_simple_value("Bool true)"), Some(SmtValue::Bool(true)));
}

#[test]
fn test_parse_simple_value_bool_false() {
    assert_eq!(
        parse_simple_value("Bool false)"),
        Some(SmtValue::Bool(false))
    );
}

#[test]
fn test_parse_simple_value_unknown_sort() {
    assert_eq!(parse_simple_value("Real 1.5)"), None);
}

/// #6180 (updated for the i128 widening): in-range beyond-i64 values now
/// parse EXACTLY into the widened `SmtValue::Int(i128)` model lane.
#[test]
fn test_parse_simple_value_beyond_i64_parses_exactly() {
    assert_eq!(
        parse_simple_value("Int 9223372036854775808)"),
        Some(SmtValue::Int(i128::from(i64::MAX) + 1)),
        "i64::MAX+1 must parse exactly (was dropped pre-widening)"
    );
    // u64::MAX round-trips through the model value lane.
    assert_eq!(
        parse_simple_value("Int 18446744073709551615)"),
        Some(SmtValue::Int(u64::MAX as i128)),
    );
    assert_eq!(
        parse_simple_value("Int (- 9223372036854775809))"),
        Some(SmtValue::Int(-(i128::from(i64::MAX) + 2))),
        "negative beyond-i64 must parse exactly"
    );
}

/// #6180 → Phase-2 BigInt escape: beyond-i128 integers are preserved
/// exactly as canonical `SmtValue::BigInt` — never wrapped, never dropped.
#[test]
fn test_parse_simple_value_int_overflow_returns_none() {
    let two_127: num_bigint::BigInt = num_bigint::BigInt::from(1u8) << 127;
    assert_eq!(
        parse_simple_value("Int 170141183460469231731687303715884105728)"),
        Some(SmtValue::int_from_bigint(two_127)),
        "positive beyond-i128 numeral must be preserved exactly"
    );
}

/// #6180 → Phase-2: same for negative beyond-i128 integers.
#[test]
fn test_parse_simple_value_neg_int_overflow_returns_none() {
    let two_127: num_bigint::BigInt = num_bigint::BigInt::from(1u8) << 127;
    let neg: num_bigint::BigInt = -(two_127 + num_bigint::BigInt::from(1u8));
    assert_eq!(
        parse_simple_value("Int (- 170141183460469231731687303715884105729))"),
        Some(SmtValue::int_from_bigint(neg)),
        "negative beyond-i128 numeral must be preserved exactly"
    );
}

// ========================================================================
// parse_model_simple tests (fallback parser)
// ========================================================================

#[test]
fn test_parse_model_simple_basic() {
    let mut model = FxHashMap::default();
    let model_str = "(define-fun x () Int 42)\n(define-fun b () Bool true)";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(42)));
    assert_eq!(model.get("b"), Some(&SmtValue::Bool(true)));
}

#[test]
fn test_parse_model_simple_negative_int() {
    let mut model = FxHashMap::default();
    let model_str = "(define-fun x () Int (- 3))";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(-3)));
}

#[test]
fn test_parse_model_simple_skips_non_define_fun() {
    let mut model = FxHashMap::default();
    let model_str = "(model\n  some garbage\n  (define-fun x () Int 1)\n)";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("x"), Some(&SmtValue::Int(1)));
}

#[test]
fn test_parse_model_simple_skips_parameterized() {
    let mut model = FxHashMap::default();
    // Has params "(x Int)" instead of "()" — should be skipped.
    let model_str = "(define-fun f (x Int) Int x)";
    parse_model_simple(&mut model, model_str);
    assert!(model.is_empty());
}

#[test]
fn test_parse_model_simple_pipe_quoted_name_no_spaces() {
    // Pipe-quoted names without internal spaces parse correctly.
    // Names with spaces (e.g., |my var|) are split incorrectly by the
    // space-based heuristic — this is a known limitation of the fallback
    // parser. The primary parser (parse_model_into via ay-frontend) handles
    // pipe-quoted names correctly.
    let mut model = FxHashMap::default();
    let model_str = "(define-fun |my_var| () Int 99)";
    parse_model_simple(&mut model, model_str);
    assert_eq!(model.get("my_var"), Some(&SmtValue::Int(99)));
}

// ========================================================================
// check_sat_via_executor integration tests
// ========================================================================

#[test]
fn test_check_sat_via_executor_sat_simple() {
    // (x > 0) with x:Int — trivially SAT.
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "x > 0 should be SAT via executor: got {result:?}"
    );
}

#[test]
fn test_check_sat_via_executor_unsat_contradiction() {
    // (x > 0 AND x < 0) — UNSAT.
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(0).into()],
    );
    let lt = ChcExpr::Op(
        crate::ChcOp::Lt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let expr = ChcExpr::Op(crate::ChcOp::And, vec![gt.into(), lt.into()]);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Unsat),
        "(x > 0 AND x < 0) should be UNSAT via executor: got {result:?}"
    );
}

#[test]
fn test_check_sat_via_executor_propagated_model_merged() {
    // SAT formula with propagated model entries — propagated values appear in result.
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let smt = SmtContext::new();
    let mut propagated = FxHashMap::default();
    propagated.insert("y".to_string(), SmtValue::Int(42));
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    if let SmtResult::Sat(model) = result {
        assert_eq!(
            model.get("y"),
            Some(&SmtValue::Int(42)),
            "propagated model entry should be preserved in SAT model"
        );
    } else {
        panic!("expected SAT, got {result:?}");
    }
}

#[test]
fn test_check_sat_via_executor_empty_vars_returns_unknown() {
    // Expression with no free variables returns Unknown (line 38-41).
    let expr = ChcExpr::Bool(true);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Unknown),
        "no-variable expression should return Unknown: got {result:?}"
    );
}

#[test]
fn test_check_sat_via_executor_declares_expr_local_datatype_terms_9476() {
    let option_u8 = ChcSort::Datatype {
        name: "Option_u8".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "None_Option_u8".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "Some_Option_u8".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "value_Option_u8".to_string(),
                    sort: ChcSort::BitVec(8),
                }],
            },
        ]),
    };

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let some_four = ChcExpr::FuncApp(
        "Some_Option_u8".to_string(),
        option_u8,
        vec![ChcExpr::BitVec(4, 8).into()],
    );
    let selected = ChcExpr::FuncApp(
        "value_Option_u8".to_string(),
        ChcSort::BitVec(8),
        vec![some_four.into()],
    );
    let expr = ChcExpr::Op(
        crate::ChcOp::And,
        vec![
            ChcExpr::eq(x.clone(), x).into(),
            ChcExpr::eq(selected, ChcExpr::BitVec(4, 8)).into(),
        ],
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();

    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));

    assert!(
        matches!(result, SmtResult::Sat(_)),
        "expression-local datatype constructor/selector terms should be declared: got {result:?}"
    );
}

#[test]
fn test_check_sat_via_executor_rejects_arithmetic_lt_on_bv_unknown_not_panic() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let expr = ChcExpr::Op(
        crate::ChcOp::Lt,
        vec![ChcExpr::var(x).into(), ChcExpr::BitVec(1, 8).into()],
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();

    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));

    assert!(
        matches!(result, SmtResult::Unknown),
        "BV arithmetic comparison should be rejected before SMT-LIB parsing, got {result:?}"
    );
}

#[test]
fn test_check_sat_via_executor_rejects_store_index_sort_mismatch_9699() {
    let arr = ChcVar::new(
        "A",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::Store,
            vec![
                ChcExpr::var(arr.clone()).into(),
                ChcExpr::Bool(true).into(),
                ChcExpr::Int(1).into(),
            ],
        ),
        ChcExpr::var(arr),
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();

    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));

    assert!(
        matches!(result, SmtResult::Unknown),
        "ill-sorted store index should fail closed before executor parsing, got {result:?}"
    );
}

#[test]
fn test_accept_reparsed_sat_model_rejects_indeterminate_array_query_4993() {
    let arr = ChcVar::new(
        "A",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let expr = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(arr), ChcExpr::Int(0)),
        ChcExpr::Int(42),
    );

    assert!(
        accept_reparsed_sat_model(&[&expr], FxHashMap::default(), "executor_adapter test",)
            .is_none(),
        "array fallback SAT models must validate definitively before acceptance"
    );
}

/// Executor twin of the `sat_or_unknown` model-completion path (2026-07): a
/// reparsed model missing one evaluable-position BV variable is completed with
/// the sort default and — because the completed model strictly verifies the
/// ORIGINAL conjunction — accepted, returning the COMPLETED model.
#[test]
fn test_accept_reparsed_sat_model_completes_missing_bv_var_to_valid_witness() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let d = ChcVar::new("d", ChcSort::BitVec(8));
    let ex = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(0, 8));
    let ed = ChcExpr::eq(ChcExpr::var(d), ChcExpr::BitVec(5, 8));
    let mut model = FxHashMap::default();
    model.insert("d".to_string(), SmtValue::BitVec(5, 8));
    let out = accept_reparsed_sat_model(&[&ex, &ed], model, "executor_adapter test")
        .expect("default-completed strictly-Valid witness must be accepted");
    assert_eq!(
        out.get("x"),
        Some(&SmtValue::BitVec(0, 8)),
        "returned model must contain the default-filled BV variable"
    );
    assert_eq!(out.get("d"), Some(&SmtValue::BitVec(5, 8)));
}

/// Executor twin, fail-closed direction: when no defining equality is available
/// and the default completion does NOT strictly verify (x must be nonzero but
/// the default is 0), the model is rejected (None → Unknown upstream).
#[test]
fn test_accept_reparsed_sat_model_completion_not_valid_stays_rejected() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    // `x = 1` AND `x = 2` — genuinely UNSAT, so NO completion (neither the
    // FIX 5 bindings derivation, which derives x=1 and then fails the second
    // conjunct under strict conjunction re-verification, nor the scalar
    // default x=0) can produce a Valid witness; the model must stay rejected.
    // (A single-conjunct `x = 1` is now CORRECTLY accepted: the bindings
    // derivation yields the forced, strict-verified witness x=1.)
    let ex1 = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(1, 8));
    let ex2 = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(2, 8));
    assert!(
        accept_reparsed_sat_model(&[&ex1, &ex2], FxHashMap::default(), "executor_adapter test")
            .is_none(),
        "a completion that fails strict re-verification must stay rejected"
    );
}

// debug-only: the mk_le sort check is a debug_assert! (ay-core arithmetic.rs:1080).
// In release, the assert is compiled out and Le(Bool, true) is processed normally.
#[test]
#[cfg(debug_assertions)]
fn test_check_sat_via_executor_ay_panic_returns_unknown_issue_6781() {
    // #6781: malformed arithmetic comparisons can still reach the executor
    // through higher-level CHC discovery. The executor boundary must convert
    // ay-internal sort panics into Unknown instead of aborting the solve.
    let b = ChcVar::new("b", ChcSort::Bool);
    let expr = ChcExpr::Op(
        crate::ChcOp::Le,
        vec![ChcExpr::var(b).into(), ChcExpr::Bool(true).into()],
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Unknown),
        "ay-internal sort panic should degrade to Unknown: got {result:?}"
    );
}

// ========================================================================
// check_sat_conjunction_via_executor integration tests
// ========================================================================

#[test]
fn test_check_sat_conjunction_via_executor_sat() {
    use super::super::incremental::IncrementalCheckResult;
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(0).into()],
    );
    let lt = ChcExpr::Op(
        crate::ChcOp::Lt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(100).into()],
    );
    let propagated = FxHashMap::default();
    let result = check_sat_conjunction_via_executor(
        &[gt, lt],
        &propagated,
        std::time::Duration::from_secs(5),
    );
    assert!(
        matches!(result, IncrementalCheckResult::Sat(_)),
        "(x > 0) AND (x < 100) conjunction should be SAT: got {result:?}"
    );
}

#[test]
fn test_check_sat_conjunction_via_executor_unsat() {
    use super::super::incremental::IncrementalCheckResult;
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(10).into()],
    );
    let lt = ChcExpr::Op(
        crate::ChcOp::Lt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(5).into()],
    );
    let propagated = FxHashMap::default();
    let result = check_sat_conjunction_via_executor(
        &[gt, lt],
        &propagated,
        std::time::Duration::from_secs(5),
    );
    assert!(
        matches!(result, IncrementalCheckResult::Unsat),
        "(x > 10) AND (x < 5) conjunction should be UNSAT: got {result:?}"
    );
}

#[test]
fn test_check_sat_conjunction_via_executor_empty_returns_unknown() {
    use super::super::incremental::IncrementalCheckResult;
    // No expressions with variables -> Unknown.
    let result = check_sat_conjunction_via_executor(
        &[ChcExpr::Bool(true)],
        &FxHashMap::default(),
        std::time::Duration::from_secs(5),
    );
    assert!(
        matches!(result, IncrementalCheckResult::Unknown),
        "no-variable conjunction should return Unknown: got {result:?}"
    );
}

#[test]
fn test_check_sat_conjunction_via_executor_merges_propagated() {
    use super::super::incremental::IncrementalCheckResult;
    let x = ChcVar::new("x", ChcSort::Int);
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x).into(), ChcExpr::Int(0).into()],
    );
    let mut propagated = FxHashMap::default();
    propagated.insert("y".to_string(), 99);
    let result =
        check_sat_conjunction_via_executor(&[gt], &propagated, std::time::Duration::from_secs(5));
    if let IncrementalCheckResult::Sat(model) = result {
        assert_eq!(
            model.get("y"),
            Some(&SmtValue::Int(99)),
            "propagated equality should be in SAT model"
        );
    } else {
        panic!("expected SAT, got {result:?}");
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_enum() {
    // Nullary constructors (enum): Color = Red | Green | Blue
    let ctors = vec![
        ChcDtConstructor {
            name: "Red".to_string(),
            selectors: vec![],
        },
        ChcDtConstructor {
            name: "Green".to_string(),
            selectors: vec![],
        },
        ChcDtConstructor {
            name: "Blue".to_string(),
            selectors: vec![],
        },
    ];
    let emitted = emit_declare_datatype("Color", &ctors);
    let sexp = ay_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = ay_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        ay_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Color");
            assert_eq!(dt_dec.constructors.len(), 3);
            assert_eq!(dt_dec.constructors[0].name, "Red");
            assert_eq!(dt_dec.constructors[1].name, "Green");
            assert_eq!(dt_dec.constructors[2].name, "Blue");
            for c in &dt_dec.constructors {
                assert!(c.selectors.is_empty(), "enum ctors have no selectors");
            }
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_record() {
    // Record with selectors: Point = mk-point(x: Int, y: Int)
    let ctors = vec![ChcDtConstructor {
        name: "mk-point".to_string(),
        selectors: vec![
            ChcDtSelector {
                name: "x".to_string(),
                sort: ChcSort::Int,
            },
            ChcDtSelector {
                name: "y".to_string(),
                sort: ChcSort::Int,
            },
        ],
    }];
    let emitted = emit_declare_datatype("Point", &ctors);
    let sexp = ay_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = ay_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        ay_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Point");
            assert_eq!(dt_dec.constructors.len(), 1);
            let ctor = &dt_dec.constructors[0];
            assert_eq!(ctor.name, "mk-point");
            assert_eq!(ctor.selectors.len(), 2);
            assert_eq!(ctor.selectors[0].name, "x");
            assert_eq!(ctor.selectors[1].name, "y");
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_model_checker_consumer_tuple() {
    // model-checker-consumer-style tuple: Tuple_bv32_bool = mk-Tuple_bv32_bool(fst: BitVec(32), snd: Bool)
    let ctors = vec![ChcDtConstructor {
        name: "mk-Tuple_bv32_bool".to_string(),
        selectors: vec![
            ChcDtSelector {
                name: "fst".to_string(),
                sort: ChcSort::BitVec(32),
            },
            ChcDtSelector {
                name: "snd".to_string(),
                sort: ChcSort::Bool,
            },
        ],
    }];
    let emitted = emit_declare_datatype("Tuple_bv32_bool", &ctors);
    let sexp = ay_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = ay_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        ay_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Tuple_bv32_bool");
            assert_eq!(dt_dec.constructors.len(), 1);
            let ctor = &dt_dec.constructors[0];
            assert_eq!(ctor.name, "mk-Tuple_bv32_bool");
            assert_eq!(ctor.selectors.len(), 2);
            assert_eq!(ctor.selectors[0].name, "fst");
            assert_eq!(ctor.selectors[1].name, "snd");
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

#[test]
fn test_emit_declare_datatype_roundtrip_nested_array_sort() {
    // DT with Array-sorted selector: Wrapper = wrap(data: Array(Int, Int))
    let ctors = vec![ChcDtConstructor {
        name: "wrap".to_string(),
        selectors: vec![ChcDtSelector {
            name: "data".to_string(),
            sort: ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        }],
    }];
    let emitted = emit_declare_datatype("Wrapper", &ctors);
    let sexp = ay_frontend::sexp::parse_sexp(&emitted).unwrap();
    let cmd = ay_frontend::Command::from_sexp(&sexp).unwrap();
    match &cmd {
        ay_frontend::Command::DeclareDatatype(name, dt_dec) => {
            assert_eq!(name, "Wrapper");
            assert_eq!(dt_dec.constructors.len(), 1);
            let sel = &dt_dec.constructors[0].selectors[0];
            assert_eq!(sel.name, "data");
            // Sort should be (Array Int Int)
            match &sel.sort {
                ay_frontend::Sort::Parameterized(sort_name, params) => {
                    assert_eq!(sort_name, "Array");
                    assert_eq!(params.len(), 2);
                }
                other => panic!("expected Parameterized Array sort, got {other:?}"),
            }
        }
        other => panic!("expected DeclareDatatype, got {other:?}"),
    }
}

// ========================================================================
// #A3: div/mod axiomatization at the executor conversion boundary
// ========================================================================

/// `(mod x 3) = 1 ∧ select(a,0) = x ∧ 0 ≤ x ≤ 5` — SAT (x ∈ {1,4}).
/// AUFLIA query with raw mod: the executor boundary must axiomatize the mod
/// (Euclidean q/r decomposition) instead of degrading to Unknown via the
/// "(unsupported arithmetic)" fragment rejection.
#[test]
fn test_check_sat_via_executor_array_mod_literal_divisor_sat() {
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let select = ChcExpr::select(ChcExpr::var(a), ChcExpr::Int(0));
    let expr = ChcExpr::and_all([
        ChcExpr::eq(select, ChcExpr::var(x.clone())),
        ChcExpr::eq(
            ChcExpr::Op(
                crate::ChcOp::Mod,
                vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(3).into()],
            ),
            ChcExpr::Int(1),
        ),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5)),
    ]);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "array + (mod x 3) query must be SAT via executor, got {result:?}"
    );
}

/// `(mod x 3) = 1 ∧ select(a,0) = x ∧ x = 3` — UNSAT ((mod 3 3) = 0 ≠ 1).
#[test]
fn test_check_sat_via_executor_array_mod_literal_divisor_unsat() {
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let select = ChcExpr::select(ChcExpr::var(a), ChcExpr::Int(0));
    let expr = ChcExpr::and_all([
        ChcExpr::eq(select, ChcExpr::var(x.clone())),
        ChcExpr::eq(
            ChcExpr::Op(
                crate::ChcOp::Mod,
                vec![ChcExpr::var(x.clone()).into(), ChcExpr::Int(3).into()],
            ),
            ChcExpr::Int(1),
        ),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(3)),
    ]);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Unsat),
        "array + contradictory (mod x 3) query must be UNSAT via executor, got {result:?}"
    );
}

/// `(div (x - h) 4) ≥ h`-style div with literal divisor (heap__swaparray query
/// shape) must not be rejected as unsupported arithmetic in AUFLIA.
#[test]
fn test_check_sat_via_executor_array_div_literal_divisor_sat() {
    let x = ChcVar::new("x", ChcSort::Int);
    let h = ChcVar::new("h", ChcSort::Int);
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let select = ChcExpr::select(ChcExpr::var(a), ChcExpr::Int(0));
    let diff = ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(h.clone()));
    let div = ChcExpr::Op(crate::ChcOp::Div, vec![diff.into(), ChcExpr::Int(4).into()]);
    let expr = ChcExpr::and_all([
        ChcExpr::eq(select, ChcExpr::var(x.clone())),
        ChcExpr::le(ChcExpr::var(h.clone()), div),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(8)),
        ChcExpr::eq(ChcExpr::var(h), ChcExpr::Int(1)),
    ]);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    // h=1, x=8: (div 7 4) = 1 >= 1 — SAT.
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "array + (div (- x h) 4) query must be SAT via executor, got {result:?}"
    );
}

/// Select-dividend: `(mod (select a 0) 3) = 1 ∧ select(a,0) = 4` — SAT.
/// Exercises the `is_int_euclidean_dividend` Select extension: without it the
/// mod survives elimination and AUFLIA paths can reject the query.
#[test]
fn test_check_sat_via_executor_mod_select_dividend_sat() {
    let a = ChcVar::new(
        "a",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
    );
    let select = ChcExpr::select(ChcExpr::var(a), ChcExpr::Int(0));
    let expr = ChcExpr::and_all([
        ChcExpr::eq(
            ChcExpr::Op(
                crate::ChcOp::Mod,
                vec![select.clone().into(), ChcExpr::Int(3).into()],
            ),
            ChcExpr::Int(1),
        ),
        ChcExpr::eq(select, ChcExpr::Int(4)),
    ]);
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor(&expr, &propagated, std::time::Duration::from_secs(5));
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "(mod (select a 0) 3) query must be SAT via executor, got {result:?}"
    );
}

/// `axiomatize_mod_div_for_executor` rewrites constant-divisor mod/div and
/// leaves mod-free expressions untouched (returns None).
#[test]
fn test_axiomatize_mod_div_for_executor_rewrites_and_skips() {
    let x = ChcVar::new("x", ChcSort::Int);
    let plain = ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::Int(0));
    assert!(
        axiomatize_mod_div_for_executor(&plain).is_none(),
        "mod-free expression must not be rewritten"
    );

    let with_mod = ChcExpr::eq(
        ChcExpr::Op(
            crate::ChcOp::Mod,
            vec![ChcExpr::var(x).into(), ChcExpr::Int(3).into()],
        ),
        ChcExpr::Int(1),
    );
    let rewritten = axiomatize_mod_div_for_executor(&with_mod)
        .expect("mod expression must be axiomatized for the executor");
    assert!(
        !rewritten.contains_mod_or_div(),
        "constant-divisor mod must be fully eliminated, got {rewritten}"
    );
}

/// Inc-18: the per-run EqDiffVar opt-out plumbs end-to-end — the emitted
/// `(set-option :ay-eq-diffvar false)` parses, executes, and the solve
/// still returns the right verdicts on both polarities (guarded equality
/// shape so the pass would otherwise fire).
#[test]
fn test_check_sat_via_executor_with_dv_disabled_sat_and_unsat() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let g = ChcVar::new("g", ChcSort::Bool);
    let eq_xy = ChcExpr::Op(
        crate::ChcOp::Eq,
        vec![
            ChcExpr::var(x.clone()).into(),
            ChcExpr::var(y.clone()).into(),
        ],
    );
    let guarded = ChcExpr::Op(
        crate::ChcOp::Or,
        vec![ChcExpr::var(g).into(), eq_xy.clone().into()],
    );
    let smt = SmtContext::new();
    let propagated = FxHashMap::default();
    let result = smt.check_sat_via_executor_with_opts(
        &guarded,
        &propagated,
        std::time::Duration::from_secs(5),
        true,
    );
    assert!(
        matches!(result, SmtResult::Sat(_)),
        "(g or x=y) should be SAT with the dv pass disabled: got {result:?}"
    );

    // x = y AND x > y — UNSAT regardless of the pass.
    let gt = ChcExpr::Op(
        crate::ChcOp::Gt,
        vec![ChcExpr::var(x).into(), ChcExpr::var(y).into()],
    );
    let expr = ChcExpr::Op(crate::ChcOp::And, vec![eq_xy.into(), gt.into()]);
    let result = smt.check_sat_via_executor_with_opts(
        &expr,
        &propagated,
        std::time::Duration::from_secs(5),
        true,
    );
    assert!(
        matches!(result, SmtResult::Unsat),
        "(x=y and x>y) should be UNSAT with the dv pass disabled: got {result:?}"
    );
}

// ========================================================================
// Phase-2 BigInt escape: executor-fallback model lane
// ========================================================================

/// Beyond-i128 numerals in executor model text become canonical
/// `SmtValue::BigInt` instead of being dropped (positive and negated), and
/// in-range numerals stay canonical `SmtValue::Int`.
#[test]
fn test_parse_model_into_beyond_i128_numeral() {
    use num_bigint::BigInt;
    let big: BigInt = (BigInt::from(1u8) << 128) + 1;

    let mut model = FxHashMap::default();
    let model_str = format!(
        "(model\n  (define-fun x () Int {big})\n  (define-fun y () Int (- {big}))\n  (define-fun z () Int {})\n)",
        i128::MAX
    );
    pm(&mut model, &model_str);

    assert_eq!(
        model.get("x"),
        Some(&SmtValue::int_from_bigint(big.clone()))
    );
    assert_eq!(model.get("y"), Some(&SmtValue::int_from_bigint(-big)));
    assert_eq!(
        model.get("z"),
        Some(&SmtValue::Int(i128::MAX)),
        "in-range values stay canonical Int"
    );
}

/// The simple string-fallback parser handles beyond-i128 numerals too
/// (including the negated form and the i128::MIN magnitude edge).
#[test]
fn test_parse_simple_value_beyond_i128() {
    use num_bigint::BigInt;
    let big: BigInt = (BigInt::from(1u8) << 128) + 1;

    assert_eq!(
        parse_simple_value(&format!("Int {big})")),
        Some(SmtValue::int_from_bigint(big.clone()))
    );
    assert_eq!(
        parse_simple_value(&format!("Int (- {big}))")),
        Some(SmtValue::int_from_bigint(-big))
    );
    // -(i128::MIN) magnitude: previously dropped by checked_neg; now exact.
    let min_magnitude = -BigInt::from(i128::MIN);
    assert_eq!(
        parse_simple_value(&format!("Int (- {min_magnitude}))")),
        Some(SmtValue::Int(i128::MIN))
    );
}

/// `Solver::try_new*` dispatches its own `set-logic`, so a script that keeps
/// one makes it the SECOND — which the elaborator rejects for z3 parity
/// (`118630ef6`). Callers must therefore hand construction the script's own
/// logic and strip the command; when they did not, `parse_smtlib2` failed and
/// the error was swallowed into a bare `None`, surfacing as checked replay
/// reporting "did not produce a native strict UNSAT certificate".
#[test]
fn split_leading_set_logic_takes_the_declared_logic_and_removes_the_command() {
    use ay_dpll::api::Logic;

    let (logic, body) = super::split_leading_set_logic(
        "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (> x 0))\n",
        Logic::All,
    );
    assert_eq!(logic, Logic::QfLia, "the script's own logic must be used");
    assert!(
        !body.contains("set-logic"),
        "the command must be stripped so the constructor's is the only one: {body}"
    );
    assert!(
        body.contains("(assert (> x 0))"),
        "body must survive: {body}"
    );

    // Only the FIRST is removed — a genuine second one is a real error and must
    // still reach the elaborator.
    let (_, two) = super::split_leading_set_logic(
        "(set-logic QF_LIA)\n(set-logic QF_UF)\n(assert true)\n",
        Logic::All,
    );
    assert!(
        two.contains("(set-logic QF_UF)"),
        "second must survive: {two}"
    );
}

#[test]
fn split_leading_set_logic_falls_back_and_leaves_unrecognized_input_alone() {
    use ay_dpll::api::Logic;

    // No declaration: caller's fallback, script untouched.
    let script = "(declare-fun x () Int)\n(assert (> x 0))\n";
    let (logic, body) = super::split_leading_set_logic(script, Logic::QfLia);
    assert_eq!(logic, Logic::QfLia);
    assert_eq!(body, script);

    // Not the `(set-logic <token>)` shape — pass through verbatim rather than
    // silently altering a script we do not understand.
    for odd in [
        "(set-logicQF_LIA)\n(assert true)\n",
        "(set-logic (weird))\n(assert true)\n",
        "(set-logic\n",
    ] {
        let (logic, body) = super::split_leading_set_logic(odd, Logic::QfLia);
        assert_eq!(logic, Logic::QfLia, "must fall back on {odd:?}");
        assert_eq!(body, odd, "must be untouched: {odd:?}");
    }
}
