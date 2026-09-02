// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #5151: indexed identifiers must parse correctly.
/// Covers `(_ BitVec N)` sorts, `(_ bvN W)` literals, and `(_ extract i j)`
/// / `(_ zero_extend N)` / `(_ sign_extend N)` indexed operations.
#[test]
fn test_parse_indexed_identifiers() {
    // Test 1: (_ BitVec N) sort in declare-fun
    let input = r#"
            (set-logic HORN)
            (declare-fun inv ((_ BitVec 32) (_ BitVec 8)) Bool)
            (assert (forall ((x (_ BitVec 32)) (y (_ BitVec 8)))
              (=> (= x (_ bv0 32)) (inv x y))))
            (check-sat)
        "#;
    let problem = ChcParser::parse(input).expect("indexed identifier parse should succeed");
    assert_eq!(problem.predicates().len(), 1);
    assert_eq!(problem.predicates()[0].arg_sorts.len(), 2);
    assert_eq!(problem.predicates()[0].arg_sorts[0], ChcSort::BitVec(32));
    assert_eq!(problem.predicates()[0].arg_sorts[1], ChcSort::BitVec(8));

    // Test 2: (_ extract i j) as higher-order application
    let mut parser = ChcParser::new();
    parser
        .variables
        .insert("x".to_string(), ChcSort::BitVec(32));

    parser.input = "((_ extract 7 0) x)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("extract should parse");
    assert!(
        matches!(expr, ChcExpr::Op(ChcOp::BvExtract(7, 0), _)),
        "Expected BvExtract(7, 0), got {expr:?}"
    );

    // Test 3: (_ zero_extend N) as higher-order application
    parser.input = "((_ zero_extend 24) x)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("zero_extend should parse");
    assert!(
        matches!(expr, ChcExpr::Op(ChcOp::BvZeroExtend(24), _)),
        "Expected BvZeroExtend(24), got {expr:?}"
    );

    // Test 4: (_ sign_extend N) as higher-order application
    parser.input = "((_ sign_extend 16) x)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("sign_extend should parse");
    assert!(
        matches!(expr, ChcExpr::Op(ChcOp::BvSignExtend(16), _)),
        "Expected BvSignExtend(16), got {expr:?}"
    );

    // Test 5: (_ bvN W) literal
    parser.input = "(_ bv42 32)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("bv literal should parse");
    assert_eq!(expr, ChcExpr::BitVec(42, 32));
}

/// Test n-ary left-associative BV operations (#5526, #5445).
/// SMT-LIB 2.6 defines bvadd/bvmul/bvand/bvor/bvxor as left-associative,
/// so (bvadd a b c) = (bvadd (bvadd a b) c).
#[test]
fn test_parse_nary_bv_left_associative() {
    let mut parser = ChcParser::new();
    parser
        .variables
        .insert("a".to_string(), ChcSort::BitVec(32));
    parser
        .variables
        .insert("b".to_string(), ChcSort::BitVec(32));
    parser
        .variables
        .insert("c".to_string(), ChcSort::BitVec(32));

    // Binary bvadd (baseline)
    parser.input = "(bvadd a b)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("binary bvadd should parse");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::BvAdd, ref args) if args.len() == 2));

    // Ternary bvadd: (bvadd a b c) => (bvadd (bvadd a b) c)
    parser.input = "(bvadd a b c)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("ternary bvadd should parse");
    // Outer node is BvAdd with 2 args, first arg is also BvAdd
    match &expr {
        ChcExpr::Op(ChcOp::BvAdd, args) => {
            assert_eq!(args.len(), 2, "folded bvadd should have 2 args");
            assert!(
                matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::BvAdd, inner) if inner.len() == 2),
                "first arg should be nested bvadd"
            );
        }
        _ => panic!("expected BvAdd, got {expr:?}"),
    }

    // 4-ary bvadd: (bvadd a b c a) => (bvadd (bvadd (bvadd a b) c) a)
    parser.input = "(bvadd a b c a)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("4-ary bvadd should parse");
    match &expr {
        ChcExpr::Op(ChcOp::BvAdd, args) => {
            assert_eq!(args.len(), 2);
            // First arg is (bvadd (bvadd a b) c)
            match args[0].as_ref() {
                ChcExpr::Op(ChcOp::BvAdd, inner) => {
                    assert_eq!(inner.len(), 2);
                    assert!(matches!(inner[0].as_ref(), ChcExpr::Op(ChcOp::BvAdd, _)));
                }
                _ => panic!("expected nested bvadd"),
            }
        }
        _ => panic!("expected BvAdd, got {expr:?}"),
    }

    // Other left-associative BV ops: bvmul, bvand, bvor, bvxor
    for (op_name, expected_op) in [
        ("bvmul", ChcOp::BvMul),
        ("bvand", ChcOp::BvAnd),
        ("bvor", ChcOp::BvOr),
        ("bvxor", ChcOp::BvXor),
    ] {
        parser.input = format!("({op_name} a b c)");
        parser.pos = 0;
        let expr = parser
            .parse_expr()
            .unwrap_or_else(|e| panic!("ternary {op_name} should parse: {e}"));
        match &expr {
            ChcExpr::Op(op, args) if *op == expected_op => {
                assert_eq!(args.len(), 2, "{op_name} folded should have 2 args");
                assert!(
                    matches!(args[0].as_ref(), ChcExpr::Op(inner_op, inner) if *inner_op == expected_op && inner.len() == 2),
                    "{op_name} first arg should be nested {op_name}"
                );
            }
            _ => panic!("expected {expected_op:?}, got {expr:?}"),
        }
    }

    // Non-left-associative ops reject 3 args
    parser.input = "(bvsub a b c)".to_string();
    parser.pos = 0;
    assert!(
        parser.parse_expr().is_err(),
        "bvsub should reject 3 arguments"
    );

    parser.input = "(bvudiv a b c)".to_string();
    parser.pos = 0;
    assert!(
        parser.parse_expr().is_err(),
        "bvudiv should reject 3 arguments"
    );
}

/// Test #5122: hex and binary BV literal parsing.
/// SMT-LIB 2.6 §3.1: #xABCD = BitVec(width=4*len, value), #b0101 = BitVec(width=len, value).
#[test]
fn test_parse_bv_hex_binary_literals() {
    let mut parser = ChcParser::new();

    // Hex literals
    parser.input = "#xFF".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#xFF should parse");
    assert_eq!(expr, ChcExpr::BitVec(0xFF, 8), "8-bit hex");

    parser.input = "#x0A".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#x0A should parse");
    assert_eq!(
        expr,
        ChcExpr::BitVec(0x0A, 8),
        "8-bit hex with leading zero"
    );

    parser.input = "#xDEAD".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#xDEAD should parse");
    assert_eq!(expr, ChcExpr::BitVec(0xDEAD, 16), "16-bit hex");

    parser.input = "#x00000000".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#x00000000 should parse");
    assert_eq!(expr, ChcExpr::BitVec(0, 32), "32-bit zero hex");

    parser.input = "#xF".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#xF should parse");
    assert_eq!(expr, ChcExpr::BitVec(0xF, 4), "4-bit single hex digit");

    // Binary literals
    parser.input = "#b0101".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#b0101 should parse");
    assert_eq!(expr, ChcExpr::BitVec(0b0101, 4), "4-bit binary");

    parser.input = "#b11111111".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#b11111111 should parse");
    assert_eq!(expr, ChcExpr::BitVec(0xFF, 8), "8-bit binary all ones");

    parser.input = "#b0".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#b0 should parse");
    assert_eq!(expr, ChcExpr::BitVec(0, 1), "1-bit binary zero");

    parser.input = "#b1".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("#b1 should parse");
    assert_eq!(expr, ChcExpr::BitVec(1, 1), "1-bit binary one");

    // Error cases
    parser.input = "#x".to_string();
    parser.pos = 0;
    assert!(parser.parse_expr().is_err(), "empty hex should fail");

    parser.input = "#b".to_string();
    parser.pos = 0;
    assert!(parser.parse_expr().is_err(), "empty binary should fail");

    parser.input = "#z1234".to_string();
    parser.pos = 0;
    assert!(
        parser.parse_expr().is_err(),
        "invalid prefix #z should fail"
    );
}

/// Test #6215: 128-bit hex BV literals that previously caused parse errors.
#[test]
fn test_parse_128bit_bv_hex_literal() {
    let mut parser = ChcParser::new();

    // The exact literal from #6215 that caused the crash
    parser.input = "#x00000000000000040000000000000004".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("128-bit hex literal should parse");
    assert_eq!(
        expr,
        ChcExpr::BitVec(0x00000000000000040000000000000004u128, 128),
        "128-bit hex literal from model-checker-consumer layout descriptors"
    );

    // Another 128-bit value: all ones
    parser.input = "#xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("128-bit all-ones should parse");
    assert_eq!(expr, ChcExpr::BitVec(u128::MAX, 128), "128-bit all-ones");

    // 96-bit value (between 64 and 128)
    parser.input = "#xABCDEF0123456789AABBCCDD".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("96-bit hex should parse");
    assert_eq!(
        expr,
        ChcExpr::BitVec(0xABCDEF0123456789AABBCCDDu128, 96),
        "96-bit hex (24 hex digits)"
    );
}

/// Test #7040: wide BV literals (>128 bits) parse as BvConcat trees.
#[test]
fn test_parse_wide_bv_literal_issue_7040() {
    let mut parser = ChcParser::new();

    // 192-bit hex literal: high 64 bits = 0xAABBCCDDEEFF0011, low 128 bits = 0x2233445566778899AABBCCDDAABB0011
    parser.input = "#xAABBCCDDEEFF00112233445566778899AABBCCDDAABB0011".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("192-bit hex literal should parse");
    // BvConcat(high_64, low_128) — high bits first per SMT-LIB semantics
    match &expr {
        ChcExpr::Op(ChcOp::BvConcat, args) => {
            assert_eq!(args.len(), 2, "192-bit = concat of 2 pieces");
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::BitVec(high_val, 64), ChcExpr::BitVec(low_val, 128)) => {
                    assert_eq!(*high_val, 0xAABBCCDDEEFF0011u128, "high 64 bits");
                    assert_eq!(
                        *low_val, 0x2233445566778899AABBCCDDAABB0011u128,
                        "low 128 bits"
                    );
                }
                (h, l) => panic!("expected (BitVec 64, BitVec 128), got ({h:?}, {l:?})"),
            }
        }
        _ => panic!("expected BvConcat for 192-bit literal, got {expr:?}"),
    }

    // 256-bit: high 128 = 0x00...01, low 128 = 0x00...01
    parser.input = "#x0000000000000000000000000000000100000000000000000000000000000001".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("256-bit hex literal should parse");
    match &expr {
        ChcExpr::Op(ChcOp::BvConcat, args) => match (args[0].as_ref(), args[1].as_ref()) {
            (ChcExpr::BitVec(high_val, 128), ChcExpr::BitVec(low_val, 128)) => {
                assert_eq!(*high_val, 1u128, "high 128 bits = 1");
                assert_eq!(*low_val, 1u128, "low 128 bits = 1");
            }
            (h, l) => panic!("expected (BitVec 128, BitVec 128), got ({h:?}, {l:?})"),
        },
        _ => panic!("expected BvConcat for 256-bit literal"),
    }
}

/// Test #7040 (updated for the i128 widening): large integer literals that
/// fit i128 parse as plain `Int` constants; only beyond-i128 values fall back
/// to Horner addition trees.
#[test]
fn test_parse_large_int_literal_issue_7040() {
    let mut parser = ChcParser::new();

    // 2^64 = 18446744073709551616 (model-checker-consumer pointer arithmetic):
    // i128-lockstep — now a plain Int constant, no encoding tree.
    parser.input = "18446744073709551616".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("2^64 should parse without overflow");
    assert_eq!(expr, ChcExpr::Int(18_446_744_073_709_551_616_i128));

    // u64::MAX (the gap-log #19 type-range literal) is a plain Int.
    parser.input = "18446744073709551615".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("u64::MAX should parse");
    assert_eq!(expr, ChcExpr::Int(u64::MAX as i128));

    // i64::MAX + 1 (old boundary) is a plain Int.
    parser.input = "9223372036854775808".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("i64::MAX+1 should parse");
    assert_eq!(expr, ChcExpr::Int(i128::from(i64::MAX) + 1));

    // i64::MAX still parses as plain Int
    parser.input = "9223372036854775807".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("i64::MAX should parse");
    assert_eq!(expr, ChcExpr::Int(i128::from(i64::MAX)));

    // i128::MAX (new boundary) is a plain Int.
    parser.input = "170141183460469231731687303715884105727".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("i128::MAX should parse");
    assert_eq!(expr, ChcExpr::Int(i128::MAX));

    // i128::MAX + 1 falls back to the Horner addition tree (beyond-i128).
    parser.input = "170141183460469231731687303715884105728".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("i128::MAX+1 should parse");
    match &expr {
        ChcExpr::Op(ChcOp::Add, args) => {
            assert_eq!(args.len(), 2, "beyond-i128 int = add(a, b)");
        }
        _ => panic!("expected Add for i128::MAX+1, got {expr:?}"),
    }
}

/// Test #381: 256-bit integer literals parse without i128 overflow.
#[test]
fn test_parse_256_bit_int_literal_issue_381() {
    let mut parser = ChcParser::new();

    let max_uint256 =
        "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    parser.input = max_uint256.to_string();
    parser.pos = 0;

    let expr = parser
        .parse_expr()
        .expect("uint256 max integer literal should parse");
    let parsed_value = eval_int_literal_tree(&expr).expect("literal tree should be evaluable");
    assert_eq!(
        parsed_value,
        max_uint256.parse::<num_bigint::BigInt>().unwrap()
    );
}

#[test]
fn test_parse_chc_with_256_bit_int_literal_issue_381() {
    let max_uint256 =
        "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    let input = format!(
        r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x {max_uint256}) (Inv x)))
            (query Inv)
        "#
    );

    let problem = ChcParser::parse(&input).expect("CHC problem with uint256 literal should parse");
    assert_eq!(problem.predicates().len(), 1);
    assert_eq!(problem.clauses().len(), 2);
}

fn eval_int_literal_tree(expr: &ChcExpr) -> Option<num_bigint::BigInt> {
    match expr {
        ChcExpr::Int(n) => Some(num_bigint::BigInt::from(*n)),
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut sum = num_bigint::BigInt::from(0);
            for arg in args {
                sum += eval_int_literal_tree(arg)?;
            }
            Some(sum)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut product = num_bigint::BigInt::from(1);
            for arg in args {
                product *= eval_int_literal_tree(arg)?;
            }
            Some(product)
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => Some(-eval_int_literal_tree(&args[0])?),
        _ => None,
    }
}

/// Test #7040: propagate_constants on wide BvConcat (>128-bit) doesn't panic.
#[test]
fn test_wide_bv_concat_propagate_constants_no_panic() {
    let mut parser = ChcParser::new();
    // 192-bit hex literal → BvConcat(high_64, low_128)
    parser.input = "#xAABBCCDDEEFF00112233445566778899AABBCCDDAABB0011".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("192-bit hex literal should parse");
    // propagate_constants must not panic on wide BvConcat
    let simplified = expr.propagate_constants();
    // Should remain a BvConcat (can't fold into u128)
    match &simplified {
        ChcExpr::Op(ChcOp::BvConcat, args) => {
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected BvConcat to be preserved, got {simplified:?}"),
    }
}

/// Test #7040: wide decimal BV literal (_ bvN W) where N > u128::MAX.
#[test]
fn test_parse_wide_decimal_bv_literal_issue_7040() {
    let mut parser = ChcParser::new();

    // (_ bv340282366920938463463374607431768211456 256)
    // = 2^128, which is u128::MAX + 1
    // Expected: BvConcat(high_128=1, low_128=0)
    parser.input = "(_ bv340282366920938463463374607431768211456 256)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("(_ bv<2^128> 256) should parse");
    match &expr {
        ChcExpr::Op(ChcOp::BvConcat, args) => {
            assert_eq!(args.len(), 2, "256-bit = concat of 2 pieces");
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::BitVec(high_val, 128), ChcExpr::BitVec(low_val, 128)) => {
                    assert_eq!(*high_val, 1u128, "high 128 bits = 1");
                    assert_eq!(*low_val, 0u128, "low 128 bits = 0");
                }
                (h, l) => panic!("expected (BitVec 128, BitVec 128), got ({h:?}, {l:?})"),
            }
        }
        _ => panic!("expected BvConcat for (_ bv<2^128> 256), got {expr:?}"),
    }

    // (_ bv42 8) — small value, fast path still works
    parser.input = "(_ bv42 8)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("(_ bv42 8) should parse");
    assert_eq!(expr, ChcExpr::BitVec(42, 8));

    // (_ bv<u128::MAX> 128) — boundary, u128 fast path
    parser.input = "(_ bv340282366920938463463374607431768211455 128)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("(_ bv<u128::MAX> 128) should parse");
    assert_eq!(expr, ChcExpr::BitVec(u128::MAX, 128));

    // A small numerical value with a wide declared width still uses the exact
    // wide representation, so every >128-bit literal has one canonical shape.
    parser.input = "(_ bv1 129)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("(_ bv1 129) should parse");
    match &expr {
        ChcExpr::Op(ChcOp::BvConcat, args) => {
            assert_eq!(args.len(), 2);
            assert_eq!(args[0].as_ref(), &ChcExpr::BitVec(0, 1));
            assert_eq!(args[1].as_ref(), &ChcExpr::BitVec(1, 128));
        }
        _ => panic!("expected canonical BvConcat for (_ bv1 129), got {expr:?}"),
    }
}

/// Test #5122: hex/binary BV literals in compound expressions.
#[test]
fn test_parse_bv_literals_in_expressions() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::BitVec(8));

    // BV literal in bvadd
    parser.input = "(bvadd x #xFF)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("bvadd with hex literal should parse");
    match &expr {
        ChcExpr::Op(ChcOp::BvAdd, args) => {
            assert_eq!(args.len(), 2);
            assert_eq!(*args[1], ChcExpr::BitVec(0xFF, 8));
        }
        _ => panic!("expected BvAdd, got {expr:?}"),
    }

    // BV literal in comparison
    parser.input = "(bvult x #b00001010)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("bvult with binary literal should parse");
    match &expr {
        ChcExpr::Op(ChcOp::BvULt, args) => {
            assert_eq!(args.len(), 2);
            assert_eq!(*args[1], ChcExpr::BitVec(10, 8));
        }
        _ => panic!("expected BvULt, got {expr:?}"),
    }
}

/// Regression test for #6116: bv2int must parse as Bv2Nat (unsigned conversion).
#[test]
fn test_parse_bv2int_as_bv2nat() {
    let mut parser = ChcParser::new();
    parser.input = "(bv2int #x0000000A)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("bv2int should parse");
    match &expr {
        ChcExpr::Op(ChcOp::Bv2Nat, args) => {
            assert_eq!(args.len(), 1);
            assert_eq!(*args[0], ChcExpr::BitVec(10, 32));
        }
        _ => panic!("expected Bv2Nat, got {expr:?}"),
    }
}

#[test]
fn test_parse_bv2nat_unchanged() {
    let mut parser = ChcParser::new();
    parser.input = "(bv2nat #b1010)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("bv2nat should parse");
    match &expr {
        ChcExpr::Op(ChcOp::Bv2Nat, args) => {
            assert_eq!(args.len(), 1);
            assert_eq!(*args[0], ChcExpr::BitVec(10, 4));
        }
        _ => panic!("expected Bv2Nat, got {expr:?}"),
    }
}

/// Regression test for #6536: bvsdiv_i should use operand width, not fabricated 32.
#[test]
fn test_parse_bvsdiv_i_uses_operand_width_not_32_6536() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::BitVec(8));
    parser.variables.insert("y".to_string(), ChcSort::BitVec(8));
    parser.input = "(bvsdiv_i x y)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("bvsdiv_i should parse");
    // The desugaring is: ite(y=0, ite(slt(x,0), 1, -1), bvsdiv(x,y))
    // All BV literals must be 8-bit, not 32-bit.
    fn check_no_32bit_literals(e: &ChcExpr) {
        match e {
            ChcExpr::BitVec(_, w) => {
                assert_ne!(*w, 32, "found fabricated 32-bit literal in bvsdiv_i output");
                assert_eq!(*w, 8, "expected 8-bit literal, got {w}-bit");
            }
            ChcExpr::Op(_, args) => {
                for a in args {
                    check_no_32bit_literals(a);
                }
            }
            _ => {}
        }
    }
    check_no_32bit_literals(&expr);
}

/// Regression test for #7040: bvudiv_i with 192-bit operands must not panic.
#[test]
fn test_parse_bvudiv_i_wide_192bit_no_panic_7040() {
    let mut parser = ChcParser::new();
    parser
        .variables
        .insert("x".to_string(), ChcSort::BitVec(192));
    parser
        .variables
        .insert("y".to_string(), ChcSort::BitVec(192));
    parser.input = "(bvudiv_i x y)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("bvudiv_i 192-bit should parse");
    // The all-ones default value must be a BvConcat tree, not a single BitVec
    fn has_bvconcat(e: &ChcExpr) -> bool {
        match e {
            ChcExpr::Op(ChcOp::BvConcat, _) => true,
            ChcExpr::Op(_, args) => args.iter().any(|a| has_bvconcat(a)),
            _ => false,
        }
    }
    assert!(
        has_bvconcat(&expr),
        "192-bit bvudiv_i should produce BvConcat tree for all-ones default"
    );
}

/// Regression test for #7040: bvsdiv_i with 192-bit operands must not panic.
#[test]
fn test_parse_bvsdiv_i_wide_192bit_no_panic_7040() {
    let mut parser = ChcParser::new();
    parser
        .variables
        .insert("x".to_string(), ChcSort::BitVec(192));
    parser
        .variables
        .insert("y".to_string(), ChcSort::BitVec(192));
    parser.input = "(bvsdiv_i x y)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("bvsdiv_i 192-bit should parse");
    fn has_bvconcat(e: &ChcExpr) -> bool {
        match e {
            ChcExpr::Op(ChcOp::BvConcat, _) => true,
            ChcExpr::Op(_, args) => args.iter().any(|a| has_bvconcat(a)),
            _ => false,
        }
    }
    assert!(
        has_bvconcat(&expr),
        "192-bit bvsdiv_i should produce BvConcat tree for all-ones neg_one"
    );
}

/// Regression test for #6536: bvsrem_i with unknown-width operands should fail.
#[test]
fn test_parse_bvsrem_i_unknown_width_errors_6536() {
    let mut parser = ChcParser::new();
    // Variables with Int sort — not BV, so width inference should fail.
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("y".to_string(), ChcSort::Int);
    parser.input = "(bvsrem_i x y)".to_string();
    parser.pos = 0;
    let result = parser.parse_expr();
    assert!(
        result.is_err(),
        "bvsrem_i with non-BV operands should return parse error"
    );
}

#[test]
fn safe_division_uses_the_sort_of_a_wide_literal_tree() {
    let mut parser = ChcParser::new();
    let high_bit = (num_bigint::BigUint::from(1_u8) << 128_usize).to_str_radix(10);
    parser.input = format!("(bvsdiv_i (_ bv{high_bit} 129) (_ bv1 129))");
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("wide literal safe division should parse");
    assert_eq!(expr.sort(), ChcSort::BitVec(129));
}

#[test]
fn raw_bv_literals_and_indexed_results_obey_the_shared_width_cap() {
    let mut parser = ChcParser::new();
    parser.input = format!("#b{}", "0".repeat(crate::MAX_BITVECTOR_WIDTH as usize + 1));
    parser.pos = 0;
    assert!(parser.parse_expr().is_err());

    parser
        .variables
        .insert("x".to_string(), ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH));
    parser.variables.insert("y".to_string(), ChcSort::BitVec(1));
    parser.input = "((_ zero_extend 1) x)".to_string();
    parser.pos = 0;
    assert!(parser.parse_expr().is_err());

    parser.input = "((_ repeat 0) x)".to_string();
    parser.pos = 0;
    assert!(parser.parse_expr().is_err());
    parser.input = "((_ int2bv 0) 1)".to_string();
    parser.pos = 0;
    assert!(parser.parse_expr().is_err());

    parser.input = "(concat x y)".to_string();
    parser.pos = 0;
    assert!(parser.parse_expr().is_err());

    parser.input = "(concat #b1 #b0 #b1)".to_string();
    parser.pos = 0;
    let concat = parser
        .parse_expr()
        .expect("the parser's variadic concat extension folds to binary AST nodes");
    assert_eq!(concat.sort(), ChcSort::BitVec(3));
    assert!(matches!(
        concat,
        ChcExpr::Op(ChcOp::BvConcat, ref args)
            if args.len() == 2
                && matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::BvConcat, inner) if inner.len() == 2)
    ));
}
