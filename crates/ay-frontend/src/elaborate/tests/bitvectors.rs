// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_elaborate_bitvector() {
    let input = r#"
            (declare-const x (_ BitVec 32))
            (assert (= x #x0000FFFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn invalid_or_excessive_bitvector_widths_fail_before_allocation() {
    for input in [
        "(declare-const x (_ BitVec 0))",
        "(declare-const x (_ BitVec 1048577))",
        "(assert (= (_ bv0 0) (_ bv0 0)))",
        "(declare-const x (_ BitVec 2)) (assert (= ((_ repeat 600000) x) x))",
        "(declare-const x (_ BitVec 600000)) (declare-const y (_ BitVec 600000)) (assert (= (concat x y) x))",
        "(assert (= ((_ zero_extend 1048576) 1) 1))",
        "(assert (= ((_ repeat 1048576) 1) 1))",
    ] {
        let commands = parse(input).expect("syntax parses");
        let mut ctx = Context::new();
        let result = commands
            .iter()
            .try_for_each(|cmd| ctx.process_command(cmd).map(|_| ()));
        assert!(result.is_err(), "expected width rejection for {input}");
    }
}

#[test]
fn bitvector_apps_reject_non_bitvector_operands_before_core_builders() {
    for input in [
        "(assert (= (concat true #b0) #b0))",
        "(assert (= (concat #b0 #b1 true) #b01))",
        "(assert (= (bvadd true false) true))",
        "(assert (= (bvnot true) true))",
        "(assert (= (bv2nat true) 0))",
    ] {
        let commands = parse(input).expect("syntax parses");
        let mut ctx = Context::new();
        let error = commands
            .iter()
            .try_for_each(|command| ctx.process_command(command).map(|_| ()))
            .expect_err("non-BitVec operands must be rejected during elaboration");
        assert!(error.to_string().contains("BitVec"), "{input}: {error}");
    }
}

#[test]
fn structured_indexed_path_rejects_invalid_extract_bounds() {
    use crate::command::{Index, Term};

    let commands = parse("(declare-const x (_ BitVec 8))").unwrap();
    let mut ctx = Context::new();
    ctx.process_command(&commands[0]).unwrap();
    let env = ay_core::kani_compat::DetHashMap::default();

    let term = Term::IndexedApp(
        "extract".to_string(),
        vec![
            Index::Numeral("0".to_string()),
            Index::Numeral("1".to_string()),
        ],
        vec![Term::Symbol("x".to_string())],
    );
    let error = ctx
        .elaborate_term(&term, &env)
        .expect_err("inverted extract bounds must be rejected");
    assert!(error.to_string().contains("below low index"), "{error}");
}

#[test]
fn structured_indexed_path_rejects_wrong_operand_sorts() {
    use crate::command::{Constant as ParsedConstant, Index, Term};

    let env = ay_core::kani_compat::DetHashMap::default();
    for (name, indices, operand) in [
        (
            "int2bv",
            vec!["8".to_string()],
            Term::Const(ParsedConstant::True),
        ),
        (
            "rotate_left",
            vec!["1".to_string()],
            Term::Const(ParsedConstant::Numeral("1".to_string())),
        ),
        (
            "rotate_right",
            vec!["1".to_string()],
            Term::Const(ParsedConstant::Numeral("1".to_string())),
        ),
    ] {
        let term = Term::IndexedApp(
            name.to_string(),
            indices.into_iter().map(Index::Numeral).collect(),
            vec![operand],
        );
        let mut ctx = Context::new();
        let error = ctx
            .elaborate_term(&term, &env)
            .expect_err("wrong-sort indexed operand must be rejected");
        assert!(
            matches!(error, ElaborateError::SortMismatch { .. }),
            "{name}: {error}"
        );
    }
}

#[test]
fn indexed_parser_rejects_invalid_or_missing_indices() {
    for input in [
        "(assert (= ((_ extract 7 0 1.5) #x00) #x00))",
        "(assert (= (_ bv0 8 1.5) #x00))",
        "(assert (_))",
        "(assert (_ bv0))",
        "(assert ((_ extract) #x00))",
        "(assert (= ((_ bv0 8)) #x00))",
    ] {
        assert!(
            parse(input).is_err(),
            "malformed indexed term parsed: {input}"
        );
    }
}

#[test]
fn quoted_numeric_indices_do_not_become_numeric_tokens() {
    for input in [
        "(assert (= (_ bv0 |8|) #x00))",
        "(assert (= (_ Char |65|) 65))",
        "(assert (= (_ char |#x41|) 65))",
        "(assert (= (_ +zero |8| 24) (_ +zero 8 24)))",
        "(assert (= ((_ extract |7| 0) #xff) #xff))",
        "(declare-const x (_ BitVec |8|))",
        "(declare-const x (_ FloatingPoint |8| 24))",
    ] {
        let commands = parse(input).expect("quoted index syntax parses");
        let mut ctx = Context::new();
        assert!(
            ctx.process_command(&commands[0]).is_err(),
            "quoted numeric index was treated as a numeral: {input}"
        );
    }
}

/// Test for #924: bitvector numeral syntax (_ bvN w)
/// SMT-LIB 2.6 Section 3.5 defines this as equivalent to #x/#b forms.
#[test]
fn test_elaborate_bv_numeral_syntax_924() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            ; (_ bv255 8) should equal #xFF
            (assert (= (_ bv255 8) #xFF))
            ; (_ bv7 3) should equal #b111
            (assert (= (_ bv7 3) #b111))
            ; (_ bv0 1) should equal #b0
            (assert (= (_ bv0 1) #b0))
            ; (_ bv1 1) should equal #b1
            (assert (= (_ bv1 1) #b1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    // Should have 4 assertions (all equivalences)
    assert_eq!(ctx.assertions.len(), 4);
}

#[test]
fn test_elaborate_bv_extract() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ extract 7 4) x) #xF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_concat() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (concat x y) #x0FF0))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_zero_extend() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ zero_extend 8) x) #x00FF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_sign_extend() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ sign_extend 8) x) #xFFFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv_rotate() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= ((_ rotate_left 2) x) #xAA))
            (assert (= ((_ rotate_right 2) x) #x55))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_elaborate_bv_repeat() {
    let input = r#"
            (declare-const x (_ BitVec 4))
            (assert (= ((_ repeat 4) x) #xAAAA))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvsdiv() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvsdiv x y) #xFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvsrem() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvsrem x y) #x01))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvsmod() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvsmod x y) #x02))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bvcomp() {
    let input = r#"
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvcomp x y) #b1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_elaborate_bv2nat_and_int2bv() {
    let input = r#"
            (assert (= (bv2nat #x0F) 15))
            (assert (= ((_ int2bv 8) (- 1)) #xFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 2);
}

#[test]
fn test_elaborate_bvnand_bvnor_bvxnor() {
    let input = r#"
            (assert (= (bvnand #xFF #xFF) #x00))
            (assert (= (bvnor #x00 #x00) #xFF))
            (assert (= (bvxnor #x0F #x0F) #xFF))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd).unwrap();
    }

    assert_eq!(ctx.assertions.len(), 3);
}

#[test]
fn test_bv_left_associative_nary_ops() {
    // SMT-LIB 2.6: bvadd, bvmul, bvand, bvor, bvxor are left-associative
    // (bvadd x y z) should desugar to (bvadd (bvadd x y) z)
    let input = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (declare-const z (_ BitVec 8))
            (assert (= (bvadd x y z) (bvadd (bvadd x y) z)))
            (assert (= (bvmul x y z) (bvmul (bvmul x y) z)))
            (assert (= (bvand x y z) (bvand (bvand x y) z)))
            (assert (= (bvor x y z) (bvor (bvor x y) z)))
            (assert (= (bvxor x y z) (bvxor (bvxor x y) z)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("n-ary BV op should elaborate");
    }

    // 5 assertions, all should parse successfully
    assert_eq!(ctx.assertions.len(), 5);
}

#[test]
fn test_bv_left_associative_4args() {
    // 4-argument case: (bvadd a b c d) => (bvadd (bvadd (bvadd a b) c) d)
    let input = r#"
            (set-logic QF_BV)
            (declare-const a (_ BitVec 8))
            (declare-const b (_ BitVec 8))
            (declare-const c (_ BitVec 8))
            (declare-const d (_ BitVec 8))
            (assert (= (bvadd a b c d) (bvadd (bvadd (bvadd a b) c) d)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("4-arg bvadd should elaborate");
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_bv_binary_still_works() {
    // Binary (2-arg) BV ops should still work as before
    let input = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= (bvadd x y) (bvor x y)))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("binary BV op should still work");
    }

    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_bv_width_mismatch_rejected_not_panicked() {
    // Regression: `#x1` is a 4-bit literal while `x` is 8-bit, so
    // `(bvadd x #x1)` is ill-typed. Previously this fed a width-mismatched
    // term to the core builders and tripped a debug_assert
    // ("BUG: bvadd expects same-width BitVec args"), crashing with exit 101.
    // It must now elaborate to a clean SortMismatch error instead.
    for op in [
        "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor", "bvshl",
        "bvlshr", "bvashr", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvcomp", "bvult",
        "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
    ] {
        // Bind the ill-typed op result via `let` so the surrounding
        // assertion stays well-formed regardless of the op's result sort —
        // we only care that constructing `({op} x #x1)` errors cleanly. The
        // body uses `r` (`(= r r)`, sort-agnostic) so the binding is LIVE: the
        // dead-binding elimination in the `let` elaborator (#arr_lia561) would
        // otherwise skip an unused binding and never elaborate the ill-typed op.
        let input =
            format!("(declare-const x (_ BitVec 8))(assert (let ((r ({op} x #x1))) (= r r)))");
        let commands = parse(&input).unwrap_or_else(|e| panic!("parse failed for {op}: {e:?}"));
        let mut ctx = Context::new();
        let mut found_err = false;
        for cmd in &commands {
            if let Err(e) = ctx.process_command(cmd) {
                assert!(
                    matches!(e, ElaborateError::SortMismatch { .. }),
                    "expected SortMismatch for {op}, got: {e:?}"
                );
                found_err = true;
            }
        }
        assert!(found_err, "expected width-mismatch error for {op}");
    }
}

#[test]
fn test_bv_same_width_ops_still_elaborate() {
    // Well-typed (same-width) versions of the width-sensitive ops must keep
    // elaborating successfully — the new guard must not reject valid input.
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= (bvadd x #x01) #x00))
            (assert (= (bvshl x #x03) #x00))
            (assert (= (bvlshr x #x01) #x00))
            (assert (bvult x #x10))
            (assert (= (bvcomp x #x05) #b1))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("same-width BV ops should elaborate");
    }
    assert_eq!(ctx.assertions.len(), 5);
}

#[test]
fn test_bv_concat_different_widths_still_allowed() {
    // `concat` is intentionally NOT width-sensitive: it joins BitVecs of
    // differing widths. The new guard must not reject it.
    let input = r#"
            (declare-const x (_ BitVec 8))
            (assert (= (concat x #x1) #x000))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();
    for cmd in &commands {
        ctx.process_command(cmd)
            .expect("concat of differing widths should elaborate");
    }
    assert_eq!(ctx.assertions.len(), 1);
}

#[test]
fn test_bv_nary_rejects_unary() {
    // Even left-associative ops require at least 2 arguments
    let input = r#"
            (set-logic QF_BV)
            (declare-const x (_ BitVec 8))
            (assert (= (bvadd x) x))
        "#;
    let commands = parse(input).unwrap();
    let mut ctx = Context::new();

    let mut found_error = false;
    for cmd in &commands {
        if let Err(e) = ctx.process_command(cmd) {
            assert!(
                format!("{e:?}").contains("at least 2 arguments"),
                "Expected 'at least 2 arguments' error, got: {e:?}"
            );
            found_error = true;
        }
    }
    assert!(found_error, "Expected error for unary bvadd");
}

#[test]
fn test_indexed_bad_numeral_index_reports_index_not_arity() {
    // Regression: unparseable or u32-overflowing indices used to be silently
    // dropped by filter_map, so `((_ extract 4294967296 0) x)` (exactly 2
    // indices, one overflowing u32) was rejected with the misleading arity
    // message "extract requires 2 indices and 1 argument". The error must
    // name the offending index instead.
    for bad_idx in ["4294967296", "a"] {
        let input =
            format!("(declare-const x (_ BitVec 8))(assert (= ((_ extract {bad_idx} 0) x) #b0))");
        let commands = parse(&input).unwrap();
        let mut ctx = Context::new();
        let mut found_err = false;
        for cmd in &commands {
            if let Err(e) = ctx.process_command(cmd) {
                let msg = format!("{e}");
                assert!(
                    msg.contains(&format!("index '{bad_idx}'")) && msg.contains("u32"),
                    "expected bad-index message naming '{bad_idx}', got: {msg}"
                );
                found_err = true;
            }
        }
        assert!(found_err, "expected error for index {bad_idx}");
    }
}
