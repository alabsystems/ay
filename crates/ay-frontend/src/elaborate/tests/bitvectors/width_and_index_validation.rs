// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `elaborate::tests::bitvectors` to preserve test FQNs.

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
