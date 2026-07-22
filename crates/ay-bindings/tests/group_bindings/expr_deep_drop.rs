// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
//! Memory safety tests for deeply nested Expr/ExprValue trees.
//!
//! The ay-bindings `Expr` type uses the default recursive Drop via
//! `Arc<ExprValue>`. Unlike `ChcExpr` (which has `iterative_drop()`
//! at ay-chc/src/expr.rs:431), `Expr` has no iterative drop mitigation.
//!
//! For depth > ~8K on a 512KB stack, dropping a deep Expr tree causes
//! SIGABRT (stack overflow). Verified empirically.
//!
//! Tracked by: #2495

use ay_bindings::expr::{Expr, ExprValue};

/// Documents the missing iterative drop for deeply nested Expr trees.
///
/// Builds a depth-400 right-skewed Not chain and uses `mem::forget` to
/// avoid recursive drop overflow. This mirrors the ChcExpr test pattern
/// at ay-chc/src/lib.rs:506.
///
/// When `Expr::iterative_drop()` is implemented, replace `mem::forget`
/// with an explicit iterative_drop call and raise depth to 10,000+.
#[test]
fn deep_expr_tree_documents_missing_iterative_drop() {
    // Build a deeply nested Not chain: Not(Not(Not(...(true)...)))
    // Depth 10_000 overflows a 512KB stack on drop (verified via SIGABRT).
    // Depth 400 is safe on default stacks but documents the pattern.
    let depth = 400;
    let mut expr = Expr::bool_const(true);
    for _ in 0..depth {
        expr = expr.not();
    }

    // Verify the tree was actually built to the expected depth.
    // Use references to avoid O(depth) ExprValue clones.
    let mut current_value: &ExprValue = expr.value();
    let mut measured_depth = 0;
    while let ExprValue::Not(inner) = current_value {
        measured_depth += 1;
        current_value = inner.value();
    }
    assert_eq!(measured_depth, depth);

    // Leak to avoid recursive Drop overflow (#2495).
    // When Expr gains an iterative_drop(), this mem::forget should be
    // replaced with an explicit iterative_drop() call, and the depth
    // should be raised to 10_000+ to match ChcExpr stress tests.
    std::mem::forget(expr);
}

/// Verify that shallow Expr trees drop safely on a small (512KB) stack.
/// Control case for the deep drop test above.
#[test]
fn shallow_expr_drop_is_safe() {
    let depth = 100;
    let mut expr = Expr::bool_const(true);
    for _ in 0..depth {
        expr = expr.not();
    }

    let result = std::thread::Builder::new()
        .name("shallow-drop-test".into())
        .stack_size(512 * 1024)
        .spawn(move || {
            drop(expr);
        })
        .expect("thread spawn failed")
        .join();

    assert!(result.is_ok(), "Shallow Expr drop should never overflow");
}
