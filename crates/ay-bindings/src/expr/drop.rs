// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Iterative Drop implementation for Expr to prevent stack overflow (#8414).
//!
//! `Expr` wraps `Arc<ExprValue>` where `ExprValue` contains child `Expr` nodes.
//! The default recursive Drop would overflow the stack on deeply nested trees
//! (e.g., chains of `Not(Not(Not(...)))` or nested DT selectors). This is fatal:
//! SIGABRT, not catchable by `catch_unwind`. `stacker::maybe_grow` cannot protect
//! `Drop::drop` because `drop` is invoked by the runtime.
//!
//! The fix: when we are the sole owner of an `Arc<ExprValue>`, extract children
//! into a work queue and drop them iteratively instead of recursively.

use std::mem;
use std::sync::Arc;

use super::{Expr, ExprValue};

impl Drop for Expr {
    fn drop(&mut self) {
        // Fast path: if we are not the sole owner of this Arc, the inner
        // ExprValue will survive this drop — no children to handle.
        // This covers the common case where Exprs are shared via Arc::clone.
        if Arc::strong_count(&self.value) != 1 {
            return;
            // The default Arc drop decrements the refcount. Since we return
            // without doing anything special, Rust will still drop self.value
            // (the Arc field) normally after our Drop::drop returns.
        }

        // We are the sole owner. Replace the Arc with a cheap leaf to prevent
        // the default recursive drop from running on the original tree.
        let leaf = Arc::new(ExprValue::BoolConst(false));
        let original_arc = mem::replace(&mut self.value, leaf);

        // Try to unwrap the Arc. Since strong_count was 1, this should succeed
        // unless a weak reference was upgraded between the count check and here.
        let inner = match Arc::try_unwrap(original_arc) {
            Ok(val) => val,
            Err(_arc) => {
                // Rare race: a weak ref was upgraded. Let normal drop handle it.
                // The tree is already detached from self (we replaced with leaf),
                // so we need to put it back or just let the Arc drop normally.
                // Dropping the Arc here is safe — the extra reference means no
                // deep recursion (someone else also holds the children).
                return;
            }
        };

        // Extract owned children and drop them iteratively.
        let mut work = inner.into_children_vec();
        while let Some(mut child) = work.pop() {
            // Same logic: only recurse into sole-owner Arcs
            if Arc::strong_count(&child.value) == 1 {
                let child_leaf = Arc::new(ExprValue::BoolConst(false));
                let child_arc = mem::replace(&mut child.value, child_leaf);
                if let Ok(child_inner) = Arc::try_unwrap(child_arc) {
                    work.extend(child_inner.into_children_vec());
                }
            }
            // child drops here with either the leaf (no recursion) or
            // the original Arc (shared, so refcount decrement only)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sort::Sort;

    /// Build a deeply nested Expr chain: Not(Not(Not(... Var("x") ...)))
    fn build_deep_not_chain(depth: usize) -> Expr {
        let mut expr = Expr::var("x".to_string(), Sort::bool());
        for _ in 0..depth {
            expr = Expr {
                sort: Sort::bool(),
                value: Arc::new(ExprValue::Not(expr)),
            };
        }
        expr
    }

    #[test]
    fn test_deep_expr_drop_no_stack_overflow() {
        // On a typical 8MB stack, recursive drop of ~100K nodes would overflow.
        // The iterative drop handles this without issue.
        let deep = build_deep_not_chain(200_000);
        drop(deep);
        // If we get here without SIGABRT, the iterative drop works.
    }

    #[test]
    fn test_shared_expr_drop_does_not_destroy_shared() {
        let leaf = Expr::var("x".to_string(), Sort::bool());
        let shared = Expr {
            sort: Sort::bool(),
            value: Arc::new(ExprValue::Not(leaf)),
        };
        let cloned = shared.clone();
        drop(shared);
        // cloned should still be valid
        assert!(matches!(cloned.value(), ExprValue::Not(_)));
    }

    #[test]
    fn test_deep_binary_tree_drop() {
        // Build a deep Eq chain: Eq(Eq(Eq(... x ..., y), y), y)
        let x = Expr::var("x".to_string(), Sort::int());
        let y = Expr::var("y".to_string(), Sort::int());
        let mut expr = x;
        for _ in 0..100_000 {
            expr = Expr {
                sort: Sort::bool(),
                value: Arc::new(ExprValue::Eq(expr, y.clone())),
            };
        }
        drop(expr);
    }
}
