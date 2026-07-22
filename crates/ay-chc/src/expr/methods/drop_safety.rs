// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deep-tree drop safety for ChcExpr.

use std::sync::Arc;

use super::ChcExpr;

impl Drop for ChcExpr {
    /// Iterative drop prevents stack overflow on deeply nested expression trees.
    ///
    /// When an `Arc<ChcExpr>` is the last reference and gets dropped, Rust's
    /// default recursive destructor follows the tree to its leaves — one stack
    /// frame per node. For PDKind/BMC unrollings (500K+ depth), this overflows
    /// any fixed-size stack, including 128MB debug stacks (SIGBUS on #8544).
    ///
    /// This Drop impl extracts uniquely-owned Arc children into a local worklist
    /// before the compiler's field-drop phase runs. After extraction, the node's
    /// Vec/Arc fields are empty/dummy, so compiler-generated drops are trivial.
    /// Re-entrant calls (from worklist-popped nodes) find nothing and return.
    fn drop(&mut self) {
        // Fast path: leaf nodes have no Arc<ChcExpr> children.
        match self {
            Self::Bool(_)
            | Self::Int(_)
            | Self::Real(_, _)
            | Self::BitVec(_, _)
            | Self::Var(_)
            | Self::ConstArrayMarker(_)
            | Self::IsTesterMarker(_) => return,
            _ => {}
        }

        let mut worklist: Vec<Self> = Vec::new();
        Self::extract_children_for_drop(self, &mut worklist);
        // self's children are now drained; compiler field-drops are trivial.
        while let Some(mut node) = worklist.pop() {
            Self::extract_children_for_drop(&mut node, &mut worklist);
            // node drops here as a leaf (children already extracted).
            // Re-enters Drop, but fast-path returns since children are gone.
        }
    }
}

impl ChcExpr {
    /// Explicit iterative drop — legacy API for existing call sites.
    ///
    /// With `impl Drop for ChcExpr`, this is redundant: just letting a value
    /// go out of scope achieves the same iterative drop. Retained to avoid
    /// churn at 32 existing call sites; these can be simplified to `drop(x)`
    /// in a future cleanup pass.
    pub fn iterative_drop(root: Self) {
        drop(root);
    }

    /// Extract uniquely-owned children from `node` into `worklist`, leaving
    /// `node` as a childless shell that can be dropped without recursion.
    fn extract_children_for_drop(node: &mut Self, worklist: &mut Vec<Self>) {
        match node {
            Self::Op(_, children)
            | Self::PredicateApp(_, _, children)
            | Self::FuncApp(_, _, children) => {
                for arc in children.drain(..) {
                    if let Ok(inner) = Arc::try_unwrap(arc) {
                        worklist.push(inner);
                    }
                    // else: shared Arc, refcount decremented, no deep recursion
                }
            }
            Self::ConstArray(_ks, arc) => {
                let taken = std::mem::replace(arc, Arc::new(Self::Bool(false)));
                if let Ok(inner) = Arc::try_unwrap(taken) {
                    worklist.push(inner);
                }
            }
            Self::Bool(_)
            | Self::Int(_)
            | Self::Real(_, _)
            | Self::BitVec(_, _)
            | Self::Var(_)
            | Self::ConstArrayMarker(_)
            | Self::IsTesterMarker(_) => {}
        }
    }
}
