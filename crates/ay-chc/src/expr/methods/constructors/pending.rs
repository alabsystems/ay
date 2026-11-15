// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Flattening worklist item for `and_all` / `or_all` (WP-F F0a).

use std::sync::Arc;

use ay_core::kani_compat::DetHashSet as FxHashSet;

use super::ChcExpr;
use crate::expr::intern::arc as mk_arc;

/// A conjunct/disjunct awaiting flattening in [`ChcExpr::and_all_checked`] /
/// [`ChcExpr::or_all`]: either a caller-supplied value or a child `Arc` of a
/// flattened node, kept as that same `Arc` so its sharing survives (F0a).
pub(super) enum Pending {
    Owned(ChcExpr),
    Shared(Arc<ChcExpr>),
}

impl Pending {
    pub(super) fn as_expr(&self) -> &ChcExpr {
        match self {
            Self::Owned(expr) => expr,
            Self::Shared(arc) => arc,
        }
    }

    pub(super) fn into_arc(self) -> Arc<ChcExpr> {
        match self {
            Self::Owned(expr) => mk_arc(expr),
            Self::Shared(arc) => arc,
        }
    }
}

/// The shared `and`/`or` nodes a flattening has already expanded.
///
/// Expanding a shared node a second time adds nothing: every operand it holds
/// was already deduplicated into the output (or already short-circuited the
/// result), so the flattening skips it. Without this, flattening a DAG whose
/// `and` spine shares nodes walked every tree occurrence — measured on
/// om1_with_relays_general_3_9 (LRA-Lin) as PDKIND's k-step background
/// conjunction growing to gigabytes in `IncrementalQueryContext`. The nodes
/// are kept alive so their addresses cannot be reused while the flattening
/// runs.
#[derive(Default)]
pub(super) struct FlattenedNodes {
    seen: FxHashSet<*const ChcExpr>,
    alive: Vec<Arc<ChcExpr>>,
}

impl FlattenedNodes {
    /// Whether `item` is expanded for the first time. An owned operand is
    /// never shared, so it always is.
    pub(super) fn first_visit(&mut self, item: &Pending) -> bool {
        let Pending::Shared(arc) = item else {
            return true;
        };
        if !self.seen.insert(Arc::as_ptr(arc)) {
            return false;
        }
        self.alive.push(Arc::clone(arc));
        true
    }
}
