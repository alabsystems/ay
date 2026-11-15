// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A small raw store-chain candidate for the existing wire-first proof repair.
//! This selects a question only. The renderer, native checker, full strict
//! replay, authored round trip and premise-scope checks still decide it.

use super::*;

impl Executor {
    pub(super) fn is_bounded_const_array_root(&self, root: TermId) -> bool {
        // Stay inside the packed circuit's existing source-node envelope.
        const MAX_NODES: usize = 512;
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut pending = vec![root];
        let mut has_array = false;
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_NODES {
                return false;
            }
            match self.ctx.terms.sort(term) {
                Sort::Bool => (),
                Sort::BitVec(width) if (1..=128).contains(&width.width) => (),
                Sort::Array(shape) => {
                    has_array = true;
                    if !matches!((&shape.index_sort, &shape.element_sort),
                        (Sort::BitVec(index), Sort::BitVec(value))
                        if (1..=128).contains(&index.width) && (1..=128).contains(&value.width))
                    {
                        return false;
                    }
                    // No arbitrary array base, nested array, or array-valued
                    // branch may turn the old broad-frame decline into a blast.
                    match self.ctx.terms.get(term) {
                        TermData::App(Symbol::Named(op), args)
                            if op == "const-array" && args.len() == 1 =>
                        {
                            ()
                        }
                        TermData::App(Symbol::Named(op), args)
                            if op == "store" && args.len() == 3 =>
                        {
                            ()
                        }
                        _ => return false,
                    }
                }
                _ => return false,
            }
            pending.extend(self.ctx.terms.children(term));
        }
        has_array
    }
}
