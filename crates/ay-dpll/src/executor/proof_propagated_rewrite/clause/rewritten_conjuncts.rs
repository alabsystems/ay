// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Project an exact conjunct only after deriving its recorded rewritten root.

use super::*;

const MAX_REWRITTEN_CONJUNCT_DEPTH: usize = 64;

struct PathNode {
    term: TermId,
    parent: Option<(usize, u32)>,
    depth: usize,
}

impl PropagationChainPlanner<'_> {
    /// Flattening need not record a separate rewrite for every unit. The
    /// after-root is a discovery hint, never an assumption: ordinary stamped
    /// replay must derive it before checked `and_pos` projects its child.
    pub(super) fn plan_rewritten_conjunct(
        &mut self,
        cx: &mut PlanCx<'_>,
        target: TermId,
    ) -> Option<ProofId> {
        // Bound the new recursive parent search independently of record
        // cycles, which the existing `in_progress` set already rejects.
        if cx.in_progress.len() >= MAX_REWRITTEN_CONJUNCT_DEPTH {
            return None;
        }
        cx.spend(cx.record_by_after.len())?;
        let mut parents: Vec<_> = cx.record_by_after.keys().copied().collect();
        parents.sort_unstable_by_key(|term| term.index());
        for parent in parents {
            if parent == target || cx.in_progress.contains(&parent) {
                continue;
            }
            let AndPath::Found(path) = self.rewritten_conjunct_path(cx, parent, target)? else {
                continue;
            };
            cx.spend(path.len().checked_mul(2)?)?;
            let mark = cx.mark();
            if let Some(parent_id) = self.plan_derive_clause(cx, parent) {
                return Some(self.plan_emit_and_pos_chain_from(cx, parent_id, parent, &path));
            }
            // A refused parent cannot leave assumptions or memoized proof
            // indices in a later successful candidate. Work is not refunded.
            cx.rollback(mark);
        }
        None
    }

    /// Iterative, identity-only DAG walk. Charge fanout before allocating it;
    /// only raw AND edges are traversed, never an OR, ITE, equality or binder.
    fn rewritten_conjunct_path(
        &self,
        cx: &mut PlanCx<'_>,
        root: TermId,
        target: TermId,
    ) -> Option<AndPath> {
        cx.spend(1)?;
        let mut nodes = vec![PathNode {
            term: root,
            parent: None,
            depth: 0,
        }];
        let mut seen = HashSet::from_iter([root]);
        let mut cursor = 0;
        while cursor < nodes.len() {
            cx.spend(1)?;
            let node = &nodes[cursor];
            if node.term == target {
                let mut path = Vec::with_capacity(node.depth);
                let mut ancestor = cursor;
                while let Some((parent, position)) = nodes[ancestor].parent {
                    path.push(position);
                    ancestor = parent;
                }
                path.reverse();
                return Some(AndPath::Found(path));
            }
            if node.depth < MAX_REWRITTEN_CONJUNCT_DEPTH {
                if let TermData::App(symbol, args) = self.terms.get(node.term) {
                    if symbol.name() == "and" {
                        cx.spend(args.len())?;
                        let depth = node.depth + 1;
                        for (position, &term) in args.iter().enumerate() {
                            if seen.insert(term) {
                                nodes.push(PathNode {
                                    term,
                                    parent: Some((cursor, u32::try_from(position).ok()?)),
                                    depth,
                                });
                            }
                        }
                    }
                }
            }
            cursor += 1;
        }
        Some(AndPath::Missing)
    }
}

#[cfg(test)]
mod tests;
