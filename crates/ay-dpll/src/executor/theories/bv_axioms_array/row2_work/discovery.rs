// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Persistent preorder DFS and generation-local read scheduling.

use super::super::{HashMap, HashSet, Sort, TermData, TermId};
use ay_core::TermStore;

#[derive(Default)]
pub(super) struct Discovery {
    visited: HashSet<TermId>,
    store_ordinals: HashMap<TermId, usize>,
    #[cfg(test)]
    pub(super) stats: DiscoveryStats,
}

#[cfg(test)]
#[derive(Debug, Default)]
pub(super) struct DiscoveryStats {
    pub(super) unique_nodes: usize,
    pub(super) child_edges: usize,
    pub(super) root_attempts: usize,
    pub(super) rounds: usize,
    pub(super) ite_jobs: usize,
    pub(super) row2_jobs: usize,
    pub(super) max_new_selects: usize,
}

pub(super) struct ReadJobs {
    pub(super) ite: Vec<(TermId, TermId)>,
    pub(super) row2: Vec<(TermId, TermId)>,
}

enum Frame {
    Enter(TermId),
    Child(TermId, usize),
}

impl Discovery {
    pub(super) fn collect(
        &mut self,
        terms: &TermStore,
        roots: impl IntoIterator<Item = TermId>,
    ) -> ReadJobs {
        let mut selects = Vec::new();
        let mut stack = Vec::new();
        #[cfg(test)]
        {
            self.stats.rounds += 1;
        }
        for root in roots {
            #[cfg(test)]
            {
                self.stats.root_attempts += 1;
            }
            stack.push(Frame::Enter(root));
            self.visit(terms, &mut stack, &mut selects);
        }
        #[cfg(test)]
        {
            self.stats.max_new_selects = self.stats.max_new_selects.max(selects.len());
        }
        let jobs = self.schedule(terms, selects);
        #[cfg(test)]
        {
            self.stats.ite_jobs += jobs.ite.len();
            self.stats.row2_jobs += jobs.row2.len();
        }
        jobs
    }

    fn visit(
        &mut self,
        terms: &TermStore,
        stack: &mut Vec<Frame>,
        selects: &mut Vec<(TermId, TermId)>,
    ) {
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(term) => {
                    // Mark on entry, NOT when siblings are enqueued: a shared
                    // descendant must retain the recursive DFS's first visit.
                    if !self.visited.insert(term) {
                        continue;
                    }
                    #[cfg(test)]
                    {
                        self.stats.unique_nodes += 1;
                    }
                    if let TermData::App(sym, args) = terms.get(term) {
                        match sym.name() {
                            "select" if args.len() == 2 => selects.push((args[0], args[1])),
                            "store" if args.len() == 3 => {
                                let ordinal = self.store_ordinals.len();
                                self.store_ordinals.insert(term, ordinal);
                            }
                            _ => {}
                        }
                    }
                    stack.push(Frame::Child(term, 0));
                }
                Frame::Child(term, next) => {
                    if let Some(child) = child_at(terms.get(term), next) {
                        #[cfg(test)]
                        {
                            self.stats.child_edges += 1;
                        }
                        // Keep one continuation per ancestor rather than a
                        // pending vector containing every edge of a wide App.
                        stack.push(Frame::Child(term, next + 1));
                        stack.push(Frame::Enter(child));
                    }
                }
            }
        }
    }

    fn schedule(&self, terms: &TermStore, selects: Vec<(TermId, TermId)>) -> ReadJobs {
        let mut ite = Vec::new();
        let mut stores = Vec::new();
        for (select_ordinal, (array, index)) in selects.into_iter().enumerate() {
            match terms.get(array) {
                TermData::Ite(_, then_array, else_array) => {
                    for branch in [*then_array, *else_array] {
                        if matches!(terms.sort(branch), Sort::Array(_)) {
                            ite.push((branch, index));
                        }
                    }
                }
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    if args[1] != index {
                        if let Some(&store_ordinal) = self.store_ordinals.get(&array) {
                            stores.push((store_ordinal, select_ordinal, args[0], index));
                        }
                    }
                }
                _ => {}
            }
        }
        // Every select ordinal is unique, so this total key retains the old
        // store-list order and within-store select order without stable-sort
        // scratch space or scanning all previously discovered stores again.
        stores.sort_unstable_by_key(|&(store, select, _, _)| (store, select));
        ReadJobs {
            ite,
            row2: stores
                .into_iter()
                .map(|(_, _, array, index)| (array, index))
                .collect(),
        }
    }
}

/// Match the legacy collector's grammar and child order, including generic
/// indexed App operands. Let/quantifier/other nodes remain outside this walk.
fn child_at(data: &TermData, index: usize) -> Option<TermId> {
    match data {
        TermData::App(_, args) => args.get(index).copied(),
        TermData::Not(inner) if index == 0 => Some(*inner),
        TermData::Ite(c, t, e) => [*c, *t, *e].get(index).copied(),
        _ => None,
    }
}
