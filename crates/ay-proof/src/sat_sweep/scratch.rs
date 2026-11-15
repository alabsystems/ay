// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dense, reused membership marks for the sweep's per-lemma cone and local
//! problem.
//!
//! Every candidate lemma builds its cone and its local clause set afresh.
//! With hash sets that was the whole cost of a large sweep: sampled
//! 2026-09-29 on the 64-bit `x / 2 = x >> 1` divider (external-codegen `UDIV` rows),
//! hash inserts and rehashes plus `Sweep::local` itself took about 90% of the
//! compute thread and the solver a sliver, and the row timed out at 120 s.
//! A generation-stamped array answers the same membership questions in O(1)
//! and is cleared in O(1), so one allocation serves every lemma. The sets it
//! stands for are unchanged, and so is every order derived from them.

use super::{Gate, Merge, Sweep, MAX_CONE_VARS};

impl Sweep<'_, '_> {
    /// Every variable the lemma over `roots` can depend on, stopping at
    /// merged gates' representatives; `None` when it is not local.
    pub(super) fn cone(&self, roots: &[usize]) -> Option<Vec<usize>> {
        self.cone_within(roots, usize::MAX).map(|(cone, _)| cone)
    }

    /// [`Self::cone`] cut `depth` operand edges below the roots: an unmerged
    /// gate that deep stays in the cone as a FREE variable, its definition
    /// left out (an equivalence to a merged gate's representative costs no
    /// depth). The flag says whether anything was cut, i.e. whether the cone
    /// is smaller than the full one.
    ///
    /// Any clause set is sound to refute from — the lemma is derived from
    /// the clauses the cut cone keeps — so a cut only loses completeness: a
    /// lemma that needs the gates below the cut is not proved here.
    pub(super) fn cone_within(&self, roots: &[usize], depth: usize) -> Option<(Vec<usize>, bool)> {
        let mut scratch = self.scratch.borrow_mut();
        let seen = &mut scratch.cone;
        seen.clear();
        let mut cone: Vec<usize> = Vec::new();
        let mut cut = false;
        // Breadth first, so every variable is expanded at its least depth.
        let mut queue: std::collections::VecDeque<(usize, usize)> =
            roots.iter().map(|&root| (root, 0)).collect();
        while let Some((var, level)) = queue.pop_front() {
            if !seen.insert(var) {
                continue;
            }
            cone.push(var);
            if cone.len() > MAX_CONE_VARS {
                return None;
            }
            match &self.merged[var] {
                Some(Merge::Const(_)) => {}
                Some(Merge::Equiv(to, _)) => queue.push_back((to.variable().index(), level)),
                None if level < depth => {
                    queue.extend(
                        self.nodes[var]
                            .operands()
                            .into_iter()
                            .map(|operand| (operand, level + 1)),
                    );
                    // A guarded `ite` bit's equalities enter UNEXPANDED
                    // (`Gate::GuardedIte`).
                    if let Gate::GuardedIte { equalities, .. } = &self.nodes[var] {
                        for &equality in equalities {
                            if seen.insert(equality) {
                                cone.push(equality);
                            }
                        }
                    }
                }
                None => cut |= !self.nodes[var].operands().is_empty(),
            }
        }
        cone.sort_unstable();
        Some((cone, cut))
    }
}

/// Membership over `0..`, cleared by starting a new generation.
pub(super) struct Marks {
    stamp: Vec<u32>,
    generation: u32,
}

impl Marks {
    pub(super) fn new(len: usize) -> Self {
        Self {
            stamp: vec![0; len],
            generation: 1,
        }
    }

    /// Forget every mark.
    pub(super) fn clear(&mut self) {
        if self.generation == u32::MAX {
            self.stamp.fill(0);
            self.generation = 1;
        } else {
            self.generation += 1;
        }
    }

    /// Mark `index`; `false` when it was already marked.
    pub(super) fn insert(&mut self, index: usize) -> bool {
        if index >= self.stamp.len() {
            self.stamp.resize(index + 1, 0);
        }
        let slot = &mut self.stamp[index];
        let fresh = *slot != self.generation;
        *slot = self.generation;
        fresh
    }

    pub(super) fn contains(&self, index: usize) -> bool {
        self.stamp.get(index) == Some(&self.generation)
    }
}

/// A map from a global variable to its local index, cleared like [`Marks`].
pub(super) struct LocalIndex {
    marks: Marks,
    local: Vec<usize>,
}

impl LocalIndex {
    pub(super) fn new(len: usize) -> Self {
        Self {
            marks: Marks::new(len),
            local: vec![0; len],
        }
    }

    pub(super) fn clear(&mut self) {
        self.marks.clear();
    }

    /// The local index of `var`, from `fresh` the first time it is asked.
    pub(super) fn index_of(&mut self, var: usize, fresh: impl FnOnce() -> usize) -> usize {
        if !self.marks.insert(var) {
            return self.local[var];
        }
        if var >= self.local.len() {
            self.local.resize(var + 1, 0);
        }
        let index = fresh();
        self.local[var] = index;
        index
    }
}

/// The marks one lemma's cone and local problem use; never held across calls.
pub(super) struct Scratch {
    pub(super) cone: Marks,
    pub(super) inside: Marks,
    pub(super) local: LocalIndex,
}

impl Scratch {
    pub(super) fn new(vars: usize) -> Self {
        Self {
            cone: Marks::new(vars),
            inside: Marks::new(vars),
            local: LocalIndex::new(vars),
        }
    }
}

#[cfg(test)]
#[path = "scratch_tests.rs"]
mod tests;
