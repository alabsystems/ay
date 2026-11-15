// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Forward aliases, and the order the gates are simulated in.
//!
//! The printer names a theory atom — `(= l r)`, `(bvult a b)` — before the
//! bits that define it, and describes it as an ALIAS of the later gate its two
//! link clauses equate it with (`alethe_printer/complete_blast/sweep.rs`).
//! Swept in index order, the atom came first, so the defining gate was merged
//! INTO the atom: the atom's cone is its alias, the alias is merged back to
//! the atom, and the definition's clauses never enter any cone. Measured
//! 2026-09-30 on external-codegen's `BFM` row 2051: the closing refutation over the
//! root's cone read the three atoms of `(and h1 h2 (not (= l r)))` and their
//! definitions merged into them — 36 variables, SATISFIABLE — and only the
//! refutation over every clause closed, printing 74 MB.
//!
//! An atom that aliases a later variable is therefore merged into that
//! variable before anything is swept, by its own two link clauses: the cone of
//! every gate that reads the atom continues into its definition.
//!
//! The same forward references are why the gates are simulated in an order
//! computed once from their operands rather than in index order, which took
//! three passes and still misread a chain of atoms deeper than that.

use super::*;

impl Sweep<'_, '_> {
    /// Merge every variable whose gate is an alias of a LATER variable into
    /// it (see the module documentation).
    pub(super) fn merge_forward_aliases(&mut self) {
        for var in 0..self.nodes.len() {
            let Gate::Alias(target) = self.nodes[var] else {
                continue;
            };
            if target.variable().index() <= var {
                continue;
            }
            let forward = [literal(var, true), target];
            let backward = [literal(var, false), target.negated()];
            if let (Some(first), Some(second)) = (self.link(&forward), self.link(&backward)) {
                self.merged[var] = Some(Merge::Equiv(target, [first, second]));
            }
        }
    }

    /// The binary clause `link` of the CNF, as a derived step that cites it.
    fn link(&mut self, link: &[Literal; 2]) -> Option<u64> {
        let owner = link.iter().map(|lit| lit.variable().index()).max()?;
        let index = self.by_owner.get(owner)?.iter().copied().find(|&index| {
            let clause = &self.cnf[index];
            clause.len() == 2 && link.iter().all(|lit| clause.contains(lit))
        })?;
        let (hints, clause) = self.normalized_hints(link, &[index as u64 + 1])?;
        let id = self.next_id;
        self.next_id += 1;
        self.derived_at.insert(id, self.derived.len());
        self.derived.push(RupStep {
            id,
            clause,
            rup_hints: hints,
        });
        Some(id)
    }
}

/// An input a unit clause of the CNF fixes — other than a root — is that
/// constant. The printer spells a constant word's bits as atoms, each fixed
/// by its own unit clause (`((_ @bit_of i) #x…)`); simulated as free inputs,
/// every shift by a constant amount and every mask read noise (measured
/// 2026-09-30 on external-codegen's `BFM` row 2051, whose root implied its first
/// 2,380 literals from the bits of `(_ bv64 64)` alone).
pub(super) fn fix_unit_inputs(nodes: &mut [Gate], cnf: &[Vec<Literal>], roots: &[usize]) {
    for (index, clause) in cnf.iter().enumerate() {
        let [unit] = clause.as_slice() else {
            continue;
        };
        if roots.contains(&index) {
            continue;
        }
        if let Some(node) = nodes.get_mut(unit.variable().index()) {
            if matches!(node, Gate::Input) {
                *node = Gate::Const(unit.is_positive());
            }
        }
    }
}

/// Every variable after the ones its simulated value reads — a guarded
/// `ite` bit reads its condition and branches, never its links — or `None`
/// when those reads have a cycle.
pub(super) fn simulation_order(nodes: &[Gate]) -> Option<Vec<usize>> {
    let reads = |var: usize| -> Vec<usize> {
        match &nodes[var] {
            Gate::GuardedIte {
                condition,
                then_bit,
                else_bit,
                ..
            } => [condition, then_bit, else_bit]
                .iter()
                .map(|lit| lit.variable().index())
                .collect(),
            gate => gate.operands(),
        }
    };
    // 0: unvisited, 1: on the stack, 2: placed.
    let mut state = vec![0_u8; nodes.len()];
    let mut order = Vec::with_capacity(nodes.len());
    for start in 0..nodes.len() {
        if state[start] != 0 {
            continue;
        }
        state[start] = 1;
        let mut stack: Vec<(usize, Vec<usize>)> = vec![(start, reads(start))];
        while let Some((var, pending)) = stack.last_mut() {
            let var = *var;
            match pending.pop() {
                Some(next) => match state.get(next)? {
                    0 => {
                        state[next] = 1;
                        let next_reads = reads(next);
                        stack.push((next, next_reads));
                    }
                    1 => return None,
                    _ => {}
                },
                None => {
                    state[var] = 2;
                    order.push(var);
                    stack.pop();
                }
            }
        }
    }
    Some(order)
}
