// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The clauses in force a leaf can do without: those BLOCKED on a free
//! variable, and the rows of a gate nothing else still mentions.
//!
//! ## Why
//!
//! A defined word whose condition the leaf has decided is forced equal to
//! one branch, although nothing else may read it. Measured 2026-09-30 on
//! proof_gate_strict row 1257: once a leaf knew the sign, each of the 53
//! other exponents' decodings `t = ite(sign, -X, X)` was forced to `-X`,
//! and the forced equality pulled its negation circuit in: 3,800 of the
//! core's variables were those circuits, and the solver searched them.
//!
//! ## Why dropping them changes no verdict
//!
//! A clause is blocked on a variable when resolving it on that variable
//! with every clause of the opposite polarity gives a tautology; removing a
//! blocked clause preserves satisfiability (Järvisalo, Biere, Heule 2010),
//! so the rest is refuted exactly when the whole is. Here the two rows of an
//! `xnor` forced true, `(¬w ∨ x)` and `(w ∨ ¬x)`, are blocked on a word bit
//! `w` that nothing else mentions. A gate whose output only its own rows
//! mention is then a definition nobody reads: any assignment of the rest
//! extends to it by computing it. Removing clauses only ever shrinks the
//! leaf, and whatever it refutes is replayed against the full CNF.

use super::super::*;
use super::node::Propagated;
use super::pool::Pool;

impl Sweep<'_, '_> {
    /// `counted` without its blocked clauses and dead gates' rows, to a
    /// fixed point.
    pub(super) fn prune(&self, pool: &Pool, prop: &Propagated, counted: &[usize]) -> Vec<usize> {
        let value = &prop.value;
        let mut alive: DetHashSet<usize> = counted.iter().copied().collect();
        // Open occurrences of each unassigned variable.
        let mut occurs: DetHashMap<usize, Vec<usize>> = DetHashMap::default();
        for &index in counted {
            for lit in &pool.clauses[index] {
                let var = lit.variable().index();
                if value[var].is_none() {
                    occurs.entry(var).or_default().push(index);
                }
            }
        }
        let mut work: Vec<usize> = occurs.keys().copied().collect();
        work.sort_unstable();
        while let Some(var) = work.pop() {
            let Some(list) = occurs.get_mut(&var) else {
                continue;
            };
            list.retain(|index| alive.contains(index));
            if list.is_empty() {
                continue;
            }
            let list = list.clone();
            let removable = match &self.nodes[var] {
                Gate::Input => self.blocked(pool, value, var, &list),
                Gate::Const(_) => false,
                _ => list
                    .iter()
                    .all(|index| pool.rows[var].contains(&(*index as u32))),
            };
            if !removable {
                continue;
            }
            for index in list {
                if alive.remove(&index) {
                    for lit in &pool.clauses[index] {
                        let other = lit.variable().index();
                        if other != var && value[other].is_none() {
                            work.push(other);
                        }
                    }
                }
            }
        }
        counted
            .iter()
            .copied()
            .filter(|index| alive.contains(index))
            .collect()
    }

    /// Whether every clause of `list` (the open clauses mentioning `var`) is
    /// blocked on `var`: each resolvent on it over the open literals is a
    /// tautology.
    fn blocked(&self, pool: &Pool, value: &[Option<bool>], var: usize, list: &[usize]) -> bool {
        const MAX_PAIRS: usize = 64;
        let open = |index: usize| -> Vec<Literal> {
            pool.clauses[index]
                .iter()
                .copied()
                .filter(|lit| value[lit.variable().index()].is_none())
                .collect()
        };
        let (positive, negative): (Vec<usize>, Vec<usize>) = list.iter().partition(|&&index| {
            pool.clauses[index]
                .iter()
                .any(|lit| lit.variable().index() == var && lit.is_positive())
        });
        if positive.len().saturating_mul(negative.len()) > MAX_PAIRS {
            return false;
        }
        positive.iter().all(|&left| {
            let left = open(left);
            negative.iter().all(|&right| {
                let right = open(right);
                left.iter()
                    .any(|lit| lit.variable().index() != var && right.contains(&lit.negated()))
            })
        })
    }
}
