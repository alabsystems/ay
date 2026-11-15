// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every gate read through its PRIME clauses.
//!
//! The strict checker spells each gate as its truth table
//! (`bv_blast_export::tseitin_clauses`): one full-width clause per violating
//! row, so `o = (and a b)` is `(¬o a b) (¬o a ¬b) (¬o ¬a b) (o ¬a ¬b)`, and
//! unit propagation from `o` reaches neither `a` nor `b`. Unit propagation is
//! how the sweep proves most lemmas without a solver (`unit.rs`) and how it
//! finds the roots' hypotheses (`care.rs`), and a solver searching a
//! truth table learns by conflict what the prime clause `(¬o a)` says
//! outright. Measured 2026-09-30 on external-codegen's `BFM` row 2051: the checker's
//! sweep proved 5,388 lemmas by propagation where the printer's, over the
//! same assertion spelled with prime clauses, proved 7,612.
//!
//! So each gate's prime clauses that the CNF does not already hold are
//! derived once, before sweeping, as RUP steps over the gate's own clauses
//! (`probe_clause`), and enter every local problem that holds the gate. A
//! prime clause the gate's clauses do not derive is simply not added.

use super::*;

impl Sweep<'_, '_> {
    /// Derive every live gate's missing prime clauses (see the module
    /// documentation).
    pub(super) fn derive_prime_clauses(&mut self) {
        for var in 0..self.nodes.len() {
            if !self.live[var] {
                continue;
            }
            let primes = prime_clauses(&self.nodes[var], var);
            if primes.is_empty() {
                continue;
            }
            let own = self.by_owner[var].clone();
            let held: DetHashSet<Vec<Literal>> =
                own.iter().map(|&index| sorted(&self.cnf[index])).collect();
            for prime in primes {
                if held.contains(&sorted(&prime)) {
                    continue;
                }
                let Some(hints) = self.probe_clause(&prime, &own) else {
                    continue;
                };
                let Some((hints, clause)) = self.normalized_hints(&prime, &hints) else {
                    continue;
                };
                let id = self.next_id;
                self.next_id += 1;
                self.derived_at.insert(id, self.derived.len());
                self.derived.push(RupStep {
                    id,
                    clause,
                    rup_hints: hints,
                });
                self.prime[var].push(id);
            }
        }
    }

    /// The ids of `clauses` whose unit propagation from the negation of
    /// `clause` ends in a falsified one, in order, or `None`.
    fn probe_clause(&self, clause: &[Literal], clauses: &[usize]) -> Option<Vec<u64>> {
        let mut assigned: DetHashMap<usize, bool> = clause
            .iter()
            .map(|lit| (lit.variable().index(), !lit.is_positive()))
            .collect();
        let mut used: Vec<usize> = Vec::new();
        loop {
            let mut progressed = false;
            for &index in clauses {
                if used.contains(&index) {
                    continue;
                }
                let mut open: Option<Literal> = None;
                let mut several = false;
                let mut satisfied = false;
                for lit in &self.cnf[index] {
                    match assigned.get(&lit.variable().index()) {
                        Some(value) if *value == lit.is_positive() => {
                            satisfied = true;
                            break;
                        }
                        Some(_) => {}
                        None if open.is_some_and(|existing| existing != *lit) => several = true,
                        None => open = Some(*lit),
                    }
                }
                if satisfied || several {
                    continue;
                }
                used.push(index);
                match open {
                    None => return Some(used.iter().map(|&index| index as u64 + 1).collect()),
                    Some(lit) => {
                        assigned.insert(lit.variable().index(), lit.is_positive());
                        progressed = true;
                    }
                }
            }
            if !progressed {
                return None;
            }
        }
    }
}

fn sorted(clause: &[Literal]) -> Vec<Literal> {
    let mut clause = clause.to_vec();
    clause.sort_unstable_by_key(|lit| lit.index());
    clause.dedup();
    clause
}

/// The prime clauses of `gate` with output `var`: the shortest clauses that
/// together define it. A parity has no shorter ones than its truth table, and
/// an alias is its two binary clauses already.
fn prime_clauses(gate: &Gate, var: usize) -> Vec<Vec<Literal>> {
    let out = literal(var, false);
    match gate {
        Gate::And(args) => {
            let mut primes: Vec<Vec<Literal>> =
                args.iter().map(|arg| vec![out.negated(), *arg]).collect();
            primes.push(
                std::iter::once(out)
                    .chain(args.iter().map(|arg| arg.negated()))
                    .collect(),
            );
            primes
        }
        Gate::Or(args) => {
            let mut primes: Vec<Vec<Literal>> =
                args.iter().map(|arg| vec![out, arg.negated()]).collect();
            primes.push(
                std::iter::once(out.negated())
                    .chain(args.iter().copied())
                    .collect(),
            );
            primes
        }
        Gate::Majority(a, b, c) => {
            let pairs = [(a, b), (a, c), (b, c)];
            let mut primes: Vec<Vec<Literal>> = pairs
                .iter()
                .map(|(x, y)| vec![out.negated(), **x, **y])
                .collect();
            primes.extend(
                pairs
                    .iter()
                    .map(|(x, y)| vec![out, x.negated(), y.negated()]),
            );
            primes
        }
        Gate::Ite(c, a, b) => vec![
            vec![c.negated(), out.negated(), *a],
            vec![c.negated(), out, a.negated()],
            vec![*c, out.negated(), *b],
            vec![*c, out, b.negated()],
            vec![a.negated(), b.negated(), out],
            vec![*a, *b, out.negated()],
        ],
        Gate::Input
        | Gate::Const(_)
        | Gate::Xor(_)
        | Gate::Iff(..)
        | Gate::Alias(_)
        | Gate::GuardedIte { .. } => Vec::new(),
    }
}
