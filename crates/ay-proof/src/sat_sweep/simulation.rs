// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sweep's simulation: random and counterexample patterns run through the
//! gates, the signatures that sort gates into candidate classes
//! (`signature.rs`), and the fan-in of the roots that the sweep is confined to.

use super::*;

impl Sweep<'_, '_> {
    /// One 64-pattern simulation word; inputs come from `input`.
    pub(super) fn simulate(&self, input: &mut dyn FnMut(usize) -> u64) -> Vec<u64> {
        let inputs: Vec<u64> = (0..self.nodes.len())
            .map(|var| match self.nodes[var] {
                Gate::Input => input(var),
                _ => 0,
            })
            .collect();
        let mut values = inputs.clone();
        // One pass in the order computed from the gates' reads (`alias.rs`),
        // or, should those reads have a cycle, three in index order.
        let (passes, order): (usize, &[usize]) = match &self.order {
            Some(order) => (1, order),
            None => (3, &self.index_order),
        };
        for _ in 0..passes {
            for &var in order {
                values[var] = match &self.nodes[var] {
                    Gate::Input => inputs[var],
                    Gate::Const(value) => {
                        if *value {
                            u64::MAX
                        } else {
                            0
                        }
                    }
                    Gate::And(args) => args
                        .iter()
                        .fold(u64::MAX, |acc, a| acc & value_of(&values, *a)),
                    Gate::Or(args) => args.iter().fold(0, |acc, a| acc | value_of(&values, *a)),
                    Gate::Xor(args) => args.iter().fold(0, |acc, a| acc ^ value_of(&values, *a)),
                    Gate::Iff(a, b) => !(value_of(&values, *a) ^ value_of(&values, *b)),
                    Gate::Ite(c, a, b)
                    | Gate::GuardedIte {
                        condition: c,
                        then_bit: a,
                        else_bit: b,
                        ..
                    } => {
                        let c = value_of(&values, *c);
                        (c & value_of(&values, *a)) | (!c & value_of(&values, *b))
                    }
                    Gate::Majority(a, b, c) => {
                        let (a, b, c) = (
                            value_of(&values, *a),
                            value_of(&values, *b),
                            value_of(&values, *c),
                        );
                        (a & b) | (a & c) | (b & c)
                    }
                    Gate::Alias(target) => value_of(&values, *target),
                };
            }
        }
        values
    }

    /// The phase-normalized signature of `var` (its class key), its phase,
    /// and whether it is a candidate constant.
    pub(super) fn signature(&self, var: usize) -> (u64, bool, bool) {
        self.signatures.of(var)
    }

    pub(super) fn classes(&self, upto: usize) -> DetHashMap<u64, Vec<usize>> {
        let mut classes: DetHashMap<u64, Vec<usize>> = DetHashMap::default();
        for var in 0..upto {
            if self.live[var]
                && self.merged[var].is_none()
                && !matches!(self.nodes[var], Gate::Const(_))
            {
                classes.entry(self.signature(var).0).or_default().push(var);
            }
        }
        classes
    }

    /// Add the pending counterexamples as one simulation word.
    pub(super) fn flush_patterns(&mut self) {
        let pending = std::mem::take(&mut self.pending);
        if self.signatures.words() >= MAX_WORDS {
            return;
        }
        let mut assigned: DetHashMap<usize, u64> = DetHashMap::default();
        let mut mask: DetHashMap<usize, u64> = DetHashMap::default();
        for (bit, pattern) in pending.iter().enumerate().take(64) {
            for &(var, value) in pattern {
                *mask.entry(var).or_default() |= 1 << bit;
                if value {
                    *assigned.entry(var).or_default() |= 1 << bit;
                }
            }
        }
        let salt = splitmix(0x5eed ^ self.signatures.words() as u64);
        let values = self.simulate(&mut |var| {
            let random = splitmix(salt ^ var as u64);
            let fixed = mask.get(&var).copied().unwrap_or(0);
            (random & !fixed) | assigned.get(&var).copied().unwrap_or(0)
        });
        self.absorb(&values);
    }

    /// Fold one simulation word into the signatures: every pattern, or,
    /// under hypotheses, the patterns that satisfy them (`care.rs`).
    pub(super) fn absorb(&mut self, values: &[u64]) {
        let care = self
            .care
            .as_ref()
            .map_or(u64::MAX, |care| care.mask(values));
        self.signatures.absorb(values, care);
    }

    /// The salt of the `word`th random simulation word: the sweep's own
    /// sequence, or, under hypotheses, the one `care.rs` measured them on.
    pub(super) fn random_salt(&self, word: usize) -> u64 {
        if self.care.is_some() {
            care::care_salt(word)
        } else {
            splitmix(word as u64)
        }
    }
}

/// Whether each gate is in the fan-in of the root clauses' variables.
///
/// A gate outside it can never matter to the refutation, but swept in
/// topological order it becomes the representative a later live gate is
/// merged to, and then its own lemmas are part of the proof. Measured
/// 2026-09-30 on the pinned checker's long divider: the carry chain it builds
/// for `x < y` at every level also builds the sums, which nothing reads.
pub(super) fn live_gates(nodes: &[Gate], cnf: &[Vec<Literal>], roots: &[usize]) -> Vec<bool> {
    let mut live = vec![false; nodes.len()];
    let mut stack: Vec<usize> = roots
        .iter()
        .filter_map(|&root| cnf.get(root))
        .flat_map(|clause| clause.iter().map(|lit| lit.variable().index()))
        .collect();
    while let Some(var) = stack.pop() {
        let Some(slot) = live.get_mut(var) else {
            continue;
        };
        if std::mem::replace(slot, true) {
            continue;
        }
        stack.extend(nodes[var].operands());
        if let Gate::GuardedIte { equalities, .. } = &nodes[var] {
            stack.extend(equalities.iter().copied());
        }
    }
    live
}
