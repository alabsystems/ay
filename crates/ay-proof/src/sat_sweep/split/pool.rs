// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The clauses a split works over: the CNF's own (roots included), the
//! strong gate clauses derived from them, and the widened units each node
//! derives for its subtree.
//!
//! ## Why strong gate clauses
//!
//! The strict checker's bit-blaster states every gate by its full truth
//! table: `out = a ∧ b` is the four three-literal rows, never the binary
//! `(¬out ∨ a)`. Unit propagation over rows alone infers nothing from
//! `out = 1`, so a node's propagation would stop at the root and every
//! leaf would re-learn each binary clause by search. Each strong clause is
//! derived once, by unit propagation over its gate's own rows, and is
//! recorded as an ordinary RUP step; the printer's CNF already holds them
//! and derives none.

use super::super::unit::unit_refutation;
use super::super::*;

pub(in crate::sat_sweep) struct Pool {
    pub(super) clauses: Vec<Vec<Literal>>,
    /// The DAG id of each clause (a CNF clause's LRAT id or a derived one).
    pub(super) ids: Vec<u64>,
    /// Clause indices by literal.
    pub(super) by_literal: Vec<Vec<u32>>,
    /// Indices of the unit clauses, in order.
    pub(super) units: Vec<usize>,
    /// Indices of the CNF clauses no gate and no [`Definition`] defines:
    /// the roots and every other side constraint. What they do not yet
    /// satisfy is what a node must still refute.
    pub(super) constraints: Vec<usize>,
    /// Each gate's own clauses, by its variable: the CNF rows over it and
    /// its operands, and the strong clauses derived from them.
    pub(super) rows: Vec<Vec<u32>>,
    /// The clause indices of each [`Definition`].
    pub(super) definitions: Vec<Vec<usize>>,
    /// The definition each defined variable belongs to.
    pub(super) defined_by: DetHashMap<usize, usize>,
}

/// Free variables whose meaning arrives as clauses rather than as a gate:
/// the printer's bit-vector `ite` word, whose bits are free and whose two
/// guarded equalities are its semantics. A node needs those clauses only
/// while one of the variables matters, and only the ones still in force.
pub(crate) struct Definition {
    /// The defined variables.
    pub(crate) vars: Vec<usize>,
    /// The CNF clauses that define them.
    pub(crate) clauses: Vec<usize>,
}

impl Pool {
    pub(super) fn len(&self) -> usize {
        self.clauses.len()
    }

    pub(super) fn push(&mut self, clause: Vec<Literal>, id: u64) {
        let index = self.clauses.len();
        if clause.len() == 1 {
            self.units.push(index);
        }
        for lit in &clause {
            if let Some(list) = self.by_literal.get_mut(lit.index()) {
                list.push(index as u32);
            }
        }
        self.clauses.push(clause);
        self.ids.push(id);
    }

    /// Forget every clause from `len` on: a node's widened units belong to
    /// its subtree.
    pub(super) fn truncate(&mut self, len: usize) {
        for clause in self.clauses.drain(len..) {
            for lit in clause {
                if let Some(list) = self.by_literal.get_mut(lit.index()) {
                    while list.last().is_some_and(|&index| index as usize >= len) {
                        list.pop();
                    }
                }
            }
        }
        self.ids.truncate(len);
        while self.units.last().is_some_and(|&index| index >= len) {
            self.units.pop();
        }
    }
}

/// The clauses that state `gate`'s function in the strong (prime) form the
/// truth-table rows imply: for `out = a ∧ b`, `(¬out ∨ a)` and `(¬out ∨ b)`;
/// for a disjunction, the dual; for a full adder's carry, the six ternary
/// clauses.
fn strong_clauses(out: Literal, gate: &Gate) -> Vec<Vec<Literal>> {
    match gate {
        Gate::And(args) if args.len() >= 2 => {
            args.iter().map(|arg| vec![out.negated(), *arg]).collect()
        }
        Gate::Or(args) if args.len() >= 2 => {
            args.iter().map(|arg| vec![out, arg.negated()]).collect()
        }
        Gate::Majority(a, b, c) => [(*a, *b), (*a, *c), (*b, *c)]
            .iter()
            .flat_map(|&(x, y)| {
                [
                    vec![x.negated(), y.negated(), out],
                    vec![x, y, out.negated()],
                ]
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn sorted(clause: &[Literal]) -> Vec<Literal> {
    let mut key = clause.to_vec();
    key.sort_unstable();
    key.dedup();
    key
}

impl Sweep<'_, '_> {
    /// The pool of this CNF: its clauses, then every strong gate clause it
    /// does not already hold. Every clause is also known to the stitcher,
    /// so a derivation that lands on one reuses it.
    pub(super) fn pool(&mut self, definitions: &[Definition], implied: &[usize]) -> Pool {
        let vars = self.nodes.len();
        let mut pool = Pool {
            clauses: Vec::with_capacity(self.cnf.len()),
            ids: Vec::with_capacity(self.cnf.len()),
            by_literal: vec![Vec::new(); vars * 2],
            units: Vec::new(),
            constraints: Vec::new(),
            rows: vec![Vec::new(); vars],
            definitions: Vec::with_capacity(definitions.len()),
            defined_by: DetHashMap::default(),
        };
        let mut defining: DetHashSet<usize> = DetHashSet::default();
        for definition in definitions {
            if definition
                .clauses
                .iter()
                .any(|&index| index >= self.cnf.len())
                || definition.vars.iter().any(|&var| var >= vars)
            {
                continue;
            }
            for &var in &definition.vars {
                pool.defined_by.insert(var, pool.definitions.len());
            }
            defining.extend(definition.clauses.iter().copied());
            pool.definitions.push(definition.clauses.clone());
        }
        let implied: DetHashSet<usize> = implied.iter().copied().collect();
        let mut known: DetHashMap<Vec<Literal>, u64> = DetHashMap::default();
        for (index, clause) in self.cnf.iter().enumerate() {
            known.entry(sorted(clause)).or_insert(index as u64 + 1);
            pool.push(clause.clone(), index as u64 + 1);
            // An IMPLIED clause (a lemma the rest of the CNF entails, such as
            // a chain shortcut) only propagates: it constrains nothing.
            if implied.contains(&index) {
                continue;
            }
            if self.roots.contains(&index) || defining.contains(&index) {
                if self.roots.contains(&index) {
                    pool.constraints.push(index);
                }
                continue;
            }
            let owners = self.owners(clause);
            if owners.is_empty() {
                pool.constraints.push(index);
            }
            for owner in owners {
                pool.rows[owner].push(index as u32);
            }
        }
        self.known_clauses = Some(known);
        for var in 0..vars {
            let targets = strong_clauses(literal(var, false), &self.nodes[var]);
            if targets.is_empty() {
                continue;
            }
            let mut scope: Vec<usize> = self.nodes[var].operands();
            scope.push(var);
            // The gate's own CNF rows (`owners`): over its output and
            // operands alone.
            let rows: Vec<usize> = pool.rows[var].iter().map(|&index| index as usize).collect();
            for target in targets {
                let key = sorted(&target);
                if key.windows(2).any(|pair| pair[0] == pair[1].negated())
                    || self
                        .known_clauses
                        .as_ref()
                        .is_some_and(|known| known.contains_key(&key))
                {
                    continue;
                }
                if let Some(id) = self.derive_from_rows(&scope, &rows, &target) {
                    if let Some(clause) = self.clause_of(id).map(<[Literal]>::to_vec) {
                        let index = pool.len() as u32;
                        pool.rows[var].push(index);
                        pool.push(clause, id);
                    }
                }
            }
        }
        pool
    }

    /// The gates `clause` is one of the defining rows of: each gate it
    /// mentions whose output and operands cover all of it.
    fn owners(&self, clause: &[Literal]) -> Vec<usize> {
        let mut owners: Vec<usize> = Vec::new();
        for output in clause {
            let gate = output.variable().index();
            if matches!(self.nodes[gate], Gate::Input | Gate::Const(_)) || owners.contains(&gate) {
                continue;
            }
            let operands = self.nodes[gate].operands();
            if clause.iter().all(|lit| {
                let var = lit.variable().index();
                var == gate || operands.contains(&var)
            }) {
                owners.push(gate);
            }
        }
        owners
    }

    /// `target` as one RUP step over `rows` (the clauses over `scope`), or
    /// `None` when unit propagation over them does not refute its negation.
    fn derive_from_rows(
        &mut self,
        scope: &[usize],
        rows: &[usize],
        target: &[Literal],
    ) -> Option<u64> {
        let local = |lit: &Literal| -> Option<Literal> {
            let position = scope.iter().position(|v| *v == lit.variable().index())?;
            Some(literal(position, !lit.is_positive()))
        };
        let mut clauses: Vec<Vec<Literal>> = Vec::with_capacity(rows.len() + target.len());
        for &index in rows {
            clauses.push(self.cnf[index].iter().filter_map(local).collect());
        }
        for lit in target {
            clauses.push(vec![local(lit)?.negated()]);
        }
        let used = unit_refutation(&clauses, scope.len())?;
        let hints: Vec<u64> = used
            .iter()
            .filter(|&&index| index < rows.len())
            .map(|&index| rows[index] as u64 + 1)
            .collect();
        self.record_chain(target, &hints)
    }

    /// Record `clause` by the RUP chain `hints` (normalized to the clause it
    /// actually derives), reusing an equal known clause.
    pub(super) fn record_chain(&mut self, clause: &[Literal], hints: &[u64]) -> Option<u64> {
        let (hints, clause) = self.normalized_hints(clause, hints)?;
        Some(self.record_step(clause, hints))
    }

    /// Record `clause` by `hints` as given, reusing an equal known clause.
    pub(super) fn record_step(&mut self, clause: Vec<Literal>, hints: Vec<u64>) -> u64 {
        let key = sorted(&clause);
        if let Some(existing) = self
            .known_clauses
            .as_ref()
            .and_then(|known| known.get(&key).copied())
        {
            return existing;
        }
        let id = self.next_id;
        self.next_id += 1;
        if let Some(known) = self.known_clauses.as_mut() {
            known.insert(key, id);
        }
        self.derived_at.insert(id, self.derived.len());
        self.derived.push(RupStep {
            id,
            clause,
            rup_hints: hints,
        });
        id
    }
}
