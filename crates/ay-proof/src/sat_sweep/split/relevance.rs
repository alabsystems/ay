// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What one node of the split must still refute, and the disjunctions it
//! may split on.

use super::super::*;
use super::node::{lit_value, Propagated};
use super::pool::Pool;

/// What a node still has to refute (`Sweep::relevance`).
pub(super) struct Relevance {
    /// The pool clauses in force: none of their literals is true.
    pub(super) clauses: Vec<usize>,
    /// The literals the node may split on (`Sweep::guards`).
    pub(super) guards: Vec<Literal>,
}

/// A disjunction in force with no literal true: an `or` gate forced true,
/// a definition's guarded equality, or a side constraint.
struct Source {
    /// Its unassigned literals.
    literals: Vec<Literal>,
    /// The definition it belongs to, or the `or` gate it is.
    owner: Owner,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Owner {
    Definition(usize),
    Gate(usize),
    Constraint,
}

/// The walk [`Sweep::relevance`] makes: the clauses counted so far and the
/// unassigned variables they mention.
struct Walk<'v> {
    value: &'v [Option<bool>],
    vars: Vec<bool>,
    counted: Vec<bool>,
    clauses: Vec<usize>,
    stack: Vec<usize>,
}

impl Walk<'_> {
    /// Count pool clause `index` unless it is counted already or a value
    /// satisfies it; whether it was newly counted.
    fn take(&mut self, pool: &Pool, index: usize) -> bool {
        if std::mem::replace(&mut self.counted[index], true) {
            return false;
        }
        let clause = &pool.clauses[index];
        if clause
            .iter()
            .any(|lit| lit_value(self.value, *lit) == Some(true))
        {
            return false;
        }
        self.clauses.push(index);
        for lit in clause {
            let var = lit.variable().index();
            if self.value[var].is_none() && !std::mem::replace(&mut self.vars[var], true) {
                self.stack.push(var);
            }
        }
        true
    }

    fn open(&self, clause: &[Literal]) -> Vec<Literal> {
        clause
            .iter()
            .copied()
            .filter(|lit| self.value[lit.variable().index()].is_none())
            .collect()
    }
}

impl Sweep<'_, '_> {
    /// What the node must still refute: the clauses no value satisfies
    /// that can still constrain the roots, and the unassigned variables in
    /// them. Every side constraint in force counts; so does every row of an
    /// ASSIGNED gate that its value alone does not satisfy (an `or` forced
    /// true with no operand true, an `xor` whose output is known); a gate
    /// that is unassigned counts only when something counted mentions it,
    /// and then all its open rows do; a DEFINED word's clauses count once
    /// any of its bits is assigned or counted.
    ///
    /// Nothing else can matter: any assignment of the counted variables
    /// that satisfies the counted clauses extends to the whole CNF — the
    /// node's values as they are, every uncounted gate computed from its
    /// operands, every uncounted defined word from its definition, every
    /// other free variable arbitrary. A leaf refuted over these clauses is
    /// therefore refuted outright, and one they cannot refute would not be
    /// refuted by more.
    pub(super) fn relevance(&self, pool: &Pool, prop: &Propagated) -> Relevance {
        let value = &prop.value;
        let mut walk = Walk {
            value,
            vars: vec![false; self.nodes.len()],
            counted: vec![false; pool.len()],
            clauses: Vec::new(),
            stack: Vec::new(),
        };
        let mut sources: Vec<Source> = Vec::new();
        for &index in &pool.constraints {
            if walk.take(pool, index) && !self.roots.contains(&index) {
                sources.push(Source {
                    literals: walk.open(&pool.clauses[index]),
                    owner: Owner::Constraint,
                });
            }
        }
        let mut definitions_taken = vec![false; pool.definitions.len()];
        let mut take_definition = |walk: &mut Walk<'_>, sources: &mut Vec<Source>, var: usize| {
            let Some(&definition) = pool.defined_by.get(&var) else {
                return;
            };
            if std::mem::replace(&mut definitions_taken[definition], true) {
                return;
            }
            for &index in &pool.definitions[definition] {
                if walk.take(pool, index) {
                    sources.push(Source {
                        literals: walk.open(&pool.clauses[index]),
                        owner: Owner::Definition(definition),
                    });
                }
            }
        };
        for var in 0..self.nodes.len() {
            let Some(own) = value[var] else {
                continue;
            };
            match &self.nodes[var] {
                Gate::Input => take_definition(&mut walk, &mut sources, var),
                Gate::Const(_) => {}
                gate => {
                    for &index in &pool.rows[var] {
                        walk.take(pool, index as usize);
                    }
                    if let Gate::Or(args) = gate {
                        if own && !args.iter().any(|arg| lit_value(value, *arg) == Some(true)) {
                            sources.push(Source {
                                literals: walk.open(args),
                                owner: Owner::Gate(var),
                            });
                        }
                    }
                }
            }
        }
        while let Some(var) = walk.stack.pop() {
            match &self.nodes[var] {
                Gate::Input => take_definition(&mut walk, &mut sources, var),
                Gate::Const(_) => {}
                _ => {
                    for &index in &pool.rows[var] {
                        walk.take(pool, index as usize);
                    }
                }
            }
        }
        let guards = self.guards(pool, &sources);
        let Walk { clauses, .. } = walk;
        Relevance { clauses, guards }
    }

    /// The literals of the disjunctions no other one lies above. A
    /// disjunction below another's operands decides only inside one of the
    /// other's cases: `ite(c1, x, ite(c2, y, z))` split on `c2` first leaves
    /// `c1` open in both cases, and a chain of `n` such levels split from
    /// the inside grows `2^n` nodes, where split from the outside it grows
    /// `n` (each `c` true closes its level).
    fn guards(&self, pool: &Pool, sources: &[Source]) -> Vec<Literal> {
        let mut gate_source: DetHashMap<usize, usize> = DetHashMap::default();
        for (index, source) in sources.iter().enumerate() {
            if let Owner::Gate(var) = source.owner {
                gate_source.insert(var, index);
            }
        }
        let mut definition_dominated = vec![false; pool.definitions.len()];
        let mut gate_dominated = vec![false; sources.len()];
        let mut visited = vec![false; self.nodes.len()];
        let mut stack: Vec<usize> = Vec::new();
        for (index, source) in sources.iter().enumerate() {
            stack.extend(source.literals.iter().map(|lit| lit.variable().index()));
            if let Owner::Gate(var) = source.owner {
                stack.extend(self.nodes[var].operands());
            }
            while let Some(var) = stack.pop() {
                let definition = pool.defined_by.get(&var).copied();
                if let Some(definition) = definition {
                    if source.owner != Owner::Definition(definition) {
                        definition_dominated[definition] = true;
                    }
                }
                if let Some(&other) = gate_source.get(&var) {
                    if other != index {
                        gate_dominated[other] = true;
                    }
                }
                if std::mem::replace(&mut visited[var], true) {
                    continue;
                }
                match (&self.nodes[var], definition) {
                    (Gate::Input, Some(definition)) => {
                        if source.owner != Owner::Definition(definition) {
                            for &clause in &pool.definitions[definition] {
                                stack.extend(
                                    pool.clauses[clause]
                                        .iter()
                                        .map(|lit| lit.variable().index()),
                                );
                            }
                        }
                    }
                    (gate, _) => stack.extend(gate.operands()),
                }
            }
        }
        let mut guards: Vec<Literal> = sources
            .iter()
            .enumerate()
            .filter(|(index, source)| match source.owner {
                Owner::Definition(definition) => !definition_dominated[definition],
                Owner::Gate(_) => !gate_dominated[*index],
                Owner::Constraint => true,
            })
            .flat_map(|(_, source)| source.literals.iter().copied())
            .collect();
        if guards.is_empty() {
            guards = sources
                .iter()
                .flat_map(|source| source.literals.iter().copied())
                .collect();
        }
        guards.sort_unstable();
        guards.dedup();
        guards
    }
}
