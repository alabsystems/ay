// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One node of the split: unit propagation under its path, the literal it
//! splits on, and — for a leaf whose core does not refute (`leaf.rs`) —
//! the uncompressed local problem: its clauses in force with every value
//! they mention as a widened unit.

use super::super::proof::Local;
use super::super::*;
use super::pool::Pool;
use super::relevance::Relevance;

/// What unit propagation under one path established.
pub(super) struct Propagated {
    pub(super) value: Vec<Option<bool>>,
    /// The pool clause that propagated each variable; `None` for a path
    /// literal or an unassigned variable.
    pub(super) reason_of: Vec<Option<usize>>,
    /// The propagating clauses, in trail order.
    pub(super) trail: Vec<usize>,
}

pub(super) enum Up {
    /// The pool clause every literal of which propagation made false, and
    /// the values it made on the way; `None` when the path itself clashes.
    Conflict(Option<(usize, Propagated)>),
    Settled(Propagated),
}

pub(super) fn lit_value(value: &[Option<bool>], lit: Literal) -> Option<bool> {
    value[lit.variable().index()].map(|v| v == lit.is_positive())
}

/// Path positions, as a bit set (a path is at most [`super::MAX_DEPTH`]).
type Deps = [u64; 2];

fn with(mut deps: Deps, position: usize) -> Deps {
    deps[position / 64] |= 1 << (position % 64);
    deps
}

fn union(left: Deps, right: Deps) -> Deps {
    [left[0] | right[0], left[1] | right[1]]
}

impl Sweep<'_, '_> {
    /// Unit propagation over the whole pool under `path`.
    pub(super) fn propagate(&self, pool: &Pool, path: &[Literal]) -> Up {
        let vars = self.nodes.len();
        let mut value: Vec<Option<bool>> = vec![None; vars];
        let mut reason_of: Vec<Option<usize>> = vec![None; vars];
        let mut trail: Vec<usize> = Vec::new();
        let mut queue: Vec<Literal> = Vec::with_capacity(path.len());
        for lit in path {
            match lit_value(&value, *lit) {
                Some(true) => {}
                Some(false) => return Up::Conflict(None),
                None => {
                    value[lit.variable().index()] = Some(lit.is_positive());
                    queue.push(*lit);
                }
            }
        }
        let mut pending: Vec<usize> = pool.units.clone();
        let mut head = 0;
        loop {
            while let Some(index) = pending.pop() {
                let mut open: Option<Literal> = None;
                let mut open_count = 0;
                let mut satisfied = false;
                for lit in &pool.clauses[index] {
                    match lit_value(&value, *lit) {
                        Some(true) => {
                            satisfied = true;
                            break;
                        }
                        Some(false) => {}
                        None if open != Some(*lit) => {
                            open_count += 1;
                            open = Some(*lit);
                        }
                        None => {}
                    }
                }
                if satisfied {
                    continue;
                }
                match (open_count, open) {
                    (0, _) => {
                        let state = Propagated {
                            value,
                            reason_of,
                            trail,
                        };
                        return Up::Conflict(Some((index, state)));
                    }
                    (1, Some(unit)) => {
                        value[unit.variable().index()] = Some(unit.is_positive());
                        reason_of[unit.variable().index()] = Some(index);
                        trail.push(index);
                        queue.push(unit);
                    }
                    _ => {}
                }
            }
            let Some(&lit) = queue.get(head) else {
                break;
            };
            head += 1;
            if let Some(list) = pool.by_literal.get(lit.negated().index()) {
                pending.extend(list.iter().map(|&index| index as usize));
            }
        }
        Up::Settled(Propagated {
            value,
            reason_of,
            trail,
        })
    }

    /// Derive, as the widened clause `(lit ∨ ¬p …)` over just the path
    /// literals it rests on, every propagated literal the clauses in force
    /// mention, and make it that variable's reason: the uncompressed leaf's
    /// solver then finds each value already a clause of its problem.
    pub(super) fn derive_units(
        &mut self,
        pool: &mut Pool,
        prop: &mut Propagated,
        path: &[Literal],
        relevance: &Relevance,
    ) -> Option<()> {
        // The values the counted clauses mention, and the reasons they rest
        // on, transitively.
        let mut needed = vec![false; self.nodes.len()];
        let mut stack: Vec<usize> = relevance
            .clauses
            .iter()
            .flat_map(|&index| pool.clauses[index].iter().map(|lit| lit.variable().index()))
            .filter(|&var| prop.value[var].is_some())
            .collect();
        while let Some(var) = stack.pop() {
            if std::mem::replace(&mut needed[var], true) {
                continue;
            }
            if let Some(reason) = prop.reason_of[var] {
                stack.extend(
                    pool.clauses[reason]
                        .iter()
                        .map(|lit| lit.variable().index()),
                );
            }
        }
        let mut deps: DetHashMap<usize, Deps> = DetHashMap::default();
        let mut unit_id: DetHashMap<usize, u64> = DetHashMap::default();
        for (position, lit) in path.iter().enumerate() {
            deps.insert(lit.variable().index(), with([0, 0], position));
        }
        let trail = std::mem::take(&mut prop.trail);
        for &reason in &trail {
            let clause = pool.clauses[reason].clone();
            let implied = clause.iter().copied().find(|lit| {
                prop.reason_of[lit.variable().index()] == Some(reason)
                    && lit_value(&prop.value, *lit) == Some(true)
            })?;
            let var = implied.variable().index();
            let mut rests_on: Deps = [0, 0];
            let mut hints: Vec<u64> = Vec::with_capacity(clause.len());
            for lit in &clause {
                let other = lit.variable().index();
                if other == var {
                    continue;
                }
                rests_on = union(rests_on, *deps.get(&other)?);
                if let Some(id) = unit_id.get(&other) {
                    hints.push(*id);
                }
            }
            deps.insert(var, rests_on);
            hints.push(pool.ids[reason]);
            if clause.len() == 1 {
                unit_id.insert(var, pool.ids[reason]);
                continue;
            }
            if !needed[var] {
                continue;
            }
            let mut widened = vec![implied];
            for (position, lit) in path.iter().enumerate() {
                if rests_on[position / 64] & (1 << (position % 64)) != 0 {
                    widened.push(lit.negated());
                }
            }
            let id = self.record_step(widened, hints);
            unit_id.insert(var, id);
            let clause = self.clause_of(id)?.to_vec();
            prop.reason_of[var] = Some(pool.len());
            pool.push(clause, id);
        }
        prop.trail = trail;
        Some(())
    }

    /// The local problem of a leaf: the counted clauses, the reason of
    /// every value they mention (a widened unit, `derive_units`), and the
    /// path as assumption units.
    pub(super) fn relevant_local(
        &self,
        pool: &Pool,
        prop: &Propagated,
        path: &[Literal],
        relevance: &Relevance,
    ) -> Local {
        let mut chosen: Vec<usize> = relevance.clauses.clone();
        let mut reasons: DetHashSet<usize> = DetHashSet::default();
        for &index in &relevance.clauses {
            for lit in &pool.clauses[index] {
                if let Some(reason) = prop.reason_of[lit.variable().index()] {
                    if reasons.insert(reason) {
                        chosen.push(reason);
                    }
                }
            }
        }
        let mut clauses: Vec<Vec<Literal>> = Vec::with_capacity(chosen.len() + path.len());
        let mut origin: Vec<Option<u64>> = Vec::with_capacity(chosen.len() + path.len());
        for index in chosen {
            if let Some(clause) = solver_clause(&pool.clauses[index]) {
                clauses.push(clause);
                origin.push(Some(pool.ids[index]));
            }
        }
        for assumption in path {
            clauses.push(vec![*assumption]);
            origin.push(None);
        }
        let mut local_of: DetHashMap<usize, usize> = DetHashMap::default();
        let mut global: Vec<usize> = Vec::new();
        for clause in &mut clauses {
            for lit in clause.iter_mut() {
                let var = lit.variable().index();
                let local = *local_of.entry(var).or_insert_with(|| {
                    global.push(var);
                    global.len() - 1
                });
                *lit = literal(local, !lit.is_positive());
            }
        }
        Local {
            clauses,
            origin,
            global,
        }
    }

    /// The literal to split on: of the node's guards (`Relevance::guards`),
    /// the one with the smallest unassigned cone.
    pub(super) fn open_guard(
        &self,
        pool: &Pool,
        prop: &Propagated,
        relevance: &Relevance,
    ) -> Option<Literal> {
        relevance
            .guards
            .iter()
            .map(|&lit| {
                (
                    self.bounded_cone(pool, lit.variable().index(), &prop.value, 512),
                    lit,
                )
            })
            .min()
            .map(|(_, lit)| lit)
    }

    /// Unassigned variables below `root`, counted up to `bound`. A defined
    /// word's bit is not free: its cone is its definition's.
    fn bounded_cone(
        &self,
        pool: &Pool,
        root: usize,
        value: &[Option<bool>],
        bound: usize,
    ) -> usize {
        let mut seen: DetHashSet<usize> = DetHashSet::default();
        let mut definitions: DetHashSet<usize> = DetHashSet::default();
        let mut stack = vec![root];
        while let Some(var) = stack.pop() {
            if value[var].is_some() || !seen.insert(var) {
                continue;
            }
            if seen.len() >= bound {
                return bound;
            }
            if let Some(&definition) = pool.defined_by.get(&var) {
                if definitions.insert(definition) {
                    for &clause in &pool.definitions[definition] {
                        stack.extend(
                            pool.clauses[clause]
                                .iter()
                                .map(|lit| lit.variable().index()),
                        );
                    }
                }
            }
            stack.extend(self.nodes[var].operands());
        }
        seen.len()
    }
}
