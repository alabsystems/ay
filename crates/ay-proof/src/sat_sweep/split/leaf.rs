// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A leaf refuted over its CORE: the wiring its values leave between
//! equivalent literals collapsed before the solver sees it.
//!
//! ## Why
//!
//! Under a leaf's values most of a bit-blasted circuit is wire: an `xnor`
//! forced true, a multiplexer whose select is known, an `and` with a true
//! operand. Each is a pair of binary clauses, and a chain of them joins
//! literals that are one value. A solver handed the chains re-walks them in
//! every learned clause's hints; measured 2026-09-30 on proof_gate_strict
//! row 1257 (`i64 → f64 → i64`), the 104 leaves spent 1.07M hints on 16.7k
//! learned clauses (64 per clause) and the printed document passed the
//! 76 MiB budget. Collapsed, each chain is walked once per end it has.
//!
//! ## What it does
//!
//! The leaf's clauses in force (`Relevance::clauses`) lose their false
//! literals; the binary ones are an implication graph, whose strongly
//! connected components are classes of equal literals. Each class keeps one
//! representative and every clause is rewritten over them. The solver
//! refutes the rewritten clauses; only the ones its refutation uses are then
//! DERIVED: the clause in force, the values of its false literals, and for
//! each rewritten literal a SHORTCUT `(¬x ∨ rep)` walked along the class.
//!
//! ## Why the result is a refutation of the SAME CNF
//!
//! Every derived clause is an ordinary RUP step over pool clauses and
//! earlier steps, widened by the negated path and recorded as the resolvent
//! its chain actually derives (`Sweep::record_chain`): a value's step from
//! its reason and the values that reason rests on, a shortcut from the
//! implications it walks, a rewritten clause from its source, the values
//! of its false literals and the shortcuts of its rewritten ones. The
//! leaf's refutation is then stitched like any local one, and the caller
//! replays everything.

use super::super::proof::Local;
use super::super::*;
use super::implications::Implications;
use super::node::Propagated;
use super::pool::Pool;
use super::relevance::Relevance;
use super::units::Derived;

/// Conflicts one lemma of a core's sweep may spend.
const CORE_LEMMA_CONFLICTS: u64 = 500;

/// The leaf's clauses in force, over representatives: each rewritten
/// clause and its source pool clause.
struct Rewritten {
    clauses: Vec<(Vec<Literal>, usize)>,
}

/// The rewritten clauses as a solver's problem.
struct Core {
    /// The global variable of each core variable, in the circuit's order,
    /// so a gate's operands come before it (`core_sweep.rs` sweeps in that
    /// order).
    global: Vec<usize>,
    local_of: DetHashMap<usize, usize>,
    clauses: Vec<Vec<Literal>>,
    sources: Vec<usize>,
}

impl Rewritten {
    fn numbered(&self) -> Core {
        let mut global: Vec<usize> = self
            .clauses
            .iter()
            .flat_map(|(lits, _)| lits.iter().map(|lit| lit.variable().index()))
            .collect();
        global.sort_unstable();
        global.dedup();
        let local_of: DetHashMap<usize, usize> = global
            .iter()
            .enumerate()
            .map(|(local, &var)| (var, local))
            .collect();
        let clauses = self
            .clauses
            .iter()
            .map(|(lits, _)| {
                lits.iter()
                    .map(|lit| literal(local_of[&lit.variable().index()], !lit.is_positive()))
                    .collect()
            })
            .collect();
        Core {
            global,
            local_of,
            clauses,
            sources: self.clauses.iter().map(|(_, source)| *source).collect(),
        }
    }
}

/// The values the derivations of the `used` rewritten clauses need, once
/// per need: each false literal of a clause that must be rewritten, and
/// along each rewritten literal's walk to its representative, each false
/// literal of the implications it takes.
fn demand(derived: &Derived<'_>, rewritten: &Rewritten, used: &[usize]) -> Option<Vec<usize>> {
    let (pool, value) = (derived.pool, &derived.prop.value);
    let mut demand: Vec<usize> = Vec::new();
    let mut shortcuts: Vec<Literal> = Vec::new();
    for &index in used {
        let (lits, source) = &rewritten.clauses[index];
        let clause = &pool.clauses[*source];
        if clause.len() == lits.len() && clause.iter().all(|lit| lits.contains(lit)) {
            continue;
        }
        for lit in clause {
            if value[lit.variable().index()].is_some() {
                demand.push(lit.variable().index());
            } else if derived.rep.contains_key(lit) {
                shortcuts.push(*lit);
            }
        }
    }
    shortcuts.sort_unstable();
    shortcuts.dedup();
    for &x in &shortcuts {
        let mut at = x;
        let mut hops = 0;
        while let Some(&(next, clause)) = derived.toward.get(&at) {
            demand.extend(
                pool.clauses[clause]
                    .iter()
                    .map(|lit| lit.variable().index())
                    .filter(|&var| value[var].is_some()),
            );
            at = next;
            hops += 1;
            if hops > derived.toward.len() {
                return None;
            }
        }
    }
    Some(demand)
}

impl Sweep<'_, '_> {
    /// The clause refuting a leaf over its core, or `None` when the core
    /// does not refute within the leaf's allowance (the caller then tries
    /// the uncompressed leaf).
    pub(super) fn refute_leaf(
        &mut self,
        pool: &Pool,
        prop: &Propagated,
        path: &[Literal],
        relevance: &Relevance,
        conflicts: u64,
    ) -> Option<u64> {
        let mut derived = Derived::new(pool, prop, path);
        let counted = self.prune(pool, prop, &relevance.clauses);
        let rewritten = self.collapse(&mut derived, &counted)?;
        let core = rewritten.numbered();
        // A leaf that keeps this much of the circuit is the whole circuit's
        // sweep's to refute (`Leaves::Small`).
        if core.global.len() > self.largest_leaf {
            self.deferred_leaf = true;
            return None;
        }
        let dag = self.refute_core(&derived, &core, conflicts)?;
        let used = used_originals(&dag, core.clauses.len() as u64)?;
        let demand = demand(&derived, &rewritten, &used)?;
        self.leaf_units(&mut derived, &demand)?;
        let mut origin: Vec<Option<u64>> = vec![None; core.clauses.len()];
        for index in used {
            let (lits, source) = &rewritten.clauses[index];
            origin[index] = Some(self.derive_rewritten(&mut derived, lits, *source)?);
        }
        let local = Local {
            clauses: core.clauses,
            origin,
            global: core.global,
        };
        let widen = derived.widen.clone();
        self.stitch(&local, &dag, &widen)
    }

    /// The core's refutation: swept when its gates line up
    /// (`core_sweep.rs`), searched otherwise.
    fn refute_core(
        &mut self,
        derived: &Derived<'_>,
        core: &Core,
        conflicts: u64,
    ) -> Option<ResolutionDag> {
        if self.stopped {
            return None;
        }
        let limits = SweepLimits {
            lemma_conflicts: CORE_LEMMA_CONFLICTS,
            total_conflicts: self.conflicts_left.min(conflicts.saturating_mul(4)),
            total_work: self.work_cap.saturating_sub(self.work_read),
            deadline: self.deadline,
        };
        // A nested sweep consumes its own stopped flag. Keep any observation
        // in this original parent too, so refusal cannot select direct retry.
        let keep_going = &mut *self.keep_going;
        let stopped = &mut self.stopped;
        let mut inherited = || {
            if *stopped {
                return false;
            }
            // A callback panic must not reopen this owner after unwinding.
            *stopped = true;
            let allowed = keep_going();
            *stopped = !allowed;
            allowed
        };
        let (swept, spent) = super::core_sweep::Core {
            nodes: &self.nodes,
            value: &derived.prop.value,
            rep: &derived.rep,
            pool: derived.pool,
            sources: &core.sources,
            clauses: &core.clauses,
            global: &core.global,
            local_of: &core.local_of,
        }
        .sweep(limits, &mut inherited);
        self.conflicts_left = self.conflicts_left.saturating_sub(spent.conflicts);
        self.work_read = self.work_read.saturating_add(spent.work);
        if self.stopped {
            return None;
        }
        if swept.is_some() {
            return swept;
        }
        match self.solve(core.global.len(), &core.clauses, conflicts)? {
            ResolutionSolveOutcome::Unsat(dag) => Some(dag),
            ResolutionSolveOutcome::Sat(_) => None,
        }
    }

    /// The clauses in force over representatives: their false literals
    /// dropped, each class of equal literals (a strongly connected component
    /// of the binary clauses' implications) replaced by one member.
    fn collapse(&self, derived: &mut Derived<'_>, counted: &[usize]) -> Option<Rewritten> {
        let pool = derived.pool;
        let value = &derived.prop.value;
        let open = |index: usize| -> Vec<Literal> {
            let mut lits: Vec<Literal> = pool.clauses[index]
                .iter()
                .copied()
                .filter(|lit| value[lit.variable().index()].is_none())
                .collect();
            lits.sort_unstable();
            lits.dedup();
            lits
        };
        let mut graph = Implications::default();
        for &index in counted {
            if let [a, b] = open(index)[..] {
                graph.edge(a.negated(), b, index);
                graph.edge(b.negated(), a, index);
            }
        }
        let component = graph.components();
        // Every class and its complement: the member with the smallest
        // variable represents the class, its negation the complement.
        let mut rep_of: Vec<Option<Literal>> = vec![None; component.count];
        for (node, &lit) in graph.lits.iter().enumerate() {
            let class = component.of[node];
            let complement = component.of[*graph.node.get(&lit.negated())? as usize];
            if class == complement {
                // `x` and `¬x` in one class: the leaf's binary clauses alone
                // are contradictory, which the uncompressed leaf refutes.
                return None;
            }
            // A gate of two or more open operands represents its class before
            // a free bit or a wire (a gate the values leave one operand), so
            // the core keeps the class's function (`core_sweep.rs`); among
            // equals, the smallest variable.
            let rank = |lit: Literal| {
                let var = lit.variable().index();
                let open = self.nodes[var]
                    .operands()
                    .into_iter()
                    .filter(|&operand| value[operand].is_none())
                    .count();
                (open < 2, var)
            };
            let better = rep_of[class].is_none_or(|kept| rank(lit) < rank(kept));
            if better {
                rep_of[class] = Some(lit);
                rep_of[complement] = Some(lit.negated());
            }
        }
        for (node, &lit) in graph.lits.iter().enumerate() {
            let rep = rep_of[component.of[node]]?;
            if rep != lit {
                derived.rep.insert(lit, rep);
            }
        }
        // Each member's way to its representative: a search backwards from
        // the representative along its class's implications.
        for (node, &lit) in graph.lits.iter().enumerate() {
            if derived.rep.contains_key(&lit) {
                continue;
            }
            let class = component.of[node];
            let mut queue = std::collections::VecDeque::from([node as u32]);
            while let Some(at) = queue.pop_front() {
                for &(from, clause) in &graph.into[at as usize] {
                    let from_lit = graph.lits[from as usize];
                    if component.of[from as usize] != class
                        || from_lit == lit
                        || derived.toward.contains_key(&from_lit)
                    {
                        continue;
                    }
                    derived
                        .toward
                        .insert(from_lit, (graph.lits[at as usize], clause));
                    queue.push_back(from);
                }
            }
        }
        let mut seen: DetHashSet<Vec<Literal>> = DetHashSet::default();
        let mut clauses: Vec<(Vec<Literal>, usize)> = Vec::new();
        for &index in counted {
            let mut lits: Vec<Literal> = open(index)
                .into_iter()
                .map(|lit| derived.rep.get(&lit).copied().unwrap_or(lit))
                .collect();
            lits.sort_unstable();
            lits.dedup();
            if lits.windows(2).any(|pair| pair[0] == pair[1].negated())
                || !seen.insert(lits.clone())
            {
                continue;
            }
            clauses.push((lits, index));
        }
        Some(Rewritten { clauses })
    }

    /// The rewritten clause `lits` of pool clause `source`, as a derived
    /// step (or the source itself when nothing was rewritten).
    fn derive_rewritten(
        &mut self,
        derived: &mut Derived<'_>,
        lits: &[Literal],
        source: usize,
    ) -> Option<u64> {
        let pool = derived.pool;
        let value = &derived.prop.value;
        let clause = &pool.clauses[source];
        if clause.len() == lits.len() && clause.iter().all(|lit| lits.contains(lit)) {
            return Some(pool.ids[source]);
        }
        let mut hints: Vec<u64> = Vec::new();
        for lit in clause {
            let var = lit.variable().index();
            if value[var].is_some() {
                hints.extend(self.unit_hints(derived, var)?);
            }
        }
        for lit in clause {
            if value[lit.variable().index()].is_none() && derived.rep.contains_key(lit) {
                hints.push(self.shortcut(derived, *lit)?);
            }
        }
        hints.push(pool.ids[source]);
        let mut target = lits.to_vec();
        target.extend(derived.widen.iter().copied());
        self.record_chain(&target, &hints)
    }

    /// `(¬x ∨ rep(x))`, walked along `x`'s class.
    fn shortcut(&mut self, derived: &mut Derived<'_>, x: Literal) -> Option<u64> {
        if let Some(&id) = derived.shortcuts.get(&x) {
            return Some(id);
        }
        let rep = *derived.rep.get(&x)?;
        let mut hints: Vec<u64> = Vec::new();
        let mut at = x;
        let mut hops = 0;
        while at != rep {
            let (next, clause) = *derived.toward.get(&at)?;
            for lit in &derived.pool.clauses[clause] {
                let var = lit.variable().index();
                if derived.prop.value[var].is_some() {
                    hints.extend(self.unit_hints(derived, var)?);
                }
            }
            hints.push(derived.pool.ids[clause]);
            at = next;
            hops += 1;
            if hops > derived.toward.len() {
                return None;
            }
        }
        let mut target = vec![x.negated(), rep];
        target.extend(derived.widen.iter().copied());
        let id = self.record_chain(&target, &hints)?;
        derived.shortcuts.insert(x, id);
        Some(id)
    }
}

/// The local clauses (0-based) a refutation's empty clause rests on.
fn used_originals(dag: &ResolutionDag, originals: u64) -> Option<Vec<usize>> {
    let at: DetHashMap<u64, usize> = dag
        .derived
        .iter()
        .enumerate()
        .map(|(index, step)| (step.id, index))
        .collect();
    let mut used: DetHashSet<u64> = DetHashSet::default();
    let mut seen: DetHashSet<u64> = DetHashSet::default();
    let mut stack = vec![dag.empty_clause_id];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if id <= originals {
            used.insert(id);
            continue;
        }
        stack.extend(dag.derived.get(*at.get(&id)?)?.rup_hints.iter().copied());
    }
    let mut used: Vec<usize> = used
        .into_iter()
        .filter_map(|id| usize::try_from(id.checked_sub(1)?).ok())
        .collect();
    used.sort_unstable();
    Some(used)
}

#[cfg(test)]
mod owner_control_tests;
