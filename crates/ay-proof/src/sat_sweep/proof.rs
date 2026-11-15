// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sweep's refutations: one local, cone-restricted refutation per
//! candidate lemma, stitched into the global DAG and replayed step by step.
//! The closing refutation of the root is `close.rs`.

use super::*;

mod local;
mod shallow;
pub(super) use local::Local;
use shallow::Shallow;

impl Sweep<'_, '_> {
    /// Prove the clause `lemma` from the CNF: never from the root itself,
    /// but, in a sweep under hypotheses (`care.rs`), from the unit lemmas the
    /// root implies.
    pub(super) fn prove(&mut self, lemma: &[Literal]) -> Attempt {
        // Nothing more is attempted once the candidates have read their
        // whole allowance (`work.rs`).
        if self.out_of_work() {
            return Attempt::Undecided;
        }
        let roots: Vec<usize> = lemma.iter().map(|lit| lit.variable().index()).collect();
        // First over the cone cut below the lemma's own gates (`shallow.rs`).
        let counted = match self.prove_shallow(lemma, &roots) {
            Shallow::Proved(id) => return Attempt::Proved(id),
            Shallow::Whole => false,
            Shallow::Cut => true,
        };
        let Some((cone, units)) = self.lemma_cone(&roots, false) else {
            return Attempt::Undecided;
        };
        match self.prove_over(lemma, &cone, units, counted) {
            // A counterexample the hypotheses exclude refutes nothing the
            // sweep cares about: the lemma is tried again under all of them.
            Attempt::Refuted(pattern) if self.outside_care(&pattern) => {
                match self.lemma_cone(&roots, true) {
                    Some((cone, units)) => self.prove_over(lemma, &cone, units, false),
                    None => Attempt::Undecided,
                }
            }
            other => other,
        }
    }

    /// Refute `lemma` over `cone`, from the `units` (`care.rs`) and the
    /// lemma's negation; `counted` when this candidate's call is already
    /// charged against `max_lemma_calls`.
    fn prove_over(
        &mut self,
        lemma: &[Literal],
        cone: &[usize],
        mut units: Vec<(Literal, Option<u64>)>,
        counted: bool,
    ) -> Attempt {
        if self.out_of_work() {
            return Attempt::Undecided;
        }
        units.extend(lemma.iter().map(|lit| (lit.negated(), None)));
        let local = self.local(cone, false, &units);
        self.lemma_calls += usize::from(!counted);
        // Most lemmas follow by unit propagation alone once the gates below
        // them are merged: record those as one RUP step, without a solver.
        if let Some(id) = self
            .propagate_candidate(&local)
            .and_then(|used| self.record_rup(&local, &used, lemma))
        {
            return Attempt::Proved(id);
        }
        match self.solve(local.global.len(), &local.clauses, self.lemma_conflicts) {
            Some(ResolutionSolveOutcome::Unsat(dag)) => match self.stitch(&local, &dag, lemma) {
                Some(id) => Attempt::Proved(id),
                None => Attempt::Undecided,
            },
            Some(ResolutionSolveOutcome::Sat(model)) => Attempt::Refuted(
                local
                    .global
                    .iter()
                    .zip(&model)
                    .filter(|(var, _)| matches!(self.nodes[**var], Gate::Input))
                    .map(|(var, value)| (*var, *value))
                    .collect(),
            ),
            None => Attempt::Undecided,
        }
    }

    /// The lemma as one derived step whose hints are the local clauses unit
    /// propagation `used` (in order, the conflict last), assumption units
    /// dropped; replayed like every stitched step.
    fn record_rup(&mut self, local: &Local, used: &[usize], lemma: &[Literal]) -> Option<u64> {
        let hints: Vec<u64> = used
            .iter()
            .filter_map(|&index| local.origin.get(index).copied().flatten())
            .collect();
        let (hints, clause) = self.normalized_hints(lemma, &hints)?;
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

    /// Renumber a local refutation into the global DAG, every clause widened
    /// by `widen`; the global id of its empty clause (the lemma).
    pub(super) fn stitch(
        &mut self,
        local: &Local,
        dag: &ResolutionDag,
        widen: &[Literal],
    ) -> Option<u64> {
        let original = local.clauses.len() as u64;
        let at: DetHashMap<u64, usize> = dag
            .derived
            .iter()
            .enumerate()
            .map(|(index, step)| (step.id, index))
            .collect();
        let mut used: DetHashSet<u64> = DetHashSet::default();
        let mut queue = vec![dag.empty_clause_id];
        while let Some(id) = queue.pop() {
            if id > original && used.insert(id) {
                queue.extend(dag.derived.get(*at.get(&id)?)?.rup_hints.iter().copied());
            }
        }
        let mut renumbered: DetHashMap<u64, u64> = DetHashMap::default();
        let mark = self.derived.len();
        for step in &dag.derived {
            if !used.contains(&step.id) {
                continue;
            }
            let mut clause: Vec<Literal> = Vec::with_capacity(step.clause.len() + widen.len());
            for lit in &step.clause {
                let var = *local.global.get(lit.variable().index())?;
                clause.push(literal(var, !lit.is_positive()));
            }
            for lit in widen {
                if !clause.contains(lit) {
                    clause.push(*lit);
                }
            }
            clause.dedup();
            let mut hints: Vec<u64> = Vec::with_capacity(step.rup_hints.len());
            for hint in &step.rup_hints {
                if *hint <= original {
                    if let Some(id) = local.origin.get(usize::try_from(*hint - 1).ok()?)? {
                        hints.push(*id);
                    }
                } else {
                    hints.push(*renumbered.get(hint)?);
                }
            }
            let Some((hints, clause)) = self.normalized_hints(&clause, &hints) else {
                self.derived.truncate(mark);
                return None;
            };
            let key = self.known_clauses.as_ref().map(|_| {
                let mut key = clause.clone();
                key.sort_unstable();
                key
            });
            if let (Some(known), Some(key)) = (&self.known_clauses, &key) {
                if let Some(&existing) = known.get(key) {
                    renumbered.insert(step.id, existing);
                    continue;
                }
            }
            let id = self.next_id;
            self.next_id += 1;
            if let (Some(known), Some(key)) = (&mut self.known_clauses, key) {
                known.insert(key, id);
            }
            renumbered.insert(step.id, id);
            self.derived_at.insert(id, self.derived.len());
            self.derived.push(RupStep {
                id,
                clause,
                rup_hints: hints,
            });
        }
        renumbered.get(&dag.empty_clause_id).copied()
    }

    pub(super) fn clause_of(&self, id: u64) -> Option<&[Literal]> {
        let original = self.cnf.len() as u64;
        if id >= 1 && id <= original {
            return self
                .cnf
                .get(usize::try_from(id - 1).ok()?)
                .map(Vec::as_slice);
        }
        Some(&self.derived.get(*self.derived_at.get(&id)?)?.clause)
    }

    /// Replay `hints` as unit propagation from the negation of `clause`,
    /// keeping only the hints that propagate and the one that conflicts, and
    /// return them with the clause the chain ACTUALLY derives: the resolvent
    /// of the conflict and the units it needs, a subset of `clause`. The
    /// transport replays exactly that resolution and lands on its resolvent,
    /// so a widened lemma step is recorded as the stronger clause it proves.
    ///
    /// The transport carries the root as a literal and so cannot use it as
    /// the CONFLICTING clause; a chain that ends on it is replayed again with
    /// the root first, where it can only propagate.
    pub(super) fn normalized_hints(
        &self,
        clause: &[Literal],
        hints: &[u64],
    ) -> Option<(Vec<u64>, Vec<Literal>)> {
        let (kept, resolvent) = self.replayed_hints(clause, hints)?;
        if !self.transport_root {
            return Some((kept, resolvent));
        }
        let root = self.roots[0] as u64 + 1;
        if kept.last() != Some(&root) {
            return Some((kept, resolvent));
        }
        let reordered: Vec<u64> = std::iter::once(root)
            .chain(hints.iter().copied().filter(|hint| *hint != root))
            .collect();
        self.replayed_hints(clause, &reordered)
            .filter(|(again, _)| again.last() != Some(&root))
    }

    fn replayed_hints(
        &self,
        clause: &[Literal],
        hints: &[u64],
    ) -> Option<(Vec<u64>, Vec<Literal>)> {
        let mut assigned: DetHashMap<usize, bool> = DetHashMap::default();
        for lit in clause {
            if assigned
                .insert(lit.variable().index(), !lit.is_positive())
                .is_some()
            {
                return None;
            }
        }
        let mut kept = Vec::with_capacity(hints.len());
        let mut units: Vec<Literal> = Vec::with_capacity(hints.len());
        let mut conflict = None;
        for &hint in hints {
            let hint_clause = self.clause_of(hint)?;
            let mut open: Option<Literal> = None;
            let mut satisfied = false;
            let mut several = false;
            for lit in hint_clause {
                match assigned.get(&lit.variable().index()) {
                    Some(value) if *value == lit.is_positive() => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => match open {
                        None => open = Some(*lit),
                        Some(existing) if existing == *lit => {}
                        // Both polarities of an open variable: a tautology.
                        Some(existing) if existing == lit.negated() => {
                            satisfied = true;
                            break;
                        }
                        Some(_) => several = true,
                    },
                }
            }
            if satisfied {
                continue;
            }
            if several {
                return None;
            }
            kept.push(hint);
            match open {
                None => {
                    conflict = Some(hint_clause);
                    break;
                }
                Some(unit) => {
                    assigned.insert(unit.variable().index(), unit.is_positive());
                    units.push(unit);
                }
            }
        }
        // Reverse resolution, exactly as the transport replays it.
        let mut resolvent: Vec<Literal> = Vec::new();
        for lit in conflict? {
            if !resolvent.contains(lit) {
                resolvent.push(*lit);
            }
        }
        let mut used = vec![false; units.len()];
        for (index, unit) in units.iter().enumerate().rev() {
            if !resolvent.contains(&unit.negated()) {
                continue;
            }
            used[index] = true;
            resolvent.retain(|lit| *lit != unit.negated());
            for lit in self.clause_of(kept[index])? {
                if lit != unit && !resolvent.contains(lit) {
                    resolvent.push(*lit);
                }
            }
        }
        if !resolvent.iter().all(|lit| clause.contains(lit)) {
            return None;
        }
        // Under the negation of the RESOLVENT only the hints the resolution
        // used still propagate, each from earlier ones or the resolvent.
        let conflict_hint = *kept.last()?;
        let mut chain: Vec<u64> = kept
            .iter()
            .zip(&used)
            .filter(|(_, used)| **used)
            .map(|(hint, _)| *hint)
            .collect();
        chain.push(conflict_hint);
        Some((chain, resolvent))
    }

    /// The transport carries the root as a literal, so a final chain whose
    /// only other clause is one derived lemma resolves NOTHING and prints no
    /// step. Replace that lemma by its own hints, under the root, until the
    /// final chain resolves.
    pub(super) fn inline_degenerate_final(&mut self) -> Option<()> {
        if !self.transport_root {
            return Some(());
        }
        let root = self.roots[0] as u64 + 1;
        let last = self.derived.len().checked_sub(1)?;
        for _ in 0..16 {
            let hints = &self.derived[last].rup_hints;
            let mut others = hints.iter().copied().filter(|hint| *hint != root);
            let (Some(only), None) = (others.next(), others.next()) else {
                return Some(());
            };
            let Some(&index) = self.derived_at.get(&only) else {
                return Some(());
            };
            let expanded: Vec<u64> = std::iter::once(root)
                .chain(
                    self.derived[index]
                        .rup_hints
                        .iter()
                        .copied()
                        .filter(|hint| *hint != root),
                )
                .collect();
            let clause = self.derived[last].clause.clone();
            let (chain, resolvent) = self.normalized_hints(&clause, &expanded)?;
            self.derived[last].rup_hints = chain;
            self.derived[last].clause = resolvent;
        }
        None
    }
}

/// `clause` without repeated literals, or `None` when it is a tautology.
pub(super) fn solver_clause(clause: &[Literal]) -> Option<Vec<Literal>> {
    let mut out: Vec<Literal> = Vec::with_capacity(clause.len());
    for lit in clause {
        if out.contains(&lit.negated()) {
            return None;
        }
        if !out.contains(lit) {
            out.push(*lit);
        }
    }
    Some(out)
}
