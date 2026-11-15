// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sweep's closing refutation, and the trimming every finished DAG gets:
//! only the steps its empty clause rests on.

use super::*;

/// What the closing refutation found when it ran before any sweep
/// ([`refute_directly`]).
pub(crate) enum Direct {
    /// A refutation of the roots.
    Refuted(ResolutionDag),
    /// Its solve over EVERY clause found a model. That solve reads the CNF
    /// and only clauses the sweep derived from it (aliases, prime clauses),
    /// so the CNF itself is satisfiable and no lane can refute it.
    Satisfiable,
    /// Neither, within its limits.
    Undecided,
}

/// The closing refutation [`refute`] ends with, run before any candidate is
/// swept: the refutation of `roots` when no gate is merged, within `limits`,
/// each solver call retaining at most `proof_output_bytes` of binary LRAT.
/// A root whose cone refutes cheaply needs no lemma, and a caller that tries
/// this first pays only its budget when the root does need them. Its solve
/// over every clause may instead find a model ([`Direct::Satisfiable`]).
pub(crate) fn refute_directly(
    gates: Vec<Gate>,
    cnf: &[Vec<Literal>],
    roots: &[usize],
    transport_root: bool,
    limits: SweepLimits,
    proof_output_bytes: usize,
    keep_going: &mut dyn FnMut() -> bool,
) -> Direct {
    let Some(mut sweep) = Sweep::new(gates, cnf, roots, transport_root, limits, keep_going) else {
        return Direct::Undecided;
    };
    sweep.proof_output_bytes = proof_output_bytes;
    sweep.close_direct()
}

impl Sweep<'_, '_> {
    /// The closing refutation over the root's cone, then over everything,
    /// telling a model of the whole CNF from a solve that ran out.
    pub(super) fn close_direct(mut self) -> Direct {
        match self.close_inner() {
            Some(dag) => Direct::Refuted(dag),
            None if self.satisfiable => Direct::Satisfiable,
            None => Direct::Undecided,
        }
    }

    /// The closing refutation, and what the sweep spent of `limits`.
    pub(super) fn close_counted(
        mut self,
        limits: SweepLimits,
    ) -> (Option<ResolutionDag>, work::Spent) {
        let closed = self.close_inner();
        (closed, self.spent(limits))
    }

    /// Append every root clause to the cone's `local` problem, each root
    /// variable numbered once: one already in `local` keeps its number, any
    /// other is numbered after the rest. The numbers come from a map rather
    /// than a scan of `local.global` per literal: a split's leaf core is
    /// swept with tens of thousands of roots (`proof/local.rs`).
    pub(super) fn push_roots(&self, local: &mut proof::Local) {
        let mut local_of: DetHashMap<usize, usize> = local
            .global
            .iter()
            .enumerate()
            .map(|(index, &var)| (var, index))
            .collect();
        for &root in &self.roots {
            let clause = self.cnf[root]
                .iter()
                .map(|lit| {
                    let var = lit.variable().index();
                    let index = *local_of.entry(var).or_insert_with(|| {
                        local.global.push(var);
                        local.global.len() - 1
                    });
                    literal(index, !lit.is_positive())
                })
                .collect();
            local.clauses.push(clause);
            local.origin.push(Some(root as u64 + 1));
        }
    }

    fn close_inner(&mut self) -> Option<ResolutionDag> {
        let mut seeds: Vec<usize> = self
            .roots
            .iter()
            .flat_map(|&root| self.cnf[root].iter().map(|lit| lit.variable().index()))
            .collect();
        seeds.sort_unstable();
        seeds.dedup();
        let mut empty = None;
        for whole in [false, true] {
            let cone = if whole {
                Vec::new()
            } else {
                match self.cone(&seeds) {
                    Some(cone) => cone,
                    None => continue,
                }
            };
            // Under hypotheses (`care.rs`) the merges hold only where they
            // do, so the root's cone is refuted with their unit lemmas.
            let hypotheses = if whole {
                Vec::new()
            } else {
                self.care_units_all()
            };
            let mut local = self.local(&cone, whole, &hypotheses);
            if !whole {
                self.push_roots(&mut local);
            }
            let outcome = self.solve(local.global.len(), &local.clauses, FINAL_CONFLICTS);
            // A model of the cone under hypotheses says nothing about the
            // CNF; one of every clause does.
            self.satisfiable |= whole && matches!(outcome, Some(ResolutionSolveOutcome::Sat(_)));
            if let Some(ResolutionSolveOutcome::Unsat(dag)) = outcome {
                empty = self
                    .stitch(&local, &dag, &[])
                    .and_then(|id| self.inline_degenerate_final().map(|()| id));
                if empty.is_some() {
                    break;
                }
            }
        }
        let empty = empty?;
        let dag = ResolutionDag {
            num_vars: self.nodes.len(),
            original_clauses: self
                .cnf
                .iter()
                .enumerate()
                .map(|(index, clause)| (index as u64 + 1, clause.clone()))
                .collect(),
            derived: reachable(std::mem::take(&mut self.derived), &self.derived_at, empty),
            empty_clause_id: empty,
        };
        // Every step was replayed as it was stitched (`replayed_hints`),
        // over literal SETS as the transport and the consumer read a clause.
        // `ResolutionDag::validate` scores a hint by literal OCCURRENCES, so a
        // gate over one operand twice (`(cl g (not x) (not x))`) reads as
        // non-unit there; it is not the arbiter for this DAG.
        Some(dag)
    }
}

/// The steps of `derived` the empty clause `root` actually rests on, in
/// their order. Every candidate lemma the sweep proved is stitched, but only
/// the merges the closing refutation used are needed: measured 2026-09-29 on
/// external-codegen's `LDP` and `BFM` rows, the whole swept DAG exceeded the strict
/// checker's 4,000,000 replay hints although the refutation rests on far
/// fewer. Dropping the rest changes no refutation, only its size.
pub(super) fn reachable(
    derived: Vec<RupStep>,
    at: &DetHashMap<u64, usize>,
    root: u64,
) -> Vec<RupStep> {
    let mut keep = vec![false; derived.len()];
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        let Some(&index) = at.get(&id) else {
            continue;
        };
        if !std::mem::replace(&mut keep[index], true) {
            stack.extend(derived[index].rup_hints.iter().copied());
        }
    }
    // Collected into a fresh vector: an in-place collect would keep the
    // whole sweep's capacity, which the replay charges as retained bytes.
    let count = keep.iter().filter(|kept| **kept).count();
    let mut steps = Vec::with_capacity(count);
    steps.extend(
        derived
            .into_iter()
            .zip(keep)
            .filter_map(|(step, kept)| kept.then_some(step)),
    );
    steps
}

#[cfg(test)]
#[path = "close_tests.rs"]
mod tests;
