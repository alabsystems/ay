// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The local, cone-restricted refutation problem for one candidate lemma.

use super::*;

/// The local refutation problem for one candidate.
pub(in crate::sat_sweep) struct Local {
    pub(in crate::sat_sweep) clauses: Vec<Vec<Literal>>,
    /// Global id of each local clause, `None` for an assumption unit.
    pub(in crate::sat_sweep) origin: Vec<Option<u64>>,
    /// Global variable of each local variable.
    pub(in crate::sat_sweep) global: Vec<usize>,
}

impl Sweep<'_, '_> {
    /// The clauses over exactly `cone`, the lemmas of its merged gates, and
    /// the `units`: each an assumption (`None`) or a hypothesis's unit lemma
    /// (`care.rs`) — or every clause, when `whole`.
    pub(in crate::sat_sweep) fn local(
        &self,
        cone: &[usize],
        whole: bool,
        units: &[(Literal, Option<u64>)],
    ) -> Local {
        let mut scratch = self.scratch.borrow_mut();
        let scratch::Scratch {
            inside,
            local: local_of,
            ..
        } = &mut *scratch;
        inside.clear();
        for &var in cone {
            inside.insert(var);
        }
        let ids = self.cone_clause_ids(cone, whole, inside);
        let mut clauses: Vec<Vec<Literal>> = Vec::with_capacity(ids.len() + units.len());
        let mut origin: Vec<Option<u64>> = Vec::with_capacity(clauses.capacity());
        for index in ids {
            // A root is never part of a candidate's problem (`by_owner`
            // holds none). Its membership is an index, not a scan of
            // `roots`: a split's leaf core is swept with every clause no
            // core gate defines as a root (`split/core_sweep.rs`). Measured
            // 2026-10-15 on the strict checker's 64-bit `(x / 7) * 7 <= x`
            // (model-checker-consumer R30): leaf cores of about 19,390 variables and about
            // 22,770 roots spent 26 of each core sweep's 33 s on that scan,
            // and the split's deadline, not its 100,000 conflicts, ended it
            // at 150 s. Indexed, a core sweep takes 7.5 s and the split ends
            // on its conflicts in 41 s.
            if !whole && self.is_root[index] {
                continue;
            }
            // The structural clauses of a gate over one operand twice repeat a
            // literal or carry both polarities; the bounded solver takes
            // neither, and neither changes what is refutable.
            if let Some(clause) = solver_clause(&self.cnf[index]) {
                clauses.push(clause);
                origin.push(Some(index as u64 + 1));
            }
        }
        self.push_merged_lemmas(cone, whole, &mut clauses, &mut origin);
        self.push_prime_clauses(cone, whole, inside, &mut clauses, &mut origin);
        for &(unit, id) in units {
            clauses.push(vec![unit]);
            origin.push(id);
        }
        // Compact the variables.
        local_of.clear();
        let mut global: Vec<usize> = Vec::new();
        for clause in &mut clauses {
            for lit in clause.iter_mut() {
                let var = lit.variable().index();
                let local = local_of.index_of(var, || {
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

    /// The CNF clauses inside the cone (every clause, when `whole`), sorted.
    fn cone_clause_ids(&self, cone: &[usize], whole: bool, inside: &scratch::Marks) -> Vec<usize> {
        if whole {
            return (0..self.cnf.len()).collect();
        }
        // A clause lies inside the cone only if its owner (its largest
        // variable) does, so each candidate is visited once, from its owner.
        // Indexing every variable instead visited a constant's whole
        // occurrence list — tens of thousands of clauses — for every cone it
        // entered: measured 2026-09-30 on external-codegen's 64-bit `SDIV`
        // definitional rows, building local problems took 74 of the sweep's
        // 84 seconds.
        let mut ids: Vec<usize> = Vec::new();
        for var in cone {
            for &index in &self.by_owner[*var] {
                if self.cnf[index]
                    .iter()
                    .all(|lit| inside.contains(lit.variable().index()))
                {
                    ids.push(index);
                }
            }
        }
        ids.sort_unstable();
        ids
    }

    /// The lemmas of the merged gates owned inside the cone (every gate's,
    /// when `whole`).
    fn push_merged_lemmas(
        &self,
        cone: &[usize],
        whole: bool,
        clauses: &mut Vec<Vec<Literal>>,
        origin: &mut Vec<Option<u64>>,
    ) {
        let lemma_owners: Vec<usize> = if whole {
            (0..self.nodes.len()).collect()
        } else {
            cone.to_vec()
        };
        for var in lemma_owners {
            let ids: &[u64] = match &self.merged[var] {
                Some(Merge::Const(id)) => std::slice::from_ref(id),
                Some(Merge::Equiv(_, ids)) => ids,
                None => continue,
            };
            for id in ids {
                if let Some(clause) = solver_clause(&self.derived[self.derived_at[id]].clause) {
                    clauses.push(clause);
                    origin.push(Some(*id));
                }
            }
        }
    }

    /// The prime clauses of the gates inside (`prime.rs`).
    fn push_prime_clauses(
        &self,
        cone: &[usize],
        whole: bool,
        inside: &scratch::Marks,
        clauses: &mut Vec<Vec<Literal>>,
        origin: &mut Vec<Option<u64>>,
    ) {
        let prime_owners: Box<dyn Iterator<Item = usize>> = if whole {
            Box::new(0..self.nodes.len())
        } else {
            Box::new(cone.iter().copied())
        };
        for var in prime_owners {
            for id in &self.prime[var] {
                let clause = &self.derived[self.derived_at[id]].clause;
                let inner = whole
                    || clause
                        .iter()
                        .all(|lit| inside.contains(lit.variable().index()));
                if let Some(clause) = solver_clause(clause).filter(|_| inner) {
                    clauses.push(clause);
                    origin.push(Some(*id));
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "local_tests.rs"]
mod tests;
