// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use std::collections::BTreeSet;

pub(super) struct Native<'cnf, 'terms> {
    pub(super) cnf: &'cnf CountedCnf<'terms>,
    pub(super) proof: Proof,
    pub(super) assumptions: Vec<ProofId>,
    rows: Vec<(Vec<i32>, ProofId)>,
    pub(super) source_steps: Vec<ProofId>,
    pub(super) bridge_steps: Vec<ProofId>,
}

impl<'cnf, 'terms> Native<'cnf, 'terms> {
    pub(super) fn from_cnf(cnf: &'cnf CountedCnf<'terms>) -> Self {
        cnf.check().unwrap();
        assert_eq!(cnf.theory_atoms(), []);
        let mut proof = Proof::new();
        let assumptions: Vec<_> = cnf
            .roots()
            .iter()
            .map(|root| proof.add_assume(*root, None))
            .collect();
        let mut source_steps = Vec::new();
        let mut bridge_steps = Vec::new();
        for step in cnf.steps() {
            let clause = step
                .clause()
                .iter()
                .map(|lit| cnf.source_literal_term(*lit).unwrap())
                .collect();
            let id = if let (Some([left, right]), Some(pivot)) = (step.premises(), step.pivot()) {
                assert_eq!(step.rule(), &AletheRule::Resolution);
                assert!(left < source_steps.len() && right < source_steps.len());
                let id =
                    proof.add_resolution(clause, pivot, source_steps[left], source_steps[right]);
                bridge_steps.push(id);
                id
            } else {
                assert!(step.premises().is_none() && step.pivot().is_none());
                proof.add_rule_step(step.rule().clone(), clause, vec![], vec![step.source()])
            };
            source_steps.push(id);
        }
        assert_eq!(proof.steps.len(), cnf.roots().len() + cnf.steps().len());
        let rows = cnf
            .rows()
            .iter()
            .map(|row| {
                let id = match row.justification() {
                    Justification::Root(root) => {
                        assumptions[cnf.roots().iter().position(|id| *id == root).unwrap()]
                    }
                    Justification::Step(index) => source_steps[index],
                };
                let mut literals = row.literals().to_vec();
                literals.sort_unstable();
                literals.dedup();
                (literals, id)
            })
            .collect();
        cnf.check().unwrap();
        Self {
            cnf,
            proof,
            assumptions,
            rows,
            source_steps,
            bridge_steps,
        }
    }

    /// Derive, not assume, every simplified row with actual binary resolution.
    pub(super) fn close_by_units(&mut self) {
        let mut processed = BTreeSet::new();
        loop {
            self.cnf.check().unwrap();
            let unit = self
                .rows
                .iter()
                .find_map(|(clause, proof)| {
                    (clause.len() == 1 && !processed.contains(&clause[0]))
                        .then(|| (clause[0], *proof))
                })
                .expect("test contradiction must be unit-refutable");
            processed.insert(unit.0);
            for index in 0..self.rows.len() {
                if !self.rows[index].0.contains(&-unit.0) || self.rows[index].0.contains(&unit.0) {
                    continue;
                }
                let premise = self.rows[index].1;
                let reduced: Vec<_> = self.rows[index]
                    .0
                    .iter()
                    .copied()
                    .filter(|lit| *lit != -unit.0)
                    .collect();
                let clause = reduced
                    .iter()
                    .map(|lit| self.cnf.sat_literal_term(*lit).unwrap())
                    .collect();
                let pivot = self
                    .cnf
                    .sat_literal_term(unit.0.checked_abs().unwrap())
                    .unwrap();
                let proof = self.proof.add_resolution(clause, pivot, unit.1, premise);
                if reduced.is_empty() {
                    return;
                }
                self.rows[index] = (reduced, proof);
            }
        }
    }

    pub(super) fn require_valid(&self) {
        self.cnf.check().unwrap();
        let quality = ay_proof::check_proof_strict_with_context(
            &self.proof,
            self.cnf.terms(),
            None,
            None,
            Some(self.cnf.roots()),
        )
        .unwrap();
        assert_eq!(quality.hole_count, 0);
        assert_eq!(quality.trust_count, 0);
        assert_eq!(quality.theory_lemma_count, 0);
        assert!(
            matches!(self.proof.steps.last(), Some(ProofStep::Resolution { clause, .. }) if clause.is_empty())
        );
        self.cnf.check().unwrap();
    }

    pub(super) fn require_rejected(&self, proof: &Proof) {
        self.cnf.check().unwrap();
        assert!(ay_proof::check_proof_strict_with_context(
            proof,
            self.cnf.terms(),
            None,
            None,
            Some(self.cnf.roots()),
        )
        .is_err());
        self.cnf.check().unwrap();
    }
}
