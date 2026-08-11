// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked emission for exact conjunctive provenance-OR transfer.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TermStore, TheoryLemmaKind};

use super::{
    conjunctive_transfer_plan_shape_is_valid, ProvenanceOrAndMapping,
    ProvenanceOrAndTransferOutcome, ProvenanceOrAndTransferPlan,
};
use crate::executor::proof_repair::proof_trust_surgery_provenance::complement_of;
use crate::executor::proof_repair::proof_trust_surgery_provenance_or::ProvenanceOrAndRefutation;
use crate::executor::Executor;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct SignedLiteral {
    atom: TermId,
    positive: bool,
}

impl SignedLiteral {
    fn negated(self) -> Self {
        Self {
            atom: self.atom,
            positive: !self.positive,
        }
    }
}

fn decode_literal(terms: &TermStore, mut literal: TermId) -> SignedLiteral {
    let mut positive = true;
    while let TermData::Not(inner) = terms.get(literal) {
        literal = *inner;
        positive = !positive;
    }
    SignedLiteral {
        atom: literal,
        positive,
    }
}

/// Return the checker-equivalent parity set while rejecting two distinct raw
/// spellings for one signed literal. Generated clauses never need that native-
/// only ambiguity, and declining keeps the external Alethe residual exact.
fn exact_clause_set(terms: &TermStore, clause: &[TermId]) -> Option<Vec<(SignedLiteral, TermId)>> {
    let mut set: Vec<_> = clause
        .iter()
        .copied()
        .map(|literal| (decode_literal(terms, literal), literal))
        .collect();
    set.sort_unstable();
    for pair in set.windows(2) {
        if pair[0].0 == pair[1].0 && pair[0].1 != pair[1].1 {
            return None;
        }
    }
    set.dedup_by_key(|entry| entry.0);
    Some(set)
}

fn resolve_clause(
    terms: &TermStore,
    left: &[TermId],
    right: &[TermId],
    pivot: TermId,
) -> Option<Vec<TermId>> {
    let left = exact_clause_set(terms, left)?;
    let right = exact_clause_set(terms, right)?;
    let pivot = decode_literal(terms, pivot);
    for (left_pivot, right_pivot) in [(pivot, pivot.negated()), (pivot.negated(), pivot)] {
        if !left.iter().any(|entry| entry.0 == left_pivot)
            || !right.iter().any(|entry| entry.0 == right_pivot)
        {
            continue;
        }
        let mut result: Vec<_> = left
            .iter()
            .copied()
            .filter(|entry| entry.0 != left_pivot)
            .chain(right.iter().copied().filter(|entry| entry.0 != right_pivot))
            .collect();
        result.sort_unstable();
        for pair in result.windows(2) {
            if pair[0].0 == pair[1].0 && pair[0].1 != pair[1].1 {
                return None;
            }
        }
        result.dedup_by_key(|entry| entry.0);
        return Some(result.into_iter().map(|entry| entry.1).collect());
    }
    None
}

fn exact_clause_matches(terms: &TermStore, actual: &[TermId], expected: &[TermId]) -> bool {
    exact_clause_set(terms, actual)
        .zip(exact_clause_set(terms, expected))
        .is_some_and(|(actual, expected)| actual == expected)
}

fn add_checked_resolution(
    proof: &mut Proof,
    terms: &TermStore,
    left_id: ProofId,
    left: &[TermId],
    right_id: ProofId,
    right: &[TermId],
    pivot: TermId,
) -> Option<(ProofId, Vec<TermId>)> {
    let clause = resolve_clause(terms, left, right, pivot)?;
    let id = proof.add_resolution(clause.clone(), pivot, left_id, right_id);
    Some((id, clause))
}

fn add_farkas_refutation(
    proof: &mut Proof,
    terms: &mut TermStore,
    refutation: &ProvenanceOrAndRefutation,
    authored_assumes: &HashMap<TermId, ProofId>,
) -> Option<(ProofId, Vec<TermId>)> {
    let mut current = proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: refutation.lemma.clause.clone(),
        farkas: Some(refutation.lemma.farkas.clone()),
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });
    let mut clause = refutation.lemma.clause.clone();
    for &support in &refutation.lemma.supports {
        let assume = *authored_assumes.get(&support)?;
        (current, clause) =
            add_checked_resolution(proof, terms, current, &clause, assume, &[support], support)?;
    }
    let not_conjunct = complement_of(terms, refutation.conjunct);
    if !exact_clause_matches(terms, &clause, &[not_conjunct]) {
        return None;
    }
    let not_disjunct = complement_of(terms, refutation.disjunct);
    let projection_clause = vec![not_disjunct, refutation.conjunct];
    let projection = proof.add_rule_step(
        AletheRule::AndPos(refutation.index),
        projection_clause.clone(),
        Vec::new(),
        vec![refutation.disjunct],
    );
    let (current, clause) = add_checked_resolution(
        proof,
        terms,
        current,
        &clause,
        projection,
        &projection_clause,
        refutation.conjunct,
    )?;
    exact_clause_matches(terms, &clause, &[not_disjunct]).then_some((current, clause))
}

fn add_true_bridge(
    proof: &mut Proof,
    terms: &mut TermStore,
    truth_step: &mut Option<ProofId>,
    source: TermId,
) -> (ProofId, Vec<TermId>) {
    let truth = terms.mk_bool(true);
    let truth_step = *truth_step.get_or_insert_with(|| {
        proof.add_rule_step(AletheRule::True, vec![truth], Vec::new(), Vec::new())
    });
    let not_source = complement_of(terms, source);
    let clause = vec![truth, not_source];
    let step = proof.add_rule_step(
        AletheRule::Weakening,
        clause.clone(),
        vec![truth_step],
        Vec::new(),
    );
    (step, clause)
}

fn add_mapping(
    proof: &mut Proof,
    terms: &mut TermStore,
    mapping: &ProvenanceOrAndMapping,
    truth_step: &mut Option<ProofId>,
) -> Option<(ProofId, Vec<TermId>)> {
    let not_source = complement_of(terms, mapping.source);
    let mut clause = Vec::with_capacity(mapping.target_children.len() + 1);
    clause.push(mapping.target);
    for &child in &mapping.target_children {
        clause.push(complement_of(terms, child));
    }
    let mut current = proof.add_rule_step(
        AletheRule::AndNeg,
        clause.clone(),
        Vec::new(),
        vec![mapping.target],
    );
    for projection in &mapping.projections {
        let link_clause = vec![not_source, projection.conjunct];
        let link = proof.add_rule_step(
            AletheRule::AndPos(projection.index),
            link_clause.clone(),
            Vec::new(),
            vec![mapping.source],
        );
        (current, clause) = add_checked_resolution(
            proof,
            terms,
            current,
            &clause,
            link,
            &link_clause,
            projection.conjunct,
        )?;
    }
    if mapping.has_true {
        let truth = terms.mk_bool(true);
        let (link, link_clause) = add_true_bridge(proof, terms, truth_step, mapping.source);
        (current, clause) =
            add_checked_resolution(proof, terms, current, &clause, link, &link_clause, truth)?;
    }
    let expected = [mapping.target, not_source];
    exact_clause_matches(terms, &clause, &expected).then_some((current, clause))
}

impl Executor {
    pub(in crate::executor::proof_repair) fn emit_provenance_or_and_transfer(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrAndTransferPlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        if !conjunctive_transfer_plan_shape_is_valid(&mut self.ctx.terms, plan) {
            return None;
        }
        let &or_assume = authored_assumes.get(&plan.orig)?;
        if plan.outcomes.iter().any(|outcome| match outcome {
            ProvenanceOrAndTransferOutcome::Refute(refutation) => refutation
                .lemma
                .supports
                .iter()
                .any(|support| !authored_assumes.contains_key(support)),
            ProvenanceOrAndTransferOutcome::Map(_) => false,
        }) {
            return None;
        }

        let mut current = proof.add_rule_step(
            AletheRule::Or,
            plan.source_disjuncts.clone(),
            vec![or_assume],
            Vec::new(),
        );
        let mut current_clause = plan.source_disjuncts.clone();
        let mut truth_step = None;
        for outcome in &plan.outcomes {
            let source = outcome.source();
            let (bridge, bridge_clause) = match outcome {
                ProvenanceOrAndTransferOutcome::Refute(refutation) => {
                    add_farkas_refutation(proof, &mut self.ctx.terms, refutation, authored_assumes)?
                }
                ProvenanceOrAndTransferOutcome::Map(mapping) => {
                    add_mapping(proof, &mut self.ctx.terms, mapping, &mut truth_step)?
                }
            };
            (current, current_clause) = add_checked_resolution(
                proof,
                &self.ctx.terms,
                current,
                &current_clause,
                bridge,
                &bridge_clause,
                source,
            )?;
        }
        if !exact_clause_matches(&self.ctx.terms, &current_clause, &plan.remaining_targets) {
            return None;
        }
        if plan.remaining_targets.is_empty() {
            return Some(proof.add_rule_step(
                AletheRule::Weakening,
                vec![plan.goal],
                vec![current],
                Vec::new(),
            ));
        }
        for &target in &plan.remaining_targets {
            let not_target = complement_of(&mut self.ctx.terms, target);
            let link_clause = vec![plan.goal, not_target];
            let link = proof.add_rule_step(
                AletheRule::OrNeg,
                link_clause.clone(),
                Vec::new(),
                vec![plan.goal],
            );
            (current, current_clause) = add_checked_resolution(
                proof,
                &self.ctx.terms,
                current,
                &current_clause,
                link,
                &link_clause,
                target,
            )?;
        }
        if !exact_clause_matches(&self.ctx.terms, &current_clause, &[plan.goal]) {
            return None;
        }
        Some(proof.add_rule_step(
            AletheRule::Contraction,
            vec![plan.goal],
            vec![current],
            Vec::new(),
        ))
    }
}
