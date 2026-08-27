// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surgery-wide bound on proof vectors materialized by replacement emitters.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Proof, TermId, TermStore};

use super::super::proof_euf_lemma::{EufLemmaPlan, EufTarget};
use super::super::proof_trust_surgery_ite::{
    ProvenanceFarkasLemma, ProvenanceItePlan, ProvenanceIteSource,
};
use super::super::proof_trust_surgery_ite_branch::ProvenanceBranchLemma;
use super::super::proof_trust_surgery_provenance_or::{ProvenanceOrPlan, ProvenanceOrRefutation};
use super::super::proof_trust_surgery_provenance_or_transfer::ProvenanceOrBridge;
use super::taut_surface::MAX_EMITTED_CLAUSE_WIDTH;
use super::{
    AndDistinctKind, AssumePlan, IteLiftPlan, OrTautologyPlan, OrUnitPlan, QuantConsequencePlan,
    QuantInstanceChain, QuantNegationPlan, SubstEqPlan, TautRoute, TrichotomyPlan,
};

#[path = "proof_trust_surgery_volume_copied.rs"]
mod copied;

const MAX_EMITTED_VECTOR_ENTRIES: usize = 262_144;

pub(super) struct EmittedVolumePlans<'a> {
    pub(super) trichotomies: &'a HashMap<usize, TrichotomyPlan>,
    pub(super) ite_lifts: &'a HashMap<usize, IteLiftPlan>,
    pub(super) provenance_ite_lifts: &'a HashMap<usize, ProvenanceItePlan>,
    pub(super) exact_or_assumes: &'a HashMap<usize, TermId>,
    pub(super) provenance_or_plans: &'a HashMap<usize, ProvenanceOrPlan>,
    pub(super) or_units: &'a HashMap<usize, OrUnitPlan>,
    pub(super) taut_units: &'a HashMap<usize, OrTautologyPlan>,
    pub(super) euf_lemmas: &'a HashMap<usize, EufLemmaPlan>,
    pub(super) subst_eqs: &'a HashMap<usize, SubstEqPlan>,
    pub(super) quant_negations: &'a HashMap<usize, QuantNegationPlan>,
    pub(super) quant_consequences: &'a HashMap<usize, QuantConsequencePlan>,
    pub(super) assume_plans: &'a HashMap<usize, AssumePlan>,
    pub(super) unit_patterns: &'a HashMap<usize, (usize, usize)>,
    pub(super) quant_chains: &'a HashMap<(usize, usize), QuantInstanceChain>,
}

struct Volume {
    used: usize,
}

impl Volume {
    fn spend(&mut self, amount: usize) -> bool {
        let Some(used) = self.used.checked_add(amount) else {
            return false;
        };
        if used > MAX_EMITTED_VECTOR_ENTRIES {
            return false;
        }
        self.used = used;
        true
    }

    fn clause(&mut self, width: usize) -> bool {
        width <= MAX_EMITTED_CLAUSE_WIDTH && self.spend(width)
    }

    fn triangle(&mut self, width: usize) -> bool {
        if width > MAX_EMITTED_CLAUSE_WIDTH {
            return false;
        }
        let Some(amount) = width
            .checked_mul(width.saturating_add(1))
            .and_then(|product| product.checked_div(2))
        else {
            return false;
        };
        self.spend(amount)
    }

    fn decreasing(&mut self, start: usize, removals: usize) -> bool {
        if start > MAX_EMITTED_CLAUSE_WIDTH || removals > start {
            return false;
        }
        let Some(amount) = removals.checked_mul(start).and_then(|total| {
            removals
                .checked_mul(removals.saturating_add(1))
                .and_then(|product| product.checked_div(2))
                .and_then(|removed| total.checked_sub(removed))
        }) else {
            return false;
        };
        self.spend(amount)
    }
}

fn spend_farkas_chain(volume: &mut Volume, lemma: &ProvenanceFarkasLemma) -> bool {
    let width = lemma.clause.len();
    volume.clause(width) && volume.spend(width) && volume.decreasing(width, lemma.supports.len())
}

fn spend_ite_branch(volume: &mut Volume, lemma: &ProvenanceBranchLemma) -> bool {
    let width = lemma.clause().len();
    let certificate = match lemma {
        ProvenanceBranchLemma::Farkas(_) => volume.spend(width),
        ProvenanceBranchLemma::Transitive { .. } => true,
    };
    volume.clause(3)
        && volume.clause(width)
        && certificate
        && volume.clause(width.saturating_add(1))
        && volume.clause(width)
        && volume.decreasing(width, lemma.supports().len())
}

fn spend_provenance_ite(volume: &mut Volume, plan: &ProvenanceItePlan) -> bool {
    let prefix: usize = match &plan.source {
        ProvenanceIteSource::Formula => 4,
        ProvenanceIteSource::Defined { .. } => 14,
    };
    volume.spend(prefix.saturating_add(plan.supports.len()))
        && spend_ite_branch(volume, &plan.then_lemma)
        && spend_ite_branch(volume, &plan.else_lemma)
        && volume.clause(1)
}

fn spend_or_refutation(volume: &mut Volume, refutation: &ProvenanceOrRefutation) -> bool {
    match refutation {
        ProvenanceOrRefutation::Farkas { lemma, .. } => spend_farkas_chain(volume, lemma),
        ProvenanceOrRefutation::Ite(ite) => {
            let then_supports = ite
                .then_lemma
                .supports
                .iter()
                .filter(|&&support| support != ite.disjunct)
                .count();
            let else_supports = ite
                .else_lemma
                .supports
                .iter()
                .filter(|&&support| support != ite.disjunct)
                .count();
            let then_width = ite.then_lemma.clause.len();
            let else_width = ite.else_lemma.clause.len();
            volume.spend(4)
                && volume.clause(then_width)
                && volume.spend(then_width)
                && volume.clause(then_width)
                && volume.decreasing(then_width, then_supports)
                && volume.clause(else_width)
                && volume.spend(else_width)
                && volume.clause(else_width)
                && volume.decreasing(else_width, else_supports)
                && volume.clause(1)
        }
    }
}

fn spend_or_bridge(volume: &mut Volume, bridge: &ProvenanceOrBridge) -> bool {
    match bridge {
        ProvenanceOrBridge::Farkas { lemma, .. } => spend_farkas_chain(volume, lemma),
        ProvenanceOrBridge::Ite(ite) => {
            let branch =
                |volume: &mut Volume, lemma: &ProvenanceFarkasLemma, source: TermId| -> bool {
                    let supports = lemma
                        .supports
                        .iter()
                        .filter(|&&support| support != source)
                        .count();
                    let width = lemma.clause.len();
                    volume.clause(3)
                        && volume.clause(width)
                        && volume.spend(width)
                        && volume.clause(width.saturating_add(1))
                        && volume.clause(width)
                        && volume.decreasing(width, supports)
                };
            volume.spend(4)
                && branch(volume, &ite.then_lemma, ite.source)
                && branch(volume, &ite.else_lemma, ite.source)
                && volume.clause(2)
        }
    }
}

fn spend_provenance_or(volume: &mut Volume, plan: &ProvenanceOrPlan) -> bool {
    match plan {
        ProvenanceOrPlan::FalseDisjunct(plan) => {
            let width = plan.source_disjuncts.len();
            if plan.eliminations.len().saturating_add(plan.kept.len()) != width
                || !volume.spend(plan.authored_sources.len())
                || !volume.clause(width)
            {
                return false;
            }
            for _ in &plan.eliminations {
                // lemma clause, support resolution unit, shrinking resolution
                if !volume.clause(2) || !volume.clause(1) || !volume.clause(width) {
                    return false;
                }
            }
            // or_neg links plus packing resolutions plus the contraction
            volume.spend(plan.kept.len().saturating_mul(2))
                && volume.triangle(width)
                && volume.clause(1)
        }
        ProvenanceOrPlan::Conflict(plan) => {
            let width = plan.disjuncts.len();
            if plan.refutations.len() != width
                || !volume.spend(plan.authored_sources.len())
                || !volume.clause(width)
            {
                return false;
            }
            if plan
                .refutations
                .iter()
                .any(|refutation| !spend_or_refutation(volume, refutation))
            {
                return false;
            }
            volume.triangle(width.saturating_sub(1)) && volume.clause(1)
        }
        ProvenanceOrPlan::ConjunctiveConflict(plan) => {
            let width = plan.disjuncts.len();
            if plan.refutations.len() != width
                || !volume.spend(plan.authored_sources.len())
                || !volume.clause(width)
            {
                return false;
            }
            for refutation in &plan.refutations {
                let lemma_width = refutation.lemma.clause.len();
                if !volume.clause(lemma_width)
                    || !volume.spend(lemma_width)
                    || !volume.decreasing(lemma_width, refutation.lemma.supports.len())
                    || !volume.clause(2)
                    || !volume.spend(1)
                    || !volume.clause(1)
                {
                    return false;
                }
            }
            volume.triangle(width.saturating_sub(1)) && volume.clause(1)
        }
        ProvenanceOrPlan::ConjunctiveTransfer(plan) => {
            volume.spend(plan.emitted_literal_volume().unwrap_or(usize::MAX))
        }
        ProvenanceOrPlan::ExactTransfer(plan) => {
            let source_width = plan.source_disjuncts.len();
            let target_width = plan.target_disjuncts.len();
            if plan.bridges.len() != source_width
                || source_width != target_width
                || !volume.spend(plan.authored_sources.len())
                || !volume.clause(source_width)
            {
                return false;
            }
            for bridge in &plan.bridges {
                if !spend_or_bridge(volume, bridge) || !volume.clause(source_width) {
                    return false;
                }
            }
            for _ in &plan.target_disjuncts {
                if !volume.clause(2) || !volume.clause(source_width) {
                    return false;
                }
            }
            volume.clause(1)
        }
    }
}

fn spend_tautology(volume: &mut Volume, plan: &OrTautologyPlan) -> bool {
    let derive = |volume: &mut Volume, negs: &[TermId]| -> bool {
        let width = negs.len().saturating_add(1);
        if !volume.clause(width) {
            return false;
        }
        for _ in negs {
            if !volume.clause(2) || !volume.clause(width) {
                return false;
            }
        }
        negs.len() <= 1 || volume.clause(2)
    };
    let inner = match &plan.route {
        TautRoute::Plain { negs } => derive(volume, negs),
        TautRoute::And {
            conjs,
            per_conj_negs,
            ..
        } => {
            if conjs.len() != per_conj_negs.len()
                || per_conj_negs.iter().any(|negs| !derive(volume, negs))
                || !volume.clause(conjs.len().saturating_add(1))
            {
                return false;
            }
            for _ in conjs {
                if !volume.clause(conjs.len().saturating_add(1)) {
                    return false;
                }
            }
            (conjs.len() <= 1 || volume.clause(2)) && volume.spend(9)
        }
    };
    inner && volume.spend(5)
}

fn spend_or_unit(volume: &mut Volume, plan: &OrUnitPlan) -> bool {
    let width = plan.disjuncts.len();
    width == plan.eliminations.len().saturating_add(1)
        && volume.triangle(width)
        // The disjunction and complementary authored premises are hoisted.
        && volume.spend(width)
}

fn spend_and_distinct(
    volume: &mut Volume,
    terms: &TermStore,
    units: &[super::AndDistinctUnit],
    conjs: &[TermId],
) -> bool {
    for unit in units {
        if !volume.spend(3) {
            return false;
        }
        let ok = match &unit.kind {
            AndDistinctKind::Plain => true,
            AndDistinctKind::Arith { .. } => volume.spend(5),
            AndDistinctKind::DistinctBinary => volume.spend(7),
            AndDistinctKind::DistinctNary { count, .. } => match usize::try_from(*count) {
                Ok(count) => volume.spend(7usize.saturating_add(count.saturating_mul(3))),
                Err(_) => false,
            },
            AndDistinctKind::OrPerm { lits } => {
                let TermData::App(_, full) = terms.get(unit.raw) else {
                    return false;
                };
                let width = lits.len();
                let flips = lits
                    .iter()
                    .filter(|(raw, canonical)| raw != canonical)
                    .count();
                volume.clause(full.len())
                    && (full.len() == width || volume.clause(width))
                    && volume.spend(flips.saturating_mul(width.saturating_add(6)))
                    && volume.spend(width.saturating_mul(width.saturating_add(2)))
                    && volume.clause(1)
            }
        };
        if !ok {
            return false;
        }
    }
    volume.triangle(conjs.len().saturating_add(1))
}

fn spend_quant_chain(volume: &mut Volume, chain: &QuantInstanceChain) -> bool {
    if !volume.spend(chain.values.len()) || !volume.spend(4) {
        return false;
    }
    if let Some((_, atoms)) = &chain.guard {
        if !volume.clause(3) {
            return false;
        }
        if atoms.len() == 1 {
            if !volume.spend(2) {
                return false;
            }
        } else if !volume.triangle(atoms.len().saturating_add(1))
            || !volume.spend(atoms.len().saturating_mul(2))
        {
            return false;
        }
        if !volume.spend(3) {
            return false;
        }
    }
    chain.target == chain.body_lit || volume.spend(5)
}

/// Validate the total vector materialization before `Proof` construction.
pub(super) fn emitted_proof_volume_is_bounded(
    proof: &Proof,
    live: &[bool],
    terms: &TermStore,
    plans: EmittedVolumePlans<'_>,
) -> bool {
    let mut volume = Volume { used: 0 };
    if !copied::spend_original_proof(&mut volume, proof, live)
        || !volume.spend(plans.trichotomies.len().saturating_mul(20))
        || !volume.spend(plans.ite_lifts.len().saturating_mul(72))
        || !volume.spend(plans.exact_or_assumes.len())
    {
        return false;
    }
    for plan in plans.provenance_ite_lifts.values() {
        if !spend_provenance_ite(&mut volume, plan) {
            return false;
        }
    }
    for plan in plans.provenance_or_plans.values() {
        if !spend_provenance_or(&mut volume, plan) {
            return false;
        }
    }
    for plan in plans.or_units.values() {
        if !spend_or_unit(&mut volume, plan) {
            return false;
        }
    }
    let mut seen_tautologies = HashSet::default();
    for plan in plans.taut_units.values() {
        if seen_tautologies.insert(plan.term) && !spend_tautology(&mut volume, plan) {
            return false;
        }
    }
    let mut seen_euf_units = HashSet::default();
    for plan in plans.euf_lemmas.values() {
        let emitted = match plan.target {
            EufTarget::OrUnit { term } if !seen_euf_units.insert(term) => 0,
            _ => plan.emitted_literal_volume().unwrap_or(usize::MAX),
        };
        if !volume.spend(emitted) {
            return false;
        }
    }
    for plan in plans.subst_eqs.values() {
        if plan.lemma.len() != plan.hyps.len().saturating_add(1)
            || !volume.spend(plan.euf.emitted_literal_volume().unwrap_or(usize::MAX))
            || !volume.triangle(plan.lemma.len().saturating_sub(1))
            || !volume.spend(plan.hyps.len())
        {
            return false;
        }
    }
    for plan in plans.assume_plans.values() {
        let ok = match plan {
            AssumePlan::Distinct { .. } => volume.spend(7),
            AssumePlan::AndBounds { .. } | AssumePlan::QuantExpansion { .. } => true,
            AssumePlan::AndDistinct { units, conjs, .. } => {
                spend_and_distinct(&mut volume, terms, units, conjs)
            }
            AssumePlan::Literal { .. } => volume.spend(5),
        };
        if !ok {
            return false;
        }
    }
    for &(assume_index, position) in plans.unit_patterns.values() {
        let Some(plan) = plans.assume_plans.get(&assume_index) else {
            return false;
        };
        let amount = match plan {
            AssumePlan::Distinct { conjs, .. } if position < conjs.len() => 3,
            AssumePlan::AndBounds { raws, conjs, .. }
                if position < raws.len() && position < conjs.len() =>
            {
                if raws[position].1.is_some() {
                    8
                } else {
                    3
                }
            }
            AssumePlan::AndDistinct { conjs, .. } if position < conjs.len() => 0,
            AssumePlan::QuantExpansion { conjs, .. } if position < conjs.len() => 0,
            _ => return false,
        };
        if !volume.spend(amount) {
            return false;
        }
    }
    for chain in plans.quant_chains.values() {
        if !spend_quant_chain(&mut volume, chain) {
            return false;
        }
    }
    for plan in plans.quant_consequences.values() {
        if plan.lemma.len() != plan.supports.len().saturating_add(2)
            || !spend_quant_chain(&mut volume, &plan.chain)
            || !volume.triangle(plan.lemma.len())
            || !volume.spend(plan.lemma.len())
            || !volume.spend(plan.supports.len().saturating_add(1))
        {
            return false;
        }
    }
    for plan in plans.quant_negations.values() {
        if plan.lemma.len() != plan.supports.len().saturating_add(1)
            || plan.chain.guard.is_some()
            || !volume.spend(plan.chain.values.len().saturating_add(4))
            || !volume.triangle(plan.lemma.len())
            || !volume.spend(plan.lemma.len())
            || !volume.spend(plan.supports.len().saturating_add(1))
        {
            return false;
        }
    }
    true
}

#[cfg(test)]
#[path = "proof_trust_surgery_volume_tests.rs"]
mod tests;
