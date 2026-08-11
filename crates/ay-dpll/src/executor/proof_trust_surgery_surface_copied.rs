// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Retained-map checks for old proof steps copied through surgery.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, Symbol, TermId, TermStore};

use super::{term_child_count, ProvenanceSurfaceAudit, MAX_ALIAS_SCAN_TERMS, MAX_SURFACE_DEPTH};

#[path = "proof_trust_surgery_surface_copied_and.rs"]
mod and;
#[path = "proof_trust_surgery_surface_copied_ite.rs"]
mod ite;
#[path = "proof_trust_surgery_surface_copied_or.rs"]
mod or;

fn clause_of(step: &ProofStep) -> Option<&[TermId]> {
    match step {
        ProofStep::Step { clause, .. }
        | ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. } => Some(clause),
        ProofStep::Assume(_) | ProofStep::Anchor { .. } => None,
        _ => None,
    }
}

fn spend_scan_work(work: &mut usize, amount: usize) -> bool {
    let Some(next) = (*work).checked_add(amount) else {
        return false;
    };
    if next > MAX_ALIAS_SCAN_TERMS {
        return false;
    }
    *work = next;
    true
}

fn protect_premise_clauses(
    audit: &mut ProvenanceSurfaceAudit,
    proof: &Proof,
    terms: &mut TermStore,
    premises: impl IntoIterator<Item = ay_core::ProofId>,
    work: &mut usize,
) -> bool {
    for premise in premises {
        if !spend_scan_work(work, 1) {
            return false;
        }
        let Some(step) = proof.steps.get(premise.0 as usize) else {
            return false;
        };
        if let ProofStep::Assume(term) = step {
            audit.protect_operand(terms, *term);
            continue;
        }
        let Some(clause) = clause_of(step) else {
            continue;
        };
        if !spend_scan_work(work, clause.len()) {
            return false;
        }
        for &literal in clause {
            audit.protect_operand(terms, literal);
        }
    }
    true
}

impl ProvenanceSurfaceAudit {
    /// Generic resolution needs exact printed complements; copied Farkas
    /// lemmas need replay under the final map. Register both before merging.
    pub(in crate::executor) fn protect_copied_resolution_and_farkas_roles(
        &mut self,
        proof: &Proof,
        live: &[bool],
        replaced: &HashSet<usize>,
        terms: &mut TermStore,
    ) -> bool {
        if live.len() != proof.steps.len() {
            return false;
        }
        let mut work = 0usize;
        for (index, step) in proof.steps.iter().enumerate() {
            if !live[index] || replaced.contains(&index) {
                continue;
            }
            if !spend_scan_work(&mut work, 1) {
                return false;
            }
            match step {
                ProofStep::Step {
                    rule: rule @ AletheRule::AndPos(_),
                    clause,
                    premises,
                    args,
                } => {
                    if !premises.is_empty()
                        || !spend_scan_work(
                            &mut work,
                            clause.len().saturating_add(args.len()).saturating_add(1),
                        )
                        || !and::protect_copied_and_pos_role(
                            self, terms, rule, clause, args, &mut work,
                        )
                    {
                        return false;
                    }
                }
                ProofStep::Step {
                    rule: AletheRule::Or,
                    clause,
                    premises,
                    ..
                } => {
                    let [premise] = premises.as_slice() else {
                        return false;
                    };
                    let Some(premise_step) = proof.steps.get(premise.0 as usize) else {
                        return false;
                    };
                    let root = match premise_step {
                        ProofStep::Assume(term) => *term,
                        step => {
                            let Some([term]) = clause_of(step) else {
                                return false;
                            };
                            *term
                        }
                    };
                    let disjuncts = {
                        let TermData::App(Symbol::Named(op), disjuncts) = terms.get(root) else {
                            return false;
                        };
                        if op != "or"
                            || disjuncts.len() < 2
                            || disjuncts.len()
                                > crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS
                            || !spend_scan_work(
                                &mut work,
                                clause
                                    .len()
                                    .saturating_add(disjuncts.len())
                                    .saturating_add(1),
                            )
                        {
                            return false;
                        }
                        disjuncts.clone()
                    };
                    if !or::protect_or_composition_role(self, terms, root, &disjuncts) {
                        return false;
                    }
                    for &literal in clause {
                        self.protect_operand(terms, literal);
                    }
                }
                ProofStep::Step {
                    rule: rule @ AletheRule::OrPos(_),
                    clause,
                    premises,
                    args,
                } => {
                    if !premises.is_empty()
                        || !spend_scan_work(
                            &mut work,
                            clause.len().saturating_add(args.len()).saturating_add(1),
                        )
                        || !or::protect_copied_or_pos_role(self, terms, rule, clause, args)
                    {
                        return false;
                    }
                }
                ProofStep::Step {
                    rule:
                        rule @ (AletheRule::ItePos1
                        | AletheRule::ItePos2
                        | AletheRule::IteNeg1
                        | AletheRule::IteNeg2),
                    clause,
                    premises,
                    args,
                } => {
                    if !premises.is_empty()
                        || !spend_scan_work(
                            &mut work,
                            clause.len().saturating_add(args.len()).saturating_add(1),
                        )
                    {
                        return false;
                    }
                    if !ite::protect_copied_formula_ite_role(self, terms, rule, clause, args) {
                        return false;
                    }
                }
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => {
                    if !spend_scan_work(&mut work, clause.len().saturating_add(1)) {
                        return false;
                    }
                    for &literal in clause {
                        self.protect_operand(terms, literal);
                    }
                    self.protect_operand(terms, *pivot);
                    if !protect_premise_clauses(self, proof, terms, [*clause1, *clause2], &mut work)
                    {
                        return false;
                    }
                }
                ProofStep::Step {
                    rule: AletheRule::Resolution | AletheRule::ThResolution,
                    clause,
                    premises,
                    args,
                } => {
                    if !spend_scan_work(&mut work, clause.len().saturating_add(args.len()))
                        || premises.len() > MAX_ALIAS_SCAN_TERMS.saturating_sub(work)
                    {
                        return false;
                    }
                    for &literal in clause.iter().chain(args) {
                        self.protect_operand(terms, literal);
                    }
                    if !protect_premise_clauses(
                        self,
                        proof,
                        terms,
                        premises.iter().copied(),
                        &mut work,
                    ) {
                        return false;
                    }
                }
                ProofStep::TheoryLemma {
                    clause,
                    farkas: Some(farkas),
                    ..
                } => {
                    if !spend_scan_work(&mut work, clause.len()) {
                        return false;
                    }
                    self.protect_farkas_lemma(terms, clause, farkas);
                }
                _ => {}
            }
        }
        !self.overflowed
    }
}

fn roots_intersect_overrides(
    roots: &[TermId],
    terms: &TermStore,
    effective: &HashMap<TermId, String>,
    work: &mut usize,
) -> bool {
    let mut pending: Vec<(TermId, usize)> = roots.iter().map(|&term| (term, 0usize)).collect();
    let mut seen = HashSet::default();
    while let Some((term, depth)) = pending.pop() {
        *work = work.saturating_add(1);
        if *work > MAX_ALIAS_SCAN_TERMS || depth > MAX_SURFACE_DEPTH {
            return true;
        }
        if effective.contains_key(&term) {
            return true;
        }
        if !seen.insert(term) {
            continue;
        }
        let Some(child_count) = term_child_count(terms, term) else {
            return true;
        };
        if child_count
            > MAX_ALIAS_SCAN_TERMS
                .saturating_sub(*work)
                .saturating_sub(pending.len())
        {
            return true;
        }
        for child in terms.children(term) {
            pending.push((child, depth + 1));
        }
    }
    false
}

fn structural_rule_needs_canonical_operands(rule: &AletheRule) -> bool {
    !matches!(
        rule,
        AletheRule::Resolution
            | AletheRule::ThResolution
            | AletheRule::Contraction
            | AletheRule::Weakening
            | AletheRule::AndPos(_)
            | AletheRule::Or
            | AletheRule::OrPos(_)
            | AletheRule::ItePos1
            | AletheRule::ItePos2
            | AletheRule::IteNeg1
            | AletheRule::IteNeg2
    )
}

/// Reject any unplanned positional rule whose conclusion, arguments, or
/// referenced premise clause is changed by the retained map.
pub(in crate::executor) fn copied_structural_roles_are_static(
    proof: &Proof,
    live: &[bool],
    replaced: &HashSet<usize>,
    terms: &TermStore,
    effective: &HashMap<TermId, String>,
) -> bool {
    if effective.is_empty() {
        return true;
    }
    if live.len() != proof.steps.len() {
        return false;
    }
    let mut work = 0usize;
    for (index, step) in proof.steps.iter().enumerate() {
        if !live[index] || replaced.contains(&index) {
            continue;
        }
        work = work.saturating_add(1);
        if work > MAX_ALIAS_SCAN_TERMS {
            return false;
        }
        let mut roots = Vec::new();
        let premises = match step {
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } if structural_rule_needs_canonical_operands(rule) => {
                if clause.len().saturating_add(args.len())
                    > MAX_ALIAS_SCAN_TERMS.saturating_sub(work)
                {
                    return false;
                }
                roots.extend(clause.iter().copied());
                roots.extend(args.iter().copied());
                Some(premises.as_slice())
            }
            ProofStep::TheoryLemma { clause, farkas, .. } if farkas.is_none() => {
                if clause.len() > MAX_ALIAS_SCAN_TERMS.saturating_sub(work) {
                    return false;
                }
                roots.extend(clause.iter().copied());
                None
            }
            _ => continue,
        };
        if let Some(premises) = premises {
            if premises.len() > MAX_ALIAS_SCAN_TERMS.saturating_sub(work) {
                return false;
            }
            for premise in premises {
                work = work.saturating_add(1);
                let Some(step) = proof.steps.get(premise.0 as usize) else {
                    return false;
                };
                if let ProofStep::Assume(term) = step {
                    roots.push(*term);
                    continue;
                }
                let Some(clause) = clause_of(step) else {
                    return false;
                };
                if roots.len().saturating_add(clause.len())
                    > MAX_ALIAS_SCAN_TERMS.saturating_sub(work)
                {
                    return false;
                }
                roots.extend(clause.iter().copied());
            }
        }
        if roots_intersect_overrides(&roots, terms, effective, &mut work) {
            return false;
        }
    }
    true
}

#[cfg(test)]
#[path = "proof_trust_surgery_surface_copied_tests.rs"]
mod tests;
