// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked proof emission for provenance-authenticated arithmetic ITE plans.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TheoryLemmaKind};

use super::proof_trust_surgery_ite::{ProvenanceItePlan, ProvenanceIteSource};
use super::proof_trust_surgery_ite_branch::ProvenanceBranchLemma;
use super::proof_trust_surgery_provenance::{complement_of, ProvenanceSurfaceAudit};
use super::Executor;

struct IteBranch<'a> {
    guard: TermId,
    source_fact: TermId,
    source_step: ProofId,
    lifted: TermId,
    lemma: &'a ProvenanceBranchLemma,
}

impl ProvenanceItePlan {
    pub(in crate::executor) fn goal(&self) -> TermId {
        self.goal
    }

    pub(in crate::executor) fn authored_assumption_terms(
        &self,
    ) -> impl Iterator<Item = TermId> + '_ {
        std::iter::once(self.orig).chain(self.supports.iter().copied())
    }

    pub(super) fn protect_surface_operands(
        &self,
        audit: &mut ProvenanceSurfaceAudit,
        terms: &mut ay_core::TermStore,
    ) {
        // The authored premise is consumed directly by ite1/ite2 (or by the
        // ite_intro bridge), even when a zero Farkas row prunes it later.
        audit.protect_operand(terms, self.orig);
        audit.protect_rigid_root(terms, self.goal);
        audit.protect_operand(terms, self.cond);
        for operand in [
            self.source_then,
            self.source_else,
            self.lifted_then,
            self.lifted_else,
        ] {
            audit.protect_farkas_operand(terms, operand);
        }
        if let ProvenanceIteSource::Defined {
            ite_term,
            ite_def,
            and_term,
            intro_eq,
        } = &self.source
        {
            for operand in [*ite_def, *and_term, *intro_eq] {
                audit.protect_rigid_root(terms, operand);
            }
            audit.protect_ite_intro_role(terms, *ite_term, self.source_then, self.source_else);
        }
        for lemma in [&self.then_lemma, &self.else_lemma] {
            match lemma {
                ProvenanceBranchLemma::Farkas(lemma) => {
                    audit.protect_farkas_lemma(terms, &lemma.clause, &lemma.farkas);
                }
                ProvenanceBranchLemma::Transitive { clause, .. } => {
                    for &hypothesis in &clause[..clause.len().saturating_sub(1)] {
                        audit.protect_operand(terms, hypothesis);
                    }
                    if let Some(&conclusion) = clause.last() {
                        audit.protect_rigid_operand(terms, conclusion);
                    }
                }
            }
        }
    }
}

impl Executor {
    /// Emit the checked ITE/branch derivation planned by the sibling module.
    ///
    /// Its full-unit route is valid only after retained-surface finalization
    /// has removed any whole-term override for `plan.goal`.
    pub(in crate::executor::proof_repair) fn emit_ite_lift(
        &mut self,
        new_proof: &mut Proof,
        plan: &ProvenanceItePlan,
        authored_assumes: &HashMap<TermId, ProofId>,
        surface: Option<&HashMap<TermId, String>>,
    ) -> Option<ProofId> {
        if surface?.contains_key(&plan.goal) {
            return None;
        }
        let (not_cond, source_then, source_else) =
            self.emit_provenance_ite_source_branches(new_proof, plan, authored_assumes)?;

        let then_step = self.emit_provenance_ite_goal_branch(
            new_proof,
            plan,
            IteBranch {
                guard: not_cond,
                source_fact: plan.source_then,
                source_step: source_then,
                lifted: plan.lifted_then,
                lemma: &plan.then_lemma,
            },
            AletheRule::IteNeg2,
            authored_assumes,
        )?;
        let else_step = self.emit_provenance_ite_goal_branch(
            new_proof,
            plan,
            IteBranch {
                guard: plan.cond,
                source_fact: plan.source_else,
                source_step: source_else,
                lifted: plan.lifted_else,
                lemma: &plan.else_lemma,
            },
            AletheRule::IteNeg1,
            authored_assumes,
        )?;
        Some(new_proof.add_resolution(vec![plan.goal], plan.cond, then_step, else_step))
    }

    /// Emit the two guarded branch consequences directly. The seeded SAT
    /// fallback consumes these clauses as-is, so it never has to render the
    /// derived formula-ITE root through an authored defining-equality override.
    pub(in crate::executor) fn emit_provenance_ite_seed_branches(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceItePlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<(ProofId, ProofId)> {
        let (not_cond, source_then, source_else) =
            self.emit_provenance_ite_source_branches(proof, plan, authored_assumes)?;
        let then_step = self.emit_provenance_ite_branch_implication(
            proof,
            IteBranch {
                guard: not_cond,
                source_fact: plan.source_then,
                source_step: source_then,
                lifted: plan.lifted_then,
                lemma: &plan.then_lemma,
            },
            authored_assumes,
        )?;
        let else_step = self.emit_provenance_ite_branch_implication(
            proof,
            IteBranch {
                guard: plan.cond,
                source_fact: plan.source_else,
                source_step: source_else,
                lifted: plan.lifted_else,
                lemma: &plan.else_lemma,
            },
            authored_assumes,
        )?;
        Some((then_step, else_step))
    }

    fn emit_provenance_ite_source_branches(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceItePlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<(TermId, ProofId, ProofId)> {
        let &orig_assume = authored_assumes.get(&plan.orig)?;
        let not_cond = self.ctx.terms.mk_not_raw(plan.cond);
        let branch_premise = match &plan.source {
            ProvenanceIteSource::Formula => orig_assume,
            ProvenanceIteSource::Defined {
                ite_term: _,
                ite_def,
                and_term,
                intro_eq,
            } => {
                let not_intro_eq = self.ctx.terms.mk_not_raw(*intro_eq);
                let not_orig = self.ctx.terms.mk_not_raw(plan.orig);
                let intro = proof.add_rule_step(
                    AletheRule::IteIntro,
                    vec![*intro_eq],
                    Vec::new(),
                    Vec::new(),
                );
                let equivalence = proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_intro_eq, not_orig, *and_term],
                    Vec::new(),
                    Vec::new(),
                );
                let resolved_eq =
                    proof.add_resolution(vec![not_orig, *and_term], *intro_eq, equivalence, intro);
                let resolved_orig =
                    proof.add_resolution(vec![*and_term], plan.orig, resolved_eq, orig_assume);
                let not_and = self.ctx.terms.mk_not_raw(*and_term);
                let and_pos = proof.add_rule_step(
                    AletheRule::AndPos(1),
                    vec![not_and, *ite_def],
                    Vec::new(),
                    Vec::new(),
                );
                proof.add_resolution(vec![*ite_def], *and_term, and_pos, resolved_orig)
            }
        };
        let source_then = proof.add_rule_step(
            AletheRule::Ite2,
            vec![not_cond, plan.source_then],
            vec![branch_premise],
            Vec::new(),
        );
        let source_else = proof.add_rule_step(
            AletheRule::Ite1,
            vec![plan.cond, plan.source_else],
            vec![branch_premise],
            Vec::new(),
        );
        Some((not_cond, source_then, source_else))
    }

    fn emit_provenance_ite_goal_branch(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceItePlan,
        branch: IteBranch<'_>,
        goal_rule: AletheRule,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let guard = branch.guard;
        let lifted = branch.lifted;
        let implication =
            self.emit_provenance_ite_branch_implication(proof, branch, authored_assumes)?;
        let not_lifted = complement_of(&mut self.ctx.terms, lifted);
        let goal_link = proof.add_rule_step(
            goal_rule,
            vec![plan.goal, guard, not_lifted],
            Vec::new(),
            Vec::new(),
        );
        Some(proof.add_resolution(vec![plan.goal, guard], lifted, goal_link, implication))
    }

    fn emit_provenance_ite_branch_implication(
        &mut self,
        proof: &mut Proof,
        branch: IteBranch<'_>,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let IteBranch {
            guard,
            source_fact,
            source_step,
            lifted,
            lemma,
        } = branch;
        let lemma_id = match lemma {
            ProvenanceBranchLemma::Farkas(lemma) => proof.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: lemma.clause.clone(),
                farkas: Some(lemma.farkas.clone()),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            }),
            ProvenanceBranchLemma::Transitive { clause, .. } => proof.add_theory_lemma_with_kind(
                "euf",
                clause.clone(),
                TheoryLemmaKind::EufTransitive,
            ),
        };

        // Resolve the guarded source fact, then every retained non-zero exact
        // authored support, leaving exactly the guarded lifted consequence.
        let mut lemma_tail = lemma.clause().to_vec();
        let source_complement = complement_of(&mut self.ctx.terms, source_fact);
        let source_pos = lemma_tail
            .iter()
            .position(|&literal| literal == source_complement)?;
        let _ = lemma_tail.remove(source_pos);
        let mut remaining = vec![guard];
        remaining.extend(lemma_tail);
        let mut current =
            proof.add_resolution(remaining.clone(), source_fact, lemma_id, source_step);

        for &support in lemma.supports() {
            let support_complement = complement_of(&mut self.ctx.terms, support);
            let position = remaining
                .iter()
                .position(|&literal| literal == support_complement)?;
            let _ = remaining.remove(position);
            let &support_assume = authored_assumes.get(&support)?;
            current = proof.add_resolution(remaining.clone(), support, current, support_assume);
        }
        (remaining == [guard, lifted]).then_some(current)
    }
}
