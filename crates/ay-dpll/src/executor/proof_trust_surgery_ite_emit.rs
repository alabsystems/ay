// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked proof emission for provenance-authenticated arithmetic ITE plans.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TheoryLemmaKind};

use super::proof_trust_surgery_ite::{
    ProvenanceFarkasLemma, ProvenanceItePlan, ProvenanceIteSource,
};
use super::proof_trust_surgery_provenance::{complement_of, ProvenanceSurfaceAudit};
use super::Executor;

struct IteBranch<'a> {
    guard: TermId,
    source_fact: TermId,
    source_step: ProofId,
    lifted: TermId,
    goal_rule: AletheRule,
    lemma: &'a ProvenanceFarkasLemma,
}

impl ProvenanceItePlan {
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
        audit.protect_farkas_lemma(terms, &self.then_lemma.clause, &self.then_lemma.farkas);
        audit.protect_farkas_lemma(terms, &self.else_lemma.clause, &self.else_lemma.farkas);
    }
}

impl Executor {
    /// Emit the checked ITE/Farkas derivation planned by the sibling module.
    pub(super) fn emit_provenance_ite_lift(
        &mut self,
        new_proof: &mut Proof,
        plan: &ProvenanceItePlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
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
                let intro = new_proof.add_rule_step(
                    AletheRule::IteIntro,
                    vec![*intro_eq],
                    Vec::new(),
                    Vec::new(),
                );
                let equivalence = new_proof.add_rule_step(
                    AletheRule::EquivPos2,
                    vec![not_intro_eq, not_orig, *and_term],
                    Vec::new(),
                    Vec::new(),
                );
                let resolved_eq = new_proof.add_resolution(
                    vec![not_orig, *and_term],
                    *intro_eq,
                    equivalence,
                    intro,
                );
                let resolved_orig =
                    new_proof.add_resolution(vec![*and_term], plan.orig, resolved_eq, orig_assume);
                let not_and = self.ctx.terms.mk_not_raw(*and_term);
                let and_pos = new_proof.add_rule_step(
                    AletheRule::AndPos(1),
                    vec![not_and, *ite_def],
                    Vec::new(),
                    Vec::new(),
                );
                new_proof.add_resolution(vec![*ite_def], *and_term, and_pos, resolved_orig)
            }
        };
        let source_then = new_proof.add_rule_step(
            AletheRule::Ite2,
            vec![not_cond, plan.source_then],
            vec![branch_premise],
            Vec::new(),
        );
        let source_else = new_proof.add_rule_step(
            AletheRule::Ite1,
            vec![plan.cond, plan.source_else],
            vec![branch_premise],
            Vec::new(),
        );

        let then_step = self.emit_provenance_ite_branch(
            new_proof,
            plan,
            IteBranch {
                guard: not_cond,
                source_fact: plan.source_then,
                source_step: source_then,
                lifted: plan.lifted_then,
                goal_rule: AletheRule::IteNeg2,
                lemma: &plan.then_lemma,
            },
            authored_assumes,
        )?;
        let else_step = self.emit_provenance_ite_branch(
            new_proof,
            plan,
            IteBranch {
                guard: plan.cond,
                source_fact: plan.source_else,
                source_step: source_else,
                lifted: plan.lifted_else,
                goal_rule: AletheRule::IteNeg1,
                lemma: &plan.else_lemma,
            },
            authored_assumes,
        )?;
        Some(new_proof.add_resolution(vec![plan.goal], plan.cond, then_step, else_step))
    }

    fn emit_provenance_ite_branch(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceItePlan,
        branch: IteBranch<'_>,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let IteBranch {
            guard,
            source_fact,
            source_step,
            lifted,
            goal_rule,
            lemma,
        } = branch;
        let not_lifted = complement_of(&mut self.ctx.terms, lifted);
        let goal_link = proof.add_rule_step(
            goal_rule,
            vec![plan.goal, guard, not_lifted],
            Vec::new(),
            Vec::new(),
        );
        let lemma_id = proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: lemma.clause.clone(),
            farkas: Some(lemma.farkas.clone()),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });

        // Resolve the branch conclusion, its guarded source fact, then every
        // retained non-zero exact authored support.
        let mut remaining = vec![plan.goal, guard];
        remaining.extend(
            lemma
                .clause
                .iter()
                .copied()
                .filter(|&literal| literal != lifted),
        );
        let mut current = proof.add_resolution(remaining.clone(), lifted, goal_link, lemma_id);

        let source_complement = complement_of(&mut self.ctx.terms, source_fact);
        let source_pos = remaining
            .iter()
            .position(|&literal| literal == source_complement)?;
        let _ = remaining.remove(source_pos);
        current = proof.add_resolution(remaining.clone(), source_fact, current, source_step);

        for &support in &lemma.supports {
            let support_complement = complement_of(&mut self.ctx.terms, support);
            let position = remaining
                .iter()
                .position(|&literal| literal == support_complement)?;
            let _ = remaining.remove(position);
            let &support_assume = authored_assumes.get(&support)?;
            current = proof.add_resolution(remaining.clone(), support, current, support_assume);
        }
        (remaining == [plan.goal, guard]).then_some(current)
    }
}
