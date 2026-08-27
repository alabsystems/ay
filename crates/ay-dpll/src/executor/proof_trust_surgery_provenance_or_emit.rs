// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked emission for provenance-authenticated OR repair.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TheoryLemmaKind};

use super::proof_trust_surgery_ite::ProvenanceFarkasLemma;
use super::proof_trust_surgery_provenance::complement_of;
use super::proof_trust_surgery_provenance_or::{
    ProvenanceOrConflictPlan, ProvenanceOrFalseDisjunctPlan, ProvenanceOrIteRefutation,
    ProvenanceOrPlan, ProvenanceOrRefutation,
};
use super::proof_trust_surgery_provenance_or_transfer::{
    ProvenanceOrBridge, ProvenanceOrIteBridge, ProvenanceOrTransferPlan,
};
use super::Executor;

struct IteRefutationBranch<'a> {
    guard: TermId,
    source_branch: TermId,
    source_step: ProofId,
    lemma: &'a ProvenanceFarkasLemma,
}

struct IteTransferBranch<'a> {
    guard: TermId,
    source_branch: TermId,
    target_branch: TermId,
    source_step: ProofId,
    goal_rule: AletheRule,
    lemma: &'a ProvenanceFarkasLemma,
}

impl Executor {
    pub(super) fn emit_provenance_or(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrPlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        match plan {
            ProvenanceOrPlan::Conflict(plan) => {
                self.emit_provenance_or_conflict(proof, plan, authored_assumes)
            }
            ProvenanceOrPlan::ConjunctiveConflict(plan) => {
                self.emit_provenance_or_and_conflict(proof, plan, authored_assumes)
            }
            ProvenanceOrPlan::ConjunctiveTransfer(plan) => {
                self.emit_provenance_or_and_transfer(proof, plan, authored_assumes)
            }
            ProvenanceOrPlan::ExactTransfer(plan) => {
                self.emit_provenance_or_transfer(proof, plan, authored_assumes)
            }
            ProvenanceOrPlan::FalseDisjunct(plan) => {
                self.emit_provenance_or_false_disjunct(proof, plan, authored_assumes)
            }
        }
    }

    /// Derive the target `or` whose folded disjuncts the plan refutes:
    ///
    /// ```text
    /// or                       |- (cl d1 .. dn)          ; from the assume of orig
    /// la_generic + resolution  |- (cl (not di))          ; one per folded disjunct
    /// resolution               |- (cl kept..)
    /// or_neg + resolution      |- (cl goal .. goal)      ; one per kept disjunct
    /// contraction              |- (cl goal)
    /// ```
    fn emit_provenance_or_false_disjunct(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrFalseDisjunctPlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let &or_assume = authored_assumes.get(&plan.orig)?;
        let mut current = proof.add_rule_step(
            AletheRule::Or,
            plan.source_disjuncts.clone(),
            vec![or_assume],
            Vec::new(),
        );
        let mut remaining = plan.source_disjuncts.clone();
        for elimination in &plan.eliminations {
            let unit = self.emit_provenance_farkas_refutation(
                proof,
                elimination.disjunct,
                &elimination.lemma,
                authored_assumes,
            )?;
            let position = remaining
                .iter()
                .position(|&literal| literal == elimination.disjunct)?;
            let _ = remaining.remove(position);
            current = proof.add_resolution(remaining.clone(), elimination.disjunct, current, unit);
        }
        if remaining != plan.kept {
            return None;
        }
        for &target in &plan.kept {
            let blocker = complement_of(&mut self.ctx.terms, target);
            let link = proof.add_rule_step(
                AletheRule::OrNeg,
                vec![plan.goal, blocker],
                Vec::new(),
                Vec::new(),
            );
            let position = remaining.iter().position(|&literal| literal == target)?;
            let _ = remaining.remove(position);
            remaining.push(plan.goal);
            current = proof.add_resolution(remaining.clone(), target, current, link);
        }
        if !remaining.iter().all(|&literal| literal == plan.goal) {
            return None;
        }
        Some(proof.add_rule_step(
            AletheRule::Contraction,
            vec![plan.goal],
            vec![current],
            Vec::new(),
        ))
    }

    pub(super) fn emit_provenance_or_conflict(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrConflictPlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let &or_assume = authored_assumes.get(&plan.orig)?;
        let mut current = proof.add_rule_step(
            AletheRule::Or,
            plan.disjuncts.clone(),
            vec![or_assume],
            Vec::new(),
        );
        let mut remaining = plan.disjuncts.clone();

        for refutation in &plan.refutations {
            let (disjunct, unit) = match refutation {
                ProvenanceOrRefutation::Farkas { disjunct, lemma } => (
                    *disjunct,
                    self.emit_provenance_farkas_refutation(
                        proof,
                        *disjunct,
                        lemma,
                        authored_assumes,
                    )?,
                ),
                ProvenanceOrRefutation::Ite(ite) => (
                    ite.disjunct,
                    self.emit_provenance_ite_refutation(proof, ite, authored_assumes)?,
                ),
            };
            let index = remaining.iter().position(|&literal| literal == disjunct)?;
            let _ = remaining.remove(index);
            current = proof.add_resolution(remaining.clone(), disjunct, current, unit);
        }
        if !remaining.is_empty() {
            return None;
        }
        Some(proof.add_rule_step(
            AletheRule::Weakening,
            vec![plan.goal],
            vec![current],
            Vec::new(),
        ))
    }

    fn add_provenance_farkas_lemma(proof: &mut Proof, lemma: &ProvenanceFarkasLemma) -> ProofId {
        proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: lemma.clause.clone(),
            farkas: Some(lemma.farkas.clone()),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        })
    }

    fn emit_provenance_farkas_refutation(
        &mut self,
        proof: &mut Proof,
        disjunct: TermId,
        lemma: &ProvenanceFarkasLemma,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let mut current = Self::add_provenance_farkas_lemma(proof, lemma);
        let mut remaining = lemma.clause.clone();
        for &support in &lemma.supports {
            let blocker = complement_of(&mut self.ctx.terms, support);
            let index = remaining.iter().position(|&literal| literal == blocker)?;
            let _ = remaining.remove(index);
            let &assume = authored_assumes.get(&support)?;
            current = proof.add_resolution(remaining.clone(), support, current, assume);
        }
        let blocker = complement_of(&mut self.ctx.terms, disjunct);
        (remaining == [blocker]).then_some(current)
    }

    fn emit_provenance_ite_refutation(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrIteRefutation,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let &ite_assume = authored_assumes.get(&plan.ite_orig)?;
        let not_cond = self.ctx.terms.mk_not_raw(plan.cond);
        let source_then = proof.add_rule_step(
            AletheRule::Ite2,
            vec![not_cond, plan.source_then],
            vec![ite_assume],
            Vec::new(),
        );
        let source_else = proof.add_rule_step(
            AletheRule::Ite1,
            vec![plan.cond, plan.source_else],
            vec![ite_assume],
            Vec::new(),
        );
        let then_step = self.emit_provenance_ite_refutation_branch(
            proof,
            plan,
            IteRefutationBranch {
                guard: not_cond,
                source_branch: plan.source_then,
                source_step: source_then,
                lemma: &plan.then_lemma,
            },
            authored_assumes,
        )?;
        let else_step = self.emit_provenance_ite_refutation_branch(
            proof,
            plan,
            IteRefutationBranch {
                guard: plan.cond,
                source_branch: plan.source_else,
                source_step: source_else,
                lemma: &plan.else_lemma,
            },
            authored_assumes,
        )?;
        let blocker = complement_of(&mut self.ctx.terms, plan.disjunct);
        Some(proof.add_resolution(vec![blocker], plan.cond, then_step, else_step))
    }

    fn emit_provenance_ite_refutation_branch(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrIteRefutation,
        branch: IteRefutationBranch<'_>,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let IteRefutationBranch {
            guard,
            source_branch,
            source_step,
            lemma,
        } = branch;
        let lemma_id = Self::add_provenance_farkas_lemma(proof, lemma);
        let source_blocker = complement_of(&mut self.ctx.terms, source_branch);
        let mut remaining = vec![guard];
        remaining.extend(
            lemma
                .clause
                .iter()
                .copied()
                .filter(|&literal| literal != source_blocker),
        );
        let mut current =
            proof.add_resolution(remaining.clone(), source_branch, source_step, lemma_id);
        for &support in &lemma.supports {
            if support == plan.disjunct {
                continue;
            }
            let blocker = complement_of(&mut self.ctx.terms, support);
            let index = remaining.iter().position(|&literal| literal == blocker)?;
            let _ = remaining.remove(index);
            let &assume = authored_assumes.get(&support)?;
            current = proof.add_resolution(remaining.clone(), support, current, assume);
        }
        let disjunct_blocker = complement_of(&mut self.ctx.terms, plan.disjunct);
        (remaining == [guard, disjunct_blocker]).then_some(current)
    }

    fn emit_provenance_or_transfer(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrTransferPlan,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let &or_assume = authored_assumes.get(&plan.orig)?;
        let mut current = proof.add_rule_step(
            AletheRule::Or,
            plan.source_disjuncts.clone(),
            vec![or_assume],
            Vec::new(),
        );
        let mut remaining = plan.source_disjuncts.clone();
        for bridge in &plan.bridges {
            let (source, target) = bridge.endpoints();
            let bridge_step = match bridge {
                ProvenanceOrBridge::Farkas { lemma, .. } => self.emit_provenance_or_direct_bridge(
                    proof,
                    source,
                    target,
                    lemma,
                    authored_assumes,
                )?,
                ProvenanceOrBridge::Ite(ite) => {
                    self.emit_provenance_or_ite_bridge(proof, ite, authored_assumes)?
                }
            };
            let position = remaining.iter().position(|&literal| literal == source)?;
            let _ = remaining.remove(position);
            remaining.push(target);
            current = proof.add_resolution(remaining.clone(), source, current, bridge_step);
        }
        let mut actual_targets = remaining.clone();
        let mut expected_targets = plan.target_disjuncts.clone();
        actual_targets.sort_unstable();
        expected_targets.sort_unstable();
        if actual_targets != expected_targets {
            return None;
        }

        for &target in &plan.target_disjuncts {
            let blocker = complement_of(&mut self.ctx.terms, target);
            let link = proof.add_rule_step(
                AletheRule::OrNeg,
                vec![plan.goal, blocker],
                Vec::new(),
                Vec::new(),
            );
            let position = remaining.iter().position(|&literal| literal == target)?;
            let _ = remaining.remove(position);
            remaining.push(plan.goal);
            current = proof.add_resolution(remaining.clone(), target, current, link);
        }
        if !remaining.iter().all(|&literal| literal == plan.goal) {
            return None;
        }
        Some(proof.add_rule_step(
            AletheRule::Contraction,
            vec![plan.goal],
            vec![current],
            Vec::new(),
        ))
    }

    fn emit_provenance_or_direct_bridge(
        &mut self,
        proof: &mut Proof,
        source: TermId,
        target: TermId,
        lemma: &ProvenanceFarkasLemma,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let mut current = Self::add_provenance_farkas_lemma(proof, lemma);
        let mut remaining = lemma.clause.clone();
        for &support in &lemma.supports {
            let blocker = complement_of(&mut self.ctx.terms, support);
            let position = remaining.iter().position(|&literal| literal == blocker)?;
            let _ = remaining.remove(position);
            let &assume = authored_assumes.get(&support)?;
            current = proof.add_resolution(remaining.clone(), support, current, assume);
        }
        let source_blocker = complement_of(&mut self.ctx.terms, source);
        (remaining == [source_blocker, target]).then_some(current)
    }

    fn emit_provenance_or_ite_bridge(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrIteBridge,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let &ite_assume = authored_assumes.get(&plan.ite_orig)?;
        let not_cond = self.ctx.terms.mk_not_raw(plan.cond);
        let source_then = proof.add_rule_step(
            AletheRule::Ite2,
            vec![not_cond, plan.source_then],
            vec![ite_assume],
            Vec::new(),
        );
        let source_else = proof.add_rule_step(
            AletheRule::Ite1,
            vec![plan.cond, plan.source_else],
            vec![ite_assume],
            Vec::new(),
        );
        let then_step = self.emit_provenance_or_ite_bridge_branch(
            proof,
            plan,
            IteTransferBranch {
                guard: not_cond,
                source_branch: plan.source_then,
                target_branch: plan.target_then,
                source_step: source_then,
                goal_rule: AletheRule::IteNeg2,
                lemma: &plan.then_lemma,
            },
            authored_assumes,
        )?;
        let else_step = self.emit_provenance_or_ite_bridge_branch(
            proof,
            plan,
            IteTransferBranch {
                guard: plan.cond,
                source_branch: plan.source_else,
                target_branch: plan.target_else,
                source_step: source_else,
                goal_rule: AletheRule::IteNeg1,
                lemma: &plan.else_lemma,
            },
            authored_assumes,
        )?;
        let source_blocker = complement_of(&mut self.ctx.terms, plan.source);
        Some(proof.add_resolution(
            vec![source_blocker, plan.target],
            plan.cond,
            then_step,
            else_step,
        ))
    }

    fn emit_provenance_or_ite_bridge_branch(
        &mut self,
        proof: &mut Proof,
        plan: &ProvenanceOrIteBridge,
        branch: IteTransferBranch<'_>,
        authored_assumes: &HashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        let target_blocker = complement_of(&mut self.ctx.terms, branch.target_branch);
        let goal_link = proof.add_rule_step(
            branch.goal_rule,
            vec![plan.target, branch.guard, target_blocker],
            Vec::new(),
            Vec::new(),
        );
        let lemma_step = Self::add_provenance_farkas_lemma(proof, branch.lemma);
        let mut remaining = vec![plan.target, branch.guard];
        remaining.extend(
            branch
                .lemma
                .clause
                .iter()
                .copied()
                .filter(|&literal| literal != branch.target_branch),
        );
        let mut current = proof.add_resolution(
            remaining.clone(),
            branch.target_branch,
            goal_link,
            lemma_step,
        );
        let source_branch_blocker = complement_of(&mut self.ctx.terms, branch.source_branch);
        let position = remaining
            .iter()
            .position(|&literal| literal == source_branch_blocker)?;
        let _ = remaining.remove(position);
        current = proof.add_resolution(
            remaining.clone(),
            branch.source_branch,
            current,
            branch.source_step,
        );
        for &support in &branch.lemma.supports {
            if support == plan.source {
                continue;
            }
            let blocker = complement_of(&mut self.ctx.terms, support);
            let position = remaining.iter().position(|&literal| literal == blocker)?;
            let _ = remaining.remove(position);
            let &assume = authored_assumes.get(&support)?;
            current = proof.add_resolution(remaining.clone(), support, current, assume);
        }
        let source_blocker = complement_of(&mut self.ctx.terms, plan.source);
        (remaining == [plan.target, branch.guard, source_blocker]).then_some(current)
    }
}
