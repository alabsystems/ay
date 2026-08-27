// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE/provenance replacement emission in planner priority order.

use super::super::*;
use super::model::{EmitDecision, RebuildWalk};

#[derive(Clone, Copy)]
struct BoundAssume {
    term: TermId,
    complement: TermId,
    proof: ProofId,
}

struct LegacyIteCore {
    assume: ProofId,
    ite_then: ProofId,
    ite_else: ProofId,
    bridge_then: ProofId,
    bridge_else: ProofId,
    neg_then: ProofId,
    neg_else: ProofId,
    not_eq_then: TermId,
    not_eq_else: TermId,
    not_orig: TermId,
    not_cond: TermId,
    bound: Option<BoundAssume>,
}

struct LegacyIteEmitter<'a> {
    executor: &'a mut Executor,
    state: &'a mut super::model::RebuildState,
}

fn append_bound(mut literals: Vec<TermId>, bound: Option<BoundAssume>) -> Vec<TermId> {
    if let Some(bound) = bound {
        literals.push(bound.complement);
    }
    literals
}

impl RebuildWalk<'_, '_> {
    pub(super) fn emit_lift_family(&mut self, index: usize) -> EmitDecision {
        if let Some(plan) = self.plans.provenance_ite_lifts.get(&index) {
            let surface = self.plans.prepared_surface_overrides.as_ref();
            let emitted = self.executor.emit_ite_lift(
                &mut self.state.new_proof,
                plan,
                &self.state.lift_assume,
                surface,
            );
            return self.record_lift_optional(index, emitted);
        }
        if let Some(original) = self.plans.exact_provenance_or_assumes.get(&index) {
            let Some(&assume) = self.state.lift_assume.get(original) else {
                return EmitDecision::Reject;
            };
            self.state.map[index] = Some(assume);
            return EmitDecision::Emitted;
        }
        if let Some(plan) = self.plans.provenance_or_plans.get(&index) {
            let emitted = self.executor.emit_provenance_or(
                &mut self.state.new_proof,
                plan,
                &self.state.lift_assume,
            );
            return self.record_lift_optional(index, emitted);
        }
        let Some(plan) = self.plans.ite_lifts.get(&index) else {
            return EmitDecision::NotApplicable;
        };
        let Some(emitted) = (LegacyIteEmitter {
            executor: self.executor,
            state: self.state,
        })
        .emit(plan) else {
            return EmitDecision::Reject;
        };
        self.state.map[index] = Some(emitted);
        EmitDecision::Emitted
    }

    fn record_lift_optional(&mut self, index: usize, emitted: Option<ProofId>) -> EmitDecision {
        let Some(emitted) = emitted else {
            return EmitDecision::Reject;
        };
        self.state.map[index] = Some(emitted);
        EmitDecision::Emitted
    }
}

impl LegacyIteEmitter<'_> {
    fn emit(&mut self, plan: &IteLiftPlan) -> Option<ProofId> {
        let assume = *self.state.lift_assume.get(&plan.orig)?;
        if plan.guarded_then_or {
            return self.emit_guarded_then_or(plan, assume);
        }
        let core = self.emit_legacy_ite_core(plan, assume)?;
        Some(self.close_legacy_ite_branches(plan, &core))
    }

    /// Derive the guarded then-projection `(cl (or (not c) A))` from the
    /// authored `orig` containing `(ite c u v)`:
    ///
    /// ```text
    /// ite_intro/equiv_pos2/and_pos    |- (cl ite_def)          ; as the packed form
    /// ite2                            |- (cl (not c) eq_then)
    /// la_generic (checked)            |- (cl (not eq_then) (not orig) A)
    /// resolution x2 (eq_then, orig)   |- (cl (not c) A)
    /// or_neg x2 + contraction         |- (cl (or (not c) A))
    /// ```
    ///
    /// The else side of the plan is validated by recognition but never
    /// emitted: the else-branch clause of the clausified source was
    /// trivially true and has no counterpart in the target proof.
    fn emit_guarded_then_or(&mut self, plan: &IteLiftPlan, assume: ProofId) -> Option<ProofId> {
        if plan.bound.is_some() {
            return None;
        }
        let terms = &mut self.executor.ctx.terms;
        let not_orig = terms.mk_not_raw(plan.orig);
        let not_cond = terms.mk_not_raw(plan.cond);
        let not_eq_then = terms.mk_not_raw(plan.eq_then);
        let definition = self.emit_ite_definition(plan, assume);
        let proof = &mut self.state.new_proof;
        let ite_then = proof.add_rule_step(
            AletheRule::Ite2,
            vec![not_cond, plan.eq_then],
            vec![definition],
            Vec::new(),
        );
        let bridge_then =
            Executor::add_guarded_then_transfer_lemma(proof, plan, not_eq_then, not_orig);
        let transferred = proof.add_resolution(
            vec![not_cond, not_orig, plan.lifted_then],
            plan.eq_then,
            ite_then,
            bridge_then,
        );
        let projected = proof.add_resolution(
            vec![not_cond, plan.lifted_then],
            plan.orig,
            transferred,
            assume,
        );
        let mut current = projected;
        let mut remaining = vec![not_cond, plan.lifted_then];
        for target in [not_cond, plan.lifted_then] {
            let blocker = complement_of(&mut self.executor.ctx.terms, target);
            let proof = &mut self.state.new_proof;
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
        Some(self.state.new_proof.add_rule_step(
            AletheRule::Contraction,
            vec![plan.goal],
            vec![current],
            Vec::new(),
        ))
    }

    /// The shared `ite_intro` definition chain: from the hoisted assume of
    /// `orig`, derive the unit `(cl ite_def)` for the plan's term-ITE.
    fn emit_ite_definition(&mut self, plan: &IteLiftPlan, assume: ProofId) -> ProofId {
        let terms = &mut self.executor.ctx.terms;
        let not_intro_eq = terms.mk_not_raw(plan.intro_eq);
        let not_orig = terms.mk_not_raw(plan.orig);
        let not_and = terms.mk_not_raw(plan.and_term);
        let proof = &mut self.state.new_proof;
        let intro = proof.add_rule_step(
            AletheRule::IteIntro,
            vec![plan.intro_eq],
            Vec::new(),
            Vec::new(),
        );
        let equiv = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_intro_eq, not_orig, plan.and_term],
            Vec::new(),
            Vec::new(),
        );
        let equality =
            proof.add_resolution(vec![not_orig, plan.and_term], plan.intro_eq, equiv, intro);
        let conjunction = proof.add_resolution(vec![plan.and_term], plan.orig, equality, assume);
        let and_pos = proof.add_rule_step(
            AletheRule::AndPos(1),
            vec![not_and, plan.ite_def],
            Vec::new(),
            Vec::new(),
        );
        proof.add_resolution(vec![plan.ite_def], plan.and_term, and_pos, conjunction)
    }

    fn emit_legacy_ite_core(
        &mut self,
        plan: &IteLiftPlan,
        assume: ProofId,
    ) -> Option<LegacyIteCore> {
        let terms = &mut self.executor.ctx.terms;
        let not_intro_eq = terms.mk_not_raw(plan.intro_eq);
        let not_orig = terms.mk_not_raw(plan.orig);
        let not_cond = terms.mk_not_raw(plan.cond);
        let not_eq_then = terms.mk_not_raw(plan.eq_then);
        let not_eq_else = terms.mk_not_raw(plan.eq_else);
        let not_lifted_then = complement_of(terms, plan.lifted_then);
        let not_lifted_else = complement_of(terms, plan.lifted_else);
        let (ite_then, ite_else) = {
            let proof = &mut self.state.new_proof;
            let intro = proof.add_rule_step(
                AletheRule::IteIntro,
                vec![plan.intro_eq],
                Vec::new(),
                Vec::new(),
            );
            let equiv = proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_intro_eq, not_orig, plan.and_term],
                Vec::new(),
                Vec::new(),
            );
            let equality =
                proof.add_resolution(vec![not_orig, plan.and_term], plan.intro_eq, equiv, intro);
            let conjunction =
                proof.add_resolution(vec![plan.and_term], plan.orig, equality, assume);
            let not_and = self.executor.ctx.terms.mk_not_raw(plan.and_term);
            let and_pos = proof.add_rule_step(
                AletheRule::AndPos(1),
                vec![not_and, plan.ite_def],
                Vec::new(),
                Vec::new(),
            );
            let definition =
                proof.add_resolution(vec![plan.ite_def], plan.and_term, and_pos, conjunction);
            let ite_then = proof.add_rule_step(
                AletheRule::Ite2,
                vec![not_cond, plan.eq_then],
                vec![definition],
                Vec::new(),
            );
            let ite_else = proof.add_rule_step(
                AletheRule::Ite1,
                vec![plan.cond, plan.eq_else],
                vec![definition],
                Vec::new(),
            );
            (ite_then, ite_else)
        };
        let bound = self.prepare_bound_assume(plan)?;
        let proof = &mut self.state.new_proof;
        let (bridge_then, bridge_else) = Executor::add_ite_transfer_lemmas(
            proof,
            plan,
            not_eq_then,
            not_eq_else,
            not_orig,
            bound.map(|value| value.complement),
        );
        let neg_then = proof.add_rule_step(
            AletheRule::IteNeg2,
            vec![plan.goal, not_cond, not_lifted_then],
            Vec::new(),
            Vec::new(),
        );
        let neg_else = proof.add_rule_step(
            AletheRule::IteNeg1,
            vec![plan.goal, plan.cond, not_lifted_else],
            Vec::new(),
            Vec::new(),
        );
        Some(LegacyIteCore {
            assume,
            ite_then,
            ite_else,
            bridge_then,
            bridge_else,
            neg_then,
            neg_else,
            not_eq_then,
            not_eq_else,
            not_orig,
            not_cond,
            bound,
        })
    }

    fn prepare_bound_assume(&mut self, plan: &IteLiftPlan) -> Option<Option<BoundAssume>> {
        let Some(term) = plan.bound else {
            return Some(None);
        };
        let proof = *self.state.lift_assume.get(&term)?;
        let complement = self.executor.ctx.terms.mk_not_raw(term);
        Some(Some(BoundAssume {
            term,
            complement,
            proof,
        }))
    }

    fn close_legacy_ite_branches(&mut self, plan: &IteLiftPlan, core: &LegacyIteCore) -> ProofId {
        let proof = &mut self.state.new_proof;
        let first_then = proof.add_resolution(
            append_bound(
                vec![plan.goal, core.not_cond, core.not_eq_then, core.not_orig],
                core.bound,
            ),
            plan.lifted_then,
            core.neg_then,
            core.bridge_then,
        );
        let second_then = proof.add_resolution(
            append_bound(vec![plan.goal, core.not_cond, core.not_orig], core.bound),
            plan.eq_then,
            first_then,
            core.ite_then,
        );
        let mut then_branch = proof.add_resolution(
            append_bound(vec![plan.goal, core.not_cond], core.bound),
            plan.orig,
            second_then,
            core.assume,
        );
        if let Some(bound) = core.bound {
            then_branch = proof.add_resolution(
                vec![plan.goal, core.not_cond],
                bound.term,
                then_branch,
                bound.proof,
            );
        }
        let first_else = proof.add_resolution(
            append_bound(
                vec![plan.goal, plan.cond, core.not_eq_else, core.not_orig],
                core.bound,
            ),
            plan.lifted_else,
            core.neg_else,
            core.bridge_else,
        );
        let second_else = proof.add_resolution(
            append_bound(vec![plan.goal, plan.cond, core.not_orig], core.bound),
            plan.eq_else,
            first_else,
            core.ite_else,
        );
        let mut else_branch = proof.add_resolution(
            append_bound(vec![plan.goal, plan.cond], core.bound),
            plan.orig,
            second_else,
            core.assume,
        );
        if let Some(bound) = core.bound {
            else_branch = proof.add_resolution(
                vec![plan.goal, plan.cond],
                bound.term,
                else_branch,
                bound.proof,
            );
        }
        proof.add_resolution(vec![plan.goal], plan.cond, then_branch, else_branch)
    }
}
