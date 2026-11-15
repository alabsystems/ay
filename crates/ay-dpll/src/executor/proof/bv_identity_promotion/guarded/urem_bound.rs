// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strengthen the joint search with independently checked total BV theorems.
//!
//! For every genuine authored `bvurem x d`, the guard `d=0 or urem(x,d)<d`
//! follows from SMT-LIB unsigned remainder semantics. It is DERIVED, never
//! assumed. The remaining contradiction still uses the ordinary strict
//! bit-blast checker, and all original authored roots stay in the proof.

use super::*;
use ay_core::{ProofId, TermStore};
use control::Control;

mod before_division;
mod collect;
mod control;
#[cfg(test)]
mod tests;

impl Executor {
    /// Presentation advice only: the native theorem and actual exported
    /// document remain independently checked by their existing gates.
    pub(in crate::executor::proof) fn urem_bound_wire_supported(
        &self,
        clause: &[TermId],
        overrides: Option<&ay_core::kani_compat::DetHashMap<TermId, String>>,
    ) -> bool {
        let stop = self.make_proof_assembly_should_stop();
        let Some(mut control) = Control::capture(self, &stop) else {
            return false;
        };
        let _scope = control.enter();
        let supported = ay_proof::checked_urem_bound_lowering_supported(
            &self.ctx.terms,
            clause,
            overrides,
            &mut |work, bytes| {
                control
                    .admit(&self.proof_source_work, work, bytes)
                    .is_some()
            },
        );
        let stopped = control.stopped();
        if let Some(reason) = control.reason() {
            self.note_certification_stop(reason);
        }
        supported && !stopped
    }

    /// `None` is terminal stop/refusal, not permission to retry a fresh lane.
    pub(super) fn promote_urem_bound_joint(
        &mut self,
        proof: &mut Proof,
        roots: &[TermId],
        stage: GuardedCollapseStage,
        incumbent: &mut IncumbentFacts,
        stop: &dyn Fn() -> bool,
    ) -> Option<bool> {
        let mut control = Control::capture(self, stop)?;
        let _scope = control.enter();
        let result = self.urem_bound_candidate(proof, roots, stage, incumbent, &mut control);
        let stopped = control.stopped();
        if let Some(reason) = control.reason() {
            self.note_certification_stop(reason);
        }
        if stopped {
            None
        } else {
            result
        }
    }

    fn urem_bound_candidate(
        &mut self,
        proof: &mut Proof,
        roots: &[TermId],
        stage: GuardedCollapseStage,
        incumbent: &mut IncumbentFacts,
        control: &mut Control<'_>,
    ) -> Option<bool> {
        control.admit(&self.proof_source_work, 1, 0)?;
        // A partial raw-source census may still support the older repair, but
        // this new producer explicitly preserves EVERY original assertion.
        if roots.is_empty() || roots.len() != self.ctx.assertions_parsed().len() {
            return Some(false);
        }
        let occurrences =
            collect::occurrences(self, roots, control).or_else(|| control.refuse())?;
        if occurrences.is_empty() {
            return Some(false);
        }
        let candidate = augmented(
            &mut self.ctx.terms,
            &self.proof_source_work,
            roots,
            &occurrences,
            control,
        )
        .or_else(|| control.refuse())?;
        drop(occurrences);
        control.admit(&self.proof_source_work, 0, 0)?;
        // Ahead of an exact divider the strict check decides with the division
        // abstracted, which costs less than the stage's wire screen (a complete
        // blast of the joint's lemma): there it is asked first
        // (`before_division.rs`). Either way a candidate needs both.
        let screen_first = stage != GuardedCollapseStage::BeforeExactDivision;
        let eligible = !screen_first
            || self.guarded_repair_worth_checking(proof, &candidate, stage, incumbent);
        control.admit(&self.proof_source_work, 0, 0)?;
        let accepted = eligible
            && self.check_proof_strict_until_stopped(&candidate).is_ok()
            && (screen_first
                || self.guarded_repair_worth_checking(proof, &candidate, stage, incumbent));
        control.admit(&self.proof_source_work, 0, 0)?;
        if !accepted {
            drop(candidate);
            control.admit(&self.proof_source_work, 0, 0)?;
            return Some(false);
        }
        for &root in roots {
            control.admit(&self.proof_source_work, 1, 0)?;
            self.record_raw_authored_problem_assertion(root);
        }
        self.purge_surface_overrides_for_certified_proof(&candidate);
        control.admit(&self.proof_source_work, 0, 0)?;
        *proof = candidate;
        control.admit(&self.proof_source_work, 0, 0)?;
        Some(true)
    }
}

fn augmented(
    terms: &mut TermStore,
    work: &crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourceWorkEnvelope,
    roots: &[TermId],
    occurrences: &[(TermId, TermId, u32)],
    control: &mut Control<'_>,
) -> Option<Proof> {
    let count = roots.len().checked_add(occurrences.len())?;
    control.admit(work, count, count.checked_mul(16)?)?;
    let mut premises = Vec::new();
    premises.try_reserve(count).ok()?;
    let mut proof = Proof::new();
    for &root in roots {
        control.admit(work, 1, 128)?;
        premises.push((root, proof.add_assume(root, None)));
    }
    for &(remainder, divisor, width) in occurrences {
        control.admit(work, 16, 2048)?;
        let zero = terms.mk_bitvec(0.into(), width);
        let is_zero = terms.mk_app(Symbol::named("="), vec![divisor, zero], Sort::Bool);
        let less = terms.mk_app(Symbol::named("bvult"), vec![remainder, divisor], Sort::Bool);
        let bound = terms.mk_app(Symbol::named("or"), vec![is_zero, less], Sort::Bool);
        let lemma =
            proof.add_theory_lemma_with_kind("bv", vec![bound], TheoryLemmaKind::BvUremBound);
        premises.push((bound, lemma));
    }
    finish_joint(terms, work, &premises, &mut proof, control)?;
    drop(premises);
    control.admit(work, 0, 0)?;
    Some(proof)
}

fn finish_joint(
    terms: &mut TermStore,
    work: &crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourceWorkEnvelope,
    premises: &[(TermId, ProofId)],
    proof: &mut Proof,
    control: &mut Control<'_>,
) -> Option<()> {
    control.admit(
        work,
        premises.len(),
        premises.len().checked_mul(16)?.checked_add(256)?,
    )?;
    let mut args = Vec::new();
    args.try_reserve(premises.len()).ok()?;
    args.extend(premises.iter().map(|(term, _)| *term));
    let root = terms.mk_app(Symbol::named("and"), args, Sort::Bool);
    let mut clause = Vec::new();
    clause.try_reserve(premises.len().checked_add(1)?).ok()?;
    clause.push(root);
    for &(premise, _) in premises {
        control.admit(work, 1, 128)?;
        clause.push(terms.mk_not_raw(premise));
    }
    control.admit(
        work,
        clause.len(),
        clause.len().checked_mul(4)?.checked_add(128)?,
    )?;
    let mut unit = proof.add_rule_step(AletheRule::AndNeg, clause.clone(), Vec::new(), Vec::new());
    for &(premise, derived) in premises {
        control.admit(
            work,
            clause.len(),
            clause.len().checked_mul(4)?.checked_add(128)?,
        )?;
        let _ = clause.remove(1);
        unit = proof.add_resolution(clause.clone(), premise, unit, derived);
    }
    control.admit(work, 4, 512)?;
    let negative = terms.mk_not_raw(root);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(Vec::new(), root, lemma, unit);
    drop(clause);
    control.admit(work, 0, 0)
}
