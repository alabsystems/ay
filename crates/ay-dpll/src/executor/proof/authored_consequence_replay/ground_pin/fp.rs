// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Close an authored instance with an independently checked FP lemma.

use super::*;

/// This shortcut does not enumerate residual variables. Bound the entire
/// variable-free input before asking the exact FP kernel to evaluate it.
const MAX_CLOSED_FP_NODES: usize = 512;

fn closed_fp_instance(terms: &TermStore, instance: TermId) -> bool {
    if !matches!(terms.sort(instance), Sort::Bool) {
        return false;
    }
    let mut remaining = MAX_CLOSED_FP_NODES;
    let mut stack = vec![instance];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    let mut has_fp = false;
    while let Some(term) = stack.pop() {
        let Some(next) = remaining.checked_sub(1) else {
            return false;
        };
        remaining = next;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::App(..) | TermData::Not(_) | TermData::Ite(..) => {}
            _ => return false,
        }
        has_fp |= matches!(terms.sort(term), Sort::FloatingPoint(..));
        for child in terms.children(term) {
            if stack.len() >= remaining {
                return false;
            }
            stack.push(child);
        }
    }
    has_fp
}

impl Executor {
    /// Propose one exact clause over the original query, then use the existing
    /// strict authored-scope installation boundary. Literal pins are premises
    /// of the checked theorem, never substitutions granted as assumptions.
    pub(in crate::executor) fn try_install_pinned_fp_refutation(&mut self) -> bool {
        let Ok(scope) = self.capture_tactic_construction() else {
            return false;
        };
        let Some(candidate) = self.build_pinned_fp_refutation(&scope) else {
            return false;
        };
        if ay_core::term::reserve_counted(&mut self.proof_construction_memory, 1, &scope).is_err() {
            return false;
        }
        let Some(memory) = scope.retain_data_memory(self) else {
            return false;
        };
        if !self.install_consequence_replay_candidate(Some(candidate)) {
            return false;
        }
        self.proof_construction_memory.push(memory);
        true
    }

    fn build_pinned_fp_refutation(
        &mut self,
        scope: &crate::executor::model::evaluation_copies::TacticConstructionScope,
    ) -> Option<Proof> {
        use ay_core::term::{
            reserve_counted, reserve_map_counted, CountedBuiltin, CountedTermBuilder,
            TermConstructionAdmission,
        };

        let mut roots = Vec::new();
        let bound = self.independent_gate_query_root_bound()?;
        reserve_counted(&mut roots, bound, scope).ok()?;
        let _ = self
            .visit_independent_gate_query_roots(
                || scope.admit(1, 0),
                |root| {
                    roots.push(root);
                    std::ops::ControlFlow::Continue(())
                },
            )
            .ok()?;
        // Repeated authored assertions are the same premise, not additional
        // resolution pivots. Keep original order and the SAME paid buffer.
        let mut seen = ay_core::kani_compat::DetHashMap::default();
        let mut retained = 0;
        for index in 0..roots.len() {
            scope.admit(1, 0).ok()?;
            let root = roots[index];
            if seen.contains_key(&root) {
                continue;
            }
            reserve_map_counted(&mut seen, 1, scope).ok()?;
            seen.insert(root, ());
            roots[retained] = root;
            retained += 1;
        }
        roots.truncate(retained);
        if roots.is_empty() || !scope.validate(self) {
            return None;
        }
        let count = roots.len().checked_add(2)?;
        u32::try_from(count).ok()?;
        let mut clause = Vec::new();
        reserve_counted(&mut clause, roots.len(), scope).ok()?;
        {
            let mut builder =
                CountedTermBuilder::with_admission(&mut self.ctx.terms, scope).ok()?;
            for &root in &roots {
                clause.push(builder.apply(CountedBuiltin::Not, &[root]).ok()?);
            }
            builder.finish().ok()?;
        }
        if !scope.validate(self)
            || !ay_proof::recognize_fp_ground_eval_without_enumeration_with_progress(
                &self.ctx.terms,
                &clause,
                &mut |work, bytes| scope.admit(work, bytes).is_ok(),
            )
        {
            return None;
        }
        let mut steps = Vec::new();
        reserve_counted(&mut steps, count, scope).ok()?;
        let mut premises = Vec::new();
        reserve_counted(&mut premises, roots.len().checked_add(1)?, scope).ok()?;
        scope.admit(1, 2).ok()?;
        steps.push(ProofStep::TheoryLemma {
            theory: "FP".to_owned(),
            clause,
            farkas: None,
            kind: TheoryLemmaKind::FpGroundEval,
            lia: None,
        });
        premises.push(ProofId(0));
        for &root in &roots {
            scope.admit(1, 0).ok()?;
            let assumption = ProofId(u32::try_from(steps.len()).ok()?);
            steps.push(ProofStep::Assume(root));
            premises.push(assumption);
        }
        // The existing strict n-ary resolver validates a unit tail by set
        // subtraction. Do not retain a quadratic triangle of clause suffixes.
        scope.admit(1, 0).ok()?;
        steps.push(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: Vec::new(),
            premises,
            args: Vec::new(),
        });
        scope.validate(self).then(|| Proof::from_steps(steps))
    }

    /// Refute a bounded closed authored FP root without constructing a SAT
    /// model. This reuses the ordinary proof factory and its full strict
    /// installation boundary, not a Boolean simplification as a new premise.
    pub(in crate::executor) fn try_install_closed_authored_fp_refutation(&mut self) -> bool {
        let candidate = self.build_closed_authored_fp_refutation();
        if !self.install_consequence_replay_candidate(candidate) {
            return false;
        }
        let installed = self.last_proof.take();
        // Plan only the authored spellings: the broad input-rewrite pipeline
        // can replace a derivation on a presentation-budget refusal. This
        // already checked native candidate needs no such derivation changes.
        if self.ctx.retains_parsed_assertions() {
            if let Ok((_, overrides)) = self.prepare_surface_overrides() {
                self.last_proof_term_overrides = (!overrides.is_empty()).then_some(overrides);
            }
            if let Some(proof) = installed.as_ref() {
                // Restore after installation so a presentation refusal is
                // never cleared by the native installer's lifecycle reset.
                self.restore_reachable_authored_assume_surface_overrides(proof);
            }
        }
        self.last_proof = installed;
        true
    }

    /// The same bounded proof factory also repairs an ordinary ground UNSAT
    /// trace. No quantified instance or second solver run is needed: the
    /// independent kernel checks the negation of an original authored root.
    pub(in crate::executor::proof) fn replace_with_closed_authored_fp_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let Some(candidate) = self.build_closed_authored_fp_refutation() else {
            return;
        };
        // Native authority comes from the exact frozen premises and checker,
        // independently of whether their Alethe spelling can be retained.
        // The existing presentation/export boundary still refuses absent or
        // unsupported external surfaces.
        let authored = self.exact_concrete_authored_scope();
        self.commit_if_strictly_checked(proof, candidate, &authored);
    }

    fn build_closed_authored_fp_refutation(&mut self) -> Option<Proof> {
        let authored = self.exact_concrete_authored_scope();
        let plans = ay_core::kani_compat::DetHashMap::default();
        authored
            .iter()
            .take(MAX_CANDIDATE_CHECKS)
            .find_map(|&root| self.build_fp_instance_refutation(&authored, &plans, root))
    }

    /// No equality pin is needed when the exact instance is already false in
    /// every interpretation. The FP kernel proves its negation; the ordinary
    /// consequence derivation supplies the instance from the authored roots.
    /// The caller retains the shared attempt/node budgets and checks the whole
    /// proof, including exact `forall_inst` substitution, before installation.
    pub(in crate::executor::proof::authored_consequence_replay) fn build_fp_instance_refutation(
        &mut self,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        instance: TermId,
    ) -> Option<Proof> {
        if self.should_abort_theory_loop() || !closed_fp_instance(&self.ctx.terms, instance) {
            return None;
        }
        let negated = self.ctx.terms.mk_not_raw(instance);
        // Preserve the older rule on its supported fragment, as the theory
        // classifier does. Consumers may support that rule independently of
        // the exact-arithmetic extension.
        let kind = if let Some(operation) =
            ay_proof::recognize_fp_classification_op(&self.ctx.terms, &[negated])
        {
            TheoryLemmaKind::FpClassification { operation }
        } else if ay_proof::recognize_fp_ground_eval(&self.ctx.terms, &[negated]) {
            TheoryLemmaKind::FpGroundEval
        } else {
            return None;
        };
        let mut candidate = Proof::new();
        let authored_set = authored.iter().copied().collect();
        let mut unit_ids = ay_core::kani_compat::DetHashMap::default();
        let instance_unit = self.consequence_unit(
            &mut candidate,
            instance,
            &authored_set,
            authored,
            instance_plan,
            &mut unit_ids,
        )?;
        let refuted = candidate.add_step(ProofStep::TheoryLemma {
            theory: "FP".to_owned(),
            clause: vec![negated],
            farkas: None,
            kind,
            lia: None,
        });
        candidate.add_resolution(Vec::new(), instance, instance_unit, refuted);
        Some(candidate)
    }
}

#[cfg(test)]
mod tests;
