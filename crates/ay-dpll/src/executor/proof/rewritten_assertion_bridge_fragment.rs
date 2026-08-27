// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assembling and committing one rewritten-assertion bridge fragment.
//!
//! Split out of `rewritten_assertion_bridge.rs` so each file stays inside the
//! repository's 500-line ceiling. The lane, its guards and its hypothesis
//! pools are in that file; this one turns a planned
//! [`ay_proof::DefinitionBridge`] into steps and splices them in.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId};
use ay_proof::DefinitionBridge;

use super::super::Executor;
use super::congruence_explanation::offset_premises;
use super::rewritten_assertion_bridge::HypothesisLeaf;

impl Executor {
    /// Build the replacement fragment: one leaf per cited hypothesis, the
    /// derivation, then one `th_resolution` per hypothesis.
    pub(super) fn assemble_bridge_fragment(
        &self,
        bridge: &DefinitionBridge,
        leaf_of: &DetHashMap<TermId, HypothesisLeaf>,
        atom: TermId,
    ) -> Option<Vec<ProofStep>> {
        let arity = bridge.hypotheses.len();
        // Guard 4, first half: the derivation's clause is the bridge clause.
        if arity == 0 || bridge.derivation.clause.len() != arity + 1 {
            return None;
        }
        if bridge.derivation.clause[arity] != atom {
            return None;
        }
        let mut steps: Vec<ProofStep> = Vec::with_capacity(
            arity
                .saturating_mul(2)
                .saturating_add(bridge.derivation.steps.len()),
        );
        // Each hypothesis contributes a leaf PREFIX of one or more steps; the
        // resolution below cites the prefix's LAST step, so a multi-step
        // derived leaf resolves exactly as a one-step leaf does.
        let mut leaf_ids: Vec<usize> = Vec::with_capacity(arity);
        let mut root_assumes: DetHashMap<TermId, usize> = DetHashMap::default();
        for &hypothesis in &bridge.hypotheses {
            leaf_ids.push(self.push_hypothesis_leaf(
                &mut steps,
                &mut root_assumes,
                leaf_of.get(&hypothesis)?,
                hypothesis,
            )?);
        }
        let base = steps.len();
        for step in &bridge.derivation.steps {
            steps.push(offset_premises(step.clone(), base));
        }
        let mut current = steps.len().checked_sub(1)?;
        let mut clause = bridge.derivation.clause.clone();
        for position in 0..arity {
            let pivot = bridge.derivation.clause[position];
            clause.retain(|&literal| literal != pivot);
            let id = steps.len();
            steps.push(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: clause.clone(),
                premises: vec![
                    ProofId(u32::try_from(current).ok()?),
                    ProofId(u32::try_from(*leaf_ids.get(position)?).ok()?),
                ],
                args: Vec::new(),
            });
            current = id;
        }
        // Guard 4, second half: the fragment ends on exactly the leaf's clause.
        (clause.as_slice() == [atom]).then_some(steps)
    }

    /// Emit the leaf PREFIX for one cited hypothesis and return the index of
    /// its LAST step — the step the bridge's `th_resolution` cites.
    ///
    /// An authored assertion, a checked definition and a READ-OVER-WRITE
    /// axiom instance are one step each. An
    /// `and`-CONJUNCT is an `assume` of its authored ROOT (shared across every
    /// hypothesis from the same root) plus one premiseless `and_pos` and one
    /// `th_resolution` per nesting level, so the conjunct is DERIVED rather
    /// than assumed.
    pub(super) fn push_hypothesis_leaf(
        &self,
        steps: &mut Vec<ProofStep>,
        root_assumes: &mut DetHashMap<TermId, usize>,
        leaf: &HypothesisLeaf,
        hypothesis: TermId,
    ) -> Option<usize> {
        match leaf {
            HypothesisLeaf::Authored => {
                steps.push(ProofStep::Assume(hypothesis));
                steps.len().checked_sub(1)
            }
            HypothesisLeaf::Definition { rule, args } => {
                steps.push(ProofStep::Step {
                    rule: rule.clone(),
                    clause: vec![hypothesis],
                    premises: Vec::new(),
                    args: args.clone(),
                });
                steps.len().checked_sub(1)
            }
            HypothesisLeaf::ArrayRowAxiom => {
                // Re-asked at EMISSION time, not just at pool time: the
                // recognizer is the checker's own, and the leaf may not be
                // written unless it answers `Some(true)` for exactly this
                // unit clause. A pool entry that somehow stopped being a
                // read-over-write instance declines the whole fragment.
                if ay_proof::recognize_array_select_store(&self.ctx.terms, &[hypothesis])
                    != Some(true)
                {
                    return None;
                }
                steps.push(ProofStep::TheoryLemma {
                    theory: "ArrayEUF".to_string(),
                    clause: vec![hypothesis],
                    farkas: None,
                    kind: ay_core::TheoryLemmaKind::ArraySelectStore { index_eq: true },
                    lia: None,
                });
                steps.len().checked_sub(1)
            }
            HypothesisLeaf::ArrayStoreOverwrite => {
                // Re-asked at EMISSION time, not just at pool time: the
                // recognizer is the checker's own, and the leaf may not be
                // written unless it classifies exactly this unit clause as the
                // row-chain kind. A pool entry that somehow stopped being a
                // store-over-store instance declines the whole fragment.
                if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &[hypothesis])
                    != Some(ay_core::TheoryLemmaKind::ArrayRowChain)
                {
                    return None;
                }
                steps.push(ProofStep::TheoryLemma {
                    theory: "ArrayEUF".to_string(),
                    clause: vec![hypothesis],
                    farkas: None,
                    kind: ay_core::TheoryLemmaKind::ArrayRowChain,
                    lia: None,
                });
                steps.len().checked_sub(1)
            }
            HypothesisLeaf::Conjunct { root, descents } => {
                let mut current = match root_assumes.get(root) {
                    Some(&id) => id,
                    None => {
                        steps.push(ProofStep::Assume(*root));
                        let id = steps.len().checked_sub(1)?;
                        root_assumes.insert(*root, id);
                        id
                    }
                };
                for descent in descents {
                    steps.push(ProofStep::Step {
                        rule: AletheRule::AndPos(descent.position),
                        clause: vec![descent.not_parent, descent.child],
                        premises: Vec::new(),
                        args: vec![descent.parent],
                    });
                    let and_pos = steps.len().checked_sub(1)?;
                    steps.push(ProofStep::Step {
                        rule: AletheRule::ThResolution,
                        clause: vec![descent.child],
                        premises: vec![
                            ProofId(u32::try_from(and_pos).ok()?),
                            ProofId(u32::try_from(current).ok()?),
                        ],
                        args: Vec::new(),
                    });
                    current = steps.len().checked_sub(1)?;
                }
                // The prefix must end on exactly the hypothesis clause.
                match steps.get(current) {
                    Some(ProofStep::Step { clause, .. }) if clause.as_slice() == [hypothesis] => {}
                    _ => return None,
                }
                Some(current)
            }
        }
    }

    /// Guard 5: whether the fragment would fail to PUBLISH.
    pub(super) fn bridge_fragment_is_unrenderable(
        &self,
        fragment: &[ProofStep],
        atom: TermId,
        overrides: Option<&DetHashMap<TermId, String>>,
    ) -> bool {
        let rendered = ay_proof::CongruenceDerivation {
            steps: fragment.to_vec(),
            clause: vec![atom],
        };
        if !ay_proof::congruence_derivation_renders(&self.ctx.terms, overrides, &rendered) {
            return true;
        }
        let Some(overrides) = overrides else {
            return false;
        };
        fragment.iter().any(|step| match step {
            ProofStep::Step { clause, .. } => {
                Self::eq_transitive_clause_is_unrenderable(&self.ctx.terms, overrides, clause)
            }
            _ => false,
        })
    }

    /// Splice every planned fragment in, remapping premise references, and
    /// revert wholesale if the rebuilt proof does not check.
    pub(super) fn commit_bridge_fragments(
        &self,
        proof: &mut Proof,
        mut plans: Vec<Option<Vec<ProofStep>>>,
    ) -> usize {
        let original = proof.steps.clone();
        let original_named = proof.named_steps.clone();
        let old = std::mem::take(&mut proof.steps);
        let mut remap: Vec<ProofId> = Vec::with_capacity(old.len());
        let mut steps: Vec<ProofStep> = Vec::with_capacity(old.len());
        let mut derived = 0usize;
        for (index, step) in old.into_iter().enumerate() {
            // Premises reference only EARLIER steps, already remapped.
            let step = super::remap_step_premises(step, &remap);
            if let Some(fragment) = plans[index].take() {
                let base = steps.len();
                for fragment_step in fragment {
                    steps.push(offset_premises(fragment_step, base));
                }
                remap.push(ProofId(u32::try_from(steps.len() - 1).unwrap_or(u32::MAX)));
                derived += 1;
                continue;
            }
            remap.push(ProofId(u32::try_from(steps.len()).unwrap_or(u32::MAX)));
            steps.push(step);
        }
        let mut named = original_named.clone();
        named.retain(|_, id| {
            let old_index = id.0 as usize;
            if !matches!(original.get(old_index), Some(ProofStep::Assume(_))) {
                return false;
            }
            let Some(new_id) = remap.get(old_index) else {
                return false;
            };
            *id = *new_id;
            true
        });
        proof.steps = steps;
        proof.named_steps = named;
        // Whole-proof backstop: never ship a proof this rebuild broke, and
        // never trade a certification the original had. The second condition
        // is not hypothetical — the strict checker's semantic precharge for
        // `weakening`/`reordering` is quadratic in the TREE-unfolded payload,
        // and this population's clauses ARE the heavily-shared `store` chains
        // where tree unfolding dwarfs the DAG.
        // #diagnostic-envelope: see `check_proof_gate_with_executor_progress`.
        if crate::executor::proof::check::check_proof_gate_with_executor_progress(self, proof)
            .is_err()
            || self.bridge_loses_certification(proof, &original, &original_named)
        {
            proof.steps = original;
            proof.named_steps = original_named;
            return 0;
        }
        derived
    }

    /// Whether the rewrite costs the MANDATORY gate a proof it certified
    /// before, decided by running that exact gate on both proofs. The cheap
    /// direction is checked FIRST: when the rebuilt proof certifies, nothing
    /// can have been lost and the second check never runs.
    pub(super) fn bridge_loses_certification(
        &self,
        rebuilt: &Proof,
        original: &[ProofStep],
        original_named: &DetHashMap<String, ProofId>,
    ) -> bool {
        if self.check_proof_strict_with_datatypes(rebuilt).is_ok() {
            return false;
        }
        let mut before = Proof::new();
        before.steps = original.to_vec();
        before.named_steps = original_named.clone();
        self.check_proof_strict_with_datatypes(&before).is_ok()
    }
}
