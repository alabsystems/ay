// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The congruence fragment the MINTED-DEFINITION leaf lane emits.
//!
//! Split out of `minted_definition_leaf.rs` so each file stays inside the
//! repository's 500-line ceiling. That file owns the lane, the alignment and
//! the minting guards; this one turns one `(root, leaf, pool)` triple into
//! steps.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ProofStep, TermData, TermId};

use super::super::Executor;
use super::rewritten_assertion_bridge::{is_binary_equality, HypothesisLeaf};

impl Executor {
    /// Derive `(cl atom)` from an `assume` of `root` plus a congruence between
    /// them, over `pool`.
    ///
    /// This is the non-equality bridge's shape with ONE difference, and it is
    /// measured rather than stylistic: the complement literal is the SYNTACTIC
    /// complement of `root`, not `mk_not(root)`. On this population `root` is
    /// an `and` application, and `mk_not` returns the De Morgan DUAL — Boolean-
    /// equivalent, but not a resolution complement, so the fragment's last
    /// `th_resolution` cannot cancel it. Measured on
    /// `clearsy_0000_00307_falsesat13`: all 6 planned fragments were reverted
    /// by `commit_bridge_fragments` with
    /// `InvalidResolution { rule: "th_resolution" }` before this was corrected.
    /// The sibling lane is left byte-identical; its own population never
    /// carries an `and`-headed root.
    pub(super) fn plan_minted_congruence_fragment(
        &mut self,
        atom: TermId,
        root: TermId,
        pool: &[TermId],
        leaf_of: &DetHashMap<TermId, HypothesisLeaf>,
    ) -> Option<Vec<ProofStep>> {
        if self.ctx.terms.sort(root) != self.ctx.terms.sort(atom) {
            return None;
        }
        let goal = self.ctx.terms.mk_eq(root, atom);
        if !is_binary_equality(&self.ctx.terms, goal) {
            return None;
        }
        let bridge = ay_proof::plan_definitional_bridge(&mut self.ctx.terms, goal, pool)?;
        // Guard 9: the untouched strict checker replays the congruence half,
        // closed, before any step of it may enter the proof.
        let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &bridge.derivation);
        if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_err() {
            return None;
        }
        let mut fragment = self.assemble_bridge_fragment(&bridge, leaf_of, goal)?;
        let equality_step = fragment.len().checked_sub(1)?;
        let complement =
            super::minted_definition_leaf::syntactic_complement(&mut self.ctx.terms, root);
        let not_goal = self.ctx.terms.mk_not(goal);
        // The gate literal must be a plain `Not` wrapper: `mk_not` normalises
        // De Morgan, and a literal that is not the wrapper is not what the
        // validator reads as `(not (= ..))`.
        if !matches!(self.ctx.terms.get(not_goal), TermData::Not(inner) if *inner == goal) {
            return None;
        }
        let clause = vec![not_goal, complement, atom];
        // Guard 9, second half: the propositional step is CHOSEN by the
        // checker, not by re-deriving its operand-order convention here.
        let rule = [AletheRule::EquivPos1, AletheRule::EquivPos2]
            .into_iter()
            .find(|rule| {
                let derivation = ay_proof::CongruenceDerivation {
                    steps: vec![ProofStep::Step {
                        rule: rule.clone(),
                        clause: clause.clone(),
                        premises: Vec::new(),
                        args: Vec::new(),
                    }],
                    clause: clause.clone(),
                };
                let closed =
                    ay_proof::close_congruence_derivation(&mut self.ctx.terms, &derivation);
                ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_ok()
            })?;
        fragment.push(ProofStep::Assume(root));
        let assumed = fragment.len() - 1;
        fragment.push(ProofStep::Step {
            rule,
            clause,
            premises: Vec::new(),
            args: Vec::new(),
        });
        let tautology = fragment.len() - 1;
        fragment.push(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![complement, atom],
            premises: vec![
                ay_core::ProofId(u32::try_from(tautology).ok()?),
                ay_core::ProofId(u32::try_from(equality_step).ok()?),
            ],
            args: Vec::new(),
        });
        let resolved = fragment.len() - 1;
        fragment.push(ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![atom],
            premises: vec![
                ay_core::ProofId(u32::try_from(resolved).ok()?),
                ay_core::ProofId(u32::try_from(assumed).ok()?),
            ],
            args: Vec::new(),
        });
        // The fragment must end on exactly the leaf's clause.
        match fragment.last() {
            Some(ProofStep::Step { clause, .. }) if clause.as_slice() == [atom] => Some(fragment),
            _ => None,
        }
    }
}
