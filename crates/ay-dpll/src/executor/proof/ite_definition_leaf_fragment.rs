// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The ten-step replacement fragment of the ITE-definition leaf lane.
//!
//! Split out of `ite_definition_leaf.rs` so each file stays inside the
//! repository's 500-line ceiling. That file owns the lane, its guards and the
//! module-level soundness argument; this one owns the EMISSION — Guards 10 and
//! 11, the two checker recognizers asked on the exact triples that will be
//! written, and the `or_neg`/`contraction` packing.

use ay_core::proof_validation::recognize_fresh_def_eq;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol};

use super::super::Executor;
use super::ite_definition_leaf::IteDefinitionPlan;

impl Executor {
    /// Emit the ten-step fragment, or `None` when a checker recognizer
    /// declines one of the two new leaf steps (Guard 10) or the fragment would
    /// not end on the leaf's own clause (Guard 11).
    pub(super) fn assemble_ite_definition_fragment(
        &mut self,
        plan: &IteDefinitionPlan,
    ) -> Option<Vec<ProofStep>> {
        let definition = self.ctx.terms.mk_app(
            Symbol::named("="),
            [plan.definiendum, plan.definiens],
            Sort::Bool,
        );
        let projection = self.ctx.terms.mk_app(
            Symbol::named("="),
            [plan.definiens, plan.branch],
            Sort::Bool,
        );
        // Guard 10, on the exact triples that will be emitted.
        if recognize_fresh_def_eq(&self.ctx.terms, &[definition], 0, &[plan.definiendum]).is_err() {
            return None;
        }
        if !ay_proof::recognize_ite_branch_projection(&self.ctx.terms, &[plan.guard, projection]) {
            return None;
        }
        let not_definition = self.ctx.terms.mk_not_raw(definition);
        let not_projection = self.ctx.terms.mk_not_raw(projection);
        let not_equality = self.ctx.terms.mk_not_raw(plan.equality);
        let not_guard = self.ctx.terms.mk_not_raw(plan.guard);

        let id = |index: usize| ProofId(u32::try_from(index).unwrap_or(u32::MAX));
        let mut fragment = vec![
            ProofStep::Step {
                rule: AletheRule::FreshDefEq,
                clause: vec![definition],
                premises: Vec::new(),
                args: vec![plan.definiendum],
            },
            ProofStep::TheoryLemma {
                theory: "ite".to_owned(),
                clause: vec![plan.guard, projection],
                farkas: None,
                kind: ay_core::TheoryLemmaKind::IteBranchProjection,
                lia: None,
            },
            ProofStep::Step {
                rule: AletheRule::EqTransitive,
                clause: vec![not_definition, not_projection, plan.equality],
                premises: Vec::new(),
                args: Vec::new(),
            },
            ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![not_projection, plan.equality],
                premises: vec![id(2), id(0)],
                args: Vec::new(),
            },
            ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![plan.equality, plan.guard],
                premises: vec![id(3), id(1)],
                args: Vec::new(),
            },
        ];
        // `or_neg` + resolution per literal, then one `contraction` — the
        // packing `ite_guard_promotion` already uses, verbatim.
        let mut clause = vec![plan.equality, plan.guard];
        let mut cursor = 4usize;
        for (literal, complement) in [(plan.equality, not_equality), (plan.guard, not_guard)] {
            fragment.push(ProofStep::Step {
                rule: AletheRule::OrNeg,
                clause: vec![plan.or_term, complement],
                premises: Vec::new(),
                args: Vec::new(),
            });
            let introduction = fragment.len() - 1;
            if let Some(position) = clause.iter().position(|&l| l == literal) {
                let _removed = clause.remove(position);
            }
            clause.push(plan.or_term);
            fragment.push(ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: clause.clone(),
                premises: vec![id(cursor), id(introduction)],
                args: Vec::new(),
            });
            cursor = fragment.len() - 1;
        }
        fragment.push(ProofStep::Step {
            rule: AletheRule::Contraction,
            clause: vec![plan.or_term],
            premises: vec![id(cursor)],
            args: Vec::new(),
        });
        // Guard 11.
        match fragment.last() {
            Some(ProofStep::Step { clause, .. }) if clause.as_slice() == [plan.or_term] => {}
            _ => return None,
        }
        Some(fragment)
    }
}
