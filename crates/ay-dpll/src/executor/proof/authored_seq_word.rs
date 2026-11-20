// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Propose a refutation of an exact negated sequence theorem. The independent
//! sequence kernel and ordinary strict authored-scope installer decide it.

use super::*;
use ay_core::term::{reserve_counted, TermConstructionAdmission};

const MAX_SOURCE_ROOTS: usize = 64;
const MAX_SOURCE_NODES: usize = 16_384;

impl Executor {
    /// This is a proof-producing presolver, including on disposable validity
    /// probes. A successful recognizer supplies DATA only: no result escapes
    /// without the ordinary complete strict proof and publication gates.
    pub(in crate::executor) fn try_presolve_seq_word_refutation(&mut self) -> Option<SolveResult> {
        let (candidate, memory) = self.propose_authored_seq_word_refutation()?;
        let result = if self.prepare_check_sat_internal_state()
            || !self.install_consequence_replay_candidate(Some(candidate))
            || self.should_abort_theory_loop()
        {
            self.last_proof = None;
            self.last_proof_quality = None;
            SolveResult::Unknown
        } else {
            self.proof_construction_memory.push(memory);
            self.last_model = None;
            self.last_unknown_reason = None;
            self.last_statistics.set_int("seq.word.checked_presolve", 1);
            SolveResult::unsat()
        };
        self.last_result = Some(result.clone());
        self.finalize_array_ext_shadow();
        self.finalize_unknown_diagnostics();
        Some(result)
    }

    fn propose_authored_seq_word_refutation(
        &mut self,
    ) -> Option<(
        Proof,
        crate::executor::model::evaluation_copies::RetainedEvaluationMemory,
    )> {
        let bound = self.independent_gate_query_root_bound()?;
        if bound == 0 || bound > MAX_SOURCE_ROOTS {
            return None;
        }
        let scope = self.capture_tactic_construction().ok()?;
        let mut roots = Vec::new();
        reserve_counted(&mut roots, bound, &scope).ok()?;
        self.visit_independent_gate_query_roots(
            || scope.admit(1, 0),
            |root| {
                roots.push(root);
                std::ops::ControlFlow::Continue(())
            },
        )
        .ok()?;
        let mut remaining = MAX_SOURCE_NODES;
        for root in roots {
            scope.admit(1, 0).ok()?;
            if self.ctx.terms.entry_stamp(root).is_none()
                || self.ctx.terms.sort(root) != &Sort::Bool
            {
                return None;
            }
            let TermData::Not(theorem) = self.ctx.terms.get(root) else {
                continue;
            };
            let theorem = *theorem;
            if !self.seq_word_source_operators_are_native(theorem, &scope, &mut remaining)? {
                continue;
            }
            // The independent kernel debits this SAME original account before
            // each traversal, comparison and scratch growth. No maximum-size
            // prepayment or fresh functional-model allowance is introduced.
            if !ay_proof::recognize_seq_ground_eval_with_progress(
                &self.ctx.terms,
                &[theorem],
                &mut |work, bytes| scope.admit(work, bytes).is_ok(),
            ) {
                continue;
            }
            let mut steps = Vec::new();
            reserve_counted(&mut steps, 3, &scope).ok()?;
            let mut clause = Vec::new();
            reserve_counted(&mut clause, 1, &scope).ok()?;
            clause.push(theorem);
            scope.admit(1, 3).ok()?;
            steps.push(ProofStep::TheoryLemma {
                theory: "SEQ".to_owned(),
                clause,
                farkas: None,
                kind: TheoryLemmaKind::SeqGroundEval,
                lia: None,
            });
            steps.push(ProofStep::Assume(root));
            let mut premises = Vec::new();
            reserve_counted(&mut premises, 2, &scope).ok()?;
            premises.extend([ProofId(0), ProofId(1)]);
            steps.push(ProofStep::Step {
                rule: AletheRule::Resolution,
                clause: Vec::new(),
                premises,
                args: Vec::new(),
            });
            reserve_counted(&mut self.proof_construction_memory, 1, &scope).ok()?;
            let memory = scope.retain_data_memory(self)?;
            return Some((Proof::from_steps(steps), memory));
        }
        None
    }

    /// The declaration-free proof kernel treats native spellings as native
    /// operations. Authenticate that interpretation against the live source
    /// context before proposing any lemma; an ordinary same-spelled UF cannot
    /// inherit sequence/arithmetic/Boolean semantics.
    fn seq_word_source_operators_are_native(
        &self,
        root: TermId,
        scope: &crate::executor::model::evaluation_copies::TacticConstructionScope,
        remaining: &mut usize,
    ) -> Option<bool> {
        let mut pending = Vec::new();
        reserve_counted(&mut pending, 1, scope).ok()?;
        pending.push(root);
        let mut has_sequence = false;
        while let Some(term) = pending.pop() {
            *remaining = remaining.checked_sub(1)?;
            scope.admit(1, 0).ok()?;
            if self.ctx.terms.entry_stamp(term).is_none() {
                return Some(false);
            }
            has_sequence |= matches!(self.ctx.terms.sort(term), Sort::Seq(_));
            if let TermData::App(Symbol::Named(name), _) = self.ctx.terms.get(term) {
                if matches!(
                    name.as_str(),
                    "seq.empty"
                        | "seq.unit"
                        | "seq.++"
                        | "seq.len"
                        | "seq.contains"
                        | "="
                        | "and"
                        | "or"
                        | "+"
                        | "<"
                        | "<="
                        | ">"
                        | ">="
                ) && (self.ctx.terms.is_declared_function(name)
                    || !self.ctx.canonical_operator_binding_is_unambiguous(name)
                    || self.ctx.symbol_info_by_identity(name).is_some_and(|info| {
                        self.ctx.effective_declaration_kind(info.declaration_id())
                            != Some(ay_frontend::DeclarationKind::Theory)
                    }))
                {
                    return Some(false);
                }
            }
            let ite_children;
            let children: &[TermId] = match self.ctx.terms.get(term) {
                TermData::Const(_) | TermData::Var(..) => &[],
                TermData::App(_, arguments) => arguments,
                TermData::Not(inner) => std::slice::from_ref(inner),
                TermData::Ite(condition, yes, no) => {
                    ite_children = [*condition, *yes, *no];
                    &ite_children
                }
                _ => return Some(false),
            };
            if pending.len().checked_add(children.len())? > *remaining {
                return None;
            }
            reserve_counted(&mut pending, children.len(), scope).ok()?;
            pending.extend_from_slice(children);
        }
        Some(has_sequence && scope.validate(self))
    }
}

#[cfg(test)]
mod tests;
