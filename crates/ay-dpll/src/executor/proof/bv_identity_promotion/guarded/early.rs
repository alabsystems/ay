// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Try a checked original-source memory refutation before SAT clausification.

use super::{bounded_source, source, Executor, FrontendTerm};
use ay_core::{Proof, Sort, TermId, TheoryLemmaKind};

mod array_read_bridge;
mod literal_spelling;
mod reflexive;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EarlyGroundKind {
    Memory,
    CompactMemory,
    PureBitVector,
}

impl Executor {
    pub(in crate::executor) fn try_early_ground_memory_refutation(&mut self) -> bool {
        early_note("entered");
        if crate::executor::theories::bv_cnf_dump::requested()
            || !self.ctx.objectives().is_empty()
            || !self.ctx.soft_constraints().is_empty()
            || self.ctx.assertions_parsed().len() != 1
            || self.should_abort_theory_loop()
        {
            early_note("plain source/control precondition declined");
            return false;
        }
        let Some(authored) = self.authenticated_plain_query_assertions_after_named_core_redirect()
        else {
            early_note("exact public epoch declined");
            return false;
        };
        if authored.len() != 1 {
            return false;
        }
        let Some((root, kind, used_definition)) = self.early_ground_memory_root(authored[0]) else {
            early_note("source reconstruction declined");
            return false;
        };
        if self.ctx.terms.sort(root) != &Sort::Bool {
            return false;
        }
        let negative = self.ctx.terms.mk_not_raw(root);
        if !self.early_ground_memory_terms_print_faithfully(&[root, negative])
            || self.should_abort_theory_loop()
        {
            early_note("printer roundtrip or live stop declined");
            return false;
        }
        // A pure BV conjunction is offered only to the existing bounded word
        // producer. A decline keeps the ordinary solver route; it never starts
        // the memory lane's whole-root bit-blast fallback.
        let candidate = if kind == EarlyGroundKind::PureBitVector {
            let Some(candidate) = self.early_ground_closure_memory_candidate(root) else {
                early_note("pure BV word closure declined");
                return false;
            };
            candidate
        } else {
            let candidate = self
                .early_reflexive_memory_candidate(root)
                .or_else(|| self.early_ground_closure_memory_candidate(root))
                .or_else(|| self.early_array_read_memory_candidate(root));
            match candidate {
                Some(proof) => proof,
                None if kind == EarlyGroundKind::CompactMemory => {
                    early_note("compact memory checked producers declined");
                    return false;
                }
                None => {
                    let mut proof = Proof::new();
                    let premise = proof.add_assume(root, None);
                    let lemma = proof.add_theory_lemma_with_kind(
                        "bv",
                        vec![negative],
                        TheoryLemmaKind::BvBitBlast,
                    );
                    proof.add_resolution(Vec::new(), root, premise, lemma);
                    proof
                }
            }
        };
        // Check the derivation with executor deadline/interrupt/memory controls.
        // Its ONLY Assume was authenticated above against the exact public
        // epoch, independently of any rebuilt-premise ledger. Do not record
        // that authority until the strict derivation succeeds.
        let quality = match self.check_proof_strict_derivation_with_datatypes(&candidate) {
            Ok(quality) => quality,
            Err(error) => {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    format!("early ground memory: strict derivation declined: {error}")
                });
                return false;
            }
        };
        if self.should_abort_theory_loop()
            || self
                .authenticated_plain_query_assertions_after_named_core_redirect()
                .as_deref()
                != Some(authored.as_slice())
        {
            return false;
        }
        let Ok(mut literal_spellings) =
            self.checked_ground_literal_spellings(root, negative, &candidate)
        else {
            return false;
        };
        if used_definition {
            // The raw producer expands nullary definitions before interning its
            // sole premise. Retain the ORIGINAL spelling as presentation DATA;
            // the exporter must still derive its equality through the authenticated
            // definition premises. Canonical printing alone loses that boundary.
            let Ok(source_work) = crate::executor::proof_repair::proof_trust_surgery_surface_audit::surface_source_work_probe_as(
            &self.ctx.assertions_parsed()[0],
            crate::executor::proof_repair::proof_trust_surgery_surface_audit::SurfaceWorkModel::Traversal,
        ) else {
            return false;
        };
            let Some(source_work) = source_work.checked_add(size_of::<(TermId, String)>() * 2)
            else {
                return false;
            };
            if !self
                .proof_source_work
                .spend_canonical_scan_work(source_work)
                || self.should_abort_theory_loop()
            {
                return false;
            }
            let original_spelling = crate::executor::proof_surface_syntax::format_frontend_term(
                &self.ctx.assertions_parsed()[0],
            );
            literal_spellings
                .get_or_insert_with(Default::default)
                .insert(root, original_spelling);
        }
        if self.should_abort_theory_loop()
            || self
                .authenticated_plain_query_assertions_after_named_core_redirect()
                .as_deref()
                != Some(authored.as_slice())
        {
            return false;
        }
        self.record_raw_authored_problem_assertion(root);
        self.commit_authenticated_plain_refutation(candidate, quality);
        self.last_proof_term_overrides = literal_spellings;
        early_note("committed exact-source refutation");
        true
    }

    fn early_ground_memory_root(
        &mut self,
        expected: TermId,
    ) -> Option<(TermId, EarlyGroundKind, bool)> {
        use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
            surface_source_work_probe_as, SurfaceWorkModel,
        };
        let original = &self.ctx.assertions_parsed()[0];
        // Existing nullary expansion remains bounded. A larger direct source
        // may be cloned only under the existing linear traversal policy; the
        // shared builder then independently refuses macros and excess work.
        let (assertion, used_definition) = source::expand_with_definition_use(&self.ctx, original)
            .or_else(|| {
                surface_source_work_probe_as(original, SurfaceWorkModel::Traversal).ok()?;
                Some((original.clone(), false))
            })?;
        let (root, kind) = match bounded_source(&assertion) {
            Some(true) => {
                let kind = if large_source(&assertion) {
                    EarlyGroundKind::Memory
                } else {
                    // Compact actual SSA memory statements need the same
                    // checked producers. A decline keeps their ordinary SAT
                    // route, without the large-memory whole-root fallback.
                    EarlyGroundKind::CompactMemory
                };
                (self.raw_intern_ground_bv_surface(&assertion)?, kind)
            }
            Some(false) if matches!(&assertion, FrontendTerm::App(head, args) if head == "and" && args.len() >= 2) =>
            {
                let root = self.raw_intern_ground_bv_surface(&assertion)?;
                if !self.is_pure_bit_vector_ground_root(root) {
                    return None;
                }
                (root, EarlyGroundKind::PureBitVector)
            }
            None => (
                self.raw_intern_shared_ground_memory_surface(&assertion)?,
                EarlyGroundKind::Memory,
            ),
            _ => return None,
        };
        (self.ctx.elaborate_surface_subterm(&assertion) == Some(expected)).then_some((
            root,
            kind,
            used_definition,
        ))
    }

    fn early_ground_memory_terms_print_faithfully(&mut self, terms: &[TermId]) -> bool {
        if self.should_abort_theory_loop() {
            return false;
        }
        // This is one derived proof shell paired with its source root, never
        // recursive peeling of authored syntax or a source-depth exemption.
        if let [root, negative] = terms {
            if !matches!(self.ctx.terms.get(*negative), ay_core::TermData::Not(child) if child == root)
                || self.ctx.terms.sort(*root) != &Sort::Bool
                || self.ctx.terms.sort(*negative) != &Sort::Bool
                || self.ctx.symbol_iter().any(|(name, _)| name == "not")
                || self.ctx.is_defined_fun("not")
                || self.ctx.adopted_macro_interp("not").is_some()
            {
                return false;
            }
        }
        let overrides = self.proof_export_term_overrides().unwrap_or_default();
        let Some(copy_budget) = self.ground_surface_render_budget(terms, &overrides) else {
            return false;
        };
        let Ok((mut rendered_terms, _, _actual_copy_work)) =
            ay_proof::format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
                &self.ctx.terms,
                terms,
                &overrides,
                &[],
                copy_budget,
            )
        else {
            return false;
        };
        let mut checked_root = None;
        for (index, &term) in terms.iter().enumerate() {
            if self.should_abort_theory_loop() {
                return false;
            }
            let Some(rendered) = rendered_terms.remove(&term) else {
                return false;
            };
            let Some(mut parsed) = super::super::super::parse_rendered_assertion(&rendered) else {
                return false;
            };
            use crate::executor::proof_repair::proof_trust_surgery_surface_audit::{
                surface_source_work_probe_as, SurfaceWorkModel,
            };
            // Charge the ENTIRE actual rendering, including the shell and its
            // payload, before inspecting its child or normalizing literals.
            if surface_source_work_probe_as(&parsed, SurfaceWorkModel::Traversal).is_err()
                || self.should_abort_theory_loop()
                || super::compact_roundtrip_literal_leaves(&mut parsed).is_none()
            {
                return false;
            }
            if terms.len() == 2 && index == 1 {
                let FrontendTerm::App(head, args) = &parsed else {
                    return false;
                };
                let [child] = args.as_slice() else {
                    return false;
                };
                if head != "not" || checked_root.as_ref() != Some(child) {
                    return false;
                }
                // The actual printed child passed a complete ordinary raw
                // roundtrip to root. The live, unshadowed builtin not above
                // and the exact core Not(root) relation authenticate this one
                // outer constructor without re-elaborating the checked body.
            } else {
                if !self.guarded_parsed_rendering_matches_term(&parsed, term)
                    && self.raw_intern_shared_ground_memory_surface(&parsed) != Some(term)
                {
                    return false;
                }
                if terms.len() == 2 {
                    checked_root = Some(parsed);
                }
            }
        }
        !self.should_abort_theory_loop()
    }
}

fn early_note(message: &str) {
    crate::executor::unsat_cert::probe_cert_reject(|| format!("early ground memory: {message}"));
}

// Large SSA memory claims need their authored geometry before preprocessing.
// Read/write parts below 8192 nodes were missed by the committed hint. Keep
// compact queries on their ordinary path and offer these to the bounded producer.
// This is a search hint; every installed refutation still passes strict replay.
fn large_source(root: &FrontendTerm) -> bool {
    let mut pending = vec![root];
    let mut nodes = 0usize;
    while let Some(term) = pending.pop() {
        nodes += 1;
        if nodes > 2048 {
            return true;
        }
        match term {
            FrontendTerm::App(_, args)
            | FrontendTerm::IndexedApp(_, _, args)
            | FrontendTerm::QualifiedApp(_, _, args) => pending.extend(args),
            _ => (),
        }
    }
    false
}

#[cfg(test)]
mod tests;
