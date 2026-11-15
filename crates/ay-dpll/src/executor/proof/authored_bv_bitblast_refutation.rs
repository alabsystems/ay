// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Record a preprocessor fold-to-`false` as a BIT-BLAST refutation of the
//! authored roots, when AY's own bounded bit-blast checker re-derives it.
//!
//! ## Why this exists
//!
//! Term construction rewrites bit-vector terms before any proof is recorded:
//! `(bvudiv x #x00000002)` becomes `(bvlshr x #x00000001)`, `(bvmul x c)` for a
//! power-of-two `c` becomes a shift, and so on. When the rewrite makes the two
//! sides of an authored disequality the same term, the whole root folds to
//! `false` and the proof rests on `assume false`, which
//! `false_source::demote_unattributed_assumed_false` rightly erases. The four
//! rescues before this one recover the fold's argument by evaluation, by the
//! bounded Bool/Int/BV interpreter, by a spelled identity, or by propositional
//! structure. None of them covers an OPEN bit-vector root over free words —
//! external-codegen's `base + src/2^k == base + (src >>u k)` (`Add_Lsr_Shift`),
//! `x / 2^k == x >> k`, `UDIV Xd, Xn, #2^k == LSR` and 56 more of its strict-gate
//! obligations, measured 2026-09-28 on build 11390: every one printed
//! `(step t0 (cl) :rule hole)`.
//!
//! `replace_with_exact_authored_bv_refutation` already proves exactly such a
//! root by bit-blasting, but it reads the provenance ledger, where a folded
//! root is recorded as the constant `false`. This pass is that lemma over the
//! author's own assertion, re-interned RAW from the parsed surface.
//!
//! ## What is recorded
//!
//! ```text
//! (assume h A)
//! (step l (cl (not A)) :rule bv_bitblast)   ; re-derived by the strict checker
//! (step t (cl) :rule th_resolution :premises (l h))
//! ```
//!
//! `TheoryLemmaKind::BvBitBlast` is validated by the strict checker's bounded
//! bit-blast producer (`ay-proof/src/checker/bv_bitblast.rs`), which re-derives
//! the clause with an LRAT-checked refutation and refuses anything it cannot
//! decide. The printer lowers the same lemma through its checked
//! `bitblast_*` circuits (`format_checked_bv_bitblast_lowering`, ending in
//! `complete_blast`); where it cannot, it prints the honest `hole`, which is
//! never worse than the erasure this replaces.
//!
//! ## What this is NOT
//!
//! No checker rule, gate or mode policy changes. The candidate is committed
//! only when `check_proof_strict_with_datatypes` accepts it whole, it derives
//! the empty clause, every `assume` round-trips to the author's own assertion,
//! and the EXPORTER's own premise-scope check accepts it — the same four gates
//! as `authored_bv_lia_refutation`, whose module docs explain why the fourth
//! cannot be left to the strict checker. A satisfiable root is refused by the
//! bit-blaster itself.

use super::*;

pub(super) mod bv_literal_spelling;
mod finite_arrays;
mod singleton_screen;
pub(in crate::executor::proof) use singleton_screen::SingletonSearch;

#[derive(Clone, Copy)]
enum WordForm {
    Source,
    OffsetNormalized,
}

impl Executor {
    /// Replace an about-to-be-erased proof with a `BvBitBlast`-anchored
    /// refutation of the authored roots. `true` when a strictly-checked
    /// replacement was committed.
    pub(super) fn replace_with_exact_authored_bv_bitblast_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        self.replace_with_authored_bv_bitblast_refutation(proof, false)
    }

    /// The raw-root source of `repair_wire_gap_with_authored_root_refutation`:
    /// the same replacement for a strict-complete proof whose only defect is
    /// a wire gap, committed only when the replacement prints without an
    /// unproved step (`wire_repair_candidate_prints_clean`), since trading one
    /// gapped presentation for a lemma the printer cannot lower is no repair
    /// (the joint array lemma of `(= lo (concat #x0 #x4))`, measured
    /// 2026-09-29, displaced a `trans` chain the printer closes with
    /// `evaluate`).
    pub(super) fn repair_wire_gap_with_authored_bv_bitblast_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        self.replace_with_authored_bv_bitblast_refutation(proof, true)
    }

    fn replace_with_authored_bv_bitblast_refutation(
        &mut self,
        proof: &mut Proof,
        wire_clean: bool,
    ) -> bool {
        if !self.proof_source_work.spend(
            crate::executor::proof_repair::proof_trust_surgery_surface_audit::ProofSourcePass::AuthoredConjunctEvalRebuild,
            self.ctx.assertions_parsed(),
        ) {
            return false;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        if parsed.is_empty() {
            return false;
        }

        // (1) Re-intern the authored assertions RAW, keeping only the roots the
        // exporter's premise set already admits (see `authored_bv_lia_refutation`
        // step (1b): this pass reads the scope, it never widens it).
        let scope = self.proof_export_scope_assertions();
        let mut roots: Vec<(TermId, &FrontendTerm)> = Vec::new();
        if roots.try_reserve_exact(parsed.len()).is_err() {
            return false;
        }
        for assertion in &parsed {
            let Some(root) = self.raw_intern_surface(assertion) else {
                continue;
            };
            if matches!(self.ctx.terms.sort(root), Sort::Bool)
                && scope.contains(&root)
                && (self.is_pure_bit_vector_root(root)
                    || (wire_clean && self.is_bounded_const_array_root(root)))
            {
                roots.push((root, assertion));
            }
        }
        if roots.is_empty() {
            return false;
        }

        // (2) Each root ALONE first, except exact free definitions whose
        // singleton is provably satisfiable. This is search advice only: every
        // root stays in the unchanged joint attempt and all acceptance gates
        // below still run. The screen uses this query's original stop/work
        // owners; unsupported or refused scans keep the legacy singleton.
        let stop = self.make_proof_assembly_should_stop();
        let attempts = singleton_screen::candidate_selections(
            &roots,
            &scope,
            &self.ctx,
            &self.proof_source_work,
            &stop,
        );
        drop(stop);
        // (3) The replacement is exported WITHOUT the wire overrides of the
        // proof it replaces, like every other whole-proof raw rebuild: those
        // render the OLD proof's folded terms as authored text, and a raw
        // subterm that hash-conses with a folded one would print as that
        // text instead of its own. Measured on the definitional
        // `SDIV Xn, #-1 == NEG Xn` obligation: the whole signed-division `ite`
        // folds to `(bvneg xn)`, so the raw root's own `(bvneg xn)` printed as
        // the entire `ite`. The round-trip gate below reads the table the
        // replacement will be exported with; a decline restores the old one.
        let replaced_overrides = self.last_proof_term_overrides.take();
        let stop = self.make_proof_assembly_should_stop();
        for selected in attempts {
            if stop() {
                break;
            }
            if let Some(candidate) =
                self.authored_bv_bitblast_candidate(&selected, &scope, wire_clean)
            {
                *proof = candidate;
                return true;
            }
        }
        self.last_proof_term_overrides = replaced_overrides;
        false
    }

    /// Whether every node below `root` is Bool- or BitVec-sorted: no array,
    /// integer or uninterpreted-sort operand reaches the bit-blaster. The
    /// pass exists for pure bit-vector folds; offered an array frame
    /// (group_proofs `frame_ite_lift_nested`, measured 2026-09-29) the exact
    /// finite-array lowering spent the proof's budget and the verdict fell to
    /// `unknown`. Bounded; a larger root is not pure.
    fn is_pure_bit_vector_root(&self, root: TermId) -> bool {
        const MAX_NODES: usize = 1 << 16;
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_NODES
                || !matches!(self.ctx.terms.sort(term), Sort::Bool | Sort::BitVec(_))
            {
                return false;
            }
            stack.extend(self.ctx.terms.children(term));
        }
        true
    }

    /// The committed shape for one selection of authored roots, or `None` when
    /// any gate refuses it.
    fn authored_bv_bitblast_candidate(
        &mut self,
        selected: &[(TermId, &FrontendTerm)],
        scope: &[TermId],
        wire_clean: bool,
    ) -> Option<Proof> {
        self.authored_bv_bitblast_candidate_in_form(selected, scope, wire_clean, WordForm::Source)
            .or_else(|| {
                // Keep the original candidate first. A failed affine-adder
                // refutation can become cheap after checked offset cuts,
                // without assuming the normalized root or changing a limit.
                let stop = self.make_proof_assembly_should_stop();
                if stop()
                    || !selected
                        .iter()
                        .all(|&(root, _)| self.is_pure_bit_vector_root(root))
                {
                    return None;
                }
                self.authored_bv_bitblast_candidate_in_form(
                    selected,
                    scope,
                    wire_clean,
                    WordForm::OffsetNormalized,
                )
            })
    }

    fn authored_bv_bitblast_candidate_in_form(
        &mut self,
        selected: &[(TermId, &FrontendTerm)],
        scope: &[TermId],
        wire_clean: bool,
        form: WordForm,
    ) -> Option<Proof> {
        // Every `assume` must print back as the author wrote it.
        for &(root, assertion) in selected {
            if !scope.contains(&root)
                || !self.rebuilt_root_prints_as_authored_up_to_literals(root, assertion)
            {
                return None;
            }
        }
        let mut candidate = Proof::new();
        let assume_ids: Vec<ProofId> = selected
            .iter()
            .map(|&(root, _)| candidate.add_assume(root, None))
            .collect();
        let mut derived = Vec::with_capacity(selected.len());
        for (&assume, &(root, _)) in assume_ids.iter().zip(selected) {
            // The newly admitted bounded array lane records each affine cut
            // and lifts it through the raw root. The normalized root is
            // DERIVED from the authored assumption, never assumed itself.
            let next = if matches!(form, WordForm::OffsetNormalized)
                || (wire_clean && !self.is_pure_bit_vector_root(root))
            {
                ay_proof::derive_bv_offset_normalization(
                    &mut self.ctx.terms,
                    &mut candidate,
                    root,
                    assume,
                )?
            } else {
                (root, assume)
            };
            derived.push(next);
        }
        if matches!(form, WordForm::OffsetNormalized)
            && derived
                .iter()
                .zip(selected)
                .all(|(&(next, _), &(root, _))| next == root)
        {
            return None;
        }
        // The clause is `(not A_1) .. (not A_n)`, each an EXPLICIT outer
        // negation so resolution against `A_i` removes exactly that literal;
        // `mk_not_raw` must not fold, and a folded literal fails closed.
        let mut clause: Vec<TermId> = Vec::with_capacity(selected.len());
        for &(root, _) in &derived {
            let negated = self.ctx.terms.mk_not_raw(root);
            if !matches!(self.ctx.terms.get(negated), TermData::Not(inner) if *inner == root) {
                return None;
            }
            clause.push(negated);
        }
        let mut current =
            candidate.add_theory_lemma_with_kind("bv", clause.clone(), TheoryLemmaKind::BvBitBlast);
        let mut residual = clause.clone();
        for &(root, assume_id) in &derived {
            let position = residual.iter().position(
                |&literal| matches!(self.ctx.terms.get(literal), TermData::Not(inner) if *inner == root),
            )?;
            let _ = residual.remove(position);
            current = candidate.add_rule_step(
                AletheRule::ThResolution,
                residual.clone(),
                vec![current, assume_id],
                Vec::new(),
            );
        }

        // A wire-gap repair must print without an unproved step. Asked first,
        // so a lemma the printer cannot lower costs no bit-blast and no strict
        // replay.
        if wire_clean && !self.wire_repair_candidate_prints_clean(&candidate) {
            return None;
        }
        // The bounded bit-blaster decides the clause, or the pass declines.
        if !self.recognize_bv_bitblast_until_stopped(&clause) {
            return None;
        }
        // Commit only what the UNCHANGED strict checker accepts whole and what
        // the exporter's own authority check accepts against the scope as it
        // stands now (candidate construction interned raw negations).
        let accepted = residual.is_empty()
            && Self::proof_derives_empty_clause(&candidate)
            && self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
            && ay_proof::validate_reachable_assumes_in_problem_scope(
                &candidate,
                &self.proof_export_scope_assertions(),
            )
            .is_ok();
        accepted.then_some(candidate)
    }
}

#[cfg(test)]
mod memory_surface_tests;
