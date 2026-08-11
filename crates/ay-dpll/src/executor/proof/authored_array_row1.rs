// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Array read-over-write collapse (#trust-count→0). When an assertion
    /// `(not (= (select (store a i e) i) e))` is elaborated, the term builder
    /// eagerly folds `select(store(a,i,e),i) → e` (the ROW1 rewrite), so the
    /// assertion collapses to `false` and the UNSAT proof degenerates to a
    /// single empty-clause `trust` step: the theory reasoning happened INSIDE
    /// simplification and left no lemma to certify. Reconstruct the refutation
    /// FROM THE PARSED ASSERTION — the real SMT-LIB input, retained structurally
    /// by the frontend — as
    ///   assume      (not (= (select (store a i e) i) e))   the input hypothesis
    ///   lemma ROW1  (= (select (store a i e) i) e)          strict-validated
    ///   resolution  □
    /// SOUND: fires ONLY when ay already returned UNSAT and the parsed assertion
    /// is a TRUE ROW1-negation (store index == select index AND stored value ==
    /// compared value), which is unsatisfiable on its own — so refuting it alone
    /// certifies the real input regardless of any other assertions. The emitted
    /// lemma is independently re-checked by the strict checker's
    /// `validate_array_select_store`; any structural mismatch leaves the trust
    /// step untouched (fail-closed). The `assume` term is reconstructed via raw
    /// builders (`mk_app` for the select-over-store, `mk_not_raw`) precisely so
    /// the ROW / store-eq folds cannot collapse it back to `false`.
    pub(super) fn promote_array_row_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        // Borrow split: snapshot the parsed assertions before mutating `terms`.
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((arr, idx, val)) = match_row1_negation(asrt) else {
                continue;
            };
            let (Some(a_id), Some(i_id), Some(e_id)) = (
                self.ctx.terms.lookup(arr),
                self.ctx.terms.lookup(idx),
                self.ctx.terms.lookup(val),
            ) else {
                continue;
            };
            if !matches!(self.ctx.terms.sort(a_id), Sort::Array(_)) {
                continue;
            }
            let elem_sort = self.ctx.terms.sort(e_id).clone();
            // Rebuild the structure the ROW1 fold erased. `mk_store` is a true
            // constructor (no ROW fold); the select must go through `mk_app`
            // (NOT `mk_select`, which would re-apply the fold) so the raw
            // application is interned; the equality and negation likewise use
            // raw builders so store-eq / not folds cannot collapse them.
            let store_t = self.ctx.terms.mk_store(a_id, i_id, e_id);
            let raw_select =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("select"), [store_t, i_id], elem_sort);
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [raw_select, e_id], Sort::Bool);
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);

            self.record_rebuilt_authored_proof_premise(neg_t);
            proof.steps.clear();
            proof.named_steps.clear();
            let assume_id = proof.add_assume(neg_t, None);
            let lemma_id = proof.add_theory_lemma_with_kind(
                "array",
                vec![eq_t],
                TheoryLemmaKind::ArraySelectStore { index_eq: true },
            );
            proof.add_resolution(vec![], eq_t, assume_id, lemma_id);
            return;
        }
    }

    /// Reconstruct a ROW1 value-mismatch refutation erased by eager folding.
    ///
    /// For an authored assertion
    /// `(= (select (store a i stored) i) compared)`, simplification replaces
    /// the select with `stored`. If the two values are arithmetically
    /// inconsistent, surface rewriting can otherwise print the resulting
    /// arithmetic lemma as though it directly refuted the unfurled select.
    /// Rebuild the missing theory boundary explicitly:
    ///
    /// 1. assume the exact raw authored equality;
    /// 2. derive `select(store(a,i,stored),i) = stored` by ROW1;
    /// 3. derive that the two equalities cannot both hold by a checked Farkas
    ///    certificate; and
    /// 4. resolve to the empty clause.
    ///
    /// Every recognition or checker failure is a no-op.
    pub(super) fn promote_array_row_value_mismatch(&mut self, proof: &mut Proof) {
        if !Self::proof_derives_empty_clause(proof) {
            return;
        }
        let parsed: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        for assertion in &parsed {
            let Some((array, index, stored, compared, select_on_left)) =
                match_row1_value_mismatch(assertion)
            else {
                continue;
            };
            let (Some(array), Some(index), Some(stored), Some(compared)) = (
                self.ctx.elaborate_surface_subterm(array),
                self.ctx.elaborate_surface_subterm(index),
                self.ctx.elaborate_surface_subterm(stored),
                self.ctx.elaborate_surface_subterm(compared),
            ) else {
                continue;
            };
            let Sort::Array(array_sort) = self.ctx.terms.sort(array).clone() else {
                continue;
            };
            if self.ctx.terms.sort(index) != &array_sort.index_sort
                || self.ctx.terms.sort(stored) != &array_sort.element_sort
                || self.ctx.terms.sort(compared) != &array_sort.element_sort
                || !matches!(&array_sort.element_sort, Sort::Int | Sort::Real)
            {
                continue;
            }

            let store = self.ctx.terms.mk_store(array, index, stored);
            let select = self.ctx.terms.mk_app(
                Symbol::named("select"),
                [store, index],
                array_sort.element_sort,
            );
            let row_equality =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [select, stored], Sort::Bool);
            let authored_equality = if select_on_left {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [select, compared], Sort::Bool)
            } else {
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [compared, select], Sort::Bool)
            };
            // The premise admitted below must be the exact recursively raw
            // SMT-LIB source, not merely a semantically equivalent equality
            // rebuilt from canonicalized children. Nested folds/reorderings
            // need their own explicit proof bridge; this narrow ROW1 repair
            // declines them.
            let Some(raw_authored_equality) = self.raw_intern_surface(assertion) else {
                continue;
            };
            if raw_authored_equality != authored_equality {
                continue;
            }
            let not_authored = self.ctx.terms.mk_not_raw(authored_equality);
            let not_row = self.ctx.terms.mk_not_raw(row_equality);
            let farkas = FarkasAnnotation::from_ints(&[1, 1]);
            let conflict = [
                TheoryLit::new(authored_equality, true),
                TheoryLit::new(row_equality, true),
            ];
            if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                &self.ctx.terms,
                &conflict,
                &farkas,
            )
            .is_err()
            {
                continue;
            }

            let mut rebuilt = Proof::new();
            let authored_id = rebuilt.add_assume(authored_equality, None);
            let row_id = rebuilt.add_theory_lemma_with_kind(
                "array",
                vec![row_equality],
                TheoryLemmaKind::ArraySelectStore { index_eq: true },
            );
            let conflict_id = rebuilt.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: vec![not_authored, not_row],
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let without_authored =
                rebuilt.add_resolution(vec![not_row], authored_equality, conflict_id, authored_id);
            rebuilt.add_resolution(vec![], row_equality, without_authored, row_id);

            let Ok(quality) = self.check_proof_strict_derivation_with_datatypes(&rebuilt) else {
                continue;
            };
            if quality.trust_count != 0 {
                continue;
            }
            *proof = rebuilt;
            self.record_rebuilt_authored_proof_premise(raw_authored_equality);
            self.last_proof_term_overrides = None;
            return;
        }
    }
}
