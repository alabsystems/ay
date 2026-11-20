// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// A registered selector applied directly to its constructor has the value
/// of the corresponding field. Use that equality to transport an authored
/// bit-vector equation to the bit-blaster, retaining the original assumption.
impl Executor {
    pub(super) fn refute_projected_word_equality(
        &mut self,
        scope: &[TermId],
        leaves: &[OwnedLeaf],
        selectors: &[(String, Vec<String>)],
    ) -> Option<Proof> {
        for leaf in leaves {
            let Some((left, right)) = decode_eq_local(&self.ctx.terms, leaf.term) else {
                continue;
            };
            if !matches!(self.ctx.terms.sort(left), Sort::BitVec(_)) {
                continue;
            }
            for selected in [left, right] {
                let TermData::App(symbol, args) = self.ctx.terms.get(selected) else {
                    continue;
                };
                let [constructor] = args.as_slice() else {
                    continue;
                };
                let Some(value) =
                    projected_field(&self.ctx.terms, selectors, symbol.name(), *constructor)
                else {
                    continue;
                };
                let (field_sides, word_sides) = if selected == left {
                    ([value, left], [value, right])
                } else {
                    ([right, value], [left, value])
                };
                let field = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), field_sides, Sort::Bool);
                let word = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), word_sides, Sort::Bool);
                let impossible = self.ctx.terms.mk_not_raw(word);
                if !ay_proof::recognize_datatype_selector_project(
                    &self.ctx.terms,
                    &[field],
                    selectors,
                ) || !self.recognize_bv_bitblast_until_stopped(&[impossible])
                {
                    continue;
                }

                let mut proof = Proof::new();
                let assumption = append_owned_leaf(&mut self.ctx.terms, &mut proof, leaf)?;
                let projection = proof.add_theory_lemma_with_kind(
                    "datatype",
                    vec![field],
                    TheoryLemmaKind::DatatypeSelectorProject,
                );
                let (first, second) = if selected == left {
                    ((field, projection), (leaf.term, assumption))
                } else {
                    ((leaf.term, assumption), (field, projection))
                };
                let not_second = self.ctx.terms.mk_not_raw(second.0);
                let transitive = proof.add_rule_step(
                    AletheRule::EqTransitive,
                    vec![self.ctx.terms.mk_not_raw(first.0), not_second, word],
                    Vec::new(),
                    Vec::new(),
                );
                let remaining =
                    proof.add_resolution(vec![not_second, word], first.0, transitive, first.1);
                let derived = proof.add_resolution(vec![word], second.0, remaining, second.1);
                let refutation = proof.add_theory_lemma_with_kind(
                    "bv",
                    vec![impossible],
                    TheoryLemmaKind::BvBitBlast,
                );
                proof.add_resolution(Vec::new(), word, derived, refutation);
                if ay_proof::validate_reachable_assumes_in_problem_scope(&proof, scope).is_ok()
                    && Self::proof_derives_empty_clause(&proof)
                    && self
                        .check_proof_strict_with_datatypes(&proof)
                        .is_ok_and(|quality| quality.is_complete())
                {
                    return Some(proof);
                }
            }
        }
        None
    }
}
