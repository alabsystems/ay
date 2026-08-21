// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

type AuthoredNegatedExists = (TermId, TermId, Vec<(String, Sort)>, TermId);

/// Authored-scope size beyond which this pass declines (the scans are
/// quadratic in the authored roots).
const MAX_AUTHORED_ROOTS: usize = 64;
/// Cap on `(negated-exists, ground-root)` proposals per rejected proof. Each
/// surviving one costs a single strict replay.
const MAX_PROPOSALS: usize = 64;

impl Executor {
    /// Rebuild a UNIVERSAL-INSTANTIATION refutation whose universal is the NNF
    /// DUAL of an authored NEGATED EXISTENTIAL, `¬∃x⃗.φ`, rather than an authored
    /// `forall` (#p2-diag-position, the negated-exists lane).
    ///
    /// [`Self::replace_with_exact_authored_forall_inst_refutation`] closes the
    /// case where the source universal is an authored `forall` root. The dual
    /// shape asserts `(not (exists (x⃗) φ))` together with a ground root that is
    /// an INSTANCE of `φ`:
    ///
    /// ```text
    /// (assert (not (s d d)))
    /// (assert (not (exists ((x U) (y U)) (not (s x y)))))
    /// ```
    ///
    /// `¬∃x⃗.φ` is classically equivalent to the universal `∀x⃗.¬φ`, whose
    /// diagonal instance `¬φ[d,d] = ¬¬(s d d)` contradicts `¬(s d d)`. AY decides
    /// it every time — its `collect_entailed_foralls` mints exactly that dual and
    /// E-matches the diagonal — but the produced refutation leans on the minted
    /// dual as a `trust`/generic leaf, which is NOT an authored root, so the
    /// mandatory certification gate turns a correct `unsat` into `unknown`.
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Every step is strict-checkable
    /// by `ay-proof`, and AY now emits them:
    ///
    /// ```text
    /// (assume h0 (not E))                       ; E = (exists (x⃗) φ)
    /// (assume h1 R)                             ; authored ground root, R = φ[t⃗]
    /// (step s1 (cl E F) :rule qnt_neg_exists)   ; F = (forall (x⃗) (not φ))
    /// (step s2 (cl F) :rule resolution :premises (h0 s1))
    /// (step s3 (cl (or (not F) I)) :rule forall_inst :args (t⃗))  ; I = (not R)
    /// (step s4 (cl (not F) I) :rule or :premises (s3))
    /// (step s5 (cl I) :rule resolution :premises (s4 s2))
    /// (step s6 (cl) :rule resolution :premises (s5 h1))
    /// ```
    ///
    /// NOTHING IS TAKEN ON THE PRODUCER'S WORD:
    ///
    /// * `qnt_neg_exists` — `ay_proof::checker::quantifier::validate_qnt_neg_exists`
    ///   independently re-derives that `F` is the exact De Morgan dual of `E`
    ///   (identical binder vector; `F`'s body is the single negation of `E`'s
    ///   body), which is what makes `(cl E F)` the tautology `A ∨ ¬A`.
    /// * `forall_inst` — `validate_forall_inst` re-derives binder/argument arity
    ///   and sorts, argument groundness, and that `I` is the EXACT simultaneous
    ///   capture-safe substitution of `F`'s body.
    /// * `or` — the clausification validator re-derives the disjunction.
    ///
    /// Fail-closed at every step, mirroring the sibling forall-inst passes: it
    /// runs only on a proof the strict checker already rejects; every `assume`
    /// is an exact authored root; and the rebuilt proof must derive the empty
    /// clause and pass `check_proof_strict_with_datatypes` (via
    /// [`Self::commit_if_strictly_checked`]) before it replaces anything. A
    /// mis-recognition can only leave the verdict the `unknown` it already is.
    pub(super) fn replace_with_exact_authored_negated_exists_forall_inst_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        let negated_exists_roots = self.exact_authored_negated_exists_roots(&authored);
        if negated_exists_roots.is_empty() {
            return;
        }

        let mut proposals = 0usize;
        for (not_exists_root, exists, bindings, body) in &negated_exists_roots {
            // The closing ground root R must be a Bool authored root that is an
            // INSTANCE of the existential body φ. Matching φ against R reads the
            // binder values t⃗; the derived instance is then I = (not R), which
            // resolves against the assumed R to close.
            for &ground_root in &authored {
                if ground_root == *not_exists_root
                    || self.ctx.terms.sort(ground_root) != &Sort::Bool
                {
                    continue;
                }
                let Some(values) =
                    Self::match_forall_body_instance(&self.ctx.terms, *body, ground_root, bindings)
                else {
                    continue;
                };
                proposals += 1;
                if proposals > MAX_PROPOSALS {
                    return;
                }

                let candidate = self.build_authored_negated_exists_candidate(
                    *not_exists_root,
                    *exists,
                    bindings,
                    *body,
                    ground_root,
                    values,
                );
                if self.commit_if_strictly_checked(proof, candidate, &authored) {
                    return;
                }
            }
        }
    }

    /// Collect the exact authored `not (exists ...)` roots this lane can replay.
    ///
    /// Shared with the ground-instantiation sibling
    /// (`authored_negated_exists_ground_inst`), which needs the identical
    /// recognition — an authored root that is literally `Not(Exists(..))` —
    /// and must NOT reach for `forall_ids_in_conjunctive_position`, whose NNF
    /// rewrite mints a FRESH `Forall` id that is not the authored node.
    pub(super) fn exact_authored_negated_exists_roots(
        &self,
        authored: &[TermId],
    ) -> Vec<AuthoredNegatedExists> {
        authored
            .iter()
            .filter_map(|&root| {
                let TermData::Not(inner) = self.ctx.terms.get(root) else {
                    return None;
                };
                let exists = *inner;
                let TermData::Exists(bindings, body, _) = self.ctx.terms.get(exists) else {
                    return None;
                };
                let body = *body;
                if bindings.is_empty()
                    || matches!(
                        self.ctx.terms.get(body),
                        TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
                    )
                {
                    return None;
                }
                Some((root, exists, bindings.clone(), body))
            })
            .collect()
    }

    /// Build the strict-checkable derivation for one matched authored pair.
    fn build_authored_negated_exists_candidate(
        &mut self,
        not_exists_root: TermId,
        exists: TermId,
        bindings: &[(String, Sort)],
        body: TermId,
        ground_root: TermId,
        values: Vec<TermId>,
    ) -> Proof {
        // F = (forall (x⃗) (not φ)), the De Morgan dual of E.
        let neg_body = self.ctx.terms.mk_not_raw(body);
        let forall = self.ctx.terms.mk_forall(bindings.to_vec(), neg_body);
        // I = (not R). Because φ[t⃗] is the interned root R, the raw
        // substitution of F's body (not φ) at t⃗ is exactly (not R), so this is
        // precisely the instance `validate_forall_inst` expects.
        let instance = self.ctx.terms.mk_not_raw(ground_root);
        let not_forall = self.ctx.terms.mk_not_raw(forall);
        let disjunction =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), vec![not_forall, instance], Sort::Bool);

        let mut candidate = Proof::new();
        let not_exists_assume = candidate.add_assume(not_exists_root, None);
        let ground_assume = candidate.add_assume(ground_root, None);
        let neg_exists_step = candidate.add_rule_step(
            AletheRule::QntNegExists,
            vec![exists, forall],
            Vec::new(),
            Vec::new(),
        );
        let forall_step =
            candidate.add_resolution(vec![forall], exists, not_exists_assume, neg_exists_step);
        let instantiated = candidate.add_rule_step(
            AletheRule::ForallInst,
            vec![disjunction],
            Vec::new(),
            values,
        );
        let clausified = candidate.add_rule_step(
            AletheRule::Or,
            vec![not_forall, instance],
            vec![instantiated],
            Vec::new(),
        );
        let instance_step =
            candidate.add_resolution(vec![instance], forall, clausified, forall_step);
        candidate.add_resolution(Vec::new(), ground_root, instance_step, ground_assume);
        candidate
    }
}
