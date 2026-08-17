// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Authored single-binder `forall` roots whose bodies are eligible for the
    /// strict structural `forall_inst` validator.
    fn authored_single_binder_foralls(
        &self,
        authored: &[TermId],
    ) -> Vec<(TermId, String, Sort, TermId)> {
        authored
            .iter()
            .filter_map(|&root| {
                let TermData::Forall(bindings, body, _) = self.ctx.terms.get(root) else {
                    return None;
                };
                let body = *body;
                let [(name, sort)] = bindings.as_slice() else {
                    return None;
                };
                if matches!(
                    self.ctx.terms.get(body),
                    TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
                ) {
                    return None;
                }
                Some((root, name.clone(), sort.clone(), body))
            })
            .collect()
    }

    /// Emit and independently validate one complementary witnessed pair.
    fn checked_witness_conflict_candidate(
        &mut self,
        authored: &[TermId],
        witness: TermId,
        positive: (TermId, TermId),
        negative: (TermId, TermId),
    ) -> Option<Proof> {
        let (pos_root, pos_instance) = positive;
        let (neg_root, neg_instance) = negative;
        let mut candidate = Proof::new();
        let pos_unit =
            self.add_forall_instance_prologue(&mut candidate, pos_root, witness, pos_instance);
        let neg_unit =
            self.add_forall_instance_prologue(&mut candidate, neg_root, witness, neg_instance);
        // `pos_instance` = A(w) is the resolution pivot;
        // `neg_instance` = (not A(w)).
        candidate.add_resolution(Vec::new(), pos_instance, pos_unit, neg_unit);

        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
        {
            Some(candidate)
        } else {
            None
        }
    }

    /// Build a genuine, strict-checkable `forall_inst` refutation whose empty
    /// clause comes from TWO authored universals whose instances at a shared
    /// element are complementary — the empty / witnessed-universe conflict
    /// (`∀x. p(x)` ∧ `∀x. ¬p(x)`).
    ///
    /// This is the shared certificate builder behind both entry points:
    /// [`Self::replace_with_exact_authored_witnessed_forall_conflict_refutation`]
    /// (the ordinary trust-rejected cascade member) and
    /// [`Self::try_translate_witnessed_forall_conflict_unsat`] (the EPR
    /// empty-universe artifact-firewall translation, where AY has already
    /// checked the singleton-instance UNSAT but its raw proof names the
    /// synthesized witness assertions rather than the authored `forall`s).
    ///
    /// The honest refutation states where each instance comes from, and every
    /// step already has a strict validator in `ay-proof`:
    ///
    /// ```text
    /// (assume h0 F1)                            ; F1 = (forall (x) A(x))
    /// (assume h1 F2)                            ; F2 = (forall (x) (not A(x)))
    /// (step p0 (cl (or (not F1) A(w)))       :rule forall_inst :args (w))
    /// (step p1 (cl (not F1) A(w))            :rule or :premises (p0))
    /// (step p2 (cl A(w))                     :rule resolution :premises (p1 h0))
    /// (step p3 (cl (or (not F2) (not A(w)))) :rule forall_inst :args (w))
    /// (step p4 (cl (not F2) (not A(w)))      :rule or :premises (p3))
    /// (step p5 (cl (not A(w)))               :rule resolution :premises (p4 h1))
    /// (step p6 (cl)                          :rule resolution :premises (p2 p5))
    /// ```
    ///
    /// The shared witness `w` is a producer-side HINT: any ground term of the
    /// binder sort works, and a fresh element is minted only when the problem
    /// has none. `validate_forall_inst` re-checks that `w` is ground w.r.t. the
    /// source binders and of the declared sort and that each instance is the
    /// EXACT substitution; the `or`/`resolution` steps are re-checked
    /// independently.
    ///
    /// Returns `Some(candidate)` ONLY when the candidate derives the empty
    /// clause, keeps every reachable `assume` in the authored scope, and passes
    /// the plain `check_proof_strict_with_datatypes` gate complete; otherwise
    /// `None`. A wrong witness or a non-complementary pair can only cost a
    /// declined candidate, never an unsound one.
    fn build_witnessed_forall_conflict_certificate(
        &mut self,
        authored: &[TermId],
    ) -> Option<Proof> {
        /// Cap on distinct ground witnesses proposed per binder sort.
        const MAX_WITNESS_CANDIDATES: usize = 8;
        /// Cap on `(forall, forall, witness)` proposals. Each surviving proposal
        /// costs at most one strict replay.
        const MAX_PROPOSALS: usize = 48;

        // Nested binders fail closed in the structural validator, so the
        // collector excludes them before the bounded proposal scan.
        let forall_roots = self.authored_single_binder_foralls(authored);
        if forall_roots.len() < 2 {
            return None;
        }

        let mut proposals = 0usize;
        for i in 0..forall_roots.len() {
            for j in (i + 1)..forall_roots.len() {
                let (root1, name1, sort1, body1) = &forall_roots[i];
                let (root2, name2, sort2, body2) = &forall_roots[j];
                if sort1 != sort2 {
                    continue;
                }

                // Witness pool: authored ground terms of the binder sort, or a
                // single fresh element when the problem has none (the empty /
                // witnessed-universe shape). A fresh element is sound for any
                // universal — SMT-LIB sorts are non-empty — and the strict
                // `forall_inst` validator only requires the argument to be
                // ground w.r.t. the SOURCE binders and of the declared sort.
                let mut witnesses = Self::ground_instantiation_candidates(
                    &self.ctx.terms,
                    authored,
                    sort1,
                    MAX_WITNESS_CANDIDATES,
                );
                if witnesses.is_empty() {
                    witnesses.push(self.ctx.terms.mk_fresh_var("ay_qwit", sort1.clone()));
                }

                for witness in witnesses {
                    proposals += 1;
                    if proposals > MAX_PROPOSALS {
                        return None;
                    }

                    let (Some(instance1), Some(instance2)) = (
                        Self::substitute_single_binder_structurally(
                            &mut self.ctx.terms,
                            *body1,
                            name1,
                            witness,
                        ),
                        Self::substitute_single_binder_structurally(
                            &mut self.ctx.terms,
                            *body2,
                            name2,
                            witness,
                        ),
                    ) else {
                        continue;
                    };

                    // The two instances must be complementary literals: one is
                    // exactly the raw negation of the other. The positive atom
                    // is the resolution pivot.
                    let (pos_root, pos_instance, neg_root, neg_instance) =
                        if self.instance_is_raw_negation(instance2, instance1) {
                            (*root1, instance1, *root2, instance2)
                        } else if self.instance_is_raw_negation(instance1, instance2) {
                            (*root2, instance2, *root1, instance1)
                        } else {
                            continue;
                        };

                    if let Some(candidate) = self.checked_witness_conflict_candidate(
                        authored,
                        witness,
                        (pos_root, pos_instance),
                        (neg_root, neg_instance),
                    ) {
                        return Some(candidate);
                    }
                }
            }
        }
        None
    }

    /// Cascade member: rebuild a trust-rejected proof as the witnessed-universe
    /// `forall_inst` conflict refutation when one applies.
    ///
    /// Fail-closed exactly like its `authored_forall*` siblings: runs only on a
    /// proof the strict checker already rejects; the candidate is committed only
    /// through the shared strict gate.
    pub(super) fn replace_with_exact_authored_witnessed_forall_conflict_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        /// Authored-scope size beyond which this pass declines. The pair scan
        /// is quadratic in the authored foralls and this runs on every
        /// refutation the strict checker rejects.
        const MAX_AUTHORED_ROOTS: usize = 64;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }
        if let Some(candidate) = self.build_witnessed_forall_conflict_certificate(&authored) {
            self.commit_if_strictly_checked(proof, candidate, &authored);
        }
    }

    /// EPR empty-universe artifact-firewall translation.
    ///
    /// The EPR singleton path ([`Self::mbqi_empty_universe_singleton_decide`])
    /// has already CHECKED the singleton-instance UNSAT, but its raw proof names
    /// the synthesized `ay_epr_u0` witness assertions rather than the authored
    /// `forall`s, so `quantified_semantic_unsat_or_unknown` fails the mandatory
    /// artifact firewall and downgrades the correct `unsat` to `unknown`.
    ///
    /// This translates that semantic verdict into an authored-scope
    /// `forall_inst` certificate and installs it as `last_proof`, so the
    /// ordinary publication funnel's strict-proof presentation check
    /// (`check_strict_unsat_presentation`) mints a genuine `StrictProof` token
    /// over the immutable authored query. Returns `true` only when a complete,
    /// scope-authorized, strict-checkable certificate was installed; on `false`
    /// the caller keeps the fail-closed firewall path and `last_proof` is
    /// untouched (the empty candidate is never installed).
    ///
    /// SOUNDNESS: nothing is taken on the producer's word. The installed proof
    /// is re-checked from scratch by the mandatory certification mint
    /// (`mint_unsat_certificate` → `check_strict_unsat_presentation`) before any
    /// verdict is published, so a mis-built certificate can only cost the
    /// firewall's `unknown`, never an unsound `unsat`.
    pub(in crate::executor) fn try_translate_witnessed_forall_conflict_unsat(&mut self) -> bool {
        /// Authored-scope size beyond which this translation declines.
        const MAX_AUTHORED_ROOTS: usize = 64;

        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return false;
        }
        let Some(candidate) = self.build_witnessed_forall_conflict_certificate(&authored) else {
            return false;
        };
        let Ok(quality) = self.check_proof_strict_with_datatypes(&candidate) else {
            return false;
        };
        if !quality.is_complete() {
            return false;
        }

        // The self-check gate runs before the public UNSAT certification mint.
        // Install the checker lifecycle state together with the proof, rather
        // than leaving a success bit from an older proof (or no success bit at
        // all). This mirrors the ordinary `build_unsat_proof` installation
        // boundary; a checker disagreement can only decline the translation.
        self.proof_check_result = None;
        self.proof_check_ok = false;
        self.last_proof_quality = None;
        #[cfg(feature = "proof-checker")]
        {
            self.run_internal_proof_check(&candidate);
            if !self.proof_check_ok {
                self.proof_check_result = None;
                return false;
            }
        }
        #[cfg(not(feature = "proof-checker"))]
        if self.self_check() {
            return false;
        }
        self.populate_proof_quality_stats(&quality);
        self.last_proof_quality = Some(quality);
        self.last_unsat_proof_reconstruction_suppressed = false;
        self.last_proof = Some(candidate);
        true
    }

    /// Whether `neg` is exactly the raw negation of `pos` — `neg = (not pos)`.
    fn instance_is_raw_negation(&self, neg: TermId, pos: TermId) -> bool {
        matches!(self.ctx.terms.get(neg), TermData::Not(inner) if *inner == pos)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn executor_with_assertions(script: &str) -> Executor {
        let commands = ay_frontend::parse(script).expect("witnessed-forall fixture parses");
        let mut exec = Executor::new();
        assert!(
            exec.execute_all(&commands)
                .expect("witnessed-forall fixture loads")
                .is_empty(),
            "fixture must contain declarations and assertions only"
        );
        exec
    }

    fn complementary_foralls(extra: &str) -> Executor {
        executor_with_assertions(&format!(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                {extra}
                (declare-fun p (U) Bool)
                (assert (forall ((x U)) (p x)))
                (assert (forall ((x U)) (not (p x))))
            "#
        ))
    }

    fn assert_certificate_declined(script: &str, label: &str) {
        let mut exec = executor_with_assertions(script);
        let authored = exec.ctx.assertions.clone();
        assert!(
            exec.build_witnessed_forall_conflict_certificate(&authored)
                .is_none(),
            "unsupported shape must not mint a certificate: {label}"
        );
        assert!(
            !exec.try_translate_witnessed_forall_conflict_unsat(),
            "unsupported shape must not install a proof: {label}"
        );
        assert!(exec.last_proof().is_none(), "{label}");
    }

    #[test]
    fn forged_forall_inst_witness_fails_strict_replay() {
        let mut exec = complementary_foralls("");
        let authored = exec.ctx.assertions.clone();
        let mut proof = exec
            .build_witnessed_forall_conflict_certificate(&authored)
            .expect("complementary authored foralls produce a certificate");
        let forged = exec
            .ctx
            .terms
            .mk_fresh_var("forged_qwit", Sort::Uninterpreted("U".to_owned()));
        let args = proof
            .steps
            .iter_mut()
            .find_map(|step| match step {
                ProofStep::Step {
                    rule: AletheRule::ForallInst,
                    args,
                    ..
                } => Some(args),
                _ => None,
            })
            .expect("certificate contains forall_inst");
        args[0] = forged;

        assert!(
            exec.check_proof_strict_with_datatypes(&proof).is_err(),
            "the checker must recompute exact substitution instead of trusting the witness hint"
        );
    }

    #[test]
    fn fresh_witness_is_internally_strict_but_problem_scoped_export_declines() {
        let mut exec = complementary_foralls("");
        let authored = exec.ctx.assertions.clone();
        let proof = exec
            .build_witnessed_forall_conflict_certificate(&authored)
            .expect("SMT sorts are non-empty, so a fresh witness is sound internally");
        assert!(exec
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete()));
        assert!(
            ay_proof::try_export_alethe_with_problem_scope_and_overrides(
                &proof,
                &exec.ctx.terms,
                &authored,
                None,
            )
            .is_err(),
            "an unregistered proof-only constant cannot be declared in an Alethe document"
        );
    }

    #[test]
    fn authored_ground_witness_has_a_problem_scoped_alethe_surface() {
        let mut exec = complementary_foralls(
            "(declare-const authored_w U) (declare-fun q (U) Bool) (assert (q authored_w))",
        );
        let authored = exec.ctx.assertions.clone();
        let proof = exec
            .build_witnessed_forall_conflict_certificate(&authored)
            .expect("authored ground witness produces a certificate");
        let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &exec.ctx.terms,
            &authored,
            None,
        )
        .expect("authored witness is resolvable from the problem scope");
        assert!(document.contains(":rule forall_inst"));
        assert!(!document.contains("(declare-"));
    }

    #[test]
    fn noncomplementary_predicates_do_not_mint_a_certificate() {
        assert_certificate_declined(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun p (U) Bool)
                (declare-fun q (U) Bool)
                (assert (forall ((x U)) (p x)))
                (assert (forall ((x U)) (not (q x))))
            "#,
            "noncomplementary predicates",
        );
    }

    #[test]
    fn binder_sort_mismatch_does_not_mint_a_certificate() {
        assert_certificate_declined(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                (declare-sort V 0)
                (declare-fun p (U) Bool)
                (declare-fun q (V) Bool)
                (assert (forall ((x U)) (p x)))
                (assert (forall ((x V)) (not (q x))))
            "#,
            "binder sort mismatch",
        );
    }

    #[test]
    fn nested_and_multi_binders_do_not_mint_certificates() {
        assert_certificate_declined(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun r (U U) Bool)
                (assert (forall ((x U)) (forall ((y U)) (r x y))))
                (assert (forall ((x U)) (forall ((y U)) (not (r x y)))))
            "#,
            "nested binders",
        );
        assert_certificate_declined(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun r (U U) Bool)
                (assert (forall ((x U) (y U)) (r x y)))
                (assert (forall ((x U) (y U)) (not (r x y))))
            "#,
            "multiple binders",
        );
    }

    #[test]
    fn foralls_buried_under_or_do_not_mint_a_certificate() {
        assert_certificate_declined(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun p (U) Bool)
                (declare-const guard Bool)
                (assert (or guard (forall ((x U)) (p x))))
                (assert (or guard (forall ((x U)) (not (p x)))))
            "#,
            "foralls under or",
        );
    }
}
