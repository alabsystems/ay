// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Translate one independently checked false arithmetic instance of an
    /// authored universal into an authored-scope strict proof.
    ///
    /// The exact closed-forall lane already authenticates the source query,
    /// binder tuple, raw substitution, and false ground instance before it
    /// calls this helper. Translation is still independently fail-closed: the
    /// candidate assumes only the frozen authored scope, derives the instance
    /// through `forall_inst`, closes it with a checker-replayed Farkas lemma,
    /// and is installed only after the ordinary strict checker accepts the
    /// complete empty-clause derivation.  Failure leaves all proof state
    /// untouched so the caller can retain its semantic-only authority class.
    pub(in crate::executor) fn try_translate_arithmetic_forall_instance_unsat(
        &mut self,
        forall_root: TermId,
        value: TermId,
    ) -> bool {
        const MAX_AUTHORED_ROOTS: usize = 64;
        const MAX_FARKAS_PREMISES: usize = 4;

        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return false;
        }
        let TermData::Forall(bindings, body, _) = self.ctx.terms.get(forall_root).clone() else {
            return false;
        };
        let [(binder_name, binder_sort)] = bindings.as_slice() else {
            return false;
        };
        if self.ctx.terms.sort(value) != binder_sort {
            return false;
        }
        let Some(instance) = Self::substitute_single_binder_structurally(
            &mut self.ctx.terms,
            body,
            binder_name,
            value,
        ) else {
            return false;
        };
        let Some(candidate) = self.build_arithmetic_forall_instance_refutation(
            forall_root,
            value,
            instance,
            &authored,
            MAX_FARKAS_PREMISES,
        ) else {
            return false;
        };
        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_err()
            || !Self::proof_derives_empty_clause(&candidate)
        {
            return false;
        }
        let quality = match self.check_proof_strict_with_datatypes(&candidate) {
            Ok(quality) => quality,
            Err(_) => return false,
        };
        if !quality.is_complete() {
            return false;
        }

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

    /// Rebuild a UNIVERSAL-INSTANTIATION refutation whose instance is refuted
    /// by the REST of the authored problem rather than being the literal
    /// complement of one authored root (#trust-count→0).
    ///
    /// [`Self::replace_with_exact_authored_forall_inst_refutation`] closes the
    /// case where an authored root is exactly `(not I)` for an instance `I` of
    /// the `forall` body — a SYNTACTIC complement it can read the binder values
    /// off. The UFLIA "instantiate a referenced axiom, then contradict a ground
    /// arithmetic chain" shape is one step past that, and fell through to the
    /// whole-problem `trust` closer:
    ///
    /// ```text
    /// (assert (>= i 0))
    /// (assert (= i_prime (double i)))
    /// (assert (not (>= i_prime 0)))
    /// (assert (forall ((x Int)) (! (= (double x) (+ x x)) :pattern ((double x)))))
    /// ```
    ///
    /// The instance at `x := i` is `(= (double i) (+ i i))`, which complements
    /// NO authored root; it conflicts with three of them together, and only
    /// arithmetically. `(cl I)` is therefore not a theory tautology — it holds
    /// only under the authored `forall` — so the deferred-trust rescue cannot
    /// discharge it either, and the mandatory certification gate correctly
    /// turned a correct `unsat` into `unknown`:
    ///
    /// ```text
    /// strict UNSAT proof validation failed: step t5 uses unverified trust
    /// rule; deferred-trust discharge failed: a collected trust clause is not a
    /// standalone theory tautology AND the authored assertions could not be
    /// independently re-solved as UNSAT
    /// ```
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Every step below already has
    /// a strict validator in `ay-proof`, and AY now emits them:
    ///
    /// ```text
    /// (assume h0 F)                                  ; F = (forall (x) body)
    /// (step p0 (cl (or (not F) I)) :rule forall_inst :args (v))
    /// (step p1 (cl (not F) I)      :rule or :premises (p0))
    /// (step p2 (cl I)              :rule resolution :premises (p1 h0))
    /// (step p3 (cl (not r_1) … (not r_k) (not I)) :rule la_generic :args <farkas>)
    /// (step p4… (cl)               :rule resolution :premises (p3 h_1 … p2)
    /// ```
    ///
    /// NOTHING IS TAKEN ON THE PRODUCER'S WORD. The binder value, the instance
    /// and the arithmetic conflict are all producer-side HINTS that the
    /// checkers re-decide:
    ///
    /// * `forall_inst` — `ay_proof::checker::quantifier::validate_forall_inst`
    ///   re-derives binder/argument arity and sorts, argument groundness, and
    ///   that the instance is the EXACT simultaneous capture-safe substitution.
    /// * `or` — `ay-proof`'s clausification validator re-derives that the
    ///   conclusion carries exactly the premise disjunction's children.
    /// * the arithmetic conflict — `try_lra_farkas_reconstruction`, the same
    ///   LRA solver the checker's `la_generic` validator replays, must return
    ///   an actual certificate for the exact clause; a satisfiable premise set
    ///   yields none and no candidate is ever built.
    ///
    /// Fail-closed at every step, mirroring
    /// [`Self::replace_with_exact_authored_congruence_value_refutation`]: it
    /// runs only on a proof the strict checker already rejects; every `assume`
    /// is an exact authored root; and the rebuilt proof must derive the empty
    /// clause, keep every reachable assume inside the authored scope, and pass
    /// `check_proof_strict_with_datatypes` before it replaces anything. If any
    /// of that fails the proof — and the `unknown` — is left exactly as found,
    /// so this can never widen what the checker accepts.
    pub(super) fn replace_with_exact_authored_forall_inst_conflict_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        /// Authored-scope size beyond which this pass declines. The scans below
        /// are quadratic in the authored roots and this runs on every
        /// refutation the strict checker rejects; declining leaves the verdict
        /// exactly the `unknown` it already is.
        const MAX_AUTHORED_ROOTS: usize = 64;
        /// Cap on distinct ground values proposed for the binder.
        const MAX_INSTANTIATION_VALUES: usize = 16;
        /// Cap on `(forall, value)` proposals per rejected proof. Each one
        /// costs at most one strict replay.
        const MAX_PROPOSALS: usize = 48;
        /// Cap on the Farkas premise subset scan in ARM B. The UFLIA
        /// "instantiate a definition, then contradict a ground chain" shape
        /// needs three authored premises (a value equality, a bound, and the
        /// refuted comparison); `search_authored_farkas_conflict` bounds its
        /// own solver calls independently, so a large scope declines on the
        /// call budget rather than exploding here.
        const MAX_FARKAS_PREMISES: usize = 4;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        // Authored `forall` roots with a quantifier-free body and exactly ONE
        // binder. The value search below is per-binder, and both shapes this
        // lane closes bind one variable; a multi-binder `forall` is left to the
        // complement-matching sibling, whose values are read off rather than
        // searched. This flat conflict lane skips nested binders because the
        // bounded nested-chain producer owns them.
        let forall_roots = self.flat_authored_forall_roots(&authored);
        if forall_roots.is_empty() {
            return;
        }

        let mut proposals = 0usize;
        for (forall_root, binder_name, binder_sort, body) in &forall_roots {
            let mut values = Self::ground_instantiation_candidates(
                &self.ctx.terms,
                &authored,
                binder_sort,
                MAX_INSTANTIATION_VALUES,
            );
            // A universal can be refuted by a ground value even when the
            // authored scope contains no ground subterm of its binder sort.
            // Seed the arithmetic search with the canonical zero value used by
            // the enumerative quantifier lane. This is only a producer-side
            // hint: `forall_inst` re-checks the exact substitution and the
            // Farkas validator independently proves the resulting conflict.
            self.seed_canonical_arithmetic_zero(binder_sort, &mut values, MAX_INSTANTIATION_VALUES);
            for value in values {
                proposals += 1;
                if proposals > MAX_PROPOSALS {
                    return;
                }
                let Some(instance) = Self::substitute_single_binder_structurally(
                    &mut self.ctx.terms,
                    *body,
                    binder_name,
                    value,
                ) else {
                    continue;
                };
                if let Some(candidate) = self.build_arithmetic_forall_instance_refutation(
                    *forall_root,
                    value,
                    instance,
                    &authored,
                    MAX_FARKAS_PREMISES,
                ) {
                    if self.commit_if_strictly_checked(proof, candidate, &authored) {
                        return;
                    }
                }
            }
        }
    }

    fn flat_authored_forall_roots(
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

    fn seed_canonical_arithmetic_zero(
        &mut self,
        sort: &Sort,
        values: &mut Vec<TermId>,
        limit: usize,
    ) {
        let zero = match sort {
            Sort::Int => Some(self.ctx.terms.mk_int(BigInt::from(0))),
            Sort::Real => Some(
                self.ctx
                    .terms
                    .mk_rational(num_rational::BigRational::from_integer(BigInt::from(0))),
            ),
            _ => None,
        };
        let Some(zero) = zero else {
            return;
        };
        if let Some(position) = values.iter().position(|&value| value == zero) {
            let _ = values.remove(position);
        }
        values.insert(0, zero);
        values.truncate(limit);
    }

    /// Emit the shared prologue `assume F` → `forall_inst` → `or` →
    /// `resolution`, leaving the unit clause `(cl instance)`.
    pub(super) fn add_forall_instance_prologue(
        &mut self,
        candidate: &mut Proof,
        forall_root: TermId,
        value: TermId,
        instance: TermId,
    ) -> ProofId {
        let not_forall = self.ctx.terms.mk_not_raw(forall_root);
        let implication =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), vec![not_forall, instance], Sort::Bool);
        let forall_assume = candidate.add_assume(forall_root, None);
        let instantiated = candidate.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            vec![value],
        );
        let clausified = candidate.add_rule_step(
            AletheRule::Or,
            vec![not_forall, instance],
            vec![instantiated],
            Vec::new(),
        );
        candidate.add_resolution(vec![instance], forall_root, clausified, forall_assume)
    }

    /// Derive a negated, false closed arithmetic comparison with the strict
    /// `evaluate` rule. Recognition here is deliberately only syntactic: the
    /// proof checker re-evaluates the exact comparison and rejects the
    /// candidate unless it really is false.
    fn add_closed_false_comparison_unit(
        &mut self,
        candidate: &mut Proof,
        instance: TermId,
    ) -> Option<ProofId> {
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(instance) else {
            return None;
        };
        if !matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=")
            || args.is_empty()
            || !args
                .iter()
                .all(|&arg| matches!(self.ctx.terms.get(arg), TermData::Const(_)))
        {
            return None;
        }

        let false_term = self.ctx.terms.false_term();
        let equality =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [instance, false_term], Sort::Bool);
        let evaluated =
            candidate.add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new());
        let not_equality = self.ctx.terms.mk_not_raw(equality);
        let not_instance = self.ctx.terms.mk_not_raw(instance);
        let tautology = candidate.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equality, not_instance, false_term],
            Vec::new(),
            Vec::new(),
        );
        let elided = candidate.add_resolution(
            vec![not_instance, false_term],
            equality,
            tautology,
            evaluated,
        );
        let not_false = self.ctx.terms.mk_not_raw(false_term);
        let false_taut =
            candidate.add_rule_step(AletheRule::True, vec![not_false], Vec::new(), Vec::new());
        Some(candidate.add_resolution(vec![not_instance], false_term, false_taut, elided))
    }

    /// Build the refutation: the instance together with a subset of the
    /// authored roots is arithmetically infeasible.
    fn build_arithmetic_forall_instance_refutation(
        &mut self,
        forall_root: TermId,
        value: TermId,
        instance: TermId,
        authored: &[TermId],
        max_premises: usize,
    ) -> Option<Proof> {
        // Shape pre-filter, so the Farkas scan below (the only expensive thing
        // in this pass) runs only where it can possibly succeed: `la_generic`
        // consumes comparisons and asserted-true equalities over Int/Real
        // terms, so an instance that is not one of those can never be the
        // trailing literal of a certificate. This decides nothing — the
        // certificate is still `try_lra_farkas_reconstruction`'s.
        let arithmetic_instance = match self.ctx.terms.get(instance) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                matches!(name.as_str(), "=" | "<" | "<=" | ">" | ">=")
                    && matches!(self.ctx.terms.sort(args[0]), Sort::Int | Sort::Real)
                    && matches!(self.ctx.terms.sort(args[1]), Sort::Int | Sort::Real)
            }
            _ => false,
        };
        if !arithmetic_instance {
            return None;
        }
        let mut candidate = Proof::new();
        let unit = self.add_forall_instance_prologue(&mut candidate, forall_root, value, instance);

        let trailing = vec![Self::negated_root_literal(&mut self.ctx.terms, instance)];
        if let Some((clause, farkas, kind, premises)) =
            self.search_authored_farkas_conflict(&trailing, authored, max_premises)
        {
            let mut current = candidate.add_theory_lemma_with_farkas_and_kind(
                "LRA",
                clause.clone(),
                farkas,
                kind,
            );
            let mut remaining = clause;
            let supports: Vec<(TermId, ProofId)> = premises
                .iter()
                .map(|&root| (root, candidate.add_assume(root, None)))
                .chain(std::iter::once((instance, unit)))
                .collect();
            for (pivot, support) in supports {
                let negated = Self::negated_root_literal(&mut self.ctx.terms, pivot);
                let position = remaining.iter().position(|&literal| literal == negated)?;
                let _ = remaining.remove(position);
                current = candidate.add_resolution(remaining.clone(), pivot, current, support);
            }
            return remaining.is_empty().then_some(candidate);
        }

        let negated_unit = self.add_closed_false_comparison_unit(&mut candidate, instance)?;
        let _empty = candidate.add_resolution(Vec::new(), instance, unit, negated_unit);
        Some(candidate)
    }
}
