// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild a UNIVERSAL-INSTANTIATION refutation directly from exact
    /// authored roots (#trust-count→0, the `forall_inst` + ground-complement
    /// shape).
    ///
    /// The problem asserts a `forall` whose body is quantifier-free together
    /// with an authored ground assertion that is exactly the NEGATION of one
    /// of that body's instances. That is unsatisfiable by universal
    /// instantiation, and AY decides it every time — but the instance is
    /// produced by E-matching inside the quantifier lane, so no clause-level
    /// conflict reaches the SAT trace, the level-0 RUP replay declines, and
    /// the reconstruction closes on the whole-problem `trust` fallback. The
    /// rejected proof is literally
    ///
    /// ```text
    /// (assume h0 (not I))
    /// (step t0 (cl I) :rule trust)          <- Generic theory lemma
    /// (step t1 (cl) :rule th_resolution :premises (t0 h0))
    /// ```
    ///
    /// `(cl I)` is NOT a theory tautology — it holds only under the authored
    /// `forall` — so the deferred-trust rescue correctly cannot discharge it
    /// either, and the mandatory certification gate turns a correct `unsat`
    /// into `unknown`.
    ///
    /// The honest refutation states where `I` comes from, and every step of it
    /// is already checkable by `ay-proof`:
    ///
    /// ```text
    /// (assume h0 F)                                  ; F = (forall (x..) body)
    /// (assume h1 (not I))                            ; authored ground root
    /// (step t0 (cl (or (not F) I)) :rule forall_inst :args (v..))
    /// (step t1 (cl (not F) I)      :rule or :premises (t0))
    /// (step t2 (cl I)              :rule resolution :premises (t1 h0))
    /// (step t3 (cl)                :rule resolution :premises (t2 h1))
    /// ```
    ///
    /// Both `assume`s are drawn from the EXACT authored scope, and the only
    /// non-Boolean step is `forall_inst`, whose strict validator
    /// (`ay_proof::checker::quantifier::validate_forall_inst`) independently
    /// re-derives the whole certificate from the clause and args alone: the
    /// binder/argument arity and sorts, that every argument is GROUND with
    /// respect to the source binders, and that the instance is the EXACT
    /// simultaneous capture-safe substitution — rejecting duplicate binder
    /// names, same-name/distinct-identity variables, and any nested
    /// binder/`let` rather than approximating them.
    ///
    /// The binder-value search below is therefore a producer-side HINT only.
    /// It proposes `(F, values, I)` triples; the checker decides. A wrong or
    /// sloppy proposal can only make `check_proof_strict_with_datatypes`
    /// reject the candidate, which leaves the incoming proof — and the
    /// `unknown` — exactly as this pass found them. It can never widen what
    /// the checker accepts.
    ///
    /// (The printed WIRE rule is `forall_inst`, which Alethe implements.)
    pub(super) fn replace_with_exact_authored_forall_inst_refutation(&mut self, proof: &mut Proof) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();

        // Authored `(not I)` roots paired with the instance they negate. The
        // ground root of the refutation is drawn from this list, so nothing
        // outside the authored scope can enter.
        let negated_roots: Vec<(TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| match self.ctx.terms.get(root) {
                TermData::Not(inner) => Some((root, *inner)),
                _ => None,
            })
            .collect();
        if negated_roots.is_empty() {
            return;
        }

        // Authored `forall` roots with their binders and body, in authored
        // order. A `forall` whose body is itself a binder is skipped here: the
        // strict `forall_inst` validator fails closed on nested binders, so
        // proposing one could only produce a candidate it rejects.
        let forall_roots: Vec<(TermId, Vec<(String, Sort)>, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                let TermData::Forall(bindings, body, _) = self.ctx.terms.get(root) else {
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
                Some((root, bindings.clone(), body))
            })
            .collect();
        if forall_roots.is_empty() {
            return;
        }

        // Work bound. Each surviving proposal costs one full strict re-check,
        // and this pass runs on every refutation the strict checker rejects.
        // Declining past the bound leaves today's behaviour exactly as it is
        // (the verdict stays `unknown`), so it can only cost completeness on a
        // problem carrying more than this many DISTINCT matching
        // forall/ground-complement pairs.
        const MAX_FORALL_INST_CANDIDATES: usize = 64;
        let mut attempts = 0usize;

        for (forall_root, bindings, body) in &forall_roots {
            for &(ground_root, instance) in &negated_roots {
                if ground_root == *forall_root {
                    continue;
                }
                let Some(values) =
                    Self::match_forall_body_instance(&self.ctx.terms, *body, instance, bindings)
                else {
                    continue;
                };
                attempts += 1;
                if attempts > MAX_FORALL_INST_CANDIDATES {
                    return;
                }

                let not_forall = self.ctx.terms.mk_not_raw(*forall_root);
                let implication = self.ctx.terms.mk_app(
                    Symbol::named("or"),
                    vec![not_forall, instance],
                    Sort::Bool,
                );

                let mut candidate = Proof::new();
                let forall_assume = candidate.add_assume(*forall_root, None);
                let ground_assume = candidate.add_assume(ground_root, None);
                let instantiated = candidate.add_rule_step(
                    AletheRule::ForallInst,
                    vec![implication],
                    Vec::new(),
                    values,
                );
                let clausified = candidate.add_rule_step(
                    AletheRule::Or,
                    vec![not_forall, instance],
                    vec![instantiated],
                    Vec::new(),
                );
                let derived = candidate.add_resolution(
                    vec![instance],
                    *forall_root,
                    clausified,
                    forall_assume,
                );
                candidate.add_resolution(Vec::new(), instance, derived, ground_assume);

                if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
                    .is_ok()
                    && Self::proof_derives_empty_clause(&candidate)
                    && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                {
                    *proof = candidate;
                    return;
                }
            }
        }
    }

    /// Producer-side HINT: propose the binder values that would make
    /// `instance` the simultaneous substitution of `body`.
    ///
    /// One-sided structural match of the quantified body against a candidate
    /// ground instance. A binder variable binds the term it faces (consistently
    /// across occurrences); everything else must already be syntactically
    /// equal. Nested binders and `let` fail closed, matching the strict
    /// validator's own deliberate restriction.
    ///
    /// This decides NOTHING. Its output is re-derived from scratch by
    /// `validate_forall_inst`, so an imprecise match can only cost this pass a
    /// candidate, never buy an unsound one.
    fn match_forall_body_instance(
        terms: &TermStore,
        body: TermId,
        instance: TermId,
        bindings: &[(String, Sort)],
    ) -> Option<Vec<TermId>> {
        /// Node-pair budget; the shapes this lane targets are tiny, and
        /// declining an oversized body leaves the verdict exactly as it is.
        const MAX_MATCH_WORK: usize = 20_000;

        let binder_names: std::collections::HashSet<&str> =
            bindings.iter().map(|(name, _)| name.as_str()).collect();
        if binder_names.len() != bindings.len() {
            // Duplicate binder names are rejected by the strict validator.
            return None;
        }
        let mut bound: std::collections::HashMap<&str, TermId> = std::collections::HashMap::new();
        let mut work = 0usize;
        let mut stack = vec![(body, instance)];
        while let Some((pattern, actual)) = stack.pop() {
            work += 1;
            if work > MAX_MATCH_WORK {
                return None;
            }
            if let TermData::Var(name, _) = terms.get(pattern) {
                if binder_names.contains(name.as_str()) {
                    match bound.get(name.as_str()) {
                        Some(&seen) if seen != actual => return None,
                        Some(_) => {}
                        None => {
                            if terms.sort(pattern) != terms.sort(actual) {
                                return None;
                            }
                            bound.insert(name.as_str(), actual);
                        }
                    }
                    continue;
                }
            }
            if pattern == actual {
                continue;
            }
            match (terms.get(pattern), terms.get(actual)) {
                (TermData::Not(inner), TermData::Not(actual_inner)) => {
                    stack.push((*inner, *actual_inner));
                }
                (
                    TermData::Ite(condition, then_branch, else_branch),
                    TermData::Ite(actual_condition, actual_then, actual_else),
                ) => {
                    stack.extend([
                        (*condition, *actual_condition),
                        (*then_branch, *actual_then),
                        (*else_branch, *actual_else),
                    ]);
                }
                (TermData::App(symbol, args), TermData::App(actual_symbol, actual_args)) => {
                    if symbol != actual_symbol || args.len() != actual_args.len() {
                        return None;
                    }
                    stack.extend(args.iter().copied().zip(actual_args.iter().copied()));
                }
                _ => return None,
            }
        }
        // Every binder must be determined; a body that does not mention one of
        // its binders leaves the value unconstrained, and guessing it here
        // would be inventing a certificate rather than reading one off.
        bindings
            .iter()
            .map(|(name, _)| bound.get(name.as_str()).copied())
            .collect()
    }
}
