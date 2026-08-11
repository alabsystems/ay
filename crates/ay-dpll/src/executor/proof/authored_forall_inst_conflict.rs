// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
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
        // searched. A body that is itself a binder is skipped because
        // `validate_forall_inst` fails closed on nested binders, so proposing
        // one could only produce a candidate the checker rejects.
        let forall_roots: Vec<(TermId, String, Sort, TermId)> = authored
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
            .collect();
        if forall_roots.is_empty() {
            return;
        }

        let mut proposals = 0usize;
        for (forall_root, binder_name, binder_sort, body) in &forall_roots {
            let values = Self::ground_instantiation_candidates(
                &self.ctx.terms,
                &authored,
                binder_sort,
                MAX_INSTANTIATION_VALUES,
            );
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

    /// Producer-side HINT: ground terms of `sort` that could instantiate a
    /// binder, drawn from the authored scope's own sub-terms.
    ///
    /// The scan deliberately STOPS at every binder instead of descending into
    /// its body. That is what makes each proposal ground without a separate
    /// occurrence check: a bound variable can only appear under its own
    /// binder, so nothing reachable from this walk can mention one. Declared
    /// constants (which the term store represents as variables) are therefore
    /// eligible values, exactly as `validate_forall_inst` allows — it requires
    /// the argument to be ground with respect to the SOURCE BINDERS, not free
    /// of every variable.
    ///
    /// This decides nothing. `validate_forall_inst` re-checks the argument's
    /// sort and groundness and re-derives the substitution, so a useless
    /// proposal can only cost this pass one declined candidate.
    fn ground_instantiation_candidates(
        terms: &TermStore,
        authored: &[TermId],
        sort: &Sort,
        limit: usize,
    ) -> Vec<TermId> {
        /// Sub-term visits per scan. The scope is already capped, but a single
        /// deeply-shared assertion can still be large.
        const MAX_SCAN_WORK: usize = 20_000;

        let mut found: Vec<TermId> = Vec::new();
        let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
        let mut work = 0usize;
        let mut stack: Vec<TermId> = authored.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            work += 1;
            if work > MAX_SCAN_WORK || found.len() >= limit {
                break;
            }
            if terms.sort(term) == sort {
                found.push(term);
            }
            match terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_branch, else_branch) => {
                    stack.extend([*condition, *then_branch, *else_branch]);
                }
                // Binders are NOT descended into — see the doc comment.
                _ => {}
            }
        }
        found
    }

    /// Producer-side HINT: build `body[binder := value]` with RAW constructors.
    ///
    /// `validate_forall_inst`'s `matches_substitution` compares the instance to
    /// the body node by node, so the instance must be the LITERAL substitution
    /// — a folding builder (`mk_and`, `mk_ite`, `mk_or`) would collapse
    /// `(ite (< 5 0) 0 1)` to `1` and the checker would (correctly) refuse the
    /// result as "not the exact simultaneous binder substitution". Every node
    /// is therefore rebuilt through `mk_app` / `mk_ite_raw` / `mk_not_raw`,
    /// which intern without simplifying, at the ORIGINAL node's sort (only a
    /// same-sorted variable is replaced, so no sort can change).
    ///
    /// Returns `None` for a body carrying a nested binder or a `let`, matching
    /// the strict validator's own deliberate restriction.
    fn substitute_single_binder_structurally(
        terms: &mut TermStore,
        body: TermId,
        binder_name: &str,
        value: TermId,
    ) -> Option<TermId> {
        /// Node budget for one substitution.
        const MAX_SUBST_WORK: usize = 20_000;

        fn walk(
            terms: &mut TermStore,
            term: TermId,
            binder_name: &str,
            value: TermId,
            work: &mut usize,
            memo: &mut std::collections::HashMap<TermId, Option<TermId>>,
        ) -> Option<TermId> {
            if let Some(&cached) = memo.get(&term) {
                return cached;
            }
            *work += 1;
            if *work > MAX_SUBST_WORK {
                return None;
            }
            let sort = terms.sort(term).clone();
            let rebuilt = match terms.get(term).clone() {
                TermData::Var(name, _) if name == binder_name => {
                    (terms.sort(value) == &sort).then_some(value)
                }
                TermData::Var(..) | TermData::Const(..) => Some(term),
                TermData::Not(inner) => {
                    let inner = walk(terms, inner, binder_name, value, work, memo)?;
                    Some(terms.mk_not_raw(inner))
                }
                TermData::Ite(condition, then_branch, else_branch) => {
                    let condition = walk(terms, condition, binder_name, value, work, memo)?;
                    let then_branch = walk(terms, then_branch, binder_name, value, work, memo)?;
                    let else_branch = walk(terms, else_branch, binder_name, value, work, memo)?;
                    Some(terms.mk_ite_raw(condition, then_branch, else_branch))
                }
                TermData::App(symbol, args) => {
                    let mut rebuilt = Vec::with_capacity(args.len());
                    for arg in args {
                        rebuilt.push(walk(terms, arg, binder_name, value, work, memo)?);
                    }
                    Some(terms.mk_app(symbol, rebuilt, sort.clone()))
                }
                // A nested binder or `let` is rejected rather than descended
                // into: capture-avoidance is exactly what the strict validator
                // refuses to approximate, and so does this.
                _ => None,
            };
            memo.insert(term, rebuilt);
            rebuilt
        }

        let mut work = 0usize;
        let mut memo = std::collections::HashMap::new();
        let instance = walk(terms, body, binder_name, value, &mut work, &mut memo)?;
        (terms.sort(instance) == &Sort::Bool).then_some(instance)
    }

    /// Emit the shared prologue `assume F` → `forall_inst` → `or` →
    /// `resolution`, leaving the unit clause `(cl instance)`.
    fn add_forall_instance_prologue(
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
        let trailing = vec![Self::negated_root_literal(&mut self.ctx.terms, instance)];
        let (clause, farkas, kind, premises) =
            self.search_authored_farkas_conflict(&trailing, authored, max_premises)?;

        let mut candidate = Proof::new();
        let unit = self.add_forall_instance_prologue(&mut candidate, forall_root, value, instance);
        let mut current =
            candidate.add_theory_lemma_with_farkas_and_kind("LRA", clause.clone(), farkas, kind);
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
        remaining.is_empty().then_some(candidate)
    }
}
