// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild a SYMBOLIC word-identity refutation directly from exact
    /// authored roots — the two shapes whose whole content is a closed-form
    /// theorem of the SMT-LIB 2.6 string theory rather than an evaluation.
    ///
    /// ```text
    /// (assert (not (str.contains x x)))              ; a word contains itself
    ///
    /// (assert (str.contains "ab" (str.++ x "c")))    ; "c" is not a factor of "ab"
    /// (assert (str.suffixof "c" (str.++ x "b")))     ; the last character is "b"
    ///
    /// (assert (= (str.++ x "c") (str.++ y "c")))     ; str.++ cancels on the right
    /// (assert (not (= x y)))
    /// ```
    ///
    /// AY decides both every time — the string solver closes the first on its
    /// self-containment rule and the second on the word-equation pre-pass — but
    /// neither closure reaches the SAT trace as a clause-level conflict, so the
    /// reconstruction falls through to the whole-problem `trust` closer, the
    /// rejected proof reads `uses unsupported theory lemma kind Generic`, and
    /// the mandatory gate degrades a correct `unsat` to `unknown`.
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. The refutation states the
    /// theorem it actually used, as a kind whose `ay-proof` validator
    /// INDEPENDENTLY re-derives it from the clause alone:
    ///
    /// * [`TheoryLemmaKind::StringContainmentIdentity`] —
    ///   `validate_string_containment_identity` re-checks that the two argument
    ///   positions hold the SAME `TermId` (or the exact empty-string constant in
    ///   the operator's own contained-word position) at the right polarity and
    ///   over String-sorted arguments.
    /// * [`TheoryLemmaKind::StringGroundFactorConflict`] —
    ///   `validate_string_ground_factor_conflict` re-runs its own factor scan
    ///   over the clause's OWN constants: a ground block of the contained word
    ///   absent from a ground container, or a ground pattern disagreeing with
    ///   the container's ground boundary block. It never reasons about the
    ///   symbolic parts, and rejects an over-long pattern, a symbolic container
    ///   or boundary, and a positive-polarity literal.
    /// * [`TheoryLemmaKind::StringConcatCancellation`] —
    ///   `validate_string_concat_cancellation` re-derives the shared operand run
    ///   and both residuals from the two-literal clause, rejecting a block that
    ///   is not syntactically identical, sits at the wrong end, or does not leave
    ///   exactly the conclusion's two sides.
    ///
    /// The producer proposes only; every candidate clause is admitted ONLY when
    /// the CHECKER'S OWN matcher (`ay_proof::recognize_string_containment_identity`,
    /// `recognize_string_ground_factor_conflict`,
    /// `recognize_string_concat_cancellation` — the exact preconditions of
    /// those validators) already accepts it, so no schema logic is duplicated
    /// here. The refutations are
    ///
    /// ```text
    /// (assume h0 (not (str.contains x x)))
    /// (step t0 (cl (str.contains x x)) :rule string_containment_identity)
    /// (step t1 (cl) :rule resolution :premises (t0 h0))
    ///
    /// (assume h0 (= (str.++ x "c") (str.++ y "c")))
    /// (assume h1 (not (= x y)))
    /// (step t0 (cl (not (= (str.++ x "c") (str.++ y "c"))) (= x y))
    ///          :rule string_concat_cancellation)
    /// (step t1 (cl (= x y)) :rule resolution :premises (t0 h0))
    /// (step t2 (cl)         :rule resolution :premises (t1 h1))
    /// ```
    ///
    /// FAIL-CLOSED at every step: the pass runs ONLY on a proof the strict
    /// checker already rejects, every `assume` is an exact authored root, and
    /// the rebuilt proof must derive the empty clause, keep every reachable
    /// assume inside the authored scope, and pass the PLAIN
    /// `check_proof_strict_with_datatypes` before it replaces anything. When no
    /// authored root carries one of the two theorems the pass declines and the
    /// proof — and the `unknown` — are left exactly as they were found.
    pub(super) fn replace_with_exact_authored_word_identity_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        const MAX_AUTHORED_ROOTS: usize = 64;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        // ── 1. One authored root whose complement is a string theorem ────
        //
        // Which kind applies is decided by the CHECKER'S OWN matchers, in the
        // order they are listed; a root no matcher accepts is skipped.
        for &root in &authored {
            let (theorem, pivot) = match self.ctx.terms.get(root) {
                TermData::Not(inner) => (*inner, *inner),
                _ => (self.ctx.terms.mk_not_raw(root), root),
            };
            let kind =
                if ay_proof::recognize_string_containment_identity(&self.ctx.terms, &[theorem]) {
                    TheoryLemmaKind::StringContainmentIdentity
                } else if ay_proof::recognize_string_ground_factor_conflict(
                    &self.ctx.terms,
                    &[theorem],
                ) {
                    TheoryLemmaKind::StringGroundFactorConflict
                } else {
                    continue;
                };
            let mut candidate = Proof::new();
            let lemma = candidate.add_theory_lemma_with_kind("STRINGS", vec![theorem], kind);
            let assume = candidate.add_assume(root, None);
            candidate.add_resolution(Vec::new(), pivot, lemma, assume);
            if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
                && Self::proof_derives_empty_clause(&candidate)
                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
            {
                *proof = candidate;
                return;
            }
        }

        // ── 2. A concatenation equality cancelled against a disequality ──
        for &disequality_root in &authored {
            let TermData::Not(goal) = self.ctx.terms.get(disequality_root) else {
                continue;
            };
            let goal = *goal;
            for &equality_root in &authored {
                if equality_root == disequality_root {
                    continue;
                }
                let negated_equality = self.ctx.terms.mk_not_raw(equality_root);
                let clause = vec![negated_equality, goal];
                if !ay_proof::recognize_string_concat_cancellation(&self.ctx.terms, &clause) {
                    continue;
                }
                let mut candidate = Proof::new();
                let lemma = candidate.add_theory_lemma_with_kind(
                    "STRINGS",
                    clause,
                    TheoryLemmaKind::StringConcatCancellation,
                );
                let equality = candidate.add_assume(equality_root, None);
                let cancelled =
                    candidate.add_resolution(vec![goal], equality_root, lemma, equality);
                let disequality = candidate.add_assume(disequality_root, None);
                candidate.add_resolution(Vec::new(), goal, cancelled, disequality);
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

    /// Rebuild a GROUND-SUBSTITUTION refutation directly from exact authored
    /// roots: one authored root pins a term to a ground value, and a second
    /// authored root becomes GROUND-FALSE once that value is substituted in.
    ///
    /// ```text
    /// (assert (= x "hello"))
    /// (assert (= (str.substr x 1 3) "abc"))   ; substr("hello",1,3) = "ell"
    /// ```
    ///
    /// AY decides this family every time — the extended-function reduction
    /// lane evaluates `str.substr` / `str.indexof` / `str.replace` on the
    /// propagated constant and closes the branch — but the reduction happens
    /// outside the SAT trace, so no clause-level conflict is recorded and the
    /// reconstruction falls through to the whole-problem `trust` closer. The
    /// rejected proof is `step tN uses unsupported theory lemma kind Generic`,
    /// the deferred-trust rescue cannot discharge a clause that is not a
    /// standalone tautology, and the mandatory gate degrades a correct `unsat`
    /// to `unknown`.
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Nothing here is asserted on
    /// the producer's authority; every step is a rule `ay-proof` validates
    /// INDEPENDENTLY:
    ///
    /// * [`AletheRule::Refl`] — `(cl (= t t))`, checked by `validate_refl`
    ///   (the two sides must be the same `TermId`).
    /// * [`AletheRule::EqCongruent`] —
    ///   `(cl (not (= a₁ b₁)) … (not (= aₙ bₙ)) (= (f a…) (f b…)))`, checked by
    ///   `validate_euf_congruent`, which re-derives that both sides apply the
    ///   SAME symbol at the same arity and that premise `i` connects exactly
    ///   argument position `i`.
    /// * [`AletheRule::EqCongruentPred`] — the predicate form
    ///   `(cl (not (= a₁ b₁)) … (not (p a…)) (p b…))`, checked by
    ///   `validate_euf_congruent_pred`.
    /// * [`TheoryLemmaKind::StringGroundEval`] — checked by
    ///   `validate_string_ground_eval`, whose OWN ground evaluator (a
    ///   memoized interval matcher independent of the solver's `WeRegex` /
    ///   `RegexSolver`) re-decides the substituted literal under SMT-LIB 2.6
    ///   Unicode-string semantics and fails closed on any non-ground leaf,
    ///   unimplemented operator, or budget exhaustion. The candidate literal
    ///   is proposed ONLY when the CHECKER'S OWN matcher
    ///   `ay_proof::recognize_string_ground_eval` — the exact precondition of
    ///   that validator — already accepts it, so no evaluation logic is
    ///   duplicated producer-side.
    ///
    /// The refutation for the example above is
    ///
    /// ```text
    /// (assume h0 (= x "hello"))
    /// (assume h1 (= (str.substr x 1 3) "abc"))
    /// (step t0 (cl (= 1 1)) :rule refl)
    /// (step t1 (cl (= 3 3)) :rule refl)
    /// (step t2 (cl (not (= x "hello")) (not (= 1 1)) (not (= 3 3))
    ///              (= (str.substr x 1 3) (str.substr "hello" 1 3)))
    ///          :rule eq_congruent)
    /// (step t3 (cl (= (str.substr x 1 3) (str.substr "hello" 1 3)))
    ///          :rule resolution :premises (t2 h0 t0 t1))
    /// (step t4 (cl (not (= (str.substr x 1 3) (str.substr "hello" 1 3)))
    ///              (not (= (str.substr x 1 3) "abc"))
    ///              (= (str.substr "hello" 1 3) "abc"))
    ///          :rule eq_congruent_pred)
    /// (step t5 (cl (= (str.substr "hello" 1 3) "abc"))
    ///          :rule resolution :premises (t4 t3 h1))
    /// (step t6 (cl (not (= (str.substr "hello" 1 3) "abc")))
    ///          :rule string_ground_eval)
    /// (step t7 (cl) :rule resolution :premises (t5 t6))
    /// ```
    ///
    /// FAIL-CLOSED at every step, mirroring
    /// [`Self::replace_with_exact_authored_string_length_arith_refutation`]:
    /// the pass runs ONLY on a proof the strict checker already rejects; every
    /// `assume` is an exact authored root; the substituted literal is admitted
    /// only by the checker's own ground-evaluation matcher; and the rebuilt
    /// proof must derive the empty clause, keep every reachable assume inside
    /// the authored scope, and pass the PLAIN
    /// `check_proof_strict_with_datatypes` before it replaces anything. When no
    /// authored root becomes ground-false the pass declines and the proof — and
    /// the `unknown` — are left exactly as they were found.
    ///
    /// NO FALSE-PROVE RISK: the candidate derives the empty clause from
    /// AUTHORED assertions plus clauses the strict checker independently
    /// re-derives, so it ESTABLISHES the verdict rather than borrowing it.
    pub(super) fn replace_with_exact_authored_ground_substitution_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        // Work bounds. This pass runs on every refutation the strict checker
        // rejects, so it must be cheap to DECLINE. Declining leaves today's
        // behaviour exactly as it is (the verdict stays `unknown`), so the
        // bounds can only cost completeness on shapes far larger than the
        // extended-function reduction family.
        const MAX_AUTHORED_ROOTS: usize = 64;
        const MAX_BINDINGS: usize = 16;
        // Also the recursion-depth cap: `rewrite_with_ground_bindings` and the
        // congruence emitter both descend one frame per node, and every frame
        // spends at least one unit of this budget.
        const MAX_REWRITE_NODES: usize = 1024;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }

        // ── The ground bindings ──────────────────────────────────────────
        //
        // An authored `(= subject value)` (either orientation) whose `value` is
        // GROUND and whose `subject` is not. `subject` must be a leaf so the
        // rewrite below is a plain occurrence replacement; a compound subject
        // would need matching modulo the rewrite itself.
        let mut bindings: Vec<GroundBinding> = Vec::new();
        for &root in &authored {
            let Some((left, right)) = decode_eq_local(&self.ctx.terms, root) else {
                continue;
            };
            let candidate = if Self::is_ground_for_substitution(&self.ctx.terms, right)
                && Self::is_substitutable_leaf(&self.ctx.terms, left)
            {
                Some((left, right))
            } else if Self::is_ground_for_substitution(&self.ctx.terms, left)
                && Self::is_substitutable_leaf(&self.ctx.terms, right)
            {
                Some((right, left))
            } else {
                None
            };
            let Some((subject, value)) = candidate else {
                continue;
            };
            // Rebuilding a parent node reuses the ORIGINAL node's sort, so a
            // sort-changing replacement would mint a mis-sorted term. A
            // well-sorted `=` cannot have one, but this reconstruction fails
            // closed rather than relying on that.
            if self.ctx.terms.sort(subject) != self.ctx.terms.sort(value) {
                continue;
            }
            // One value per subject. A second, DIFFERENT value for the same
            // subject would make the problem contradictory by an argument this
            // pass does not make, and keeping both would make the rewrite
            // depend on iteration order.
            if bindings.iter().any(|binding| binding.subject == subject) {
                continue;
            }
            if bindings.len() == MAX_BINDINGS {
                return;
            }
            bindings.push(GroundBinding {
                subject,
                value,
                root,
            });
        }
        if bindings.is_empty() {
            return;
        }

        // ── The authored root that becomes ground-false ──────────────────
        for &root in &authored {
            if bindings.iter().any(|binding| binding.root == root) {
                continue;
            }
            let (atom, positive) = match self.ctx.terms.get(root) {
                TermData::Not(inner) => (*inner, false),
                _ => (root, true),
            };
            if !matches!(self.ctx.terms.get(atom), TermData::App(..)) {
                continue;
            }
            let mut budget = MAX_REWRITE_NODES;
            let Some(substituted) = self.rewrite_with_ground_bindings(atom, &bindings, &mut budget)
            else {
                continue;
            };
            if substituted == atom {
                continue;
            }
            // The authored root gives `atom` the polarity `positive`. The
            // refutation needs the SUBSTITUTED atom to take the OPPOSITE truth
            // value, and the checker's own ground matcher must already agree
            // before a single step is built.
            let refuting_literal = if positive {
                self.ctx.terms.mk_not_raw(substituted)
            } else {
                substituted
            };
            if !ay_proof::recognize_string_ground_eval(&self.ctx.terms, &[refuting_literal]) {
                continue;
            }

            let mut candidate = Proof::new();
            let Some(transported) = self.emit_ground_substitution_transport(
                &mut candidate,
                &bindings,
                root,
                atom,
                substituted,
                positive,
            ) else {
                continue;
            };
            let ground = candidate.add_theory_lemma_with_kind(
                "STRINGS",
                vec![refuting_literal],
                TheoryLemmaKind::StringGroundEval,
            );
            candidate.add_resolution(Vec::new(), substituted, transported, ground);

            if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
                && Self::proof_derives_empty_clause(&candidate)
                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
            {
                *proof = candidate;
                return;
            }
        }
    }

    /// Transport the authored root's literal across the ground substitution,
    /// returning the id of the UNIT clause carrying the SUBSTITUTED literal at
    /// the root's own polarity — `(cl atom')` for a positive root,
    /// `(cl (not atom'))` for a negated one.
    ///
    /// `eq_congruent_pred` orients its clause from the negated predicate to the
    /// positive one, so a negated authored root is transported by the mirrored
    /// congruence (`atom'` on the negated side, `atom` on the positive side).
    fn emit_ground_substitution_transport(
        &mut self,
        candidate: &mut Proof,
        bindings: &[GroundBinding],
        root: TermId,
        atom: TermId,
        substituted: TermId,
        positive: bool,
    ) -> Option<ProofId> {
        let (negated_side, positive_side) = if positive {
            (atom, substituted)
        } else {
            (substituted, atom)
        };
        let TermData::App(symbol, negated_args) = self.ctx.terms.get(negated_side) else {
            return None;
        };
        let symbol = symbol.clone();
        let negated_args: Vec<TermId> = negated_args.clone();
        let TermData::App(other_symbol, positive_args) = self.ctx.terms.get(positive_side) else {
            return None;
        };
        if &symbol != other_symbol || negated_args.len() != positive_args.len() {
            return None;
        }
        let positive_args: Vec<TermId> = positive_args.clone();

        // `eq_congruent_pred` needs a premise only where the two argument
        // positions differ; identical positions are entailed by reflexivity and
        // its validator accepts their omission.
        let mut premises: Vec<(TermId, ProofId)> = Vec::new();
        for (&from, &to) in negated_args.iter().zip(positive_args.iter()) {
            if from == to {
                continue;
            }
            let derived = self.emit_ground_substitution_equality(candidate, bindings, from, to)?;
            if !premises.iter().any(|&(equality, _)| equality == derived.0) {
                premises.push(derived);
            }
        }

        let mut clause: Vec<TermId> = Vec::with_capacity(premises.len() + 2);
        for &(equality, _) in &premises {
            let complement = self.ctx.terms.mk_not_raw(equality);
            clause.push(complement);
        }
        let negated_literal = self.ctx.terms.mk_not_raw(negated_side);
        clause.push(negated_literal);
        clause.push(positive_side);
        let mut current = candidate.add_rule_step(
            AletheRule::EqCongruentPred,
            clause.clone(),
            Vec::new(),
            Vec::new(),
        );

        // Resolve each premise away, then the authored root itself. A literal
        // is removed wholesale rather than once, because resolution deletes
        // every copy of the pivot's complement from the resolvent.
        let mut residual = clause;
        for &(equality, unit) in &premises {
            let complement = self.ctx.terms.mk_not_raw(equality);
            if !residual.contains(&complement) {
                return None;
            }
            residual.retain(|&literal| literal != complement);
            current = candidate.add_resolution(residual.clone(), equality, current, unit);
        }
        let assume = candidate.add_assume(root, None);
        let cancelled = if positive {
            negated_literal
        } else {
            positive_side
        };
        if !residual.contains(&cancelled) {
            return None;
        }
        residual.retain(|&literal| literal != cancelled);
        let transported = candidate.add_resolution(residual.clone(), atom, current, assume);
        (residual.len() == 1).then_some(transported)
    }

    /// Emit the steps establishing `(= from to)` as a UNIT clause, returning
    /// the equality term and that unit's id.
    ///
    /// `to` is `from` with the ground bindings applied, so the two differ only
    /// where a bound subject was replaced. Identity closes by `refl`, a bound
    /// subject by its authored `assume`, and a compound term recurses through
    /// `eq_congruent`.
    fn emit_ground_substitution_equality(
        &mut self,
        candidate: &mut Proof,
        bindings: &[GroundBinding],
        from: TermId,
        to: TermId,
    ) -> Option<(TermId, ProofId)> {
        if from == to {
            let equality = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [from, to], Sort::Bool);
            let unit =
                candidate.add_rule_step(AletheRule::Refl, vec![equality], Vec::new(), Vec::new());
            return Some((equality, unit));
        }
        if let Some(binding) = bindings
            .iter()
            .find(|binding| binding.subject == from && binding.value == to)
        {
            return Some((binding.root, candidate.add_assume(binding.root, None)));
        }

        let TermData::App(symbol, from_args) = self.ctx.terms.get(from) else {
            return None;
        };
        let symbol = symbol.clone();
        let from_args: Vec<TermId> = from_args.clone();
        let TermData::App(other_symbol, to_args) = self.ctx.terms.get(to) else {
            return None;
        };
        if &symbol != other_symbol || from_args.len() != to_args.len() {
            return None;
        }
        let to_args: Vec<TermId> = to_args.clone();

        // `eq_congruent` demands one premise per argument position, so the
        // reflexive positions are stated too and discharged by `refl`.
        let mut premises: Vec<(TermId, ProofId)> = Vec::with_capacity(from_args.len());
        for (&from_arg, &to_arg) in from_args.iter().zip(to_args.iter()) {
            premises.push(
                self.emit_ground_substitution_equality(candidate, bindings, from_arg, to_arg)?,
            );
        }
        let conclusion = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [from, to], Sort::Bool);
        let mut clause: Vec<TermId> = Vec::with_capacity(premises.len() + 1);
        for &(equality, _) in &premises {
            let complement = self.ctx.terms.mk_not_raw(equality);
            clause.push(complement);
        }
        clause.push(conclusion);
        let mut current = candidate.add_rule_step(
            AletheRule::EqCongruent,
            clause.clone(),
            Vec::new(),
            Vec::new(),
        );

        // Distinct pivots only: two argument positions can share one premise
        // equality (`(= 0 0)` twice, say), and resolution removes every copy of
        // the complement at once.
        let mut residual = clause;
        let mut resolved: Vec<TermId> = Vec::with_capacity(premises.len());
        for &(equality, unit) in &premises {
            if resolved.contains(&equality) {
                continue;
            }
            resolved.push(equality);
            let complement = self.ctx.terms.mk_not_raw(equality);
            if !residual.contains(&complement) {
                return None;
            }
            residual.retain(|&literal| literal != complement);
            current = candidate.add_resolution(residual.clone(), equality, current, unit);
        }
        (residual == [conclusion]).then_some((conclusion, current))
    }

    /// Rewrite `term` by replacing every occurrence of a bound subject with its
    /// ground value, or `None` when the walk exceeds `budget` or meets a node
    /// shape (`ite`, quantifier, `let`) this reconstruction cannot transport.
    fn rewrite_with_ground_bindings(
        &mut self,
        term: TermId,
        bindings: &[GroundBinding],
        budget: &mut usize,
    ) -> Option<TermId> {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        if let Some(binding) = bindings.iter().find(|binding| binding.subject == term) {
            return Some(binding.value);
        }
        match self.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(..) => Some(term),
            TermData::App(symbol, args) => {
                let symbol = symbol.clone();
                let args: Vec<TermId> = args.clone();
                let sort = self.ctx.terms.sort(term).clone();
                let mut rewritten = Vec::with_capacity(args.len());
                for &arg in &args {
                    rewritten.push(self.rewrite_with_ground_bindings(arg, bindings, budget)?);
                }
                if rewritten == args {
                    return Some(term);
                }
                Some(self.ctx.terms.mk_app(symbol, rewritten, sort))
            }
            // `ite`, quantifiers and `let` are not `App` nodes, so neither
            // `eq_congruent` nor `eq_congruent_pred` can transport them. Fail
            // closed rather than rebuild a term the checker cannot follow.
            _ => None,
        }
    }

    /// Whether every leaf beneath `term` is a constant — the precondition for
    /// the checker's ground evaluator to have anything to decide.
    fn is_ground_for_substitution(terms: &TermStore, term: TermId) -> bool {
        const MAX_GROUND_VISITS: usize = 4096;
        let mut stack = vec![term];
        let mut visits = 0usize;
        while let Some(current) = stack.pop() {
            visits += 1;
            if visits > MAX_GROUND_VISITS {
                return false;
            }
            match terms.get(current) {
                TermData::Const(_) => {}
                TermData::App(_, args) => {
                    if args.is_empty() {
                        // A nullary application is a DECLARED symbol, i.e. a
                        // variable — not a ground value.
                        return false;
                    }
                    stack.extend(args.iter().copied());
                }
                _ => return false,
            }
        }
        true
    }

    /// Whether `term` is a leaf the substitution may replace: a declared
    /// nullary symbol or a variable, never a compound term.
    fn is_substitutable_leaf(terms: &TermStore, term: TermId) -> bool {
        match terms.get(term) {
            TermData::Var(..) => true,
            TermData::App(_, args) => args.is_empty(),
            _ => false,
        }
    }
}
