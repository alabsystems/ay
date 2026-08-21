// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Authenticated rebuilds for preprocessor-folded ground arithmetic literals.

/// Whether `literal` is a (possibly negated) binary linear-arithmetic atom.
///
/// This is deliberately narrower than the internal Farkas verifier: an
/// external `la_generic` checker reasons only about arithmetic syntax, so a
/// producer-side reconstruction must not smuggle an opaque Bool atom into a
/// certificate merely because the internal store can assign it a variable.
fn is_pure_linear_arith_literal(terms: &ay_core::TermStore, literal: TermId) -> bool {
    let atom = atom_of(terms, literal);
    match terms.get(atom) {
        TermData::App(Symbol::Named(op), args)
            if matches!(op.as_str(), "=" | "<" | "<=" | ">" | ">=") && args.len() == 2 =>
        {
            terms.sort(args[0]) == terms.sort(args[1])
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                && args
                    .iter()
                    .all(|&arg| term_is_pure_linear_arith(terms, arg))
        }
        _ => false,
    }
}

impl Executor {
    /// Select a checked rebuild from the exact authored surface shape.
    ///
    /// The collapse assume holds a folded canonical term. Parsed syntax is used
    /// only to choose a derivation after its aligned canonical root matches that
    /// term. `let` sugar is expanded capture-safely; any failed expansion or
    /// unrecognized shape leaves the original proof byte-identical.
    fn try_rebuild_false_collapse_from_originals(
        &mut self,
        proof: &mut Proof,
        folded: TermId,
        originals: &[(TermId, FrontendTerm)],
        authored_originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        for (original_idx, (canonical, parsed)) in originals.iter().enumerate() {
            if *canonical != folded {
                continue;
            }
            let stripped = strip_frontend_annotations(parsed);
            // CAV09-family assertions wrap the conjunction in `let` sugar.
            // The expanded form is accepted by external checkers that compare
            // premises modulo let expansion.
            let expanded;
            let stripped = if matches!(stripped, FrontendTerm::Let(..)) {
                match expand_surface_lets(stripped, &std::collections::HashMap::new()) {
                    Some(term) => {
                        expanded = term;
                        strip_frontend_annotations(&expanded)
                    }
                    None => continue,
                }
            } else {
                stripped
            };
            let FrontendTerm::App(head, operands) = stripped else {
                continue;
            };
            let rebuilt =
                match head.as_str() {
                    "distinct" if operands.len() >= 2 => {
                        self.rebuild_duplicate_distinct_collapse(proof, operands)
                    }
                    "=" | "<" | "<=" | ">" | ">=" if operands.len() == 2 => {
                        self.rebuild_ground_linear_literal_collapse(proof, stripped)
                    }
                    "not" if operands.len() == 1 => {
                        let inner = strip_frontend_annotations(&operands[0]);
                        matches!(
                            inner,
                            FrontendTerm::App(op, args)
                                if matches!(op.as_str(), "=" | "<" | "<=" | ">" | ">=")
                                    && args.len() == 2
                        ) && self.rebuild_ground_linear_literal_collapse(proof, stripped)
                    }
                    "and" if operands.len() >= 2 => {
                        let authored_root = authored_originals.get(original_idx).and_then(
                            |(root, authored_parsed)| (authored_parsed == parsed).then_some(*root),
                        );
                        authored_root.is_some_and(|root| {
                            self.rebuild_complementary_and_collapse(proof, root, operands.len())
                        }) || self.rebuild_linear_and_collapse(proof, operands)
                    }
                    _ => false,
                };
            if rebuilt {
                return true;
            }
        }
        false
    }

    /// Derive the complement of an exact authored ground linear literal.
    ///
    /// A printable, independently re-verified one-row Farkas lemma is
    /// preferred. A true ground equality instead uses the primitive `evaluate`
    /// bridge because its disequality complement has no one-row Alethe Farkas
    /// encoding. Raw spelling is load-bearing for premise authority and
    /// external matching: elaboration has already folded the live assertion to
    /// `false` by the time this repair runs.
    fn rebuild_ground_linear_literal_collapse(
        &mut self,
        proof: &mut Proof,
        surface: &FrontendTerm,
    ) -> bool {
        let Some(authored) = self.raw_intern_surface(surface) else {
            return false;
        };
        if !is_pure_linear_arith_literal(&self.ctx.terms, authored) {
            return false;
        }
        let complement = complement_of(&mut self.ctx.terms, authored);
        let farkas = FarkasAnnotation::from_ints(&[1]);
        let literals = [match self.ctx.terms.get(authored) {
            TermData::Not(inner) => TheoryLit::new(*inner, false),
            _ => TheoryLit::new(authored, true),
        }];
        let mut rebuilt = Proof::new();
        let assume_id = rebuilt.add_assume(authored, None);
        let lemma = if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &literals,
            &farkas,
        )
        .is_ok()
            && ay_core::proof_validation::resolve_equality_coefficient_signs(
                &self.ctx.terms,
                &literals,
                &farkas,
            )
            .is_some()
        {
            rebuilt.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: vec![complement],
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            })
        } else if ay_proof::recognize_ground_evaluate(&self.ctx.terms, complement) {
            // `evaluate` concludes an equality to a concrete value. Derive the
            // true complement from `(= complement true)` using primitive Alethe
            // rules, exactly as the proof tracker does for a folded instance.
            let truth = self.ctx.terms.true_term();
            let evaluation =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [complement, truth], Sort::Bool);
            let evaluated = rebuilt.add_rule_step(
                AletheRule::Evaluate,
                vec![evaluation],
                Vec::new(),
                Vec::new(),
            );
            let not_evaluation = self.ctx.terms.mk_not_raw(evaluation);
            let not_truth = self.ctx.terms.mk_not_raw(truth);
            let equivalence = rebuilt.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_evaluation, complement, not_truth],
                Vec::new(),
                Vec::new(),
            );
            let truth_unit =
                rebuilt.add_rule_step(AletheRule::True, vec![truth], Vec::new(), Vec::new());
            let implication = rebuilt.add_resolution(
                vec![not_evaluation, complement],
                truth,
                equivalence,
                truth_unit,
            );
            rebuilt.add_resolution(vec![complement], evaluation, evaluated, implication)
        } else {
            return false;
        };
        rebuilt.add_resolution(Vec::new(), authored, lemma, assume_id);

        if self.check_proof_strict_with_datatypes(&rebuilt).is_err()
            || ay_proof::validate_reachable_assumes_in_problem_scope(&rebuilt, &[authored]).is_err()
        {
            return false;
        }
        *proof = rebuilt;
        self.record_rebuilt_authored_proof_premise(authored);
        // Raw-interned nodes must not be printed through canonical overrides.
        self.last_proof_term_overrides = None;
        true
    }
}
