// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticated rebuilds for preprocessor-folded ground arithmetic
//! literals and their closed disjunctions.

use super::and_collapse::LinearAndSourceProvenance;
use super::*;

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
    pub(super) fn try_rebuild_false_collapse_from_originals(
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
            let expanded_let_provenance;
            let stripped = if matches!(stripped, FrontendTerm::Let(..)) {
                let source_surface =
                    crate::executor::proof_surface_syntax::format_frontend_term(stripped);
                match expand_surface_lets(stripped, &std::collections::HashMap::new()) {
                    Some(term) => {
                        expanded = term;
                        let stripped = strip_frontend_annotations(&expanded);
                        expanded_let_provenance =
                            self.raw_intern_surface(stripped).map(|expanded_root| {
                                LinearAndSourceProvenance::ExpandedLet {
                                    expanded_root,
                                    source_index: original_idx,
                                    source_surface,
                                }
                            });
                        stripped
                    }
                    None => continue,
                }
            } else {
                expanded_let_provenance = None;
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
                    // The DUAL of the `and` arm below. Every disjunct of a
                    // closed order-atom disjunction is refutable on its own by
                    // exactly the one-row `la_generic` the single-literal arm
                    // above already emits, so the whole disjunction is that
                    // obligation n times plus one `or` elimination.
                    "or" if operands.len() >= 2 => {
                        self.rebuild_ground_linear_or_collapse(proof, stripped)
                    }
                    "and" if operands.len() >= 2 => {
                        let authored_root = authored_originals.get(original_idx).and_then(
                            |(root, authored_parsed)| (authored_parsed == parsed).then_some(*root),
                        );
                        authored_root.is_some_and(|root| {
                            self.rebuild_complementary_and_collapse(proof, root, operands.len())
                        }) || match expanded_let_provenance {
                            None => self.rebuild_linear_and_collapse(
                                proof,
                                operands,
                                LinearAndSourceProvenance::IndexedApplication,
                            ),
                            Some(provenance) => {
                                self.rebuild_linear_and_collapse(proof, operands, provenance)
                            }
                        }
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

    /// Refute an authored ground linear DISJUNCTION whose every disjunct is
    /// self-false — the closed-constant range check
    /// `(or (< 2 0) (>= 2 32))` and its n-ary relatives.
    ///
    /// `rebuild_ground_linear_literal_collapse` already discharges ONE closed
    /// order atom with an independently re-verified one-row `la_generic`. A
    /// closed disjunction is n copies of exactly that obligation plus the
    /// `or` elimination that puts the disjuncts onto a clause, so nothing new
    /// is trusted here; only the assembly was missing. Before this arm the
    /// `or` head fell through to `_ => false`, the fold-to-`false` erasure
    /// ran, and the terminal `BvLiaTautology` fallback recorded the refutation
    /// as a step that PRINTS `hole` (`bv_lia_tautology` is not an Alethe rule
    /// name) — so a contradiction AY re-derives from constants alone shipped
    /// unchecked next to an atomic sibling that shipped checked.
    ///
    /// ```text
    /// (assume t0 (or (< 2 0) (>= 2 32)))
    /// (step t1 (cl (< 2 0) (>= 2 32)) :rule or :premises (t0))
    /// (step t2 (cl (not (< 2 0))) :rule la_generic :args (1))
    /// (step t3 (cl (>= 2 32)) :rule resolution :premises (t2 t1))
    /// (step t4 (cl (not (>= 2 32))) :rule la_generic :args (1))
    /// (step t5 (cl) :rule resolution :premises (t4 t3))
    /// ```
    ///
    /// Fail-closed exactly like the single-literal lane: a disjunct that is
    /// not a pure linear atom, or whose unit-weight row does not actually
    /// contradict, declines the WHOLE rebuild (a partial refutation over a
    /// subset of the disjuncts is a different and unproven claim), and the
    /// UNCHANGED strict checker plus the exporter's own premise-scope check
    /// are the only commit authority.
    fn rebuild_ground_linear_or_collapse(
        &mut self,
        proof: &mut Proof,
        surface: &FrontendTerm,
    ) -> bool {
        let Some(authored) = self.raw_intern_surface(surface) else {
            return false;
        };
        let TermData::App(Symbol::Named(head), disjuncts) = self.ctx.terms.get(authored) else {
            return false;
        };
        if head != "or" || disjuncts.len() < 2 {
            return false;
        }
        let disjuncts = disjuncts.clone();
        // carcara's `or` is POSITIONAL and the peel below removes exactly one
        // occurrence per step, so a repeated disjunct would leave the residual
        // clause out of step with the printed one. Decline instead.
        let mut distinct = disjuncts.clone();
        distinct.sort_unstable();
        distinct.dedup();
        if distinct.len() != disjuncts.len() {
            return false;
        }
        let Some(rows) = self.ground_linear_or_rows(&disjuncts) else {
            return false;
        };

        let mut rebuilt = Proof::new();
        let assume_id = rebuilt.add_assume(authored, None);
        let mut current = rebuilt.add_rule_step(
            AletheRule::Or,
            disjuncts.clone(),
            vec![assume_id],
            Vec::new(),
        );
        for (position, (&disjunct, (complement, farkas))) in disjuncts.iter().zip(rows).enumerate()
        {
            let lemma = rebuilt.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: vec![complement],
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let residual = disjuncts[position + 1..].to_vec();
            // `add_resolution(clause, pivot, c1, c2)` takes the premise
            // carrying the pivot's NEGATIVE occurrence first: that is the
            // lemma for a positive disjunct and the running clause for a
            // negated one.
            current = if matches!(self.ctx.terms.get(disjunct), TermData::Not(_)) {
                rebuilt.add_resolution(residual, disjunct, current, lemma)
            } else {
                rebuilt.add_resolution(residual, disjunct, lemma, current)
            };
        }

        if !self
            .check_proof_strict_with_datatypes(&rebuilt)
            .is_ok_and(|quality| quality.is_complete())
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

    /// One independently re-verified unit-weight Farkas row per disjunct:
    /// `(complement, coefficients)`. `None` as soon as any disjunct is not a
    /// pure linear atom that contradicts on its own — the same two checks
    /// (`la_generic`-strength verification plus a printable equality-sign
    /// orientation) the single-literal lane runs, so a row admitted here is
    /// one the strict checker re-derives below.
    fn ground_linear_or_rows(
        &mut self,
        disjuncts: &[TermId],
    ) -> Option<Vec<(TermId, FarkasAnnotation)>> {
        let mut rows = Vec::new();
        rows.try_reserve_exact(disjuncts.len()).ok()?;
        for &disjunct in disjuncts {
            if !is_pure_linear_arith_literal(&self.ctx.terms, disjunct) {
                return None;
            }
            let complement = complement_of(&mut self.ctx.terms, disjunct);
            let farkas = FarkasAnnotation::from_ints(&[1]);
            let literals = [match self.ctx.terms.get(disjunct) {
                TermData::Not(inner) => TheoryLit::new(*inner, false),
                _ => TheoryLit::new(disjunct, true),
            }];
            ay_core::proof_validation::verify_farkas_conflict_lits_linear(
                &self.ctx.terms,
                &literals,
                &farkas,
            )
            .ok()?;
            ay_core::proof_validation::resolve_equality_coefficient_signs(
                &self.ctx.terms,
                &literals,
                &farkas,
            )?;
            rows.push((complement, farkas));
        }
        Some(rows)
    }
}

#[cfg(test)]
mod or_collapse_tests {
    use ay_core::{
        AletheRule, FarkasAnnotation, Proof, ProofStep, TermData, TermId, TheoryLemmaKind,
    };

    /// The EXACT shape `rebuild_ground_linear_or_collapse` commits, rebuilt
    /// here from raw parts so a PLANTED one can be handed to the same checker.
    fn candidate(executor: &mut crate::Executor, root: TermId, disjuncts: &[TermId]) -> Proof {
        let mut proof = Proof::new();
        let assume_id = proof.add_assume(root, None);
        let mut current = proof.add_rule_step(
            AletheRule::Or,
            disjuncts.to_vec(),
            vec![assume_id],
            Vec::new(),
        );
        for (position, &disjunct) in disjuncts.iter().enumerate() {
            let complement = executor.ctx.terms.mk_not_raw(disjunct);
            let lemma = proof.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: vec![complement],
                farkas: Some(FarkasAnnotation::from_ints(&[1])),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let residual = disjuncts[position + 1..].to_vec();
            current = proof.add_resolution(residual, disjunct, lemma, current);
        }
        proof
    }

    fn disjuncts_of(executor: &crate::Executor, root: TermId) -> Vec<TermId> {
        match executor.ctx.terms.get(root) {
            TermData::App(_, arguments) => arguments.clone(),
            other => panic!("fixture root must be an `or` application, got {other:?}"),
        }
    }

    /// FALSIFY-ONCE. The lane's whole soundness argument is that every
    /// one-row `la_generic` it emits is RE-DERIVED by the strict checker
    /// rather than taken on the producer's word. Plant the byte-identical
    /// candidate over a SATISFIABLE disjunction — `(or (< 2 0) (>= 2 1))`,
    /// whose second disjunct is TRUE — and watch
    /// `check_proof_strict_with_datatypes` reject it. If this ever passes, the
    /// lane is a false-proof machine.
    ///
    /// Both states are asserted, because a rejection with no control proves
    /// only that the checker rejects something.
    #[test]
    fn a_planted_row_over_a_satisfiable_disjunct_is_rejected() {
        let commands = ay_frontend::parse(
            "(set-logic QF_LIA)\n(assert (or (< 2 0) (>= 2 1)))\n(assert (or (< 2 0) (>= 2 32)))",
        )
        .expect("fixture must parse");
        let mut executor = crate::Executor::new();
        executor
            .execute_all(&commands)
            .expect("fixture must elaborate");
        // Re-intern from the AUTHORED surface, exactly as the lane does:
        // `ctx.assertions` holds the post-fold window, where the refutable
        // root has already become the constant `false`.
        let parsed: Vec<_> = executor.ctx.assertions_parsed().to_vec();
        assert_eq!(parsed.len(), 2, "fixture precondition: two authored roots");
        let satisfiable = executor
            .raw_intern_surface(&parsed[0])
            .expect("the satisfiable root must re-intern");
        let refutable = executor
            .raw_intern_surface(&parsed[1])
            .expect("the refutable root must re-intern");
        // Authorize both re-interned roots as problem premises, which is the
        // scope the lane runs inside; otherwise the checker stops at
        // `UnauthorizedAssumption` before it ever reaches a row.
        executor.ctx.assertions = vec![satisfiable, refutable];
        let satisfiable_disjuncts = disjuncts_of(&executor, satisfiable);
        let refutable_disjuncts = disjuncts_of(&executor, refutable);

        let honest = candidate(&mut executor, refutable, &refutable_disjuncts);
        assert!(
            executor
                .check_proof_strict_with_datatypes(&honest)
                .is_ok_and(|quality| quality.is_complete()),
            "control: the same shape over a genuinely false disjunction must \
             CHECK, or this test proves nothing about the planted one"
        );

        let planted = candidate(&mut executor, satisfiable, &satisfiable_disjuncts);
        assert!(
            executor
                .check_proof_strict_with_datatypes(&planted)
                .is_err(),
            "a one-row `la_generic` claiming a SATISFIABLE disjunct is unsound; \
             the strict checker re-verifies the Farkas row and must reject it"
        );
    }
}
