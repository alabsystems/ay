// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Congruence and authored-premise collapse repair.

use super::*;

impl Executor {
    /// Consumed-assertions collapse whose contradiction is pure EUF
    /// CONGRUENCE (`(= a b)` together with `(not (= (f .. a ..) (f .. b ..)))`):
    /// the preprocessor rewrote one side into the other, folded the result,
    /// and the exported proof is the bare `(cl false) :rule trust`.
    ///
    /// Re-prove it from the ORIGINAL assertions with a single `cong` step —
    /// a first-class Alethe rule that AY's own strict checker validates
    /// (`validate_cong`) and that Carcara checks natively — closed by one
    /// resolution against the assumed disequality:
    ///
    /// ```text
    /// (assume h0 (= a b))
    /// (assume h1 (not (= (f .. a ..) (f .. b ..))))
    /// (step  c  (cl (= (f .. a ..) (f .. b ..))) :rule cong :premises (h0))
    /// (step  r  (cl) :rule resolution :premises (c h1))
    /// ```
    ///
    /// FAIL-CLOSED CONDITIONS (any one keeps the honest `trust` step):
    ///  - the assertion set is not exactly one disequality plus one or more
    ///    equalities (an unused original could be the one that mattered, and
    ///    the rebuilt proof must not claim a refutation it did not use);
    ///  - the two disequality sides are not applications of the SAME symbol
    ///    with the same arity;
    ///  - some differing argument position has no equality original for
    ///    exactly that unordered pair, or some equality original is left
    ///    over (`cong` requires every premise to be consumed);
    ///  - re-interning any reconstructed term does not reproduce it RAW (a
    ///    folding interner would make the derivation not match the premise).
    ///
    /// This is congruence over the ORIGINAL assertions only. It never appeals
    /// to array extensionality, so `(= a b)` between arrays is used exactly
    /// as the congruence premise for a shared argument position — the same
    /// obligation Carcara's `cong` checks.
    pub(super) fn rebuild_congruence_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        if originals.len() < 2 {
            return false;
        }
        // Partition the originals: exactly one disequality conclusion, every
        // other one an equality that must end up used as a `cong` premise.
        let mut disequality: Option<(TermId, TermId)> = None;
        let mut equalities: Vec<(TermId, TermId)> = Vec::with_capacity(originals.len());
        for (_, parsed) in originals {
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(head, operands) = stripped else {
                return false;
            };
            let (is_disequality, sides) = match (head.as_str(), operands.len()) {
                ("=", 2) => (false, &operands[..]),
                ("distinct", 2) => (true, &operands[..]),
                ("not", 1) => match strip_frontend_annotations(&operands[0]) {
                    FrontendTerm::App(inner_head, inner_operands)
                        if inner_head == "=" && inner_operands.len() == 2 =>
                    {
                        (true, &inner_operands[..])
                    }
                    _ => return false,
                },
                _ => return false,
            };
            let (Some(lhs), Some(rhs)) = (
                self.ctx.elaborate_surface_subterm(&sides[0]),
                self.ctx.elaborate_surface_subterm(&sides[1]),
            ) else {
                return false;
            };
            if self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
                return false;
            }
            if is_disequality {
                if disequality.is_some() {
                    return false;
                }
                disequality = Some((lhs, rhs));
            } else {
                equalities.push((lhs, rhs));
            }
        }
        let (Some((conc_lhs, conc_rhs)), false) = (disequality, equalities.is_empty()) else {
            return false;
        };

        // The two sides must be the same application, differing only at
        // positions an original equality covers — and every equality must be
        // consumed, which is exactly what `validate_cong` re-checks.
        let (TermData::App(lhs_sym, lhs_args), TermData::App(rhs_sym, rhs_args)) = (
            self.ctx.terms.get(conc_lhs).clone(),
            self.ctx.terms.get(conc_rhs).clone(),
        ) else {
            return false;
        };
        if lhs_sym != rhs_sym || lhs_args.len() != rhs_args.len() {
            return false;
        }
        let mut used = vec![false; equalities.len()];
        for (left, right) in lhs_args.iter().zip(rhs_args.iter()) {
            if left == right {
                continue;
            }
            let Some(position) = equalities.iter().enumerate().position(|(k, &(a, b))| {
                !used[k] && ((a == *left && b == *right) || (a == *right && b == *left))
            }) else {
                return false;
            };
            used[position] = true;
        }
        if used.iter().any(|consumed| !consumed) {
            return false;
        }

        // Re-intern every premise RAW; a folding interner would leave the
        // derivation referring to terms the printed premises do not carry.
        let mut premises: Vec<TermId> = Vec::with_capacity(equalities.len());
        for &(lhs, rhs) in &equalities {
            let eq = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(eq),
                TermData::App(Symbol::Named(op), a)
                    if op == "=" && a.len() == 2 && a[0] == lhs && a[1] == rhs
            ) {
                return false;
            }
            premises.push(eq);
        }
        let conclusion =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [conc_lhs, conc_rhs], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(conclusion),
            TermData::App(Symbol::Named(op), a)
                if op == "=" && a.len() == 2 && a[0] == conc_lhs && a[1] == conc_rhs
        ) {
            return false;
        }
        let negated = self.ctx.terms.mk_not_raw(conclusion);
        if negated == conclusion {
            return false;
        }

        let mut new_proof = Proof::new();
        let mut premise_ids: Vec<ProofId> = Vec::with_capacity(premises.len());
        for &eq in &premises {
            premise_ids.push(new_proof.add_assume(eq, None));
        }
        let negated_id = new_proof.add_assume(negated, None);
        let cong =
            new_proof.add_rule_step(AletheRule::Cong, vec![conclusion], premise_ids, Vec::new());
        new_proof.add_resolution(Vec::new(), conclusion, cong, negated_id);
        *proof = new_proof;
        for &eq in &premises {
            self.record_rebuilt_authored_proof_premise(eq);
        }
        self.record_rebuilt_authored_proof_premise(negated);
        true
    }

    /// Consumed-assertions collapse (`x = 1 ∧ y = 2 ∧ x + y = 4`): the
    /// preprocessor substituted the assertions into each other, folded the
    /// contradiction, and the exported proof is the bare `(cl false) :rule
    /// trust` — no assume, no derivation. Re-prove from the ORIGINAL
    /// arithmetic-equality assertions: a single `la_generic` lemma over
    /// their negations, coefficients SYNTHESIZED by the LRA solver and
    /// independently re-verified (rational check + printable sign
    /// orientation, both fail-closed), closed by one resolution per assumed
    /// equality. Any non-equality original or failed certificate keeps the
    /// honest trust step.
    /// Last-resort Shape-C repair: BIND THE PREMISES even when the refutation
    /// itself cannot be certified (#dt-premise-binding).
    ///
    /// Shape C is "the preprocessor consumed the assertions entirely", leaving
    /// the bare `(cl false)` with NO assume and NO derivation. The two rebuilds
    /// above re-prove such a collapse for arithmetic and congruence. A DATATYPE
    /// collapse has no such rebuild and cannot get one: Alethe defines no
    /// datatype rules, carcara implements none (181 rules, zero datatype), and
    /// cvc5 itself refuses to emit Alethe for datatypes. So the refutation step
    /// stays an unproved `hole`.
    ///
    /// But an unproved step is not the worst property of the exported artefact.
    /// A bare `(cl false) :rule hole` mentions NOTHING from the problem, so it
    /// checks IDENTICALLY AGAINST ANY INPUT FILE — it is not a weak proof of
    /// this instance, it is not a proof of anything. This repair fixes exactly
    /// that, without inventing a rule:
    ///
    /// ```text
    /// (assume a0 A0) ... (assume aN AN)          <- must match problem premises
    /// (step  t0 (cl (not A0) ... (not AN)) :rule hole)
    /// (step  t1 (cl) :rule th_resolution ...)    <- CHECKED
    /// ```
    ///
    /// A checker now verifies (a) every assume is a premise OF THIS PROBLEM,
    /// and (b) the contradiction genuinely follows from the hole's clause plus
    /// those premises. The hole also states its own content — "this premise set
    /// is jointly unsatisfiable" — instead of "false, trust me", so the trusted
    /// surface is one explicit clause a human can audit and a future rule can
    /// discharge.
    ///
    /// SOUNDNESS: the emitted clause is the negation of the conjunction of the
    /// problem's own assertions, which is exactly the claim "these are jointly
    /// unsat" — the claim the solver already made by answering `unsat`. No new
    /// assertion is introduced and no gate is relaxed; `terminal_trust.rs`
    /// counts the `hole` exactly as it counted the `trust`, so nothing that
    /// rejected the old proof accepts this one. Fail-closed: any original that
    /// does not elaborate to a Bool-sorted term leaves the proof unchanged.
    pub(super) fn rebuild_premise_binding_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        if originals.is_empty() {
            return false;
        }
        // Elaborate every original assertion. Totality is required: binding a
        // SUBSET would claim a smaller premise set refutes the instance, which
        // the solver has not established.
        let mut premises: Vec<TermId> = Vec::with_capacity(originals.len());
        for (_, parsed) in originals {
            let stripped = strip_frontend_annotations(parsed);
            let Some(t) = self.ctx.elaborate_surface_subterm(stripped) else {
                return false;
            };
            if !matches!(self.ctx.terms.sort(t), Sort::Bool) {
                return false;
            }
            premises.push(t);
        }
        // Full (not just adjacent) dedup. `Vec::dedup` drops only CONSECUTIVE
        // repeats, so a file that asserts the same formula twice non-adjacently
        // used to bind it twice — harmless for the claim (the conjunction is
        // unchanged, so totality still holds) but it makes the closing
        // resolution ambiguous: the second copy of `A` has no `(not A)` left to
        // resolve against. Keep the first occurrence, in assertion order.
        let mut seen: HashSet<TermId> = HashSet::default();
        premises.retain(|&p| seen.insert(p));
        if premises.is_empty() {
            return false;
        }

        let clause: Vec<TermId> = premises
            .iter()
            .map(|&p| self.ctx.terms.mk_not_raw(p))
            .collect();

        let mut new_proof = Proof::new();
        let assume_ids: Vec<ProofId> = premises
            .iter()
            .map(|&p| new_proof.add_assume(p, None))
            .collect();
        // Unproved by construction — prints as `hole`, the honest encoding for
        // a step no checker can discharge. NOT a certified lemma.
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "DT".to_string(),
            clause: clause.clone(),
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        });
        // ONE n-ary resolution, not a binary chain (#dt-premise-binding).
        //
        // This closed as `for i in 0..n { resolve(clause[i+1..], premises[i]) }`
        // — n binary steps, step i printing the n-i literals it has left. That
        // is TRIANGULAR text. Measured on the file that motivated the rebuild,
        // QF_DT/20210312-Bouvier/vlsat3_b14.smt2 (n = 2,986): 105.6 MB of
        // `.alethe`, 105.5 MB of it resolution steps whose lines decayed
        // 75,252 → 61,678 → 36,896 → … → 83 chars. The by-default sibling
        // emission is budgeted at 64 MiB of work (`executor/proof.rs`), so that
        // document was not a big proof — it was NO PROOF: emission aborted with
        // "work budget exhausted after 3502 steps" and the file was never
        // written.
        //
        // Alethe `resolution`/`th_resolution` are n-ary, so the whole chain is
        // one step whose premises are the lemma followed by every assume. Same
        // claim, same premises, same `hole`: 193,103 bytes (547x smaller),
        // inside the default budget, carcara 1.1.0 verdict `holey` in 0.01 s —
        // `holey` being the best achievable here, as Alethe defines no
        // datatype rules.
        // The order (lemma first, then assumes in assertion order) is the order
        // the checker folds in: the accumulator starts as the hole's clause
        // `[(not A0) … (not An)]` and each assume `Ai` cancels its own literal,
        // ending empty.
        let mut chain: Vec<ProofId> = Vec::with_capacity(assume_ids.len() + 1);
        chain.push(lemma);
        chain.extend_from_slice(&assume_ids);
        // Alethe requires >= 2 premises on a resolution (carcara: "expected at
        // least 2 premises, got 1"). Lemma + >= 1 assume always satisfies it,
        // but check rather than assume: a one-premise step would be rejected
        // outright, i.e. no proof, which is worse than keeping the trust stub.
        if chain.len() < 2 {
            return false;
        }
        new_proof.add_rule_step(AletheRule::ThResolution, Vec::new(), chain, Vec::new());
        *proof = new_proof;
        true
    }

    pub(super) fn rebuild_consumed_equalities_collapse(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        // Every original must be a re-internable arithmetic equality (the
        // lemma's premises must cover the WHOLE assertion set: a dropped
        // non-equality premise could be the one that mattered — though any
        // certified subset would still be sound, requiring totality keeps
        // the rebuilt proof honest about what refuted the instance).
        let mut eqs: Vec<TermId> = Vec::with_capacity(originals.len());
        for (_, parsed) in originals {
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(head, operands) = stripped else {
                return false;
            };
            if head != "=" || operands.len() != 2 {
                return false;
            }
            let (Some(lhs), Some(rhs)) = (
                self.ctx.elaborate_surface_subterm(&operands[0]),
                self.ctx.elaborate_surface_subterm(&operands[1]),
            ) else {
                return false;
            };
            if !matches!(self.ctx.terms.sort(lhs), Sort::Int | Sort::Real)
                || self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs)
            {
                return false;
            }
            let eq = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
            if !matches!(
                self.ctx.terms.get(eq),
                TermData::App(Symbol::Named(op), a) if op == "=" && a.len() == 2 && a[0] == lhs && a[1] == rhs
            ) {
                return false;
            }
            // External `la_generic` evaluates the combination syntactically:
            // impure atoms (UF/array applications) are out of scope.
            if !equality_is_pure_linear_arith(&self.ctx.terms, eq) {
                return false;
            }
            if !eqs.contains(&eq) {
                eqs.push(eq);
            }
        }
        if eqs.len() < 2 {
            return false;
        }
        let clause: Vec<TermId> = eqs.iter().map(|&e| self.ctx.terms.mk_not_raw(e)).collect();
        // Synthesize the certificate, then independently re-verify it and
        // require a printable equality-sign orientation (fail-closed).
        let mut farkas: Option<FarkasAnnotation> = None;
        let mut kind = TheoryLemmaKind::Generic;
        if !proof_farkas::try_lra_farkas_reconstruction(
            &self.ctx.terms,
            &clause,
            &mut farkas,
            &mut kind,
        ) {
            return false;
        }
        let Some(farkas) = farkas else {
            return false;
        };
        let conflict: Vec<TheoryLit> = eqs.iter().map(|&e| TheoryLit::new(e, true)).collect();
        if ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_err()
        {
            return false;
        }
        if ay_core::proof_validation::resolve_equality_coefficient_signs(
            &self.ctx.terms,
            &conflict,
            &farkas,
        )
        .is_none()
        {
            return false;
        }
        let mut new_proof = Proof::new();
        let assume_ids: Vec<ProofId> = eqs.iter().map(|&e| new_proof.add_assume(e, None)).collect();
        // Rationally certified: `la_generic`, fully checked externally.
        let lemma = new_proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: clause.clone(),
            farkas: Some(farkas),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });
        let mut current = lemma;
        for (i, (&eq, &aid)) in eqs.iter().zip(assume_ids.iter()).enumerate() {
            let remaining: Vec<TermId> = clause[i + 1..].to_vec();
            current = new_proof.add_resolution(remaining, eq, current, aid);
        }
        *proof = new_proof;
        true
    }
}
