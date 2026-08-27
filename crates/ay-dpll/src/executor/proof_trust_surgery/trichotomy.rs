// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer-trichotomy and ITE-lift planning.

use super::*;

impl Executor {
    /// Recognize a trust step's clause as an Int trichotomy lemma
    /// `(cl (or (= x y) S1 S2))` with a single `or`-split consumer, and
    /// pre-verify both `[1, 1]` strengthening bridges (fail-closed).
    pub(super) fn plan_trichotomy(
        &mut self,
        proof: &Proof,
        clause: &[TermId],
        consumers: &[usize],
        trust_idx: usize,
    ) -> Option<TrichotomyPlan> {
        if clause.len() != 1 {
            return None;
        }
        let TermData::App(Symbol::Named(name), disjuncts) = self.ctx.terms.get(clause[0]) else {
            return None;
        };
        if name != "or" || disjuncts.len() != 3 {
            return None;
        }
        let disjuncts = disjuncts.clone();
        // Exactly one equality disjunct over Int operands.
        let mut eq_pos: Option<usize> = None;
        for (i, &d) in disjuncts.iter().enumerate() {
            if let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(d) {
                if op == "=" && args.len() == 2 {
                    if eq_pos.is_some() {
                        return None;
                    }
                    eq_pos = Some(i);
                }
            }
        }
        let eq_pos = eq_pos?;
        let eq = disjuncts[eq_pos];
        let TermData::App(_, eq_args) = self.ctx.terms.get(eq) else {
            return None;
        };
        let (x, y) = (eq_args[0], eq_args[1]);
        if *self.ctx.terms.sort(x) != Sort::Int || *self.ctx.terms.sort(y) != Sort::Int {
            return None;
        }
        let mut strengthened = disjuncts
            .iter()
            .enumerate()
            .filter(|&(i, _)| i != eq_pos)
            .map(|(_, &d)| d);
        let (s1, s2) = (strengthened.next()?, strengthened.next()?);

        // The `la_disequality` split literals (raw operand order is the
        // rule's rigid shape; fail-closed on constant-fold surprises).
        let le_xy = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [x, y], Sort::Bool);
        let le_yx = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [y, x], Sort::Bool);
        for le in [le_xy, le_yx] {
            let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(le) else {
                return None;
            };
            if op != "<=" || args.len() != 2 {
                return None;
            }
        }
        let not_le_xy = self.ctx.terms.mk_not_raw(le_xy);
        let not_le_yx = self.ctx.terms.mk_not_raw(le_yx);
        let or_term =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [eq, not_le_xy, not_le_yx], Sort::Bool);

        // Pair each strengthened disjunct with the split literal that
        // implies it, VERIFYING the `[1, 1]` certificate both ways
        // (never pattern-match what a checker can decide).
        let (strong_from_yx, strong_from_xy) =
            if self.pair_lemma_valid(s1, le_yx) && self.pair_lemma_valid(s2, le_xy) {
                (s1, s2)
            } else if self.pair_lemma_valid(s2, le_yx) && self.pair_lemma_valid(s1, le_xy) {
                (s2, s1)
            } else {
                return None;
            };

        // Exactly one consumer: the `or` split of this trust step, whose
        // clause is the same 3-literal set the derivation reproduces.
        let mut uniq: Vec<usize> = consumers.to_vec();
        uniq.sort_unstable();
        uniq.dedup();
        if uniq.len() != 1 {
            return None;
        }
        let or_split_idx = uniq[0];
        let ProofStep::Step {
            rule: AletheRule::Or,
            clause: split_clause,
            premises,
            ..
        } = &proof.steps[or_split_idx]
        else {
            return None;
        };
        if premises.len() != 1 || premises[0].0 as usize != trust_idx {
            return None;
        }
        let mut want = vec![eq, strong_from_yx, strong_from_xy];
        let mut have = split_clause.clone();
        want.sort_unstable();
        have.sort_unstable();
        if want != have {
            return None;
        }

        Some(TrichotomyPlan {
            or_split_idx,
            eq,
            le_xy,
            le_yx,
            not_le_xy,
            not_le_yx,
            or_term,
            strong_from_yx,
            strong_from_xy,
        })
    }

    /// Recognize exact term-ITE lifting from an authored assertion and
    /// pre-verify both branch transfers as Farkas certificates.
    pub(super) fn plan_ite_lift(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<IteLiftPlan> {
        if clause.len() != 1 {
            return None;
        }
        let goal = clause[0];
        let TermData::Ite(cond, lifted_then, lifted_else) = *self.ctx.terms.get(goal) else {
            return None;
        };
        for (orig, parsed) in originals {
            let orig = *orig;
            if !source_index.contains(orig) {
                continue;
            }
            if !planning.spend_surface(orig, parsed) {
                return None;
            }
            // An authored assertion the cost model REFUSES to price is skipped,
            // not treated as budget exhaustion. Every binder is refused outright
            // (`canonical_term_work`'s `Forall`/`Exists`/`Let` arm), and a binder
            // can never SOURCE a ground arithmetic ITE lift anyway —
            // `term_ite_candidates_with_cond` does not descend into one — so the
            // skip costs the scan nothing. Aborting on it cost the whole scan:
            // on the `inc_some_list` dual-vocabulary obligation the 5th of 111
            // authored assertions is a `forall`, so the Shannon-lift leaf's own
            // source (`dn13`, the 15th) was never examined and a provable leaf
            // was exported as an unverified `trust` step.
            match planning.charge_operand(&self.ctx.terms, orig) {
                OperandCharge::Charged => {}
                OperandCharge::Unpriceable => continue,
                OperandCharge::Exhausted => return None,
            }
            // Collect the term-level ite subterms of `orig` that share the
            // lifted condition.
            let candidates = self.term_ite_candidates_with_cond(orig, cond);
            for (ite_term, u, v) in candidates {
                if !planning.spend_terms(&self.ctx.terms, &[orig, orig]) {
                    return None;
                }
                let then_subst = self.ctx.terms.substitute(orig, &[ite_term], &[u]);
                let else_subst = self.ctx.terms.substitute(orig, &[ite_term], &[v]);
                if then_subst != lifted_then || else_subst != lifted_else {
                    continue;
                }
                let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                    self.build_ite_lift_connectives(orig, cond, ite_term, u, v)
                else {
                    continue;
                };
                // Verify both transfer lemmas (fail-closed; never
                // pattern-match what a checker can decide).
                if !self.triple_lemma_valid(eq_then, orig, lifted_then)
                    || !self.triple_lemma_valid(eq_else, orig, lifted_else)
                {
                    continue;
                }
                return Some(IteLiftPlan {
                    guarded_then_or: false,
                    orig,
                    defining_source: None,
                    bound: None,
                    cond,
                    lifted_then,
                    lifted_else,
                    goal,
                    ite_term,
                    eq_then,
                    eq_else,
                    ite_def,
                    and_term,
                    intro_eq,
                    then_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1]),
                    else_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1]),
                });
            }
        }
        // Defined-equality variant: `(= d (ite c u v))` plus an authored
        // bound `P(d)` derives the two lifted branches through `ite_intro`.
        for (canonical, parsed) in originals {
            let canonical = *canonical;
            if !source_index.contains(canonical) {
                continue;
            }
            if !planning.spend_surface(canonical, parsed) {
                return None;
            }
            let stripped = strip_frontend_annotations(parsed);
            let FrontendTerm::App(op, sides) = stripped else {
                continue;
            };
            if op != "=" || sides.len() != 2 {
                continue;
            }
            for ite_side in [0usize, 1] {
                let ite_surface = strip_frontend_annotations(&sides[ite_side]);
                let def_surface = strip_frontend_annotations(&sides[1 - ite_side]);
                let FrontendTerm::App(iop, iargs) = ite_surface else {
                    continue;
                };
                if iop != "ite" || iargs.len() != 3 {
                    continue;
                }
                let (Some(c), Some(u), Some(v), Some(defined)) = (
                    self.ctx.elaborate_surface_subterm(&iargs[0]),
                    self.ctx.elaborate_surface_subterm(&iargs[1]),
                    self.ctx.elaborate_surface_subterm(&iargs[2]),
                    self.ctx.elaborate_surface_subterm(def_surface),
                ) else {
                    continue;
                };
                if c != cond {
                    continue;
                }
                let ite_term = self.ctx.terms.mk_ite(cond, u, v);
                if *self.ctx.terms.sort(ite_term) == Sort::Bool
                    || !matches!(
                        self.ctx.terms.get(ite_term),
                        TermData::Ite(ic, iu, iv) if *ic == cond && *iu == u && *iv == v
                    )
                {
                    continue;
                }
                // The defining equality, re-interned in SURFACE operand order
                // (fail-closed if interning folds it away from that shape).
                let ordered = if ite_side == 0 {
                    [ite_term, defined]
                } else {
                    [defined, ite_term]
                };
                let p_raw = self
                    .ctx
                    .terms
                    .mk_app(Symbol::named("="), ordered, Sort::Bool);
                if !matches!(
                    self.ctx.terms.get(p_raw),
                    TermData::App(Symbol::Named(eop), eargs)
                        if eop == "=" && eargs.as_slice() == ordered
                ) {
                    continue;
                }
                let Some(authored_raw) = self.raw_intern_surface(stripped) else {
                    continue;
                };
                if authored_raw != p_raw {
                    // The lift below treats `p_raw` as an authored premise.
                    // Nested folds inside the condition, either branch, or
                    // the defined side need their own derivation; a
                    // whole-term print override is not proof authority.
                    continue;
                }
                for &(bound, _) in originals {
                    if bound == canonical || !source_index.contains(bound) {
                        continue;
                    }
                    // Same distinction as the first loop: a binder-bearing
                    // authored assertion cannot be the substituted bound of a
                    // ground lift, so skip it instead of abandoning the scan.
                    // Charged twice — `substitute` runs once per branch below.
                    match planning.charge_operand(&self.ctx.terms, bound) {
                        OperandCharge::Charged => {}
                        OperandCharge::Unpriceable => continue,
                        OperandCharge::Exhausted => return None,
                    }
                    if !planning.spend_terms(&self.ctx.terms, &[bound]) {
                        return None;
                    }
                    let then_subst = self.ctx.terms.substitute(bound, &[defined], &[u]);
                    let else_subst = self.ctx.terms.substitute(bound, &[defined], &[v]);
                    if then_subst != lifted_then || else_subst != lifted_else {
                        continue;
                    }
                    let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                        self.build_ite_lift_connectives(p_raw, cond, ite_term, u, v)
                    else {
                        continue;
                    };
                    if !self.quad_lemma_valid(eq_then, p_raw, bound, lifted_then)
                        || !self.quad_lemma_valid(eq_else, p_raw, bound, lifted_else)
                    {
                        continue;
                    }
                    return Some(IteLiftPlan {
                        guarded_then_or: false,
                        orig: p_raw,
                        defining_source: Some(canonical),
                        bound: Some(bound),
                        cond,
                        lifted_then,
                        lifted_else,
                        goal,
                        ite_term,
                        eq_then,
                        eq_else,
                        ite_def,
                        and_term,
                        intro_eq,
                        then_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1, 1]),
                        else_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1, 1]),
                    });
                }
            }
        }
        self.plan_ite_lift_over_substituted_bound(originals, cond, lifted_then, lifted_else, goal)
    }

    /// Recognize the GUARDED THEN-PROJECTION of an exact term-ITE lift:
    /// a trust unit `(cl (or (not c) P[s/u]))` left by arithmetic-ITE
    /// clausification of an authored `P` containing the term-level
    /// `s = (ite c u v)` whose else-branch clause was trivially true and
    /// dropped (`(<= 0 (ite c X 0))` clausifies to the guarded then clause
    /// plus `(or c (<= 0 0))`, and the latter folds away). Only the then
    /// side exists in the target proof, so only the then transfer is
    /// verified and emitted, packed into the goal `or` by `or_neg` +
    /// `contraction`.
    pub(super) fn plan_ite_lift_guarded_then(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
        source_index: &OriginalSourceIndex,
        planning: &mut SurgeryPlanningBudget,
    ) -> Option<IteLiftPlan> {
        if clause.len() != 1 {
            return None;
        }
        let goal = clause[0];
        let TermData::App(Symbol::Named(op), disjuncts) = self.ctx.terms.get(goal) else {
            return None;
        };
        if op != "or" || disjuncts.len() != 2 {
            return None;
        }
        let (guard, lifted_then) = (disjuncts[0], disjuncts[1]);
        let TermData::Not(cond) = *self.ctx.terms.get(guard) else {
            return None;
        };
        // Unambiguous resolution pivots: the guard and the lifted branch must
        // be distinct atoms, and neither may be the goal itself.
        if !crate::executor::proof_trust_surgery_provenance::unique_atoms(
            &self.ctx.terms,
            &[guard, lifted_then],
        ) || lifted_then == goal
        {
            return None;
        }
        for (orig, parsed) in originals {
            let orig = *orig;
            if !source_index.contains(orig) {
                continue;
            }
            if !planning.spend_surface(orig, parsed) {
                return None;
            }
            // Same skip-vs-abort discipline as `plan_ite_lift`: an assertion
            // the cost model refuses to price cannot source this lift.
            match planning.charge_operand(&self.ctx.terms, orig) {
                OperandCharge::Charged => {}
                OperandCharge::Unpriceable => continue,
                OperandCharge::Exhausted => return None,
            }
            let candidates = self.term_ite_candidates_with_cond(orig, cond);
            for (ite_term, u, v) in candidates {
                if !planning.spend_terms(&self.ctx.terms, &[orig, orig]) {
                    return None;
                }
                let then_subst = self.ctx.terms.substitute(orig, &[ite_term], &[u]);
                if then_subst != lifted_then {
                    continue;
                }
                let else_subst = self.ctx.terms.substitute(orig, &[ite_term], &[v]);
                let Some((eq_then, eq_else, ite_def, and_term, intro_eq)) =
                    self.build_ite_lift_connectives(orig, cond, ite_term, u, v)
                else {
                    continue;
                };
                // Verify ONLY the then-side transfer lemma: the else branch
                // of the clausified source was trivially true (that is why
                // the preprocessor dropped its clause), so its substitution
                // typically folds to `true` and has no `la_generic` reading.
                // Nothing else-side is emitted or registered with the
                // retained-surface audit.
                if !self.triple_lemma_valid(eq_then, orig, then_subst) {
                    continue;
                }
                return Some(IteLiftPlan {
                    guarded_then_or: true,
                    orig,
                    defining_source: None,
                    bound: None,
                    cond,
                    lifted_then: then_subst,
                    lifted_else: else_subst,
                    goal,
                    ite_term,
                    eq_then,
                    eq_else,
                    ite_def,
                    and_term,
                    intro_eq,
                    then_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1]),
                    else_coeffs: FarkasAnnotation::from_ints(&[1, 1, 1]),
                });
            }
        }
        None
    }

    /// Build and shape-check the `ite_intro` derivation's connective terms
    /// for `orig` containing the term-level `ite_term = (ite cond u v)`.
    /// Fail-closed: `None` when any raw application does not intern with the
    /// exact expected shape.
    pub(in crate::executor::proof_repair) fn build_ite_lift_connectives(
        &mut self,
        orig: TermId,
        cond: TermId,
        ite_term: TermId,
        u: TermId,
        v: TermId,
    ) -> Option<(TermId, TermId, TermId, TermId, TermId)> {
        let eq_then = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [ite_term, u], Sort::Bool);
        let eq_else = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [ite_term, v], Sort::Bool);
        let eq_shape = |terms: &ay_core::TermStore, t: TermId, l: TermId, r: TermId| {
            matches!(
                terms.get(t),
                TermData::App(Symbol::Named(op), args)
                    if op == "=" && args.len() == 2 && args[0] == l && args[1] == r
            )
        };
        if !eq_shape(&self.ctx.terms, eq_then, ite_term, u)
            || !eq_shape(&self.ctx.terms, eq_else, ite_term, v)
        {
            return None;
        }
        let ite_def = self.ctx.terms.mk_ite(cond, eq_then, eq_else);
        if !matches!(
            self.ctx.terms.get(ite_def),
            TermData::Ite(c, a, b) if *c == cond && *a == eq_then && *b == eq_else
        ) {
            return None;
        }
        let and_term = self
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [orig, ite_def], Sort::Bool);
        if !matches!(
            self.ctx.terms.get(and_term),
            TermData::App(Symbol::Named(op), args)
                if op == "and" && args.len() == 2 && args[0] == orig && args[1] == ite_def
        ) {
            return None;
        }
        let intro_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [orig, and_term], Sort::Bool);
        if !eq_shape(&self.ctx.terms, intro_eq, orig, and_term) {
            return None;
        }
        Some((eq_then, eq_else, ite_def, and_term, intro_eq))
    }
}
