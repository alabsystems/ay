// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fact classification for the arithmetic-ITE seeded clause database:
//! conjunction flattening, root-`assume` authentication, and the dispatch
//! into the checked emission lanes.

use ay_core::term::TermData as Td;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId};

use super::{
    usable_atom, ArithIteSeeding, RootAuthentication, MAX_OR_DISTRIBUTION_CHOICES,
    MAX_OR_DISTRIBUTION_CLAUSES, MAX_SEED_DEPTH,
};
use crate::executor::proof_trust_surgery_provenance::{
    immediate_surface_parts_match, surface_arithmetic_ite_matches, surface_or_decomposition_matches,
};
use crate::executor::Executor;

impl Executor {
    /// Classify one fact — an authored root (`unit == None`, which must
    /// authenticate against the authored surface before it is assumed) or a
    /// conjunct already derived as the unit clause `unit` — and seed the
    /// clause(s) it contributes. Unusable or unauthenticated facts are
    /// skipped, never fatal; `false` aborts the whole attempt (a provenance
    /// emission failed after planning).
    pub(super) fn seed_fact_clauses(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        auth: &mut RootAuthentication<'_>,
        fact: TermId,
        unit: Option<ProofId>,
        depth: usize,
    ) -> bool {
        if !seeding.charge() || depth > MAX_SEED_DEPTH {
            return true;
        }
        if !matches!(self.ctx.terms.sort(fact), Sort::Bool) {
            return true;
        }

        // Top-level conjunction: derive each conjunct as its own unit clause
        // (`and_pos` ⊢ `(cl (not (and …)) tᵢ)`, resolved against the unit) and
        // recurse. The deductive-checks consumer asserts its whole obligation as ONE
        // `(and …)`, so without this the pass never sees the ITEs at all.
        if let Td::App(Symbol::Named(name), args) = self.ctx.terms.get(fact) {
            if name == "and" && !args.is_empty() {
                let conjuncts = args.clone();
                // An authored conjunction may only be assumed when it
                // decomposes exactly as the parsed original spells it:
                // `and_pos` is positional, so a reordered or flattened surface
                // would print a different rule shape than the authored text.
                if unit.is_none() && !self.and_root_matches_authored_surface(auth, fact, &conjuncts)
                {
                    return true;
                }
                let unit = unit.unwrap_or_else(|| seeding.assume_once(candidate, fact));
                let not_fact = self.ctx.terms.mk_not_raw(fact);
                for (index, &conjunct) in conjuncts.iter().enumerate() {
                    let Ok(position) = u32::try_from(index) else {
                        continue;
                    };
                    if !seeding.charge() {
                        return true;
                    }
                    let and_pos = candidate.add_rule_step(
                        AletheRule::AndPos(position),
                        vec![not_fact, conjunct],
                        Vec::new(),
                        vec![fact],
                    );
                    let conjunct_unit =
                        candidate.add_resolution(vec![conjunct], fact, and_pos, unit);
                    if !self.seed_fact_clauses(
                        seeding,
                        candidate,
                        auth,
                        conjunct,
                        Some(conjunct_unit),
                        depth + 1,
                    ) {
                        return false;
                    }
                }
                return true;
            }
        }

        // Formula-level ITE tree: peel into path clauses. An authored ITE
        // root must first authenticate — directly, or via a provenance lift.
        if matches!(self.ctx.terms.get(fact), Td::Ite(..)) {
            return match unit {
                Some(unit) => {
                    self.seed_ite_path_clauses(seeding, candidate, fact, unit);
                    true
                }
                None => self.seed_authenticated_ite_root(seeding, candidate, auth, fact),
            };
        }

        // A Bool-sorted binary `=` is an IFF, not an atom: seed BOTH its
        // implications. Without this it interns as one opaque SAT variable and
        // a case split needing either direction stalls. ADDITIVE — the flat
        // lane below still seeds that opaque literal, so no clause this pass
        // used to seed is lost.
        self.seed_boolean_equivalence_fact(seeding, candidate, fact, unit);

        self.seed_flat_clause_fact(seeding, candidate, auth, fact, unit);
        true
    }

    /// Seed a Bool-sorted binary equality — an IFF between two propositional
    /// atoms, NOT a linear-arithmetic atom — as its two implication clauses:
    ///
    /// ```text
    /// equiv_pos2 ⊢ (cl (not (= a b)) (not a) b)   resolve on (= a b) → (cl (not a) b)
    /// equiv_pos1 ⊢ (cl (not (= a b)) a (not b))   resolve on (= a b) → (cl a (not b))
    /// ```
    ///
    /// `usable_atom` accepts a binary `=` whatever its operand sort, so
    /// `(= b (< i 8))` used to intern as ONE opaque Boolean variable: the
    /// theory atom `(< i 8)` never reached the LRA oracle and neither
    /// implication was available to the closer, so a refutation that needs
    /// both polarities (the deductive-checks contract panic-freedom VC — a `bool`
    /// temporary bound to a comparison, then case-split) stalled and the
    /// `trust` closer survived. Both rules are premise-free tautologies the
    /// strict checker re-derives positionally from the equality itself
    /// (`validate_equiv_pos1`/`validate_equiv_pos2`), and the ONLY `assume`
    /// this lane can take is the one the flat lane would have taken for the
    /// very same fact — no new assumption enters the candidate, so the root
    /// authentication story is unchanged.
    ///
    /// Seeds NOTHING and returns quietly on any shape it cannot derive — the
    /// flat lane still seeds the opaque literal exactly as before, so this is
    /// purely additive.
    fn seed_boolean_equivalence_fact(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        fact: TermId,
        unit: Option<ProofId>,
    ) {
        let Td::App(Symbol::Named(name), args) = self.ctx.terms.get(fact) else {
            return;
        };
        if name != "=" || args.len() != 2 {
            return;
        }
        let (lhs, rhs) = (args[0], args[1]);
        // Bool-sorted operands only: an Int/Real `=` is a genuine linear atom
        // and belongs to the flat lane (and to `la_disequality`).
        if !matches!(self.ctx.terms.sort(lhs), Sort::Bool)
            || !matches!(self.ctx.terms.sort(rhs), Sort::Bool)
        {
            return;
        }
        // Both sides must be POSITIVE usable atoms, exactly as the
        // single-level ITE lane demands of its condition: the seeded clause
        // literals must map back through `lit_to_term` to these very terms,
        // and `mk_not_raw` must produce a single-negation literal.
        //
        // CORRECTED (adversarial review measured it): an earlier note here said
        // "a term store collapses `(not (not x))`". It does NOT — `mk_not_raw`
        // (ay-core term/boolean.rs) interns `TermData::Not(arg)` unconditionally,
        // with no double-negation folding. The gate is still exactly right, but
        // the reason is the opposite one: because there is no folding, a NEGATIVE
        // operand would yield the distinct term `(not (not x))`, which is not the
        // literal the emitted clause carries, so the positional re-derivation in
        // the strict checker would not line up. Requiring positive atoms keeps
        // the emitted literal and the term identical.
        let (Some((lhs_atom, true)), Some((rhs_atom, true))) = (
            usable_atom(&self.ctx.terms, lhs),
            usable_atom(&self.ctx.terms, rhs),
        ) else {
            return;
        };
        if lhs_atom != lhs || rhs_atom != rhs {
            return;
        }
        if !seeding.charge() {
            return;
        }
        let not_eq = self.ctx.terms.mk_not_raw(fact);
        let not_lhs = self.ctx.terms.mk_not_raw(lhs);
        let not_rhs = self.ctx.terms.mk_not_raw(rhs);
        let (Some(sat_forward), Some(sat_backward)) = (
            seeding.sat_clause(&self.ctx.terms, &[not_lhs, rhs]),
            seeding.sat_clause(&self.ctx.terms, &[lhs, not_rhs]),
        ) else {
            return;
        };
        let unit = unit.unwrap_or_else(|| seeding.assume_once(candidate, fact));
        // equiv_pos2 ⊢ `(cl (not (= a b)) (not a) b)`.
        let equiv_pos2 = candidate.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_eq, not_lhs, rhs],
            Vec::new(),
            Vec::new(),
        );
        let forward = candidate.add_resolution(vec![not_lhs, rhs], fact, equiv_pos2, unit);
        // equiv_pos1 ⊢ `(cl (not (= a b)) a (not b))`.
        let equiv_pos1 = candidate.add_rule_step(
            AletheRule::EquivPos1,
            vec![not_eq, lhs, not_rhs],
            Vec::new(),
            Vec::new(),
        );
        let backward = candidate.add_resolution(vec![lhs, not_rhs], fact, equiv_pos1, unit);
        seeding.clause_versions.push((sat_forward, forward));
        seeding.clause_versions.push((sat_backward, backward));
    }

    /// Seed a unit literal or flat `(or …)` clause of usable atoms, plus the
    /// `la_disequality` bound split for a refuted arithmetic equality.
    fn seed_flat_clause_fact(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        auth: &RootAuthentication<'_>,
        fact: TermId,
        unit: Option<ProofId>,
    ) {
        let lit_terms: Vec<TermId> = match self.ctx.terms.get(fact) {
            Td::App(Symbol::Named(name), args) if name == "or" && args.len() >= 2 => {
                let args = args.clone();
                // An authored `or` root is seeded only when the parsed
                // original decomposes into exactly these disjuncts (the
                // printed `or` step is positional over the authored surface)
                // — or, in native mode, when the root IS an original-stack
                // assertion, whose canonical args are that decomposition.
                if unit.is_none() {
                    match auth.native_root_identity(fact) {
                        Some(false) => return,
                        Some(true) => {}
                        None => {
                            let Some((_, parsed)) = auth.source_index.get(auth.originals, fact)
                            else {
                                return;
                            };
                            if !surface_or_decomposition_matches(&mut self.ctx, parsed, &args) {
                                return;
                            }
                        }
                    }
                }
                args
            }
            _ => vec![fact],
        };
        // A disjunct that is itself a conjunction is not a usable atom, so the
        // whole clause used to be dropped. Distribute instead — checked, and
        // bounded by the cross-product budget.
        if lit_terms.len() >= 2
            && lit_terms
                .iter()
                .any(|&disjunct| self.conjunction_parts(disjunct).is_some())
        {
            self.seed_or_conjunct_distribution(seeding, candidate, fact, &lit_terms, unit);
            return;
        }
        let Some(sat) = seeding.sat_clause(&self.ctx.terms, &lit_terms) else {
            return;
        };
        let unit = unit.unwrap_or_else(|| seeding.assume_once(candidate, fact));
        let proof_id = if lit_terms.len() == 1 {
            unit
        } else {
            candidate.add_step(ProofStep::Step {
                rule: AletheRule::Or,
                clause: lit_terms.clone(),
                premises: vec![unit],
                args: Vec::new(),
            })
        };
        seeding.clause_versions.push((sat, proof_id));

        // A refuted arithmetic equality: the LRA oracle never asserts a
        // disequality, so branch conflicts resting on it would stall the
        // closer. Seed the checker-validated `la_disequality` bound split.
        if lit_terms.len() == 1 {
            self.seed_la_disequality_split(seeding, candidate, lit_terms[0], proof_id);
        }
    }

    /// The immediate conjuncts of `term` when it is an `(and t₁ … t_k)` with
    /// `k ≥ 2`, else `None`.
    fn conjunction_parts(&self, term: TermId) -> Option<Vec<TermId>> {
        match self.ctx.terms.get(term) {
            Td::App(Symbol::Named(name), args) if name == "and" && args.len() >= 2 => {
                Some(args.clone())
            }
            _ => None,
        }
    }

    /// Seed the CNF distribution of an `(or d₁ … d_n)` whose disjuncts include
    /// CONJUNCTIONS. Each conjunctive disjunct is weakened to one chosen
    /// conjunct by the premise-free `and_pos` tautology resolved on that
    /// disjunct:
    ///
    /// ```text
    /// (cl d₁ … d_n)  +  and_pos j ⊢ (cl (not dᵢ) c_j)   →  (cl … c_j …)
    /// ```
    ///
    /// so the cross-product of the choices yields clauses over usable atoms.
    /// `(or (and (not p) q) (and p q))` — the deductive-checks panic-freedom VC's
    /// "both paths reach the bound" disjunction — distributes to
    /// `(¬p∨p) (¬p∨q) (q∨p) (q)`, and it is the unit `q` the closer needs; the
    /// whole clause used to be dropped because `(and …)` is not a usable atom.
    ///
    /// Fail-closed at every gate: every added step is a strictly-validated
    /// tautology or a resolution against a clause this lane already derived, a
    /// choice that is not a usable atom declines the WHOLE distribution, and the
    /// emitted cross-product is capped — seeding a subset is always sound, so an
    /// over-budget shape simply seeds nothing.
    ///
    /// # This lane CAN take an `assume` the flat lane never took
    ///
    /// An earlier version of this comment claimed "the root `assume` is the SAME
    /// one the flat lane takes". Two independent adversarial reviews measured that
    /// to be FALSE for exactly the shape this lane exists to handle, and the claim
    /// is withdrawn rather than reworded. In the pristine file `seed_flat_clause_fact`
    /// reaches `assume_once` only AFTER `sat_clause` succeeds, and `sat_clause`
    /// returns `None` for any clause holding an `(and …)` disjunct, because
    /// `usable_atom` accepts only `{<, <=, >, >=, =}` apps and Bool vars. So on an
    /// `(or …)`-with-conjunctive-disjuncts ROOT the flat lane took no assume at all,
    /// and this lane's assume is new. (For the iff lane the original claim IS true:
    /// whenever it fires, `usable_atom(fact)` also succeeds.)
    ///
    /// The soundness conclusion survives, but for a DIFFERENT reason than the one
    /// originally given, and that reason is the one to rely on: the assume is
    /// authorized by `complete_problem_assertions_for_strict_proof()` scope
    /// enforcement in the strict checker — an assume outside the problem's own
    /// assertion set is rejected there — and the `or` root authentication above
    /// (native TermId identity / parsed-surface match) still runs untouched ahead
    /// of the distribution. The checker, not this comment, is the arbiter.
    fn seed_or_conjunct_distribution(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        fact: TermId,
        disjuncts: &[TermId],
        unit: Option<ProofId>,
    ) {
        // Per-disjunct choices, plus the DISTINCT conjunctive disjuncts to
        // peel. Resolution removes every occurrence of its pivot, so a
        // repeated conjunctive disjunct is peeled exactly once.
        let mut peel: Vec<(TermId, Vec<TermId>)> = Vec::new();
        let mut emitted_clauses: usize = 1;
        for &disjunct in disjuncts {
            let Some(parts) = self.conjunction_parts(disjunct) else {
                // A plain disjunct must still be a usable atom, or no
                // selection of this clause can ever be seeded.
                if usable_atom(&self.ctx.terms, disjunct).is_none() {
                    return;
                }
                continue;
            };
            if parts.len() > MAX_OR_DISTRIBUTION_CHOICES {
                return;
            }
            if parts
                .iter()
                .any(|&part| usable_atom(&self.ctx.terms, part).is_none())
            {
                return;
            }
            if peel.iter().any(|(term, _)| *term == disjunct) {
                continue;
            }
            let Some(product) = emitted_clauses.checked_mul(parts.len()) else {
                return;
            };
            if product > MAX_OR_DISTRIBUTION_CLAUSES {
                return;
            }
            emitted_clauses = product;
            peel.push((disjunct, parts));
        }
        if peel.is_empty() {
            return;
        }

        let unit = unit.unwrap_or_else(|| seeding.assume_once(candidate, fact));
        let or_step = candidate.add_step(ProofStep::Step {
            rule: AletheRule::Or,
            clause: disjuncts.to_vec(),
            premises: vec![unit],
            args: Vec::new(),
        });

        for selection in 0..emitted_clauses {
            if !seeding.charge() {
                return;
            }
            let mut clause = disjuncts.to_vec();
            let mut proof_id = or_step;
            let mut remaining = selection;
            for (disjunct, parts) in &peel {
                let position = remaining % parts.len();
                remaining /= parts.len();
                let chosen = parts[position];
                let Ok(position) = u32::try_from(position) else {
                    return;
                };
                let not_disjunct = self.ctx.terms.mk_not_raw(*disjunct);
                // and_pos ⊢ `(cl (not (and …)) c_position)`; the checker
                // re-decodes the source conjunction and re-checks the index.
                let and_pos = candidate.add_rule_step(
                    AletheRule::AndPos(position),
                    vec![not_disjunct, chosen],
                    Vec::new(),
                    vec![*disjunct],
                );
                // Resolution is a SET operation: drop every occurrence of the
                // pivot, and keep the resolvent duplicate-free.
                let mut next: Vec<TermId> = Vec::with_capacity(clause.len());
                for &literal in &clause {
                    if literal != *disjunct && !next.contains(&literal) {
                        next.push(literal);
                    }
                }
                if !next.contains(&chosen) {
                    next.push(chosen);
                }
                proof_id = candidate.add_resolution(next.clone(), *disjunct, and_pos, proof_id);
                clause = next;
            }
            // Every literal was pre-checked usable, so this maps; a shape that
            // still does not is skipped, never fatal.
            if let Some(sat) = seeding.sat_clause(&self.ctx.terms, &clause) {
                seeding.clause_versions.push((sat, proof_id));
            }
        }
    }

    /// Whether the authored surface for `root` is an `(and …)` whose immediate
    /// conjuncts elaborate, in order, to exactly `conjuncts` — the positional
    /// contract the seeded `and_pos` steps print. In native mode the canonical
    /// conjunction IS the authored problem term (its args are exactly the
    /// conjuncts `and_pos` prints), so TermId identity with an original-stack
    /// assertion is the whole check.
    fn and_root_matches_authored_surface(
        &mut self,
        auth: &RootAuthentication<'_>,
        root: TermId,
        conjuncts: &[TermId],
    ) -> bool {
        if let Some(native) = auth.native_root_identity(root) {
            return native;
        }
        let Some((_, parsed)) = auth.source_index.get(auth.originals, root) else {
            return false;
        };
        immediate_surface_parts_match(&mut self.ctx, parsed, "and", conjuncts)
    }

    /// Seed an authored formula-level ITE root, fail-closed. The root is
    /// assumed directly only when its authored surface matches the canonical
    /// ITE (native mode: when it IS an original-stack asserted term);
    /// otherwise the exact preprocessing sources must supply a provenance ITE
    /// lift whose checked branch derivation replaces the `assume` — parse
    /// mode only. Roots with neither are skipped. Returns `false` (abort the
    /// attempt) only when a planned provenance emission fails mid-candidate.
    fn seed_authenticated_ite_root(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        auth: &mut RootAuthentication<'_>,
        root: TermId,
    ) -> bool {
        let Td::Ite(cond, then_b, else_b) = *self.ctx.terms.get(root) else {
            return true;
        };
        let direct = match auth.native_root_identity(root) {
            Some(native) => native,
            None => auth
                .source_index
                .get(auth.originals, root)
                .is_some_and(|(_, parsed)| {
                    surface_arithmetic_ite_matches(&mut self.ctx, parsed, &[cond, then_b, else_b])
                }),
        };
        if direct {
            let unit = seeding.assume_once(candidate, root);
            self.seed_ite_path_clauses(seeding, candidate, root, unit);
            return true;
        }
        // Native mode retains no parse provenance: a root that is not itself
        // an original-stack asserted term is a rewrite/substitution product
        // whose ITE lift would need that provenance — skip it, fail-closed.
        if auth.native_asserted.is_some() {
            return true;
        }
        let Some(plan) = self.plan_provenance_ite_lift(
            &[root],
            auth.originals,
            &auth.source_index,
            &mut auth.planning,
        ) else {
            // No authenticated source: skip (never assume a substituted term).
            return true;
        };
        self.seed_provenance_ite_root(seeding, candidate, root, &plan)
    }
}
