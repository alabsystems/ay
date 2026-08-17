// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fact classification for the arithmetic-ITE seeded clause database:
//! conjunction flattening, root-`assume` authentication, and the dispatch
//! into the checked emission lanes.

use ay_core::term::TermData as Td;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId};

use super::{ArithIteSeeding, RootAuthentication, MAX_SEED_DEPTH};
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

        self.seed_flat_clause_fact(seeding, candidate, auth, fact, unit);
        true
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
