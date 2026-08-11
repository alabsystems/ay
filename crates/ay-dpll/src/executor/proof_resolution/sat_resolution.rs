// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Proof, ProofId, ProofStep, TermId, TermStore, TheoryLemmaProof};

use super::congruence::try_derive_empty_via_congruence_bridging;
use super::empty_clause::{
    derive_empty_via_trust_lemma, try_derive_empty_via_contradictory_assumptions,
    try_derive_empty_via_equality_contradiction, try_derive_empty_via_euf_transitivity,
    try_derive_empty_via_th_resolution, try_derive_empty_via_theory_packet_resolution,
};
use crate::executor::Executor;

/// Extract theory lemma annotations from the accumulated proof (#6031 Phase 4).
fn extract_theory_lemma_proofs(proof: &Proof) -> HashMap<Vec<TermId>, TheoryLemmaProof> {
    let mut map = HashMap::default();
    for step in proof.steps.iter() {
        if let ProofStep::TheoryLemma {
            clause,
            farkas,
            kind,
            lia,
            ..
        } = step
        {
            let mut normalized = clause.clone();
            normalized.sort_unstable();
            normalized.dedup();
            map.entry(normalized).or_insert_with(|| TheoryLemmaProof {
                clause: clause.clone(),
                kind: *kind,
                farkas: farkas.clone(),
                lia: lia.clone(),
            });
        }
    }
    map
}

impl Executor {
    /// Ensure the proof derives the empty clause. Tries multiple strategies
    /// in order: single-lemma th_resolution, two-lemma packet resolution,
    /// congruence bridging, equality contradiction, SAT resolution,
    /// contradictory assumptions, then trust-lemma fallback.
    pub(crate) fn ensure_empty_clause_derivation(&mut self, proof: &mut Proof) {
        if Self::proof_derives_empty_clause(proof) {
            return;
        }
        if try_derive_empty_via_th_resolution(&self.ctx.terms, proof) {
            return;
        }
        // QF_UF transitivity: synthesize an `eq_transitive` lemma directly from
        // equality assumptions when the contradiction is a pure transitivity
        // chain. Runs before the SAT-trace reconstruction because eager EUF
        // congruence axioms in the SAT trace are not recorded as theory lemmas
        // and would otherwise fall back to `trust`.
        if try_derive_empty_via_euf_transitivity(&mut self.ctx.terms, proof) {
            return;
        }
        if try_derive_empty_via_theory_packet_resolution(&self.ctx.terms, proof) {
            return;
        }
        if try_derive_empty_via_congruence_bridging(&mut self.ctx.terms, proof) {
            return;
        }
        // (#7913) Try equality contradiction before SAT resolution: the SAT
        // trace for preprocessed equality contradictions yields only trust
        // fallbacks. This strategy produces a proper LiaGeneric theory lemma.
        if try_derive_empty_via_equality_contradiction(&mut self.ctx.terms, proof) {
            return;
        }
        // Level-0 disjunctive arithmetic refutation (trust-cert-diag). A guarded
        // operation such as `if a>=b { a-b }` encodes a violation disjunction
        // `(or (a-b<0) (a-b>MAX))` that is UNSAT at level 0 given the guard and
        // domain bounds. The SAT/LRA pipeline refutes it via a *cycle* of pairwise
        // theory conflicts (`{¬D1,¬D2}`, `{guard,¬D2}`, `{¬guard,¬D1}`) that never
        // bottom out at the independent domain bounds, so the recorded clause set
        // stays satisfiable and the honest RUP closer cannot reach the empty
        // clause — leaving a `trust` hole. Re-derive a *bound-complete* Farkas
        // refutation of EACH disjunct against the original problem bounds and close
        // by genuine resolution. Runs before the SAT-trace closer (which would
        // otherwise accept a `trust`-hole empty clause) and is fail-closed: any
        // gap leaves the proof untouched for the strategies below.
        if self.try_derive_empty_via_disjunct_refutation(proof) {
            return;
        }
        if self.try_derive_empty_via_sat_resolution(proof) {
            return;
        }
        if try_derive_empty_via_contradictory_assumptions(&self.ctx.terms, proof) {
            return;
        }
        derive_empty_via_trust_lemma(&mut self.ctx.terms, proof);
    }

    /// Close a level-0 arithmetic disjunction by independently refuting each
    /// disjunct against the original problem bounds.
    ///
    /// SOUNDNESS: every recorded lemma is the conflict returned by a fresh
    /// `LraSolver::check()` over `¬Di` plus the asserted bound atoms — a genuine
    /// theory entailment carrying its own Farkas certificate (the same
    /// independently-checkable artifact the eager pipeline produces). No
    /// coefficients are fabricated; if the theory cannot refute a disjunct
    /// (returns `Sat`/`Unknown` or a certificate-less conflict) the whole
    /// strategy declines and the proof is left for the trust fallback. The final
    /// empty clause is a chain of `resolution` steps over those certified lemmas,
    /// the bound assumptions, and the disjunction's `or` decomposition.
    fn try_derive_empty_via_disjunct_refutation(&mut self, proof: &mut Proof) -> bool {
        use ay_core::{Symbol, TermData, TheoryLemmaKind, TheoryResult, TheorySolver};

        // An atom is a usable arithmetic *inequality* over only numeric leaves
        // (no `select`/`store`/UF nesting) — the shape the LRA Farkas refutation
        // and Carcara's `la_generic` checker accept. Equalities and array/UF
        // atoms are excluded: they belong to other (EUF/array/`th_resolution`)
        // strategies and must not be intercepted here.
        fn pure_arith_ineq(terms: &TermStore, t: TermId) -> bool {
            fn numeric_expr(terms: &TermStore, t: TermId) -> bool {
                match terms.get(t) {
                    TermData::Const(_) => true,
                    TermData::Var(..) => {
                        matches!(terms.sort(t), ay_core::Sort::Int | ay_core::Sort::Real)
                    }
                    TermData::App(Symbol::Named(name), args) => {
                        matches!(name.as_str(), "+" | "-" | "*" | "/")
                            && args.iter().all(|&a| numeric_expr(terms, a))
                    }
                    _ => false,
                }
            }
            let atom = match terms.get(t) {
                TermData::Not(inner) => *inner,
                _ => t,
            };
            matches!(
                terms.get(atom),
                TermData::App(Symbol::Named(name), args)
                    if args.len() == 2
                        && matches!(name.as_str(), "<" | "<=" | ">" | ">=")
                        && args.iter().all(|&a| numeric_expr(terms, a))
            )
        }

        // (1) Find a level-0 disjunction `(or D1 .. Dn)` recorded as an `assume`
        // or a premiseless single-literal `trust` step. Gate strictly: every
        // disjunct must be a pure arithmetic inequality (the guarded violation
        // shape). Any other disjunct (equality, array, UF) → not our case.
        let mut disjunction: Option<(ProofId, TermId, Vec<TermId>)> = None;
        for (idx, step) in proof.steps.iter().enumerate() {
            let term = match step {
                ProofStep::Assume(t) => *t,
                ProofStep::Step {
                    rule: ay_core::AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } if premises.is_empty() && clause.len() == 1 => clause[0],
                _ => continue,
            };
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                if name == "or"
                    && args.len() >= 2
                    && args.iter().all(|&d| pure_arith_ineq(&self.ctx.terms, d))
                {
                    disjunction = Some((ProofId(idx as u32), term, args.clone()));
                    break;
                }
            }
        }
        let Some((disj_id, disj_term, disjuncts)) = disjunction else {
            return false;
        };

        // (2) Candidate bound atoms: pure arithmetic inequalities already present
        // in the proof as `assume`/unit leaves. We deliberately use ONLY proof
        // leaves (not the raw assertion stack): every literal the refutation
        // resolves away must already have an in-proof unit, so no `assume` step
        // is injected mid-proof (which would violate Alethe's assume-before-step
        // ordering) and every resolved bound is a genuine problem premise.
        let mut bound_atoms: Vec<TermId> = Vec::new();
        let mut unit_proof: HashMap<TermId, ProofId> = HashMap::default();
        for (idx, step) in proof.steps.iter().enumerate() {
            let (term, id) = match step {
                ProofStep::Assume(t) => (*t, ProofId(idx as u32)),
                ProofStep::Step {
                    rule: ay_core::AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } if premises.is_empty() && clause.len() == 1 => (clause[0], ProofId(idx as u32)),
                _ => continue,
            };
            if term != disj_term && pure_arith_ineq(&self.ctx.terms, term) {
                if !bound_atoms.contains(&term) {
                    bound_atoms.push(term);
                }
                unit_proof.entry(term).or_insert(id);
            }
        }

        // (3) Refute each disjunct against the bounds with a fresh LRA solver,
        // capturing the certified conflict. Bail (fail-closed) on the first
        // disjunct the theory cannot refute with a Farkas certificate.
        struct Refutation {
            blocking_clause: Vec<TermId>,
            farkas: ay_core::FarkasAnnotation,
        }
        let mut refutations: Vec<Refutation> = Vec::with_capacity(disjuncts.len());
        for &di in &disjuncts {
            let (di_atom, di_val) = match self.ctx.terms.get(di) {
                TermData::Not(inner) => (*inner, false),
                _ => (di, true),
            };
            let mut lra = ay_lra::LraSolver::new(&self.ctx.terms);
            lra.set_combined_theory_mode(true);
            // Register first, then assert (matches the eager pipeline contract).
            TheorySolver::register_atom(&mut lra, di_atom);
            for &b in &bound_atoms {
                let atom = match self.ctx.terms.get(b) {
                    TermData::Not(inner) => *inner,
                    _ => b,
                };
                TheorySolver::register_atom(&mut lra, atom);
            }
            // Assert the disjunct Di *as it appears* together with the bounds.
            // The conflict `{Di} ∪ {bounds}` blocks to the lemma we want:
            // `{¬Di} ∪ {¬bounds}`, which licenses eliminating Di from the `or`.
            TheorySolver::assert_literal(&mut lra, di_atom, di_val);
            for &b in &bound_atoms {
                let (atom, val) = match self.ctx.terms.get(b) {
                    TermData::Not(inner) => (*inner, false),
                    _ => (b, true),
                };
                TheorySolver::assert_literal(&mut lra, atom, val);
            }
            let TheoryResult::UnsatWithFarkas(conflict) = TheorySolver::check(&mut lra) else {
                return false;
            };
            let Some(farkas) = conflict.farkas else {
                return false;
            };
            if farkas.coefficients.len() != conflict.literals.len() || conflict.literals.is_empty()
            {
                return false;
            }
            // The refutation must actually name this disjunct, otherwise it does
            // not license eliminating `Di` from the `or` decomposition.
            if !conflict.literals.iter().any(|l| l.term == di_atom) {
                return false;
            }
            // Blocking clause = negation of the conflict literals (a genuine
            // theory lemma): `{¬Di} ∪ {¬bound_j}`.
            let mut blocking_clause = Vec::with_capacity(conflict.literals.len());
            for lit in &conflict.literals {
                let t = if lit.value {
                    self.ctx.terms.mk_not_raw(lit.term)
                } else {
                    lit.term
                };
                blocking_clause.push(t);
            }
            refutations.push(Refutation {
                blocking_clause,
                farkas,
            });
        }

        // (4) Every non-disjunct literal we will resolve away must ALREADY be an
        // in-proof unit (`unit_proof`, built above from existing assume/unit
        // leaves). We do NOT inject new `assume` steps: that would both violate
        // Alethe's assume-before-step ordering and risk introducing a premise
        // Carcara cannot match to the original problem. If any required bound is
        // missing, decline (fail-closed) and let the trust fallback close it.
        let positive = |terms: &TermStore, lit: TermId| -> TermId {
            match terms.get(lit) {
                TermData::Not(inner) => *inner,
                _ => lit,
            }
        };
        for refutation in &refutations {
            for &lit in &refutation.blocking_clause {
                let pos = positive(&self.ctx.terms, lit);
                if disjuncts
                    .iter()
                    .any(|&d| positive(&self.ctx.terms, d) == pos)
                {
                    continue; // disjunct literal, handled via the `or` decomposition
                }
                if !unit_proof.contains_key(&pos) {
                    return false;
                }
            }
        }

        // (5) Emit certified theory-lemma steps for each refutation.
        let mut lemma_ids: Vec<ProofId> = Vec::with_capacity(refutations.len());
        for refutation in &refutations {
            let id = proof.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: refutation.blocking_clause.clone(),
                farkas: Some(refutation.farkas.clone()),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            lemma_ids.push(id);
        }

        // (6) Decompose the disjunction `(or D1..Dn)` into the clause [D1..Dn]
        // via the Alethe `or` rule, then resolve each disjunct away using its
        // refutation lemma (resolving the lemma's bound literals against their
        // units first). The running clause starts as [D1..Dn] and must end empty.
        let or_clause_id = proof.add_step(ProofStep::Step {
            rule: ay_core::AletheRule::Or,
            clause: disjuncts.clone(),
            premises: vec![disj_id],
            args: vec![],
        });

        let mut current_clause: Vec<TermId> = disjuncts.clone();
        let mut current_proof = or_clause_id;
        for (di_idx, &di) in disjuncts.iter().enumerate() {
            let refutation = &refutations[di_idx];
            // Resolve the lemma's bound literals away first so it becomes the unit
            // [¬Di], then resolve [..Di..] against [¬Di] to drop Di.
            let mut lemma_clause = refutation.blocking_clause.clone();
            let mut lemma_proof = lemma_ids[di_idx];
            let di_atom = positive(&self.ctx.terms, di);
            // Eliminate each non-disjunct bound literal of the lemma.
            let bound_lits: Vec<TermId> = lemma_clause
                .iter()
                .copied()
                .filter(|&l| positive(&self.ctx.terms, l) != di_atom)
                .collect();
            for blit in bound_lits {
                let pos = positive(&self.ctx.terms, blit);
                let Some(&unit_id) = unit_proof.get(&pos) else {
                    return false;
                };
                // Resolve lemma_clause (containing ¬pos) with unit [pos] on pos.
                let resolvent: Vec<TermId> = lemma_clause
                    .iter()
                    .copied()
                    .filter(|&l| l != blit)
                    .collect();
                let new_id = proof.add_resolution(resolvent.clone(), pos, lemma_proof, unit_id);
                lemma_clause = resolvent;
                lemma_proof = new_id;
            }
            // Now lemma_clause should be exactly [Di_literal_negation] i.e. the
            // literal that is complementary to Di in the disjunction.
            // Resolve current_clause (containing Di) against it on Di's atom.
            let resolvent: Vec<TermId> = current_clause
                .iter()
                .copied()
                .filter(|&l| positive(&self.ctx.terms, l) != di_atom)
                .chain(
                    lemma_clause
                        .iter()
                        .copied()
                        .filter(|&l| positive(&self.ctx.terms, l) != di_atom),
                )
                .collect();
            let new_id =
                proof.add_resolution(resolvent.clone(), di_atom, current_proof, lemma_proof);
            current_clause = resolvent;
            current_proof = new_id;
        }

        // (7) Success only if the resolution chain actually reached the empty
        // clause. Otherwise the proof now has dangling certified lemmas (sound,
        // unused) and we decline so the trust fallback still closes it.
        if !current_clause.is_empty() {
            return false;
        }

        // The disjunction premise is frequently recorded as a premiseless
        // `trust` step even though it is an input axiom (the SAT layer
        // materializes multi-literal input clauses as `trust`). It is already a
        // trusted, unjustified leaf; the only way a disjunction of arithmetic
        // atoms enters as a premiseless leaf is as the clausification of an
        // `(assert (or ...))`. Now that every disjunct has been independently
        // theory-refuted (so the disjunction is genuinely contradictory) and the
        // whole derivation is honest, relabel that leaf `trust` → `assume`: an
        // input assertion IS an assumption, so this only corrects the Alethe rule
        // tag without weakening or strengthening the proof.
        let authored_disjunction = self
            .proof_problem_assertion_provenance
            .as_ref()
            .map_or_else(
                || {
                    self.proof_original_problem_assertions()
                        .contains(&disj_term)
                },
                |provenance| provenance.original_problem_assertions.contains(&disj_term),
            );
        if authored_disjunction {
            for step in proof.steps.iter_mut() {
                let promote = matches!(
                    step,
                    ProofStep::Step {
                        rule: ay_core::AletheRule::Trust,
                        premises,
                        clause,
                        ..
                    } if premises.is_empty() && clause.len() == 1 && clause[0] == disj_term
                );
                if promote {
                    *step = ProofStep::Assume(disj_term);
                }
            }
        }
        // The surface-rewrite/export pass (`demote_non_problem_assumptions`) would
        // re-demote that `assume` to `trust` unless `disj_term` is whitelisted as
        // a problem assertion. Add it only when it is literally one of the
        // immutable authored roots. A substituted/current-window disjunction is
        // semantically related but is not source authority; promoting it here
        // would launder an unproved preprocessing rewrite into an `Assume`.
        if authored_disjunction && self.ctx.assertions.contains(&disj_term) {
            if let Some(provenance) = self.proof_problem_assertion_provenance.as_mut() {
                if provenance.original_problem_assertions.contains(&disj_term)
                    && !provenance.problem_assertions.contains(&disj_term)
                {
                    provenance.problem_assertions.push(disj_term);
                }
            }
        }
        true
    }

    /// Try to derive the empty clause via SAT resolution reconstruction.
    ///
    /// Returns true if successful, false if the clause trace is not available or
    /// doesn't lead to an empty-clause derivation.
    fn try_derive_empty_via_sat_resolution(&mut self, proof: &mut Proof) -> bool {
        let trace = match self.last_clause_trace.take() {
            Some(t) => t,
            None => return false,
        };
        if !trace.has_empty_clause() {
            self.last_clause_trace = Some(trace);
            return false;
        }

        let var_to_term = match self.last_var_to_term.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                return false;
            }
        };

        let _negations = match self.last_negations.take() {
            Some(m) => m,
            None => {
                self.last_clause_trace = Some(trace);
                self.last_var_to_term = Some(var_to_term);
                return false;
            }
        };

        let theory_lemma_map = extract_theory_lemma_proofs(proof);

        // Best-effort budget for synthesized-default certificates (#A2b):
        // `None` (explicit proof requests) keeps reconstruction unbounded.
        // An in-script `(set-option :produce-proofs true)` is an explicit
        // SMT-LIB demand for a proof and overrides any CLI-default budget.
        let script_demands_proof = matches!(
            self.ctx.get_option("produce-proofs"),
            Some(ay_frontend::OptionValue::Bool(true))
        );
        let mut manager = crate::SatProofManager::new(&var_to_term, &mut self.ctx.terms);
        if !script_demands_proof {
            manager.set_step_budget(self.proof_reconstruction_step_budget);
        }
        if let Some(ref cp) = self.last_clausification_proofs {
            manager.set_clausification_proofs(cp);
        }
        if let Some(ref tp) = self.last_original_clause_theory_proofs {
            manager.set_original_clause_theory_proofs(tp);
        }
        if !theory_lemma_map.is_empty() {
            manager.set_theory_lemma_proofs(&theory_lemma_map);
        }

        if !manager.can_process(&trace) {
            return false;
        }

        let result = manager.process_trace(&trace, proof);
        let trust_count = manager.trust_fallback_count();
        if trust_count > 0 {
            tracing::warn!(
                trust_fallbacks = trust_count,
                "SAT proof reconstruction used {trust_count} trust fallback(s) — \
                 proof contains unverified steps"
            );
        }
        // Proof-reconstruction introspection (`AY_PROOF_INTROSPECT=<path>`).
        //
        // Trust fallbacks are the reason a computed UNSAT can be rejected by the
        // strict publication gate, but the CAUSE lives back in conflict analysis:
        // a level-0 literal whose reason has no stable clause ID contributes no
        // resolution hint, so replay cannot resolve it away and the derived clause
        // ends up a strict superclause of its target. This report joins both ends
        // so the chain is visible without a rebuild. Writes to a FILE because
        // consumers (e.g. model-checker-consumer's driver) capture and discard the solver's
        // stderr, and ay's own `c` markers go to stdout.
        if let Some(path) = std::env::var_os("AY_PROOF_INTROSPECT") {
            use std::io::Write as _;
            let stats = trace.hint_omission_stats();
            // Hint-CAPTURE coverage: a learned clause recorded with an empty hint
            // list gives replay nothing to resolve with, which is the other way a
            // reconstruction can end up short of its target.
            let (mut learned, mut learned_no_hints, mut originals) = (0usize, 0usize, 0usize);
            for entry in trace.entries() {
                if entry.is_original {
                    originals += 1;
                } else {
                    learned += 1;
                    if entry.resolution_hints.is_empty() {
                        learned_no_hints += 1;
                    }
                }
            }
            if let Ok(mut fh) = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&path)
            {
                // Format first, then ONE `write_all`: several solver threads may
                // append concurrently, and a multi-call `writeln!` interleaves
                // their output into unparseable lines.
                let line = format!(
                    "PROOF_INTROSPECT trust_fallbacks={} hint_queries={} hint_resolved={} omitted_total={} omitted_not_clause_reason={} omitted_lazy_theory_reason={} omitted_zero_clause_id={} trace_entries={} trace_truncated={} proof_work_exhausted={} \
learned={} learned_no_hints={} originals={} untranslatable_entries={} unmapped_min={:?} unmapped_max={:?} mapped_vars={}\n",
                    trust_count,
                    stats.queries,
                    stats.resolved,
                    stats.omitted_total(),
                    stats.omitted_not_clause_reason,
                    stats.omitted_lazy_theory_reason,
                    stats.omitted_zero_clause_id,
                    trace.len(),
                    trace.is_truncated(),
                    trace.proof_work_exhausted(),
                    learned,
                    learned_no_hints,
                    originals,
                    manager.untranslatable_entries(),
                    manager.unmapped_var_range().0,
                    manager.unmapped_var_range().1,
                    manager.unmapped_var_range().2,
                );
                let _ = fh.write_all(line.as_bytes());
            }
        }
        result.is_some_and(|empty_id| {
            let step = proof.get_step(empty_id);
            matches!(
                step,
                Some(ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. })
                    if clause.is_empty()
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{FarkasAnnotation, Proof, ProofStep, TermId, TheoryLemmaKind};
    use num_rational::Rational64;

    use super::extract_theory_lemma_proofs;

    #[test]
    fn extracted_theory_map_keeps_positional_source_clause() {
        let p = TermId(8);
        let q = TermId(3);
        let mut proof = Proof::new();
        proof.add_step(ProofStep::TheoryLemma {
            theory: "LRA".to_string(),
            clause: vec![p, q, p],
            farkas: Some(FarkasAnnotation::new(vec![
                Rational64::new(1, 2),
                Rational64::from(1),
                Rational64::new(1, 2),
            ])),
            kind: TheoryLemmaKind::LraFarkas,
            lia: None,
        });

        let map = extract_theory_lemma_proofs(&proof);
        let annotation = map.get(&vec![q, p]).expect("normalized clause key");
        assert_eq!(annotation.clause, vec![p, q, p]);
        assert_eq!(
            annotation.farkas.as_ref().expect("Farkas").coefficients,
            vec![
                Rational64::new(1, 2),
                Rational64::from(1),
                Rational64::new(1, 2),
            ]
        );
    }
}
