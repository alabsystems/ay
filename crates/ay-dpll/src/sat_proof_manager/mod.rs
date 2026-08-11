// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-level proof manager for translating clause traces to Alethe proofs
//!
//! This module consumes the in-memory clause trace from the SAT solver and
//! translates it into explicit Alethe `resolution` proof steps.
//!
//! ## Design
//!
//! - The SAT solver records clause additions in a `ClauseTrace`
//! - Learned clauses include the conflict-analysis hint chain (`resolution_hints`)
//! - This manager translates SAT literals to SMT terms
//! - For each learned clause, it builds a chain of `ProofStep::Resolution`
//!   nodes and maps SAT clause IDs to proof IDs
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod derivation;
#[cfg(test)]
mod tests;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    AletheRule, ClausificationProof, Proof, ProofId, ProofStep, TermData, TermId, TermStore,
    TheoryLemmaProof,
};
use ay_sat::{ClauseTrace, Literal};

/// SAT-level proof manager for translating clause traces to Alethe steps
pub(crate) struct SatProofManager<'a> {
    /// Mapping from SAT variable index to SMT term
    var_to_term: &'a HashMap<u32, TermId>,
    /// Term store for creating negations
    terms: &'a mut TermStore,
    /// Clausification proof annotations from Tseitin encoder (#6031).
    /// Parallel to original SAT clause IDs — clause ID `n` corresponds to
    /// `clausification_proofs[n - 1]`, including reserved IDs for clauses the
    /// SAT layer recognized as tautological and omitted from the trace.
    clausification_proofs: Option<&'a [Option<ClausificationProof>]>,
    /// Original-clause theory proof annotations aligned by original clause ID.
    original_clause_theory_proofs: Option<&'a [Option<TheoryLemmaProof>]>,
    /// Theory lemma proof annotations (#6031 Phase 4).
    /// Keyed by normalized clause content (sorted TermIds) — when an original
    /// clause in the trace matches a recorded theory lemma, this map provides
    /// the annotation for emitting a `TheoryLemma` proof step.
    theory_lemma_proofs: Option<&'a HashMap<Vec<TermId>, TheoryLemmaProof>>,
    /// Number of learned clauses that fell back to Trust due to failed
    /// resolution hint reconstruction (#4585).
    trust_fallback_count: u32,
    /// Trace entries dropped because `clause_to_terms` failed (introspection).
    untranslatable_entries: u32,
    unmapped_var_min: Option<u32>,
    unmapped_var_max: Option<u32>,
    /// Remaining deterministic step budget for RUP replay (clause scans).
    /// `None` = unlimited. When it reaches `Some(0)`, `process_trace` bails
    /// out and returns `None` (best-effort synthesized-default certificates
    /// only; see `Executor::set_proof_reconstruction_step_budget`, #A2b).
    step_budget: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum HintDerivationError {
    NoUsableHints,
    NoResolutionPivot {
        usable_hint_count: usize,
    },
    FinalClauseMismatch {
        expected_clause: Vec<TermId>,
        derived_clause: Vec<TermId>,
    },
    /// RUP replay: the target clause contains complementary literals, so it
    /// is a tautology and not derivable by unit-propagation replay (#rank-4).
    RupTautologicalTarget,
    /// RUP replay: unit propagation over the hint clauses reached fixpoint
    /// without producing a conflict (#rank-4).
    RupNoConflict {
        usable_hint_count: usize,
        propagations: usize,
    },
}

impl<'a> SatProofManager<'a> {
    /// Create a new SAT proof manager
    pub(crate) fn new(var_to_term: &'a HashMap<u32, TermId>, terms: &'a mut TermStore) -> Self {
        SatProofManager {
            var_to_term,
            terms,
            clausification_proofs: None,
            original_clause_theory_proofs: None,
            theory_lemma_proofs: None,
            trust_fallback_count: 0,
            untranslatable_entries: 0,
            unmapped_var_min: None,
            unmapped_var_max: None,
            step_budget: None,
        }
    }

    /// Set the deterministic RUP-replay step budget (`None` = unlimited).
    pub(crate) fn set_step_budget(&mut self, budget: Option<u64>) {
        self.step_budget = budget;
    }

    /// Attach clausification proof annotations from the Tseitin encoder (#6031).
    ///
    /// When set, `add_original_clause_step` emits premiseless tautology rule
    /// steps (e.g., `and_pos`, `or_neg`) for annotated clauses instead of
    /// the generic `assume` + `or` pattern. Annotations are parallel to the
    /// original clause IDs (`id - 1` indexes this slice). Reserved IDs remain
    /// represented so omitted tautologies cannot shift later annotations.
    pub(crate) fn set_clausification_proofs(&mut self, proofs: &'a [Option<ClausificationProof>]) {
        self.clausification_proofs = Some(proofs);
    }

    fn original_annotation_by_id<T>(
        annotations: Option<&[Option<T>]>,
        clause_id: u64,
    ) -> Option<&T> {
        let index = usize::try_from(clause_id.checked_sub(1)?).ok()?;
        annotations?.get(index)?.as_ref()
    }

    /// Attach direct original-clause theory annotations for SAT reconstruction.
    pub(crate) fn set_original_clause_theory_proofs(
        &mut self,
        proofs: &'a [Option<TheoryLemmaProof>],
    ) {
        self.original_clause_theory_proofs = Some(proofs);
    }

    /// Attach theory lemma proof annotations (#6031 Phase 4).
    ///
    /// Keyed by normalized clause content (sorted TermIds). When an original
    /// clause in the clause trace matches a theory lemma annotation,
    /// `add_original_clause_step` emits a `TheoryLemma` proof step with
    /// the proper Alethe rule instead of the generic `assume` + `or` pattern.
    pub(crate) fn set_theory_lemma_proofs(
        &mut self,
        proofs: &'a HashMap<Vec<TermId>, TheoryLemmaProof>,
    ) {
        self.theory_lemma_proofs = Some(proofs);
    }

    /// Convert a SAT literal to an SMT term
    ///
    /// - `pos(v)` -> normalized proof literal for `var_to_term[v]`
    /// - `neg(v)` -> explicit syntactic complement of that literal
    fn lit_to_term(&mut self, lit: Literal) -> Option<TermId> {
        let var_idx = lit.variable().index() as u32;
        let Some(&term) = self.var_to_term.get(&var_idx) else {
            // Introspection: record the index range of variables absent from
            // `var_to_term`. Comparing it with the mapped range says whether the
            // unmapped vars sit ABOVE the mapped ones (allocated later, e.g. by
            // solver-internal machinery) or are interleaved with them.
            self.unmapped_var_min = Some(
                self.unmapped_var_min
                    .map_or(var_idx, |m: u32| m.min(var_idx)),
            );
            self.unmapped_var_max = Some(
                self.unmapped_var_max
                    .map_or(var_idx, |m: u32| m.max(var_idx)),
            );
            return None;
        };
        let positive_term = self.normalize_positive_literal(term);

        if lit.is_positive() {
            Some(positive_term)
        } else {
            Some(self.negate_term(positive_term))
        }
    }

    /// Normalize a SAT-variable atom for proof-literal emission.
    ///
    /// Returns the term unchanged. Previously converted AND atoms to their
    /// De Morgan dual `(not (or ...))`, but this produced incorrect Alethe
    /// syntax: and_pos expects `(cl (not (and ...)) ti)`, not
    /// `(cl (or (not ...) ...) ti)` (#6365).
    ///
    /// The AND atom stays as-is; `negate_term` produces `mk_not_raw(and_term)`
    /// which is the correct Alethe form for clausification tautology rules.
    fn normalize_positive_literal(&mut self, term: TermId) -> TermId {
        term
    }

    /// Convert a SAT clause to SMT terms.
    fn clause_to_terms(&mut self, clause: &[Literal]) -> Option<Vec<TermId>> {
        clause.iter().map(|&lit| self.lit_to_term(lit)).collect()
    }

    /// Canonicalized clause key (order-insensitive).
    fn normalize_clause(clause: &[TermId]) -> Vec<TermId> {
        let mut normalized = clause.to_vec();
        normalized.sort_unstable();
        normalized.dedup();
        normalized
    }

    /// Check whether clauses are equivalent up to ordering/duplication.
    fn clauses_equivalent(lhs: &[TermId], rhs: &[TermId]) -> bool {
        Self::normalize_clause(lhs) == Self::normalize_clause(rhs)
    }

    /// Rebind a position-indexed theory annotation to a traced clause by
    /// literal identity. SAT watched-literal movement may reorder clauses, and
    /// normalization may deduplicate them; a positional zip would silently
    /// attach Farkas multipliers to the wrong inequalities.
    ///
    /// Duplicate source coefficients are merged by sum. The merged value is
    /// placed on the first occurrence of that literal in the target order and
    /// any later duplicates receive zero. A source literal may disappear only
    /// when its merged coefficient is zero; target-only weakening literals are
    /// likewise assigned zero. Every non-Farkas annotation requires exact
    /// set-equivalence. Any other mismatch declines fail-closed.
    fn rebind_theory_annotation(
        annotation: &TheoryLemmaProof,
        target_clause: &[TermId],
    ) -> Option<TheoryLemmaProof> {
        let has_cutting_plane_farkas = matches!(
            annotation.lia.as_ref(),
            Some(ay_core::LiaAnnotation::CuttingPlane(_))
        );
        if annotation.farkas.is_none()
            && !has_cutting_plane_farkas
            && !Self::clauses_equivalent(&annotation.clause, target_clause)
        {
            return None;
        }

        let rebound_farkas = match annotation.farkas.as_ref() {
            Some(farkas) => Some(farkas.rebind_by_literal(&annotation.clause, target_clause)?),
            None => None,
        };
        let mut rebound_lia = annotation.lia.clone();
        if let Some(ay_core::LiaAnnotation::CuttingPlane(cutting_plane)) = rebound_lia.as_mut() {
            cutting_plane.farkas = cutting_plane
                .farkas
                .rebind_by_literal(&annotation.clause, target_clause)?;
        }

        Some(TheoryLemmaProof {
            clause: target_clause.to_vec(),
            kind: annotation.kind,
            farkas: rebound_farkas,
            lia: rebound_lia,
        })
    }

    /// Compute term negation, reusing cached terms where possible.
    fn negate_term(&mut self, term: TermId) -> TermId {
        if let TermData::Not(inner) = self.terms.get(term) {
            return *inner;
        }
        self.terms.mk_not_raw(term)
    }

    /// Compute a single binary resolution step, if possible.
    fn resolve_once(&mut self, lhs: &[TermId], rhs: &[TermId]) -> Option<(TermId, Vec<TermId>)> {
        let rhs_set: HashSet<TermId> = rhs.iter().copied().collect();

        let pivot = lhs
            .iter()
            .copied()
            .find(|lit| rhs_set.contains(&self.negate_term(*lit)))?;
        let neg_pivot = self.negate_term(pivot);

        let mut resolvent = Vec::with_capacity(lhs.len() + rhs.len());
        let mut seen: HashSet<TermId> = Default::default();

        for &lit in lhs.iter().chain(rhs.iter()) {
            if lit == pivot || lit == neg_pivot {
                continue;
            }
            let neg_lit = self.negate_term(lit);
            if seen.contains(&neg_lit) {
                // Tautological resolvent; skip this candidate.
                return None;
            }
            if seen.insert(lit) {
                resolvent.push(lit);
            }
        }

        Some((pivot, resolvent))
    }

    fn clause_from_step(step: &ProofStep) -> Option<Vec<TermId>> {
        match step {
            ProofStep::Assume(term) => Some(vec![*term]),
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::Step { clause, .. } => Some(clause.clone()),
            ProofStep::Anchor { .. } => None,
            // All current ProofStep variants handled above (#5692).
            // Wildcard covers future variants from #[non_exhaustive].
            other => unreachable!("unhandled ProofStep variant in clause_from_step(): {other:?}"),
        }
    }

    /// Process a clause trace and emit `resolution` proof steps.
    ///
    /// Returns the ProofId of the final empty clause derivation, or None if
    /// the trace cannot be translated to a complete resolution chain.
    pub(crate) fn process_trace(
        &mut self,
        trace: &ClauseTrace,
        proof: &mut Proof,
    ) -> Option<ProofId> {
        if !trace.has_empty_clause() {
            return None;
        }

        let mut clause_terms: HashMap<u64, Vec<TermId>> = HashMap::default();
        // Raw SAT clause versions for RUP hint replay (#rank-4 increment 1).
        // Every processed entry is appended (trace ids can be reused, so a
        // latest-wins map would drop live clauses); learned entries record
        // the clause the derivation actually proved (possibly a strict
        // subclause).
        let mut clause_versions: Vec<derivation::SatClauseVersion> = Vec::new();
        // Amortized two-watched-literal propagation engine over
        // `clause_versions` (append-only, so watch indices stay valid) —
        // replaces the per-derivation full rescans of the widening phase.
        let mut rup_engine = derivation::RupEngine::default();
        let mut latest_version_by_id: HashMap<u64, usize> = HashMap::default();
        let mut clause_proofs: HashMap<u64, ProofId> = HashMap::default();
        let mut existing_clause_map: HashMap<Vec<TermId>, ProofId> = HashMap::default();
        let mut final_empty: Option<ProofId> = None;
        let mut weak_empty: Option<ProofId> = None;
        for (idx, step) in proof.steps.iter().enumerate() {
            let Some(clause) = Self::clause_from_step(step) else {
                continue;
            };
            let key = Self::normalize_clause(&clause);
            existing_clause_map
                .entry(key)
                .or_insert(ProofId(idx as u32));
        }

        // #A2b: the SAT solver's search-time proof bookkeeping budget was
        // exhausted, so the trace's level-0 LRAT unit chains are incomplete
        // by construction. Fail closed immediately instead of grinding
        // through a reconstruction that can only end in trust holes. Only
        // ever set on budgeted (synthesized-default) runs.
        if trace.proof_work_exhausted() {
            tracing::warn!(
                "clause trace marked proof-work-exhausted (#A2b); \
                 skipping best-effort default certificate"
            );
            return None;
        }

        for entry in trace.entries() {
            // Best-effort budget (#A2b): once the RUP-replay step budget is
            // exhausted, abandon reconstruction entirely — the caller treats
            // `None` as "no reconstructable proof" (synthesized-default runs
            // degrade to a warning; verdicts are already decided upstream).
            if self.step_budget == Some(0) {
                tracing::warn!(
                    "SAT proof reconstruction step budget exhausted; \
                     skipping best-effort default certificate"
                );
                return None;
            }
            let Some(mut entry_clause_terms) = self.clause_to_terms(&entry.clause) else {
                // Introspection: this trace entry is DROPPED from the replay maps
                // entirely — its literals have no term mapping — so no later
                // resolution can use it. Counted because a small `clause_terms`
                // map is the difference between a reconstructable proof and a
                // `trust` fallback.
                self.untranslatable_entries += 1;
                continue;
            };
            let mut entry_sat_clause = entry.clause.clone();

            let clause_proof = if entry.is_original {
                // Bind annotations by the stable original-clause ID. The SAT
                // layer reserves an ID when it omits a tautological input, so
                // counting only surviving trace entries shifts every later
                // annotation and can mislabel an `or_pos` clause as `ite_neg1`.
                let annotation =
                    Self::original_annotation_by_id(self.clausification_proofs, entry.id);
                let indexed_theory_annotation =
                    Self::original_annotation_by_id(self.original_clause_theory_proofs, entry.id);
                // Look up theory lemma annotation by normalized clause content (#6031 Phase 4).
                let normalized_key = Self::normalize_clause(&entry_clause_terms);
                let theory_annotation = indexed_theory_annotation
                    .and_then(|candidate| {
                        Self::rebind_theory_annotation(candidate, &entry_clause_terms)
                    })
                    .or_else(|| {
                        self.theory_lemma_proofs
                            .and_then(|proofs| proofs.get(&normalized_key))
                            .and_then(|candidate| {
                                Self::rebind_theory_annotation(candidate, &entry_clause_terms)
                            })
                    });
                // Level-0-minimized theory lemma bridge (#rank-4 increment 2).
                // The SAT layer strips literals that are false at level 0
                // from theory conflict clauses before they reach the trace,
                // so the traced clause no longer matches the recorded
                // (annotated, possibly Farkas-certified) full lemma clause
                // and would fall through to an anonymous `assume` step that
                // later demotes to Trust. When a recorded lemma clause is a
                // SUPERSET of the traced clause, emit the full lemma as the
                // certified `TheoryLemma` leaf and derive the traced clause
                // from it by RUP replay over the already-processed clause
                // database — the level-0 units become explicit resolution
                // antecedents (the OpenSMT "units carry partition masks"
                // shape, expressed as genuine Resolution steps).
                // Units are bridged too (rank-4 inc-5): a theory conflict can
                // minimize all the way down to ONE literal at level 0, and an
                // anonymous unit `assume` for a non-assertion later demotes to
                // a premiseless Trust step (`demote_non_problem_assumptions`)
                // — the last uncertified leaf in executor proofs.
                let bridged = if annotation.is_none()
                    && theory_annotation.is_none()
                    && !entry_clause_terms.is_empty()
                    && !existing_clause_map.contains_key(&normalized_key)
                {
                    self.try_bridge_minimized_theory_lemma(
                        &entry_clause_terms,
                        &entry_sat_clause,
                        &normalized_key,
                        &mut clause_versions,
                        &mut existing_clause_map,
                        &mut rup_engine,
                        proof,
                    )
                } else {
                    None
                };
                // Last-resort certified re-derivation of a unit derived-fact
                // clause imported from an earlier split-loop iteration
                // (#seq-unit-fact): bounded DPLL with resolution logging over
                // the processed clause database. Only for units the bridge
                // declined; fail-closed (None keeps the assume path).
                let bridged = bridged.or_else(|| {
                    if annotation.is_none()
                        && theory_annotation.is_none()
                        && entry_clause_terms.len() == 1
                        && !existing_clause_map.contains_key(&normalized_key)
                    {
                        self.derive_clause_via_bounded_dpll(
                            &entry_sat_clause,
                            &mut clause_versions,
                            &mut existing_clause_map,
                            proof,
                        )
                        .inspect(|(derived_proof, derived_terms, _)| {
                            existing_clause_map
                                .entry(Self::normalize_clause(derived_terms))
                                .or_insert(*derived_proof);
                        })
                    } else {
                        None
                    }
                });
                match bridged {
                    Some((bridged_proof, bridged_terms, bridged_sat)) => {
                        entry_clause_terms = bridged_terms;
                        entry_sat_clause = bridged_sat;
                        bridged_proof
                    }
                    None => Self::add_original_clause_step(
                        self.terms,
                        proof,
                        &entry_clause_terms,
                        &mut existing_clause_map,
                        annotation,
                        theory_annotation.as_ref(),
                    ),
                }
            } else {
                match self.derive_clause_from_hints(
                    &entry_clause_terms,
                    &entry.clause,
                    &entry.resolution_hints,
                    &clause_terms,
                    &clause_versions,
                    &latest_version_by_id,
                    &clause_proofs,
                    &mut rup_engine,
                    proof,
                ) {
                    Ok((derived, derived_clause, derived_sat)) => {
                        // RUP replay may derive a strict subclause of the
                        // target (a stronger clause). Record what the proof
                        // node actually proves so downstream hint replays and
                        // resolvents stay exact (#rank-4 increment 1).
                        entry_clause_terms = derived_clause;
                        entry_sat_clause = derived_sat;
                        derived
                    }
                    Err(error) => {
                        // For the EMPTY clause, try the VERIFIED chain INLINE
                        // (level0_rup folds theory lemmas; then units; then
                        // assumptions) BEFORE Trust. A genuine empty-clause
                        // derivation must not be pre-empted by a counted/emitted
                        // orphaned Trust step — which both inflates the fallback
                        // count AND would fail check_proof_strict (#verification-route).
                        let _verified_empty = if entry_clause_terms.is_empty() {
                            // The empty-clause hint chain can resolve down to a
                            // residual arithmetic clause (e.g. `[T22,T23]`) that
                            // is only closed by the theory-conflict-exclusion
                            // lemma `[¬T22,¬T23]` — which was never recorded
                            // upstream because the eager `check()` did not
                            // return Unsat over exactly that pair. Re-derive a
                            // GENUINE Farkas certificate for that residual with
                            // a fresh LraSolver and record it, so the level0_rup
                            // replay below has the missing lemma to close `[]`.
                            // Fail-closed: records nothing unless the fresh
                            // solver certifies the conflict (strict-checkable).
                            if let HintDerivationError::FinalClauseMismatch {
                                derived_clause, ..
                            } = &error
                            {
                                let _rr_clause = derived_clause.clone();
                                // Level-0 theory context = the FULL level-0
                                // unit-propagation closure over the processed
                                // clause database, filtered to literals a fresh
                                // LraSolver can assert. Unit clauses alone are
                                // NOT enough: on the ReLU-disjunction family the
                                // bounds that make the residual infeasible (e.g.
                                // `(<= x z)` from the equality's and-split, or
                                // the refuted branch's conjuncts behind
                                // or_pos/and_pos) are only reachable BY
                                // propagation — and any literal in this closure
                                // is re-derived by `derive_empty_via_level0_rup`,
                                // so a conflict lemma recorded over it still
                                // closes to `(cl)` with genuine Resolution steps.
                                let _rr_ctx: Vec<(TermId, bool)> =
                                    self.level0_arith_context(&clause_versions);
                                self.record_residual_lra_conflict_lemma(
                                    &_rr_clause,
                                    &_rr_ctx,
                                    proof,
                                );
                            }
                            self.derive_empty_via_level0_rup(&clause_versions, proof)
                                .or_else(|| {
                                    self.derive_empty_from_units(
                                        &clause_terms,
                                        &clause_proofs,
                                        proof,
                                    )
                                })
                                .or_else(|| self.derive_empty_from_assumptions(proof))
                                // Bounded DPLL(T): re-derives the case-split
                                // exclusion lemmas the eager pipeline never
                                // recorded (the ReLU-disjunction family) with
                                // fresh Farkas certificates, then closes by
                                // genuine resolution. Fail-closed.
                                .or_else(|| {
                                    self.derive_empty_via_bounded_dpll_theory(
                                        &clause_versions,
                                        proof,
                                    )
                                })
                        } else {
                            None
                        };
                        // Bounded-DPLL re-derivation of a learned clause whose
                        // hint replay failed (#seq-unit-fact): certified
                        // resolution over the processed clause database plus
                        // the recorded theory lemmas. Fail-closed (None runs
                        // the trust fallback below unchanged).
                        let _dpll = if _verified_empty.is_none() && !entry_clause_terms.is_empty() {
                            self.derive_clause_via_bounded_dpll(
                                &entry_sat_clause,
                                &mut clause_versions,
                                &mut existing_clause_map,
                                proof,
                            )
                        } else {
                            None
                        };
                        if let Some(_v) = _verified_empty {
                            _v
                        } else if let Some((dpll_proof, dpll_terms, dpll_sat)) = _dpll {
                            entry_clause_terms = dpll_terms;
                            entry_sat_clause = dpll_sat;
                            dpll_proof
                        } else {
                            // Trust-lemma fallback (#4317 path 2 of 3).
                            // Per-clause fallback when resolution hint reconstruction
                            // fails. Emits the clause as AletheRule::Trust with whatever
                            // premises we could resolve. Sound but not independently
                            // verifiable by the proof checker.
                            // See also: executor/proof.rs derive_empty_via_trust_lemma (path 1)
                            self.trust_fallback_count += 1;
                            let premises: Vec<ProofId> = entry
                                .resolution_hints
                                .iter()
                                .filter_map(|hint| clause_proofs.get(hint).copied())
                                .collect();
                            tracing::warn!(
                                clause_id = entry.id,
                                clause = ?entry_clause_terms,
                                resolution_hints = ?entry.resolution_hints,
                                ?error,
                                trust_fallbacks = self.trust_fallback_count,
                                "sat proof reconstruction fell back to trust"
                            );
                            proof.add_rule_step(
                                AletheRule::Trust,
                                entry_clause_terms.clone(),
                                premises,
                                Vec::new(),
                            )
                        }
                    }
                }
            };

            clause_terms.insert(entry.id, entry_clause_terms.clone());
            latest_version_by_id.insert(entry.id, clause_versions.len());
            clause_versions.push((entry_sat_clause, clause_proof));
            clause_proofs.insert(entry.id, clause_proof);

            if entry_clause_terms.is_empty() {
                // Only accept if the derivation is meaningful (has premises).
                // A premise-less trust step for the empty clause is a fallback
                // that should not prevent derive_empty_from_units/assumptions
                // from producing a better proof (#4686).
                let is_meaningful = match proof.get_step(clause_proof) {
                    // A premise-bearing Trust step IS the per-clause fallback itself;
                    // it must NOT count as meaningful, or it sets `final_empty` and
                    // pre-empts the honest `derive_empty_via_level0_rup` closer below
                    // (which can reconstruct the empty clause from the recorded theory
                    // conflict lemma + level-0 units). #unit-prop.
                    Some(ProofStep::Step { premises, rule, .. }) => {
                        !premises.is_empty() && !matches!(rule, AletheRule::Trust)
                    }
                    Some(ProofStep::Resolution { .. }) => true,
                    _ => false,
                };
                if is_meaningful {
                    final_empty = Some(clause_proof);
                } else if weak_empty.is_none() {
                    weak_empty = Some(clause_proof);
                }
            }
        }

        final_empty
            // Level-0 propagation-conflict exits record no empty-clause trace
            // entry (only the UNSAT flag); replay unit propagation over the
            // whole processed clause database to recover a genuine Resolution
            // derivation of the empty clause (#rank-4 increment 5).
            .or_else(|| self.derive_empty_via_level0_rup(&clause_versions, proof))
            .or_else(|| self.derive_empty_from_units(&clause_terms, &clause_proofs, proof))
            .or_else(|| self.derive_empty_from_assumptions(proof))
            // Bounded DPLL(T) closer (#relu-trust-glue): the eager pipeline
            // refutes case-split branches without recording their exclusion
            // lemmas, leaving the traced clause set propositionally
            // SATISFIABLE — level-0 RUP stalls by construction. Re-derive
            // the missing lemmas with fresh Farkas certificates at each
            // stalled assignment and close by genuine resolution.
            // Fail-closed on any uncertifiable shape.
            .or_else(|| self.derive_empty_via_bounded_dpll_theory(&clause_versions, proof))
            // Keep a premise-less empty trust step as a last resort so
            // process_trace can still return a contradiction when no better
            // derivation exists (e.g., original empty clause inputs).
            .or(weak_empty)
    }

    /// Number of learned clauses that fell back to `AletheRule::Trust` due
    /// to failed resolution hint reconstruction.
    ///
    /// A non-zero count means the proof contains unverified steps. The proof
    /// is structurally valid but the trust nodes bypass independent checking.
    /// (min, max) index of SAT variables missing from `var_to_term`, and the
    /// number of mapped variables, for coverage diagnosis.
    pub(crate) fn unmapped_var_range(&self) -> (Option<u32>, Option<u32>, usize) {
        (
            self.unmapped_var_min,
            self.unmapped_var_max,
            self.var_to_term.len(),
        )
    }

    pub(crate) fn untranslatable_entries(&self) -> u32 {
        self.untranslatable_entries
    }

    pub(crate) fn trust_fallback_count(&self) -> u32 {
        self.trust_fallback_count
    }

    /// Check if the trace can be processed (has necessary variable mappings).
    ///
    /// Note: This method checks if clauses can be translated without actually
    /// modifying the TermStore, so it uses the var_to_term map directly.
    pub(crate) fn can_process(&self, trace: &ClauseTrace) -> bool {
        if trace.is_empty() {
            return trace.has_empty_clause();
        }

        trace.entries().iter().any(|entry| {
            entry.clause.iter().all(|lit| {
                let var_idx = lit.variable().index() as u32;
                self.var_to_term.contains_key(&var_idx)
            })
        })
    }
}
