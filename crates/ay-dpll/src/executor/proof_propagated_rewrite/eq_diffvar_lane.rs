// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer mint and consumer lane for the `EqDiffVar` atom-fold channel.
//!
//! The derivation itself lives in [`super::eq_diffvar_bridge`]; this module is
//! the plumbing on either side of it — what the preprocessing pass records, and
//! which proof steps the replay is offered.
//!
//! # Why this lane runs LAST, on `trust` steps
//!
//! [`Executor::derive_propagated_value_assumptions`] runs BEFORE
//! `demote_non_problem_assumptions`, on `Assume` steps. This one runs AFTER
//! that demotion AND after `promote_fresh_definitional_bounds`, on the
//! premiseless `trust` steps the demotion left, and both halves of that
//! ordering are load-bearing:
//!
//! * **After the demotion.** The bridge emits `fresh_def_bound` steps, and the
//!   checker decides their FRESH condition against the finished proof's
//!   `assume` set. Before the demotion the rewritten assertions that MENTION
//!   the difference variable are still `Assume` steps, so every symbol would
//!   look constrained. This is the same ordering constraint, for the same
//!   reason, that `proof_fresh_def` records.
//! * **After the promotion.** A symbol may already be bound to a definiens by
//!   a promoted `fresh_def_bound` step. Two definientia for one symbol are an
//!   EQUATION between them, which `FreshDefRegistry` rejects outright — a HARD
//!   `InvalidTheoryLemma`, strictly worse than the rescuable `trust` step this
//!   lane is trying to remove. Running afterwards lets the index ADOPT the
//!   binding that already exists instead of minting a competing one; measured
//!   on `dillig12_m`, `VariableSubstitution` rewrites the definiens of 105 of
//!   1689 difference variables, so the two do sometimes disagree and the
//!   Farkas self-check then declines those.
//!
//! A Gate-2 re-run of the checker's own `FreshDefRegistry::collect` over the
//! spliced proof reverts the WHOLE lane if it declines, so producer and checker
//! cannot drift apart.

use super::*;

/// Cap on candidate `trust` steps planned in one call. Measured population on
/// `dillig12_m` is 2-3 per proof; the cap only bounds a pathological proof.
const MAX_EQ_DIFFVAR_CANDIDATES: usize = 512;

/// What the retention-off commit gate decided about one finished subset
/// output (see `run_assumption_authority_passes_without_parsed_syntax`).
/// `remember` marks the DETERMINISTIC reverts (envelope refusal, walk past
/// the repeatable-work budget), which latch the size-scoped
/// `eqdv_retention_off_declined_at_steps`; a `Cancelled` revert is load-dependent
/// and must not disable the lane for the executor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum EqDiffVarCommitDecision {
    Commit,
    Revert {
        /// Latch the decline for this executor's remaining assemblies.
        remember: bool,
    },
}

impl Executor {
    /// Replace every premiseless `trust` step that carries an
    /// `EqDiffVar`-rewritten assertion with a derivation of that assertion from
    /// its AUTHORED form plus the pass's own definition (#4751).
    ///
    /// Declines silently, leaving today's `trust` step in place, whenever any
    /// leg fails. Nothing here can make a proof less certifiable than it was.
    ///
    /// Returns whether anything was SPLICED — the retention-off subset's
    /// commit gate evaluates its finished output only when this is true, so a
    /// rebuild the lane has nothing for never pays the gate's document walk.
    pub(in crate::executor) fn derive_eq_diffvar_rewritten_assertions(
        &mut self,
        proof: &mut Proof,
        problem_assertions: &[TermId],
    ) -> bool {
        if !crate::quant_unit_authority::quant_unit_authority_enabled()
            || self.propagated_value_provenance.eq_diffvar_atoms.is_empty()
        {
            return false;
        }
        // Cheapest possible early-out, and it is load-bearing rather than
        // cosmetic: this lane runs on EVERY proof rewrite, and on a persistent
        // executor most of those rewrites have nothing for it. A proof with no
        // premiseless unit `trust` step has no candidate whatever the indexes
        // say, so decide that first, before any index is built.
        if !proof.steps.iter().any(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty() && args.is_empty() && clause.len() == 1
            )
        }) {
            return false;
        }
        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();
        let (mut record_by_after, entry_by_expr) = self.propagation_replay_indexes();
        // The `EqDiffVar` rewrites are merged in SECOND so a term that is both
        // an `EqDiffVar` `after` and a `PropagateValues`/`VariableSubstitution`
        // `after` keeps the record the existing lane already resolves it by.
        for record in &self.propagated_value_provenance.eq_diffvar_rewrites {
            if record.before != record.after {
                record_by_after
                    .entry(record.after)
                    .or_insert((record.before, record.stamp));
            }
        }
        let definitions = self.eq_diffvar_definition_index();
        // PHASE A — reclaim the definitional bounds a LATER pass rewrote.
        //
        // The proof may already bind a difference variable through a promoted
        // `fresh_def_bound` step carrying the REWRITTEN definiens `lin'`, while
        // the folded atoms are equivalent under the MINTED `lin`. Binding `d`
        // to both is exactly what `FreshDefRegistry`'s SINGLE DEFINIENS
        // condition rejects, so each such step is instead re-derived from the
        // minted bound through the ordinary record bridge. A symbol whose group
        // cannot be reclaimed WHOLE stays bound as it is and is excluded from
        // phase B, so the two never compete.
        let scope = EqDiffVarPlanScope {
            problem_set: &problem_set,
            problem_assertions,
            record_by_after: &record_by_after,
            entry_by_expr: &entry_by_expr,
            definitions: &definitions,
        };
        let (mut planned, blocked) = self.plan_eq_diffvar_definition_reclaim(proof, &scope);
        let eqdv_by_atom = self.eq_diffvar_atom_index(&blocked);
        // PHASE B — the rewritten assertions themselves.
        self.plan_eq_diffvar_rewritten_assertions(proof, &scope, &eqdv_by_atom, &mut planned);
        if planned.is_empty() {
            return false;
        }
        // Gate-2: the CHECKER's own whole-proof fresh-definition validation,
        // run BEFORE the splice on a proof that carries exactly the two step
        // kinds `FreshDefRegistry::collect` reads — every `assume` and every
        // `fresh_def_bound`, the ones already in the proof plus the ones these
        // chains would add. That is the same decision the strict presentation
        // will make, and declining here leaves the `trust` steps exactly as
        // they are, so an introduction this lane cannot justify never becomes a
        // hard `InvalidTheoryLemma` rejection in place of the rescuable step it
        // replaced.
        //
        // Deciding it BEFORE rather than reverting after is not a refactor: the
        // revert needed a clone of the whole proof on EVERY firing, and this
        // lane fires on proofs of several thousand steps.
        if !self.eq_diffvar_definitions_stay_admissible(proof, problem_assertions, &planned) {
            return false;
        }
        splice::splice_propagated_plans(
            proof,
            splice::PlannedPropagationChains {
                shared_chain: Proof::new(),
                shared_conclusions: HashMap::default(),
                solo: planned,
            },
        );
        true
    }

    /// Whether a remembered commit-gate decline COVERS this document, i.e.
    /// whether re-asking the gate would re-pay a whole-proof walk for the same
    /// answer. A decline is priced against the pre-splice document it was made
    /// on; a document under HALF that size is a different economic question —
    /// measured on `queens_bench/super_queen5-1` and `sal/lpsat/lpsat-goal-1`,
    /// whose final assemblies shrink to 201/21 steps, splice cheaply, and
    /// strict-certify — so it re-asks (and a repeat decline narrows the scope,
    /// bounding re-asks at log2 of the first declined size).
    pub(in crate::executor) fn eq_diffvar_retention_off_decline_covers(
        &self,
        proof: &Proof,
    ) -> bool {
        let declined_at = self.eqdv_retention_off_declined_at_steps.get();
        declined_at != 0 && proof.steps.len().saturating_mul(2) >= declined_at
    }

    /// The retention-off subset's CHEAP pre-clone screen: whether this lane
    /// could possibly plan anything for `proof` — exactly the lane's own
    /// early-outs, so a solve with no `EqDiffVar` provenance or no candidate
    /// `trust` leaf never pays the commit gate's snapshot clone.
    pub(in crate::executor) fn eq_diffvar_lane_would_consider(&self, proof: &Proof) -> bool {
        crate::quant_unit_authority::quant_unit_authority_enabled()
            && !self.propagated_value_provenance.eq_diffvar_atoms.is_empty()
            && proof.steps.iter().any(|step| {
                matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::Trust,
                        clause,
                        premises,
                        args,
                    } if premises.is_empty() && args.is_empty() && clause.len() == 1
                )
            })
    }

    /// Ask the exact publication gate whether the spliced proof is worth
    /// keeping, pricing in that the pipeline will RE-RUN that gate on every
    /// assembly.
    ///
    /// The decision is made by `check_proof_strict_with_datatypes` — the same
    /// call `mint_unsat_certificate`'s presentation makes — so the lane and
    /// the mint cannot disagree about what fits the envelope. Three tiers:
    ///
    ///  * `Ok` COMMITS at any cost: the proof now strict-certifies outright —
    ///    the best outcome this lane can produce, and the mint then takes
    ///    `StrictProof` with no discharge lane and no re-solve. Measured
    ///    (QF_IDL 900-file paired sample, 2026-08-27): every such commit was
    ///    wall-safe and `job_shop/jobshop12-2-6-6-4-4-11` got FASTER
    ///    (7.55 s -> 5.42 s) because the discharge machinery disappeared.
    ///  * a TYPED rejection commits only when the walk's metered work fits
    ///    [`crate::executor::proof::REPEATABLE_CHECK_WORK`]. A typed
    ///    rejection is the same rescuable trust-family class the pre-splice
    ///    proof was in, so the mint outcome is unchanged either way — but the
    ///    walk itself is re-run ~60 times across assemblies, and a
    ///    near-envelope walk multiplies into seconds: measured on
    ///    `sal/bakery/inf-bakery-mutex-18`, 60 walks at 287-295M work each
    ///    added 6.4 s of wall and pushed a correct `unsat` over `-T:10` with
    ///    no envelope refusal anywhere. Reverting restores the pre-splice
    ///    fail-fast presentation those walks cost milliseconds on.
    ///  * `ResourceLimit` REVERTS: at mint time this exact outcome reaches
    ///    `discharge_trust_steps_for_certification` with nothing collected
    ///    and falls through to a whole-problem re-solve — the measured
    ///    degradation (`planning/plan-8`, `plan-11..14`, `sal/lpsat-goal-7`
    ///    published `unknown` over correct `unsat`s). `Cancelled` also
    ///    reverts — the caller asked us to stop; nothing was learned — but is
    ///    NOT remembered, so a transient interrupt cannot disable the lane
    ///    for the rest of the executor's life.
    ///
    /// Both deterministic reverts are REMEMBERED, size-scoped, in
    /// `eqdv_retention_off_declined_at_steps`: rebuilds of a similar-sized
    /// document share the answer, and a much smaller later document re-asks
    /// (see `eq_diffvar_retention_off_decline_covers`).
    pub(in crate::executor) fn eq_diffvar_presentation_commit_decision(
        &self,
        proof: &Proof,
    ) -> EqDiffVarCommitDecision {
        let (outcome, consumed_work) = self.check_proof_strict_with_datatypes_reporting_work(proof);
        match outcome {
            Ok(_) => EqDiffVarCommitDecision::Commit,
            Err(ay_proof::ProofCheckError::ResourceLimit) => {
                EqDiffVarCommitDecision::Revert { remember: true }
            }
            Err(ay_proof::ProofCheckError::Cancelled) => {
                EqDiffVarCommitDecision::Revert { remember: false }
            }
            Err(_) if consumed_work <= crate::executor::proof::REPEATABLE_CHECK_WORK => {
                EqDiffVarCommitDecision::Commit
            }
            Err(_) => EqDiffVarCommitDecision::Revert { remember: true },
        }
    }

    /// Whether `FreshDefRegistry::collect` still accepts the proof once the
    /// planned chains are spliced into it.
    ///
    /// Exact rather than approximate: `collect` reads `assume` steps and
    /// `fresh_def_bound` steps and nothing else, so a proof carrying just those
    /// — from the target proof and from every planned chain — puts the same
    /// question to the same code.
    fn eq_diffvar_definitions_stay_admissible(
        &self,
        proof: &Proof,
        problem_assertions: &[TermId],
        planned: &HashMap<usize, (Proof, ProofId)>,
    ) -> bool {
        let mut projection = Proof::new();
        let replaced: HashSet<usize> = planned.keys().copied().collect();
        for (index, step) in proof.steps.iter().enumerate() {
            if replaced.contains(&index) {
                continue;
            }
            match step {
                ProofStep::Assume(_) => {
                    projection.add_step(step.clone());
                }
                ProofStep::Step {
                    rule: AletheRule::FreshDefBound,
                    ..
                } => {
                    projection.add_step(step.clone());
                }
                _ => {}
            }
        }
        for (chain, _) in planned.values() {
            for step in &chain.steps {
                match step {
                    ProofStep::Assume(_) => {
                        projection.add_step(step.clone());
                    }
                    ProofStep::Step {
                        rule: AletheRule::FreshDefBound,
                        ..
                    } => {
                        projection.add_step(step.clone());
                    }
                    _ => {}
                }
            }
        }
        ay_proof::FreshDefRegistry::collect(&projection, &self.ctx.terms, Some(problem_assertions))
            .is_ok()
    }

    /// Phase B: plan a derivation for every premiseless `trust` step carrying an
    /// assertion the pass rewrote.
    fn plan_eq_diffvar_rewritten_assertions(
        &mut self,
        proof: &Proof,
        scope: &EqDiffVarPlanScope<'_>,
        eqdv_by_atom: &HashMap<TermId, EqDiffVarAtomPlan>,
        planned: &mut HashMap<usize, (Proof, ProofId)>,
    ) {
        if eqdv_by_atom.is_empty() {
            return;
        }
        for (index, term) in
            Self::eq_diffvar_replay_candidates(proof, scope.problem_set, scope.record_by_after)
        {
            let mut cx = scope
                .plan_cx()
                .with_eq_diffvar_atoms(eqdv_by_atom, scope.definitions);
            let mut planner = PropagationChainPlanner {
                terms: &mut self.ctx.terms,
            };
            if let Some(conclusion) = planner.plan_derive_clause(&mut cx, term) {
                planned.insert(index, (cx.chain, conclusion));
            }
        }
    }

    /// Phase A: plan a derivation for every `fresh_def_bound` step whose atom
    /// is a LATER pass's rewrite of a minted definitional bound.
    ///
    /// Returns the plans and the set of symbol NAMES that must not be used by
    /// phase B — every symbol still bound to a definiens other than the minted
    /// one after these plans are applied.
    fn plan_eq_diffvar_definition_reclaim(
        &mut self,
        proof: &Proof,
        scope: &EqDiffVarPlanScope<'_>,
    ) -> (HashMap<usize, (Proof, ProofId)>, HashSet<String>) {
        // (step index, bound atom) grouped by the symbol the step binds.
        let mut groups: HashMap<String, Vec<(usize, TermId)>> = HashMap::default();
        let mut minted: HashSet<String> = HashSet::default();
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: AletheRule::FreshDefBound,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            let Ok(shape) = ay_core::proof_validation::recognize_fresh_def_bound(
                &self.ctx.terms,
                clause,
                premises.len(),
                args,
            ) else {
                continue;
            };
            let TermData::Var(name, _) = self.ctx.terms.get(shape.definiendum) else {
                continue;
            };
            // A step already carrying the MINTED bound needs nothing: the
            // symbol is bound to exactly the definiens phase B will use.
            if scope.definitions.get(&shape.atom) == Some(&shape.definiendum) {
                minted.insert(name.clone());
                continue;
            }
            groups
                .entry(name.clone())
                .or_default()
                .push((index, shape.atom));
        }

        let mut planned: HashMap<usize, (Proof, ProofId)> = HashMap::default();
        let mut blocked: HashSet<String> = HashSet::default();
        for (name, group) in groups {
            if minted.contains(&name) {
                // The symbol is bound BOTH ways already; the registry will
                // reject that on its own, and nothing here can improve it.
                blocked.insert(name);
                continue;
            }
            let mut group_plans = Vec::with_capacity(group.len());
            for (index, atom) in group {
                let mut cx = scope
                    .plan_cx()
                    .with_eq_diffvar_definitions(scope.definitions);
                let mut planner = PropagationChainPlanner {
                    terms: &mut self.ctx.terms,
                };
                match planner.plan_derive_clause(&mut cx, atom) {
                    Some(conclusion) => group_plans.push((index, (cx.chain, conclusion))),
                    None => {
                        group_plans.clear();
                        break;
                    }
                }
            }
            if group_plans.is_empty() {
                blocked.insert(name);
                continue;
            }
            planned.extend(group_plans);
        }
        (planned, blocked)
    }

    /// The minted definitional bound atoms, keyed to their definiendum.
    ///
    /// Looked up rather than BUILT: a bound the term store has never interned
    /// cannot appear in the proof either, so `find_app_named` answers the same
    /// question without minting a node on every call — and this runs once per
    /// proof rewrite against a store holding up to `MAX_STORED_PROPAGATION_RECORDS`
    /// folds.
    fn eq_diffvar_definition_index(&self) -> HashMap<TermId, TermId> {
        let mut index: HashMap<TermId, TermId> = HashMap::default();
        for record in &self.propagated_value_provenance.eq_diffvar_atoms {
            let (definiendum, definiens) = (record.definiendum, record.definiens);
            for operands in [[definiendum, definiens], [definiens, definiendum]] {
                if let Some(atom) = self.ctx.terms.find_app_named("<=", &operands) {
                    index.entry(atom).or_insert(definiendum);
                }
            }
        }
        index
    }

    /// Index the recorded atom folds by their AUTHORED atom, dropping every
    /// fold over a symbol phase A could not reclaim. First record wins,
    /// mirroring the other replay indexes.
    fn eq_diffvar_atom_index(
        &self,
        blocked: &HashSet<String>,
    ) -> HashMap<TermId, EqDiffVarAtomPlan> {
        let mut index: HashMap<TermId, EqDiffVarAtomPlan> = HashMap::default();
        for record in &self.propagated_value_provenance.eq_diffvar_atoms {
            let TermData::Var(name, _) = self.ctx.terms.get(record.definiendum) else {
                continue;
            };
            if blocked.contains(name) {
                continue;
            }
            index.entry(record.atom).or_insert(EqDiffVarAtomPlan {
                replacement: record.replacement,
                definiendum: record.definiendum,
                definiens: record.definiens,
                stamp: record.stamp,
            });
        }
        index
    }

    /// Premiseless unit `trust` steps whose clause term has a recorded rewrite.
    fn eq_diffvar_replay_candidates(
        proof: &Proof,
        problem_set: &HashSet<TermId>,
        record_by_after: &HashMap<TermId, (TermId, u32)>,
    ) -> Vec<(usize, TermId)> {
        let mut candidates = Vec::new();
        for (index, step) in proof.steps.iter().enumerate() {
            if candidates.len() >= MAX_EQ_DIFFVAR_CANDIDATES {
                break;
            }
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            let [term] = clause.as_slice() else {
                continue;
            };
            if !premises.is_empty()
                || !args.is_empty()
                || problem_set.contains(term)
                || !record_by_after.contains_key(term)
            {
                continue;
            }
            candidates.push((index, *term));
        }
        candidates
    }
}

/// The shared, read-only inputs every plan in this lane is built against.
///
/// Bundled rather than passed positionally: the two phases need the same five
/// references, and threading them individually is what an
/// `allow(clippy::too_many_arguments)` would have been papering over.
struct EqDiffVarPlanScope<'a> {
    problem_set: &'a HashSet<TermId>,
    problem_assertions: &'a [TermId],
    record_by_after: &'a HashMap<TermId, (TermId, u32)>,
    entry_by_expr: &'a HashMap<TermId, (TermId, TermId, u32)>,
    definitions: &'a HashMap<TermId, TermId>,
}

impl<'a> EqDiffVarPlanScope<'a> {
    fn plan_cx(&self) -> PlanCx<'a> {
        PlanCx::new(
            self.problem_set,
            self.problem_assertions,
            self.record_by_after,
            self.entry_by_expr,
            &[],
            false,
        )
    }
}
