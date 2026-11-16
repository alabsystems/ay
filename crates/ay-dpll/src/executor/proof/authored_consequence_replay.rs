// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored consequence-replay UNSAT translation (#consequence-replay).
//!
//! THE GAP THIS CLOSES. The CEGQI/enumerative quantifier lanes derive genuine
//! refutations whose live proofs the mandatory strict gate rightly refuses: a
//! guarded-implication instance leaves a `trust` closer the flat arithmetic
//! `forall_inst` lane cannot discharge (its instance shape pre-filter admits
//! only bare comparisons), and the array/seq instance lane produces no proof
//! object at all. Twelve group_quantifiers rows lost their correct `unsat` to
//! exactly this — the engine solved, publication starved.
//!
//! THE FIX IS A DERIVATION, NOT A RELAXATION. Every write-side instance
//! chokepoint already records `ForallInstantiationProvenance`
//! (`EmatchingProofRecord`: source quantifier, positional binder values, exact
//! substituted instance) after the proof tracker independently replayed the
//! substitution. The consequence set
//!
//! ```text
//! { quantifier-free `and`-conjuncts of the authored roots }
//!   ∪ { recorded exact instances of authored universals }
//! ```
//!
//! consists solely of sound consequences of the authored problem, and when the
//! engine's refutation is real that set is UNSAT on its own. This producer:
//!
//! 1. first tries a proof-only ground shortcut: a closed FP instance is
//!    discharged by exact IEEE-754 evaluation, or an exact instance plus
//!    authored literal-valued equality pins by checked equality substitution
//!    and closed `evaluate`; otherwise it re-solves the
//!    consequence set on a SAME-CONTEXT disposable probe
//!    ([`Executor::checked_same_context_unsat_proof`]) whose own strict checker
//!    must accept its complete proof over the probe window;
//! 2. stitches that proof onto authored-scope derivations — each probe
//!    `assume` is replaced by an authored `assume`, an `and_pos` conjunct
//!    projection chain, or an `assume`→`forall_inst`→`or`→`resolution`
//!    prologue minted from the recorded provenance;
//! 3. commits only through the ordinary strict gates: reachable-assume scope
//!    authorization over the EXACT authored roots, empty-clause derivation,
//!    and `check_proof_strict_with_datatypes` complete.
//!
//! NOTHING IS TAKEN ON THE PRODUCER'S WORD. The binder values, instances, and
//! the probe's whole derivation are hints the outer checker re-decides: the
//! strict `forall_inst` validator re-derives arity, sorts, groundness, and the
//! exact simultaneous substitution; `and_pos` re-checks the indexed conjunct;
//! every theory lemma is replayed. A mis-recorded provenance or a divergent
//! probe artifact can only cost a declined candidate — the verdict stays the
//! fail-closed `unknown` it already was.
//!
//! UNSAT-ONLY: no arm of this lane can produce or influence a SAT grant, so
//! the staged-grant rule does not apply. `--no-consequence-replay` disables every
//! entry point and restores the baseline `unknown`s byte-for-byte.

use super::*;

mod anchored_instances;
mod closed_fp_forall;
mod congruence;
mod ground_pin;
mod guarded_clausal;
mod implied_ground_inst;
mod probe_conjunct;
mod probe_ite_lift;
mod skeleton_refutation;
mod types;

use types::{AndConjunctClosure, ConsequencePlan};
pub(in crate::executor) use types::{
    ClausalInstanceRecord, ClausalLiteral, ExpansionStep, ImpliedForall, NegatedExistsDual,
    QuantifierJoinRecord,
};

/// Authored-scope size beyond which this lane declines.
const MAX_AUTHORED_ROOTS: usize = 64;
/// Cap on the consequence-set size handed to the probe.
const MAX_CONSEQUENCES: usize = 256;
/// Cap on recorded instances admitted into the plan.
const MAX_INSTANCES: usize = 64;
/// Cap on bounded ground probes; retries of a declined set must not re-pay it.
const MAX_REPLAY_ATTEMPTS: u8 = 2;
/// Distinct direct ground-pin record sets tried per public query.
const MAX_DIRECT_REPLAY_ATTEMPTS: u8 = 4;
/// Node budget for each `and`-conjunct path search.
const MAX_AND_PATH_WORK: usize = 4_096;
/// Step budget for the stitched candidate.
const MAX_PROBE_PROOF_STEPS: usize = 50_000;

/// Shape of the finalized consequence-producing plan.
///
/// A negated-exists dual is only source authority for a forall instance, and a
/// negative Skolem record uses the historical replay budget. Any positive
/// Skolem record changes the shape; finite-frame replay motivates its extended
/// allowance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConsequenceReplayPlanShape {
    Standard,
    PositiveSkolem,
}

impl ConsequenceReplayPlanShape {
    fn classify(plans: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>) -> Self {
        for plan in plans.values() {
            match plan {
                ConsequencePlan::ForallInstance { .. }
                | ConsequencePlan::NegatedExistsDual { .. }
                | ConsequencePlan::ImpliedConsequent { .. }
                | ConsequencePlan::ClausalInstance { .. }
                | ConsequencePlan::QuantifierJoin { .. }
                | ConsequencePlan::CongruenceEquality { .. }
                | ConsequencePlan::SkolemInstance {
                    positive: false, ..
                } => {}
                ConsequencePlan::SkolemInstance { positive: true, .. } => {
                    return Self::PositiveSkolem;
                }
            }
        }
        Self::Standard
    }

    const fn probe_budget(self) -> ConsequenceReplayProbeBudget {
        match self {
            Self::Standard => ConsequenceReplayProbeBudget::TwoSeconds,
            Self::PositiveSkolem => ConsequenceReplayProbeBudget::FiveSeconds,
        }
    }
}

/// Wall-clock allowance for one disposable consequence-replay solve.
///
/// Forall, dual-source, and negative-Skolem plans keep the historical
/// two-second cap in every presentation posture. The positive-Skolem plan used
/// by finite-frame replay gets five seconds because that proof can need more
/// than two seconds in dev/test. Either timeout only declines this producer;
/// it never grants a verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ConsequenceReplayProbeBudget {
    TwoSeconds,
    FiveSeconds,
}

impl ConsequenceReplayProbeBudget {
    /// The probe's ceiling in both currencies (`ProbeCap`): the counted
    /// grant it normally stops at, and the wall backstop named here.
    const fn cap(self) -> consequence_replay_budget::ProbeCap {
        match self {
            Self::TwoSeconds => consequence_replay_budget::ProbeCap::STANDARD,
            Self::FiveSeconds => consequence_replay_budget::ProbeCap::POSITIVE_SKOLEM,
        }
    }

    #[cfg(test)]
    const fn milliseconds(self) -> u64 {
        self.cap().wall_ms
    }
}

/// Which gate of [`Executor::install_strict_authored_candidate`] refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum InstallRefusal {
    /// A reachable `assume` is not an exact authored root.
    Scope,
    /// The candidate does not derive the empty clause.
    EmptyClause,
    /// The strict checker rejected a step.
    Strict,
    /// The strict checker accepted but reported the proof incomplete.
    Incomplete,
    /// The internal proof check (or a self-check without it) refused.
    InternalCheck,
}

impl InstallRefusal {
    pub(in crate::executor) fn label(self) -> &'static str {
        match self {
            Self::Scope => "install-scope",
            Self::EmptyClause => "install-empty-clause",
            Self::Strict => "install-strict",
            Self::Incomplete => "install-incomplete",
            Self::InternalCheck => "install-internal-check",
        }
    }
}

/// The authored-scope context `consequence_unit` derivations draw on,
/// bundled so discharge helpers stay inside the argument budget.
struct ConsequenceScope<'a> {
    authored_set: &'a ay_core::kani_compat::DetHashSet<TermId>,
    authored: &'a [TermId],
    instance_plan: &'a ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
    unit_ids: &'a mut ay_core::kani_compat::DetHashMap<TermId, ProofId>,
}

/// One planned negated-exists dual to derive: clause-shaped `root`, its
/// existential, the dual `forall`, and the units discharging its other
/// clause literals (empty for a bare `(not E)` root).
struct NegatedDualRequest<'a> {
    root: TermId,
    exists: TermId,
    forall: TermId,
    co_units: &'a [TermId],
}

/// `--trace-cegqi-attr`-gated decline attribution, matching the CEGQI
/// disambiguation trace this lane feeds. Diagnostic only.
pub(super) fn replay_note(message: impl FnOnce() -> String) {
    if ay_core::misc_cli_flags().trace_cegqi_attr {
        eprintln!("[consequence-replay] {}", message());
    }
}

fn collect_consequence_set(
    terms: &TermStore,
    derivable_sources: &AndConjunctClosure,
    instances: &[TermId],
) -> Option<Vec<TermId>> {
    let mut consequences = Vec::new();
    for &conjunct in &derivable_sources.ordered {
        if consequences.len() > MAX_CONSEQUENCES {
            return None;
        }
        if !crate::ematching::contains_quantifier(terms, conjunct)
            && !consequences.contains(&conjunct)
        {
            consequences.push(conjunct);
        }
    }
    for &instance in instances {
        if consequences.len() > MAX_CONSEQUENCES {
            return None;
        }
        if !consequences.contains(&instance) {
            consequences.push(instance);
        }
    }
    (!consequences.is_empty()).then_some(consequences)
}

impl Executor {
    /// Translate the current quantified refutation into an authored-scope
    /// strict proof and install it as `last_proof`.
    ///
    /// Entry point for the proof-less path (the array/seq instance lane emits
    /// no proof object): called by the CEGQI UNSAT certification
    /// (`cegqi_unsat_authority::certify`) before the proof-suppressed
    /// verdict-only certificate. Returns `true` only when a complete,
    /// scope-authorized, strictly checked certificate was installed; on
    /// `false` all proof state is left exactly as found.
    pub(in crate::executor) fn try_translate_authored_consequence_replay_unsat(&mut self) -> bool {
        self.try_translate_authored_consequence_replay_unsat_with(&[])
    }

    /// Like [`Self::try_translate_authored_consequence_replay_unsat_with`],
    /// additionally admitting NEGATED-EXISTENTIAL DUAL universals as instance
    /// sources (see [`NegatedExistsDual`]). Used by the ground-instantiation
    /// lane; the duals carry no authority of their own — each one's authored
    /// `(not (exists ...))` source must be derivable, and the emitted
    /// `qnt_neg_exists` step is re-derived by the strict checker.
    /// Like [`Self::try_translate_authored_consequence_replay_unsat_with`],
    /// additionally admitting the CONSEQUENT of an authored implication whose
    /// antecedent is itself derivable as an instance source
    /// (see [`ImpliedForall`], #implied-forall-ground-inst). The records carry
    /// no authority: `consequence_unit` must derive both the implication root
    /// and its antecedent from the authored scope, the emitted `implies_pos`
    /// step is re-derived by the strict checker from the implication's own
    /// structure, and `validate_forall_inst_with_progress` re-replays every substitution.
    pub(in crate::executor) fn try_translate_authored_consequence_replay_unsat_with_implied(
        &mut self,
        extra_records: &[crate::ematching::ForallInstantiationProvenance],
        extra_implied: &[ImpliedForall],
    ) -> bool {
        let candidate = self.build_authored_consequence_replay_refutation(
            extra_records,
            &[],
            extra_implied,
            &[],
            &[],
            &[],
        );
        self.install_consequence_replay_candidate(candidate)
    }

    /// [`Self::try_translate_authored_consequence_replay_unsat_with_duals`]
    /// plus clause-shaped sources ([`ClausalInstanceRecord`]): authored
    /// `(or …)` / `(not (and …))` conjuncts whose universal literals the
    /// caller instantiated. Used by the QSAT route.
    pub(in crate::executor) fn try_translate_authored_consequence_replay_unsat_with_clauses(
        &mut self,
        extra_records: &[crate::ematching::ForallInstantiationProvenance],
        extra_duals: &[NegatedExistsDual],
        extra_skolem: &[crate::executor::SkolemInstanceRecord],
        extra_clausal: &[ClausalInstanceRecord],
        extra_chain: &[ExpansionStep],
    ) -> bool {
        let candidate = self.build_authored_consequence_replay_refutation(
            extra_records,
            extra_duals,
            &[],
            extra_skolem,
            extra_clausal,
            extra_chain,
        );
        self.install_consequence_replay_candidate(candidate)
    }

    /// `extra_skolem` supplies positive-existential Skolem provenance the
    /// caller rebuilt from the persistent choice registry
    /// (`authored_positive_exists_skolem_records`); each record carries no
    /// authority — its source must be derivable and the strict `Skolem`
    /// (`sko_ex`) validator re-authenticates binder, sort, body and the exact
    /// substitution against the registry.
    pub(in crate::executor) fn try_translate_authored_consequence_replay_unsat_with_duals(
        &mut self,
        extra_records: &[crate::ematching::ForallInstantiationProvenance],
        extra_duals: &[NegatedExistsDual],
        extra_skolem: &[crate::executor::SkolemInstanceRecord],
    ) -> bool {
        let candidate = self.build_authored_consequence_replay_refutation(
            extra_records,
            extra_duals,
            &[],
            extra_skolem,
            &[],
            &[],
        );
        self.install_consequence_replay_candidate(candidate)
    }

    /// Like [`Self::try_translate_authored_consequence_replay_unsat`], with
    /// caller-supplied additional instance provenance (e.g. the closed
    /// universal literal-witness lane's exact refuting tuple). Extra records
    /// carry no authority: their source universal must still be derivable
    /// from the authored scope, and the strict `forall_inst` validator
    /// re-derives the exact substitution on the stitched candidate.
    pub(in crate::executor) fn try_translate_authored_consequence_replay_unsat_with(
        &mut self,
        extra_records: &[crate::ematching::ForallInstantiationProvenance],
    ) -> bool {
        let candidate = self.build_authored_consequence_replay_refutation(
            extra_records,
            &[],
            &[],
            &[],
            &[],
            &[],
        );
        self.install_consequence_replay_candidate(candidate)
    }

    /// Shared installation boundary: re-gate a built candidate over the exact
    /// authored scope and install it as `last_proof`, or leave every byte of
    /// proof state as found. Also the boundary ground-first scheduling installs
    /// a same-context ground refutation through (`check_sat/ground_first.rs`).
    pub(in crate::executor) fn install_consequence_replay_candidate(
        &mut self,
        candidate: Option<Proof>,
    ) -> bool {
        let Some(candidate) = candidate else {
            return false;
        };
        match self.install_strict_authored_candidate(candidate) {
            Ok(()) => true,
            Err(refusal) => {
                replay_note(|| format!("decline: installation boundary refused ({refusal:?})"));
                false
            }
        }
    }

    /// THE strict installation boundary for a stitched authored-scope
    /// refutation (consequence replay, and the nested-CEGQI expansion
    /// certificate): reachable-assume scope authorization over the EXACT
    /// authored roots, empty-clause derivation,
    /// `check_proof_strict_with_datatypes` complete, and the internal proof
    /// check. Installs the candidate as `last_proof` with its checker
    /// lifecycle state, or leaves every byte of proof state as found and says
    /// which gate refused.
    pub(in crate::executor::proof) fn install_strict_authored_candidate(
        &mut self,
        candidate: Proof,
    ) -> Result<(), InstallRefusal> {
        let authored = self.exact_concrete_authored_scope();
        let scope = ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored);
        if scope.is_err() {
            replay_note(|| {
                format!("decline: stitched candidate failed the scope pre-gate ({scope:?})")
            });
            return Err(InstallRefusal::Scope);
        }
        if !Self::proof_derives_empty_clause(&candidate) {
            replay_note(|| "decline: stitched candidate derives no empty clause".into());
            return Err(InstallRefusal::EmptyClause);
        }
        let quality = match self.check_proof_strict_with_datatypes(&candidate) {
            Ok(quality) => quality,
            Err(error) => {
                replay_note(|| {
                    let strict = self.problem_assertions_for_strict_proof();
                    format!(
                        "decline: outer strict check refused: {error} (authored={authored:?} strict={strict:?})"
                    )
                });
                return Err(InstallRefusal::Strict);
            }
        };
        if !quality.is_complete() {
            return Err(InstallRefusal::Incomplete);
        }

        // Install the checker lifecycle state together with the proof,
        // mirroring the ordinary `build_unsat_proof` installation boundary
        // and the `try_translate_*` siblings; a checker disagreement can only
        // decline the translation.
        let saved_proof_check_result = self.proof_check_result.clone();
        let saved_proof_check_ok = self.proof_check_ok;
        let saved_proof_quality = self.last_proof_quality.clone();
        let saved_statistics = self.last_statistics.clone();
        self.proof_check_result = None;
        self.proof_check_ok = false;
        self.last_proof_quality = None;
        #[cfg(feature = "proof-checker")]
        {
            self.run_internal_proof_check(&candidate);
            if !self.proof_check_ok {
                replay_note(|| {
                    format!(
                        "decline: internal proof check refused ({:?})",
                        self.proof_check_result
                    )
                });
                self.proof_check_result = saved_proof_check_result;
                self.proof_check_ok = saved_proof_check_ok;
                self.last_proof_quality = saved_proof_quality;
                self.last_statistics = saved_statistics;
                return Err(InstallRefusal::InternalCheck);
            }
        }
        #[cfg(not(feature = "proof-checker"))]
        if self.self_check() {
            replay_note(|| "decline: self-check without proof-checker feature".into());
            self.proof_check_result = saved_proof_check_result;
            self.proof_check_ok = saved_proof_check_ok;
            self.last_proof_quality = saved_proof_quality;
            self.last_statistics = saved_statistics;
            return Err(InstallRefusal::InternalCheck);
        }
        self.populate_proof_quality_stats(&quality);
        self.last_proof_quality = Some(quality);
        self.last_unsat_proof_reconstruction_suppressed = false;
        self.last_proof = Some(candidate);
        Ok(())
    }

    /// Whether `last_proof` already holds a COMPLETE strict authored-scope
    /// refutation — e.g. the cascade member below committed a stitched
    /// consequence-replay candidate during the live proof build
    /// (#ground-conflict-decomp). Everything is re-validated at this exact
    /// moment (reachable-assume scope over the exact authored roots,
    /// empty-clause derivation, and the full strict check), so a stale or
    /// foreign proof can only decline; publication re-checks the same proof
    /// again at certificate-mint time. UNSAT-only, covered by
    /// `--no-consequence-replay` at the call site.
    pub(in crate::executor) fn authored_scope_strict_proof_installed(&mut self) -> bool {
        let Some(candidate) = self.last_proof.clone() else {
            return false;
        };
        let authored = self.exact_concrete_authored_scope();
        ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
    }

    /// Cascade member: rebuild a trust-rejected (or unrepairable) proof as the
    /// consequence-replay refutation when one applies.
    ///
    /// Fail-closed exactly like its `authored_*` siblings: runs only on a
    /// proof the strict checker already rejects; the candidate is committed
    /// only through the shared strict gate over the exact authored scope.
    pub(super) fn replace_with_authored_consequence_replay_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let Some(candidate) =
            self.build_authored_consequence_replay_refutation(&[], &[], &[], &[], &[], &[])
        else {
            return;
        };
        if !self.candidate_authored_surface_is_available(&candidate) {
            replay_note(|| "cascade decline: authored source restoration unavailable".into());
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        let committed = self.commit_if_strictly_checked(proof, candidate, &authored);
        replay_note(|| format!("cascade commit: {committed}"));
    }

    /// Build (but do not install) the stitched authored-scope refutation.
    ///
    /// `None` on any decline: kill switch off, attempt budget exhausted, no
    /// recorded instance to add (a pure-ground problem must not be re-solved
    /// here), an underivable consequence, a probe that cannot produce a
    /// strict-complete proof, or a stitch that fails a bound.
    ///
    /// `extra_duals` supplies an additional class of derivable instance SOURCE
    /// — the De Morgan dual of an authored `(not (exists ...))` root — and is
    /// empty for every caller but the ground-instantiation lane.
    fn build_authored_consequence_replay_refutation(
        &mut self,
        extra_records: &[crate::ematching::ForallInstantiationProvenance],
        extra_duals: &[NegatedExistsDual],
        extra_implied: &[ImpliedForall],
        extra_skolem: &[crate::executor::SkolemInstanceRecord],
        extra_clausal: &[ClausalInstanceRecord],
        extra_chain: &[ExpansionStep],
    ) -> Option<Proof> {
        if !crate::quant_unit_authority::consequence_replay_enabled() {
            return None;
        }
        let attempts = self.consequence_replay_attempts.get();
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return None;
        }
        // The checker authorizes an `assume` only for an exact authored root;
        // conjuncts and universals nested under a top-level conjunction are
        // reached by explicit `and_pos` projection instead, so the exported
        // document still matches the problem file's premises syntactically.
        let derivable_sources = self.authored_and_conjunct_closure(&authored);

        // Instance plan: exact recorded provenance whose source universal is
        // itself derivable and whose instance is ground. The records were
        // admitted only after the proof tracker independently replayed the
        // substitution; the strict `forall_inst` validator re-replays it
        // again on the stitched candidate.
        let mut instance_plan: ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan> =
            ay_core::kani_compat::DetHashMap::default();
        let mut instances: Vec<TermId> = Vec::new();

        // Negated-existential duals FIRST: they are instance SOURCES, not
        // consequences, so they never enter the probe's assertion vector.
        let dual_foralls =
            Self::plan_negated_exists_duals(extra_duals, &derivable_sources, &mut instance_plan);
        // Implication consequents: a SOURCE, never a consequence.
        let implied_foralls =
            Self::plan_implied_foralls(extra_implied, &derivable_sources, &mut instance_plan);

        let recorded = extra_records
            .iter()
            .map(|record| (record.quantifier, &record.binding, record.instance))
            .chain(
                self.ematching_proof_records
                    .iter()
                    .map(|record| (record.quantifier, &record.binding, record.instance)),
            );
        for (quantifier, binding, instance) in recorded {
            if instances.len() >= MAX_INSTANCES {
                break;
            }
            if !(derivable_sources.contains(&quantifier)
                || dual_foralls.contains(&quantifier)
                || implied_foralls.contains(&quantifier))
                || instance == quantifier
                || crate::ematching::contains_quantifier(&self.ctx.terms, instance)
                || instance_plan.contains_key(&instance)
            {
                continue;
            }
            instance_plan.insert(
                instance,
                ConsequencePlan::ForallInstance {
                    quantifier,
                    binding: binding.clone(),
                },
            );
            instances.push(instance);
        }
        // Single-binder Skolemization provenance (#skolem-unit-authority):
        // the asserted skolemized instance is a sound consequence of its
        // authored `exists` / `not (forall ...)` source, derivable with the
        // strict `sko_forall` chain the c5 fragment channel already emits.
        // `extra_skolem` (registry-rebuilt positive records) after the live
        // ones: the live record for the same witness, when present, wins the
        // `instance_plan` slot and the extra is a no-op.
        let skolem_records: Vec<crate::executor::SkolemInstanceRecord> = self
            .skolem_instance_records
            .iter()
            .chain(extra_skolem)
            .cloned()
            .collect();
        for record in skolem_records {
            if instances.len() >= MAX_INSTANCES {
                break;
            }
            if !derivable_sources.contains(&record.source)
                || crate::ematching::contains_quantifier(&self.ctx.terms, record.asserted)
                || instance_plan.contains_key(&record.asserted)
            {
                continue;
            }
            instance_plan.insert(
                record.asserted,
                ConsequencePlan::SkolemInstance {
                    source: record.source,
                    quantified: record.quantified,
                    witness: record.witness,
                    instance: record.instance,
                    positive: record.positive,
                },
            );
            instances.push(record.asserted);
        }
        // Clause-shaped sources with instantiated universal literals: the
        // source must be derivable; the consequence must be quantifier-free.
        for record in extra_clausal {
            if instances.len() >= MAX_INSTANCES {
                break;
            }
            if !derivable_sources.contains(&record.source)
                || crate::ematching::contains_quantifier(&self.ctx.terms, record.consequence)
                || instance_plan.contains_key(&record.consequence)
            {
                continue;
            }
            instance_plan.insert(
                record.consequence,
                ConsequencePlan::ClausalInstance {
                    source: record.source,
                    literals: record.literals.clone(),
                },
            );
            instances.push(record.consequence);
        }
        // Guarded instance clauses (#quantifier-guarded-instances): their
        // resolvent on the proxy against each authored clause that carries the
        // guarded universal as a literal.
        self.plan_guarded_clausal_instances(
            &derivable_sources,
            &mut instance_plan,
            &mut instances,
            MAX_INSTANCES,
        );
        // Instantiation / Skolemization chains, in dependency order: a step's
        // source must be derivable or an earlier step's output; quantified
        // outputs are planned but never handed to the ground probe.
        for step in extra_chain {
            let planned_or_derivable =
                |term: &TermId,
                 plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>| {
                    derivable_sources.contains(term) || plan.contains_key(term)
                };
            match step {
                ExpansionStep::Dual(dual) => {
                    if !planned_or_derivable(&dual.not_exists_root, &instance_plan)
                        || instance_plan.contains_key(&dual.forall)
                    {
                        continue;
                    }
                    instance_plan.insert(
                        dual.forall,
                        ConsequencePlan::NegatedExistsDual {
                            not_exists_root: dual.not_exists_root,
                            exists: dual.exists,
                            co_units: dual.co_units.clone(),
                        },
                    );
                }
                ExpansionStep::Forall(record) => {
                    if !planned_or_derivable(&record.quantifier, &instance_plan)
                        || record.instance == record.quantifier
                        || instance_plan.contains_key(&record.instance)
                    {
                        continue;
                    }
                    instance_plan.insert(
                        record.instance,
                        ConsequencePlan::ForallInstance {
                            quantifier: record.quantifier,
                            binding: record.binding.clone(),
                        },
                    );
                    if !crate::ematching::contains_quantifier(&self.ctx.terms, record.instance) {
                        instances.push(record.instance);
                    }
                }
                ExpansionStep::Join(join) => {
                    let derived = join.derived(&mut self.ctx.terms);
                    if !planned_or_derivable(&join.source, &instance_plan)
                        || instance_plan.contains_key(&derived)
                    {
                        continue;
                    }
                    instance_plan.insert(
                        derived,
                        ConsequencePlan::QuantifierJoin {
                            source: join.source,
                            joined: join.joined,
                            nested: join.nested,
                            positive: join.positive,
                        },
                    );
                }
                ExpansionStep::Skolem(record) => {
                    if !planned_or_derivable(&record.source, &instance_plan)
                        || instance_plan.contains_key(&record.asserted)
                    {
                        continue;
                    }
                    instance_plan.insert(
                        record.asserted,
                        ConsequencePlan::SkolemInstance {
                            source: record.source,
                            quantified: record.quantified,
                            witness: record.witness,
                            instance: record.instance,
                            positive: record.positive,
                        },
                    );
                    if !crate::ematching::contains_quantifier(&self.ctx.terms, record.asserted) {
                        instances.push(record.asserted);
                    }
                }
                ExpansionStep::Implied {
                    implication,
                    antecedent,
                    consequent,
                } => {
                    if !planned_or_derivable(implication, &instance_plan)
                        || instance_plan.contains_key(consequent)
                    {
                        continue;
                    }
                    instance_plan.insert(
                        *consequent,
                        ConsequencePlan::ImpliedConsequent {
                            implication: *implication,
                            antecedent: *antecedent,
                        },
                    );
                    if !crate::ematching::contains_quantifier(&self.ctx.terms, *consequent) {
                        instances.push(*consequent);
                    }
                }
                ExpansionStep::Congruence { equality } => {
                    if instance_plan.contains_key(equality)
                        || crate::ematching::contains_quantifier(&self.ctx.terms, *equality)
                    {
                        continue;
                    }
                    instance_plan.insert(
                        *equality,
                        ConsequencePlan::CongruenceEquality {
                            equality: *equality,
                        },
                    );
                    instances.push(*equality);
                }
            }
        }
        if instances.is_empty() {
            // Nothing this lane can add over the plain ground problem. (A
            // dual with no instance is a source without a consequence, which
            // is exactly the pure-ground case this guard refuses.)
            replay_note(|| {
                format!(
                    "decline: no derivable recorded instance ({} records)",
                    self.ematching_proof_records.len()
                )
            });
            return None;
        }

        // Quantifier-free authored conjuncts first, then recorded instances.
        let consequences =
            collect_consequence_set(&self.ctx.terms, &derivable_sources, &instances)?;

        if let candidate @ Some(_) = self.try_distinct_ground_pin(&instance_plan, &instances) {
            return candidate;
        }

        // The dual and implied-universal lanes carry their own per-check-sat
        // attempt budgets (`MAX_LANE_ATTEMPTS`, one probe each) and propose an
        // instance set the plain replay has never seen, so the plain lane's
        // exhausted retry cap must not starve them: on the deductive-checks
        // `seq_contains` shape two identical plain replays of the lone Skolem
        // instance failed first, then silently refused the dual's refuting
        // probe here (#negated-exists-cegqi-witness-hints). The total probe
        // count per check-sat stays bounded by the sum of the three caps.
        // Chain-carrying lanes (QSAT, exists-bridge, ground-inst) each
        // hold their own per-check-sat attempt caps, like the dual and
        // implied lanes.
        let carries_own_budget =
            !extra_duals.is_empty() || !extra_implied.is_empty() || !extra_chain.is_empty();
        if attempts >= MAX_REPLAY_ATTEMPTS && !carries_own_budget {
            replay_note(|| "decline: replay attempt budget exhausted".into());
            return None;
        }

        replay_note(|| {
            format!(
                "plan: {} forall-instance, {} skolem-instance records ({} ematching, {} skolem, {} extra)",
                instance_plan
                    .values()
                    .filter(|plan| matches!(plan, ConsequencePlan::ForallInstance { .. }))
                    .count(),
                instance_plan
                    .values()
                    .filter(|plan| matches!(plan, ConsequencePlan::SkolemInstance { .. }))
                    .count(),
                self.ematching_proof_records.len(),
                self.skolem_instance_records.len(),
                extra_records.len(),
            )
        });
        replay_note(|| {
            let rendered: Vec<String> = consequences
                .iter()
                .map(|&c| format!("(assert {})", self.format_term(c)))
                .collect();
            format!("consequences:\n{}", rendered.join("\n"))
        });
        // One attempt is consumed whether or not the probe succeeds.
        self.consequence_replay_attempts.set(attempts + 1);
        let budget = ConsequenceReplayPlanShape::classify(&instance_plan).probe_budget();
        if let stitched @ Some(_) = self
            .try_anchored_consequence_replay(
                &consequences,
                &instance_plan,
                &derivable_sources,
                &authored,
                budget.cap(),
            )
            .ok()?
        {
            return stitched;
        }
        let Some(probe_proof) = self.metered_consequence_replay_probe(&consequences, budget.cap())
        else {
            replay_note(|| {
                format!(
                    "decline: same-context probe produced no strict UNSAT proof \
                     ({} consequences, {} instances)",
                    consequences.len(),
                    instances.len()
                )
            });
            return None;
        };
        let stitched = self.stitch_consequence_replay(&probe_proof, &authored, &instance_plan);
        if stitched.is_none() {
            replay_note(|| {
                format!(
                    "decline: stitch failed over {} probe steps",
                    probe_proof.steps.len()
                )
            });
        }
        stitched
    }

    /// Derive the unit clause `(cl term)` for a PLANNED consequence — one the
    /// authored scope does not assume directly. Each arm recursively derives
    /// its own source's unit first, so a plan may chain (a dual universal's
    /// instance rests on the dual, which rests on the authored `(not E)`).
    #[allow(clippy::too_many_arguments)]
    fn planned_consequence_unit(
        &mut self,
        candidate: &mut Proof,
        term: TermId,
        plan: ConsequencePlan,
        authored_set: &ay_core::kani_compat::DetHashSet<TermId>,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        unit_ids: &mut ay_core::kani_compat::DetHashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        // A congruence equality has no single source unit: its premises
        // are the argument equalities, derived recursively.
        if let ConsequencePlan::CongruenceEquality { .. } = plan {
            return self.add_congruence_equality_unit(
                candidate,
                term,
                &mut ConsequenceScope {
                    authored_set,
                    authored,
                    instance_plan,
                    unit_ids,
                },
            );
        }
        let source = plan.source();
        let source_unit = self.consequence_unit(
            candidate,
            source,
            authored_set,
            authored,
            instance_plan,
            unit_ids,
        )?;
        self.dispatch_planned_consequence(
            candidate,
            term,
            plan,
            source_unit,
            &mut ConsequenceScope {
                authored_set,
                authored,
                instance_plan,
                unit_ids,
            },
        )
    }

    /// Emit the planned consequence's derivation from its source unit.
    fn dispatch_planned_consequence(
        &mut self,
        candidate: &mut Proof,
        term: TermId,
        plan: ConsequencePlan,
        source_unit: ProofId,
        scope: &mut ConsequenceScope<'_>,
    ) -> Option<ProofId> {
        match plan {
            ConsequencePlan::ForallInstance {
                quantifier,
                binding,
            } => self.add_forall_instance_values_from_unit(
                candidate,
                source_unit,
                quantifier,
                &binding,
                term,
            ),
            ConsequencePlan::SkolemInstance {
                quantified,
                witness,
                instance,
                positive,
                ..
            } => self.add_skolem_instance_from_unit(
                candidate,
                source_unit,
                quantified,
                witness,
                instance,
                positive,
                term,
            ),
            ConsequencePlan::NegatedExistsDual {
                not_exists_root,
                exists,
                co_units,
            } => self.add_negated_exists_dual_unit(
                candidate,
                source_unit,
                NegatedDualRequest {
                    root: not_exists_root,
                    exists,
                    forall: term,
                    co_units: &co_units,
                },
                scope,
            ),
            ConsequencePlan::ClausalInstance { source, literals } => {
                self.add_clausal_instance_from_unit(candidate, source_unit, source, &literals, term)
            }
            ConsequencePlan::QuantifierJoin {
                joined,
                nested,
                positive,
                ..
            } => self.add_quantifier_join_from_unit(
                candidate,
                source_unit,
                joined,
                nested,
                positive,
                term,
            ),
            ConsequencePlan::ImpliedConsequent {
                implication,
                antecedent,
            } => self.add_implied_consequent_unit(
                candidate,
                source_unit,
                implication,
                antecedent,
                term,
                scope.authored_set,
                scope.authored,
                scope.instance_plan,
                scope.unit_ids,
            ),
            // Handled before source derivation above.
            ConsequencePlan::CongruenceEquality { .. } => None,
        }
    }

    /// Admit the negated-existential duals as instance SOURCES and return the
    /// set of dual universals the instance planner may then draw on.
    ///
    /// A dual carries NO authority: its authored `(not (exists ...))` root must
    /// itself be derivable from the authored scope, and `consequence_unit`
    /// mints `(cl F)` only through a `qnt_neg_exists` + `resolution` pair the
    /// strict checker re-derives from `E` itself.
    fn plan_negated_exists_duals(
        extra_duals: &[NegatedExistsDual],
        derivable_sources: &AndConjunctClosure,
        instance_plan: &mut ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
    ) -> ay_core::kani_compat::DetHashSet<TermId> {
        let mut dual_foralls: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        for dual in extra_duals {
            if !derivable_sources.contains(&dual.not_exists_root)
                || instance_plan.contains_key(&dual.forall)
            {
                continue;
            }
            instance_plan.insert(
                dual.forall,
                ConsequencePlan::NegatedExistsDual {
                    not_exists_root: dual.not_exists_root,
                    exists: dual.exists,
                    co_units: dual.co_units.clone(),
                },
            );
            dual_foralls.insert(dual.forall);
        }
        dual_foralls
    }

    /// Replace every probe `assume` with an authored-scope derivation and
    /// re-index the remaining steps.
    ///
    /// `ProofId`s are positional, and the probe's steps were built append-only,
    /// so every premise points backward; a forward or unmapped premise, an
    /// anchor/subproof, or an underivable assumed formula declines the stitch.
    fn stitch_consequence_replay(
        &mut self,
        probe: &Proof,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
    ) -> Option<Proof> {
        if probe.steps.len() > MAX_PROBE_PROOF_STEPS {
            return None;
        }
        let authored_set: ay_core::kani_compat::DetHashSet<TermId> =
            authored.iter().copied().collect();
        let mut candidate = Proof::new();
        let mut unit_ids: ay_core::kani_compat::DetHashMap<TermId, ProofId> =
            ay_core::kani_compat::DetHashMap::default();
        let mut remap: Vec<Option<ProofId>> = vec![None; probe.steps.len()];
        for (index, step) in probe.steps.iter().enumerate() {
            let mapped = match step {
                ProofStep::Assume(term) => self.consequence_unit(
                    &mut candidate,
                    *term,
                    &authored_set,
                    authored,
                    instance_plan,
                    &mut unit_ids,
                )?,
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => {
                    let clause1 = remap.get(clause1.0 as usize).copied().flatten()?;
                    let clause2 = remap.get(clause2.0 as usize).copied().flatten()?;
                    candidate.add_resolution(clause.clone(), *pivot, clause1, clause2)
                }
                ProofStep::TheoryLemma {
                    theory,
                    clause,
                    farkas,
                    kind,
                    lia,
                } => candidate.add_step(ProofStep::TheoryLemma {
                    theory: theory.clone(),
                    clause: clause.clone(),
                    farkas: farkas.clone(),
                    kind: *kind,
                    lia: lia.clone(),
                }),
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => {
                    let premises = premises
                        .iter()
                        .map(|premise| remap.get(premise.0 as usize).copied().flatten())
                        .collect::<Option<Vec<_>>>()?;
                    candidate.add_rule_step(rule.clone(), clause.clone(), premises, args.clone())
                }
                // Anchors bind subproof scopes this flat re-index does not
                // model, and `ProofStep` is `#[non_exhaustive]`: refuse.
                _ => return None,
            };
            remap[index] = Some(mapped);
        }
        Self::proof_derives_empty_clause(&candidate).then_some(candidate)
    }

    /// Derive the unit clause `(cl term)` from the authored scope.
    ///
    /// Exactly four shapes, each with a strict validator:
    /// - an exact authored root: `assume`;
    /// - a recorded `forall` instance: recursively derive the source
    ///   universal's unit, then `forall_inst` → `or` → `resolution`;
    /// - a recorded single-binder Skolem instance: the strict `sko_forall`
    ///   chain (`Skolem` → `equiv_pos1/2` → `resolution`s, optional
    ///   evaluated Boolean-fold bridge), mirroring the c5 fragment channel's
    ///   `emit_skolem_unit_chain` exactly;
    /// - an `and`-conjunct (recursively) of any of those: an `and_pos` +
    ///   `resolution` projection chain from the nearest derivable ancestor.
    fn consequence_unit(
        &mut self,
        candidate: &mut Proof,
        term: TermId,
        authored_set: &ay_core::kani_compat::DetHashSet<TermId>,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        unit_ids: &mut ay_core::kani_compat::DetHashMap<TermId, ProofId>,
    ) -> Option<ProofId> {
        if let Some(&unit) = unit_ids.get(&term) {
            return Some(unit);
        }
        let unit = if authored_set.contains(&term) {
            candidate.add_assume(term, None)
        } else if let Some(plan) = instance_plan.get(&term).cloned() {
            self.planned_consequence_unit(
                candidate,
                term,
                plan,
                authored_set,
                authored,
                instance_plan,
                unit_ids,
            )?
        } else {
            let (source, path) = self.find_authored_and_path(authored, instance_plan, term)?;
            let mut unit = self.consequence_unit(
                candidate,
                source,
                authored_set,
                authored,
                instance_plan,
                unit_ids,
            )?;
            for (gate, index, child) in path {
                let not_gate = self.ctx.terms.mk_not_raw(gate);
                let projection = candidate.add_rule_step(
                    AletheRule::AndPos(index),
                    vec![not_gate, child],
                    Vec::new(),
                    vec![gate],
                );
                unit = candidate.add_resolution(vec![child], gate, projection, unit);
            }
            unit
        };
        unit_ids.insert(term, unit);
        Some(unit)
    }

    /// Emit the De Morgan dual step pair from an ALREADY-DERIVED
    /// `(cl (not E))` unit, leaving the unit `(cl F)`.
    ///
    /// The two-literal `qnt_neg_exists` tautology `(cl E F)` is valid because
    /// `F` is exactly `¬E`; resolving it against `(cl (not E))` on the pivot
    /// `E` leaves `(cl F)`. `validate_qnt_neg_exists` re-derives the duality
    /// (identical binder vector, singly-negated body) independently.
    fn add_negated_exists_dual(
        candidate: &mut Proof,
        not_exists_unit: ProofId,
        exists: TermId,
        forall: TermId,
    ) -> ProofId {
        let neg_exists = candidate.add_rule_step(
            AletheRule::QntNegExists,
            vec![exists, forall],
            Vec::new(),
            Vec::new(),
        );
        candidate.add_resolution(vec![forall], exists, not_exists_unit, neg_exists)
    }

    /// Derive the dual universal's unit for one planned negated-exists
    /// dual, discharging the co-literals of a clause-shaped root first:
    ///
    /// ```text
    /// or | not_and            (cl L₁ … (not E) … Lₙ)   from (cl root)
    /// per co-unit u (complement of Lᵢ):
    ///   resolution on atom(Lᵢ) (cl … (not E) …)        with (cl u)
    /// ```
    ///
    /// Each co-unit is itself derived by `consequence_unit` from the
    /// authored scope; an underivable one declines the whole candidate, so
    /// a ψ premise can never be silently dropped. Every step (`or`,
    /// `not_and`, `resolution`, `qnt_neg_exists`) has a strict validator.
    /// With no co-units the source unit already is `(cl (not E))`.
    fn add_negated_exists_dual_unit(
        &mut self,
        candidate: &mut Proof,
        source_unit: ProofId,
        request: NegatedDualRequest<'_>,
        scope: &mut ConsequenceScope<'_>,
    ) -> Option<ProofId> {
        if request.co_units.is_empty() {
            return Some(Self::add_negated_exists_dual(
                candidate,
                source_unit,
                request.exists,
                request.forall,
            ));
        }
        let (mut running, rule) = match self.ctx.terms.get(request.root).clone() {
            TermData::App(Symbol::Named(name), args) if name == "or" => (args, AletheRule::Or),
            TermData::Not(inner) => match self.ctx.terms.get(inner).clone() {
                TermData::App(Symbol::Named(name), args) if name == "and" => (
                    args.iter()
                        .map(|&a| self.ctx.terms.mk_not_raw(a))
                        .collect::<Vec<_>>(),
                    AletheRule::NotAnd,
                ),
                _ => return None,
            },
            _ => return None,
        };
        if running.len() != request.co_units.len() + 1 {
            return None;
        }
        let mut current =
            candidate.add_rule_step(rule, running.clone(), vec![source_unit], Vec::new());
        for &unit_term in request.co_units {
            // The clause literal this unit discharges is its complement:
            // unit `ψ` removes `(not ψ)`; unit `(not ψ)` removes `ψ`.
            let (atom, literal) = match self.ctx.terms.get(unit_term).clone() {
                TermData::Not(inner) => (inner, inner),
                _ => (unit_term, self.ctx.terms.mk_not_raw(unit_term)),
            };
            if !running.contains(&literal) {
                return None;
            }
            let unit = self.consequence_unit(
                candidate,
                unit_term,
                scope.authored_set,
                scope.authored,
                scope.instance_plan,
                scope.unit_ids,
            )?;
            running.retain(|&l| l != literal);
            current = candidate.add_resolution(running.clone(), atom, current, unit);
        }
        (running.len() == 1).then_some(Self::add_negated_exists_dual(
            candidate,
            current,
            request.exists,
            request.forall,
        ))
    }

    /// Find a derivable source (authored root or planned instance) with an
    /// `and`-path down to `target`, returning `(source, [(gate, index, child)])`
    /// from the source's outermost conjunction to `target` itself.
    fn find_authored_and_path(
        &self,
        authored: &[TermId],
        instance_plan: &ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>,
        target: TermId,
    ) -> Option<(TermId, Vec<(TermId, u32, TermId)>)> {
        for &source in authored.iter().chain(instance_plan.keys()) {
            if source == target {
                continue;
            }
            if let Some(path) = self.and_path_to(source, target) {
                return Some((source, path));
            }
        }
        None
    }

    /// Depth-first `and`-descent from `source` to `target`, bounded by
    /// [`MAX_AND_PATH_WORK`] visited nodes.
    pub(super) fn and_path_to(
        &self,
        source: TermId,
        target: TermId,
    ) -> Option<Vec<(TermId, u32, TermId)>> {
        let mut work = MAX_AND_PATH_WORK;
        let mut path: Vec<(TermId, u32, TermId)> = Vec::new();
        self.and_path_search(source, target, &mut path, &mut work)
            .then_some(path)
    }

    fn and_path_search(
        &self,
        node: TermId,
        target: TermId,
        path: &mut Vec<(TermId, u32, TermId)>,
        work: &mut usize,
    ) -> bool {
        if *work == 0 {
            return false;
        }
        *work -= 1;
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(node) else {
            return false;
        };
        if name != "and" {
            return false;
        }
        let args = args.clone();
        for (index, &child) in args.iter().enumerate() {
            let Ok(index) = u32::try_from(index) else {
                return false;
            };
            path.push((node, index, child));
            if child == target || self.and_path_search(child, target, path, work) {
                return true;
            }
            let _ = path.pop();
        }
        false
    }

    /// Emit `forall_inst` → `or` → `resolution` from an ALREADY-DERIVED unit
    /// clause `(cl forall_root)`, leaving the unit `(cl instance)`.
    ///
    /// Generalizes [`Self::add_forall_instance_prologue`] to multi-binder
    /// universals (the strict validator replays the simultaneous substitution
    /// for the whole argument vector) and to universals that are not
    /// themselves assumable roots (`forall_unit` may be a projection chain's
    /// conclusion rather than an `assume`).
    fn add_forall_instance_values_from_unit(
        &mut self,
        candidate: &mut Proof,
        forall_unit: ProofId,
        forall_root: TermId,
        values: &[TermId],
        instance: TermId,
    ) -> Option<ProofId> {
        let TermData::Forall(bindings, _, _) = self.ctx.terms.get(forall_root) else {
            return None;
        };
        if bindings.len() != values.len() || values.is_empty() {
            return None;
        }
        let not_forall = self.ctx.terms.mk_not_raw(forall_root);
        let implication =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), vec![not_forall, instance], Sort::Bool);
        let instantiated = candidate.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            values.to_vec(),
        );
        let clausified = candidate.add_rule_step(
            AletheRule::Or,
            vec![not_forall, instance],
            vec![instantiated],
            Vec::new(),
        );
        Some(candidate.add_resolution(vec![instance], forall_root, clausified, forall_unit))
    }

    /// Emit the clause-instance derivation from an ALREADY-DERIVED unit of
    /// the clause-shaped `source`, leaving the unit `(cl consequence)`:
    ///
    /// ```text
    /// or | not_and           (cl L₁ … Lₙ)                 from (cl source)
    /// per instantiated ∀ literal Lᵢ = (forall x⃗ B):
    ///   forall_inst (cl (or (not Lᵢ) B[t⃗])) ; or (cl (not Lᵢ) B[t⃗])
    ///   resolution on Lᵢ      (cl … B[t⃗] …)
    /// per negated existential Lᵢ = (not E):
    ///   qnt_neg_exists (cl E F) ; resolution on E  (cl … F …)
    ///   then as a ∀ literal on F
    /// per literal L'ⱼ: or_neg (cl (or L'…) (not L'ⱼ)) ; resolution on L'ⱼ
    /// ```
    ///
    /// Every step has a strict validator; a literal that does not match its
    /// record declines.
    fn add_clausal_instance_from_unit(
        &mut self,
        candidate: &mut Proof,
        source_unit: ProofId,
        source: TermId,
        literals: &[ClausalLiteral],
        consequence: TermId,
    ) -> Option<ProofId> {
        let (mut running, rule) = match self.ctx.terms.get(source).clone() {
            TermData::App(Symbol::Named(name), args) if name == "or" => (args, AletheRule::Or),
            TermData::Not(inner) => match self.ctx.terms.get(inner).clone() {
                TermData::App(Symbol::Named(name), args) if name == "and" => (
                    args.iter()
                        .map(|&a| self.ctx.terms.mk_not_raw(a))
                        .collect::<Vec<_>>(),
                    AletheRule::NotAnd,
                ),
                _ => return None,
            },
            _ => return None,
        };
        if running.len() != literals.len() {
            return None;
        }
        let mut current =
            candidate.add_rule_step(rule, running.clone(), vec![source_unit], Vec::new());
        for (index, literal) in literals.iter().enumerate() {
            let (forall, binding) = match literal {
                ClausalLiteral::Keep => continue,
                ClausalLiteral::Forall { binding } => (running[index], binding.clone()),
                ClausalLiteral::NegatedExists { forall, binding } => {
                    let TermData::Not(exists) = self.ctx.terms.get(running[index]).clone() else {
                        return None;
                    };
                    let neg_exists = candidate.add_rule_step(
                        AletheRule::QntNegExists,
                        vec![exists, *forall],
                        Vec::new(),
                        Vec::new(),
                    );
                    running[index] = *forall;
                    current =
                        candidate.add_resolution(running.clone(), exists, current, neg_exists);
                    (*forall, binding.clone())
                }
            };
            let TermData::Forall(bindings, body, _) = self.ctx.terms.get(forall).clone() else {
                return None;
            };
            if bindings.len() != binding.len() || binding.is_empty() {
                return None;
            }
            let instance = crate::cegqi::lra_nested::tree::instantiate(
                &mut self.ctx.terms,
                body,
                &bindings,
                &binding,
            )?;
            let not_forall = self.ctx.terms.mk_not_raw(forall);
            let implication =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("or"), vec![not_forall, instance], Sort::Bool);
            let instantiated = candidate.add_rule_step(
                AletheRule::ForallInst,
                vec![implication],
                Vec::new(),
                binding,
            );
            let clausified = candidate.add_rule_step(
                AletheRule::Or,
                vec![not_forall, instance],
                vec![instantiated],
                Vec::new(),
            );
            running[index] = instance;
            current = candidate.add_resolution(running.clone(), forall, current, clausified);
        }
        self.close_clause_as_formula(candidate, current, &running, consequence)
    }

    /// From `(cl L₁ … Lₙ)` at `current`, derive the unit `(cl (or L₁ … Lₙ))`
    /// by one `or_neg` + `resolution` per distinct literal; `consequence`
    /// must be exactly that `or`.
    fn close_clause_as_formula(
        &mut self,
        candidate: &mut Proof,
        mut current: ProofId,
        running: &[TermId],
        consequence: TermId,
    ) -> Option<ProofId> {
        // The consequence must be exactly the `or` of the rewritten literals.
        let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(consequence).clone()
        else {
            return None;
        };
        if name != "or" || args != running {
            return None;
        }
        let mut remaining: Vec<TermId> = running.to_vec();
        let mut distinct: Vec<TermId> = Vec::with_capacity(running.len());
        for &literal in running {
            if !distinct.contains(&literal) {
                distinct.push(literal);
            }
        }
        for literal in distinct {
            // `(not ℓ)`, with a negated literal's negation read as its atom
            // (the `or_neg` convention of the probe lift).
            let not_literal = match self.ctx.terms.get(literal) {
                TermData::Not(inner) => *inner,
                _ => self.ctx.terms.mk_not_raw(literal),
            };
            let or_neg = candidate.add_rule_step(
                AletheRule::OrNeg,
                vec![consequence, not_literal],
                Vec::new(),
                Vec::new(),
            );
            let mut next: Vec<TermId> = remaining
                .iter()
                .copied()
                .filter(|&l| l != literal)
                .collect();
            if !next.contains(&consequence) {
                next.push(consequence);
            }
            current = candidate.add_resolution(next.clone(), literal, current, or_neg);
            remaining = next;
        }
        (remaining == vec![consequence]).then_some(current)
    }

    /// Emit the strict Skolem unit chain from an ALREADY-DERIVED source unit,
    /// leaving the unit `(cl asserted)`.
    ///
    /// Byte-for-byte the derivation `emit_skolem_unit_chain` (c5, the
    /// checked-SAT-refutation fragment channel) authors, so the strict
    /// checker's `sko_forall` / registered-choice validation applies
    /// identically:
    ///
    /// ```text
    /// positive source F = (exists x. B):
    ///   t1: sko (cl (= F B[sk])) :args sk
    ///   t2: equiv_pos2 (cl (not (= F B[sk])) (not F) B[sk])
    ///   t3: resolution (cl (not F) B[sk])   ; pivot (= F B[sk])
    ///   t4: resolution (cl B[sk])           ; pivot F with the source unit
    /// negative source (not F), F = (forall x. B):
    ///   t1: sko (cl (= F B[sk])) :args sk
    ///   t2: equiv_pos1 (cl (not (= F B[sk])) F (not B[sk]))
    ///   t3: resolution (cl F (not B[sk]))   ; pivot (= F B[sk])
    ///   t4: resolution (cl (not B[sk]))     ; pivot F with the source unit
    /// bridge to the asserted term u when it differs (Boolean folding):
    ///   t5: true (cl (= d u))               ; exhaustively evaluated
    ///   t6: equiv_pos2 (cl (not (= d u)) (not d) u)
    ///   t7/t8: resolutions to (cl u)
    /// ```
    #[allow(clippy::too_many_arguments)]
    fn add_skolem_instance_from_unit(
        &mut self,
        candidate: &mut Proof,
        source_unit: ProofId,
        quantified: TermId,
        witness: TermId,
        instance: TermId,
        positive: bool,
        asserted: TermId,
    ) -> Option<ProofId> {
        let equality =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);
        let sko = candidate.add_rule_step(
            AletheRule::Skolem,
            vec![equality],
            Vec::new(),
            vec![witness],
        );
        let not_equality = self.ctx.terms.mk_not_raw(equality);
        let (derived_unit, derived_literal) = if positive {
            let not_quantified = self.ctx.terms.mk_not_raw(quantified);
            let tautology = candidate.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equality, not_quantified, instance],
                Vec::new(),
                Vec::new(),
            );
            let elided =
                candidate.add_resolution(vec![not_quantified, instance], equality, tautology, sko);
            (
                candidate.add_resolution(vec![instance], quantified, elided, source_unit),
                instance,
            )
        } else {
            let not_instance = self.ctx.terms.mk_not_raw(instance);
            let tautology = candidate.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equality, quantified, not_instance],
                Vec::new(),
                Vec::new(),
            );
            let elided =
                candidate.add_resolution(vec![quantified, not_instance], equality, tautology, sko);
            (
                candidate.add_resolution(vec![not_instance], quantified, source_unit, elided),
                not_instance,
            )
        };
        if derived_literal == asserted {
            return Some(derived_unit);
        }
        // Boolean-fold bridge, re-validated by the strict bounded evaluator.
        let bridge_equality =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [derived_literal, asserted], Sort::Bool);
        let bridge = candidate.add_rule_step(
            AletheRule::True,
            vec![bridge_equality],
            Vec::new(),
            Vec::new(),
        );
        let not_bridge_equality = self.ctx.terms.mk_not_raw(bridge_equality);
        let not_derived = self.ctx.terms.mk_not_raw(derived_literal);
        let tautology = candidate.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_bridge_equality, not_derived, asserted],
            Vec::new(),
            Vec::new(),
        );
        let elided = candidate.add_resolution(
            vec![not_derived, asserted],
            bridge_equality,
            tautology,
            bridge,
        );
        Some(candidate.add_resolution(vec![asserted], derived_literal, elided, derived_unit))
    }

    /// Carry a unit across one binder split (`qnt_join`), leaving the unit
    /// `(cl derived)`:
    ///
    /// ```text
    /// J = (Q x₁…xₙ φ), N = (Q x₁ (Q x₂…xₙ φ))
    ///   t1: qnt_join (cl (= N J))
    /// positive source unit (cl J), derived N:
    ///   t2: equiv_pos1 (cl (not (= N J)) N (not J))
    ///   t3: resolution (cl N (not J))   ; pivot (= N J)
    ///   t4: resolution (cl N)           ; pivot J with the source unit
    /// negative source unit (cl (not J)), derived (not N):
    ///   t2: equiv_pos2 (cl (not (= N J)) (not N) J)
    ///   t3: resolution (cl (not N) J)   ; pivot (= N J)
    ///   t4: resolution (cl (not N))     ; pivot J with the source unit
    /// ```
    ///
    /// Every step is re-derived by its strict validator; `derived` must be
    /// exactly the planned term or nothing is emitted.
    fn add_quantifier_join_from_unit(
        &mut self,
        candidate: &mut Proof,
        source_unit: ProofId,
        joined: TermId,
        nested: TermId,
        positive: bool,
        derived: TermId,
    ) -> Option<ProofId> {
        let equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [nested, joined], Sort::Bool);
        let join =
            candidate.add_rule_step(AletheRule::QntJoin, vec![equality], Vec::new(), Vec::new());
        let not_equality = self.ctx.terms.mk_not_raw(equality);
        if positive {
            if derived != nested {
                return None;
            }
            let not_joined = self.ctx.terms.mk_not_raw(joined);
            let tautology = candidate.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equality, nested, not_joined],
                Vec::new(),
                Vec::new(),
            );
            let elided =
                candidate.add_resolution(vec![nested, not_joined], equality, tautology, join);
            Some(candidate.add_resolution(vec![nested], joined, elided, source_unit))
        } else {
            let not_nested = self.ctx.terms.mk_not_raw(nested);
            if derived != not_nested {
                return None;
            }
            let tautology = candidate.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equality, not_nested, joined],
                Vec::new(),
                Vec::new(),
            );
            let elided =
                candidate.add_resolution(vec![not_nested, joined], equality, tautology, join);
            Some(candidate.add_resolution(vec![not_nested], joined, source_unit, elided))
        }
    }

    /// The recursive `and`-conjunct closure of the authored roots: exactly the
    /// membership the strict checker's own `validate_problem_assumptions`
    /// expansion recognizes, kept in deterministic first-visit order.
    fn authored_and_conjunct_closure(&self, authored: &[TermId]) -> AndConjunctClosure {
        let mut closure = AndConjunctClosure::default();
        let mut stack: Vec<TermId> = authored.iter().rev().copied().collect();
        while let Some(term) = stack.pop() {
            if !closure.members.insert(term) {
                continue;
            }
            closure.ordered.push(term);
            if let TermData::App(Symbol::Named(name), args) = self.ctx.terms.get(term) {
                if name == "and" {
                    for &arg in args.iter().rev() {
                        stack.push(arg);
                    }
                }
            }
        }
        closure
    }
}

#[cfg(test)]
mod tests;
