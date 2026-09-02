// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier result mapping: interprets SAT/UNSAT through CEGQI and E-matching semantics.
//!
//! `map_quantifier_result` maps raw solves through CEGQI forall/exists inversion,
//! E-matching incompleteness, interleaved refinement, and assertion restoration.

mod cert_consult;
mod checked_isolated_solve;
mod checked_model_rewrite;
mod closed_universal;
mod exact_array_negation;
mod finite_expansion_replay;
mod interleaved_ematching;
mod justification;
mod qpf_premise_forced;
mod quantified_unsat;
mod restore_refinement;
mod unsafe_partial_unknown;
mod vacuous_collapse;
use ay_core::term::{TermEntryStamp, TermStoreSnapshotStamp};
use ay_core::{TermData, TermId};
use ay_frontend::SourceContextStamp;
pub(in crate::executor) use exact_array_negation::CheckedExactArrayNegationSatAuthority;

use super::super::Executor;
use super::collect_and_conjuncts;
use super::{ExactFiniteExpansionEvidence, QuantifierProcessingResult};
use crate::cegqi::CegqiInstantiator;
use crate::ematching::contains_quantifier;
use crate::executor::mbqi::{is_pure_arith_bool_symbol, SkippedQuantifierMbqiGate};
use crate::executor::model::sat_emit::{SatCertificate, ValidatedModelCertificate};
use crate::executor::model::{CegqiUfModelEpoch, EvalValue, Model};
use crate::executor::unsat_cert::CheckedExactClosedForallUnsat;
use crate::executor::{QuantifiedSatAuthorityGrant, QueryAuthorityEpoch};
use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};

include!("result_mapping/unit_helpers.rs");
use crate::logic_detection::LogicCategory;
use ay_core::kani_compat::DetHashMap as HashMap;

/// Publication class of a refuted authored closed universal.
///
/// Only the exact literal instance carries a sealed authored-query token.  The
/// older disposable skolem-model path remains mathematically sound but has no
/// translated outer proof/certificate and therefore retains its existing
/// fail-closed publication behavior.
enum ClosedUniversalRefutation {
    TranslatedProof,
    CheckedLiteral(CheckedExactClosedForallUnsat),
    UntranslatedSkolemModel,
}

/// Immutable outer scope of one checked disposable ground obligation.
///
/// The nested proof/model certificate authenticates the cloned probe Context.
/// This scope separately binds that result back to the exact terms and public
/// query in the enclosing Executor. A whole [`TermStoreSnapshotStamp`] is
/// deliberately used here: every current consumer discharges the token
/// immediately, before constructing its next obligation, and any intervening
/// append/rollback must retire the decision rather than risk TermId aliasing.
#[derive(Debug)]
struct CheckedGroundScope {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    term_snapshot: TermStoreSnapshotStamp,
}

impl CheckedGroundScope {
    fn capture(executor: &Executor, roots: &[TermId]) -> Self {
        Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            term_snapshot: executor.ctx.terms.snapshot_stamp(),
        }
    }

    fn is_current_for(&self, executor: &Executor, roots: &[TermId]) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == roots
            && self.term_snapshot == executor.ctx.terms.snapshot_stamp()
    }
}

/// Outer authority and immutable term lineage of one same-`Context` model
/// probe.
///
/// Unlike [`CheckedGroundScope`], this scope deliberately permits terms to be
/// appended while the disposable solver owns the real frontend context.  Root
/// entry stamps prevent rollback/reuse aliasing, while the append-only prefix
/// stamp proves every term that existed before the probe kept its identity.
#[derive(Debug)]
struct CheckedSameContextGroundScope {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    term_prefix: TermStoreSnapshotStamp,
}

impl CheckedSameContextGroundScope {
    fn capture(executor: &Executor, roots: &[TermId]) -> Option<Self> {
        let root_entries = roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<_>>>()?;
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: root_entries.into_boxed_slice(),
            term_prefix: executor.ctx.terms.snapshot_stamp(),
        })
    }

    fn is_current(&self, executor: &Executor) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.root_entries.iter().copied().map(Some).eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            && self
                .term_prefix
                .is_append_only_prefix_of(&executor.ctx.terms)
    }
}

/// A fully validated model bundle still waiting for atomic installation in the
/// enclosing executor.
///
/// The ordinary SAT funnel's narrowed certificate is retained inside this
/// affine package, so theorem/projection SAT lanes cannot be relabelled as a
/// transportable solver model.
#[must_use = "a checked same-Context model must be installed or discarded"]
#[derive(Debug)]
struct CheckedSameContextGroundModel {
    scope: CheckedSameContextGroundScope,
    _certificate: ValidatedModelCertificate,
    model: Model,
    nra_algebraic_model: HashMap<TermId, ay_nra::RealAlgebraicValue>,
    dt_theory_model: Option<ay_dt::DtModel>,
    recorded_var_substitutions: HashMap<TermId, TermId>,
    delegated_assertions: ay_core::kani_compat::DetHashSet<TermId>,
}

/// Exact outer model state parked while a checked candidate is installed.
///
/// Models are moved, never cloned: cloning deliberately revokes their identity
/// seals, so a cloned rollback would not restore the authority that existed on
/// entry. Statistics and scalar result state stay live during the transaction
/// and are snapshotted only so a declining/panicking postprocessor is a true
/// no-op.
struct CheckedModelInstallSnapshot {
    model: Option<Model>,
    nra_algebraic_model: HashMap<TermId, ay_nra::RealAlgebraicValue>,
    dt_theory_model: Option<ay_dt::DtModel>,
    dt_validation_wants_egraph: bool,
    dt_egraph_assignment: Option<std::sync::Arc<crate::executor::model::DtEgraphAssignment>>,
    dt_egraph_building: bool,
    recorded_var_substitutions: HashMap<TermId, TermId>,
    delegated_assertions: ay_core::kani_compat::DetHashSet<TermId>,
    model_validated: bool,
    validation_stats: Option<crate::executor::model::ValidationStats>,
    sat_certificate: Option<SatCertificate>,
    mbqi_grant_active: bool,
    mbqi_query_grant: Option<QuantifiedSatAuthorityGrant>,
    last_result: Option<SolveResult>,
    last_unknown_reason: Option<UnknownReason>,
    last_unknown_origin: Option<UnknownOrigin>,
    defer_model_validation: bool,
    statistics: crate::executor_types::Statistics,
}

impl CheckedModelInstallSnapshot {
    fn take(executor: &mut Executor) -> Self {
        Self {
            model: executor.last_model.take(),
            nra_algebraic_model: executor.nra_algebraic_model.take_values(),
            dt_theory_model: executor.dt_theory_model.take(),
            dt_validation_wants_egraph: executor.dt_validation_wants_egraph,
            dt_egraph_assignment: executor.dt_egraph_assignment.replace(None),
            dt_egraph_building: executor.dt_egraph_building.replace(false),
            recorded_var_substitutions: std::mem::take(&mut executor.recorded_var_substitutions),
            delegated_assertions: std::mem::take(
                &mut executor.model_validation_delegated_assertions,
            ),
            model_validated: executor.last_model_validated,
            validation_stats: executor.last_validation_stats.take(),
            sat_certificate: executor.last_sat_certificate.take(),
            mbqi_grant_active: std::mem::replace(&mut executor.mbqi_sat_cert_grant_active, false),
            mbqi_query_grant: executor.mbqi_sat_cert_query_grant.take(),
            last_result: executor.last_result.clone(),
            last_unknown_reason: executor.last_unknown_reason,
            last_unknown_origin: executor.last_unknown_origin,
            defer_model_validation: executor.defer_model_validation,
            statistics: executor.last_statistics.clone(),
        }
    }

    fn restore(self, executor: &mut Executor) {
        executor.last_model = self.model;
        executor.restore_nra_values(self.nra_algebraic_model);
        executor.dt_theory_model = self.dt_theory_model;
        executor.dt_validation_wants_egraph = self.dt_validation_wants_egraph;
        executor
            .dt_egraph_assignment
            .replace(self.dt_egraph_assignment);
        executor.dt_egraph_building.set(self.dt_egraph_building);
        executor.recorded_var_substitutions = self.recorded_var_substitutions;
        executor.model_validation_delegated_assertions = self.delegated_assertions;
        executor.last_model_validated = self.model_validated;
        executor.last_validation_stats = self.validation_stats;
        executor.last_sat_certificate = self.sat_certificate;
        executor.mbqi_sat_cert_grant_active = self.mbqi_grant_active;
        executor.mbqi_sat_cert_query_grant = self.mbqi_query_grant;
        executor.last_result = self.last_result;
        executor.last_unknown_reason = self.last_unknown_reason;
        executor.last_unknown_origin = self.last_unknown_origin;
        executor.defer_model_validation = self.defer_model_validation;
        executor.last_statistics = self.statistics;
        crate::executor::model::eval_memo_clear();
    }
}

/// Panic-safe installation guard. Unless explicitly committed, dropping the
/// guard restores the exact prior model object and every paired sidecar/grant.
struct CheckedModelInstallTransaction<'a> {
    executor: &'a mut Executor,
    saved: Option<CheckedModelInstallSnapshot>,
}

impl<'a> CheckedModelInstallTransaction<'a> {
    fn begin(executor: &'a mut Executor) -> Self {
        let saved = CheckedModelInstallSnapshot::take(executor);
        Self {
            executor,
            saved: Some(saved),
        }
    }

    fn executor(&mut self) -> &mut Executor {
        self.executor
    }

    fn commit(mut self) {
        self.saved = None;
    }
}

impl Drop for CheckedModelInstallTransaction<'_> {
    fn drop(&mut self) {
        if let Some(saved) = self.saved.take() {
            saved.restore(self.executor);
        }
    }
}

include!("result_mapping/installed_checked_ground_model.rs");

/// Checked SAT authority for one exact ordered ground assertion vector.
/// Fields and construction stay private to this module.
#[must_use = "checked ground SAT authority must be consumed against its exact roots"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedGroundSat {
    scope: CheckedGroundScope,
}

impl CheckedGroundSat {
    pub(in crate::executor) fn consume(self, executor: &mut Executor, roots: &[TermId]) -> bool {
        !executor.should_abort_theory_loop() && self.scope.is_current_for(executor, roots)
    }
}

/// Checked UNSAT authority for one exact ordered ground assertion vector.
/// Fields and construction stay private to this module.
#[must_use = "checked ground UNSAT authority must be consumed against its exact roots"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedGroundUnsat {
    scope: CheckedGroundScope,
}

impl CheckedGroundUnsat {
    pub(in crate::executor) fn consume(self, executor: &mut Executor, roots: &[TermId]) -> bool {
        !executor.should_abort_theory_loop() && self.scope.is_current_for(executor, roots)
    }
}

/// Checked strict-proof UNSAT authority for one exact assertion vector.
///
/// Unlike [`CheckedGroundUnsat`], this token is UNSAT-only and accepts both
/// ground and quantified obligations.  It is shared with the small number of
/// executor subsystems that must authenticate a derived refutation (for
/// example, a nested-array residue or a proposed reduced unsat core) without
/// transporting any model or raw nested-solver verdict.
#[must_use = "checked exact UNSAT authority must be consumed against its exact roots"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedExactUnsat {
    scope: CheckedGroundScope,
}

impl CheckedExactUnsat {
    pub(in crate::executor) fn consume(self, executor: &mut Executor, roots: &[TermId]) -> bool {
        !executor.should_abort_theory_loop() && self.scope.is_current_for(executor, roots)
    }
}

/// Linear, model-relative authority that canonical finite-domain expansion
/// discharged one exact authored root window.
///
/// Expansion is an equivalence, but a satisfying interpretation of a body that
/// names free functions is not model-free. The token therefore seals the exact
/// retained model that satisfied the complete expanded ground vector. Model
/// replacement, cloning, or theorem-relevant mutation makes it stale.
#[must_use = "checked finite-expansion SAT authority must be consumed or discarded"]
#[derive(Debug)]
pub(in crate::executor) struct CheckedFiniteExpansionSatAuthority {
    checked: checked_model_rewrite::CheckedModelRewriteSatAuthority,
}

impl CheckedFiniteExpansionSatAuthority {
    fn for_current(
        executor: &mut Executor,
        roots: &[TermId],
        expanded_model_roots: &[TermId],
    ) -> Option<Self> {
        checked_model_rewrite::CheckedModelRewriteSatAuthority::for_current(
            executor,
            roots,
            expanded_model_roots,
            "exact-finite-expansion",
        )
        .map(|checked| Self { checked })
    }

    pub(in crate::executor) fn into_current_roots(
        self,
        executor: &mut Executor,
    ) -> Option<(
        Box<[TermId]>,
        crate::executor::model::QuantifiedGrantModelEpoch,
    )> {
        self.checked.into_current_roots(executor)
    }
}

/// Non-cloneable decisive result. Visible variants always require one of the
/// private-constructor payloads above, so another executor module cannot forge
/// SAT or UNSAT authority by spelling an enum variant.
#[must_use = "a checked ground decision must be consumed against its exact roots"]
#[derive(Debug)]
pub(in crate::executor) enum CheckedGroundDecision {
    Sat(CheckedGroundSat),
    Unsat(CheckedGroundUnsat),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CheckedGroundKind {
    Sat,
    Unsat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CheckedIsolatedMode {
    GroundDecision,
    ExactUnsat,
}

/// Outcome of one same-context consequence probe
/// ([`Executor::checked_same_context_unsat_proof`]).
///
/// `UnsatUnpromotable` names the one outcome the metered caller may retry
/// with the window scope off (#frame-probe-unscoped-retry): the probe DID
/// refute its exact consequence set, but the refutation's conflicts fused
/// into theory lemmas the strict checker refuses, which is a proof-SHAPE
/// failure the axiom scope can cause — never a verdict. `Other` covers every
/// remaining outcome (SAT, unknown, error, preflight or stale-window
/// decline); none of those may be retried, so a genuinely satisfiable or
/// undecided probe is never re-run against a different axiom surface.
pub(in crate::executor) enum SameContextProbeOutcome {
    /// The probe's own strict checker accepted its completed refutation.
    Proof(ay_core::Proof),
    /// Raw UNSAT whose proof completion failed the strict gate.
    UnsatUnpromotable,
    /// Any other result; carries no retry advice.
    Other,
}

/// Exact constructor-site provenance for recursive NNF normalization inside a
/// positive universal.
///
/// This record is observational: it does not grant authority by itself.
/// `fold_quantified_linear_eqs` installs it only when `source_forall` is an
/// immutable authored assertion root, and the proof tracker still validates
/// exact binders/triggers/substitution plus every changed arithmetic literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QuantifiedLinearNnfProvenance {
    source_forall: TermId,
    normalized_forall: TermId,
}

/// One exact-current quantified-SAT authority accepted during assertion
/// restoration.
///
/// The legacy Boolean markers remain useful for routing certificate probes,
/// but they are never evidence here.  Every variant below is returned only
/// after the corresponding opaque grant/package has rechecked the live query
/// epoch, source scope, ordered authored roots, and (where applicable) the
/// installed certified model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CurrentQuantifiedSatAuthority {
    Datatype,
    FiniteTable,
    ConstantInterpretation,
    Mbqi,
    BvFullDomain,
    CegqiUfRecompletion,
}

/// Whether the mapper must ask the finite/default-table producer for fresh
/// authority over the exact public roots.
///
/// A provisional CEGQI `Sat` is only a search result. A clean-source candidate
/// may continue to the public model gates, but stale source/routing state needs
/// fresh exact-root authority first. An eligible quantifier-incompleteness
/// `Unknown` may likewise be upgraded only by a theorem for the entire public
/// root vector. Other verdicts and external-stop Unknown classes are never
/// rescue candidates.
fn exact_public_table_rescue_needed(
    final_result: &Result<SolveResult>,
    unknown_reason: Option<UnknownReason>,
    public_roots_match_table_partition: bool,
    cegqi_has_forall: bool,
    cegqi_source_stamp_is_stale: bool,
    has_table_routing_bit: bool,
    exact_public_transport: bool,
    exact_public_authority: Option<CurrentQuantifiedSatAuthority>,
) -> bool {
    // Preserve the old CEGQI rescue surface, extending it only to a table
    // producer that actually left routing state. The routing bit merely
    // authorizes a fresh attempt; the producer must still mint exact-current
    // authority over the complete public root vector below.
    if !public_roots_match_table_partition || (!cegqi_has_forall && !has_table_routing_bit) {
        return false;
    }

    // An existing quantified authority can justify only its quantified
    // obligations; it cannot upgrade an already-Unknown whole query to Sat.
    // Give the all-roots table producer a chance to construct that stronger
    // witness before the Sat-only preservation rule below. If it declines,
    // the caller remains fail-closed Unknown.
    match final_result {
        Ok(SolveResult::Unknown) => {
            return matches!(
                unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            );
        }
        Ok(SolveResult::Sat) => {}
        Ok(SolveResult::Unsat(_)) | Err(_) => return false,
    }

    // A different exact-current quantified proof already owns publication.
    // Do not replace it with a narrower table certificate.  Exact table
    // transport is the exception: a stale table routing bit may still require
    // the exact-root producer below. This preservation applies only to a
    // provisional Sat; the Unknown case returned above needs whole-query
    // authority that these quantified-only grants do not provide.
    if matches!(
        exact_public_authority,
        Some(
            CurrentQuantifiedSatAuthority::Datatype
                | CurrentQuantifiedSatAuthority::Mbqi
                | CurrentQuantifiedSatAuthority::BvFullDomain
                | CurrentQuantifiedSatAuthority::CegqiUfRecompletion
        )
    ) {
        return false;
    }

    cegqi_source_stamp_is_stale
        || exact_public_authority.is_none()
        || (has_table_routing_bit && !exact_public_transport)
}

/// Exact facts consumed by the final CEGQI SAT postflight.
#[derive(Debug, Clone, Copy)]
struct CegqiSatPostflightFacts {
    final_result_is_sat: bool,
    should_abort: bool,
    cegqi_has_forall: bool,
    has_retained_model: bool,
    has_pending_certificate_model: bool,
    has_current_model_free_mbqi_authority: bool,
    cegqi_source_stamp_is_stale: bool,
    has_current_quantified_sat_authority: bool,
}

/// Final CEGQI SAT postflight over the already-selected exact authored roots.
///
/// A fresh typed quantified authority supersedes the older CEGQI routing stamp
/// because its own currentness check is bound to the live source context.  It
/// does not supersede an external stop or the independent retained-model
/// requirement; those remain separate fail-closed premises.
fn cegqi_sat_postflight_must_fail_closed(facts: CegqiSatPostflightFacts) -> bool {
    facts.final_result_is_sat
        && (facts.should_abort
            || (facts.cegqi_has_forall
                && !facts.has_retained_model
                && !facts.has_pending_certificate_model
                && !facts.has_current_model_free_mbqi_authority)
            || (facts.cegqi_source_stamp_is_stale && !facts.has_current_quantified_sat_authority))
}

/// What a successful per-group CEGQI refutation establishes about the model.
///
/// Scalar pins are exact reads of the retained snapshot-ground model. UF graph
/// pins instead describe a separately re-completed interpretation M′, which is
/// SAT-verdict evidence but not authority for the retained model artifact.
enum CegqiGroupRefutation {
    RetainedGroundModel,
    UfRecompletion(CegqiUfRecompletion),
}

/// Exact completed model whose UF graph/default interpretation was used by a
/// successful per-group CEGQI refutation.
///
/// The checked bindings tie every rewritten core head to one live direct
/// source declaration and scope epoch. Keeping the completed model inside the
/// sealed theorem prevents a mere existence proof for M' from accidentally
/// publishing the different, retained G0 model.
struct CegqiUfRecompletion {
    bindings: Box<[ay_frontend::CheckedProjectionBinding]>,
    model: Box<Model>,
    model_epoch: CegqiUfModelEpoch,
    /// Exact scalar model-definition facts used as premises by the sealed
    /// refutations. Rechecking these facts against the publication model is a
    /// proof-tight semantic revision check: direct Model field writes cannot
    /// preserve authority merely because they bypass a mutation counter.
    model_definition: Box<[TermId]>,
}

/// Query-scoped authority that the installed model is the exact UF
/// re-completion used by the sealed CEGQI theorem.
///
/// The constructor is private to this module. Other executor components may
/// only test/consume an already checked grant; they cannot promote a raw CEGQI
/// verdict, a Boolean classifier, or an arbitrary certified table to SAT
/// authority.
#[must_use = "a checked CEGQI UF grant must be consumed by the SAT funnel"]
pub(in crate::executor) struct CegqiUfRecompletionGrant {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[Option<TermEntryStamp>]>,
    bindings: Box<[ay_frontend::CheckedProjectionBinding]>,
    model_epoch: CegqiUfModelEpoch,
    model_definition: Box<[TermId]>,
    model_definition_entries: Box<[Option<TermEntryStamp>]>,
}

impl CegqiUfRecompletionGrant {
    fn from_checked(
        executor: &Executor,
        roots: Box<[TermId]>,
        completion: CegqiUfRecompletion,
    ) -> Option<(Self, Box<Model>)> {
        let root_entries: Box<[Option<TermEntryStamp>]> = roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect();
        let model_definition_entries: Box<[Option<TermEntryStamp>]> = completion
            .model_definition
            .iter()
            .map(|&pin| executor.ctx.terms.entry_stamp(pin))
            .collect();
        if completion.bindings.is_empty()
            || root_entries.iter().any(Option::is_none)
            || model_definition_entries.iter().any(Option::is_none)
            || completion
                .bindings
                .iter()
                .any(|binding| !executor.ctx.projection_binding_still_current(binding))
            || !completion
                .model
                .carries_cegqi_uf_recompletion(&completion.model_epoch)
            || !completion
                .model
                .formula_neutral_function_defaults_are_current(&executor.ctx)
            || completion.model_definition.iter().any(|&pin| {
                !matches!(
                    executor.evaluate_term(&completion.model, pin),
                    EvalValue::Bool(true)
                )
            })
        {
            return None;
        }
        let grant = Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots,
            root_entries,
            bindings: completion.bindings,
            model_epoch: completion.model_epoch,
            model_definition: completion.model_definition,
            model_definition_entries,
        };
        Some((grant, completion.model))
    }

    /// Recheck query, roots, source scope, declaration identities/signatures,
    /// exact installed-model identity, and every scalar M_def theorem premise
    /// at each authority consumer. The independent gate immediately following
    /// this handoff rechecks every quantifier-free root (including G0) against
    /// the same final model, completing the sealed proof's premise inventory.
    #[cfg(test)]
    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        self.is_current_for(executor, &executor.ctx.assertions)
    }

    /// Recheck against the exact root snapshot selected by a SAT gate.
    pub(in crate::executor) fn is_current_for(
        &self,
        executor: &Executor,
        roots: &[TermId],
    ) -> bool {
        self.model_and_source_are_current(executor)
            && self.roots.as_ref() == roots
            && self.root_entries.iter().copied().eq(roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
    }

    /// During CEGQI publication the authored roots are temporarily replaced by
    /// the refinement window. Check everything except root restoration; the
    /// public consumers call `is_current` after the authored roots are back.
    fn model_and_source_are_current(&self, executor: &Executor) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self
                .bindings
                .iter()
                .all(|binding| executor.ctx.projection_binding_still_current(binding))
            && self.root_entries.iter().copied().eq(self
                .roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            && self.model_definition_entries.iter().copied().eq(self
                .model_definition
                .iter()
                .map(|&pin| executor.ctx.terms.entry_stamp(pin)))
            && executor.last_model.as_ref().is_some_and(|model| {
                model.carries_cegqi_uf_recompletion(&self.model_epoch)
                    && model.formula_neutral_function_defaults_are_current(&executor.ctx)
                    && self.model_definition.iter().all(|&pin| {
                        matches!(executor.evaluate_term(model, pin), EvalValue::Bool(true))
                    })
            })
    }
}

/// Sealed publication authority for a CEGQI UNSAT candidate.
///
/// `Checked`'s constructor is private to this module. Callers can obtain it
/// only by running the independent consequence-set verifier; they cannot turn
/// a raw solver verdict or a Boolean classifier into publication authority.
mod cegqi_unsat_authority;
mod consequence_probe_proof;

/// Sealed witness that the snapshot's reconstructed ground remainder was
/// solved SAT on this Executor and installed a context-coherent model.
///
/// A model produced by a cloned Context cannot cross back safely: theory
/// models contain `TermId`s, including terms minted during solving.  This
/// authority is therefore constructed only by the controlled in-context solve
/// below, after it observes both a definitive SAT result and a present model.
mod cegqi_sat_authority {
    use super::{
        CegqiGroupRefutation, CegqiInstantiator, Executor, InstalledCheckedGroundModel,
        LogicCategory, Result, SolveResult, TermId,
    };

    #[must_use = "a checked CEGQI ground witness must be consumed or discarded"]
    pub(super) struct GroundWitness {
        snapshot: Box<[TermId]>,
        snapshot_entries: Box<[Option<ay_core::term::TermEntryStamp>]>,
        installed_model: InstalledCheckedGroundModel,
    }

    impl GroundWitness {
        fn entries_are_current(&self, executor: &Executor) -> bool {
            self.snapshot_entries.iter().all(Option::is_some)
                && self.snapshot_entries.iter().copied().eq(self
                    .snapshot
                    .iter()
                    .map(|&root| executor.ctx.terms.entry_stamp(root)))
        }

        pub(super) fn is_current(&self, executor: &Executor, snapshot: &[TermId]) -> bool {
            self.snapshot.as_ref() == snapshot
                && self.entries_are_current(executor)
                && self.installed_model.is_current(executor)
        }
    }

    #[must_use = "a fully checked CEGQI SAT authority must be consumed to publish SAT"]
    pub(super) struct CheckedSat {
        ground_witness: GroundWitness,
        theorem: QuantifiedTheorem,
    }

    enum QuantifiedTheorem {
        /// Every covered universal is valid independently of the model.
        GloballyValid,
        /// Every covered universal holds in the exact retained G0 model.
        SnapshotGroundModelSatisfies,
        /// The group proof witnesses and carries the exact UF/default
        /// re-completion M′ used by the theorem.
        UfRecompletion(super::CegqiUfRecompletion),
    }

    impl CheckedSat {
        /// Consume the combined ground-model and quantified-validity authority.
        ///
        /// This is the only CEGQI SAT constructor.  The postflight is part of
        /// publication rather than either theorem route so neither a late stop
        /// nor a theorem subsolve that discarded the authenticated model can
        /// turn a stale witness into `sat`.
        pub(super) fn publish(self, executor: &mut Executor) -> Result<SolveResult> {
            let Self {
                ground_witness,
                theorem,
            } = self;
            let checked_uf_bindings_are_current = match &theorem {
                QuantifiedTheorem::UfRecompletion(completion) => completion
                    .bindings
                    .iter()
                    .all(|binding| executor.ctx.projection_binding_still_current(binding)),
                QuantifiedTheorem::GloballyValid
                | QuantifiedTheorem::SnapshotGroundModelSatisfies => true,
            };
            let model_is_available = matches!(&theorem, QuantifiedTheorem::UfRecompletion(_))
                || executor.last_model.is_some();
            if !ground_witness.entries_are_current(executor)
                || !ground_witness.installed_model.is_current(executor)
                || executor.should_abort_theory_loop()
                || !model_is_available
                || !checked_uf_bindings_are_current
            {
                return executor.cegqi_fail_closed_unknown();
            }
            let GroundWitness {
                snapshot,
                snapshot_entries: _,
                installed_model,
            } = ground_witness;
            if !installed_model.consume(executor) {
                return executor.cegqi_fail_closed_unknown();
            }
            executor.clear_cegqi_inner_unsat_artifacts();
            // Revoke before installing: only the exact UF-completion arm below
            // may mint this query-scoped authority.
            executor.cegqi_uf_recompletion_grant = None;
            match theorem {
                QuantifiedTheorem::GloballyValid
                | QuantifiedTheorem::SnapshotGroundModelSatisfies => {
                    executor.defer_model_validation = false;
                    executor.last_model_validated = true;
                }
                QuantifiedTheorem::UfRecompletion(completion) => {
                    // Install the exact M′ whose typed rows/defaults were used
                    // by the sealed theorem. The public quantified-model gate
                    // still re-evaluates the restored authored problem before
                    // final SAT emission.
                    let Some((grant, model)) = super::CegqiUfRecompletionGrant::from_checked(
                        executor, snapshot, completion,
                    ) else {
                        return executor.cegqi_fail_closed_unknown();
                    };
                    executor.last_model = Some(*model);
                    // M' was completed while still parked in the theorem
                    // payload. Installing it replaces the evaluator's model
                    // identity, including under an enclosing memo session.
                    crate::executor::model::eval_memo_clear();
                    if !grant.model_and_source_are_current(executor) {
                        executor.last_model = None;
                        return executor.cegqi_fail_closed_unknown();
                    }
                    executor.cegqi_uf_recompletion_grant = Some(grant);
                    executor.defer_model_validation = false;
                    executor.last_model_validated = true;
                }
            }
            executor.last_unknown_reason = None;
            Ok(SolveResult::Sat)
        }
    }

    pub(super) fn install(
        executor: &mut Executor,
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> Option<GroundWitness> {
        let installed = executor.install_authenticated_snapshot_ground_model(snapshot, category);
        if ay_core::misc_cli_flags().trace_cegqi_attr {
            eprintln!(
                "[cegqi-attr] SAT ground witness: installed={} snapshot_roots={} model_present={} model_validated={}",
                installed.is_some(),
                snapshot.len(),
                executor.last_model.is_some(),
                executor.last_model_validated,
            );
        }
        let installed_model = installed?;
        Some(GroundWitness {
            snapshot: snapshot.into(),
            snapshot_entries: snapshot
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            installed_model,
        })
    }

    /// Combine an authenticated G0 model with the model-relative per-group
    /// theorem.  Conjunctive position is derived here from the same authored
    /// snapshot used for G0; callers cannot pass a Boolean theorem claim.
    pub(super) fn certify_model_group_refutations(
        executor: &mut Executor,
        ground_witness: GroundWitness,
        snapshot: &[TermId],
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
    ) -> std::result::Result<CheckedSat, GroundWitness> {
        let current = ground_witness.is_current(executor, snapshot);
        let nonconjunctive = executor.snapshot_has_nonconjunctive_forall(snapshot);
        if !current || nonconjunctive {
            if ay_core::misc_cli_flags().trace_cegqi_attr {
                eprintln!(
                    "[cegqi-attr] SAT model-group DECLINE: current={current} nonconjunctive={nonconjunctive}"
                );
            }
            return Err(ground_witness);
        }
        // Exact coverage is part of the theorem. A refutation of every group
        // supplied by an untrusted producer says nothing about a universal the
        // producer omitted (and duplicate groups must not hide that omission).
        use ay_core::kani_compat::DetHashSet;
        if cegqi_state.is_empty() {
            if ay_core::misc_cli_flags().trace_cegqi_attr {
                eprintln!("[cegqi-attr] SAT model-group DECLINE: empty CEGQI state");
            }
            return Err(ground_witness);
        }
        let mut state_quants = DetHashSet::default();
        for (quant, inst) in cegqi_state {
            if !inst.is_forall()
                || !matches!(
                    executor.ctx.terms.get(*quant),
                    ay_core::TermData::Forall(..)
                )
                || !state_quants.insert(*quant)
            {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    eprintln!(
                        "[cegqi-attr] SAT model-group DECLINE: invalid/duplicate state quantifier {quant:?}"
                    );
                }
                return Err(ground_witness);
            }
        }
        let mut snapshot_quants = Vec::new();
        for &root in snapshot {
            crate::ematching::collect_quantifiers(
                &mut executor.ctx.terms,
                root,
                &mut snapshot_quants,
            );
        }
        let mut snapshot_foralls = DetHashSet::default();
        for quant in snapshot_quants {
            if !matches!(executor.ctx.terms.get(quant), ay_core::TermData::Forall(..))
                || !state_quants.contains(&quant)
            {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    eprintln!(
                        "[cegqi-attr] SAT model-group DECLINE: uncovered snapshot quantifier {quant:?}"
                    );
                }
                return Err(ground_witness);
            }
            snapshot_foralls.insert(quant);
        }
        if snapshot_foralls != state_quants {
            if ay_core::misc_cli_flags().trace_cegqi_attr {
                eprintln!(
                    "[cegqi-attr] SAT model-group DECLINE: snapshot/state coverage mismatch snapshot={} state={}",
                    snapshot_foralls.len(),
                    state_quants.len(),
                );
            }
            return Err(ground_witness);
        }
        let mut grouped_quants = DetHashSet::default();
        for (quant, _) in ce_lemma_groups {
            if !state_quants.contains(quant) || !grouped_quants.insert(*quant) {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    eprintln!(
                        "[cegqi-attr] SAT model-group DECLINE: invalid/duplicate lemma group for {quant:?}"
                    );
                }
                return Err(ground_witness);
            }
        }
        if grouped_quants != state_quants {
            if ay_core::misc_cli_flags().trace_cegqi_attr {
                eprintln!(
                    "[cegqi-attr] SAT model-group DECLINE: group/state coverage mismatch groups={} state={}",
                    grouped_quants.len(),
                    state_quants.len(),
                );
            }
            return Err(ground_witness);
        }
        let ce_vars = cegqi_state
            .iter()
            .flat_map(|(_, inst)| inst.ce_variables().values().copied())
            .collect();
        let certified =
            executor.cegqi_model_refutes_all_groups(snapshot, &ce_vars, ce_lemma_groups, category);
        if ay_core::misc_cli_flags().trace_cegqi_attr {
            let outcome = match &certified {
                Some(CegqiGroupRefutation::RetainedGroundModel) => "retained-model",
                Some(CegqiGroupRefutation::UfRecompletion(_)) => "uf-recompletion",
                None => "declined",
            };
            eprintln!("[cegqi-attr] SAT model-group theorem: {outcome}");
        }
        if let Some(certified) = certified.filter(|_| ground_witness.is_current(executor, snapshot))
        {
            let theorem = match certified {
                CegqiGroupRefutation::RetainedGroundModel => {
                    QuantifiedTheorem::SnapshotGroundModelSatisfies
                }
                CegqiGroupRefutation::UfRecompletion(completion) => {
                    if !completion
                        .bindings
                        .iter()
                        .all(|binding| executor.ctx.projection_binding_still_current(binding))
                    {
                        return Err(ground_witness);
                    }
                    QuantifiedTheorem::UfRecompletion(completion)
                }
            };
            Ok(CheckedSat {
                ground_witness,
                theorem,
            })
        } else {
            Err(ground_witness)
        }
    }

    /// Combine an authenticated G0 model with the de-Skolemized quantified-CE
    /// theorem.  This route also owns its snapshot-position gate and directly
    /// invokes the verifier, so a caller cannot manufacture authority from a
    /// raw `bool`.
    pub(super) fn certify_quantified_ce_refutations(
        executor: &mut Executor,
        ground_witness: GroundWitness,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> std::result::Result<CheckedSat, GroundWitness> {
        let current = ground_witness.is_current(executor, snapshot);
        let nonconjunctive = executor.snapshot_has_nonconjunctive_forall(snapshot);
        if !current || nonconjunctive {
            if ay_core::misc_cli_flags().trace_cegqi_attr {
                eprintln!(
                    "[cegqi-attr] SAT quantified-CE DECLINE: current={current} nonconjunctive={nonconjunctive}"
                );
            }
            return Err(ground_witness);
        }
        let certified = executor.refuted_all_quantified_ce_lemmas(cegqi_state, snapshot, category);
        if ay_core::misc_cli_flags().trace_cegqi_attr {
            eprintln!("[cegqi-attr] SAT quantified-CE theorem: certified={certified}");
        }
        if certified && ground_witness.is_current(executor, snapshot) {
            Ok(CheckedSat {
                ground_witness,
                theorem: QuantifiedTheorem::GloballyValid,
            })
        } else {
            Err(ground_witness)
        }
    }
}

impl Executor {
    /// Retry the authored-consequence replay seeded with the MBQI
    /// refinement instance provenance (#bv-mbqi-refutation-authority).
    ///
    /// A refinement refutation is decided against instances the model chose,
    /// so the translation-incomplete marker is set and the plain replay —
    /// which sees only e-matching records — has no way to reach the same
    /// contradiction. Each record re-derives as the exact structural
    /// substitution and the strict `forall_inst` validator re-replays it, so
    /// the records carry no authority: a failed translation simply falls
    /// through to the unchanged downgrade.
    fn translate_refinement_seeded_replay(&mut self) -> bool {
        // The kill switch disables recording AND translation, restoring the
        // baseline downgrade byte-for-byte (its coverage gate asserts this).
        if !crate::quant_unit_authority::consequence_replay_enabled() {
            return false;
        }
        let records = std::mem::take(&mut self.mbqi_refinement_instance_records);
        if records.is_empty() {
            return false;
        }
        let mut exact_records = Vec::with_capacity(records.len());
        for record in records {
            if let Some(instance) = self.exact_forall_instance(record.quantifier, &record.binding) {
                exact_records.push(crate::ematching::ForallInstantiationProvenance {
                    quantifier: record.quantifier,
                    binding: record.binding,
                    instance,
                });
            }
        }
        !exact_records.is_empty()
            && self.try_translate_authored_consequence_replay_unsat_with(&exact_records)
    }

    fn accept_strict_producer_refutation(&mut self, result: &mut Result<SolveResult>) {
        // A strict producer can close an authored contradiction even when one
        // search lane returned Sat/Unknown for the raw instance. Only a checked
        // authored-scope proof may supersede that provisional result.
        if !matches!(result, Ok(SolveResult::Unsat(_)))
            && self.produce_proofs_enabled()
            && self.last_proof.is_none()
            && self.proof_tracker.has_empty_clause_derivation()
        {
            self.build_unsat_proof();
            let strict_refutation = self
                .last_proof
                .as_ref()
                .is_some_and(|proof| self.check_proof_strict_with_datatypes(proof).is_ok());
            if strict_refutation {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    eprintln!(
                        "[quant-proof] strict producer refutation superseded non-UNSAT search result"
                    );
                }
                *result = Ok(SolveResult::unsat());
            }
        }
    }

    /// Whether a checked certificate model is parked for affine installation
    /// by the sole public SAT funnel. Pending is transport, not SAT authority,
    /// but it satisfies internal model-existence postconditions until that
    /// funnel moves the model into `last_model`.
    pub(in crate::executor) fn has_current_pending_certificate_model_transport(
        &self,
        roots: &[TermId],
    ) -> bool {
        (self.finite_table_cert_grant_active
            && self
                .finite_table_cert_witness_state
                .as_ref()
                .is_some_and(|state| state.is_pending_current_for(self, roots)))
            || (self.const_interp_cert_grant_active
                && self
                    .const_interp_cert_witness_state
                    .as_ref()
                    .is_some_and(|state| state.is_pending_current_for(self, roots)))
    }

    /// Select a certificate that still covers exactly `roots`.
    ///
    /// This is the sole restoration-time bridge from certificate routing state
    /// to quantified SAT authority. A bit without its paired typed grant, a
    /// grant from another query epoch/source scope, a different ordered root
    /// window, or a stale certified model all fail closed to `None`.
    fn current_quantified_sat_authority(
        &self,
        roots: &[TermId],
    ) -> Option<CurrentQuantifiedSatAuthority> {
        if self.dt_cert_grant_active
            && self
                .dt_cert_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, roots))
        {
            return Some(CurrentQuantifiedSatAuthority::Datatype);
        }
        if self.finite_table_cert_grant_active
            && self
                .finite_table_cert_witness_state
                .as_ref()
                .is_some_and(|state| state.is_pending_current_for(self, roots))
        {
            return Some(CurrentQuantifiedSatAuthority::FiniteTable);
        }
        if self.const_interp_cert_grant_active
            && self
                .const_interp_cert_witness_state
                .as_ref()
                .is_some_and(|state| state.is_pending_current_for(self, roots))
        {
            return Some(CurrentQuantifiedSatAuthority::ConstantInterpretation);
        }
        if self.mbqi_sat_cert_grant_active
            && self
                .mbqi_sat_cert_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, roots))
        {
            return Some(CurrentQuantifiedSatAuthority::Mbqi);
        }
        if self.bv_quantifier_full_domain_proof
            && self
                .bv_quantifier_full_domain_query_grant
                .as_ref()
                .is_some_and(|grant| grant.is_current_for(self, roots))
        {
            return Some(CurrentQuantifiedSatAuthority::BvFullDomain);
        }
        if self
            .cegqi_uf_recompletion_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(self, roots))
        {
            return Some(CurrentQuantifiedSatAuthority::CegqiUfRecompletion);
        }
        None
    }

    /// Whether the model-free CEGQI SAT publication exception is backed by
    /// exact-current MBQI evidence for the live authored roots.
    ///
    /// The Boolean marker is routing state only.  Keeping this predicate at
    /// the final mapper boundary prevents a stale or manually-set legacy bit
    /// from exempting a model-less `forall` result from fail-closed handling.
    fn has_current_model_free_mbqi_authority(&self, roots: &[TermId]) -> bool {
        self.has_current_model_free_mbqi_sat_authority(roots)
    }

    fn replay_exact_finite_quantifier_root(&mut self, root: TermId) -> Option<TermId> {
        finite_expansion_replay::replay(&mut self.ctx.terms, root)
    }

    /// Re-authenticate a fully-ground finite expansion and return the complete
    /// root vector the retained model must satisfy.
    ///
    /// `finite_domain_expand_with_instances` is a transformation capability,
    /// not blanket equivalence authority: the legacy generic multi-Int path can
    /// enumerate a conjunctively bounded box without proving the body vacuous
    /// outside it. Keep this publication recognizer narrower than that
    /// capability. It accepts only the existing full-domain BV route and the
    /// dedicated single-Int guarded-OR route, both with nested quantifiers
    /// excluded. A derived-bound/TLS expansion also declines because canonical
    /// standalone replay of the authored root cannot reproduce it.
    fn exact_finite_expansion_model_roots(
        &mut self,
        original: &[TermId],
        evidence: &ExactFiniteExpansionEvidence,
    ) -> Option<Vec<TermId>> {
        // This is certificate replay, not producer preprocessing.  It must be
        // a theorem of the authored syntax alone, independent of entailed-bound
        // or Bool-instantiation hints left by any surrounding solve.
        let _standalone_replay = crate::skolemize::scoped_standalone_finite_domain_replay();
        macro_rules! decline {
            ($reason:expr) => {{
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!("CERT/exact-finite-expansion: decline ({})", $reason);
                }
                return None;
            }};
        }
        if evidence.records.is_empty()
            || evidence.expanded_assertions.is_empty()
            || evidence
                .expanded_assertions
                .iter()
                .any(|&root| contains_quantifier(&self.ctx.terms, root))
        {
            decline!("empty evidence or residual quantifier");
        }

        let mut matched_records = vec![false; evidence.records.len()];
        let mut quantified_roots = 0usize;
        for (assertion_index, &assertion) in original.iter().enumerate() {
            if !contains_quantifier(&self.ctx.terms, assertion) {
                continue;
            }
            quantified_roots += 1;
            let record_index =
                evidence
                    .records
                    .iter()
                    .enumerate()
                    .find_map(|(record_index, record)| {
                        (!matched_records[record_index]
                            && record.assertion_index == assertion_index
                            && record.original == assertion)
                            .then_some(record_index)
                    });
            let Some(record_index) = record_index else {
                decline!("missing one-to-one expansion record");
            };
            let recorded_expansion = evidence.records[record_index].expanded;
            if evidence.expanded_assertions.get(assertion_index).copied()
                != Some(recorded_expansion)
                || contains_quantifier(&self.ctx.terms, recorded_expansion)
            {
                decline!("recorded replacement differs from actual solved root");
            }

            // Independently reproduce the exact replacement term. Equality,
            // not mere recognizer success, is load-bearing: strict-int or
            // bridge rewrites that changed the solved root without synchronised
            // provenance must fail closed.
            let Some(canonical) = self.replay_exact_finite_quantifier_root(assertion) else {
                decline!("canonical independent replay declined");
            };
            if canonical != recorded_expansion {
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!(
                        "CERT/exact-finite-expansion: canonical={canonical:?} recorded={recorded_expansion:?}"
                    );
                }
                decline!("canonical replay differs from recorded replacement");
            }
            matched_records[record_index] = true;
        }

        if quantified_roots == 0
            || quantified_roots != evidence.records.len()
            || matched_records.iter().any(|matched| !matched)
        {
            decline!("incomplete, duplicate, or extra expansion records");
        }

        // Validate exactly what the ground solver received, plus any authored
        // ground siblings reattached after unit preprocessing. The expansion
        // grant discharges quantified leaves only; it never waives a ground
        // obligation from the complete public root window.
        let mut model_roots = evidence.expanded_assertions.to_vec();
        for &assertion in original {
            if !contains_quantifier(&self.ctx.terms, assertion) && !model_roots.contains(&assertion)
            {
                model_roots.push(assertion);
            }
        }
        Some(model_roots)
    }

    /// Independently expand an exact public root vector for model validation.
    ///
    /// Pre-solve equivalence rewrites can make the root recorded by the ground
    /// expansion differ from the authored root retained by the public model
    /// gate. A grant may name the authored vector only after replaying the same
    /// narrow exact expansion directly on every authored quantified root and
    /// checking the retained model against those replacements too.
    fn canonical_public_finite_expansion_model_roots(
        &mut self,
        roots: &[TermId],
    ) -> Option<Vec<TermId>> {
        let _standalone_replay = crate::skolemize::scoped_standalone_finite_domain_replay();
        let mut model_roots = Vec::with_capacity(roots.len());
        let mut quantified_roots = 0usize;
        for &root in roots {
            if !contains_quantifier(&self.ctx.terms, root) {
                model_roots.push(root);
                continue;
            }
            quantified_roots += 1;
            let expanded = self.replay_exact_finite_quantifier_root(root)?;
            model_roots.push(expanded);
        }
        (quantified_roots > 0).then_some(model_roots)
    }

    fn install_exact_finite_expansion_sat_authority(
        &mut self,
        original: &[TermId],
        evidence: &ExactFiniteExpansionEvidence,
    ) -> bool {
        let Some(mut model_roots) = self.exact_finite_expansion_model_roots(original, evidence)
        else {
            return false;
        };

        // The solve-time `original` snapshot can already contain exact
        // preprocessing rewrites. Public SAT authority must instead name the
        // pre-solve authored vector used by every final gate. Validate both
        // representations under the same retained model; never retarget the
        // ground record by syntax alone.
        let authority_roots = if self.independent_gate_authored_assertions.is_some() {
            self.independent_gate_query_roots()
        } else {
            original.to_vec()
        };
        if authority_roots != original {
            let Some(public_model_roots) =
                self.canonical_public_finite_expansion_model_roots(&authority_roots)
            else {
                return false;
            };
            for root in public_model_roots {
                if !model_roots.contains(&root) {
                    model_roots.push(root);
                }
            }
        }
        let Some(checked) =
            CheckedFiniteExpansionSatAuthority::for_current(self, &authority_roots, &model_roots)
        else {
            return false;
        };
        self.install_finite_expansion_sat_authority(checked)
    }

    /// Map theory-solve result through quantifier/CEGQI semantics.
    ///
    /// Handles CEGQI forall/exists result inversion, E-matching incompleteness,
    /// and assertion restoration after quantifier preprocessing.
    pub(in crate::executor) fn map_quantifier_result(
        &mut self,
        result: Result<SolveResult>,
        qr: QuantifierProcessingResult,
        category: LogicCategory,
    ) -> Result<SolveResult> {
        let QuantifierProcessingResult {
            has_uninstantiated_quantifiers,
            reached_instantiation_limit,
            has_deferred,
            cegqi_has_forall,
            cegqi_has_exists,
            ematching_added_instantiations,
            refinement_assertions,
            cegqi_ce_lemma_ids,
            cegqi_ce_lemma_groups,
            has_completely_unhandled_quantifiers,
            unhandled_quantifiers,
            ematching_has_exists,
            ematching_rounds_completed,
            ematching_instances_created,
            original_assertions,
            exact_finite_expansion,
            exact_array_negation,
            cegqi_state,
            has_unsafe_partial_quantifiers,
            quantifiers_supported_by_uf_completion,
        } = qr;
        let cegqi_source_context_stamp = cegqi_has_forall.then(|| self.ctx.source_context_stamp());

        // Exact finite-array exhaustion is cumulative for this external query.
        // Demand, E-matching, MBQI, and CEGQI re-solves cannot replenish it, so
        // do not let an initial Unknown/SAT demotion enter a refinement loop or
        // a certificate path that could manufacture a later SAT proposal.
        // Restore the pre-quantifier assertion surface exactly as the ordinary
        // tail would, then return the canonical resource Unknown.
        if !self.finite_array_expansion.is_complete()
            && !matches!(&result, Ok(SolveResult::Unsat(_)))
        {
            self.publish_unknown_from_origin(UnknownOrigin::DeterministicResourceBudget);
            let mut final_result = Ok(SolveResult::Unknown);
            self.restore_assertions(
                original_assertions,
                &mut final_result,
                category,
                has_uninstantiated_quantifiers,
                false,
                false,
            );
            return final_result;
        }

        // Phase 0 (M5 demand lane, PRODUCTION for classified families): on-demand
        // frontier flush + fence drain. When the demand lane parked over-frontier
        // instances (LAW #7) and the frontier-gated first solve did NOT already
        // refute, bump `F` and flush the newly-under-frontier parked instances (LAW
        // #1), re-solving each bump; then, before concluding, fence-drain any
        // residual parked queue (LAW #2). Inert (returns `result` verbatim) unless
        // the lane armed — i.e. a classified self-chaining/bridge-cycle family was
        // present (`demand_lane_armed` false otherwise ⇒ byte-identical).
        let result = self.demand_refine(result, category);

        // Phase 1: Interleaved E-matching refinement (#5927).
        let mut ems = self.run_interleaved_ematching(
            result,
            &refinement_assertions,
            &cegqi_ce_lemma_ids,
            has_uninstantiated_quantifiers,
            ematching_added_instantiations,
            reached_instantiation_limit,
            ematching_rounds_completed,
            ematching_instances_created,
            category,
        );
        self.last_statistics.ematching_rounds_completed = ems.ematching_rounds_completed;
        self.last_statistics.ematching_instances_created = ems.ematching_instances_created;

        self.accept_strict_producer_refutation(&mut ems.result);
        // Complete E-matching CAMPAIGN guard for the left-inverse SAT
        // certificate (#2774): every quantifier produced an accepted match
        // pre- and post-interleaving, no instantiation limit was hit, no
        // cost-capped instance was deferred, and no existential remains. This
        // is deliberately not called domain coverage — one match is not
        // coverage. Soundness comes from the left-inverse certificate
        // constructing a total interpretation and re-verifying every original
        // assertion; this campaign guard is defense in depth.
        let full_ematching_coverage = !has_uninstantiated_quantifiers
            && !ems.has_uninstantiated_quantifiers
            && !reached_instantiation_limit
            && !ems.reached_instantiation_limit
            && !has_deferred
            && !ematching_has_exists;

        // Phase 2: Classify result through CEGQI/E-matching semantics.
        //
        // Timed as its own bucket. `phase.quantifier_result_mapping.seconds`
        // covers the interleaved refinement AND this arm, and the two are very
        // different work: refinement is E-matching plus ground re-solves, while
        // classification runs MBQI / CEGQI disambiguation / certificate sub-solves.
        // Attributing them separately is what tells you whether a budget-bound
        // quantified solve died in the instance flood or somewhere else.
        let classify_started_at = std::time::Instant::now();
        let mut final_result = self.classify_quantifier_result(
            ems.result,
            ems.ematching_added_instantiations,
            ems.reached_instantiation_limit,
            ems.unsat_from_interleaved,
            ems.has_uninstantiated_quantifiers,
            has_deferred,
            cegqi_has_forall,
            cegqi_has_exists,
            &cegqi_ce_lemma_ids,
            &cegqi_ce_lemma_groups,
            has_completely_unhandled_quantifiers,
            &unhandled_quantifiers,
            ematching_has_exists,
            refinement_assertions.as_deref(),
            &cegqi_state,
            category,
            has_unsafe_partial_quantifiers,
            quantifiers_supported_by_uf_completion,
        );
        self.add_phase_seconds(
            "time.quantifier.classify_seconds",
            classify_started_at.elapsed().as_secs_f64(),
        );
        if self.quantified_proof_translation_incomplete
            && matches!(final_result, Ok(SolveResult::Unsat(_)))
        {
            // The translation-incomplete bit is a conservative dependency
            // marker, not verdict authority.  A solve may have encountered an
            // unsupported instance and still close a different, fully-derived
            // authored-scope refutation.  Prefer that independently checked
            // proof when it exists; only the strict checker may discharge the
            // marker.  A free preprocessor/instance assumption is rejected by
            // the same scope check and therefore still fails closed below.
            if self.produce_proofs_enabled() && self.last_proof.is_none() {
                self.build_unsat_proof();
            }
            let live_proof_is_strict = self.last_proof.as_ref().is_some_and(|proof| {
                match self.check_proof_strict_with_datatypes(proof) {
                    Ok(_) => true,
                    Err(error) => {
                        if ay_core::misc_cli_flags().trace_cegqi_attr {
                            eprintln!(
                                "[quant-proof] incomplete translation proof declined: {error}"
                            );
                            for (index, step) in proof.steps.iter().take(64).enumerate() {
                                eprintln!("[quant-proof] proof[{index}] = {step:?}");
                            }
                        }
                        false
                    }
                }
            });
            if !live_proof_is_strict && !self.translate_refinement_seeded_replay() {
                final_result =
                    self.quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierUnhandled);
            } else if ay_core::misc_cli_flags().trace_cegqi_attr {
                eprintln!(
                    "[quant-proof] strict authored-scope proof discharged incomplete translation"
                );
            }
        }

        // Phase 2.4 (CONSTANT-INTERPRETATION certificate): consult the
        // narrow all-`forall` constant-function class before the more general
        // finite-table certificate. Besides avoiding redundant work, this
        // preserves the certificate's exact interpretation as the published
        // witness for formulas such as `forall x. P(x)`.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && self.quantifier_sat_cert_consult_admitted()
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = original_assertions
                .as_deref()
                .or(refinement_assertions.as_deref())
            {
                let snapshot = snapshot.to_vec();
                if self
                    .try_const_interp_sat_certificate(&snapshot, category)
                    .is_some()
                {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.const_interp_cert_grant_active = true;
                    self.last_unknown_reason = None;
                    final_result = Ok(SolveResult::Sat);
                }
            }
        }

        // Phase 2.5 (CAP-1 certified MBQI SAT): a quantifier-incompleteness
        // Unknown may still be a certifiable SAT when every snapshot `forall`
        // lies in the conservative finite-table + default class. The
        // certificate re-verifies EVERY snapshot assertion under an explicitly
        // constructed interpretation (see `try_finite_table_sat_certificate`
        // for the machine-checked totality argument), so it is self-contained:
        // it never trusts the classification that produced the Unknown, and it
        // can only upgrade a fail-closed Unknown to Sat — an Unsat (or any
        // non-quantifier Unknown reason, e.g. Timeout/Incomplete) is never
        // touched.
        let mut finite_table_sat_certificate = false;
        // Admits the quantifier-incompleteness labels, plus a load-derived
        // `Timeout` label while the enclosing solve is genuinely live (see
        // `quantifier_sat_cert_consult_admitted`). CCMC M1: a
        // patterned/curried forall whose trigger never e-matched a ground app
        // lands in `QuantifierEmatchingExistsIncomplete`; it is SAFE to consult
        // the finite-table certificate there — the cert partition
        // (`try_finite_table_sat_certificate`) rejects any snapshot whose top
        // level contains an exists / nested quantifier (grant-only,
        // fail-closed), so a genuine existential is never wrongly discharged.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && self.quantifier_sat_cert_consult_admitted()
            // M4 (item 4, CERTIFICATE DISCIPLINE): consult the finite-table SAT
            // certificate ONLY after a full grant-only flush — a parked-nonempty
            // state (the fence hit the deadline/ceiling and left instances withheld)
            // must NEVER grant Sat, because a withheld parked instance could be the
            // refutation. `demand_parked_blocks_sat` is false on production (lane not
            // armed) so this is byte-identical there.
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = original_assertions
                .as_deref()
                .or(refinement_assertions.as_deref())
            {
                let snapshot = snapshot.to_vec();
                // A primary theory lane may return `Unknown` without retaining
                // a model even though the authenticated quantifier-free
                // remainder is SAT.  The finite/default certificates need that
                // exact ground witness as the base interpretation they complete.
                // Install it in the original Context (never import a model from
                // a cloned TermStore), then let the self-contained certificate
                // re-check every ground assertion and quantified obligation.
                let ground_model_ready =
                    self.ensure_snapshot_ground_model_for_completion(&snapshot, category);
                if ground_model_ready
                    && (self
                        .try_finite_table_sat_certificate(&snapshot, category)
                        .is_some()
                    // (#p2-default-row) c2: the n-ary bare-tuple + default-row
                    // certificate (multi-binder CAP-1 generalization, e.g.
                    // `∀x,y:Int. p(x,y)`). Grant-only, self-contained,
                    // fail-closed — same discipline as CAP-1.
                    || self
                        .try_default_row_sat_certificate(&snapshot, category)
                        .is_some())
                {
                    finite_table_sat_certificate = true;
                    // A finite/default completion is a distinct SAT authority.
                    // It must never inherit a DT grant from an earlier
                    // classification of this candidate.
                    self.revoke_dt_sat_authority();
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.finite_table_cert_grant_active = true;
                    self.last_unknown_reason = None;
                    final_result = Ok(SolveResult::Sat);
                }
            }
        }

        // Phase 2.5f (EXACT CLOSED-SENTENCE certificate, UNKNOWN route): a
        // symbol-free theorem can strand the lane in a quantifier-class
        // `Unknown` without ever reaching the public gate — measured on both
        // `∀x:Int. (2|x ∨ 2|x+1)` and `∀x:Int. ∃y:Int. x<y`. Nothing e-matches
        // because there is no uninterpreted head. The certificate recognizes
        // only independently proved structural theorem schemas; no QE/solver
        // candidate is authority.
        //
        // Grant-only and self-contained: it never trusts the classification
        // that produced the `Unknown`. The returned non-cloneable evidence is
        // bound to this query/source/ordered-root window and must be consumed
        // by the dedicated installer before the shared MBQI-compatible handoff
        // becomes active.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && self.quantifier_sat_cert_consult_admitted()
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = original_assertions
                .as_deref()
                .or(refinement_assertions.as_deref())
            {
                let snapshot = snapshot.to_vec();
                if let Some(evidence) =
                    self.try_valid_closed_sentence_sat_certificate(&snapshot, category)
                {
                    if self.install_exact_closed_sentence_sat_authority(evidence) {
                        self.defer_model_validation = false;
                        self.last_model_validated = true;
                        self.last_unknown_reason = None;
                        final_result = Ok(SolveResult::Sat);
                    }
                }
            }
        }

        // Phase 2.5c (CONSTANT-INTERPRETATION certificate): an all-`forall`
        // snapshot whose axioms are satisfied by pinning a few uninterpreted
        // heads to CONSTANT functions lands here as a quantifier-incompleteness
        // `Unknown` (nothing e-matches, so no lane can close it).
        // `try_const_interp_sat_certificate` substitutes the candidate
        // interpretation into every body, replaces the binders with FRESH
        // constants, and requires an independent ground-solver `Unsat` on the
        // NEGATED body — one accepting `Unsat` per assertion, all under one
        // shared interpretation. Grant-only and self-contained: it never trusts
        // the classification that produced the `Unknown`, only upgrades a
        // fail-closed quantifier-class `Unknown` to `Sat`, and never touches
        // `Unsat`. The `QuantifierEmatchingExistsIncomplete` variant is safe in
        // the guard because the certificate's own partition rejects any
        // snapshot with a non-top-level-`forall` assertion or a nested
        // quantifier, so a genuine existential can never be discharged here.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if self
                    .try_const_interp_sat_certificate(&snapshot, category)
                    .is_some()
                {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    // Emission-gate authority. Recorded on this route too (the
                    // DT arms' lesson, not the finite-table arms'): the funnel
                    // would otherwise re-check the candidate model against
                    // universals this certificate has already discharged and
                    // fail closed on an infinite binder domain.
                    self.const_interp_cert_grant_active = true;
                    self.last_unknown_reason = None;
                    final_result = Ok(SolveResult::Sat);
                }
            }
        }

        // Phase 2.5b (DT-MBQI-Sat certificate): a datatype-binder `forall`
        // whose body is F4 cell-invariant (`forall x:DT. atom-over-{uf(x)}`)
        // lands here as a quantifier-incompleteness `Unknown` (the datatype
        // binder stays MBQI-unsafe). `try_dt_model_sat_certificate` re-verifies
        // EVERY snapshot assertion under an explicitly completed interpretation
        // (grant-only, self-contained, `AY_DT_CERT`-gated: `None` — hence
        // byte-identical — unless `AY_DT_CERT=on`), so a genuine existential /
        // bridge / mixed snapshot is never wrongly discharged (all-or-nothing
        // over F4). It only ever upgrades a fail-closed quantifier-class
        // `Unknown` to `Sat`; it never touches `Unsat`.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if let Some(evidence) = self.try_dt_model_sat_certificate(&snapshot, category) {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    // The post-solve certificate is the same all-or-nothing
                    // authority as the re-sequencing certificate.  F4 installs
                    // its exact completed table model M′ into `last_model`;
                    // F2/G validate the retained candidate directly; and an
                    // unmaterialized F3/W1 selector bridge is refused.
                    // Record the grant on this path too so the public emission
                    // funnel does not recheck an already-certified model against
                    // universals.  Omitting this made the verdict depend on
                    // whether the earlier bounded re-sequencing probe happened
                    // to finish before its wall-clock budget.
                    if self.install_dt_sat_authority(evidence) {
                        self.last_unknown_reason = None;
                        final_result = Ok(SolveResult::Sat);
                    } else {
                        self.last_model_validated = false;
                        self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                    }
                }
            }
        }

        // Phase 2.5d (finite-table authority for a provisional Sat): CEGQI can
        // classify the instantiated ground remainder Sat before restoration,
        // so the Unknown-only grant arm above is skipped. When an exact
        // pre-preprocessing snapshot is available, run the same all-or-nothing
        // certificate now, while the outer candidate model is still retained.
        // This is authority-only: a decline leaves the provisional result and
        // ordinary restoration/validation path untouched.
        if matches!(final_result, Ok(SolveResult::Sat))
            && !finite_table_sat_certificate
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = original_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if self
                    .try_finite_table_sat_certificate(&snapshot, category)
                    .is_some()
                {
                    finite_table_sat_certificate = true;
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.finite_table_cert_grant_active = true;
                    self.last_unknown_reason = None;
                }
            }
        }

        // Phase 2.5e (EXACT CLOSED-SENTENCE certificate, AUTHORITY RECORD on
        // the already-`Sat` route). Changes no verdict: `final_result` is
        // already `Sat`. It records that every assertion was proved VALID, so
        // the emission funnel does not throw that evidence away.
        //
        // The public model gate cannot derive a model entry for a symbol-free
        // sentence. This arm records a structural theorem only after consuming
        // its exact query/source/root-bound token; a raw Boolean flag or a
        // sampled deep-QE residue cannot reach the handoff.
        if matches!(final_result, Ok(SolveResult::Sat))
            && !finite_table_sat_certificate
            && !self.dt_cert_grant_active
            && !self.finite_table_cert_grant_active
            && !self.const_interp_cert_grant_active
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = original_assertions
                .as_deref()
                .or(refinement_assertions.as_deref())
            {
                let snapshot = snapshot.to_vec();
                if let Some(evidence) =
                    self.try_valid_closed_sentence_sat_certificate(&snapshot, category)
                {
                    if self.install_exact_closed_sentence_sat_authority(evidence) {
                        self.defer_model_validation = false;
                        self.last_model_validated = true;
                        self.last_unknown_reason = None;
                    } else {
                        final_result = self.cegqi_fail_closed_unknown();
                    }
                }
            }
        }

        self.route_exact_array_negation_result(
            &mut final_result,
            original_assertions.as_deref(),
            exact_array_negation.as_ref(),
        );

        self.install_finite_expansion_if_sat(
            &final_result,
            full_ematching_coverage,
            original_assertions.as_deref(),
            exact_finite_expansion.as_ref(),
        );

        // Preserve only a routing fact here: before restoration, authenticate
        // that the ground UNSAT was obtained after the exact recorded
        // finite-domain replacement of every solve-time quantified root.  The
        // record is never retargeted to authored roots.  After restoration the
        // semantic certificate below independently re-expands the immutable
        // public roots and checks their complete ground vector itself.
        let exact_finite_expansion_unsat_route = matches!(final_result, Ok(SolveResult::Unsat(_)))
            && full_ematching_coverage
            && match (
                original_assertions.as_deref(),
                exact_finite_expansion.as_ref(),
            ) {
                (Some(original), Some(expansion)) => self
                    .exact_finite_expansion_model_roots(original, expansion)
                    .is_some(),
                _ => false,
            };

        // Phase 3: Restore original assertions after solve (#2844).
        self.restore_assertions(
            original_assertions,
            &mut final_result,
            category,
            has_uninstantiated_quantifiers,
            full_ematching_coverage,
            finite_table_sat_certificate,
        );

        // Exact finite-expansion UNSAT theorem.  This is deliberately after
        // restoration: its private constructor sees only the current public
        // query epoch, canonical-expands those roots afresh, and accepts a
        // model-independent `false` conjunct or distinct-scalar assignment
        // clash.  A failed theorem leaves the ordinary mandatory strict-proof
        // gate in charge; explicit proof/self-check modes decline this lane.
        if exact_finite_expansion_unsat_route && matches!(final_result, Ok(SolveResult::Unsat(_))) {
            // `original_assertions` is the solve-time preprocessing snapshot,
            // which can differ from the always-on gate's authored vector. The
            // outer transaction restores this same vector on return; install it
            // now so the source theorem binds to the immutable public epoch,
            // never to the record's transformed root identity.
            let public_roots = self.independent_gate_query_roots();
            let prior_roots = std::mem::replace(&mut self.ctx.assertions, public_roots);
            if let Some(evidence) = self.try_authorize_current_query_exact_finite_expansion_unsat()
            {
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!("CERT/exact-finite-expansion-unsat: public theorem accepted");
                }
                let emitted = self.emit_checked_exact_finite_expansion_unsat(evidence);
                if !emitted.is_unsat() {
                    // A stop or strict-presentation request can arrive between
                    // authorization and emission. It must not leave the failed
                    // semantic lane's temporary public-root window installed
                    // for later strict reconstruction.
                    self.ctx.assertions = prior_roots;
                }
                final_result = Ok(emitted);
            } else if ay_core::misc_cli_flags().debug_cert {
                self.ctx.assertions = prior_roots;
                eprintln!("CERT/exact-finite-expansion-unsat: public theorem declined");
            } else {
                self.ctx.assertions = prior_roots;
            }
        }

        // Restoration may demote a DT-certified candidate after checking the
        // original assertion window.  Once the candidate is no longer SAT,
        // its DT authority is consumed and must not authorize a different
        // certificate that re-mints SAT below.
        if !matches!(final_result, Ok(SolveResult::Sat)) {
            self.revoke_dt_sat_authority();
            self.cegqi_uf_recompletion_grant = None;
        }

        // Phase 3.5 (CCMC M1): a candidate Sat can be demoted here to a
        // quantifier-class Unknown (typically
        // `QuantifierEmatchingExistsIncomplete`) by `restore_assertions` when a
        // PATTERNED/CURRIED forall was E-match-handled but skipped by model
        // validation and left no independent ground evidence — this is exactly
        // the fail-closed path the P0 fix introduced. The finite-table
        // certificate re-verifies the ENTIRE snapshot under an explicitly
        // constructed interpretation (grant-only, self-contained: it never
        // trusts the classification, only upgrades a fail-closed
        // quantifier-class Unknown into Sat, never touches Unsat, and rejects
        // any snapshot with exists/nested quantifiers), so it can still
        // discharge the curried grant shape that only surfaces AFTER restore.
        // Byte-identical to the pre-restore arm on every snapshot the cert
        // rejects; the parked-fence guard still applies.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
            && !self.ctx.assertions.is_empty()
        {
            let snapshot = self.ctx.assertions.clone();
            let ground_model_ready =
                self.ensure_snapshot_ground_model_for_completion(&snapshot, category);
            if ground_model_ready
                && (self
                        .try_finite_table_sat_certificate(&snapshot, category)
                        .is_some()
                    // (#p2-default-row) c2, post-restore mirror of the
                    // phase-2.5 arm.
                    || self
                        .try_default_row_sat_certificate(&snapshot, category)
                        .is_some())
            {
                // Phase 3.5 is a fresh finite/default grant.  In
                // particular, it cannot reuse a pre-restore DT grant that
                // restoration revoked when it demoted the old candidate.
                self.revoke_dt_sat_authority();
                self.defer_model_validation = false;
                self.last_model_validated = true;
                self.finite_table_cert_grant_active = true;
                self.last_unknown_reason = None;
                final_result = Ok(SolveResult::Sat);
            }
        }

        // Phase 3.5c (CONSTANT-INTERPRETATION certificate, post-restore): the
        // all-`forall` grant shape that only surfaces after
        // `restore_assertions` demotes a candidate `Sat` to a quantifier-class
        // `Unknown`. Same grant-only, fail-closed certificate as the
        // pre-restore arm; byte-identical on every snapshot it declines.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
        {
            // This is deliberately the RESTORED authored snapshot. The
            // refinement snapshot can contain generated ground instances and
            // therefore fails the certificate's all-top-level-forall partition,
            // discarding the very interpretation this post-restore phase is
            // meant to publish.
            let snapshot = self.ctx.assertions.clone();
            if self
                .try_const_interp_sat_certificate(&snapshot, category)
                .is_some()
            {
                self.defer_model_validation = false;
                self.last_model_validated = true;
                // Mirror the pre-restore arm: both paths certify the same
                // explicitly constructed interpretation, so both carry the
                // same emission-gate authority bit.
                self.const_interp_cert_grant_active = true;
                self.last_unknown_reason = None;
                final_result = Ok(SolveResult::Sat);
            }
        }

        // Phase 3.5b (DT-MBQI-Sat certificate, post-restore): the datatype-
        // binder F4 grant shape that only surfaces after `restore_assertions`
        // demotes a candidate Sat to a quantifier-class `Unknown`. Same
        // grant-only, `AY_DT_CERT`-gated, all-or-nothing certificate as the
        // pre-restore arm; byte-identical on every snapshot it declines.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if let Some(evidence) = self.try_dt_model_sat_certificate(&snapshot, category) {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    // Mirror the pre-restore DT grant arm above.  Both paths
                    // certify the completed model M', so both must carry the
                    // same emission-gate authority bit.
                    if self.install_dt_sat_authority(evidence) {
                        self.last_unknown_reason = None;
                        final_result = Ok(SolveResult::Sat);
                    } else {
                        self.last_model_validated = false;
                        self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                    }
                }
            }
        }

        // Phase 3.5d (mandatory quantified-model checker, post-certificate):
        // restoration can demote a genuine candidate Sat merely because its
        // generic MBQI sampler cannot exhaust an infinite-domain quantifier.
        // Give the SAME fail-closed checker used at the public SAT boundary a
        // chance to positively certify the now-restored assertions. This runs
        // only AFTER the model-producing finite-table, constant-interpretation,
        // and datatype certificates above: those authorities retain first
        // refusal because they install the canonical witness they proved.
        // Anything other than an all-conjunct `Confirmed` result leaves the
        // existing Unknown untouched; the public funnel re-runs this checker
        // before publication, so this bridge cannot bypass the final boundary.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
            && !self.dt_cert_grant_active
            && !self.finite_table_cert_grant_active
            && !self.const_interp_cert_grant_active
            && !self.demand_parked_blocks_sat()
            && self.quantified_model_gate_confirms_current_assertions()
        {
            self.defer_model_validation = false;
            self.last_model_validated = true;
            self.last_unknown_reason = None;
            self.last_result = Some(SolveResult::Sat);
            final_result = Ok(SolveResult::Sat);
        }

        // Phase 3.5u (EXACT CLOSED-SENTENCE certificate, UNSAT arm — U2):
        // nested-alternation closed sentences (`¬∃y.(range(y) ∧ ∀x.φ)`,
        // `∀x.(guard → ∃y.ψ)`) land here as a quantifier-class `Unknown`
        // because the closed-universal precheck requires quantifier-free
        // bodies and the CEGQI-forall refutation cannot be certified without
        // a surviving consequence set.  This is the symmetric sibling of the
        // Phase 2.5f VALIDITY certificate: the same partition (every authored
        // root closed and free of uninterpreted symbols/sorts) and the same
        // checked instruments (the reconfirmation primitive and empty-model
        // evaluation), applied to the sentence side to certify one authored
        // conjunct FALSE.  Grant-only and self-contained: it never trusts the
        // classification that produced the `Unknown`, and the sealed evidence
        // is consumed by the same mandatory certification mint as the
        // closed-forall UNSAT theorem (`emit_checked_exact_unsat`), so the
        // publication still carries a one-shot exact-semantic certificate.
        //
        // `ctx.assertions` can still be a transformed refinement window at
        // this point; install the canonical public roots for the mint and
        // emission exactly as the finite-expansion UNSAT lane above does.
        if matches!(final_result, Ok(SolveResult::Unknown))
            && matches!(
                self.last_unknown_reason,
                Some(
                    UnknownReason::QuantifierCegqiIncomplete
                        | UnknownReason::QuantifierUnhandled
                        | UnknownReason::QuantifierRoundLimit
                        | UnknownReason::QuantifierEmatchingExistsIncomplete
                )
            )
        {
            let public_roots = self.independent_gate_query_roots();
            let prior_roots = std::mem::replace(&mut self.ctx.assertions, public_roots);
            if let Some(evidence) = self.try_authorize_current_query_refuted_closed_sentence_unsat()
            {
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!("CERT/refuted-sentence: public theorem accepted");
                }
                let emitted = self.emit_checked_exact_closed_sentence_unsat(evidence);
                if !emitted.is_unsat() {
                    // A stop or strict-presentation request can arrive between
                    // authorization and emission; do not leave the failed
                    // lane's temporary public-root window installed.
                    self.ctx.assertions = prior_roots;
                }
                final_result = Ok(emitted);
            } else {
                self.ctx.assertions = prior_roots;
            }
        }

        // Phase 3.6c (CONSTANT-INTERPRETATION certificate, AUTHORITY RECORD on
        // the already-`Sat` route).
        //
        // This arm changes NO verdict. `final_result` is already `Sat`; all it
        // does is record that the constant-interpretation certificate verified
        // every snapshot assertion, so the public emission funnel does not
        // throw that evidence away.
        //
        // It exists because the quantifier lane can finish `Sat` with
        // `last_unknown_reason == None` while `restore_assertions` takes
        // neither its deferred-validation branch nor its restoration branch —
        // measured on `∀s:(Seq Int). 0 <= seq_len(s)`, where the lane returns
        // `Sat` and `apply_quantified_model_failclosed_gate` then publishes
        // `unknown` with `model-check-gate.quantified = "deferred-failclosed"`
        // and `:unknown.phase = "independent-model-check-gate"`. The gate is
        // right to fail closed on its own terms: it cannot ground-evaluate a
        // `forall` over the infinite `(Seq Int)` domain from the emitted model.
        // The certificate can, and did — by refuting the negated body under an
        // explicitly constructed interpretation. Recording the bit is exactly
        // what `finite_table_cert_grant_active` does for the sibling
        // certificate on ITS `Sat` route (the restoration-branch recompute).
        //
        // Skipped when another certificate already holds the authority: the
        // handoff in `apply_quantified_model_failclosed_gate` returns on the
        // first marker it sees, so a second one only costs nested solves.
        if matches!(final_result, Ok(SolveResult::Sat))
            && !self.dt_cert_grant_active
            && !self.finite_table_cert_grant_active
            && !self.const_interp_cert_grant_active
            && {
                let public_roots = self.independent_gate_query_roots();
                self.current_quantified_sat_authority(&public_roots)
                    .is_none()
            }
            && !self.demand_parked_blocks_sat()
        {
            if let Some(snapshot) = refinement_assertions.as_deref() {
                let snapshot = snapshot.to_vec();
                if self
                    .try_const_interp_sat_certificate(&snapshot, category)
                    .is_some()
                {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.const_interp_cert_grant_active = true;
                }
            }
        }

        // Phase 3.7 (exact public-root table-certificate rescue): some CEGQI lanes
        // leave either a provisional `Sat` or a quantifier-incompleteness
        // `Unknown` after internal refinement. Internal work can also advance the
        // frontend source stamp, so the final CEGQI postflight below must reject
        // old routing authority. An independently checked finite/default-table
        // or constant-interpretation model for the exact public roots is fresh
        // whole-query authority and may replace either provisional outcome.
        //
        // Require the always-on independent gate's pre-solve root snapshot, then
        // append temporary assumptions through the same canonical constructor
        // used by every public model gate. `ctx.assertions` can still be a
        // generated/merged refinement window at this point. The producer checks
        // every public root simultaneously, and the Pending package must
        // re-authenticate that identical ordered vector before it can change the
        // verdict. A stop, failed ground-model reconstruction, producer decline,
        // or stale package mints no SAT authority: an Unknown stays Unknown and
        // final postflight demotes any stale provisional Sat. A residual
        // demand queue is deliberately not a refusal premise here. Unlike the
        // earlier refinement-window certificate arms, this producer proves one
        // total model for the complete public root vector. Every parked item
        // is an instance of one of those authored universals, so the exact-root
        // theorem strictly subsumes the unfinished instance search. If the
        // producer cannot prove that stronger fact, it declines and the parked
        // lane's Unknown remains unchanged.
        let cegqi_source_stamp_is_stale = cegqi_source_context_stamp
            .as_ref()
            .is_some_and(|stamp| stamp != &self.ctx.source_context_stamp());
        let public_table_rescue_candidate =
            matches!(final_result, Ok(SolveResult::Sat | SolveResult::Unknown));
        let public_table_rescue_aborted =
            public_table_rescue_candidate && self.should_abort_theory_loop();
        let public_table_rescue_parked = self.demand_parked_blocks_sat();
        if public_table_rescue_candidate
            && !public_table_rescue_aborted
            && self.independent_gate_authored_assertions.is_some()
        {
            let public_roots = self.independent_gate_query_roots();
            if !public_roots.is_empty() {
                // This rescue is not CEGQI-specific. E-matching and other
                // quantified routes can also mint a checked table package for
                // a rewritten/refinement window whose roots differ from the
                // authored public query. In that case the stale package must
                // trigger a fresh all-public-roots theorem instead of reaching
                // the SAT funnel with only a legacy routing bit.
                let mut has_top_level_forall = false;
                let public_roots_match_table_partition = public_roots.iter().all(|&root| {
                    if matches!(self.ctx.terms.get(root), TermData::Forall(..)) {
                        has_top_level_forall = true;
                        true
                    } else {
                        !contains_quantifier(&self.ctx.terms, root)
                    }
                }) && has_top_level_forall;
                let exact_public_transport =
                    self.has_current_pending_certificate_model_transport(&public_roots);
                let exact_public_authority = self.current_quantified_sat_authority(&public_roots);
                let has_table_routing_bit =
                    self.finite_table_cert_grant_active || self.const_interp_cert_grant_active;
                let rescue_needed = exact_public_table_rescue_needed(
                    &final_result,
                    self.last_unknown_reason,
                    public_roots_match_table_partition,
                    cegqi_has_forall,
                    cegqi_source_stamp_is_stale,
                    has_table_routing_bit,
                    exact_public_transport,
                    exact_public_authority,
                );
                if rescue_needed {
                    if ay_core::misc_cli_flags().debug_cert {
                        eprintln!(
                            "CERT/public-root-table-rescue: begin ({} public roots, prior={:?}, authority={exact_public_authority:?}, reuse={exact_public_transport})",
                            public_roots.len(),
                            final_result
                        );
                    }
                    let mut certified = exact_public_transport;
                    if !certified {
                        // A routing bit scoped to a merged/refinement window is not
                        // public authority and must not preempt the new exact-root
                        // finite lane at the SAT funnel. Retire every competing
                        // executor grant and model-side seal through the canonical
                        // lifecycle operation before minting the fresh package.
                        // On an eligible Unknown this can include a current
                        // quantified-only proof: that proof did not decide the
                        // whole query, whereas the new producer must cover every
                        // public root or decline.
                        self.clear_quantified_sat_authority();

                        let ground_model_ready = self
                            .ensure_snapshot_ground_model_for_completion(&public_roots, category);
                        let finite_producer_accepted = ground_model_ready
                            && (self
                                .try_finite_table_sat_certificate(&public_roots, category)
                                .is_some()
                                || self
                                    .try_default_row_sat_certificate(&public_roots, category)
                                    .is_some());
                        certified =
                            finite_producer_accepted
                                && self.finite_table_cert_witness_state.as_ref().is_some_and(
                                    |state| state.is_pending_current_for(self, &public_roots),
                                );
                        if certified {
                            self.finite_table_cert_grant_active = true;
                        } else {
                            // Constant-interpretation certification constructs
                            // and checks its own exact model, so it remains a
                            // valid public-root producer even when reconstructing
                            // the provisional ground model was impossible. Keep
                            // the two affine transports disjoint: a declined or
                            // stale finite package is retired before the const
                            // producer can park its replacement.
                            self.clear_quantified_sat_authority();
                            let const_producer_accepted = self
                                .try_const_interp_sat_certificate(&public_roots, category)
                                .is_some();
                            certified = const_producer_accepted
                                && self.const_interp_cert_witness_state.as_ref().is_some_and(
                                    |state| state.is_pending_current_for(self, &public_roots),
                                );
                            if certified {
                                self.const_interp_cert_grant_active = true;
                            }
                        }
                    }
                    if certified {
                        // Make every downstream currentness check name the same
                        // exact roots. The enclosing check-sat transaction restores
                        // this public vector as well, so publication cannot
                        // silently rebind the package to a refinement window.
                        self.ctx.assertions = public_roots;
                        self.defer_model_validation = false;
                        self.last_model_validated = true;
                        self.last_unknown_reason = None;
                        final_result = Ok(SolveResult::Sat);
                        if public_table_rescue_parked {
                            self.last_statistics.set_int(
                                "quantifier.demand.exact_root_theorem_superseded_parked",
                                1,
                            );
                        }
                        if ay_core::misc_cli_flags().debug_cert {
                            eprintln!("CERT/public-root-table-rescue: granted");
                        }
                    } else {
                        // A producer that returned a package which failed the
                        // immediate exact-current check cannot leave transport
                        // state for a later path to activate accidentally.
                        self.clear_quantified_sat_authority();
                        if ay_core::misc_cli_flags().debug_cert {
                            eprintln!("CERT/public-root-table-rescue: declined");
                        }
                    }
                }
            }
        }

        // Final publication postflight. Certificate work above can outlive the
        // solve that first observed a stop; no SAT route may cross the mapping
        // boundary after an interrupt/deadline/memory request. A closed-valid-
        // sentence certificate is deliberately model-free, so its scoped
        // all-assertion authority is the sole exception to the retained-model
        // requirement.
        // Recompute after the rescue's same-Context ground reconstruction and
        // certificate producers: their nested work may advance source state.
        // A pre-rescue `false` must never authorize the old CEGQI candidate if
        // every fresh producer subsequently declines.
        let cegqi_source_stamp_is_stale = cegqi_source_context_stamp
            .as_ref()
            .is_some_and(|stamp| stamp != &self.ctx.source_context_stamp());
        let postflight_roots = self.independent_gate_query_roots();
        let current_quantified_sat_authority =
            self.current_quantified_sat_authority(&postflight_roots);
        let has_current_model_free_mbqi_authority =
            self.has_current_model_free_mbqi_authority(&postflight_roots);
        let has_pending_certificate_model =
            self.has_current_pending_certificate_model_transport(&postflight_roots);
        if cegqi_sat_postflight_must_fail_closed(CegqiSatPostflightFacts {
            final_result_is_sat: matches!(final_result, Ok(SolveResult::Sat)),
            should_abort: self.should_abort_theory_loop(),
            cegqi_has_forall,
            has_retained_model: self.last_model.is_some(),
            has_pending_certificate_model,
            has_current_model_free_mbqi_authority,
            cegqi_source_stamp_is_stale,
            has_current_quantified_sat_authority: current_quantified_sat_authority.is_some(),
        }) {
            return self.cegqi_fail_closed_unknown();
        }

        final_result
    }

    /// M5 demand lane (PRODUCTION for classified families) — Phase 0 refinement:
    /// the outer demand loop that turns the frontier gate into a decision procedure.
    ///
    /// LAW #6 (interleave engages on Sat-OR-Unknown-with-model): a definitive
    /// UNSAT is the frontier-gated refutation — return it untouched (this is the
    /// takesome flip). Otherwise, while over-frontier instances are parked and the
    /// frontier ceiling is not hit:
    ///   LAW #1 (unconditional under-frontier flush): bump `F`, assert EVERY parked
    ///   instance now at generation `<= F` (model filtering may ORDER, never
    ///   suppress — the parking-fixpoint trap), and re-solve.
    /// Then LAW #2 (fence): if any instances remain parked (still over the final
    /// frontier), drain the WHOLE queue directly — bypassing the E-matching seen
    /// memo, fresh budget — and re-solve once before any conclusion. The fence
    /// guarantees no Sat/Unknown is reported while a parked instance that could
    /// refute is withheld.
    ///
    /// SOUNDNESS: every asserted instance is a universal-instantiation consequence
    /// (adding it only strengthens the problem), so an UNSAT reached here is
    /// genuine and any surviving non-UNSAT is at least as strong as the eager
    /// path's. The lane is armed only when a classified self-chaining/bridge-cycle
    /// family is present, so this whole method is inert (`result` returned verbatim)
    /// on every unclassified-quantifier / force-eager solve (byte-identical).
    fn demand_refine(
        &mut self,
        mut result: Result<SolveResult>,
        category: LogicCategory,
    ) -> Result<SolveResult> {
        if !self.demand_lane_armed() {
            return result;
        }
        // A definitive UNSAT is the frontier-gated refutation: done (the flip).
        if matches!(result, Ok(SolveResult::Unsat(_))) {
            return result;
        }
        // LAW #6: engage only on Sat / Unknown (a model or a fail-closed Unknown);
        // a hard error is left alone.
        if !matches!(result, Ok(SolveResult::Sat) | Ok(SolveResult::Unknown)) {
            return result;
        }
        // Frontier ceiling: bound the on-demand deepening. The gated families are
        // recursive-datatype defining axioms whose refutations (per the campaign's
        // measured depth analysis) sit at F<=2; a handful of extra bumps is ample
        // insurance without unbounding the loop.
        const DEMAND_FRONTIER_CEILING: u32 = 8;

        // M4 (item 2, DEADLINE SHARE): the demand lane's fence/deepening work is
        // capped at 50% of the REMAINING deadline, reserving the other half for the
        // decisive fence-drain + ground solve. Principled split (the only magic
        // constant is the 50%): the iterative-deepening flush loop below runs under
        // the tightened sub-deadline; the full deadline is restored before the fence
        // drain so the final ground solve gets the reserved budget. On a null
        // deadline nothing is installed (and the restore is a no-op). SHADOW-ONLY —
        // `demand_refine` already early-returned on production.
        let original_deadline = self.solve_deadline.get();
        if let Some(dl) = original_deadline {
            let now = ay_core::time::Instant::now();
            if let Some(remaining) = dl.checked_duration_since(now) {
                if let Some(fence_dl) = now.checked_add(remaining / 2) {
                    self.solve_deadline.set(Some(fence_dl));
                }
            }
        }

        // LAW #1: flush under-frontier on demand, re-solving each bump. A definitive
        // UNSAT reached mid-loop is the refutation — record it and break so the
        // deadline restore (below) always runs before we return it.
        let mut refuted = false;
        loop {
            let has_parked = self
                .quantifier_manager
                .as_ref()
                .is_some_and(crate::quantifier_manager::QuantifierManager::demand_has_parked);
            let frontier = self.quantifier_manager.as_ref().map_or(
                0,
                crate::quantifier_manager::QuantifierManager::demand_frontier,
            );
            if !has_parked || frontier >= DEMAND_FRONTIER_CEILING || self.should_abort_theory_loop()
            {
                break;
            }
            let flushed = match self.quantifier_manager.as_mut() {
                Some(qm) => qm.demand_flush_under_frontier(&mut self.ctx.terms),
                None => break,
            };
            if !self.demand_assert_flushed(flushed) {
                // Nothing new asserted this bump — a further bump only raises F,
                // so keep going until the ceiling or the queue empties, but avoid
                // a no-progress re-solve.
                continue;
            }
            result = self.solve_for_category(category);
            if matches!(result, Ok(SolveResult::Unsat(_))) {
                refuted = true;
                break;
            }
        }

        // M4 (item 2): restore the full deadline for the decisive fence + ground
        // solve BEFORE any return path — the flush loop above consumed at most 50%
        // of the remaining budget; the fence gets the reserved remainder.
        self.solve_deadline.set(original_deadline);
        if refuted {
            return result;
        }

        // LAW #2: fence drain. Any residual parked instance (over the final
        // frontier) is asserted directly before we conclude. The fence drains the
        // WHOLE queue (grant-only — no model filter), bypassing the seen memo and
        // resetting the seen frame (M4), then re-solves under the reserved deadline.
        let residual = self
            .quantifier_manager
            .as_ref()
            .is_some_and(crate::quantifier_manager::QuantifierManager::demand_has_parked);
        if residual && !self.should_abort_theory_loop() {
            let drained = match self.quantifier_manager.as_mut() {
                Some(qm) => qm.demand_fence_drain(&mut self.ctx.terms),
                None => Vec::new(),
            };
            if self.demand_assert_flushed(drained) {
                result = self.solve_for_category(category);
            }
        }
        result
    }

    /// M4 (item 4, CERTIFICATE DISCIPLINE): whether a demand-lane PARKED-nonempty
    /// state must block a SAT certificate. True iff the demand lane is armed (a
    /// classified family was present) AND instances are still parked (the fence did
    /// not achieve a full grant-only flush — a deadline/ceiling cut it short), so a
    /// certificate would be granting Sat while a possibly-refuting instance is
    /// withheld. On any unclassified-quantifier / force-eager solve the lane is not
    /// armed and this is always `false` — byte-identical.
    ///
    /// This complements `QuantifierManager::has_deferred` (LAW #3), which already
    /// counts the parked queue so the ordinary classification routes a
    /// parked-nonempty state to Unknown; this guard closes the ONE re-upgrade path
    /// (the Phase 2.5 finite-table certificate) that does not consult `has_deferred`.
    fn demand_parked_blocks_sat(&self) -> bool {
        self.demand_lane_armed()
            && self
                .quantifier_manager
                .as_ref()
                .is_some_and(crate::quantifier_manager::QuantifierManager::demand_has_parked)
    }

    /// Assert flushed/fenced demand-lane instances into `ctx.assertions`,
    /// deduplicating against what is already present. Returns whether anything new
    /// was added. (The instances are E-matching instances of universally-asserted
    /// foralls — sound to assert; see `demand_refine`.)
    fn demand_assert_flushed(&mut self, instances: Vec<TermId>) -> bool {
        if instances.is_empty() {
            return false;
        }
        let existing: std::collections::HashSet<TermId> =
            self.ctx.assertions.iter().copied().collect();
        let mut added = false;
        for inst in instances {
            if existing.contains(&inst) {
                continue;
            }
            self.ctx.assertions.push(inst);
            added = true;
        }
        if added {
            // The parked queue currently retains only the instantiated TermId,
            // not an authenticated authored quantifier/binding token.  Preserve
            // the sound consequence for solving, but forbid its raw proof from
            // becoming an outer artifact.
            self.quantified_proof_translation_incomplete = true;
        }
        added
    }

    /// Classify the solve result through CEGQI/E-matching semantics.
    #[allow(clippy::too_many_arguments)]
    fn classify_quantifier_result(
        &mut self,
        result: Result<SolveResult>,
        ematching_added_instantiations: bool,
        reached_instantiation_limit: bool,
        unsat_from_interleaved: bool,
        has_uninstantiated_quantifiers: bool,
        has_deferred: bool,
        cegqi_has_forall: bool,
        cegqi_has_exists: bool,
        cegqi_ce_lemma_ids: &[TermId],
        cegqi_ce_lemma_groups: &[(TermId, Vec<TermId>)],
        has_completely_unhandled_quantifiers: bool,
        unhandled_quantifiers: &[TermId],
        ematching_has_exists: bool,
        refinement_assertions: Option<&[TermId]>,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
        has_unsafe_partial_quantifiers: bool,
        quantifiers_supported_by_uf_completion: bool,
    ) -> Result<SolveResult> {
        // One classification, one verdict: the structural marker describes THIS
        // classification only, so a stale `true` from an earlier solve can never
        // widen a later certificate consult.
        self.unsafe_partial_quantifier_unknown = false;
        let cegqi_mixed = cegqi_has_forall && cegqi_has_exists;
        if ay_core::misc_cli_flags().debug_cert {
            let kind = match &result {
                Ok(SolveResult::Sat) => "Sat",
                Ok(SolveResult::Unsat(_)) => "Unsat",
                Ok(SolveResult::Unknown) => "Unknown",
                Err(_) => "Err",
            };
            eprintln!(
                "CERT/classify: result={kind} em_added={ematching_added_instantiations} cegqi_f={cegqi_has_forall} cegqi_e={cegqi_has_exists} uninst={has_uninstantiated_quantifiers} unhandled={has_completely_unhandled_quantifiers}"
            );
            for &q in unhandled_quantifiers.iter().take(4) {
                eprintln!(
                    "CERT/classify unhandled quantifier: {}",
                    ay_proof::render_term_canonical(&self.ctx.terms, q)
                );
            }
        }
        // A CEGQI-forall UNSAT with no surviving CE identifier is not a raw
        // publication exception. Rewrites can erase the identifier while
        // leaving CE-derived constraints behind. Only the independently
        // reconstructed consequence set may authorize this verdict.
        if cegqi_has_forall
            && cegqi_ce_lemma_ids.is_empty()
            && matches!(result, Ok(SolveResult::Unsat(_)))
        {
            if let Some(checked) =
                cegqi_unsat_authority::certify(self, refinement_assertions, category)
            {
                return Ok(checked.publish(self));
            }
            // (#ground-core-authored-scope) The consequence reconstruction above
            // is the only authority for a CE-DERIVED refutation. It is not the
            // only authority for THIS verdict: when the authored
            // quantifier-free conjuncts refute on their own, the contradiction
            // owes nothing to any CE lemma or instance, so the missing CE
            // identifier is immaterial. Re-decided in isolation and published
            // through the ordinary funnel — see
            // `quantified_semantic_unsat_or_unknown`. Fail-closed on every leg,
            // so this can only convert a fail-closed `unknown` into a certified
            // `unsat`.
            if let Some(published) = justification::Justification::publish_if_established(
                self,
                refinement_assertions,
                category,
            ) {
                return Ok(published);
            }
            self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
            return self.cegqi_fail_closed_unknown();
        }
        // SOUNDNESS (#quant-alternation wrong-unsat): instances of a `forall`
        // in a disjunctive or conditional position are not top-level facts;
        // conjoining them can manufacture UNSAT. This applies to eager and
        // interleaved E-matching even when no uninstantiated forall remains.
        // Re-solve the authored quantifier-free conjuncts and fail closed unless
        // that ground core is independently UNSAT. Conjunctive foralls, genuine
        // ground-core UNSATs, and the separately checked CEGQI arms are untouched.
        if matches!(result, Ok(SolveResult::Unsat(_))) && !cegqi_has_forall && !cegqi_has_exists {
            if let Some(snapshot) = refinement_assertions {
                if self.snapshot_has_nonconjunctive_forall(snapshot)
                    && !self.ground_core_is_unsat(snapshot, category)
                {
                    // SOUND UNSAT RESCUE before the non-conjunctive-forall
                    // degrade, mirroring `@298`. This arm distrusts the verdict
                    // because the refutation MAY have been manufactured by
                    // conjoining instances of a forall that is not
                    // unconditionally asserted — such instances are not
                    // entailed, so promoting them would be a false UNSAT.
                    //
                    // `instance_closure_ground_unsat` is nevertheless safe here,
                    // and the reason is an invariant maintained at the WRITE
                    // side rather than the read side: every member of
                    // `active_support_axioms` is an instance of an
                    // UNCONDITIONALLY-asserted forall. All three writers
                    // (preprocess.rs:1860, preprocess.rs:2234, dispatch.rs:201)
                    // gate on `unconditional_forall_roots.contains(&inst)`, and
                    // `push_active_support_axiom` documents the contract. So the
                    // closure set contains only consequences of universal
                    // instantiation (`forall i. P(i)` entails `P(t)`), which
                    // hold in every model — precisely the instances this arm
                    // does NOT distrust. A refutation resting only on them is
                    // genuine no matter how the distrusted forall was
                    // positioned.
                    //
                    // Gated on the closure actually carrying instances (the
                    // helper bails unless it added support), and fail-closed:
                    // anything short of a definitive UNSAT falls through to the
                    // degrade below, byte-identical to before.
                    let snapshot_owned = snapshot.to_vec();
                    if self.instance_closure_ground_unsat(&snapshot_owned, category) {
                        if ay_core::misc_cli_flags().debug_cert {
                            eprintln!("CERT/rescue@277: instance-closure UNSAT");
                        }
                        return self.quantified_semantic_unsat_or_unknown(
                            UnknownReason::QuantifierUnhandled,
                        );
                    }
                    if ay_core::misc_cli_flags().debug_cert {
                        eprintln!("CERT/degrade@277");
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                    return Ok(SolveResult::Unknown);
                }
            }
        }
        // Soundness guard: a `forall` whose binder sort MBQI cannot synthesize
        // (Array, FP, Seq, RegLan) has no sound SAT path through E-matching
        // alone — E-matching produces only ground instances that already exist
        // in the problem, while the forall ranges over an infinite domain.
        // If the ground solver returned SAT and we did not establish UNSAT
        // through interleaved refinement, return Unknown. UNSAT propagates
        // unchanged because adding partial quantifier instances can only
        // strengthen the problem (ay #8729 / Z3 #6303).
        if has_unsafe_partial_quantifiers {
            if let Ok(SolveResult::Sat) | Ok(SolveResult::Unknown) = &result {
                if !unsat_from_interleaved {
                    // SOUND UNSAT RESCUE before the MBQI-unsafe fail-close
                    // (#instance-closure@298 / F6 part v generalization). The
                    // interleaved lane can surface `Sat`/`Unknown` on a window
                    // whose universal-INSTANTIATION consequence set — the ground
                    // snapshot conjuncts plus the E-matched instances of
                    // UNCONDITIONALLY-asserted foralls — is independently UNSAT.
                    // That refutation rests ONLY on instantiation consequences
                    // (`forall i.P(i)` entails `P(t)`), NEVER on the MBQI-unsafe
                    // infinite-domain / extensionality witness this guard
                    // protects, so it is exactly the sound half already trusted
                    // at the `instance_closure` Unknown-arm below — which the
                    // early `return` here otherwise skips. It is the fix for the
                    // mixed-fragment stall where an IDLE LIA atom (e.g. a seq
                    // `len` equation) coexisting with an array-`forall` refutation
                    // flips the ground verdict from `Unsat` to `Unknown` and
                    // spuriously degrades a genuinely-UNSAT query (probe M1/M1d;
                    // minimal repro: an UNSAT array-forall core + `(= len 1)`).
                    //
                    // SOUNDNESS: `instance_closure_ground_unsat` only EVER
                    // promotes UNSAT, and only when a set of universal-
                    // instantiation consequences is itself UNSAT — so it cannot
                    // be the ay#8729/Z3#6303 wrong-SAT (a SAT flip): the
                    // `(forall i. a[i]=b[i]) ∧ a≠b` extensionality case has NO
                    // clashing ground-instance pair (a and b differ only at a
                    // non-instantiated index), so its consequence set stays SAT
                    // and this rescue declines, degrading to Unknown as before.
                    // Gated on `ematching_added_instantiations` so the closure
                    // set genuinely carries instances; declines to the existing
                    // degrade otherwise.
                    if ematching_added_instantiations {
                        if let Some(snapshot) = refinement_assertions {
                            let snapshot = snapshot.to_vec();
                            if self.instance_closure_ground_unsat(&snapshot, category) {
                                if ay_core::misc_cli_flags().debug_cert {
                                    eprintln!("CERT/rescue@298: instance-closure UNSAT");
                                }
                                if cegqi_has_forall {
                                    if let Some(checked) = cegqi_unsat_authority::certify(
                                        self,
                                        refinement_assertions,
                                        category,
                                    ) {
                                        return Ok(checked.publish(self));
                                    }
                                    self.last_unknown_reason =
                                        Some(UnknownReason::QuantifierCegqiIncomplete);
                                    return self.cegqi_fail_closed_unknown();
                                }
                                return self.quantified_semantic_unsat_or_unknown(
                                    UnknownReason::QuantifierUnhandled,
                                );
                            }
                        }
                    }
                    if ay_core::misc_cli_flags().debug_cert {
                        eprintln!("CERT/degrade@298");
                    }
                    self.record_unsafe_partial_unknown(quantifiers_supported_by_uf_completion);
                    return Ok(SolveResult::Unknown);
                }
            }
            // CEGQI's Unsat->Sat disambiguation (the `cegqi_has_forall` /
            // `cegqi_mixed` arms below) is itself unsound for an MBQI-unsafe
            // forall: a ground UNSAT obtained under counterexample-instantiation
            // lemmas can be flipped to a spurious SAT because the missing
            // infinite-domain / extensionality witness was never instantiated
            // (AUFLIA `(forall i. a[i]=b[i]) ∧ a≠b`: the ground solver returns
            // UNSAT, but disambiguation reads that as "forall valid" and reports
            // SAT — ay #8729 / Z3 #6303). A genuinely sound UNSAT here arrives via
            // interleaved E-matching (`unsat_from_interleaved`, handled below and
            // left untouched); any other CEGQI-disambiguated UNSAT degrades to
            // Unknown rather than risk a wrong sat/unsat.
            if let Ok(SolveResult::Unsat(_)) = &result {
                if !unsat_from_interleaved && (cegqi_has_forall || cegqi_mixed) {
                    if let Some(published) = cegqi_unsat_authority::publish_installed(self) {
                        return Ok(published);
                    }
                    // SOUNDNESS-PRESERVING COMPLETENESS (#mbqi-completeness Q1):
                    // The blanket degrade above is conservative. Adding a `forall`'s
                    // E-matching INSTANCES is always sound (each instance is a logical
                    // consequence: forall i.P(i) entails P(0)), so a ground UNSAT that
                    // rests on those instances - NOT on CEGQI's (possibly unsound) CE
                    // lemmas - is a genuine UNSAT even for an MBQI-unsafe (array-
                    // indexing) binder. Reconstruct a THEORY-INDEPENDENT refutation
                    // directly from the pre-instantiation snapshot: if instantiating
                    // the conjunctive-position foralls at ground terms yields a literal
                    // and its complement (a pure propositional / equality clash, valid
                    // under every interpretation incl. arrays), the contradiction came
                    // purely from sound instantiation + ground core. Accept it. The
                    // array-extensionality wrong-SAT concern (AUFLIA
                    // (forall i. a[i]=b[i]) and a!=b) is unaffected: that arrives here
                    // as a *Sat* and is degraded by the `Sat` arm above; only an
                    // independently-reconstructed UNSAT survives this exception, and a
                    // satisfiable (forall i. a[i]=b[i]) and a[0]=b[0] has no clashing
                    // literal pair.
                    let clash = refinement_assertions
                        .map(|snap| {
                            !self.snapshot_has_nonconjunctive_forall(snap)
                                && self.unsat_from_direct_instance_clash(snap, category)
                        })
                        .unwrap_or(false);
                    if clash {
                        if let Some(checked) =
                            cegqi_unsat_authority::certify(self, refinement_assertions, category)
                        {
                            return Ok(checked.publish(self));
                        }
                    }
                    // (#registry-outside-clash) NOT nested under `clash` -- see
                    // `Justification::publish_if_established` for why that nesting made
                    // the registry unreachable from the widest degrade in this function.
                    if let Some(published) = justification::Justification::publish_if_established(
                        self,
                        refinement_assertions,
                        category,
                    ) {
                        return Ok(published);
                    }
                    // (#implied-forall-ground-inst) Every leg above CONSULTS
                    // for evidence; this one BUILDS it, then re-enters the
                    // sealed publication this arm already offers at its head.
                    // The #8729 / Z3 #6303 guard is untouched: the producer
                    // reads no CE lemma, no clash reconstruction and no
                    // enclosing verdict, and `publish_installed` re-validates
                    // scope, empty clause and the full strict check. Rationale
                    // in `authored_consequence_replay::implied_ground_inst`.
                    if self.try_translate_implied_forall_ground_instantiation_unsat() {
                        if let Some(published) = cegqi_unsat_authority::publish_installed(self) {
                            return Ok(published);
                        }
                    }
                    if clash {
                        self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                        return self.cegqi_fail_closed_unknown();
                    }
                    if ay_core::misc_cli_flags().debug_cert {
                        eprintln!("CERT/degrade@343");
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierUnhandled);
                    return Ok(SolveResult::Unknown);
                }
            }
        }

        // The broad UF-completion classifier is a useful way to find the
        // premise-pinned UFBV family, but it is not a SAT certificate. Run the
        // independent, consequence-only refuter it used to guard before any
        // result mapping can fail closed. This preserves definitive UNSATs
        // without letting the syntactic classifier grant SAT.
        if quantifiers_supported_by_uf_completion
            && matches!(result, Ok(SolveResult::Sat) | Ok(SolveResult::Unknown))
        {
            if let Some(snapshot) = refinement_assertions {
                let mut quantifiers = Vec::new();
                for &assertion in snapshot {
                    crate::ematching::collect_quantifiers(
                        &mut self.ctx.terms,
                        assertion,
                        &mut quantifiers,
                    );
                }
                let foralls: Vec<TermId> = quantifiers
                    .into_iter()
                    .filter(|&q| matches!(self.ctx.terms.get(q), TermData::Forall(..)))
                    .collect();
                if let Some(Ok(SolveResult::Unsat(_))) =
                    self.premise_forced_binder_refutation(&foralls, snapshot)
                {
                    if cegqi_has_forall {
                        if let Some(checked) =
                            cegqi_unsat_authority::certify(self, refinement_assertions, category)
                        {
                            return Ok(checked.publish(self));
                        }
                        self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                        return self.cegqi_fail_closed_unknown();
                    }
                    return self
                        .quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierUnhandled);
                }
            }
        }

        match result {
            Ok(SolveResult::Sat) | Ok(SolveResult::Unknown) if cegqi_mixed => {
                self.record_unknown_from_origin(UnknownOrigin::CegqiRefinement);
                Ok(SolveResult::Unknown)
            }
            Ok(SolveResult::Unsat(_)) if cegqi_mixed || cegqi_has_forall => {
                let disamb = self.disambiguate_cegqi_unsat(
                    category,
                    cegqi_ce_lemma_ids,
                    cegqi_ce_lemma_groups,
                    cegqi_mixed,
                    cegqi_state,
                    refinement_assertions,
                );
                // Every downstream interpretation of `disamb` assumes the
                // extracted universals are asserted obligations. For a
                // non-conjunctive `forall`, that assumption can manufacture a
                // wrong result in either direction: a local validity proof can
                // flip to SAT, a conjoined CE instance can yield UNSAT, and an
                // Unknown fed to the MBQI cross-check can conjoin still more
                // non-entailed instances. Stop all three before they diverge.
                // The sole exception is an independently UNSAT quantifier-free
                // ground core, which is a certificate for the original formula
                // regardless of quantifier position. A missing snapshot cannot
                // establish position and therefore also fails closed.
                let Some(snapshot) = refinement_assertions else {
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    return Ok(SolveResult::Unknown);
                };
                if self.snapshot_has_nonconjunctive_forall(snapshot) {
                    // The sealed consequence verifier inside disambiguation is
                    // the only UNSAT authority here. Re-solving G0 in place
                    // would bypass its proof-mode refusal and could attach the
                    // CE-primary or an inner untranslated proof to the verdict.
                    if matches!(&disamb, Ok(SolveResult::Unsat(_))) {
                        return disamb;
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    return Ok(SolveResult::Unknown);
                }
                // SOUNDNESS (#forall-alternation wrong-sat): a CEGQI "forall valid
                // ⟹ SAT" verdict is unreliable when the snapshot has a
                // skolemized-alternation forall with a witness-independent
                // arithmetic conjunct (a bound-var constraint no existential
                // witness can repair). Fail closed there. The genuine
                // witness-driven cases (e.g. `(forall x (exists y (> y x)))`,
                // skolemized to `(forall x (> sk(x) x))`) have no such conjunct
                // and keep their SAT.
                if matches!(disamb, Ok(SolveResult::Sat)) {
                    if let Some(snapshot) = refinement_assertions {
                        // DECISION (#forall-alternation): the CEGQI "forall valid"
                        // verdict bypasses model validation. Validate it directly
                        // with model-based quantifier instantiation against the
                        // candidate (ground-only) model: instantiate each snapshot
                        // `forall` at ground/synthesized candidates, evaluate under
                        // the model, and re-solve the falsifying instances. If that
                        // drives the problem UNSAT the universal is genuinely
                        // violated — decide UNSAT (matching z3) rather than trust
                        // the unvalidated certificate. This resolves the
                        // alternation wrong-sats where infeasibility comes from the
                        // COMBINATION of (skolem-)constrained conjuncts, which no
                        // syntactic guard can see.
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return self.cegqi_inner_unsat_or_unknown();
                        }
                        // Safety net: fail closed on the unreliable
                        // skolem-alternation shape MBQI could not refute.
                        if self.snapshot_has_witness_independent_skolem_alternation(snapshot) {
                            self.last_unknown_reason =
                                Some(UnknownReason::QuantifierCegqiIncomplete);
                            return Ok(SolveResult::Unknown);
                        }
                    }
                }
                // DECISION (#quantified-ce-lemma, second S3 route): when
                // disambiguation stays honestly Unknown (ground remainder Sat
                // but the CE obligation neither refuted nor decided), try the
                // model-based instantiation refutation before surfacing the
                // Unknown — mirror of the refinement-Unknown branch below. It
                // only ever returns UNSAT on a real instantiation contradiction
                // (a sound universal instance driven UNSAT, now including the
                // per-candidate ISOLATED single-instance solves that decide the
                // NIA-conjunction chokepoint), so this can only upgrade a
                // fail-closed Unknown to the decisive answer, never flip a
                // genuine verdict.
                if matches!(disamb, Ok(SolveResult::Unknown)) {
                    if let Some(snapshot) = refinement_assertions {
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return self.cegqi_inner_unsat_or_unknown();
                        }
                    }
                }
                // MBQI and alternation safety nets run after the sealed SAT
                // authority was consumed. Recheck the two publication
                // postconditions after that downstream work as well.
                if matches!(disamb, Ok(SolveResult::Sat))
                    && (self.should_abort_theory_loop()
                        || (self.last_model.is_none()
                            && !self.has_current_pending_certificate_model_transport(
                                &self.ctx.assertions,
                            )))
                {
                    return self.cegqi_fail_closed_unknown();
                }
                disamb
            }
            Ok(SolveResult::Sat) if cegqi_has_forall => {
                // CEGQI asserts counterexample instances conjunctively. That
                // is sound only for a universal that is itself entailed in a
                // conjunctive position. Refining a `forall` under `or`, `xor`,
                // or an implication antecedent can manufacture either polarity:
                // a conflicting instance yields a wrong UNSAT, while stripping
                // the containing assertion can make the remainder spuriously
                // SAT. Position classification requires the original snapshot;
                // without it, fail closed as well.
                let cegqi_context_is_conjunctive = refinement_assertions
                    .is_some_and(|snapshot| !self.snapshot_has_nonconjunctive_forall(snapshot));
                if !cegqi_context_is_conjunctive {
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    return Ok(SolveResult::Unknown);
                }
                let refinement_result = self.try_cegqi_arith_refinement(
                    cegqi_state,
                    category,
                    cegqi_ce_lemma_ids,
                    cegqi_ce_lemma_groups,
                    refinement_assertions,
                );
                if let Some(result) = refinement_result {
                    // DECISION (#forall-alternation): the skolemized inner
                    // existentials of a `forall (exists ...)` leave a pure `forall`
                    // that reaches HERE (cegqi_has_forall, no surviving exists). When
                    // CEGQI refinement is honestly Unknown it has not validated the
                    // certificate; validate with the MBQI / FM projection /
                    // over-approximation pipeline and, if a snapshot `forall`
                    // instantiation / witness projection drives the problem UNSAT,
                    // decide UNSAT (matching z3). The validation only ever returns
                    // UNSAT on a real contradiction, so this only ever upgrades a
                    // fail-closed Unknown to the decisive answer. A genuine SAT
                    // ("forall valid") verdict is LEFT UNTOUCHED — re-validating it
                    // would re-enter the solver and corrupt the SAT model state — so
                    // its model-population path is byte-identical to before.
                    if matches!(result, Ok(SolveResult::Unknown)) {
                        if let Some(snapshot) = refinement_assertions {
                            // A raw-SAT CE window can represent a universal
                            // satisfied by one exact UF completion without
                            // being globally valid. Reuse the same sealed
                            // per-model theorem as the raw-UNSAT
                            // disambiguation path before asking the strictly
                            // stronger global-validity checker.
                            if let Some(checked) = self.try_cegqi_model_group_sat(
                                snapshot,
                                cegqi_ce_lemma_groups,
                                cegqi_state,
                                category,
                            ) {
                                return checked;
                            }
                            if let Some(Ok(SolveResult::Unsat(_))) =
                                self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                            {
                                return self.cegqi_inner_unsat_or_unknown();
                            }
                            // SAT leg (#quantified-ce-lemma): the refinement is
                            // honestly Unknown and MBQI could not refute. This is
                            // the ONLY reachable hook for the valid skolemized
                            // alternation (`forall x (exists y (> y x))`), whose
                            // refinement rounds stay Sat and never reach
                            // disambiguation: rebuild each universal's
                            // DE-SKOLEMIZED counterexample obligation
                            // `L_q = forall ys. ¬psi0(ys, e)` and refute it by a
                            // bounded, isolated ground instantiation. Every L_q
                            // refuted ⟹ every universal is VALID ⟹ with the
                            // full-set Sat already established on entry to this
                            // arm, the problem is SAT (see
                            // `try_quantified_ce_valid_flip` for the certificate
                            // and its gates).
                            if let Some(flip) =
                                self.try_quantified_ce_valid_flip(cegqi_state, snapshot, category)
                            {
                                return flip;
                            }
                        }
                    }
                    result
                } else {
                    // No refinement verdict: still try to refute the (unvalidated)
                    // SAT certificate before failing closed — a real instantiation
                    // contradiction makes this the decisive UNSAT.
                    if let Some(snapshot) = refinement_assertions {
                        if let Some(checked) = self.try_cegqi_model_group_sat(
                            snapshot,
                            cegqi_ce_lemma_groups,
                            cegqi_state,
                            category,
                        ) {
                            return checked;
                        }
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return self.cegqi_inner_unsat_or_unknown();
                        }
                        // SAT leg (#quantified-ce-lemma): same hook as the
                        // refinement-Unknown branch above, for problems where
                        // refinement was not applicable at all (no model / no
                        // arithmetic CE variables).
                        if let Some(flip) =
                            self.try_quantified_ce_valid_flip(cegqi_state, snapshot, category)
                        {
                            return flip;
                        }
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    Ok(SolveResult::Unknown)
                }
            }
            Ok(SolveResult::Sat) if cegqi_has_exists => {
                // SOUNDNESS (RED S3, 2026-07-08): for a PURE existential the ground
                // Sat IS the witness (the skolem constants), so the passthrough is
                // sound. But when the snapshot ALSO carries a `forall` — the ∀∃
                // alternation, e.g. `(forall x (exists y (= (* y y) x)))`, which is
                // FALSE (x = 2 has no square root) — the ground Sat only reflects
                // the finitely-INSTANTIATED fragment of the universal (0 and 1 ARE
                // perfect squares), and "incomplete instantiation defaulted to sat".
                // Try to refute via model-based instantiation first (a real
                // instantiation contradiction is the decisive UNSAT, matching z3);
                // otherwise fail closed to Unknown. Pure-∃ snapshots keep the
                // passthrough byte-identically.
                let snapshot_has_forall = refinement_assertions.as_ref().is_some_and(|snap| {
                    snap.iter().any(|&a| {
                        let mut stack = vec![a];
                        while let Some(t) = stack.pop() {
                            match self.ctx.terms.get(t) {
                                TermData::Forall(..) => return true,
                                TermData::App(_, args) => stack.extend(args.iter().copied()),
                                TermData::Not(i) => stack.push(*i),
                                TermData::Ite(c, th, el) => {
                                    stack.push(*c);
                                    stack.push(*th);
                                    stack.push(*el);
                                }
                                TermData::Exists(_, b, _) => stack.push(*b),
                                _ => {}
                            }
                        }
                        false
                    })
                });
                if snapshot_has_forall {
                    if let Some(snapshot) = refinement_assertions {
                        if let Some(Ok(SolveResult::Unsat(_))) =
                            self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, true)
                        {
                            return self.cegqi_inner_unsat_or_unknown();
                        }
                    }
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    Ok(SolveResult::Sat)
                }
            }
            Ok(SolveResult::Unsat(_)) if cegqi_has_exists => {
                self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                Ok(SolveResult::Unknown)
            }
            Ok(SolveResult::Sat)
                if (has_uninstantiated_quantifiers && !ematching_added_instantiations)
                    || reached_instantiation_limit
                    || has_deferred
                    || has_completely_unhandled_quantifiers =>
            {
                if !unhandled_quantifiers.is_empty() {
                    // SOUNDNESS (#quant-alternation wrong-unsat): `try_mbqi_refinement`
                    // discharges an unhandled `forall` by adding a falsifying ground
                    // instance and re-solving — if that drives the problem to UNSAT it
                    // concludes the universal is violated. That is only sound when the
                    // `forall` is a top-level CONJUNCT of the (post-Skolemization)
                    // problem: a conjunct that is false makes the whole problem false.
                    // A `forall` sitting in a DISJUNCTIVE position (e.g. produced by
                    // finite-domain expansion of an outer `exists` — `(exists x. forall
                    // y. (= x 0))` expands to `(or (forall y. (= 0 0)) (forall y. (= 1
                    // 0)) ...)`) is NOT a conjunct: a false disjunct does not refute the
                    // formula (a sibling `(forall y. (= 0 0))` disjunct is true, so the
                    // whole `exists` is SAT). Feeding such a disjunct to MBQI and reading
                    // its instance-driven UNSAT as a verdict is the alternation
                    // wrong-UNSAT bug. Restrict MBQI to conjunctive-position foralls; if
                    // any unhandled forall is only in a non-conjunctive position, the
                    // ground SAT cannot be soundly refuted here — fail closed to Unknown.
                    // A `forall` marked "E-matching only" (`mark_no_mbqi`, e.g. the
                    // Hilbert-`choose` witness axiom) is treated like a
                    // non-conjunctive-position forall: EXCLUDED from MBQI, and its
                    // presence forces a fail-closed `Unknown` when MBQI does not
                    // otherwise refute — so it is discharged ONLY by E-matching on a
                    // ground trigger (an established witness), matching Verus. Sound
                    // (conservative): can only lose proofs, never a wrong-UNSAT.
                    let conjunctive = refinement_assertions
                        .map(|snap| self.forall_ids_in_conjunctive_position(snap));
                    let (mbqi_quants, has_nonconjunctive): (Vec<TermId>, bool) =
                        if let Some(conj_set) = &conjunctive {
                            let mbqi: Vec<TermId> = unhandled_quantifiers
                                .iter()
                                .copied()
                                .filter(|q| conj_set.contains(q) && !self.ctx.terms.is_no_mbqi(*q))
                                .collect();
                            let has_nonconj = unhandled_quantifiers
                                .iter()
                                .any(|q| !conj_set.contains(q) || self.ctx.terms.is_no_mbqi(*q));
                            (mbqi, has_nonconj)
                        } else {
                            // No snapshot to classify positions: keep the prior
                            // behaviour (all unhandled foralls eligible) EXCEPT still
                            // honor the no-MBQI marker. This path is only reached when
                            // refinement_assertions is None, which does not occur for
                            // quantified problems.
                            let mbqi: Vec<TermId> = unhandled_quantifiers
                                .iter()
                                .copied()
                                .filter(|q| !self.ctx.terms.is_no_mbqi(*q))
                                .collect();
                            let has_nonconj = unhandled_quantifiers
                                .iter()
                                .any(|q| self.ctx.terms.is_no_mbqi(*q));
                            (mbqi, has_nonconj)
                        };

                    let mbqi_result = if mbqi_quants.is_empty() {
                        None
                    } else {
                        self.try_mbqi_refinement(
                            &mbqi_quants,
                            category,
                            refinement_assertions.unwrap_or(&[]),
                        )
                    };

                    match mbqi_result {
                        // UNSAT from a conjunctive-position forall is sound.
                        // Before the fail-closed publisher, translate it into
                        // an authored-scope strict proof seeded with the
                        // refinement's own instance provenance — the sibling
                        // consumer already does this, and without it a
                        // refutation whose instances the model chose has no
                        // route to authority and is downgraded
                        // (#bv-mbqi-refutation-authority).
                        Some(Ok(SolveResult::Unsat(_))) => {
                            if self.translate_refinement_seeded_replay() {
                                self.last_unknown_reason = None;
                                Ok(SolveResult::unsat())
                            } else {
                                self.quantified_semantic_unsat_or_unknown(
                                    UnknownReason::QuantifierUnhandled,
                                )
                            }
                        }
                        // A SAT/Unknown from MBQI, or no eligible conjunctive foralls,
                        // combined with a still-undischarged non-conjunctive forall,
                        // means the ground SAT is not verified: fail closed.
                        other => {
                            if let Some(result) = other {
                                if !has_nonconjunctive {
                                    // FAIL-CLOSED (P0 patterned-forall wrong-sat): MBQI's
                                    // "no counterexample found" is NOT a totality proof —
                                    // it rests only on the finitely-many ground candidates
                                    // it probed. For a `forall` that E-matching left
                                    // uninstantiated (this arm), emitting that as a final
                                    // SAT is exactly the shifted-trigger (`f(x+1)`)
                                    // wrong-sat this P0 closes: the ground candidate set
                                    // need not contain the falsifying witness (`f(3) = -5`
                                    // is falsified at x=2, not a ground term). Only an
                                    // MBQI *refutation* (Unsat, handled above) is decisive
                                    // here; a non-refuting outcome degrades to a sound
                                    // Unknown. (Genuine SATs certified by the finite-table
                                    // / UF-completion / quantifier_consumer certificate paths are
                                    // decided upstream and never reach here.)
                                    match result {
                                        Ok(SolveResult::Sat) => {
                                            // SOUND EPR / finite-uninterpreted-domain
                                            // SAT certification
                                            // (#special-relations-mbqi-sat). MBQI's
                                            // "no counterexample found" is not by
                                            // itself a totality proof (the P0
                                            // shifted-trigger concern above). But when
                                            // every binder ranges over an uninterpreted
                                            // sort whose universe is generated SOLELY by
                                            // ground constants, the MBQI fixpoint model
                                            // (`try_mbqi_refinement` pinned the predicate
                                            // at every ground point) is a COMPLETE, exact
                                            // witness: the validator re-checks every
                                            // cross-product instance to a definite
                                            // `Bool(true)` over the fully-enumerated
                                            // finite universe. It NEVER grants a wrong
                                            // sat — the shifted-trigger / arithmetic
                                            // shapes are excluded by the
                                            // uninterpreted-sort + no-generating-function
                                            // gates, so this only recovers the
                                            // special-relations (order-axiom) SAT family
                                            // that would otherwise fail closed.
                                            // FULL-DOMAIN BV CERTIFICATE.
                                            // The fail-closed rationale above is
                                            // that MBQI's "no counterexample
                                            // found" rests on the finitely-many
                                            // candidates it probed. When
                                            // `bv_quantifier_full_domain_proof` is set
                                            // that rationale does not apply:
                                            // every BV forall was discharged by
                                            // symbolic entailment or an
                                            // authenticated exhaustive expansion.
                                            // Both cover the binder's WHOLE domain,
                                            // with no incomplete candidate sample.
                                            // `G |= forall x. body` for each,
                                            // and `G` is Sat, so the conjunction
                                            // is Sat.
                                            if ay_core::misc_cli_flags().debug_cert {
                                                ay_core::safe_eprintln!(
                                                    "FMQ publish: proof={} pending={} gate_roots={:?} refine={:?}",
                                                    self.bv_quantifier_full_domain_proof,
                                                    self.bv_quantifier_full_domain_pending_evidence
                                                        .is_some(),
                                                    self.independent_gate_query_roots(),
                                                    refinement_assertions
                                                );
                                            }
                                            if self.bv_quantifier_full_domain_proof {
                                                // The finite-model lane installs its
                                                // staged output witness and a
                                                // model-bound grant atomically before
                                                // returning Sat. Accept that exact-
                                                // current grant directly. Generic BV
                                                // producers retain the legacy pending-
                                                // evidence path below.
                                                let gate_roots =
                                                    self.independent_gate_query_roots();
                                                let installed_current = self
                                                    .bv_quantifier_full_domain_query_grant
                                                    .as_ref()
                                                    .is_some_and(|grant| {
                                                        grant.is_current_for(self, &gate_roots)
                                                    });
                                                if installed_current {
                                                    self.defer_model_validation = false;
                                                    self.last_model_validated = true;
                                                    self.last_unknown_reason = None;
                                                    return Ok(SolveResult::Sat);
                                                }
                                                if let Some(evidence) = self
                                                    .bv_quantifier_full_domain_pending_evidence
                                                    .take()
                                                {
                                                    let installed = self
                                                        .install_bv_full_domain_sat_authority(
                                                            evidence,
                                                        );
                                                    if ay_core::misc_cli_flags().debug_cert {
                                                        ay_core::safe_eprintln!(
                                                            "FMQ publish: installed={installed}"
                                                        );
                                                    }
                                                    if installed {
                                                        self.defer_model_validation = false;
                                                        self.last_model_validated = true;
                                                        self.last_unknown_reason = None;
                                                        return Ok(SolveResult::Sat);
                                                    }
                                                }
                                                self.revoke_bv_full_domain_sat_authority();
                                            }
                                            let epr_snapshot = refinement_assertions
                                                .map(<[TermId]>::to_vec)
                                                .unwrap_or_else(|| mbqi_quants.clone());
                                            let epr_quants: Vec<TermId> = epr_snapshot
                                                .iter()
                                                .copied()
                                                .filter(|&a| {
                                                    matches!(
                                                        self.ctx.terms.get(a),
                                                        TermData::Forall(..)
                                                    )
                                                })
                                                .collect();
                                            if let Some(evidence) = self
                                                .mbqi_sat_validated_finite_uninterpreted_domain(
                                                    &epr_snapshot,
                                                    &epr_quants,
                                                )
                                            {
                                                if self.install_mbqi_sat_authority(evidence) {
                                                    self.defer_model_validation = false;
                                                    self.last_model_validated = true;
                                                    self.last_unknown_reason = None;
                                                    Ok(SolveResult::Sat)
                                                } else {
                                                    self.last_model_validated = false;
                                                    self.last_unknown_reason =
                                                        Some(UnknownReason::QuantifierUnhandled);
                                                    Ok(SolveResult::Unknown)
                                                }
                                            } else if let Some(decided) = refinement_assertions
                                                .and_then(|snap| {
                                                    let snap = snap.to_vec();
                                                    // (#p2-mbqi-empty-universe) EPR
                                                    // over an EMPTY universe:
                                                    // singleton-witness decide (both
                                                    // directions; heavily guarded,
                                                    // fail-closed — see the mbqi.rs
                                                    // doc for the review guards).
                                                    self.mbqi_empty_universe_singleton_decide(
                                                        &snap,
                                                        &epr_quants,
                                                        category,
                                                    )
                                                })
                                            {
                                                if matches!(decided, SolveResult::Unsat(_)) {
                                                    self.empty_universe_semantic_unsat_or_unknown()
                                                } else {
                                                    Ok(decided)
                                                }
                                            } else {
                                                self.last_unknown_reason =
                                                    Some(UnknownReason::QuantifierUnhandled);
                                                Ok(SolveResult::Unknown)
                                            }
                                        }
                                        _ => result,
                                    }
                                } else {
                                    if ay_core::misc_cli_flags().debug_cert {
                                        eprintln!("CERT/degrade@802");
                                    }
                                    // #inc-fp-no-complete-lane: a finite-sort
                                    // (FP) quantifier in a DISJUNCTIVE position
                                    // lands here — MBQI is correctly refused it,
                                    // since an instance of it is not a
                                    // consequence. The finite-sort lane does not
                                    // instantiate: it fixes the quantifier's
                                    // truth value under the pins with checked
                                    // UNSAT solves and substitutes a constant,
                                    // which is position-independent.
                                    if self.try_finite_model_sat_certificate() {
                                        self.defer_model_validation = false;
                                        self.last_model_validated = true;
                                        self.last_unknown_reason = None;
                                        return Ok(SolveResult::Sat);
                                    }
                                    self.last_unknown_reason =
                                        Some(UnknownReason::QuantifierUnhandled);
                                    Ok(SolveResult::Unknown)
                                }
                            } else {
                                // (#p2-mbqi-empty-universe) No MBQI verdict at
                                // all (no eligible candidates — e.g. an empty
                                // ground universe): try the singleton-witness
                                // decide before failing closed.
                                if !has_nonconjunctive {
                                    if let Some(snap) = refinement_assertions {
                                        let snap = snap.to_vec();
                                        let epr_quants: Vec<TermId> = snap
                                            .iter()
                                            .copied()
                                            .filter(|&a| {
                                                matches!(
                                                    self.ctx.terms.get(a),
                                                    TermData::Forall(..)
                                                )
                                            })
                                            .collect();
                                        if let Some(decided) = self
                                            .mbqi_empty_universe_singleton_decide(
                                                &snap,
                                                &epr_quants,
                                                category,
                                            )
                                        {
                                            return if matches!(decided, SolveResult::Unsat(_)) {
                                                self.empty_universe_semantic_unsat_or_unknown()
                                            } else {
                                                Ok(decided)
                                            };
                                        }
                                    }
                                }
                                // #inc-fp-no-complete-lane: same rescue as the
                                // sibling arm above. MBQI produced no verdict —
                                // typically because every unhandled forall sits
                                // in a non-conjunctive position, so none was
                                // eligible — but a finite-sort quantifier can
                                // still be discharged by constant substitution.
                                if self.try_finite_model_sat_certificate() {
                                    self.defer_model_validation = false;
                                    self.last_model_validated = true;
                                    self.last_unknown_reason = None;
                                    return Ok(SolveResult::Sat);
                                }
                                let reason = if reached_instantiation_limit {
                                    UnknownReason::QuantifierRoundLimit
                                } else {
                                    UnknownReason::QuantifierUnhandled
                                };
                                self.record_unknown_from_origin(reason.origin());
                                Ok(SolveResult::Unknown)
                            }
                        }
                    }
                } else {
                    // A patterned top-level forall can be classified as
                    // E-matching-managed even when its trigger has no ground
                    // occurrence. In that case `unhandled_quantifiers` is
                    // empty, but the ground SAT is still not authority for the
                    // quantified formula. Give the exact empty-universe
                    // singleton theorem the same opportunity it receives in
                    // the explicitly-unhandled lane. Its guards require the
                    // complete snapshot, top-level conjunctive foralls,
                    // quantifier-free bodies, ordinary MBQI eligibility, and
                    // exact singleton carriers; decline remains Unknown.
                    if let Some(snapshot) = refinement_assertions {
                        let snapshot = snapshot.to_vec();
                        let singleton_quants: Vec<TermId> = snapshot
                            .iter()
                            .copied()
                            .filter(|&root| {
                                matches!(self.ctx.terms.get(root), TermData::Forall(..))
                            })
                            .collect();
                        if let Some(decided) = self.mbqi_empty_universe_singleton_decide(
                            &snapshot,
                            &singleton_quants,
                            category,
                        ) {
                            return if matches!(decided, SolveResult::Unsat(_)) {
                                self.empty_universe_semantic_unsat_or_unknown()
                            } else {
                                Ok(decided)
                            };
                        }
                    }
                    let reason = if reached_instantiation_limit {
                        UnknownReason::QuantifierRoundLimit
                    } else if has_deferred {
                        UnknownReason::QuantifierDeferred
                    } else {
                        UnknownReason::QuantifierUnhandled
                    };
                    self.record_unknown_from_origin(reason.origin());
                    Ok(SolveResult::Unknown)
                }
            }
            Ok(SolveResult::Unsat(_)) if ematching_has_exists && !cegqi_has_exists => {
                if let Some(Ok(SolveResult::Unsat(_))) =
                    self.disambiguate_ematching_exists_unsat(refinement_assertions, category)
                {
                    // The independent ground-core re-solve establishes the
                    // verdict, but its proof is not translated back into the
                    // authored quantified assertion window.  Route it through
                    // the same artifact firewall as every other semantic-only
                    // quantified refutation: best-effort mode may publish a
                    // verdict-only UNSAT, while mandatory proof modes fail
                    // closed to Unknown.
                    self.quantified_semantic_unsat_or_unknown(
                        UnknownReason::QuantifierEmatchingExistsIncomplete,
                    )
                } else {
                    self.record_unknown_from_origin(UnknownOrigin::ExistentialEmatching);
                    Ok(SolveResult::Unknown)
                }
            }
            // (#p2-ufnia-refutation) A ground `Unknown` about to be surfaced,
            // with E-matched instances present: the in-place lane may have
            // failed on a window a FRESH solve of the same consequence set
            // decides (UFNIA `f(0)=0 ∧ ∀x. f(x)²≥1`). Re-solve the
            // quantifier-free snapshot conjuncts plus the provenance-filtered
            // support-axiom instances in isolation; a definitive UNSAT of that
            // consequence set is a sound UNSAT of the problem. Anything else
            // keeps the existing Unknown (reason preserved). CEGQI engagement
            // does not gate this: the closure set is built ONLY from snapshot
            // QF conjuncts + `active_support_axioms` (instances of
            // unconditionally-asserted foralls), so CE lemmas are structurally
            // excluded whatever CEGQI did. (Mixed forall/exists Unknowns are
            // already returned by the `cegqi_mixed` arm above.)
            Ok(SolveResult::Unknown) if ematching_added_instantiations => {
                if ay_core::misc_cli_flags().debug_cert {
                    eprintln!("CERT/instance-closure: unknown-arm reached");
                }
                if let Some(snapshot) = refinement_assertions {
                    let snapshot = snapshot.to_vec();
                    if self.instance_closure_ground_unsat(&snapshot, category) {
                        if cegqi_has_forall {
                            if let Some(checked) = cegqi_unsat_authority::certify(
                                self,
                                refinement_assertions,
                                category,
                            ) {
                                return Ok(checked.publish(self));
                            }
                            self.last_unknown_reason =
                                Some(UnknownReason::QuantifierCegqiIncomplete);
                            return self.cegqi_fail_closed_unknown();
                        }
                        return self.quantified_semantic_unsat_or_unknown(
                            UnknownReason::QuantifierUnhandled,
                        );
                    }
                }
                // A raw `Unknown` from the CE-augmented ground window is not
                // itself SAT evidence.  It can nevertheless be the search
                // outcome for a valid skolemized alternation after nonlinear
                // arithmetic made that temporary window undecidable.  Give the
                // existing sealed SAT theorem one opportunity to decide the
                // SOURCE obligation before surfacing the Unknown:
                //
                //  * `install` independently solves the exact snapshot ground
                //    remainder and freezes its ordered roots, public-query
                //    epoch, frontend source/scope stamp, and installed model;
                //  * `certify_quantified_ce_refutations` requires exact
                //    coverage of every snapshot quantifier and individually
                //    refutes each de-Skolemized counterexample obligation;
                //  * `publish` rechecks epoch/source/model currentness and only
                //    then returns provisional SAT; assertion restoration and
                //    the mandatory public quantified-model gate still recheck
                //    the authored roots and mint the final model-bound handoff.
                //
                // Thus the raw Unknown is only a ROUTING trigger.  A missing
                // snapshot, uncovered quantifier, satisfiable/unknown theorem
                // query, stale epoch/scope, absent ground model, or stop all
                // retain the existing fail-closed Unknown.  Keep the
                // consequence-set UNSAT check above first: a real refutation
                // must never be obscured by a later completeness probe.
                if cegqi_has_forall {
                    if let Some(snapshot) = refinement_assertions {
                        if let Some(checked_sat) =
                            self.try_quantified_ce_valid_flip(cegqi_state, snapshot, category)
                        {
                            return checked_sat;
                        }
                    }
                }
                // The primary ground lane can report generic `Incomplete` on
                // the temporary CE-augmented window even though the remaining
                // uncertainty is precisely whether the original universal has
                // a total completion. Preserve that quantifier classification
                // for syntactically supported UF-completion candidates so the
                // sealed finite/default-table certificate below is allowed to
                // inspect the authored snapshot. This is not SAT authority:
                // the broad classifier cannot grant, and the independently
                // checked certificate must still construct and re-verify M'.
                if cegqi_has_forall && quantifiers_supported_by_uf_completion {
                    self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
                }
                Ok(SolveResult::Unknown)
            }
            other => other,
        }
    }

    /// Collect the quantifier TermIds (as `collect_quantifiers` would surface
    /// them, including NNF `Not(Exists)`/`Not(Forall)` conversion) that occur in
    /// a top-level CONJUNCTIVE position of `snapshot`.
    ///
    /// A quantifier in conjunctive position is a top-level conjunct of the
    /// problem: if it is universally false, the whole problem is false, so MBQI
    /// may soundly drive it to UNSAT. Quantifiers reachable only through
    /// disjunctions, `ite` branches, or function arguments are NOT conjuncts and
    /// must not be refuted to UNSAT (the alternation wrong-UNSAT family, e.g. the
    /// disjunction of inner foralls produced by finite-domain expanding an outer
    /// `exists`).
    ///
    /// The descent follows only conjunctive contexts: each assertion is a
    /// conjunct; `(and ...)` propagates conjunctive position to its arguments;
    /// `Not(Not(x))` propagates (double negation); `Not(or ...)` De-Morgans to a
    /// conjunction of negations and propagates; and `Not(=> p q)` ≡ `p ∧ ¬q`
    /// propagates. This mirrors the conjunctive cases of
    /// `ArithInstantiator::process_assertion` and `collect_quantifiers`.
    /// A top-level assertion counts as a unit FACT only when it is a plain
    /// atom — no Boolean structure and no quantifier — so unit-simplifying with
    /// it cannot smuggle in an obligation.
    ///
    /// NOTE ON THE RETURNED IDs (load-bearing for callers that intersect this
    /// set with RAW authored nodes): for a negated quantifier this returns the
    /// NNF-CONVERTED id, never the raw one. A top-level `(not (forall x. b))`
    /// contributes a freshly built `Exists(x, not b)`, so the raw `Forall`
    /// node is ABSENT from the set — which is exactly right, since that
    /// `Forall` is not a consequence of the problem and its instances must
    /// never be asserted.
    #[allow(clippy::wrong_self_convention)]
    pub(in crate::executor) fn forall_ids_in_conjunctive_position(
        &mut self,
        snapshot: &[TermId],
    ) -> ay_core::kani_compat::DetHashSet<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        use ay_core::Symbol;
        let mut out: HashSet<TermId> = HashSet::default();

        // #unit-conjunctive: a top-level UNIT literal is a FACT, so the
        // conjunctive-position test must be taken modulo those facts, not just
        // read off the syntax tree.
        //
        // `(=> ext_eq_0 (forall i . B i))` with `(assert ext_eq_0)` also present
        // puts that `forall` in a *disjunctive* syntactic position — the walk
        // below stops at `=>` — even though `ext_eq_0` is asserted true, which
        // makes the `forall` an outright top-level consequence and its instances
        // sound ground facts. The purely syntactic reading made
        // `snapshot_has_nonconjunctive_forall` fire, and the #classA guard then
        // discarded the genuine UNSAT the engine had already derived (#7956).
        //
        // Unit-simplifying first is sound (a unit assertion is unconditionally
        // true) and strictly more accurate — it only ever RECOGNISES foralls that
        // really are consequences; it never admits one that isn't.
        let mut units: ay_core::kani_compat::DetHashMap<TermId, bool> =
            ay_core::kani_compat::DetHashMap::default();
        for &a in snapshot {
            match self.ctx.terms.get(a) {
                TermData::Not(inner) => {
                    let inner = *inner;
                    if is_unit_atom(&self.ctx.terms, inner) {
                        units.insert(inner, false);
                    }
                }
                _ => {
                    if is_unit_atom(&self.ctx.terms, a) {
                        units.insert(a, true);
                    }
                }
            }
        }

        // `positive` tracks polarity: true = the term appears positively in a
        // conjunctive context, false = it appears negated (so an inner `and`
        // becomes a disjunction and stops conjunctive descent).
        let mut stack: Vec<(TermId, bool)> = snapshot.iter().map(|&a| (a, true)).collect();
        let mut visited: HashSet<(TermId, bool)> = HashSet::default();
        while let Some((term, positive)) = stack.pop() {
            if !visited.insert((term, positive)) {
                continue;
            }
            match self.ctx.terms.get(term).clone() {
                TermData::Forall(..) | TermData::Exists(..) if positive => {
                    // A bare quantifier in positive conjunctive position. Use
                    // collect_quantifiers to surface the exact TermId(s)
                    // (identity for forall/exists in this position).
                    let mut q = Vec::new();
                    crate::ematching::collect_quantifiers(&mut self.ctx.terms, term, &mut q);
                    out.extend(q);
                }
                TermData::Not(inner) => {
                    let inner_data = self.ctx.terms.get(inner).clone();
                    match inner_data {
                        // NNF: a negated quantifier in positive conjunctive
                        // position becomes the dual quantifier (a conjunct).
                        // Reproduce the exact TermId collect_quantifiers builds.
                        TermData::Exists(vars, body, triggers) if positive => {
                            let neg_body = self.ctx.terms.mk_not(body);
                            let converted = self
                                .ctx
                                .terms
                                .mk_forall_with_triggers(vars, neg_body, triggers);
                            out.insert(converted);
                        }
                        TermData::Forall(vars, body, triggers) if positive => {
                            let neg_body = self.ctx.terms.mk_not(body);
                            let converted = self
                                .ctx
                                .terms
                                .mk_exists_with_triggers(vars, neg_body, triggers);
                            out.insert(converted);
                        }
                        // Double negation: keep polarity, descend.
                        TermData::Not(inner2) => stack.push((inner2, positive)),
                        // Not(or A B) ≡ (and ¬A ¬B): conjunctive when positive.
                        // Not(and A B) ≡ (or ¬A ¬B): disjunctive — stop descent.
                        _ => stack.push((inner, !positive)),
                    }
                }
                TermData::App(Symbol::Named(name), args) => {
                    // `(and ...)` in positive position and `(or ...)` under a
                    // negation (De Morgan -> conjunction) both keep a conjunctive
                    // context for their arguments. Everything else (positive
                    // `or`, function applications, `=>`, `ite`) breaks conjunctive
                    // descent — quantifiers below are not top-level conjuncts...
                    if (name == "and" && positive) || (name == "or" && !positive) {
                        for &arg in &args {
                            stack.push((arg, positive));
                        }
                    } else if name == "=>" && positive && args.len() == 2 {
                        // ...EXCEPT modulo top-level unit facts (#unit-conjunctive).
                        // `(=> a b)`: if `a` is a unit fact, `b` is a top-level
                        // consequence, so descend conjunctively. If `b` is already
                        // true (or `a` already false), the implication is satisfied
                        // and constrains nothing — it cannot put any forall of its
                        // own into a disjunctive obligation, so descend into
                        // neither side.
                        let (a, b) = (args[0], args[1]);
                        let a_unit = unit_value(&self.ctx.terms, &units, a);
                        let b_unit = unit_value(&self.ctx.terms, &units, b);
                        if b_unit == Some(true) || a_unit == Some(false) {
                            // satisfied by a unit fact — contributes nothing
                        } else if a_unit == Some(true) {
                            stack.push((b, positive));
                        }
                    } else if name == "or" && positive {
                        // Unit propagation through a positive `or`: if every
                        // disjunct but one is falsified by a unit fact, the
                        // survivor is a top-level consequence.
                        if !args
                            .iter()
                            .any(|&x| unit_value(&self.ctx.terms, &units, x) == Some(true))
                        {
                            let live: Vec<TermId> = args
                                .iter()
                                .copied()
                                .filter(|&x| unit_value(&self.ctx.terms, &units, x) != Some(false))
                                .collect();
                            if live.len() == 1 {
                                stack.push((live[0], positive));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// Return `true` if `snapshot` contains a `forall` (as `collect_quantifiers`
    /// would surface it, including NNF `Not(Exists)`/`Not(Forall)` conversion)
    /// that is NOT in a top-level conjunctive position.
    ///
    /// Such a `forall` is a disjunctive obligation; instances of it added
    /// conjunctively to the assertion set can manufacture a spurious UNSAT.
    pub(super) fn snapshot_has_nonconjunctive_forall_probe(&mut self, snapshot: &[TermId]) -> bool {
        self.snapshot_has_nonconjunctive_forall(snapshot)
    }

    fn snapshot_has_nonconjunctive_forall(&mut self, snapshot: &[TermId]) -> bool {
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);
        let mut all_quants: Vec<TermId> = Vec::new();
        for &a in snapshot {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, a, &mut all_quants);
        }
        all_quants
            .into_iter()
            .filter(|&q| matches!(self.ctx.terms.get(q), TermData::Forall(..)))
            .any(|q| !conjunctive.contains(&q))
    }

    /// Reconstruct the quantifier-free conjunctive consequences of the
    /// pre-instantiation assertion snapshot.
    ///
    /// This is the canonical ground remainder used by every CEGQI attribution
    /// check.  It is deliberately reconstructed from the authored snapshot,
    /// never filtered out of the live solver assertion set: preprocessing under
    /// a counterexample lemma may delete an authored conjunct or leave behind a
    /// CE-derived, CE-variable-free residue, so the live set is not provenance.
    fn snapshot_ground_core(&self, snapshot: &[TermId]) -> Vec<TermId> {
        let mut ground = Vec::new();
        for &assertion in snapshot {
            if contains_quantifier(&self.ctx.terms, assertion) {
                let mut conjuncts = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
                for conjunct in conjuncts {
                    if !contains_quantifier(&self.ctx.terms, conjunct)
                        && !ground.contains(&conjunct)
                    {
                        ground.push(conjunct);
                    }
                }
            } else if !ground.contains(&assertion) {
                ground.push(assertion);
            }
        }
        ground
    }

    /// Re-solve ONLY the quantifier-free conjuncts extracted from `snapshot`
    /// (the pre-instantiation view) and return `true` if they are UNSAT on their
    /// own. This is the genuine ground core: if it is UNSAT, a reported UNSAT did
    /// not depend on (possibly disjunctive) quantifier instances and is sound.
    pub(super) fn ground_core_is_unsat(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> bool {
        let ground = self.snapshot_ground_core(snapshot);
        if ground.is_empty() {
            // No quantifier-free core: the contradiction can only have come from
            // quantifier instances, so the ground core is NOT independently UNSAT.
            return false;
        }

        match self.checked_ground_solve(ground.clone(), fallback_category, 2_000) {
            Some(CheckedGroundDecision::Unsat(checked)) => checked.consume(self, &ground),
            _ => false,
        }
    }

    /// (#p2-ufnia-refutation) Instance-closure FRESH re-solve: re-solve the
    /// quantifier-free conjuncts of `snapshot` TOGETHER WITH the terms of
    /// `self.active_support_axioms` (the E-matched instances of
    /// UNCONDITIONALLY-asserted top-level foralls) as a standalone ground
    /// problem, and return `true` iff that consequence set is definitively
    /// UNSAT on its own.
    ///
    /// WHY A FRESH RE-SOLVE: the in-place ground lane can return `Unknown` on
    /// an instance-augmented window that a fresh solve of the identical window
    /// decides (measured on the UFNIA shape `f(0)=0 ∧ ∀x. f(x)² ≥ 1`, whose
    /// e-matched instance at `x:=0` closes immediately standalone). The
    /// codebase already treats the in-place incremental state as unsafe for
    /// verdict-grade re-solves (`ground_core_is_unsat` deliberately `take()`s
    /// `incr_theory_state`); this mirrors that pattern with ONE extension —
    /// the support-axiom instances are included.
    ///
    /// SOUNDNESS: every re-solved formula is either (a) a quantifier-free
    /// top-level conjunct of the pre-instantiation snapshot, or (b) a member
    /// of `active_support_axioms`, whose provenance contract
    /// (`push_active_support_axiom`, preprocess.rs) guarantees it is a ground
    /// instance of an UNCONDITIONALLY-asserted `forall` — i.e. a universal-
    /// instantiation consequence. CE lemmas are excluded by construction
    /// (they are never pushed into the support set). UNSAT of a consequence
    /// set implies UNSAT of the original problem. The closure set is
    /// additionally FILTERED TO QUANTIFIER-FREE members: an instance of a
    /// forall with a nested-forall body is itself quantified, and feeding it
    /// to the fresh re-solve could re-enter the quantifier pipeline
    /// (reentrancy guard; dropping such a member only weakens the re-solved
    /// set, which is always sound).
    ///
    /// Only ever used to upgrade an `Unknown` to `Unsat`; it never produces a
    /// `Sat` and never overrides a decided verdict.
    pub(super) fn instance_closure_ground_unsat(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> bool {
        if self.external_stop_reason().is_some() {
            return false;
        }
        let mut ground = self.snapshot_ground_core(snapshot);
        // Extend with the quantifier-free support-axiom instances. Without at
        // least one, this would duplicate `ground_core_is_unsat` — bail out.
        let support_terms: Vec<TermId> = self
            .active_support_axioms
            .iter()
            .map(|l| l.term)
            .filter(|&inst| !contains_quantifier(&self.ctx.terms, inst))
            .collect();
        let mut added_support = false;
        for inst in support_terms {
            if !ground.contains(&inst) {
                ground.push(inst);
                added_support = true;
            }
        }
        if ay_core::misc_cli_flags().debug_cert {
            eprintln!(
                "CERT/instance-closure: ground={} support_added={added_support}",
                ground.len()
            );
        }
        if !added_support || ground.is_empty() {
            return false;
        }

        // One conjunction through `checked_ground_solve`: it runs
        // the SAME Nelson-Oppen `purify_int_uf_arith` pass the top-level
        // check-sat pipeline runs (without it, `(* (f 0) (f 0))` stays an
        // opaque nonlinear product the NIA core cannot relate to `f(0)=0`,
        // and the fresh window misses the UNSAT a parsed standalone problem
        // decides in milliseconds), plus the full nested-solve state
        // discipline. Fail-closed: anything short of a definitive Unsat is
        // `false`.
        let formula = self.ctx.terms.mk_and(ground);
        let obligation = vec![formula];
        let decided = match self.checked_ground_solve(obligation.clone(), fallback_category, 2_000)
        {
            Some(CheckedGroundDecision::Unsat(checked)) => checked.consume(self, &obligation),
            _ => false,
        };
        if decided && ay_core::misc_cli_flags().debug_cert {
            eprintln!("CERT/instance-closure: UNSAT via fresh consequence-set re-solve");
        }
        decided
    }

    /// SOUND closed-universal-validity precheck (#quant-ws closed-forall wrong-SAT).
    ///
    /// A top-level conjunct assertion that is a `Forall(vars, body)` with a
    /// CLOSED, quantifier-free `body` (every free symbol of `body` is one of
    /// `vars`; no free constant / UF / array / outer-bound var — see
    /// `closed_quantifier_free_forall_parts`) is model-INDEPENDENT: it is either
    /// VALID (its negation is unsat — nothing to do) or unconditionally FALSE
    /// (its negation is sat — `(check-sat)` is then UNSAT *regardless* of every
    /// other assertion, because a false top-level conjunct makes the whole
    /// conjunction false).
    ///
    /// For each such conjunct we skolemize the body (substitute each bound var
    /// with a fresh free constant of the same sort) and solve `(not body)` as a
    /// GROUND problem. If that ground negation is DEFINITIVELY SAT, the universal
    /// is provably false and we return `Some(unsat())`. Anything else (negation
    /// unsat ⇒ universal valid; negation unknown ⇒ undecided) leaves the
    /// universal untouched and we fall through.
    ///
    /// SOUNDNESS: this can ONLY return UNSAT, and ONLY when a conjunct is
    /// PROVABLY false (its skolemized negation is definitively SAT). It therefore
    /// cannot over-degrade a genuine SAT (it never returns SAT/Unknown), cannot
    /// flip a genuine UNSAT, and — because it excludes any forall with an inner
    /// existential (the body would contain a quantifier ⇒ rejected) or any free
    /// symbol (rejected) — never touches `∀x∃y. P` alternations or
    /// array-extensionality `∀i. A0[i]=A1[i]` universals. The full solver state
    /// it perturbs (assertions, incremental theory state, model/validation
    /// bookkeeping) is saved and restored on every path.
    ///
    /// Returns `None` when no closed false universal is found (the normal
    /// quantifier pipeline runs unchanged).
    pub(in crate::executor) fn closed_universal_validity_precheck(
        &mut self,
        fallback_category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        // Re-entrancy guard: the ground negation solve below runs the full
        // check-sat dispatch, which must not recurse back into this precheck.
        if self.in_closed_universal_precheck {
            return None;
        }

        // Identify top-level conjunct foralls with a closed, quantifier-free body.
        // Only top-level conjuncts qualify: a forall reachable only through a
        // disjunction / ite / function argument is NOT a conjunct, so its falsity
        // does not refute the problem. We descend solely through `(and ...)`.
        let mut candidates: Vec<TermId> = Vec::new();
        let assertions = self.ctx.assertions.clone();
        for &assertion in &assertions {
            let mut conjuncts = vec![assertion];
            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
            for c in conjuncts {
                if (super::closed_quantifier_free_forall_parts(&self.ctx.terms, c).is_some()
                    || super::closed_quantifier_free_forall_literal_parts(&self.ctx.terms, c)
                        .is_some())
                    && !candidates.contains(&c)
                {
                    candidates.push(c);
                }
            }
        }
        if candidates.is_empty() {
            return None;
        }

        self.in_closed_universal_precheck = true;
        let result = self.closed_universal_validity_precheck_inner(&candidates, fallback_category);
        self.in_closed_universal_precheck = false;
        match result {
            Some(ClosedUniversalRefutation::TranslatedProof) => Some(Ok(SolveResult::unsat())),
            Some(ClosedUniversalRefutation::CheckedLiteral(evidence)) => {
                Some(Ok(self.emit_checked_exact_closed_forall_unsat(evidence)))
            }
            Some(ClosedUniversalRefutation::UntranslatedSkolemModel) => {
                Some(self.quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierUnhandled))
            }
            None => None,
        }
    }

    fn closed_universal_validity_precheck_inner(
        &mut self,
        candidates: &[TermId],
        fallback_category: LogicCategory,
    ) -> Option<ClosedUniversalRefutation> {
        use crate::ematching::subst_vars;

        for &forall_id in candidates {
            // Prefer an exact literal witness before asking the ground solver
            // for a model of a skolemized arithmetic term.  Some interpreted
            // partial operators (notably symbolic-divisor integer `rem`) are
            // deliberately fail-closed in the general ground model lane.  Once
            // every Int binder is replaced by a numeral, however, the body is a
            // closed ground proposition and the evaluator/ground solver can
            // check the actual theory semantics directly.  A single definitely
            // false instance refutes the top-level universal.
            if let Some((vars, body)) =
                super::closed_quantifier_free_forall_literal_parts(&self.ctx.terms, forall_id)
            {
                if let Some(refutation) = self.closed_universal_false_at_literal_witness(
                    &vars,
                    body,
                    forall_id,
                    fallback_category,
                ) {
                    return Some(refutation);
                }
            }

            // The skolemized-negation lane has the stronger requirement that
            // *all* operations be model-independent.  In particular, a
            // literal witness may safely use `rem 2 3`, while this lane must
            // still reject a symbolic divisor that could be zero.
            let Some((vars, body)) =
                super::closed_quantifier_free_forall_parts(&self.ctx.terms, forall_id)
            else {
                continue;
            };

            // Skolemize: map each bound var to a fresh free constant of its sort.
            let mut subst: HashMap<String, TermId> = HashMap::default();
            for (name, sort) in &vars {
                let fresh = self
                    .ctx
                    .terms
                    .mk_fresh_var(&format!("cu!{name}"), sort.clone());
                subst.insert(name.clone(), fresh);
            }
            let skolem_body = subst_vars(&mut self.ctx.terms, body, &subst);
            let neg = self.ctx.terms.mk_not(skolem_body);

            // The skolemized negation may refute the universal only through the
            // sealed ground checker. Its SAT payload proves that the disposable
            // query traversed the canonical SAT-emission/model-validation funnel,
            // and consumption binds that result to this exact outer query and
            // ordered singleton root.
            let neg_assertions = vec![neg];
            if self
                .checked_ground_solve(neg_assertions.clone(), fallback_category, 2_000)
                .is_some_and(|decision| match decision {
                    CheckedGroundDecision::Sat(checked) => checked.consume(self, &neg_assertions),
                    CheckedGroundDecision::Unsat(_) => false,
                })
            {
                return Some(ClosedUniversalRefutation::UntranslatedSkolemModel);
            }
        }
        None
    }

    /// Recover UNSAT when the quantifier-free slice is already contradictory.
    ///
    /// E-matching an existential is incomplete for proving UNSAT because it
    /// adds witness instances conjunctively. However, if the ground assertions
    /// from the pre-E-matching snapshot are UNSAT on their own, the existential
    /// instances did not cause the contradiction and the original formula is
    /// definitively UNSAT.
    fn disambiguate_ematching_exists_unsat(
        &mut self,
        refinement_assertions: Option<&[TermId]>,
        fallback_category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let refinement_assertions = refinement_assertions?;
        let mut ground = Vec::new();
        for &assertion in refinement_assertions {
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
            if conjuncts.is_empty() {
                conjuncts.push(assertion);
            }
            for conjunct in conjuncts {
                if !contains_quantifier(&self.ctx.terms, conjunct) && !ground.contains(&conjunct) {
                    ground.push(conjunct);
                }
            }
        }
        if ground.is_empty() {
            return None;
        }

        self.checked_ground_solve(ground.clone(), fallback_category, 2_000)
            .is_some_and(|decision| match decision {
                CheckedGroundDecision::Unsat(checked) => checked.consume(self, &ground),
                CheckedGroundDecision::Sat(_) => false,
            })
            .then(|| Ok(SolveResult::unsat()))
    }

    /// Restore original assertions after quantifier solving (#2844).
    ///
    /// When `defer_model_validation` is set, validates the model against the
    /// restored original assertions. Model validation violations (Violated)
    /// are caught and degraded to Unknown rather than propagated as hard
    /// errors, because the model was produced by solving preprocessed
    /// assertions (e.g., with mod_div_elim) and may not satisfy the original
    /// un-preprocessed assertions due to theory incompleteness. (#7979)
    fn restore_assertions(
        &mut self,
        original_assertions: Option<Vec<TermId>>,
        final_result: &mut Result<SolveResult>,
        category: LogicCategory,
        has_uninstantiated_quantifiers: bool,
        full_ematching_coverage: bool,
        finite_table_sat_certificate: bool,
    ) {
        if self.defer_model_validation {
            self.defer_model_validation = false;
            let pre_restore_assertions = self.ctx.assertions.clone();
            self.ctx.assertions = original_assertions
                .expect("BUG: defer_model_validation set but original_assertions is None");
            if matches!(final_result, Ok(SolveResult::Sat)) {
                match self.finalize_sat_model_validation() {
                    Ok(result) => {
                        // (#7979) Model validation deliberately skips quantified
                        // assertions: a true SAT proxy covers only the emitted
                        // instances, not the full binder domain. A returned Sat
                        // therefore still needs the exhaustive/model-building
                        // checks below whenever a quantifier was skipped.
                        //
                        // (#8729) When a quantifier assertion was skipped,
                        // theory-delegated evidence (`delegated_checks`) does
                        // NOT count as sufficient evidence. Delegation trusts a
                        // downstream theory solver (BV/array/EUF) to have
                        // validated the model, but those theory solvers never
                        // see quantifier constraints — the quantifier was only
                        // handled at the E-matching/SAT level, and its
                        // instances were removed when original_assertions were
                        // restored. Example: Z3 #6303 byte-concat reproducer
                        // (forall a[concat(...)]=b[concat(...)] + ground
                        // disequality select a #x0 != select b #x0). The
                        // quantifier is skipped; the ground disequality hits
                        // observation.rs Unknown+TERM_FLAG_ARRAY and returns
                        // delegated() because bv_model.is_some(). Prior guard
                        // saw checked > 0 (from delegation) and trusted SAT,
                        // yielding an unsound sat answer. We require
                        // *independent* evidence (checked - delegated_checks)
                        // or sat_fallback_count when a quantifier was skipped.
                        // If such evidence exists, we still run an MBQI
                        // quick-check on the restored quantifiers before
                        // trusting the SAT result.
                        if matches!(result, SolveResult::Sat) {
                            let stats = self.last_validation_stats.as_ref();
                            let has_skipped_quantifiers =
                                stats.is_some_and(|s| s.skipped_quantifier > 0);
                            let has_any_evidence = stats.is_some_and(|s| {
                                let independent = s.checked.saturating_sub(s.delegated_checks);
                                independent > 0 || s.sat_fallback_count > 0
                            });
                            if has_skipped_quantifiers {
                                // NOTE(#8969): no syntactic "restored total UF
                                // completion" authority belongs in these
                                // disjunctions. A shape-only pointwise arm
                                // reproduced the popcount wrong-SAT, and exact
                                // triggers still do not prove that every
                                // instance survived cost/model filtering.
                                let mbqi_gate = self.mbqi_soundness_gate_for_skipped_quantifiers();

                                let mbqi_gate_confirms = matches!(
                                    mbqi_gate,
                                    SkippedQuantifierMbqiGate::ExhaustivelySatisfied
                                );

                                // A typed whole-window certificate has already
                                // discharged the skipped quantified leaves. The
                                // strict pass above checked the ground siblings;
                                // compose those two evidence sources only while
                                // the certificate remains exact-current for the
                                // restored roots. A `deep_qe` rewrite is only a
                                // finite-checked candidate and deliberately does
                                // not appear here as publication authority.
                                let exact_current_authority = self
                                    .current_quantified_sat_authority(&self.ctx.assertions)
                                    .is_some();
                                if mbqi_gate_confirms || exact_current_authority {
                                    *final_result = Ok(result);
                                } else {
                                    if !has_any_evidence {
                                        // SOUND COMPLETENESS (#mbqi-completeness Q2):
                                        // even with no independent ground evidence, an
                                        // EPR / finite-uninterpreted-domain problem whose
                                        // fixpoint model satisfies every cross-product
                                        // instance is a complete, sound SAT witness.
                                        if self
                                            .try_mbqi_sat_certification(
                                                &pre_restore_assertions,
                                                category,
                                                has_uninstantiated_quantifiers,
                                                full_ematching_coverage,
                                            )
                                            .is_some()
                                        {
                                            *final_result = Ok(SolveResult::Sat);
                                            return;
                                        }
                                        // (#skolem-witness-sat) Legacy witness before the new refuter. A
                                        // restored positive `exists` whose
                                        // recorded witness instance evaluates
                                        // TRUE under the emitted model — with the
                                        // independent gate's own evaluator,
                                        // through the polarity-sound witnessed
                                        // rewrite of EVERY public query root — is
                                        // checked evidence for this exact Sat.
                                        // Keep it; the unchanged emission gates
                                        // still adjudicate the publication.
                                        if self.try_skolem_witness_sat_confirmation() {
                                            *final_result = Ok(result);
                                            return;
                                        }
                                        if self.adopt_skipped_quantifier_refinement(
                                            &pre_restore_assertions,
                                            category,
                                            final_result,
                                        ) {
                                            return;
                                        }
                                        self.last_unknown_reason = Some(
                                            UnknownReason::QuantifierEmatchingExistsIncomplete,
                                        );
                                        self.last_result = Some(SolveResult::Unknown);
                                        *final_result = Ok(SolveResult::Unknown);
                                    } else {
                                        // Retain the existing refutation-first order.
                                        if self.adopt_skipped_quantifier_refinement(
                                            &pre_restore_assertions,
                                            category,
                                            final_result,
                                        ) {
                                            return;
                                        }
                                        // (#skolem-witness-sat) Same arm as the
                                        // no-evidence branch. Placed AFTER the
                                        // MBQI refinement so every pre-existing
                                        // refutation path is untouched; the arm
                                        // only decides what previously fell
                                        // through to the fail-closed demote.
                                        if self.try_skolem_witness_sat_confirmation() {
                                            *final_result = Ok(result);
                                            return;
                                        }
                                        // SOUND COMPLETENESS (#mbqi-completeness Q2):
                                        // the refinement found no counterexample. If the
                                        // problem is in the EPR / finite-uninterpreted-
                                        // domain fragment, the fixpoint model is a
                                        // complete, sound witness - certify SAT instead
                                        // of failing closed. NEVER returns a wrong SAT
                                        // (the validator requires every cross-product
                                        // instance to evaluate to a definite Bool true
                                        // over a fully-enumerated finite universe).
                                        if self
                                            .try_mbqi_sat_certification(
                                                &pre_restore_assertions,
                                                category,
                                                has_uninstantiated_quantifiers,
                                                full_ematching_coverage,
                                            )
                                            .is_some()
                                        {
                                            *final_result = Ok(SolveResult::Sat);
                                            return;
                                        }
                                        self.last_unknown_reason = Some(
                                            UnknownReason::QuantifierEmatchingExistsIncomplete,
                                        );
                                        self.last_result = Some(SolveResult::Unknown);
                                        *final_result = Ok(SolveResult::Unknown);
                                    }
                                }
                            } else {
                                *final_result = Ok(result);
                            }
                        } else {
                            *final_result = Ok(result);
                        }
                    }
                    Err(_) => {
                        // (#p2-ufnia-refutation) Before degrading, try the
                        // instance-closure fresh re-solve: the QF conjuncts of
                        // the restored original assertions plus the
                        // provenance-filtered support-axiom instances form a
                        // consequence set; a definitive standalone UNSAT of it
                        // is a sound UNSAT of the problem (the failed model
                        // validation is evidence the in-place lane's window
                        // handling broke, not that the problem is undecided).
                        let restored_snapshot = self.ctx.assertions.clone();
                        if self.instance_closure_ground_unsat(&restored_snapshot, category) {
                            let published = self.quantified_semantic_unsat_or_unknown(
                                UnknownReason::QuantifierUnhandled,
                            );
                            if let Ok(result) = &published {
                                self.last_result = Some(result.clone());
                            }
                            *final_result = published;
                            return;
                        }
                        // Model validation violation against restored assertions
                        // means the solver produced a model (via preprocessed
                        // constraints like mod_div_elim) that doesn't satisfy the
                        // original assertions. This is a theory solver
                        // incompleteness (e.g., mod/div reasoning), not a soundness
                        // bug. Degrade to Unknown. (#7979)
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        self.last_result = Some(SolveResult::Unknown);
                        *final_result = Ok(SolveResult::Unknown);
                    }
                }
            }
        } else if let Some(original_assertions) = original_assertions {
            let pre_restore_assertions = self.ctx.assertions.clone();
            self.ctx.assertions = original_assertions;

            // A few quantified SAT certificates intentionally clear deferred
            // validation before reaching this restoration branch.  That does
            // not make a sampled interpretation of a bound-dependent declared
            // UF total: require the same explicit completion/exhaustiveness
            // authorities as the deferred branch.  Pure arithmetic CEGQI and
            // Skolem-witness certificates do not need this extra UF-totality
            // premise and remain untouched.
            if matches!(final_result, Ok(SolveResult::Sat))
                && self.restored_has_bound_dependent_non_skolem_application()
            {
                let restored_roots = self.ctx.assertions.clone();
                let public_roots = self.independent_gate_query_roots();
                let current_exact_authority = self
                    .current_quantified_sat_authority(&restored_roots)
                    .is_some()
                    || self
                        .current_quantified_sat_authority(&public_roots)
                        .is_some();
                // CEGQI can classify the ground remainder Sat before phase
                // 2.5 gets a chance to run the finite-table certificate. In
                // that case re-check the restored snapshot here. The
                // certificate's own bare-argument scan still rejects shifted
                // applications such as `f(x + 1)`.
                // Any current typed grant for the restored or canonical public
                // vector is already an all-assertion theorem here. The exact
                // finite-expansion route validated both vectors when an earlier
                // equivalence rewrite made them differ. Short-circuit before
                // another producer can replace the completed model and stale
                // that model-bound grant.
                let finite_table_sat_certificate = finite_table_sat_certificate
                    || (!current_exact_authority && {
                        let restored_snapshot = self.ctx.assertions.clone();
                        self.try_finite_table_sat_certificate(&restored_snapshot, category)
                            .is_some()
                    });
                // Same story for the CONSTANT-INTERPRETATION certificate: on the
                // CEGQI-classified-`Sat` route neither phase-2.5c nor phase-3.5c
                // can fire (both require `final_result == Unknown`), so the
                // restored snapshot is re-checked here. Run against
                // `self.ctx.assertions` — the RESTORED originals — which is
                // exactly the all-`forall` shape the certificate's partition
                // requires; the pre-restore snapshot carries ground
                // instantiation consequences that make it decline.
                //
                // Short-circuited on the finite/default-table result
                // deliberately: if either certificate already granted, its own
                // marker below satisfies the emission funnel and a second
                // (equally authoritative) certificate would only cost nested
                // solves.
                let const_interp_sat_certificate =
                    !current_exact_authority && !finite_table_sat_certificate && {
                        let restored_snapshot = self.ctx.assertions.clone();
                        self.try_const_interp_sat_certificate(&restored_snapshot, category)
                            .is_some()
                    };
                // Record the finite/default-table certificate's authority for
                // the public emission funnel. See
                // `Executor::finite_table_cert_grant_active`: on this route the
                // phase-2.5 / phase-3.5 grant arms never fire (they require
                // `final_result == Unknown`, and CEGQI has already classified the
                // ground remainder `Sat`), so without this the funnel re-checks
                // universals the certificate has already verified and fails
                // closed. Gated on the finite/default-table certificate ALONE,
                // not on the whole `explicit_certificate` disjunction, because
                // that is the authority whose contract — re-verify every
                // snapshot assertion under an explicitly constructed
                // interpretation — is what the gate's marker precondition
                // requires.
                if finite_table_sat_certificate {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.finite_table_cert_grant_active = true;
                }
                // The PARALLEL grant record for the constant-interpretation
                // certificate. Adding a certificate to `explicit_certificate`
                // WITHOUT this block reproduces exactly the defect
                // `finite_table_cert_grant_active` was created to fix:
                // `explicit_certificate` only suppresses the downgrade, and the
                // certified `Sat` is then published as `unknown` by the emission
                // funnel. Gated on this certificate ALONE, for the same reason
                // the sibling above is — it is an authority whose contract is
                // "re-verify every snapshot assertion under an explicitly
                // constructed interpretation", which is the marker's stated
                // precondition.
                if const_interp_sat_certificate {
                    self.defer_model_validation = false;
                    self.last_model_validated = true;
                    self.const_interp_cert_grant_active = true;
                }

                // Consume only paired, exact-current authority. In particular,
                // the local certificate Booleans above merely select which
                // package to expose; they cannot suppress the downgrade unless
                // that package now authenticates this exact restored root
                // window. The direct MBQI gate remains a fresh check over the
                // live roots and is not represented by a durable routing bit.
                let explicit_certificate = self
                    .current_quantified_sat_authority(&restored_roots)
                    .is_some();
                let mbqi_gate_confirms = explicit_certificate
                    || matches!(
                        self.mbqi_soundness_gate_for_skipped_quantifiers(),
                        SkippedQuantifierMbqiGate::ExhaustivelySatisfied
                    );

                if !mbqi_gate_confirms {
                    // Preserve the independently exhaustive EPR/finite-domain
                    // authority used by the deferred branch.
                    if self
                        .try_mbqi_sat_certification(
                            &pre_restore_assertions,
                            category,
                            has_uninstantiated_quantifiers,
                            full_ematching_coverage,
                        )
                        .is_some()
                    {
                        return;
                    }
                    // (#skolem-witness-sat) LAST, exactly as in the deferred
                    // branch: the arm only decides what previously fell
                    // through to this fail-closed demote. A confirm keeps the
                    // ground solve's `Sat`; the unchanged emission gates
                    // still adjudicate the publication.
                    if self.try_skolem_witness_sat_confirmation() {
                        return;
                    }
                    self.last_unknown_reason =
                        Some(UnknownReason::QuantifierEmatchingExistsIncomplete);
                    self.last_result = Some(SolveResult::Unknown);
                    *final_result = Ok(SolveResult::Unknown);
                }
            }
        }
    }

    /// Try to turn a restored skipped-quantifier model counterexample into a
    /// ground refinement before failing closed to Unknown.
    ///
    /// `restore_assertions` validates SAT against the original quantified
    /// assertions. If validation skips a `forall`, MBQI may find a concrete
    /// falsifying instance in the candidate model. In that case, re-solving the
    /// pre-restore ground assertion set plus the MBQI instance can prove UNSAT
    /// instead of returning Unknown. The original assertion set is restored on
    /// every path so incremental callers keep seeing the same formulas. A
    /// definitive UNSAT, its terminal missing-artifact downgrade, or an error
    /// is adopted. Only `None` restores the predecessor model/capabilities and
    /// permits the caller to continue through existing SAT-side gates.
    fn try_skipped_quantifier_mbqi_refinement(
        &mut self,
        pre_restore_assertions: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let original_assertions = self.ctx.assertions.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_validation_stats = self.last_validation_stats.clone();
        let saved_unknown_reason = self.last_unknown_reason;
        let forall_quants: Vec<TermId> = original_assertions
            .iter()
            .copied()
            .filter(|&a| matches!(self.ctx.terms.get(a), TermData::Forall(..)))
            .collect();

        if forall_quants.is_empty() {
            return None;
        }

        // Preserve the exact affine predecessor, including its non-cloning
        // model seals. The nested refinement may freely replace or mutate only
        // an authority-free semantic clone. On a non-decision we move the
        // original object and its parked grants back together; cloning the
        // saved object here used to restore grants against a seal-less model.
        let saved_model = self.last_model.take();
        self.last_model = saved_model.clone();
        let saved_dt_cert_grant = std::mem::replace(&mut self.dt_cert_grant_active, false);
        let saved_dt_cert_query_grant = self.dt_cert_query_grant.take();
        let saved_finite_table_cert_grant =
            std::mem::replace(&mut self.finite_table_cert_grant_active, false);
        let saved_finite_table_witness = self.finite_table_cert_witness_state.take();
        let saved_const_interp_cert_grant =
            std::mem::replace(&mut self.const_interp_cert_grant_active, false);
        let saved_const_interp_witness = self.const_interp_cert_witness_state.take();
        let saved_cegqi_uf_recompletion_grant = self.cegqi_uf_recompletion_grant.take();
        let saved_mbqi_sat_cert_grant =
            std::mem::replace(&mut self.mbqi_sat_cert_grant_active, false);
        let saved_mbqi_sat_cert_query_grant = self.mbqi_sat_cert_query_grant.take();
        let saved_bv_full_domain_proof =
            std::mem::replace(&mut self.bv_quantifier_full_domain_proof, false);
        let saved_bv_full_domain_pending_evidence =
            self.bv_quantifier_full_domain_pending_evidence.take();
        let saved_bv_full_domain_query_grant = self.bv_quantifier_full_domain_query_grant.take();
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        self.ctx.assertions = pre_restore_assertions.to_vec();
        let refinement_result =
            self.try_mbqi_refinement(&forall_quants, category, &original_assertions);
        self.ctx.assertions = original_assertions;
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;

        match refinement_result {
            Some(Ok(SolveResult::Unsat(_))) => {
                // The probe made a public semantic decision. Discard both its
                // disposable authority and the predecessor's parked grants;
                // neither may be paired with the accepted replacement state.
                self.clear_quantified_sat_authority();
                // (#mbqi-instance-provenance) Before the fail-closed
                // publisher: translate the refinement's refutation into an
                // authored-scope strict proof via the consequence replay,
                // seeded with the exact MBQI instance provenance recorded at
                // the refinement push site. Each record is re-derived here as
                // the exact structural substitution (`exact_forall_instance`),
                // and the strict `forall_inst` validator re-replays it on the
                // stitched candidate — the records carry no authority, and a
                // failed translation falls through to the unchanged firewall.
                // Covered by `--no-consequence-replay` (recording and
                // translation both disabled), restoring the baseline
                // downgrade byte-for-byte.
                let records = std::mem::take(&mut self.mbqi_refinement_instance_records);
                let mut exact_records = Vec::with_capacity(records.len());
                for record in records {
                    if let Some(instance) =
                        self.exact_forall_instance(record.quantifier, &record.binding)
                    {
                        exact_records.push(crate::ematching::ForallInstantiationProvenance {
                            quantifier: record.quantifier,
                            binding: record.binding,
                            instance,
                        });
                    }
                }
                if !exact_records.is_empty()
                    && self.try_translate_authored_consequence_replay_unsat_with(&exact_records)
                {
                    self.last_unknown_reason = None;
                    return Some(Ok(SolveResult::unsat()));
                }
                Some(self.quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierUnhandled))
            }
            Some(Err(err)) => {
                self.clear_quantified_sat_authority();
                Some(Err(err))
            }
            _ => {
                // Restore the exact model first, then every executor-side
                // capability that names it. No observation can see a restored
                // grant paired with the disposable clone.
                self.last_model = saved_model;
                self.dt_cert_grant_active = saved_dt_cert_grant;
                self.dt_cert_query_grant = saved_dt_cert_query_grant;
                self.finite_table_cert_grant_active = saved_finite_table_cert_grant;
                self.finite_table_cert_witness_state = saved_finite_table_witness;
                self.const_interp_cert_grant_active = saved_const_interp_cert_grant;
                self.const_interp_cert_witness_state = saved_const_interp_witness;
                self.cegqi_uf_recompletion_grant = saved_cegqi_uf_recompletion_grant;
                self.mbqi_sat_cert_grant_active = saved_mbqi_sat_cert_grant;
                self.mbqi_sat_cert_query_grant = saved_mbqi_sat_cert_query_grant;
                self.bv_quantifier_full_domain_proof = saved_bv_full_domain_proof;
                self.bv_quantifier_full_domain_pending_evidence =
                    saved_bv_full_domain_pending_evidence;
                self.bv_quantifier_full_domain_query_grant = saved_bv_full_domain_query_grant;
                self.last_model_validated = saved_model_validated;
                self.last_validation_stats = saved_validation_stats;
                self.last_unknown_reason = saved_unknown_reason;
                None
            }
        }
    }

    /// SOUND MBQI SAT certification for EPR / finite-uninterpreted-domain
    /// problems (#mbqi-completeness Q2).
    ///
    /// `restore_assertions` fails closed to `Unknown` when a skipped `forall`
    /// could not be re-validated, even though the MBQI refinement found NO
    /// counterexample (the model satisfies every instance). For the EPR /
    /// finite-model-finding fragment - every binder over an uninterpreted sort
    /// whose universe is generated only by ground constants - that fixpoint model
    /// is a COMPLETE, sound witness: there are finitely many domain elements and
    /// every cross-product instance evaluates true. This certifies SAT.
    ///
    /// Drives the MBQI refinement over `pre_restore_assertions` to a fixpoint
    /// (forcing model-dependent facts like the symmetric pair (r b a) implied by
    /// a (r a b) => (r b a) instance), then runs the exact finite-domain
    /// validator on the resulting model. Returns `Some(())` only on a complete,
    /// definite-Bool certification; everything else restores state and returns
    /// `None` (caller keeps its fail-closed `Unknown`). NEVER returns a wrong SAT.
    fn try_mbqi_sat_certification(
        &mut self,
        pre_restore_assertions: &[TermId],
        category: LogicCategory,
        has_uninstantiated_quantifiers: bool,
        full_ematching_coverage: bool,
    ) -> Option<()> {
        let original_assertions = self.ctx.assertions.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_validation_stats = self.last_validation_stats.clone();
        let saved_unknown_reason = self.last_unknown_reason;

        // Every quantified original must be represented in `forall_quants`.
        // This collector intentionally accepts only direct assertion roots;
        // allowing a quantifier nested under `not`, `or`, `ite`, or another
        // application would let a SAT certificate validate the extracted
        // forall while silently dropping the enclosing Boolean obligation.
        if original_assertions.iter().copied().any(|assertion| {
            contains_quantifier(&self.ctx.terms, assertion)
                && !matches!(self.ctx.terms.get(assertion), TermData::Forall(..))
        }) {
            return None;
        }
        let forall_quants: Vec<TermId> = original_assertions
            .iter()
            .copied()
            .filter(|&a| matches!(self.ctx.terms.get(a), TermData::Forall(..)))
            .collect();
        if forall_quants.is_empty() {
            return None;
        }

        // Keep the exact predecessor (and all of its non-cloning seals) out of
        // the disposable refinement. The probe receives only a semantic clone;
        // a successful certificate seals/replaces that clone explicitly, while
        // a decline moves the untouched predecessor back.
        let saved_model = self.last_model.take();
        self.last_model = saved_model.clone();
        let saved_dt_cert_grant = std::mem::replace(&mut self.dt_cert_grant_active, false);
        let saved_dt_cert_query_grant = self.dt_cert_query_grant.take();
        let saved_finite_table_cert_grant =
            std::mem::replace(&mut self.finite_table_cert_grant_active, false);
        let saved_finite_table_witness = self.finite_table_cert_witness_state.take();
        let saved_const_interp_cert_grant =
            std::mem::replace(&mut self.const_interp_cert_grant_active, false);
        let saved_const_interp_witness = self.const_interp_cert_witness_state.take();
        let saved_cegqi_uf_recompletion_grant = self.cegqi_uf_recompletion_grant.take();
        let saved_mbqi_sat_cert_grant =
            std::mem::replace(&mut self.mbqi_sat_cert_grant_active, false);
        let saved_mbqi_sat_cert_query_grant = self.mbqi_sat_cert_query_grant.take();
        let saved_bv_full_domain_proof =
            std::mem::replace(&mut self.bv_quantifier_full_domain_proof, false);
        let saved_bv_full_domain_pending_evidence =
            self.bv_quantifier_full_domain_pending_evidence.take();
        let saved_bv_full_domain_query_grant = self.bv_quantifier_full_domain_query_grant.take();
        let saved_theory_state = self.incr_theory_state.take();
        let saved_bv_state = self.incr_bv_state.take();
        self.ctx.assertions = pre_restore_assertions.to_vec();
        let refinement_result =
            self.try_mbqi_refinement(&forall_quants, category, &original_assertions);

        // Only proceed to certification when refinement did NOT refute
        // (None => SAT fixpoint, or Sat).
        let proceed = !matches!(
            refinement_result,
            Some(Ok(SolveResult::Unsat(_))) | Some(Err(_))
        );

        // The predecessor model and every capability that names it are parked
        // in the affine snapshot above. Revoke any authority minted by the
        // disposable refinement before constructing replacement evidence. In
        // particular, doing this after `CheckedMbqiSatAuthority::for_current`
        // would revoke the fresh model seal carried by that linear token and
        // make the subsequent install fail closed.
        self.clear_quantified_sat_authority();

        let certified = if proceed {
            self.mbqi_sat_validated_finite_uninterpreted_domain(
                &original_assertions,
                &forall_quants,
            )
            // LEFT-INVERSE (boxing) axioms `forall x. Unbox(Box x) = x`
            // (deductive-checks polymorphism, #2774), mixed only with
            // universe-independent shapes (unary identity definitions,
            // guarded foralls with a materialized-true closed disjunct).
            // The certificate EXHIBITS a total model by functionalized
            // re-evaluation — Box := injective embedding, Unbox :=
            // table-inverse + fallback, identity heads := id — and
            // re-verifies EVERY original assertion under it, trusting neither
            // the prior validation nor the (lossy) extracted function tables.
            // The campaign gate is defense in depth on top of that construction.
            .or_else(|| {
                (!has_uninstantiated_quantifiers && full_ematching_coverage)
                    .then(|| {
                        saved_model.clone().and_then(|model| {
                            self.mbqi_sat_validated_left_inverse_axioms(
                                &original_assertions,
                                &forall_quants,
                                model,
                            )
                        })
                    })
                    .flatten()
            })
        } else {
            None
        };

        self.ctx.assertions = original_assertions.clone();
        self.incr_theory_state = saved_theory_state;
        self.incr_bv_state = saved_bv_state;

        let restore_predecessor = |executor: &mut Executor| {
            // Model first, then the exact executor-side capabilities that name
            // it. Assignments discard every disposable-probe artifact.
            executor.last_model = saved_model;
            executor.dt_cert_grant_active = saved_dt_cert_grant;
            executor.dt_cert_query_grant = saved_dt_cert_query_grant;
            executor.finite_table_cert_grant_active = saved_finite_table_cert_grant;
            executor.finite_table_cert_witness_state = saved_finite_table_witness;
            executor.const_interp_cert_grant_active = saved_const_interp_cert_grant;
            executor.const_interp_cert_witness_state = saved_const_interp_witness;
            executor.cegqi_uf_recompletion_grant = saved_cegqi_uf_recompletion_grant;
            executor.mbqi_sat_cert_grant_active = saved_mbqi_sat_cert_grant;
            executor.mbqi_sat_cert_query_grant = saved_mbqi_sat_cert_query_grant;
            executor.bv_quantifier_full_domain_proof = saved_bv_full_domain_proof;
            executor.bv_quantifier_full_domain_pending_evidence =
                saved_bv_full_domain_pending_evidence;
            executor.bv_quantifier_full_domain_query_grant = saved_bv_full_domain_query_grant;
            executor.last_model_validated = saved_model_validated;
            executor.last_validation_stats = saved_validation_stats;
            executor.last_unknown_reason = saved_unknown_reason;
        };

        if let Some(evidence) = certified {
            // This evidence names the probe's newly sealed model. Every
            // predecessor/probe routing artifact was dropped before it was
            // constructed. If the typed install fails, the affine predecessor
            // snapshot below is still intact and can be moved back exactly.
            if self.install_mbqi_sat_authority(evidence) {
                self.last_model_validated = true;
                self.last_unknown_reason = None;
                Some(())
            } else {
                restore_predecessor(self);
                None
            }
        } else {
            restore_predecessor(self);
            None
        }
    }

    /// Independently verify a CEGQI candidate UNSAT.
    ///
    /// The live probe is intentionally not inspected here. It may contain a
    /// CE-derived, CE-variable-free residue, so neither term shape nor absence
    /// of CE variables is publication authority. Instead, reconstruct a fresh
    /// consequence set from exactly two provenance-bearing sources:
    ///
    /// - quantifier-free conjuncts of the pre-instantiation snapshot; and
    /// - `active_support_axioms`, whose write-side contract admits only ground
    ///   instances of unconditionally asserted universals.
    ///
    /// A definitive UNSAT from either the ground core or that authorized
    /// instance closure implies UNSAT of the original formula. Every other
    /// outcome fails closed, including a missing snapshot or external stop.
    fn cegqi_consequence_set_is_unsat(
        &mut self,
        snapshot: Option<&[TermId]>,
        category: LogicCategory,
    ) -> bool {
        let trace = ay_core::misc_cli_flags().trace_cegqi_attr;
        // The disposable verifier below intentionally does not export a proof.
        // Mandatory proof modes therefore decline until the consequence
        // certificate carries a translated proof object for the authored
        // snapshot. The synthesized default proof mode is best-effort: it may
        // publish the independently checked verdict, but the sealed publisher
        // marks proof reconstruction and export as unavailable for that result.
        if self.translated_unsat_proof_required() {
            if trace {
                eprintln!(
                    "[cegqi-attr] DECLINE: mandatory proof mode has no translated certificate"
                );
            }
            return false;
        }
        let Some(snapshot) = snapshot else {
            if trace {
                eprintln!("[cegqi-attr] DECLINE: no pre-instantiation snapshot");
            }
            return false;
        };
        if self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            if trace {
                eprintln!("[cegqi-attr] DECLINE: resource or external-stop preflight");
            }
            return false;
        }

        // Reconstruct, rather than filter, the only assertions the verifier is
        // allowed to trust. No live CEGQI assertion is copied.
        let mut consequences = self.snapshot_ground_core(snapshot);
        let ground_len = consequences.len();
        for support in &self.active_support_axioms {
            if support.value
                && !contains_quantifier(&self.ctx.terms, support.term)
                && !consequences.contains(&support.term)
            {
                consequences.push(support.term);
            }
        }
        if consequences.is_empty() {
            if trace {
                eprintln!("[cegqi-attr] DECLINE: authorized consequence set is empty");
            }
            return false;
        }

        // Full solve-state isolation is provided by the disposable ground
        // helper. Only constructing this conjunction touches the outer
        // append-only term store; no solver artifact crosses back.
        let consequence_len = consequences.len();
        let formula = self.ctx.terms.mk_and(consequences);
        let obligation = vec![formula];
        let refuted = match self.checked_ground_solve(obligation.clone(), category, 2_000) {
            Some(CheckedGroundDecision::Unsat(checked)) => checked.consume(self, &obligation),
            _ => false,
        };

        // Do not publish work that raced an outer interrupt/deadline/memory
        // stop, even if the disposable solver happened to finish first.
        if self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            if trace {
                eprintln!("[cegqi-attr] DECLINE: stop/resource preflight after verification");
            }
            return false;
        }
        if !refuted {
            if trace {
                eprintln!("[cegqi-attr] DECLINE: authorized consequence set not UNSAT");
            }
            return false;
        }
        if trace {
            let source = if consequence_len == ground_len {
                "snapshot-ground-core"
            } else {
                "authorized-instance-closure"
            };
            eprintln!("[cegqi-attr] GRANT: independently checked {source} UNSAT");
        }
        true
    }

    /// Install a model of the snapshot's authenticated ground remainder.
    ///
    /// This supplies the SAT-side ground premise for CEGQI disambiguation and
    /// for self-contained finite/default completion certificates. In
    /// particular, a model of the live assertion set with CE terms filtered out
    /// is insufficient: CE-directed rewriting can delete authored constraints.
    /// The solve runs in a disposable Executor that temporarily OWNS the original
    /// Context.  Moving rather than cloning the Context keeps every resulting
    /// `TermId` coherent while isolating the enclosing solve's statistics, proof
    /// tracker, validation memos, flags, and theory caches.  Only the returned
    /// Context and the successfully validated model-owned state cross back.
    fn checked_same_context_ground_model(
        &mut self,
        assertions: Vec<TermId>,
        budget_ms: u64,
    ) -> Option<CheckedSameContextGroundModel> {
        if assertions
            .iter()
            .any(|&root| contains_quantifier(&self.ctx.terms, root))
            || self.should_abort_theory_loop()
            || !self.qpf_probe_preflight()
        {
            return None;
        }
        let scope = CheckedSameContextGroundScope::capture(self, &assertions)?;

        // Construct and configure the disposable owner before lending it the
        // real Context. No allocation is then needed to put the Context back.
        let mut probe = self.qpf_probe_executor(ay_frontend::Context::new(), budget_ms);
        let window = self
            .ctx
            .begin_internal_query_window(assertions.clone())
            .ok()?;
        std::mem::swap(&mut self.ctx, &mut probe.ctx);

        // These maps name terms that live for the whole TermStore lifetime,
        // not merely one solver model. Seed the probe with the outer maps and
        // always return the possibly-extended maps, on every verdict and after
        // unwinding alike.
        std::mem::swap(
            &mut self.array_default_epsilon_by_sort,
            &mut probe.array_default_epsilon_by_sort,
        );
        std::mem::swap(
            &mut self.array_default_diag_by_sort,
            &mut probe.array_default_diag_by_sort,
        );
        probe.original_problem_had_quantifiers = false;
        probe.incremental_mode = false;

        // Keep `probe` outside the closure. A solver panic is resumed only
        // after the exact outer query window, Context, and TermStore-lifetime
        // sidecars have been restored.
        let nested = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            probe.begin_public_solve(false);
            probe.bind_unsat_query_assumptions(&[]);
            match probe.check_sat().ok()? {
                SolveResult::Sat => probe.take_sat_certificate()?.into_validated_model(),
                SolveResult::Unsat(_) | SolveResult::Unknown => None,
            }
        }));

        let window_is_current = probe.ctx.restore_internal_query_window(window);
        std::mem::swap(&mut self.ctx, &mut probe.ctx);
        std::mem::swap(
            &mut self.array_default_epsilon_by_sort,
            &mut probe.array_default_epsilon_by_sort,
        );
        std::mem::swap(
            &mut self.array_default_diag_by_sort,
            &mut probe.array_default_diag_by_sort,
        );

        let certificate = match nested {
            Ok(certificate) => certificate?,
            Err(payload) => std::panic::resume_unwind(payload),
        };
        if !window_is_current
            || !scope.is_current(self)
            || self.should_abort_theory_loop()
            || !probe.last_model_validated
            || probe.skip_model_eval
            || probe.defer_model_validation
            || probe.dt_validation_wants_egraph
            || probe.dt_egraph_building.get()
            || !probe
                .model_validation_delegated_assertions
                .iter()
                .all(|root| assertions.contains(root))
        {
            return None;
        }

        Some(CheckedSameContextGroundModel {
            scope,
            _certificate: certificate,
            model: probe.last_model.take()?,
            nra_algebraic_model: probe.nra_algebraic_model.take_values(),
            dt_theory_model: probe.dt_theory_model.take(),
            recorded_var_substitutions: std::mem::take(&mut probe.recorded_var_substitutions),
            delegated_assertions: std::mem::take(&mut probe.model_validation_delegated_assertions),
        })
    }

    /// Solve an exact quantifier-free assertion vector on a same-context
    /// disposable Executor and return its STRICT-CHECKED UNSAT proof object
    /// (#consequence-replay).
    ///
    /// The [`Self::checked_same_context_ground_model`] pattern is mirrored
    /// exactly — internal query window, Context swap, sidecar map swaps,
    /// panic-safe restoration — because the returned proof's steps reference
    /// `TermId`s that must stay coherent in the OUTER term store. A cloned
    /// context (the `checked_isolated_solve` route) cannot provide that: terms
    /// minted during the probe's own solving would dangle or diverge outside.
    ///
    /// The probe runs the ordinary public `check_sat` pipeline, so the proof
    /// tracker is armed and `build_unsat_proof` runs the full authored
    /// replacement cascade over the probe's window. The proof is returned only
    /// when the probe's OWN strict checker accepts it complete over the probe
    /// window; the caller must still re-validate the stitched result against
    /// the enclosing authored scope, which is where publication authority
    /// lives. Every other outcome — SAT, unknown, missing or trust-carrying
    /// proof, stale window, external stop — returns `None`.
    pub(in crate::executor) fn checked_same_context_unsat_proof(
        &mut self,
        assertions: &[TermId],
        budget_ms: u64,
        scope_to_window: bool,
    ) -> SameContextProbeOutcome {
        if assertions
            .iter()
            .any(|&root| contains_quantifier(&self.ctx.terms, root))
            || self.should_abort_theory_loop()
            || !self.qpf_probe_preflight()
        {
            return SameContextProbeOutcome::Other;
        }

        let mut probe = self.qpf_probe_executor(ay_frontend::Context::new(), budget_ms);
        // This disposable executor is a proof *producer*, not a publication
        // boundary.  Inherited self-check would inspect the raw proof before
        // the consequence-replay-specific assertion/conjunct and EUF rebuilds
        // below, turn the provisional UNSAT into `Unknown`, and prevent those
        // sound rebuilds from ever running.  Defer that one gate locally: no
        // verdict leaves this method, and the rebuilt proof is still returned
        // only after the probe's strict checker accepts it complete.  The
        // enclosing authored query then strictly checks the stitched proof
        // again before publication.
        probe.set_self_check(false);
        // Scope the probe's whole-store array-axiom scans to its own window
        // (see the field doc: unscoped, outer dead array-equality terms seed
        // hundreds of phantom congruence axioms and a fused Generic conflict).
        //
        // The caller controls the scope (#frame-probe-unscoped-retry): the
        // window scope keeps the #7956-class probe fast and its conflicts
        // small, but a window with NO array-equality atom of its own loses
        // every congruence/extensionality seed, and the same refutation then
        // fuses into one Generic theory conflict strict mode must refuse
        // (measured on the array-frame self-check fixture: scoped ext=0/ac=0
        // axioms -> fused 23-literal Generic, unscoped ext=2/ac=134 -> the
        // identical probe's proof is strict-complete). The metered caller
        // therefore retries exactly the raw-UNSAT-but-unpromotable outcome
        // with the scope off, under a fresh grant from the same envelope.
        probe.shared_store_derived_query = scope_to_window;
        let Ok(window) = self.ctx.begin_internal_query_window(assertions.to_vec()) else {
            return SameContextProbeOutcome::Other;
        };
        std::mem::swap(&mut self.ctx, &mut probe.ctx);
        std::mem::swap(
            &mut self.array_default_epsilon_by_sort,
            &mut probe.array_default_epsilon_by_sort,
        );
        std::mem::swap(
            &mut self.array_default_diag_by_sort,
            &mut probe.array_default_diag_by_sort,
        );
        probe.original_problem_had_quantifiers = false;
        probe.incremental_mode = false;

        // Keep `probe` outside the closure: a solver panic is resumed only
        // after the exact outer query window, Context, and sidecars have been
        // restored.
        let trace = ay_core::misc_cli_flags().trace_cegqi_attr;
        let nested = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            probe.begin_public_solve(false);
            probe.bind_unsat_query_assumptions(&[]);
            let raw = probe.check_sat();
            if trace {
                eprintln!(
                    "[consequence-replay] probe raw result: {raw:?} unknown_reason: {:?}",
                    probe.last_unknown_reason
                );
            }
            match raw {
                Ok(SolveResult::Unsat(_)) => {
                    match probe.finish_consequence_probe_unsat_proof(assertions) {
                        Some(proof) => SameContextProbeOutcome::Proof(proof),
                        // The refutation is real but its proof could not be
                        // completed to a strict-checkable document.
                        None => SameContextProbeOutcome::UnsatUnpromotable,
                    }
                }
                Ok(SolveResult::Sat | SolveResult::Unknown) | Err(_) => {
                    SameContextProbeOutcome::Other
                }
            }
        }));

        let window_is_current = probe.ctx.restore_internal_query_window(window);
        // (#ground-conflict-decomp) Fold the disposable probe's decomposition
        // meters into this executor so `--stats` reports the pass's exact
        // attempted/applied/declined counts wherever the pass actually ran.
        {
            let meters = &self.ground_conflict_decomp_meters;
            let probe_meters = &probe.ground_conflict_decomp_meters;
            meters.attempted.set(
                meters
                    .attempted
                    .get()
                    .saturating_add(probe_meters.attempted.get()),
            );
            meters.applied.set(
                meters
                    .applied
                    .get()
                    .saturating_add(probe_meters.applied.get()),
            );
            meters.declined.set(
                meters
                    .declined
                    .get()
                    .saturating_add(probe_meters.declined.get()),
            );
        }
        std::mem::swap(&mut self.ctx, &mut probe.ctx);
        std::mem::swap(
            &mut self.array_default_epsilon_by_sort,
            &mut probe.array_default_epsilon_by_sort,
        );
        std::mem::swap(
            &mut self.array_default_diag_by_sort,
            &mut probe.array_default_diag_by_sort,
        );

        let outcome = match nested {
            Ok(outcome) => outcome,
            Err(payload) => std::panic::resume_unwind(payload),
        };
        if !window_is_current || self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            // Post-probe state is suspect: no proof may leave, and no retry
            // may be advised off it either.
            return SameContextProbeOutcome::Other;
        }
        outcome
    }

    /// Atomically install, optionally postprocess, and consume a checked model.
    ///
    /// `postprocess` runs only after the untouched candidate satisfies the
    /// exact derived roots, and before the candidate receives its model seal.
    /// The evaluator memo is unconditionally cleared afterward and the exact
    /// roots are rechecked, so correctness cannot depend on a callback
    /// accurately reporting whether it mutated the model. `consume` then
    /// receives the affine installed-model token after the final model is
    /// sealed, while rollback is still armed. It must not mutate the sealed
    /// model payload.
    ///
    /// Returning `None`, observing a stale scope/interrupt, or unwinding from
    /// either callback restores the exact prior model object and all paired
    /// evaluator, validation, publication, MBQI, result, and statistics state.
    fn with_checked_same_context_ground_model_bundle<R, P, C>(
        &mut self,
        checked: CheckedSameContextGroundModel,
        postprocess: P,
        consume: C,
    ) -> Option<R>
    where
        P: FnOnce(&mut Executor, &[TermId]) -> Option<()>,
        C: FnOnce(&mut Executor, InstalledCheckedGroundModel) -> Option<R>,
    {
        let CheckedSameContextGroundModel {
            scope,
            _certificate,
            model,
            nra_algebraic_model,
            dt_theory_model,
            recorded_var_substitutions,
            delegated_assertions,
        } = checked;
        if !scope.is_current(self)
            || self.should_abort_theory_loop()
            || !delegated_assertions
                .iter()
                .all(|root| scope.roots.contains(root))
        {
            return None;
        }

        let mut transaction = CheckedModelInstallTransaction::begin(self);
        let result = {
            let executor = transaction.executor();
            executor.last_model = Some(model);
            executor.restore_nra_values(nra_algebraic_model);
            executor.dt_theory_model = dt_theory_model;
            executor.dt_validation_wants_egraph = false;
            executor.dt_egraph_assignment.replace(None);
            executor.dt_egraph_building.set(false);
            executor.recorded_var_substitutions = recorded_var_substitutions;
            executor.model_validation_delegated_assertions = delegated_assertions;
            executor.last_model_validated = false;
            executor.last_validation_stats = None;
            executor.last_sat_certificate = None;
            crate::executor::model::eval_memo_clear();

            if !installed_model_satisfies_roots(executor, &scope.roots) {
                return None;
            }

            postprocess(executor, &scope.roots)?;
            crate::executor::model::eval_memo_clear();
            if !installed_model_satisfies_roots(executor, &scope.roots) {
                return None;
            }
            if !scope.is_current(executor) || executor.should_abort_theory_loop() {
                return None;
            }

            let model_epoch = executor.last_model.as_mut()?.seal_quantified_grant_model();
            let installed = InstalledCheckedGroundModel { scope, model_epoch };
            if !installed.is_current(executor) {
                return None;
            }
            consume(executor, installed)?
        };

        transaction.commit();
        Some(result)
    }

    /// Solve exact quantifier-free roots, install their checked model, and run
    /// one pre-seal postprocessor plus one post-seal token consumer atomically.
    pub(in crate::executor) fn with_checked_same_context_ground_model<R, P, C>(
        &mut self,
        assertions: Vec<TermId>,
        budget_ms: u64,
        postprocess: P,
        consume: C,
    ) -> Option<R>
    where
        P: FnOnce(&mut Executor, &[TermId]) -> Option<()>,
        C: FnOnce(&mut Executor, InstalledCheckedGroundModel) -> Option<R>,
    {
        let checked = self.checked_same_context_ground_model(assertions, budget_ms)?;
        self.with_checked_same_context_ground_model_bundle(checked, postprocess, consume)
    }

    /// Solve exact quantifier-free roots in the original term arena and
    /// atomically install their validated model.
    ///
    /// The returned affine token is bound to the enclosing public query,
    /// frontend source/scope, ordered root entry identities, append-only term
    /// prefix, and exact installed model object. It is ground-model authority
    /// only; a caller must combine it with its own quantified theorem before
    /// proposing public SAT.
    pub(in crate::executor) fn install_checked_same_context_ground_model(
        &mut self,
        assertions: Vec<TermId>,
        budget_ms: u64,
    ) -> Option<InstalledCheckedGroundModel> {
        self.with_checked_same_context_ground_model(
            assertions,
            budget_ms,
            |_executor, _roots| Some(()),
            |_executor, installed| Some(installed),
        )
    }

    fn ensure_snapshot_ground_model_for_completion(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> bool {
        // A retained CE/live-window model is only an untrusted candidate here.
        // Reuse it when the same exact evaluator trusted by the completion
        // certificates establishes every authenticated ground conjunct. If it
        // does not, replace it with a freshly solved same-Context witness. The
        // finite/default certificate still repeats this check before granting;
        // this boundary prevents a stale candidate from suppressing the repair.
        let retained_model = self.last_model.clone();
        let retained_satisfies_ground = retained_model.as_ref().is_some_and(|model| {
            self.snapshot_ground_core(snapshot)
                .into_iter()
                .all(|ground| matches!(self.evaluate_term(model, ground), EvalValue::Bool(true)))
        });
        retained_satisfies_ground
            || self
                .install_authenticated_snapshot_ground_model(snapshot, fallback_category)
                .is_some()
    }

    fn install_authenticated_snapshot_ground_model(
        &mut self,
        snapshot: &[TermId],
        _fallback_category: LogicCategory,
    ) -> Option<InstalledCheckedGroundModel> {
        if self.should_abort_theory_loop() {
            return None;
        }
        let ground = self.snapshot_ground_core(snapshot);
        let installed = self.install_checked_same_context_ground_model(ground.clone(), 2_000);
        if installed.is_none() {
            self.clear_cegqi_inner_unsat_artifacts();
        }
        if ay_core::misc_cli_flags().trace_cegqi_attr {
            eprintln!(
                "[cegqi-attr] authenticated G0 model: ground_roots={} accepted={}",
                ground.len(),
                installed.is_some(),
            );
        }
        // The inner solver validated only the ground remainder.  The caller may
        // mark the model globally valid only after it proves every quantified
        // obligation from the authenticated snapshot.
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.last_sat_certificate = None;
        installed
    }

    /// Remove UNSAT-only artifacts left by a bounded theorem subsolve before
    /// final CEGQI SAT publication. Returning SAT does not remove the raw proof and
    /// provenance fields retained by an inner per-lemma refutation. Keep this
    /// cleanup adjacent to the sealed SAT witness consumption sites so no
    /// later internal path can reuse those stale artifacts.
    fn clear_cegqi_inner_unsat_artifacts(&mut self) {
        self.note_cegqi_inner_unsat_artifact_clear();
        self.last_proof = None;
        self.clear_finite_enum_proof_state();
        self.last_unsat_proof_reconstruction_suppressed = false;
        self.last_lrat_certificate = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_clause_trace = None;
        self.last_checked_sat_refutation = None;
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.proof_check_result = None;
        self.proof_check_ok = false;
    }

    /// Whether an internal UNSAT theorem must carry a translated
    /// authored-scope proof.
    ///
    /// A reconstruction budget is a capability installed only for the
    /// synthesized default, best-effort certificate. Script proof requests,
    /// strict checking, and self-check remain mandatory even if a caller
    /// accidentally leaves that capability installed.
    pub(in crate::executor) fn translated_unsat_proof_required(&self) -> bool {
        let script_produce_proofs = matches!(
            self.ctx.get_option("produce-proofs"),
            Some(ay_frontend::OptionValue::Bool(true))
        );
        let strict_proofs = matches!(
            self.ctx.get_option("check-proofs-strict"),
            Some(ay_frontend::OptionValue::Bool(true))
        );
        // Every public exact-query decision requires an authored-scope
        // translated proof. Disposable internal solves have no public epoch;
        // their semantic result can feed a producer, but never publication
        // authority by itself.
        self.active_unsat_query_requires_strict_proof()
            || self.self_check()
            || script_produce_proofs
            || strict_proofs
            || self.proof_artifact_required
    }

    /// Publish an independently certified semantic quantified UNSAT without
    /// claiming proof authority for an outer trace produced over a different
    /// assertion window.
    ///
    /// This is the single artifact firewall for disposable consequence solves,
    /// temporary MBQI instances, and model-independent quantified refutations.
    /// Their mathematical verdict may be sound while their raw proof refers to
    /// fresh constants or assertions that are not in the authored problem.  No
    /// such proof state is allowed to survive publication.
    fn publish_quantified_verdict_only_unsat(&mut self) -> SolveResult {
        self.clear_cegqi_inner_unsat_artifacts();
        self.last_negations = None;
        self.last_proof_rebuild_originals.clear();
        self.last_proof_raw_original_assertions.clear();
        self.last_proof_expanded_let_sources.clear();
        self.quant_expansion_records.clear();
        if self.proof_problem_assertion_provenance.is_some() {
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "proof-source provenance CLEARED by publish_quantified_verdict_only_unsat"
                    .to_string()
            });
        }
        self.proof_problem_assertion_provenance = None;
        self.proof_tracker.reset_session();
        self.suppress_unsat_proof_reconstruction();
        self.last_unknown_reason = None;
        SolveResult::unsat()
    }

    /// Empty-universe EPR UNSAT publisher.
    ///
    /// The EPR singleton path has already CHECKED the singleton-instance UNSAT,
    /// but its raw proof names the synthesized witness assertions, not the
    /// authored `forall`s, so the ordinary
    /// [`Self::quantified_semantic_unsat_or_unknown`] artifact firewall
    /// downgrades the correct `unsat` to `unknown` under mandatory
    /// certification. First TRY to translate the semantic verdict into an
    /// authored-scope `forall_inst` certificate
    /// ([`Self::try_translate_witnessed_forall_conflict_unsat`]); on success the
    /// ordinary publication funnel mints a genuine `StrictProof` token and the
    /// verdict publishes as `unsat`. On failure fall back to the unchanged
    /// fail-closed firewall — so this can only ever turn a firewalled `unknown`
    /// into a strictly-certified `unsat`, never widen what publishes.
    fn empty_universe_semantic_unsat_or_unknown(&mut self) -> Result<SolveResult> {
        if self.try_translate_witnessed_forall_conflict_unsat() {
            self.last_unknown_reason = None;
            return Ok(SolveResult::unsat());
        }
        self.quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierUnhandled)
    }

    fn cegqi_inner_unsat_or_unknown(&mut self) -> Result<SolveResult> {
        self.quantified_semantic_unsat_or_unknown(UnknownReason::QuantifierCegqiIncomplete)
    }

    fn cegqi_fail_closed_unknown(&mut self) -> Result<SolveResult> {
        self.clear_cegqi_inner_unsat_artifacts();
        // No quantified SAT authority may survive a fail-closed transition.
        self.clear_quantified_sat_authority();
        if let Some(reason) = self.external_stop_reason() {
            self.last_unknown_reason = Some(reason);
        } else if self.last_unknown_reason.is_none() {
            self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
        }
        Ok(SolveResult::Unknown)
    }

    /// Rebuild the authenticated snapshot-ground witness and combine it with
    /// the sealed per-universal model-group theorem.
    ///
    /// This route is valid whether the mutable CE window ended in `Sat` or
    /// `Unsat`: neither raw result is authority. The helper returns only after
    /// the positive source-binding checker, exact group-coverage checks, and
    /// isolated per-group refutations have constructed a consumable
    /// [`cegqi_sat_authority::CheckedSat`].
    fn try_cegqi_model_group_sat(
        &mut self,
        snapshot: &[TermId],
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        cegqi_state: &[(TermId, CegqiInstantiator)],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let ground_witness = cegqi_sat_authority::install(self, snapshot, category)?;
        let checked = cegqi_sat_authority::certify_model_group_refutations(
            self,
            ground_witness,
            snapshot,
            ce_lemma_groups,
            cegqi_state,
            category,
        )
        .ok()?;
        Some(checked.publish(self))
    }

    /// Disambiguate UNSAT from CEGQI refinement (#5975).
    ///
    /// Re-solves without CE lemmas to determine if UNSAT is genuine
    /// (from ground assertions alone) or CE-induced (forall is valid → SAT).
    ///
    /// `cegqi_state` carries the (quantifier, instantiator) pairs so the
    /// quantified-CE-lemma decider legs can rebuild per-universal obligations;
    /// `snapshot` is the pre-instantiation assertion snapshot
    /// (`refinement_assertions`), threaded through every caller (including the
    /// CEGQI refinement loop). A `None` snapshot disables both decider legs
    /// and the independent UNSAT certificate because all three need authored
    /// snapshot provenance; the result therefore fails closed to Unknown.
    pub(super) fn disambiguate_cegqi_unsat(
        &mut self,
        category: LogicCategory,
        ce_lemma_ids: &[TermId],
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        is_mixed: bool,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: Option<&[TermId]>,
    ) -> Result<SolveResult> {
        // Prefer an actual authored-scope refutation over every semantic
        // attribution heuristic.  CEGQI/enumerative writers register exact
        // ground instances as `forall_inst` derivations; when the live ground
        // conflict depends only on those consequences (and not on a CE search
        // lemma), the finished proof validates directly against the immutable
        // public problem.  A CE-dependent conflict necessarily leaves a
        // foreign Assume/trust leaf and this strict check declines, after which
        // the existing independent disambiguation remains fail-closed.
        if self.produce_proofs_enabled() && self.last_proof.is_none() {
            self.build_unsat_proof();
        }
        if let Some(proof) = self.last_proof.as_ref() {
            match self.check_proof_strict_with_datatypes(proof) {
                Ok(_) => {
                    // Surface/export reconstruction may have deliberately
                    // suppressed a proof that is valid internally but cannot
                    // be represented faithfully for an external Alethe
                    // checker.  Strict success authorizes the verdict; it must
                    // never clear that independent artifact firewall.
                    self.last_unknown_reason = None;
                    return Ok(SolveResult::unsat());
                }
                Err(error) if ay_core::misc_cli_flags().trace_cegqi_attr => {
                    eprintln!("[cegqi-attr] live strict proof declined: {error}");
                    for (index, step) in proof.steps.iter().take(64).enumerate() {
                        eprintln!("[cegqi-attr] proof[{index}] = {step:?}");
                    }
                }
                Err(_) => {}
            }
        }

        // #cegqi-attribution: the live "ground-minus-CE" set is not consulted
        // for either verdict. Identity filtering is broken by in-place
        // rewriting, while CE-variable filtering still admits CE-derived,
        // CE-variable-free residues and can delete authored constraints. UNSAT
        // therefore requires the sealed consequence certificate below. SAT
        // requires a separate, definitive solve of the reconstructed snapshot
        // ground core plus one of the sealed per-universal theorem checks below.

        if let Some(certificate) = cegqi_unsat_authority::certify(self, snapshot, category) {
            return Ok(certificate.publish(self));
        }
        // Identifier loss is itself untrusted: with no CE obligation left to
        // verify, neither SAT route has a theorem premise. The raw UNSAT was
        // already declined by the consequence verifier above.
        if ce_lemma_ids.is_empty() {
            self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
            return self.cegqi_fail_closed_unknown();
        }
        let Some(snapshot) = snapshot else {
            return self.cegqi_fail_closed_unknown();
        };
        if is_mixed {
            self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
            return self.cegqi_fail_closed_unknown();
        }
        let Some(ground_witness) = cegqi_sat_authority::install(self, snapshot, category) else {
            return self.cegqi_fail_closed_unknown();
        };
        let ground_witness = match cegqi_sat_authority::certify_model_group_refutations(
            self,
            ground_witness,
            snapshot,
            ce_lemma_groups,
            cegqi_state,
            category,
        ) {
            Ok(checked) => return checked.publish(self),
            Err(ground_witness) => ground_witness,
        };
        let ground_witness = match cegqi_sat_authority::certify_quantified_ce_refutations(
            self,
            ground_witness,
            cegqi_state,
            snapshot,
            category,
        ) {
            Ok(checked) => return checked.publish(self),
            Err(ground_witness) => ground_witness,
        };
        // Neither universal-validity route accepted the ground witness.  It
        // must not escape this decision point or be reusable as SAT authority.
        drop(ground_witness);

        // UNSAT leg: a conjunctive-position universal that is FALSE at a
        // concrete ground witness refutes the whole problem.
        let cegqi_foralls: Vec<TermId> = cegqi_state
            .iter()
            .filter(|(_, inst)| inst.is_forall())
            .map(|(q, _)| *q)
            .collect();
        if let Some(Ok(SolveResult::Unsat(_))) =
            self.universal_false_at_ground_witness(&cegqi_foralls, snapshot, category)
        {
            return self.cegqi_inner_unsat_or_unknown();
        }
        self.last_unknown_reason = Some(UnknownReason::QuantifierCegqiIncomplete);
        self.cegqi_fail_closed_unknown()
    }

    /// Check whether the installed authenticated G0 model can be completed to
    /// satisfy every CEGQI universal represented by `ce_lemma_groups`.
    ///
    /// This method returns only a theorem fact; the sealed SAT authority module
    /// combines it with the linear G0 witness and owns publication.
    fn cegqi_model_refutes_all_groups(
        &mut self,
        snapshot: &[TermId],
        ce_vars: &ay_core::kani_compat::DetHashSet<TermId>,
        ce_lemma_groups: &[(TermId, Vec<TermId>)],
        category: LogicCategory,
    ) -> Option<CegqiGroupRefutation> {
        // SOUNDNESS (RED S3, 2026-07-08): "ground-minus-CE-lemma is Sat"
        // does NOT establish the universal's validity — the CEGQI-sound
        // premise for the valid→SAT flip is "the CE lemma (the
        // counterexample search space) is UNSAT". The old unconditional
        // flip minted a wrong SAT for the ∀∃ alternation
        // `(forall x (exists y (= (* y y) x)))` (FALSE at x = 2): its CE
        // lemma `¬∃y. y² = sk` is SATISFIABLE (sk := 2), yet the empty
        // ground remainder answered Sat and the flip shipped it. Verify
        // the premise independently on the CE lemmas ALONE; anything
        // short of a definitive UNSAT fails closed to Unknown (exactly
        // the honest verdict the RED fixture prescribes). Legitimate
        // recoveries (QF_AX extensionality) carry a provably-UNSAT CE
        // lemma and keep their SAT.
        // SOUNDNESS (multi-lemma disjunction hole, 2026-07-10): the
        // refutation must be PER LEMMA, not joint. A joint UNSAT of
        // `¬B1(sk1) ∧ ¬B2(sk2)` only proves the DISJUNCTION
        // `(∀x.B1) ∨ (∀y.B2)` — not that both universals are valid.
        // With two universals coupled through a shared free symbol
        // (`∀x. x≥0 ∨ q` and `∀y. y<0 ∨ ¬q`, jointly ≡ q ∧ ¬q, UNSAT)
        // the joint CE conjunction contains `¬q ∧ q` and is trivially
        // UNSAT, and the joint flip minted a wrong SAT. Per-lemma
        // isolated UNSAT (`¬Bi(ski)` unsatisfiable on its own) proves
        // EVERY universal valid — the sound premise. Strictly stronger
        // than the joint solve, so no wrong verdict the joint check
        // rejected can pass here.
        // Every theorem query below runs through the structurally isolated
        // ground-solve helper.  The only outer state this verifier changes is
        // the bounded deadline (restored before return) and append-only pin
        // terms in the TermStore.
        // CONTEXT (#cegqi-ground-core, 2026-07-10): refute each lemma
        // against the quantifier-free ground core G0 of the
        // PRE-INSTANTIATION snapshot, not in an empty context. Sound
        // by the fresh-constant rule: the CE constants c⃗ were minted
        // AFTER the snapshot, so no G0 conjunct mentions them, and
        // UNSAT of `G0 ∧ ¬B(c⃗)` proves `G0 ⊨ ∀x⃗.B`; entailment is
        // monotone in premises, so the full ground set (just proved
        // Sat above) also entails the universal — the flip is a real
        // SAT. The snapshot (NOT the live assertion set) is essential:
        // live CEGQI instantiation lemmas can mention c⃗ (the round
        // instantiates at the CE witness), which would break freshness
        // and make the "refutation" vacuous. Empty-context isolation
        // (1ccc600d) demanded each universal be VALID outright and
        // degraded every relative-to-ground universal — asserted-Bool,
        // ground-UF, bound-coupled-free-var shapes — to Unknown (10
        // regressed group_quantifiers tests, 2026-07-10 bisect).
        let ground_core = self.snapshot_ground_core(snapshot);
        let model = self.last_model.clone()?;
        if ay_core::misc_cli_flags().trace_cegqi_attr {
            eprintln!(
                "[cegqi-attr] SAT model-group verifier: ground_roots={} groups={} ce_vars={}",
                ground_core.len(),
                ce_lemma_groups.len(),
                ce_vars.len(),
            );
        }
        // Model-relative pins (#cegqi-mdef, 2026-07-11): the
        // fresh-constant certificate below (G0 ⊨ ∀x⃗.B) cannot
        // certify a universal that is merely SATISFIED BY THE
        // CANDIDATE MODEL rather than entailed by ground facts
        // (`forall x. x>4 ∨ p` with nothing asserted: p:=true is
        // forced by no ground fact). Pin the ground-only candidate
        // model's values for the free NON-CE constants occurring in
        // the CE conjuncts: UNSAT of `M_def ∧ G0 ∧ ¬B(c⃗)` with c⃗
        // fresh w.r.t. M_def ∧ G0 proves the pinned model satisfies
        // ∀x⃗.B — an MBQI-style certificate for the model the solve
        // above just produced. Skolem-minted constants are never
        // pinned (an alternation's witness stays free, so its lemma
        // stays unrefutable on this leg — RED S3 keeps its UNSAT
        // route), and the VACUITY GUARD below requires M_def ∧ G0 to
        // be satisfiable before any refutation may use the pins, so
        // an inconsistent pin set can never mint a flip.
        let mut m_def: Vec<TermId> = Vec::new();
        let mut uf_pins: Vec<TermId> = Vec::new();
        let mut uf_recompletion: Option<CegqiUfRecompletion> = None;
        {
            use ay_core::kani_compat::DetHashSet;
            let mut pin_vars: Vec<TermId> = Vec::new();
            let mut uf_app_candidates: Vec<TermId> = Vec::new();
            let mut seen: DetHashSet<TermId> = DetHashSet::default();
            for (_, group) in ce_lemma_groups {
                for &conjunct in group {
                    let mut stack = vec![conjunct];
                    while let Some(t) = stack.pop() {
                        if !seen.insert(t) {
                            continue;
                        }
                        match self.ctx.terms.get(t) {
                            TermData::Var(name, _) => {
                                if !ce_vars.contains(&t) && !self.ctx.terms.is_skolem_symbol(name) {
                                    pin_vars.push(t);
                                }
                            }
                            TermData::App(_, args) => {
                                // UF-graph pin candidates (#cegqi-mdef
                                // v2): every application in a CE
                                // conjunct; head filtering below.
                                if !args.is_empty() {
                                    uf_app_candidates.push(t);
                                }
                                stack.extend(args.iter().copied());
                            }
                            TermData::Not(inner) => stack.push(*inner),
                            TermData::Ite(c, a, b) => {
                                stack.push(*c);
                                stack.push(*a);
                                stack.push(*b);
                            }
                            _ => {}
                        }
                    }
                }
            }
            for v in pin_vars {
                match self.evaluate_term(&model, v) {
                    EvalValue::Bool(true) => m_def.push(v),
                    EvalValue::Bool(false) => {
                        let nv = self.ctx.terms.mk_not(v);
                        m_def.push(nv);
                    }
                    EvalValue::Rational(r)
                        if r.is_integer()
                            && matches!(self.ctx.terms.sort(v), ay_core::Sort::Int) =>
                    {
                        let c = self.ctx.terms.mk_int(r.numer().clone());
                        let eq = self.ctx.terms.mk_eq(v, c);
                        m_def.push(eq);
                    }
                    EvalValue::BitVec { value, width } => {
                        let c = self.ctx.terms.mk_bitvec(value, width);
                        let eq = self.ctx.terms.mk_eq(v, c);
                        m_def.push(eq);
                    }
                    // Unpinnable value (FP/uninterpreted/...): leave
                    // the constant free — a group needing it stays
                    // unrefuted, which fails closed.
                    _ => {}
                }
            }
            // UF-GRAPH pins (#cegqi-mdef v2, 2026-07-11): constant
            // pins cannot constrain a UF application `f(t⃗)` in a CE
            // conjunct, so universals whose validity rests on the
            // model's INTERPRETATION of f stayed Unknown. Pin each
            // such head to a re-completion M′ of the candidate model:
            // collect the concrete graph {a⃗ᵢ ↦ bᵢ} of ALL f
            // occurrences across (live ground-only set ∪ ground
            // core), evaluated under M, and emit per CE application
            //   ⋁ᵢ (t⃗ = a⃗ᵢ ∧ f(t⃗) = bᵢ) ∨ f(t⃗) = d_f
            // with d_f the sort completion default. SOUNDNESS: M′ :=
            // M with pinned heads re-completed to "graph else d_f"
            // satisfies (1) every ground premise — every ground f
            // occurrence IS a collected point carrying M's own value,
            // enforced FAIL-CLOSED: an unevaluable / conflicting /
            // overflowing occurrence, a >point-cap graph, an
            // over-budget walk, or a quantified root drops the WHOLE
            // head (never a single point — dropping a point would let
            // M′ disagree with a ground premise); (2) the constant
            // pins (untouched); (3) every pin under EVERY CE-variable
            // assignment (the disjuncts mirror the two completion
            // cases exactly — the pin is weaker than the completion,
            // which only makes refutation harder, never unsound). So
            // per-group UNSAT of G0 ∧ M_def ∧ pins ∧ ¬B(c⃗) proves
            // M′ ⊨ ∀x⃗.B — the flip's SAT is witnessed by M′. Skolem
            // heads are NEVER pinned, so an alternation lemma
            // ¬psi0(sk(c),c) stays unrefutable here and RED S3 keeps
            // its UNSAT route.
            const MAX_UF_GRAPH_HEADS: usize = 4;
            const MAX_UF_GRAPH_POINTS: usize = 8;
            const UF_GRAPH_WALK_BUDGET: usize = 20_000;
            let mut heads: Vec<ay_frontend::CheckedProjectionBinding> = Vec::new();
            let mut rejected_heads: DetHashSet<ay_core::Symbol> = DetHashSet::default();
            for &app in &uf_app_candidates {
                let TermData::App(sym, args) = self.ctx.terms.get(app) else {
                    continue;
                };
                if rejected_heads.contains(sym) {
                    continue;
                }
                let request = ay_frontend::ProjectionBindingRequest {
                    symbol: sym.clone(),
                    parameter_sorts: args
                        .iter()
                        .map(|&arg| self.ctx.terms.sort(arg).clone())
                        .collect(),
                    result_sort: self.ctx.terms.sort(app).clone(),
                };
                match self.ctx.check_projection_declaration(&request) {
                    Ok(checked) => {
                        if let Some(existing) =
                            heads.iter().find(|head| head.symbol() == checked.symbol())
                        {
                            if existing.parameter_sorts() != checked.parameter_sorts()
                                || existing.result_sort() != checked.result_sort()
                                || existing.declaration_id() != checked.declaration_id()
                            {
                                let symbol = checked.symbol().clone();
                                heads.retain(|head| head.symbol() != &symbol);
                                rejected_heads.insert(symbol);
                            }
                        } else if heads.len() >= MAX_UF_GRAPH_HEADS {
                            heads.clear(); // over cap: drop ALL (fail closed)
                            break;
                        } else {
                            heads.push(checked);
                        }
                    }
                    Err(_) => {
                        // An interpreted, defined, internal, overloaded, stale,
                        // or signature-mismatched application is never a free
                        // model component. If the same exact core Symbol had a
                        // valid-looking occurrence earlier, reject that whole
                        // head rather than accepting partial occurrence coverage.
                        heads.retain(|head| head.symbol() != sym);
                        rejected_heads.insert(sym.clone());
                    }
                }
            }
            if !heads.is_empty() {
                // The set M′ must keep satisfying the authenticated
                // snapshot ground core. The live assertion set is
                // intentionally excluded: CE-directed rewrites can
                // both delete authored constraints and create residues
                // that are valid only under the CE hypothesis.
                let roots = ground_core.clone();
                type Graph = Vec<(Vec<EvalValue>, EvalValue)>;
                let mut head_points: Vec<(ay_frontend::CheckedProjectionBinding, Option<Graph>)> =
                    heads
                        .into_iter()
                        .map(|head| (head, Some(Vec::new())))
                        .collect();
                // A value is pinnable iff we can rebuild it as a term
                // (mirrors the constant-pin acceptance above).
                let pinnable = |this: &Self, term: TermId, v: &EvalValue| -> bool {
                    match (this.ctx.terms.sort(term), v) {
                        (ay_core::Sort::Bool, EvalValue::Bool(_)) => true,
                        (ay_core::Sort::Int, EvalValue::Rational(r)) => r.is_integer(),
                        (ay_core::Sort::Real, EvalValue::Rational(_)) => true,
                        (ay_core::Sort::BitVec(sort), EvalValue::BitVec { width, .. }) => {
                            sort.width == *width
                        }
                        _ => false,
                    }
                };
                let mut walk_seen: DetHashSet<TermId> = DetHashSet::default();
                let mut stack = roots;
                let mut budget = UF_GRAPH_WALK_BUDGET;
                while let Some(t) = stack.pop() {
                    if !walk_seen.insert(t) {
                        continue;
                    }
                    if budget == 0 {
                        for hp in &mut head_points {
                            hp.1 = None;
                        }
                        break;
                    }
                    budget -= 1;
                    match self.ctx.terms.get(t).clone() {
                        TermData::App(sym, args) => {
                            if let Some(hp) = head_points
                                .iter_mut()
                                .find(|(head, _)| head.symbol() == &sym)
                            {
                                if let Some(points) = hp.1.as_mut() {
                                    let signature_matches = args.len()
                                        == hp.0.parameter_sorts().len()
                                        && self.ctx.terms.sort(t) == hp.0.result_sort()
                                        && args.iter().zip(hp.0.parameter_sorts()).all(
                                            |(&arg, expected)| self.ctx.terms.sort(arg) == expected,
                                        );
                                    if !signature_matches {
                                        hp.1 = None;
                                        stack.extend(args.iter().copied());
                                        continue;
                                    }
                                    let mut avals: Vec<EvalValue> = Vec::with_capacity(args.len());
                                    let mut ok = true;
                                    for &a in &args {
                                        let av = self.evaluate_term(&model, a);
                                        if !pinnable(self, a, &av) {
                                            ok = false;
                                            break;
                                        }
                                        avals.push(av);
                                    }
                                    let rv = self.evaluate_term(&model, t);
                                    if !ok || !pinnable(self, t, &rv) {
                                        hp.1 = None;
                                    } else if let Some((_, prev)) =
                                        points.iter().find(|(pa, _)| *pa == avals)
                                    {
                                        if *prev != rv {
                                            // Same point, two values:
                                            // extraction inconsistency —
                                            // drop the head.
                                            hp.1 = None;
                                        }
                                    } else if points.len() >= MAX_UF_GRAPH_POINTS {
                                        hp.1 = None;
                                    } else {
                                        points.push((avals, rv));
                                    }
                                }
                            }
                            stack.extend(args.iter().copied());
                        }
                        TermData::Not(i) => stack.push(i),
                        TermData::Ite(c, a, b) => {
                            stack.push(c);
                            stack.push(a);
                            stack.push(b);
                        }
                        TermData::Let(binds, body) => {
                            for (_, v) in binds {
                                stack.push(v);
                            }
                            stack.push(body);
                        }
                        // A quantified root hides f occurrences M′
                        // must honor but we cannot enumerate: drop
                        // every head.
                        TermData::Forall(..) | TermData::Exists(..) => {
                            for hp in &mut head_points {
                                hp.1 = None;
                            }
                            break;
                        }
                        _ => {}
                    }
                }
                let mut used_completion_heads: DetHashSet<ay_core::Symbol> = DetHashSet::default();
                for &app in &uf_app_candidates {
                    let TermData::App(sym, args) = self.ctx.terms.get(app).clone() else {
                        continue;
                    };
                    let Some((binding, Some(points))) =
                        head_points.iter().find(|(head, _)| head.symbol() == &sym)
                    else {
                        continue;
                    };
                    if args.len() != binding.parameter_sorts().len()
                        || self.ctx.terms.sort(app) != binding.result_sort()
                        || args
                            .iter()
                            .zip(binding.parameter_sorts())
                            .any(|(&arg, expected)| self.ctx.terms.sort(arg) != expected)
                    {
                        continue;
                    }
                    let points = points.clone();
                    let app_sort = self.ctx.terms.sort(app).clone();
                    let Some(dflt) = self.unconstrained_default_value(&app_sort) else {
                        continue;
                    };
                    let Some(d_term) =
                        pin_eval_const_for_sort(&mut self.ctx.terms, &app_sort, &dflt)
                    else {
                        continue;
                    };
                    let mut disjuncts: Vec<TermId> = Vec::new();
                    let mut ok = true;
                    for (avals, rv) in &points {
                        let mut conj: Vec<TermId> = Vec::new();
                        for (&arg, av) in args.iter().zip(avals) {
                            let arg_sort = self.ctx.terms.sort(arg).clone();
                            let Some(a_term) =
                                pin_eval_const_for_sort(&mut self.ctx.terms, &arg_sort, av)
                            else {
                                ok = false;
                                break;
                            };
                            let eq = self.ctx.terms.mk_eq(arg, a_term);
                            conj.push(eq);
                        }
                        if !ok {
                            break;
                        }
                        let Some(r_term) =
                            pin_eval_const_for_sort(&mut self.ctx.terms, &app_sort, rv)
                        else {
                            ok = false;
                            break;
                        };
                        let eq = self.ctx.terms.mk_eq(app, r_term);
                        conj.push(eq);
                        disjuncts.push(self.ctx.terms.mk_and(conj));
                    }
                    if !ok {
                        // Never emit a pin missing a graph disjunct —
                        // the premise could be false in M′.
                        continue;
                    }
                    let d_eq = self.ctx.terms.mk_eq(app, d_term);
                    disjuncts.push(d_eq);
                    uf_pins.push(self.ctx.terms.mk_or(disjuncts));
                    used_completion_heads.insert(sym);
                }
                if !used_completion_heads.is_empty() {
                    let mut completed_model = model.clone();
                    let mut completed_bindings = Vec::with_capacity(used_completion_heads.len());
                    let mut installable = true;
                    for (binding, points) in head_points {
                        if !used_completion_heads.contains(binding.symbol()) {
                            continue;
                        }
                        let Some(points) = points else {
                            installable = false;
                            break;
                        };
                        let result_sort = binding.result_sort().clone();
                        let Some(default) = self.unconstrained_default_value(&result_sort) else {
                            installable = false;
                            break;
                        };
                        if completed_model
                            .install_certified_total_uf(
                                binding.symbol().name().to_string(),
                                binding.parameter_sorts().to_vec(),
                                result_sort,
                                points,
                                default,
                            )
                            .is_none()
                        {
                            installable = false;
                            break;
                        }
                        completed_bindings.push(binding);
                    }
                    let covers_used_heads = completed_bindings.len() == used_completion_heads.len();
                    let bindings_current = completed_bindings
                        .iter()
                        .all(|binding| self.ctx.projection_binding_still_current(binding));
                    let ground_core_satisfied = installable
                        && covers_used_heads
                        && bindings_current
                        && ground_core.iter().all(|&root| {
                            matches!(
                                self.evaluate_term(&completed_model, root),
                                EvalValue::Bool(true)
                            )
                        });
                    if ground_core_satisfied
                        && self.complete_quantified_output_model_before_seal(
                            &mut completed_model,
                            snapshot,
                        )
                    {
                        let model_epoch = completed_model.seal_cegqi_uf_recompletion();
                        uf_recompletion = Some(CegqiUfRecompletion {
                            bindings: completed_bindings.into_boxed_slice(),
                            model: Box::new(completed_model),
                            model_epoch,
                            // Filled after the staged vacuity guard below tells
                            // us whether M_def actually participated in the
                            // theorem. Carrying unused pins would be safe but
                            // would revoke authority unnecessarily.
                            model_definition: Box::default(),
                        });
                    } else {
                        // Pins without an installable exact M′ may still be a
                        // theorem about existence, but they are not model
                        // publication authority. Drop the entire UF pin lane.
                        uf_pins.clear();
                    }
                }
            }
        }
        // Shared tight deadline (same discipline as
        // `refuted_all_quantified_ce_lemmas`): the refutations are a
        // pure certificate — running out of budget leaves lemmas
        // unrefuted and falls through to the recovery legs / honest
        // Unknown, never a wrong verdict.
        let saved_deadline = self.solve_deadline.get();
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
        self.set_deadline(match saved_deadline {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        });
        // Refute PER UNIVERSAL (#cegqi-per-universal, 2026-07-11):
        // `ce_lemma_ids` holds the AND-FLATTENED conjuncts of every
        // CE lemma (see `flatten_and_strip_quantifiers`), so solving
        // them one-by-one demanded each CONJUNCT be unsatisfiable —
        // `¬(c>4)` from `¬((c>4) ∨ p)` never is, and the flip died on
        // shapes whose refutation lives in the OTHER conjunct(s)
        // (assert-p family). The sound unit is each universal's WHOLE
        // conjunction `¬B_q(c⃗)`: UNSAT of `G0 ∧ ¬B_q(c⃗)` with c⃗
        // fresh w.r.t. G0 proves `G0 ⊨ ∀x⃗.B_q` (fresh-constant
        // rule), and every group is solved SEPARATELY, so conjuncts
        // of two coupled universals can never refute each other (the
        // multi-lemma disjunction hole stays closed). A group that
        // lost all its conjuncts to the CE-exclusive filter has its
        // constraints in the ground core already — nothing left to
        // refute, no certificate. Fail closed when the groups are
        // missing entirely.
        // STAGED vacuity guard for the pins: usable only when
        // consistent with the ground core (all are true of the
        // candidate model, so a genuine model always passes). If the
        // joint set fails, retry WITHOUT the UF-graph pins so a flaky
        // graph can never disable the already-validated constant
        // pins; with uf_pins empty the path is identical to v1.
        let mut pins_usable = !m_def.is_empty();
        let mut uf_pins_usable = !uf_pins.is_empty();
        if pins_usable || uf_pins_usable {
            let mut ctx0 = ground_core.clone();
            ctx0.extend(m_def.iter().copied());
            ctx0.extend(uf_pins.iter().copied());
            let joint_ok = match self.checked_ground_solve(ctx0.clone(), category, 2_000) {
                Some(CheckedGroundDecision::Sat(checked)) => checked.consume(self, &ctx0),
                _ => false,
            };
            if !joint_ok {
                uf_pins_usable = false;
                if pins_usable {
                    let mut ctx0 = ground_core.clone();
                    ctx0.extend(m_def.iter().copied());
                    pins_usable = match self.checked_ground_solve(ctx0.clone(), category, 2_000) {
                        Some(CheckedGroundDecision::Sat(checked)) => checked.consume(self, &ctx0),
                        _ => false,
                    };
                }
            }
        }
        let mut all_ce_lemmas_refuted = !ce_lemma_groups.is_empty();
        for (quant, group) in ce_lemma_groups {
            if !matches!(self.ctx.terms.get(*quant), TermData::Forall(..)) {
                // Defensive: an exists group cannot be certified by
                // refutation — no flip.
                all_ce_lemmas_refuted = false;
                break;
            }
            if group.is_empty() || ay_core::time::Instant::now() >= tight {
                if ay_core::misc_cli_flags().trace_cegqi_attr {
                    eprintln!(
                        "[cegqi-attr] SAT model-group verifier DECLINE: quant={quant:?} group_terms={} deadline_expired={}",
                        group.len(),
                        ay_core::time::Instant::now() >= tight,
                    );
                }
                all_ce_lemmas_refuted = false;
                break;
            }
            let mut lemma_ctx = ground_core.clone();
            if pins_usable {
                lemma_ctx.extend(m_def.iter().copied());
            }
            if uf_pins_usable {
                lemma_ctx.extend(uf_pins.iter().copied());
            }
            lemma_ctx.extend(group.iter().copied());
            let lemma_result = match self.checked_ground_solve(lemma_ctx.clone(), category, 2_000) {
                Some(CheckedGroundDecision::Unsat(checked)) => checked
                    .consume(self, &lemma_ctx)
                    .then_some(CheckedGroundKind::Unsat),
                Some(CheckedGroundDecision::Sat(checked)) => checked
                    .consume(self, &lemma_ctx)
                    .then_some(CheckedGroundKind::Sat),
                _ => None,
            };
            if ay_core::misc_cli_flags().trace_cegqi_attr {
                eprintln!(
                    "[cegqi-attr] SAT model-group refutation: quant={quant:?} group_terms={} pins={} uf_pins={} result={lemma_result:?}",
                    group.len(),
                    if pins_usable { m_def.len() } else { 0 },
                    if uf_pins_usable { uf_pins.len() } else { 0 },
                );
            }
            if !matches!(lemma_result, Some(CheckedGroundKind::Unsat)) {
                all_ce_lemmas_refuted = false;
                break;
            }
        }
        self.set_deadline(saved_deadline);
        if ay_core::misc_cli_flags().trace_cegqi_attr {
            eprintln!(
                "[cegqi-attr] SAT model-group verifier result: all_refuted={all_ce_lemmas_refuted} uf_pins_usable={uf_pins_usable} stopped={}",
                self.should_abort_theory_loop(),
            );
        }
        if !all_ce_lemmas_refuted || self.should_abort_theory_loop() {
            None
        } else if uf_pins_usable {
            let mut completion = uf_recompletion?;
            if pins_usable {
                completion.model_definition = m_def.into_boxed_slice();
            }
            Some(CegqiGroupRefutation::UfRecompletion(completion))
        } else {
            Some(CegqiGroupRefutation::RetainedGroundModel)
        }
    }

    /// SAT-leg flip of the quantified-CE-lemma decider (#quantified-ce-lemma),
    /// for the `classify_quantifier_result` refinement-Unknown/None hooks.
    ///
    /// # Certificate
    ///
    /// Fires only when [`Self::refuted_all_quantified_ce_lemmas`] establishes
    /// that EVERY CEGQI universal's de-Skolemized counterexample obligation is
    /// UNSAT — i.e. every original `forall x⃗ (exists y⃗ psi0)` assertion is
    /// VALID (true in every theory model, independent of any other assertion) —
    /// and its coverage gate establishes that those universals are the ONLY
    /// quantified assertions in the snapshot. The snapshot ground remainder is
    /// reconstructed and solved independently;
    /// no model of the mutable live CE assertion set is accepted as that
    /// premise. Valid universals + the authenticated satisfiable ground
    /// remainder imply the original problem is SAT.
    ///
    /// # Safety nets (mirror of the disambiguation `Ok(Sat)` consumer)
    ///
    /// The callers run the MBQI cross-validation
    /// (`disambiguate_cegqi_valid_via_mbqi_ext`) BEFORE this flip and return
    /// its UNSAT if it refutes; this method re-checks the
    /// witness-independent-skolem-alternation net and fails closed (`None`) on
    /// that shape. On success it performs the documented CEGQI-valid-verdict
    /// bookkeeping (`defer_model_validation = false`,
    /// `last_model_validated = true`): the verdict is semantically validated by
    /// the refutation certificates (the ground model witnesses the remainder;
    /// no ground model can witness a `forall`), exactly like the pre-existing
    /// CE-conjunction flip.
    fn try_quantified_ce_valid_flip(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        let ground_witness = cegqi_sat_authority::install(self, snapshot, category)?;
        if self.snapshot_has_witness_independent_skolem_alternation(snapshot) {
            drop(ground_witness);
            self.clear_cegqi_inner_unsat_artifacts();
            return None;
        }
        match cegqi_sat_authority::certify_quantified_ce_refutations(
            self,
            ground_witness,
            cegqi_state,
            snapshot,
            category,
        ) {
            Ok(checked) => Some(checked.publish(self)),
            Err(ground_witness) => {
                drop(ground_witness);
                self.clear_cegqi_inner_unsat_artifacts();
                None
            }
        }
    }

    /// SAT leg of the quantified-CE-lemma decider (#quantified-ce-lemma):
    /// return `true` iff EVERY CEGQI universal's DE-SKOLEMIZED counterexample
    /// obligation `L_q = forall y⃗. ¬psi0(y⃗, e⃗)` is individually refuted by a
    /// bounded, ISOLATED ground instantiation, and the coverage gates hold.
    ///
    /// # Soundness (SAT direction)
    ///
    /// For each universal `quant = forall x⃗. B(x⃗)` (the post-Skolemization
    /// form of an original `forall x⃗ exists y⃗. psi0(y⃗, x⃗)`),
    /// [`rebuild_quantified_ce_lemma`] reconstructs `L_q` exactly (fail-closed
    /// `None` on anything outside the v1 fragment). By universal instantiation
    /// `L_q ⊨ rho(t⃗)` for ANY terms `t⃗`, so a standalone ground solve proving
    /// some `rho(t⃗)` UNSAT proves `L_q` UNSAT. `L_q` UNSAT means
    /// `exists y⃗. psi0(y⃗, e⃗)` is VALID with `e⃗` fresh free constants —
    /// i.e. the ORIGINAL assertion `forall x⃗ exists y⃗. psi0` is valid in
    /// every theory model, which is exactly the CEGQI premise ("the CE lemma
    /// alone is UNSAT") the joint ground refutation cannot discharge for
    /// skolemized lemmas (the stored `¬psi0(sk(e⃗), e⃗)` keeps `sk` free and is
    /// always satisfiable). Refutation is PER LEMMA — strictly stronger than
    /// the legacy joint-conjunction solve, which is retained byte-identically
    /// for all-ground lemma sets.
    ///
    /// Candidate synthesis is NOT a soundness surface: every candidate is
    /// verified by the isolated ground solve and silently skipped otherwise.
    /// Isolated solves are mandatory: conjoining instances demonstrably sends
    /// the NIA ground solver to unknown where each solo instance is decided.
    ///
    /// # Gates
    ///
    /// - `cegqi_state` must contain at least one universal and NO existential
    ///   (an existential CE obligation is a witness search, not a validity
    ///   check).
    /// - Coverage: every quantifier-bearing assertion in `snapshot` must BE a
    ///   bare top-level `forall` handled by CEGQI (present in `cegqi_state`).
    ///   This makes the validity certificates cover ALL quantified obligations
    ///   (a quantifier nested under `or`/`ite`/`not`, an E-matching-owned
    ///   trigger forall, or an unhandled quantifier fails the gate) so the
    ///   caller's remainder-Sat premise extends to the whole problem.
    /// - Work bounds: ≤ 12 isolated solves per lemma under one shared 300 ms
    ///   deadline for the whole leg (the standard tight-deadline pattern).
    fn refuted_all_quantified_ce_lemmas(
        &mut self,
        cegqi_state: &[(TermId, CegqiInstantiator)],
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_LEMMA_REFUTATION_SOLVES: usize = 12;

        if cegqi_state.is_empty() {
            return false;
        }
        for (_, inst) in cegqi_state {
            if !inst.is_forall() {
                return false;
            }
        }

        // Coverage gate: the certificates below must account for EVERY
        // quantified obligation in the pre-instantiation snapshot.
        let covered: HashSet<TermId> = cegqi_state.iter().map(|(q, _)| *q).collect();
        for &assertion in snapshot {
            if contains_quantifier(&self.ctx.terms, assertion)
                && !(matches!(self.ctx.terms.get(assertion), TermData::Forall(..))
                    && covered.contains(&assertion))
            {
                return false;
            }
        }

        // Shared tight deadline across the whole leg.
        let saved_deadline = self.solve_deadline.get();
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
        self.set_deadline(match saved_deadline {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        });

        let mut all_refuted = true;
        'lemmas: for (quant, inst) in cegqi_state {
            let Some((binders, rho)) =
                rebuild_quantified_ce_lemma(&mut self.ctx.terms, *quant, inst)
            else {
                all_refuted = false;
                break;
            };
            if binders.is_empty() {
                // Ground lemma: the obligation IS the stored CE lemma; refute
                // it directly with one isolated solve.
                let obligation = vec![rho];
                if self
                    .checked_ground_solve(obligation.clone(), category, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    continue;
                }
                all_refuted = false;
                break;
            }
            let tuples = self.quantified_lemma_candidate_tuples(&binders, rho);
            if tuples.is_empty() {
                all_refuted = false;
                break;
            }
            for tuple in tuples.into_iter().take(MAX_LEMMA_REFUTATION_SOLVES) {
                if ay_core::time::Instant::now() >= tight {
                    all_refuted = false;
                    break 'lemmas;
                }
                let subst: HashMap<String, TermId> = binders
                    .iter()
                    .map(|(n, _)| n.clone())
                    .zip(tuple.iter().copied())
                    .collect();
                let instance = crate::ematching::subst_vars(&mut self.ctx.terms, rho, &subst);
                let obligation = vec![instance];
                if self
                    .checked_ground_solve(obligation.clone(), category, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    continue 'lemmas; // this lemma is refuted — next lemma
                }
            }
            all_refuted = false;
            break;
        }

        self.set_deadline(saved_deadline);
        all_refuted
    }

    /// Candidate instantiation tuples for the binders of a rebuilt
    /// counterexample obligation `L_q = forall y⃗. rho`. Reuses the existing
    /// binder-base synthesizers (free Int variables — which now surface the CE
    /// variables `e⃗` —, binder-independent UF values, atom boundaries, Skolem
    /// witness points, linear combinations) with small offsets, plus a constant
    /// window. Candidates mentioning another binder are dropped so every tuple
    /// substitutes to a formula over the lemma's free symbols only. Not a
    /// soundness surface (each tuple is verified by an isolated solve).
    fn quantified_lemma_candidate_tuples(
        &mut self,
        binders: &[(String, ay_core::Sort)],
        rho: TermId,
    ) -> Vec<Vec<TermId>> {
        const MAX_TUPLES: usize = 12;
        let all_names: ay_core::kani_compat::DetHashSet<String> =
            binders.iter().map(|(n, _)| n.clone()).collect();
        let cap_per_binder = if binders.len() == 1 { MAX_TUPLES } else { 3 };

        let mut per_binder: Vec<Vec<TermId>> = Vec::with_capacity(binders.len());
        for (name, _) in binders {
            let cands =
                self.quantified_lemma_binder_candidates(rho, name, &all_names, cap_per_binder);
            if cands.is_empty() {
                return Vec::new();
            }
            per_binder.push(cands);
        }

        let mut out: Vec<Vec<TermId>> = vec![Vec::new()];
        for cands in &per_binder {
            let mut next: Vec<Vec<TermId>> = Vec::new();
            'outer: for prefix in &out {
                for &c in cands {
                    let mut tuple = prefix.clone();
                    tuple.push(c);
                    next.push(tuple);
                    if next.len() >= MAX_TUPLES {
                        break 'outer;
                    }
                }
            }
            out = next;
        }
        out
    }

    /// Per-binder candidate terms for [`Self::quantified_lemma_candidate_tuples`]:
    /// the five binder-base synthesizers with offsets ±2, then a small constant
    /// window, capped and filtered of candidates that mention any lemma binder.
    fn quantified_lemma_binder_candidates(
        &mut self,
        rho: TermId,
        name: &str,
        all_binder_names: &ay_core::kani_compat::DetHashSet<String>,
        cap: usize,
    ) -> Vec<TermId> {
        const MAX_BASES: usize = 4;
        let mut bases: Vec<TermId> = self.free_int_binder_bases(rho, name);
        for b in self.uf_value_binder_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        for b in self.skolem_app_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        for b in self.atom_boundary_binder_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        for b in self.combination_binder_bases(rho, name) {
            if !bases.contains(&b) {
                bases.push(b);
            }
        }
        bases.retain(|&b| !self.term_mentions_bound_var(b, all_binder_names));
        bases.truncate(MAX_BASES);

        let mut out: Vec<TermId> = Vec::new();
        for &base in &bases {
            for k in [0i64, 1, -1, 2, -2] {
                let cand = if k == 0 {
                    base
                } else {
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    self.ctx.terms.mk_add(vec![base, kterm])
                };
                if !out.contains(&cand) {
                    out.push(cand);
                    if out.len() >= cap {
                        return out;
                    }
                }
            }
        }
        for c in [0i64, 1, -1, 2, -2] {
            let cand = self.ctx.terms.mk_int(num_bigint::BigInt::from(c));
            if !out.contains(&cand) {
                out.push(cand);
                if out.len() >= cap {
                    break;
                }
            }
        }
        out
    }

    /// UNSAT leg of the quantified-CE-lemma decider (#quantified-ce-lemma):
    /// decide the WHOLE problem UNSAT when a conjunctive-position universal is
    /// FALSE at a concrete ground witness.
    ///
    /// # Soundness (UNSAT direction)
    ///
    /// The problem asserts each `q = forall x. B(x)` in
    /// [`Self::forall_ids_in_conjunctive_position`] as a top-level conjunct of
    /// the (post-Skolemization) snapshot, so `problem ⊨ B(c)` for every ground
    /// `c` (universal instantiation; a NON-conjunctive forall does not entail
    /// its instances and is skipped, mirroring the #classA guard). `B(c)` being
    /// UNSAT as a STANDALONE formula means NO interpretation of its free
    /// symbols — including the Skolem terms `sk(c)` left as free ground
    /// applications — satisfies it, hence no model of the problem exists;
    /// Skolemization preserves satisfiability, so the ORIGINAL problem is
    /// UNSAT regardless of any other assertion. A genuinely-SAT problem can
    /// never be flipped: its model satisfies `B(c)` for every `c`, so no
    /// standalone `B(c)` is UNSAT. Candidate synthesis
    /// ([`crate::executor::mbqi::synthesize_int_refutation_candidates`]) is not
    /// a soundness surface — every candidate is verified by the isolated
    /// ground solve, exactly like `unsat_from_direct_instance_clash` step 5.
    ///
    /// # Bounds
    ///
    /// Only single-`Int`-binder, quantifier-free-body universals that apply an
    /// uninterpreted function to the binder (the shapes the arithmetic CE
    /// search is incomplete over); ≤ 12 isolated solves under one shared
    /// 300 ms deadline.
    fn universal_false_at_ground_witness(
        &mut self,
        foralls: &[TermId],
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        const MAX_WITNESS_SOLVES: usize = 12;
        if foralls.is_empty() {
            return None;
        }
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);

        let saved_deadline = self.solve_deadline.get();
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(300);
        self.set_deadline(match saved_deadline {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        });

        let mut budget = MAX_WITNESS_SOLVES;
        let mut outcome: Option<Result<SolveResult>> = None;
        'foralls: for &q in foralls {
            if !conjunctive.contains(&q) {
                continue;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            let [(name, ay_core::Sort::Int)] = vars.as_slice() else {
                continue;
            };
            if contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            // Focus on the alternation/UF shapes the arithmetic CE search is
            // incomplete over (mirrors the eager-instantiation gate of the
            // MBQI validation); pure-arith universals are already decided
            // soundly by CEGQI.
            let bound: ay_core::kani_compat::DetHashSet<String> =
                std::iter::once(name.clone()).collect();
            if !self.term_mentions_uninterpreted_of_bound_var(body, &bound) {
                continue;
            }
            let candidates = crate::executor::mbqi::synthesize_int_refutation_candidates(
                &self.ctx.terms,
                body,
                snapshot,
            );
            for c in candidates {
                if budget == 0 || ay_core::time::Instant::now() >= tight {
                    break 'foralls;
                }
                budget -= 1;
                let cterm = self.ctx.terms.mk_int(c);
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(name.clone(), cterm);
                let instance = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                let obligation = vec![instance];
                if self
                    .checked_ground_solve(obligation.clone(), fallback_category, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    outcome = Some(Ok(SolveResult::unsat()));
                    break 'foralls;
                }
            }
        }

        self.set_deadline(saved_deadline);
        outcome
    }

    /// Decide an exact quantifier-free assertion vector on a disposable
    /// Executor and return only a sealed, outer-scope-bound result.
    ///
    /// The probe enters a fresh public-query epoch and uses the ordinary
    /// `check_sat` pipeline. SAT must therefore carry the private
    /// `SatCertificate` minted by `emit_sat_verdict`; UNSAT is routed through
    /// `certify_unsat_for_publication` and accepted only when its one-shot
    /// certificate is a checked exact-query authority. This includes strict
    /// proof, independently verified, and exact-semantic certificates, while
    /// excluding the competition raw admission. The cloned Context and every
    /// proof/model artifact die with the probe. Only the non-cloneable decision
    /// crosses back, bound to the enclosing query epoch, source stamp, exact
    /// ordered roots, and term-store snapshot.
    pub(in crate::executor) fn checked_ground_solve(
        &mut self,
        assertions: Vec<TermId>,
        _fallback_category: LogicCategory,
        budget_ms: u64,
    ) -> Option<CheckedGroundDecision> {
        let (scope, outcome) = self.checked_isolated_solve(
            assertions,
            CheckedIsolatedMode::GroundDecision,
            budget_ms,
        )?;
        match outcome {
            CheckedGroundKind::Sat => Some(CheckedGroundDecision::Sat(CheckedGroundSat { scope })),
            CheckedGroundKind::Unsat => {
                Some(CheckedGroundDecision::Unsat(CheckedGroundUnsat { scope }))
            }
        }
    }

    /// Certify one exact assertion vector as UNSAT on a disposable public-query
    /// transaction.
    ///
    /// Ground and quantified obligations share this UNSAT-only path.  A raw
    /// nested result is never returned: success requires a checked exact-query
    /// certificate (strict proof, independent verification, or exact semantic
    /// theorem), and the resulting linear token must still match the enclosing
    /// query epoch, source context, ordered roots, and exact term snapshot when
    /// consumed.
    pub(in crate::executor) fn checked_exact_unsat_solve(
        &mut self,
        assertions: Vec<TermId>,
        budget_ms: u64,
    ) -> Option<CheckedExactUnsat> {
        let (scope, outcome) =
            self.checked_isolated_solve(assertions, CheckedIsolatedMode::ExactUnsat, budget_ms)?;
        matches!(outcome, CheckedGroundKind::Unsat).then_some(CheckedExactUnsat { scope })
    }

    /// Ground instances of conjunctive-position `forall`s, for
    /// [`Self::unsat_from_direct_instance_clash`]. Appends to `literals`.
    ///
    /// The budget is spent ROUND-ROBIN across the foralls, not first-come. It
    /// used to be a single shared counter with `break 'forall`, so ONE forall
    /// with a wide cross-product could consume all `MAX_CLASH_INSTANCES` and
    /// every later forall contributed NOTHING. Measured on the verification-consumer ext_eq
    /// push/pop refutation (#7956): `produced=256 hit_cap=true` with the
    /// pointwise ext_eq axiom -- the one carrying the refutation -- never
    /// instantiated at all, while a hand-picked 5-instance set refutes in 0.32s.
    /// Round-robin gives every forall its instances before any forall gets its
    /// hundredth.
    ///
    /// BOOL BINDERS. A `Bool` binder ranges over EXACTLY {true, false}, so
    /// instantiating at both is sound (`forall b. P(b)` |= `P(true)` and
    /// |= `P(false)`) AND complete for that binder (`forall b:Bool. P(b)` is
    /// `P(true) AND P(false)`). Previously a Bool binder skipped the WHOLE
    /// forall, so a mixed `forall (b Bool) (i S). ...` contributed zero
    /// instances and any refutation needing a Bool case was missed. Two
    /// candidates keep the cross-product bounded.
    ///
    /// SELECTION ONLY. Every instance appended is a ground consequence of a
    /// conjunctive-position universal, so a refutation of the collected
    /// conjunction still refutes the original and this cannot turn a correct
    /// verdict wrong: the caller only ever returns `true` (UNSAT) off a genuine
    /// clash and never returns SAT. Reordering which consequences are derived
    /// can add refutations and can, in principle, drop one the old order
    /// happened to reach -- a completeness trade in both directions, never a
    /// soundness one.
    fn instantiate_clash_candidates(
        &mut self,
        foralls: &[TermId],
        ground_by_sort: &ay_core::kani_compat::DetHashMap<ay_core::Sort, Vec<TermId>>,
        literals: &mut Vec<TermId>,
    ) {
        use ay_core::kani_compat::DetHashMap as HashMap;
        use ay_core::Sort;
        // 3. Instantiate each conjunctive forall at the bounded cross-product of
        //    ground candidates. Each instance is a sound consequence.
        //
        const MAX_CLASH_INSTANCES: usize = 256;

        // Plan each forall first, under an immutable borrow, so instance
        // construction below can borrow `terms` mutably.
        struct ClashPlan {
            var_names: Vec<String>,
            body: TermId,
            candidates_per_var: Vec<Vec<TermId>>,
            indices: Vec<usize>,
            exhausted: bool,
        }
        let mut plans: Vec<ClashPlan> = Vec::new();
        'forall: for &q in foralls {
            let (vars, body) = match self.ctx.terms.get(q) {
                TermData::Forall(v, b, _) => (v.clone(), *b),
                _ => continue,
            };
            if vars.is_empty() {
                continue;
            }
            let mut candidates_per_var: Vec<Vec<TermId>> = Vec::with_capacity(vars.len());
            for (_n, sort) in &vars {
                let cands = if matches!(sort, Sort::Bool) {
                    // A Bool binder ranges over EXACTLY {true, false}; see the
                    // BOOL BINDERS note on this function.
                    vec![self.ctx.terms.true_term(), self.ctx.terms.false_term()]
                } else {
                    let cands = ground_by_sort.get(sort).cloned().unwrap_or_default();
                    if cands.is_empty() {
                        continue 'forall;
                    }
                    cands
                };
                candidates_per_var.push(cands);
            }
            plans.push(ClashPlan {
                var_names: vars.iter().map(|(n, _)| n.clone()).collect(),
                body,
                indices: vec![0usize; candidates_per_var.len()],
                candidates_per_var,
                exhausted: false,
            });
        }

        let mut produced = 0usize;
        while produced < MAX_CLASH_INSTANCES && plans.iter().any(|p| !p.exhausted) {
            for plan in &mut plans {
                if produced >= MAX_CLASH_INSTANCES {
                    break;
                }
                if plan.exhausted {
                    continue;
                }
                let subst_map: HashMap<String, TermId> = plan
                    .var_names
                    .iter()
                    .enumerate()
                    .map(|(var_idx, name)| {
                        (
                            name.clone(),
                            plan.candidates_per_var[var_idx][plan.indices[var_idx]],
                        )
                    })
                    .collect();
                let inst = crate::ematching::subst_vars(&mut self.ctx.terms, plan.body, &subst_map);
                if !literals.contains(&inst) {
                    literals.push(inst);
                }
                produced += 1;
                // Advance this plan's own odometer.
                let mut carry = true;
                for i in (0..plan.candidates_per_var.len()).rev() {
                    if carry {
                        plan.indices[i] += 1;
                        if plan.indices[i] < plan.candidates_per_var[i].len() {
                            carry = false;
                        } else {
                            plan.indices[i] = 0;
                        }
                    }
                }
                if carry {
                    plan.exhausted = true;
                }
            }
        }
    }
    /// SOUND UNSAT independence check (#mbqi-completeness Q1).
    ///
    /// Reconstructs a theory-INDEPENDENT UNSAT derivation directly from the
    /// pre-instantiation `snapshot` and returns `true` iff one exists. It does
    /// NOT trust the theory solver's UNSAT (which can be a latent theory
    /// incompleteness / wrong-UNSAT - e.g. the array solver collapsing a
    /// satisfiable (forall i. a[i]=b[i]) and a[0]=b[0] to `false`). Instead it:
    ///
    ///   1. Collects the quantifier-free top-level CONJUNCTS of `snapshot` (the
    ///      ground core literals).
    ///   2. Collects the top-level conjunctive-position `forall`s.
    ///   3. Instantiates each `forall` body at every tuple of ground terms (by
    ///      bound-var sort) drawn from the snapshot - bounded by a small budget.
    ///      Each instance is a SOUND logical consequence of the universal
    ///      (instantiation is universally valid).
    ///   4. Checks the (ground literals union instance literals) set for a DIRECT
    ///      complementary pair: a literal `X` and its negation (`(not X)`, or the
    ///      `=` / `distinct` complement of an equality).
    ///   5. (#mbqi-completeness Q2) If no syntactic pair is found, re-solves the
    ///      GROUND conjunction of those same literals as a pure quantifier-free
    ///      problem and returns `true` iff it is definitively UNSAT.
    ///
    /// SOUNDNESS: a literal together with its complement (step 4) is a
    /// contradiction in PURE PROPOSITIONAL / EQUALITY logic, valid under EVERY
    /// interpretation - including the array/FP/Seq one the binder ranges over -
    /// and derived from sound instantiation only. Q1
    /// ((forall i. a[i]=b[i]) and not(a[0]=b[0])) instantiates at i:=0 to
    /// (= a[0] b[0]), which clashes with the ground (not (= a[0] b[0])) => `true`.
    /// Equalities are hash-consed, so an instance and the matching negated ground
    /// literal share the same inner `TermId`.
    ///
    /// Step 5 extends this to refutations the syntactic check cannot see: a ground
    /// DISJUNCTION (the finite-domain-expanded / skolemized negated goal
    /// `(or (< a[0] 0) (< a[1] 0) (< a[2] 0))`) that closes only after case-split
    /// against several instances, or a pair complementary only under LIA/EUF
    /// (`(< a[0] 0)` vs the instance `(<= 0 a[0])`) rather than as a syntactic
    /// `Not`-pair - both ubiquitous for array/seq FRAME quantifiers. It is SOUND:
    /// every element of `literals` is either a genuine quantifier-free CONJUNCT of
    /// the original problem or a sound universal INSTANCE (`forall v. body ⊨
    /// body[v:=t]`), so their ground conjunction is ENTAILED by the original
    /// assertions; if it is UNSAT the original is UNSAT. It can NEVER manufacture a
    /// wrong UNSAT - it adds only sound consequences to the real quantifier-free
    /// core and never rides CEGQI's possibly-unsound valid->SAT flip - and it
    /// leaves the conservative Unknown whenever the ground re-solve is not
    /// definitively UNSAT (e.g. array-extensionality (forall i. a[i]=b[i]) ∧ a≠b
    /// with no index terms yields no instances => ground re-solve SAT => not
    /// certified). The caller restricts this whole method to snapshots whose every
    /// `forall` is a CONJUNCTIVE-position universal, so conjoining their instances
    /// is sound (a non-conjunctive forall's instances must never be conjoined).
    /// # OUTCOMES: three, not two
    ///
    /// The closing ground probe can answer `Unsat`, `Sat`, or decline (`None` --
    /// Unknown, budget exhausted, or a mode refusal at
    /// `checked_isolated_solve.rs`'s `SolveResult::Unknown => None`). `Sat` and
    /// `None` are BEHAVIOURALLY identical here: neither may claim UNSAT, and
    /// failing closed on both is the whole contract of this lane. They are
    /// EPISTEMICALLY opposite, and the `is_some_and` this replaced erased that
    /// difference.
    ///
    /// The erasure had a real cost. Reading only the boolean, an inconclusive
    /// probe is indistinguishable from "the collected instances were
    /// satisfiable" -- and a prior investigation of this lane drew exactly that
    /// wrong conclusion. On the verification-consumer ext_eq shape the lane looks like it
    /// found the instances satisfiable when the probe is in fact returning
    /// Unknown at its 2000ms budget, which points at a completely different
    /// fix. Matching all three explicitly costs nothing at runtime and keeps
    /// the next diagnosis honest.
    fn unsat_from_direct_instance_clash(
        &mut self,
        snapshot: &[TermId],
        fallback_category: LogicCategory,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        // 1. Ground (quantifier-free) literals + conjunctive-position foralls.
        let mut literals: Vec<TermId> = Vec::new();
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);
        let mut foralls: Vec<TermId> = Vec::new();
        for &assertion in snapshot {
            let mut conjuncts = vec![assertion];
            collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
            for c in conjuncts {
                if contains_quantifier(&self.ctx.terms, c) {
                    if matches!(self.ctx.terms.get(c), TermData::Forall(..))
                        && conjunctive.contains(&c)
                        && !foralls.contains(&c)
                    {
                        foralls.push(c);
                    }
                } else if !literals.contains(&c) {
                    literals.push(c);
                }
            }
        }
        // 1b. Conjunctive-position foralls the AND-descent could not REACH.
        //
        // `collect_and_conjuncts` above descends only `and`, and `mk_implies`
        // rewrites `(=> p X)` to `(or (not p) X)` at construction. So a forall
        // that is conjunctive only MODULO a top-level unit fact is never offered
        // to the `conjunctive.contains(..)` test below and is silently dropped.
        // That is exactly the verification-consumer ext_eq shape (#7956): `(assert ext_eq_0)`
        // beside `(assert (=> ext_eq_0 (forall ((ext_eq_i Int)) ...)))`, where the
        // dropped axiom is the one carrying the entire refutation -- measured
        // `foralls=4` against `conjunctive_set=5`.
        //
        // `forall_ids_in_conjunctive_position` ALREADY decides this correctly: its
        // `#unit-conjunctive` rule takes the position test modulo top-level unit
        // facts, and names this very shape. The set was computed and then only
        // ever used as a FILTER on what the syntactic descent happened to find.
        // Using it as a SOURCE as well changes no judgement about what is
        // conjunctive -- every forall added here is one that predicate already
        // certified -- it just stops discarding the ones the descent cannot see.
        for &q in conjunctive.iter() {
            if !foralls.contains(&q) {
                foralls.push(q);
            }
        }

        if foralls.is_empty() {
            return false;
        }

        // 2. Ground terms by sort, for instantiation candidates.
        let ground_by_sort =
            crate::ematching::collect_ground_terms_by_sort(&self.ctx.terms, snapshot);

        // 3. Instantiate each conjunctive forall at the bounded cross-product of
        //    ground candidates. Each instance is a sound consequence.
        self.instantiate_clash_candidates(&foralls, &ground_by_sort, &mut literals);

        // 4. Direct complementary-pair check (pure propositional/equality).
        let false_term = self.ctx.terms.false_term();
        let true_term = self.ctx.terms.true_term();
        let mut positives: HashSet<TermId> = HashSet::default();
        let mut negatives: HashSet<TermId> = HashSet::default();
        for &lit in &literals {
            if lit == false_term {
                // A literal that IS the constant `false` (a ground conjunct or an
                // instance that simplified to false) is an unconditional, sound
                // contradiction.
                return true;
            }
            if lit == true_term {
                continue;
            }
            let (is_neg, inner) = match self.ctx.terms.get(lit) {
                TermData::Not(inner) => (true, *inner),
                TermData::App(sym, args) if sym.name() == "distinct" && args.len() == 2 => {
                    match self.ctx.terms.find_eq(args[0], args[1]) {
                        Some(eq) => (true, eq),
                        None => (false, lit),
                    }
                }
                _ => (false, lit),
            };
            if is_neg {
                if positives.contains(&inner) {
                    return true;
                }
                negatives.insert(inner);
            } else {
                if negatives.contains(&inner) {
                    return true;
                }
                positives.insert(inner);
            }
        }

        // 5. Sound ground re-solve certification (#mbqi-completeness Q2). The
        //    syntactic pair check misses refutations that need the theory/BCP
        //    solver to case-split a ground disjunction against several instances
        //    or to close a LIA/EUF-complementary pair. `literals` (ground
        //    conjuncts + sound conjunctive-forall instances) is entailed by the
        //    original assertions, so re-solving its ground conjunction certifies
        //    the reported UNSAT without trusting CEGQI's valid->SAT flip. All
        //    instances are quantifier-free by construction; bail if a nested
        //    quantifier in a forall body leaked one through, keeping this a pure
        //    ground solve.
        if literals.is_empty()
            || literals
                .iter()
                .any(|&l| contains_quantifier(&self.ctx.terms, l))
        {
            return false;
        }
        // Three outcomes, not two; see the OUTCOMES note on this function.
        let probe = self.checked_ground_solve(literals.clone(), fallback_category, 2_000);
        let declined = match probe {
            Some(CheckedGroundDecision::Unsat(checked)) => return checked.consume(self, &literals),
            Some(CheckedGroundDecision::Sat(_)) => "SATISFIABLE (conclusive)",
            None => "INCONCLUSIVE (Unknown/budget), NOT a satisfiability finding",
        };
        if ay_core::misc_cli_flags().trace_cegqi_attr {
            ay_core::safe_eprintln!(
                "c cegqi-attr clash-lane DECLINED over {} instance(s): {declined}",
                literals.len()
            );
        }
        false
    }

    /// Validate a CEGQI "forall valid ⟹ SAT" verdict with model-based quantifier
    /// instantiation (MBQI) and DECIDE UNSAT when the universal is actually
    /// violated by the candidate model.
    ///
    /// `disambiguate_cegqi_unsat` leaves the ground-only candidate model in
    /// `last_model`. We rebuild the quantifier-free ground core from `snapshot`,
    /// then run `try_mbqi_refinement` over the snapshot's `forall`s: it
    /// instantiates each at ground/synthesized candidates, evaluates under the
    /// candidate model, and re-solves the falsifying instances. If that drives
    /// the problem UNSAT, the universal is genuinely false (e.g. the alternation
    /// cases whose infeasibility comes from the COMBINATION of skolem-constrained
    /// conjuncts, which no syntactic guard can detect), so we decide UNSAT —
    /// matching z3 — instead of trusting the unvalidated certificate. Returns
    /// `Some(Ok(unsat))` only on a definitive MBQI refutation; otherwise restores
    /// state and returns `None` (caller keeps the SAT / fail-closed path). MBQI
    /// is model-targeted (a few candidates per round), not a blind enumeration.
    // Non-aggressive entry point of the `_ext` API pair; live callers currently use
    // the `aggressive=true` form, but this default-mode wrapper is retained for the
    // non-alternation CEGQI/uf-completion validation paths it documents.
    #[allow(dead_code)]
    fn disambiguate_cegqi_valid_via_mbqi(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        self.disambiguate_cegqi_valid_via_mbqi_ext(snapshot, category, false)
    }

    /// `aggressive` enables the relaxation-based extra refutation paths
    /// (multi-Skolem FM projection, binder-dependent UF over-approximation). They
    /// run additional `(forall ...)` sub-solves, so they are gated to the bare
    /// ALTERNATION arm: the uf-completion / CEGQI-disambiguation callers validate
    /// genuine-SAT library completions where those extra sub-solves would only burn
    /// time and perturb the SAT model-building state. The base validation (bounded
    /// instantiation + single-Skolem projection + Skolem over-approximation) runs
    /// in both modes and is unchanged from the pre-existing behaviour.
    fn disambiguate_cegqi_valid_via_mbqi_ext(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
        aggressive: bool,
    ) -> Option<Result<SolveResult>> {
        // Re-entrancy guard: the over-approximation step below issues its own
        // `(forall ...)` solve, which must not recurse back into this validation.
        if self.in_alternation_validation {
            return None;
        }
        // The validation's nested `(forall ...)` sub-solves re-enter the quantifier
        // pipeline and mutate the verdict-bookkeeping state (`defer_model_validation`
        // / model / validated / unknown-reason). Only an UNSAT outcome is consumed by
        // callers; for ANY other outcome this validation made no decision, so snapshot
        // that state and restore it fully. Otherwise a non-refuting validation run on
        // a genuine-SAT problem leaves `defer_model_validation` perturbed and the
        // caller's later SAT model build is skipped (panics the SAT/model postcondition
        // on library-completion problems that reach here).
        let saved_defer = self.defer_model_validation;
        let saved_validated = self.last_model_validated;
        let saved_reason = self.last_unknown_reason;
        // Move the sealed predecessor out of reach of the nested solve. The
        // disposable validation reads an authority-free semantic clone; only a
        // non-decision moves the exact predecessor and its grants back.
        let saved_model = self.last_model.take();
        self.last_model = saved_model.clone();
        // Nested validation solves may independently reach SAT-certificate
        // routes for their projected one-forall obligation. Those grants are
        // authoritative only for the disposable subproblem and must never
        // survive into the outer mapper. Preserve every certificate-side
        // artifact as one lifecycle unit alongside the model state above.
        let saved_dt_cert_grant = std::mem::replace(&mut self.dt_cert_grant_active, false);
        let saved_dt_cert_query_grant = self.dt_cert_query_grant.take();
        let saved_finite_table_cert_grant =
            std::mem::replace(&mut self.finite_table_cert_grant_active, false);
        let saved_finite_table_witness = self.finite_table_cert_witness_state.take();
        let saved_const_interp_cert_grant =
            std::mem::replace(&mut self.const_interp_cert_grant_active, false);
        let saved_const_interp_witness = self.const_interp_cert_witness_state.take();
        let saved_cegqi_uf_recompletion_grant = self.cegqi_uf_recompletion_grant.take();
        let saved_mbqi_sat_cert_grant =
            std::mem::replace(&mut self.mbqi_sat_cert_grant_active, false);
        let saved_mbqi_sat_cert_query_grant = self.mbqi_sat_cert_query_grant.take();
        let saved_bv_full_domain_proof =
            std::mem::replace(&mut self.bv_quantifier_full_domain_proof, false);
        let saved_bv_full_domain_pending_evidence =
            self.bv_quantifier_full_domain_pending_evidence.take();
        let saved_bv_full_domain_query_grant = self.bv_quantifier_full_domain_query_grant.take();
        self.in_alternation_validation = true;
        let out = self.disambiguate_cegqi_valid_via_mbqi_inner(snapshot, category, aggressive);
        self.in_alternation_validation = false;
        if matches!(out, Some(Ok(SolveResult::Unsat(_)))) {
            // The nested probe made the accepted semantic decision. Neither
            // its disposable grants nor predecessor grants may survive it.
            self.clear_quantified_sat_authority();
        } else {
            // Exact model first, then the executor capabilities that name it.
            self.defer_model_validation = saved_defer;
            self.last_model = saved_model;
            self.dt_cert_grant_active = saved_dt_cert_grant;
            self.dt_cert_query_grant = saved_dt_cert_query_grant;
            self.finite_table_cert_grant_active = saved_finite_table_cert_grant;
            self.finite_table_cert_witness_state = saved_finite_table_witness;
            self.const_interp_cert_grant_active = saved_const_interp_cert_grant;
            self.const_interp_cert_witness_state = saved_const_interp_witness;
            self.cegqi_uf_recompletion_grant = saved_cegqi_uf_recompletion_grant;
            self.mbqi_sat_cert_grant_active = saved_mbqi_sat_cert_grant;
            self.mbqi_sat_cert_query_grant = saved_mbqi_sat_cert_query_grant;
            self.bv_quantifier_full_domain_proof = saved_bv_full_domain_proof;
            self.bv_quantifier_full_domain_pending_evidence = saved_bv_full_domain_pending_evidence;
            self.bv_quantifier_full_domain_query_grant = saved_bv_full_domain_query_grant;
            self.last_model_validated = saved_validated;
            self.last_unknown_reason = saved_reason;
        }
        out
    }

    fn disambiguate_cegqi_valid_via_mbqi_inner(
        &mut self,
        snapshot: &[TermId],
        category: LogicCategory,
        aggressive: bool,
    ) -> Option<Result<SolveResult>> {
        let mut quants: Vec<TermId> = Vec::new();
        for &a in snapshot {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, a, &mut quants);
        }
        let foralls: Vec<TermId> = quants
            .into_iter()
            .filter(|&q| matches!(self.ctx.terms.get(q), TermData::Forall(..)))
            .collect();
        // PERF: this validation adds an instantiation solve. The alternation
        // wrong-sats it targets are small, bare-`forall` problems; a query with
        // many quantifiers or a large ground state (e.g. a verification-consumer/quantifier_consumer
        // completion) is genuinely SAT and must not pay for a validation solve.
        // Bound the work to keep it off the hot path.
        if foralls.is_empty() || foralls.len() > 3 {
            return None;
        }

        // Quantifier-free ground core (candidate terms + ground constraints).
        let mut ground: Vec<TermId> = Vec::new();
        for &assertion in snapshot {
            if contains_quantifier(&self.ctx.terms, assertion) {
                let mut conjuncts = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, assertion, &mut conjuncts);
                for c in conjuncts {
                    if !contains_quantifier(&self.ctx.terms, c) && !ground.contains(&c) {
                        ground.push(c);
                    }
                }
            } else if !ground.contains(&assertion) {
                ground.push(assertion);
            }
        }
        if ground.len() > 12 {
            return None;
        }

        // Premise-forced refutation for the multi-binder / BitVec `fixpoint`
        // shape (`∀xs. premise(xs) ⟹ conclusion(xs)` with a UF-free
        // binder-pinning premise): the Int value-window loop below only covers
        // single-`Int`-binder foralls, so these fell through and the UF-
        // completion certificate granted a wrong `sat`. Sound; only ever UNSAT.
        if let Some(r @ Ok(SolveResult::Unsat(_))) =
            self.premise_forced_binder_refutation(&foralls, snapshot)
        {
            return Some(r);
        }

        // Eager bounded instantiation: for each single-`Int`-binder `forall`
        // with a quantifier-free body, add the ground instances `body[c]` for a
        // small window of concrete `c`. The Skolem function `sk` is SHARED across
        // instances, so a genuine universal (`(forall x (> sk(x) x))`) stays SAT
        // (`sk` maps each `c` to a witness), while a universal that is false at
        // some in-window `c` contributes a contradictory instance (e.g.
        // `(and (<= sk(2) 0) (>= sk(2) 2))`) that drives the whole conjunction
        // UNSAT. One solve decides it — no per-candidate sub-solving.
        let mut instances = ground;
        let mut added = false;
        let mut budget = 256usize;
        for &q in &foralls {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            let [(name, ay_core::Sort::Int)] = vars.as_slice() else {
                continue;
            };
            if contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            // Only the ALTERNATION shapes can be wrongly SAT here: the body must
            // apply a Skolem/uninterpreted function to the bound variable (a
            // skolemized inner existential or a declared UF). A pure-arithmetic
            // universal is already decided soundly by CEGQI, so skip it to avoid
            // adding an instantiation solve on every benign forall.
            let bound: ay_core::kani_compat::DetHashSet<String> =
                std::iter::once(name.clone()).collect();
            if !self.term_mentions_uninterpreted_of_bound_var(body, &bound) {
                continue;
            }
            for c in -16i64..=16 {
                if budget == 0 {
                    break;
                }
                budget -= 1;
                let cval = self.ctx.terms.mk_int(num_bigint::BigInt::from(c));
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(name.clone(), cval);
                let body_c = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                instances.push(body_c);
                added = true;
            }
            // E-matching instances: when the body applies a UF to a term LINEAR in
            // the bound variable (e.g. `(f (+ q0 q2))`) and the problem has a
            // ground application of the same UF (e.g. `(f 0)`), instantiate the
            // bound variable so the arguments ALIGN (`q2 = (- 0 q0)`). Congruence
            // then forces `(f (+ q0 q2)) = (f 0)`, exposing a contradiction a
            // value window cannot reach — the forall-over-UF-range case
            // `(forall q2 (and (= (f 0) 1) (<= (f (+ q0 q2)) 0)))`.
            for v in self.ematching_binder_values(body, name, &instances) {
                if budget == 0 {
                    break;
                }
                budget -= 1;
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(name.clone(), v);
                let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                instances.push(body_v);
                added = true;
            }
            // Relative instances: the falsifying value can be OFFSET from another
            // (outer-quantified) Int variable rather than absolute, e.g.
            // `(forall q1 (or (and (> (f (- q0 q1)) 3) (<= q1 q0)) (= q1 -3)))`
            // is UNSAT via `q1 = q0 + 1` (just above `q0`). Instantiate the binder
            // at `other ± k` for each free Int variable `other` in the body.
            for base in self.free_int_binder_bases(body, name) {
                for k in -2i64..=2 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
            // Round-2 (skolem-aligned) instances: a universal conjunct that
            // constrains a UF over its WHOLE range (`f(q0-1) > 1` for all q0)
            // contradicts the existential witness point (`f(sk(q0)-2) < -2`) only
            // when the two arguments meet. The witness point lives at the Skolem
            // application `sk(q0)`, so ground it at a few concrete binder values
            // and instantiate the binder NEAR each — bringing the whole-range
            // conjunct to the witness point so congruence exposes the conflict.
            for sk_base in self.skolem_app_bases(body, name) {
                for k in -2i64..=2 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![sk_base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
            // UF-value instances: instantiate the binder at `±U + k` for each
            // binder-independent UF value `U` (e.g. `f(3)`, `f(sk0)`). The
            // falsifying point of a universal over an unbounded binder with a
            // disjunctive/implication body frequently lands exactly at such a value
            // (`q1 = f(3)`) or just past its negation (`q1 = 1 - f(sk0)`), and the
            // two instances together expose a contradiction CEGQI's value window
            // and Presburger-incomplete path both miss. These are real instances of
            // the universal, so a resulting UNSAT is sound.
            for uf_base in self.uf_value_binder_bases(body, name) {
                let neg_base = self.ctx.terms.mk_neg(uf_base);
                for &base in &[uf_base, neg_base] {
                    for k in -2i64..=2 {
                        if budget == 0 {
                            break;
                        }
                        budget -= 1;
                        let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                        let v = self.ctx.terms.mk_add(vec![base, kterm]);
                        let mut subst: HashMap<String, TermId> = HashMap::default();
                        subst.insert(name.clone(), v);
                        let body_v =
                            crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                        instances.push(body_v);
                        added = true;
                    }
                }
            }
            // Atom-boundary instances: instantiate the binder at `boundary + k`
            // for each comparison atom's flip point (handles scaled/combined free
            // expressions like `3*c0 + 2` or `sk0 - c0` that the per-variable and
            // UF-value bases cannot reach, plus DIVISIBILITY boundaries `div(-rest,
            // c)` for non-unit coefficients). Real instances ⇒ sound.
            for base in self.atom_boundary_binder_bases(body, name) {
                for k in -2i64..=2 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
            // Combination instances: instantiate the binder at pairwise / limited
            // triple sums and differences of the anchor expressions (free vars, UF
            // values, atom boundaries). The simultaneous-violation point of several
            // atoms can be a linear COMBINATION of their individual boundaries
            // (`sk0 + c0 - d0`) that no single boundary reaches. Real instances of
            // the universal ⇒ a resulting UNSAT is sound; offsets kept to ±1 to
            // bound the count.
            for base in self.combination_binder_bases(body, name) {
                for k in -1i64..=1 {
                    if budget == 0 {
                        break;
                    }
                    budget -= 1;
                    let kterm = self.ctx.terms.mk_int(num_bigint::BigInt::from(k));
                    let v = self.ctx.terms.mk_add(vec![base, kterm]);
                    let mut subst: HashMap<String, TermId> = HashMap::default();
                    subst.insert(name.clone(), v);
                    let body_v = crate::ematching::subst_vars(&mut self.ctx.terms, body, &subst);
                    instances.push(body_v);
                    added = true;
                }
            }
        }
        if !added {
            return None;
        }

        // Canonicalize the argument order of every `+` node in the instance set so
        // that sums equal up to commutativity share one interned node. The eager
        // instances are built by substitution (`mk_add` preserves source order),
        // so an aligned witness term like `f(q1-c0)[q1:=sk0+c0-2] = f(+ -2 sk0)`
        // would otherwise NOT hash-cons with the ground `f(+ sk0 -2)`, defeating
        // E-graph congruence and missing the very contradiction the alignment was
        // built to expose. This is LOCAL to the validation's throwaway assertion
        // set — the global `mk_add` order is left untouched (canonicalizing it
        // perturbs unrelated UFLIA solver heuristics into incompleteness).
        let instances: Vec<TermId> = instances
            .into_iter()
            .map(|t| self.canonicalize_sums(t))
            .collect();

        // PERF: keep the historical 300 ms cap. Unlike the former in-place
        // `solve_for_category` call, the checked probe cannot leak its model,
        // proof, grants, or diagnostics into this enclosing quantified solve.
        // A refutation is accepted only with a strict authored-scope proof token
        // consumed against this exact ordered instance vector.
        let refuted = self
            .checked_ground_solve(instances.clone(), category, 300)
            .is_some_and(|decision| match decision {
                CheckedGroundDecision::Unsat(checked) => checked.consume(self, &instances),
                CheckedGroundDecision::Sat(_) => false,
            });
        if refuted {
            Some(Ok(SolveResult::unsat()))
        } else {
            // Per-candidate ISOLATED single-instance refutation
            // (#quantified-ce-lemma): the conjunction solve above conjoins
            // ~dozens of instances into ONE ground problem, and the NIA
            // ground solver demonstrably chokes on such conjunctions (three
            // UF-square atoms already answer unknown) while deciding each
            // instance SOLO (e.g. `(= (* (sk 2) (sk 2)) 2)` is UNSAT on its
            // own). Re-try a bounded set of concrete witnesses one instance
            // at a time. SOUND: gated to CONJUNCTIVE-position foralls (the
            // problem entails every instance of such a forall), and a
            // standalone instance being UNSAT means no interpretation of
            // its free symbols satisfies it — so the whole problem is
            // UNSAT. Candidate synthesis is not a soundness surface (every
            // candidate is verified by the ground solve).
            if let Some(r @ Ok(SolveResult::Unsat(_))) =
                self.universal_false_at_ground_witness(&foralls, snapshot, category)
            {
                return Some(r);
            }
            // Exact Fourier-Motzkin projection of the existential witness
            // (decides `(forall q1 (exists q2 <linear>))` shapes), then the
            // Skolem-atom over-approximation. These are the pre-existing base
            // refutations and run in both modes.
            if let Some(r @ Ok(SolveResult::Unsat(_))) =
                self.alternation_project_witness_unsat(&foralls, category, aggressive)
            {
                return Some(r);
            }
            if let Some(r @ Ok(SolveResult::Unsat(_))) =
                self.alternation_overapprox_unsat(&foralls, category)
            {
                return Some(r);
            }
            // Aggressive-only: the binder-dependent UF over-approximation (keeps
            // binder-INDEPENDENT UF terms as opaque constants — e.g. `f(1)` in
            // `(forall q0 (or (< q0 2) (<= (- q0 1) (f 1))))` — while weakening
            // binder-dependent UF atoms). Runs an extra `(forall ...)` sub-solve,
            // so it is reserved for the bare-alternation arm.
            if aggressive {
                return self.alternation_uf_overapprox_unsat(&foralls, category);
            }
            None
        }
    }

    /// Refute a conjunctive `∀xs. (premise(xs) ⟹ conclusion(xs))` in the
    /// multi-binder BitVector `fixpoint` family that the Int value-window path
    /// cannot reach.
    ///
    /// The recovered premise is ONLY a candidate generator. A disposable
    /// executor solves it at fresh BitVector constants and supplies concrete
    /// binder values `k`. We then substitute those literals into the WHOLE
    /// universal body and independently ground-solve `body(k)`. The premise is
    /// never asserted into the proof problem.
    ///
    /// SOUNDNESS. [`Self::forall_ids_in_conjunctive_position`] establishes that
    /// the original problem entails this universal, hence it entails every
    /// concrete instance `body(k)`. Therefore a definitive standalone UNSAT for
    /// `body(k)` proves the original problem UNSAT. Candidate quality is not a
    /// soundness surface: a mistaken De Morgan partition, a shadowed
    /// builtin-looking symbol, or an underspecified operation can at worst
    /// produce an unhelpful `k` whose whole-body verification is SAT/Unknown.
    /// Restricting binders to fixed-width BitVectors and Bool makes every
    /// candidate value exactly materializable as a model-independent literal.
    ///
    /// Both solves use fresh executors over cloned contexts. This is
    /// load-bearing: the old in-place probe changed quantified/QF routing state,
    /// invalidated proof/core provenance while registering constants, and leaked
    /// those registrations into later checks.
    fn premise_forced_binder_refutation(
        &mut self,
        foralls: &[TermId],
        snapshot: &[TermId],
    ) -> Option<Result<SolveResult>> {
        // Industrial UFBV routinely exceeds 100k terms; four known `fixpoint`
        // wrong-SATs exceeded the old cap. This cap bounds sub-solve work, not
        // soundness: UNSAT still requires an independent concrete ground solve.
        const MAX_QPF_CONTEXT_TERMS: usize = 500_000;
        if self.ctx.terms.len() > MAX_QPF_CONTEXT_TERMS || !self.qpf_probe_preflight() {
            return None;
        }
        let _export_suppression = Self::suppress_bv_cnf_export_for_internal_checks();
        let conjunctive = self.forall_ids_in_conjunctive_position(snapshot);
        'quantifier: for &q in foralls {
            if !conjunctive.contains(&q) {
                continue;
            }
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.is_empty()
                || vars
                    .iter()
                    // Bool is exactly materializable alongside fixed-width BV;
                    // excluding it lost most known UFBV premise recoveries.
                    .any(|(_, sort)| {
                        !matches!(sort, ay_core::Sort::BitVec(_) | ay_core::Sort::Bool)
                    })
                || contains_quantifier(&self.ctx.terms, body)
            {
                continue;
            }
            let Some(premise) = self.forall_premise_candidate(body) else {
                continue;
            };
            if contains_quantifier(&self.ctx.terms, premise) {
                continue;
            }
            if !self.qpf_probe_preflight() {
                return None;
            }

            // MULTIPLE candidate points, not just one (#ufbv-qpf-one-model).
            //
            // Each attempt asks the premise solver for a model, pins the binders
            // to that model's literals, and ground-refutes the substituted body.
            // A single attempt is at the mercy of which model the solver happens
            // to return, and the first one is routinely useless: on
            // `small-pipeline-fixpoint-1` the premise is satisfied by all-zeros,
            // the body holds there (`0 + 0 = 0`), and the probe declined — while
            // the refutation sits at `dataIn_64_0 = 1`, one blocking clause away.
            // That single missed point was a wrong `sat` on a declared-UNSAT
            // benchmark.
            //
            // So on a non-refuting attempt we block that exact valuation and ask
            // for a DIFFERENT model, up to `MAX_QPF_POINTS` times. Blocking is
            // recorded as concrete VALUES (`EvalValue`), not `TermId`s: each
            // attempt clones a fresh context, and ids minted in a previous
            // clone's `TermStore` are meaningless in the next one.
            //
            // Soundness is unchanged and does not depend on how many points are
            // tried. Every point yields `unsat` only via `∀v⃗. body ⊨ body[v⃗:=c⃗]`
            // plus an independent ground refutation of `body[c⃗]`, so a wider
            // search can add decided UNSATs or waste bounded time — never a wrong
            // answer. `qpf_probe_preflight` and the per-attempt sub-budgets bound
            // the cost, and the loop stops early as soon as the premise solver
            // stops producing new valuations.
            // Attempt one retains the old single-point cost. Extra points share
            // one wall budget checked between complete solve/verify attempts.
            const MAX_QPF_POINTS: usize = 8;
            const EXTRA_POINTS_BUDGET_MS: u64 = 1200;
            let extra_points_deadline = ay_core::time::Instant::now()
                + std::time::Duration::from_millis(EXTRA_POINTS_BUDGET_MS);
            let mut tried_values: Vec<Vec<EvalValue>> = Vec::new();

            'points: for _attempt in 0..MAX_QPF_POINTS {
                // Extra points are a completeness bonus, never an obligation:
                // abandon them the moment the caller's deadline or this probe's
                // own extra budget is spent.
                if _attempt > 0
                    && (self.solve_deadline.expired()
                        || ay_core::time::Instant::now() >= extra_points_deadline)
                {
                    continue 'quantifier;
                }
                if !self.qpf_probe_preflight() {
                    return None;
                }
                let candidate_ctx = self.ctx.clone();
                let mut candidate = self.qpf_probe_executor(candidate_ctx, 1000);
                if candidate
                    .ctx
                    .process_command(&ay_frontend::Command::ResetAssertions)
                    .is_err()
                {
                    continue 'quantifier;
                }
                let mut subst: HashMap<String, TermId> = HashMap::default();
                let mut fresh_terms = Vec::with_capacity(vars.len());
                let mut fresh_ok = true;
                for (name, sort) in &vars {
                    let c = candidate.ctx.terms.mk_fresh_var("__ay_qpf", sort.clone());
                    let cname = match candidate.ctx.terms.get(c) {
                        TermData::Var(n, _) => n.clone(),
                        _ => {
                            fresh_ok = false;
                            break;
                        }
                    };
                    candidate
                        .ctx
                        .register_native_global_symbol(cname.clone(), c, sort.clone());
                    subst.insert(name.clone(), c);
                    fresh_terms.push(c);
                }
                if !fresh_ok || subst.len() != vars.len() {
                    continue 'quantifier;
                }

                let premise_c =
                    crate::ematching::subst_vars(&mut candidate.ctx.terms, premise, &subst);
                candidate.ctx.assertions.push(premise_c);

                // Block every valuation already tried, so the solver is forced to
                // a genuinely new point instead of repeating the first one.
                for previous in &tried_values {
                    let mut diseqs = Vec::with_capacity(fresh_terms.len());
                    for (((_, sort), value), &fresh) in
                        vars.iter().zip(previous).zip(fresh_terms.iter())
                    {
                        let Some(literal) =
                            pin_eval_const_for_sort(&mut candidate.ctx.terms, sort, value)
                        else {
                            continue 'quantifier;
                        };
                        let eq = candidate.ctx.terms.mk_eq(fresh, literal);
                        diseqs.push(candidate.ctx.terms.mk_not(eq));
                    }
                    if diseqs.len() != vars.len() {
                        continue 'quantifier;
                    }
                    let block = candidate.ctx.terms.mk_or(diseqs);
                    candidate.ctx.assertions.push(block);
                }

                if !matches!(candidate.check_sat(), Ok(SolveResult::Sat)) {
                    // No further distinct valuation of the premise: nothing left
                    // for this quantifier, and `unsat` here is a property of the
                    // blocked premise, never of the original goal.
                    continue 'quantifier;
                }
                let Some(model) = candidate.last_model.as_ref() else {
                    continue 'quantifier;
                };
                let witness_values = {
                    fresh_terms
                        .iter()
                        .map(|&term| candidate.evaluate_term(model, term))
                        .collect::<Vec<_>>()
                };
                // Defensive: a solver that re-offers a blocked valuation (or a
                // sort whose values the blocking clause cannot express exactly)
                // would otherwise spin the remaining attempts on one point.
                if tried_values.contains(&witness_values) {
                    continue 'quantifier;
                }
                // Candidate terms and symbols belong only to the disposable
                // premise solver. Carry back scalar values, then materialize
                // their exact literals in the OUTER term store so the checked
                // verifier can bind its decision to this query's term identity.
                drop(candidate);

                let mut literal_subst: HashMap<String, TermId> = HashMap::default();
                for ((name, sort), value) in vars.iter().zip(&witness_values) {
                    let Some(literal) = pin_eval_const_for_sort(&mut self.ctx.terms, sort, value)
                    else {
                        continue 'quantifier;
                    };
                    literal_subst.insert(name.clone(), literal);
                }
                if literal_subst.len() != vars.len() {
                    continue 'quantifier;
                }
                let body_k =
                    crate::ematching::subst_vars(&mut self.ctx.terms, body, &literal_subst);
                if contains_quantifier(&self.ctx.terms, body_k) {
                    continue 'quantifier;
                }

                let obligation = vec![body_k];
                if self
                    .checked_ground_solve(obligation.clone(), LogicCategory::QfUfbv, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => checked.consume(self, &obligation),
                        CheckedGroundDecision::Sat(_) => false,
                    })
                {
                    // Preserve this independently checked instance as a c7 fragment hint.
                    self.qpf_register_premise_forced_instance(
                        q,
                        &vars,
                        body,
                        &literal_subst,
                        body_k,
                    );
                    return Some(Ok(SolveResult::unsat()));
                }
                tried_values.push(witness_values);
                continue 'points;
            }
        }
        None
    }

    /// Decline a disposable deep-context probe before it can breach the
    /// caller's deadline, interrupt, or memory envelope.
    ///
    /// The 50% checks are predictive: cloning the context roughly doubles its
    /// term/parser footprint. A term-count cap alone does not bound parsed AST,
    /// symbol, or string storage, so waiting until after `Context::clone` can
    /// already have crossed the process ceiling.
    fn qpf_probe_preflight(&self) -> bool {
        if self.external_stop_reason().is_some()
            || self.term_memory_exceeded()
            || ay_core::TermStore::global_memory_exceeded()
            || ay_sys::process_memory_exceeded_at_percent(50)
            || crate::memory::memory_exceeded(self.memory_limit())
        {
            return false;
        }
        // Charge the probe's OWN clone, never the whole-process footprint — see
        // [`crate::memory::probe_clone_fits`]. This is the preflight the ground
        // optimization-authority probe reaches
        // (`checked_optimization_roots_decision` -> `checked_ground_solve` ->
        // `checked_isolated_solve`), and reading process RSS here is what made
        // `native_decision_routes_preserve_parsed_publication_controls`
        // nondeterministic in the full lib binary while passing in isolation.
        // `optimization_probe_preflight` is the byte-identical twin of this
        // gate; both now charge the same quantity through the same helper.
        if !crate::memory::probe_clone_fits(self.ctx.terms.true_memory_bytes(), self.memory_limit())
        {
            return false;
        }
        self.ctx.terms.true_memory_bytes() <= ay_core::TermStore::per_engine_budget() / 2
    }

    /// Heuristically recover a premise candidate from a universal body.
    ///
    /// `(=> premise _)` yields `premise` directly. A body normalized to De
    /// Morgan disjunctive form `(=> (and p₁ … pₖ) C)` = `(or C (not p₁) … (not
    /// pₖ))` yields the FULL premise `(and p₁ … pₖ)` — every negated disjunct is
    /// a premise conjunct. (Grabbing only the first `(not p₁)` under-pins the
    /// binders — the SSA chain leaves later binders free and the instance is
    /// vacuously SAT.)
    ///
    /// `term_mentions_completable_uf` is deliberately an operational,
    /// name-oriented completion classifier, not a semantic partition oracle.
    /// Mispartitioning is harmless here because this term only proposes concrete
    /// binder values; [`Self::premise_forced_binder_refutation`] verifies the
    /// Probe-local: does `term` mention a user-DECLARED function symbol?
    ///
    /// Replaces `term_mentions_completable_uf` when `forall_premise_candidate`
    /// decides which `or` disjuncts form the CONCLUSION rather than premise
    /// conjuncts. That predicate bottoms out in
    /// `is_mbqi_completable_uf_symbol`, a hardcoded exclusion list plus
    /// `!name.starts_with("bv")`. SMT-LIB's structural bit-vector operators are
    /// named `concat`, `extract`, `zero_extend`, `sign_extend`, `rotate_left`,
    /// `rotate_right` and `repeat` — none of which start with `bv` — so every
    /// one was misread as a user UF. A premise conjunct mentioning one was then
    /// booked as conclusion and discarded, the binders it pins stayed free, the
    /// disposable candidate solve returned an arbitrary value for them, the
    /// substituted body was vacuously SAT on a false premise, and the probe
    /// returned None. That is how small-synabs-fixpoint-2/3/9 were lost: their
    /// `ite` conditions read `(= ((_ zero_extend 26) v) (_ bvN 32))`.
    ///
    /// It also failed in the other direction — a genuine user UF whose name
    /// happens to start with `bv` was not recognised as a UF at all.
    ///
    /// This asks the semantic question instead: is the head a user-declared
    /// symbol of arity > 0, per `ctx.symbol_iter()` — the same source
    /// used by the quantified model gate. Deliberately probe-local:
    /// `is_mbqi_completable_uf_symbol` is read by several other MBQI
    /// certificates and by `quantifier_consumer_ground_assertion_supported_by_completion`,
    /// so changing it globally would perturb quantified classification across
    /// every division and needs its own differential run.
    fn disjunct_mentions_declared_uf(&self, term: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let declared: HashSet<String> = self
            .ctx
            .symbol_iter()
            .filter(|(_, info)| !info.arg_sorts.is_empty())
            .map(|(name, info)| self.ctx.symbol_identity_name(name, info).to_string())
            .collect();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if !args.is_empty() && declared.contains(sym.name()) {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, el) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*el);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }

    /// whole universal instance and never treats this candidate as an asserted
    /// fact.
    fn forall_premise_candidate(&mut self, body: TermId) -> Option<TermId> {
        match self.ctx.terms.get(body).clone() {
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => Some(args[0]),
            TermData::App(sym, args) if sym.name() == "or" && args.len() >= 2 => {
                // `(or C (not p₁) … (not pₖ))` = `(=> (and p₁ … pₖ) C)` where the
                // conclusion `C` carries the UF applications and each premise
                // conjunct `pᵢ` is UF-FREE (a binder equality). Collect the
                // apparently UF-free disjuncts (robust to how preprocessing renders each
                // `(not pᵢ)` — `Not`, `distinct`, a folded comparison, …) and
                // NEGATE each to recover `pᵢ`.
                let mut conjs: Vec<TermId> = Vec::new();
                let mut has_uf_disjunct = false;
                for &d in &args {
                    if self.disjunct_mentions_declared_uf(d) {
                        has_uf_disjunct = true;
                    } else {
                        conjs.push(self.ctx.terms.mk_not(d));
                    }
                }
                // Require a UF-bearing conclusion disjunct (else this is a pure
                // universal handled elsewhere) and at least one premise conjunct.
                if !has_uf_disjunct || conjs.is_empty() {
                    return None;
                }
                match conjs.len() {
                    1 => Some(conjs[0]),
                    _ => Some(self.ctx.terms.mk_and(conjs)),
                }
            }
            _ => None,
        }
    }

    /// Build an isolated probe executor over `ctx` under the caller's resource
    /// envelope. The caller owns the cloned context, so solving may mutate every
    /// executor/context bookkeeping field without touching the outer query.
    fn qpf_probe_executor(&self, ctx: ay_frontend::Context, budget_ms: u64) -> Executor {
        let mut probe = Executor::new();
        probe.ctx = ctx;
        probe.set_verification_level(self.verification_level());
        probe.set_self_check(self.self_check());
        probe.set_learned_clause_limit(self.learned_clause_limit());
        probe.set_clause_db_bytes_limit(self.clause_db_bytes_limit());
        probe.set_resource_limit(self.resource_limit());
        probe.set_decision_limit(self.decision_limit());
        probe.set_ground_budget_enabled(self.ground_budget_enabled());
        probe.set_memory_limit(self.memory_limit());
        probe.set_term_memory_limit(self.term_memory_limit());
        let tight = ay_core::time::Instant::now() + std::time::Duration::from_millis(budget_ms);
        let bounded = match self.solve_deadline.get() {
            Some(d) if d < tight => Some(d),
            _ => Some(tight),
        };
        probe.set_solve_controls(self.solve_interrupt.clone(), bounded);
        probe
    }

    /// Over-approximate each alternation `forall` to a NECESSARY condition on the
    /// universal alone and decide THAT with the ordinary quantifier procedure.
    ///
    /// Replace every existential-witness-dependent (Skolem-function) atom in the
    /// body with its polarity-permissive truth value, yielding `C'` with
    /// `(exists q1. body) => C'`. Hence `(forall q0 (exists q1. body)) =>
    /// (forall q0. C')`, so if `(forall q0. C')` is UNSAT the original is UNSAT.
    /// This catches whole-range / unbounded contradictions a value window cannot
    /// (e.g. `f(1) <= q0` required for ALL q0). Sound: it only ever returns UNSAT,
    /// and the differential fuzz validates no wrong-unsat is introduced.
    fn alternation_overapprox_unsat(
        &mut self,
        foralls: &[TermId],
        _category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        for &q in foralls {
            let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.len() != 1 || contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            let Some(cprime) = self.abstract_skolem_atoms(body, true) else {
                continue;
            };
            if cprime == body {
                continue; // no Skolem atom abstracted — nothing gained
            }
            let new_forall =
                self.ctx
                    .terms
                    .mk_forall_with_triggers(vars.clone(), cprime, triggers.clone());
            let obligation = vec![new_forall];
            if self
                .checked_exact_unsat_solve(obligation.clone(), 300)
                .is_some_and(|checked| checked.consume(self, &obligation))
            {
                return Some(Ok(SolveResult::unsat()));
            }
        }
        None
    }

    /// Over-approximate each alternation `forall` by weakening only the atoms that
    /// apply an uninterpreted/non-arith function to a term mentioning the BINDER,
    /// while keeping binder-INDEPENDENT UF terms intact as opaque constants.
    ///
    /// A binder-dependent application (`(f (* 2 q0))`, a skolemized inner
    /// existential, …) is a value the model can choose freely per binder point, so
    /// replacing its enclosing atom with the polarity-permissive constant only
    /// WEAKENS the body (`body => C'`). A binder-independent application (`(f 1)`)
    /// is a single fixed unknown — keeping it lets the universal procedure refute
    /// `(forall q0 (or (< q0 2) (<= (- q0 1) (f 1))))` (no value of `f(1)` bounds
    /// `q0 - 1` for all `q0`). Hence `(forall q0. body) => (forall q0. C')` and an
    /// UNSAT `C'` refutes the original. Distinct from `alternation_overapprox_unsat`
    /// (which abstracts EVERY Skolem atom, including binder-independent ones, and so
    /// would erase the `(f 1)` constraint here). Sound: only ever returns UNSAT.
    fn alternation_uf_overapprox_unsat(
        &mut self,
        foralls: &[TermId],
        _category: LogicCategory,
    ) -> Option<Result<SolveResult>> {
        for &q in foralls {
            let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.len() != 1 || contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            let bound: ay_core::kani_compat::DetHashSet<String> =
                vars.iter().map(|(n, _)| n.clone()).collect();
            let Some(cprime) = self.abstract_binder_dependent_uf_atoms(body, true, &bound) else {
                continue;
            };
            if cprime == body {
                continue; // nothing weakened — no gain
            }
            let new_forall =
                self.ctx
                    .terms
                    .mk_forall_with_triggers(vars.clone(), cprime, triggers.clone());
            let obligation = vec![new_forall];
            if self
                .checked_exact_unsat_solve(obligation.clone(), 300)
                .is_some_and(|checked| checked.consume(self, &obligation))
            {
                return Some(Ok(SolveResult::unsat()));
            }
        }
        None
    }

    /// Polarity-tracking NNF weakening: replace every atom that applies an
    /// uninterpreted/non-arith function to a BINDER-dependent subterm with its
    /// polarity-permissive constant (`true` positive, `false` negative). Atoms over
    /// binder-INDEPENDENT UF terms are kept verbatim. Returns `None` on a
    /// non-monotone Ite condition (a condition mentioning such an atom).
    fn abstract_binder_dependent_uf_atoms(
        &mut self,
        term: TermId,
        positive: bool,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> Option<TermId> {
        match self.ctx.terms.get(term).clone() {
            TermData::Not(inner) => {
                let a = self.abstract_binder_dependent_uf_atoms(inner, !positive, bound)?;
                Some(self.ctx.terms.mk_not(a))
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_binder_dependent_uf_atoms(a, positive, bound)?);
                }
                Some(self.ctx.terms.mk_and(new))
            }
            TermData::App(sym, args) if sym.name() == "or" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_binder_dependent_uf_atoms(a, positive, bound)?);
                }
                Some(self.ctx.terms.mk_or(new))
            }
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => {
                let a = self.abstract_binder_dependent_uf_atoms(args[0], !positive, bound)?;
                let b = self.abstract_binder_dependent_uf_atoms(args[1], positive, bound)?;
                Some(self.ctx.terms.mk_implies(a, b))
            }
            TermData::Ite(c, t, e) => {
                if self.term_mentions_uninterpreted_of_bound_var(c, bound) {
                    return None; // non-monotone condition
                }
                let t2 = self.abstract_binder_dependent_uf_atoms(t, positive, bound)?;
                let e2 = self.abstract_binder_dependent_uf_atoms(e, positive, bound)?;
                Some(self.ctx.terms.mk_ite(c, t2, e2))
            }
            _ => {
                if self.term_mentions_uninterpreted_of_bound_var(term, bound) {
                    Some(self.ctx.terms.mk_bool(positive))
                } else {
                    Some(term)
                }
            }
        }
    }

    /// Decide `(forall q1 (exists q2 <body>))`-shaped alternations EXACTLY by
    /// Fourier-Motzkin projection of the (skolemized) existential witness.
    ///
    /// For a single-`Int`-binder `forall` whose body is a CONJUNCTION of linear
    /// atoms in which a single Skolem application `sk(q1)` occurs only with unit
    /// coefficient, eliminate `sk(q1)` exactly: each `sk >= L` paired with each
    /// `sk <= U` yields `L <= U`, plus the sk-free atoms. The projected
    /// `(forall q1. proj)` is EQUISATISFIABLE to the original (unit-coefficient FM
    /// is exact over the integers), so its UNSAT is the original's UNSAT — and it
    /// is a pure-arithmetic universal the ordinary procedure decides (e.g.
    /// `(forall q1 (exists q2 (and (<= q2 (+ c0 1)) (>= q2 (- q1)))))` projects to
    /// `(forall q1. (- q1) <= (+ c0 1))`, UNSAT). Returns `Some(Ok(unsat))` only on
    /// a definitive refutation.
    fn alternation_project_witness_unsat(
        &mut self,
        foralls: &[TermId],
        _category: LogicCategory,
        aggressive: bool,
    ) -> Option<Result<SolveResult>> {
        for &q in foralls {
            let TermData::Forall(vars, body, trig) = self.ctx.terms.get(q).clone() else {
                continue;
            };
            if vars.len() != 1 || contains_quantifier(&self.ctx.terms, body) {
                continue;
            }
            // Try the EXACT single-Skolem projection first (base mode); in
            // aggressive mode fall back to the multi-Skolem relaxation (drops the
            // atoms it cannot FM, which only enlarges the existential witness set,
            // so a refuted projection still refutes the original).
            let Some(proj_body) = self
                .project_single_skolem(body)
                .or_else(|| self.project_single_skolem_dnf(body))
                .or_else(|| {
                    if aggressive {
                        self.project_multi_skolem(body)
                    } else {
                        None
                    }
                })
            else {
                continue;
            };
            let proj_forall =
                self.ctx
                    .terms
                    .mk_forall_with_triggers(vars.clone(), proj_body, trig.clone());
            let obligation = vec![proj_forall];
            if self
                .checked_exact_unsat_solve(obligation.clone(), 300)
                .is_some_and(|checked| checked.consume(self, &obligation))
            {
                return Some(Ok(SolveResult::unsat()));
            }

            // Per-conjunct isolated refutation: `(forall q (and c1..cn))` is
            // equivalent to `AND_i (forall q ci)`, so if ANY isolated `(forall q
            // ci)` is UNSAT the whole projection is UNSAT. This sidesteps a
            // downstream gap where the multi-conjunct universal (a binder-free
            // conjunct sharing a free var with the binder-dependent one) is
            // returned `unknown` even though one conjunct alone refutes. Sound:
            // isolation only removes constraints, never adds satisfiability, and we
            // act ONLY on a definitive isolated UNSAT.
            if aggressive {
                let mut conjs = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, proj_body, &mut conjs);
                if conjs.len() >= 2 {
                    for ci in conjs {
                        let fi =
                            self.ctx
                                .terms
                                .mk_forall_with_triggers(vars.clone(), ci, trig.clone());
                        let obligation = vec![fi];
                        if self
                            .checked_exact_unsat_solve(obligation.clone(), 300)
                            .is_some_and(|checked| checked.consume(self, &obligation))
                        {
                            return Some(Ok(SolveResult::unsat()));
                        }
                    }
                }
            }
        }
        None
    }

    /// Project a single unit-coefficient Skolem application out of a conjunctive
    /// `Int` body by Fourier-Motzkin. Returns `None` when the shape is outside the
    /// exact fragment (not a conjunction of linear atoms, multiple Skolem
    /// applications, a non-unit/non-linear coefficient, or a Skolem application
    /// inside an uninterpreted/non-arith term).
    fn project_single_skolem(&mut self, body: TermId) -> Option<TermId> {
        // Exactly one distinct Skolem application in the body.
        let mut sk_apps: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(body, &mut sk_apps);
        if sk_apps.len() != 1 {
            return None;
        }
        let sk = sk_apps[0];

        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        if conjuncts.is_empty() {
            return None;
        }

        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));

        let mut lowers: Vec<TermId> = Vec::new(); // sk >= L
        let mut uppers: Vec<TermId> = Vec::new(); // sk <= U
        let mut kept: Vec<TermId> = Vec::new();

        for c in conjuncts {
            // (d rel 0): rel in {>=, >, =}. Normalize each comparison.
            let (a, b, strict, is_eq) = match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                    ">=" => (args[0], args[1], false, false),
                    ">" => (args[0], args[1], true, false),
                    "<=" => (args[1], args[0], false, false),
                    "<" => (args[1], args[0], true, false),
                    "=" if matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) => {
                        (args[0], args[1], false, true)
                    }
                    _ => {
                        // Non-(in)equality atom: keep iff sk-free, else bail.
                        if self.term_contains_id(c, sk) {
                            return None;
                        }
                        kept.push(c);
                        continue;
                    }
                },
                _ => {
                    if self.term_contains_id(c, sk) {
                        return None;
                    }
                    kept.push(c);
                    continue;
                }
            };
            // d = a - b, atom is `d (>= or >) 0` (or `= 0`).
            let d = self.ctx.terms.mk_sub(vec![a, b]);
            if !self.term_contains_id(d, sk) {
                kept.push(c);
                continue;
            }
            // SOUNDNESS (S2 disease, quantified-CE-lemma fuzz 2026-07-09): the
            // difference probe below measures a genuine linear coefficient ONLY
            // when `d` is AFFINE in `sk`. A quadratic occurrence (`sk*sk > -3`,
            // d = sk² + 3) folds to the FAKE constant coefficient 1 and turns a
            // vacuous bounded-below atom into a hard bound `sk >= -2` — the
            // projection then wrongly refutes a VALID alternation (wrong-UNSAT,
            // caught by the alternation differential fuzz). This projector
            // claims exactness, so bail out entirely.
            if self.var_under_nonarith(d, sk) {
                return None;
            }
            // coeff of sk = d[sk:=1] - d[sk:=0]; rest = d[sk:=0]; require coeff = ±1.
            let d1 = self.subst_term(d, sk, one);
            let d0 = self.subst_term(d, sk, zero);
            let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
            let coeff_val = match self.ctx.terms.get(coeff) {
                TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                _ => return None, // non-constant => sk non-linear / under UF
            };
            let rest = d0; // d = coeff*sk + rest
            if coeff_val == num_bigint::BigInt::from(1) {
                // sk + rest (>= or >) 0  =>  sk >= -rest (+1 if strict, int)
                let neg_rest = self.ctx.terms.mk_sub(vec![zero, rest]);
                let l = if strict {
                    self.ctx.terms.mk_add(vec![neg_rest, one])
                } else {
                    neg_rest
                };
                lowers.push(l);
                if is_eq {
                    uppers.push(neg_rest);
                }
            } else if coeff_val == num_bigint::BigInt::from(-1) {
                // -sk + rest (>= or >) 0  =>  sk <= rest (-1 if strict, int)
                let u = if strict {
                    self.ctx.terms.mk_sub(vec![rest, one])
                } else {
                    rest
                };
                uppers.push(u);
                if is_eq {
                    lowers.push(rest);
                }
            } else {
                return None; // non-unit coefficient: outside the exact fragment
            }
        }

        // FM: every lower bound <= every upper bound, plus kept atoms.
        let mut proj: Vec<TermId> = kept;
        for &l in &lowers {
            for &u in &uppers {
                let le = self.ctx.terms.mk_le(l, u);
                proj.push(le);
            }
        }
        if proj.is_empty() {
            return None;
        }
        Some(self.ctx.terms.mk_and(proj))
    }

    /// Exact Fourier-Motzkin projection of a SINGLE unit-coefficient `Int` Skolem
    /// application out of a CONJUNCTION of atoms (`atoms` is the implicit `and`).
    /// `atoms` may mix sk-comparison atoms (FM-eliminated) and sk-free atoms (kept
    /// verbatim). Returns the sk-free formula `≡ ∃sk. AND(atoms)`:
    ///   * `Some(true)` when the projection is unconstrained (`∃sk` always holds —
    ///     e.g. only upper bounds on `sk` and no kept atoms),
    ///   * `Some(φ)` for the exact projected formula,
    ///   * `None` when an sk-containing atom is outside the unit-coefficient linear
    ///     fragment (the caller must then bail — it cannot soundly project).
    /// Over the integers this is EXACT: each strict atom is integer-tightened
    /// (`sk+rest>0 ⟺ sk >= 1-rest`), and `∃ integer sk. l<=sk<=u ⟺ l<=u` because
    /// `l,u` are integer-valued. Used by [`project_single_skolem_dnf`].
    fn fm_project_sk_conjunction(&mut self, atoms: &[TermId], sk: TermId) -> Option<TermId> {
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let mut lowers: Vec<TermId> = Vec::new(); // sk >= L
        let mut uppers: Vec<TermId> = Vec::new(); // sk <= U
        let mut kept: Vec<TermId> = Vec::new();
        for &c in atoms {
            let (a, b, strict, is_eq) = match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                    ">=" => (args[0], args[1], false, false),
                    ">" => (args[0], args[1], true, false),
                    "<=" => (args[1], args[0], false, false),
                    "<" => (args[1], args[0], true, false),
                    "=" if matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) => {
                        (args[0], args[1], false, true)
                    }
                    _ => {
                        if self.term_contains_id(c, sk) {
                            return None;
                        }
                        kept.push(c);
                        continue;
                    }
                },
                _ => {
                    if self.term_contains_id(c, sk) {
                        return None;
                    }
                    kept.push(c);
                    continue;
                }
            };
            let d = self.ctx.terms.mk_sub(vec![a, b]);
            if !self.term_contains_id(d, sk) {
                kept.push(c);
                continue;
            }
            // SOUNDNESS (S2 disease): the probe needs `d` AFFINE in `sk` — a
            // quadratic occurrence folds to a fake constant coefficient and
            // manufactures a bound that wrongly refutes a valid alternation.
            // This projector claims exactness, so bail out entirely.
            if self.var_under_nonarith(d, sk) {
                return None;
            }
            let d1 = self.subst_term(d, sk, one);
            let d0 = self.subst_term(d, sk, zero);
            let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
            let coeff_val = match self.ctx.terms.get(coeff) {
                TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                _ => return None,
            };
            let rest = d0;
            if coeff_val == num_bigint::BigInt::from(1) {
                let neg_rest = self.ctx.terms.mk_sub(vec![zero, rest]);
                let l = if strict {
                    self.ctx.terms.mk_add(vec![neg_rest, one])
                } else {
                    neg_rest
                };
                lowers.push(l);
                if is_eq {
                    uppers.push(neg_rest);
                }
            } else if coeff_val == num_bigint::BigInt::from(-1) {
                let u = if strict {
                    self.ctx.terms.mk_sub(vec![rest, one])
                } else {
                    rest
                };
                uppers.push(u);
                if is_eq {
                    lowers.push(rest);
                }
            } else {
                return None;
            }
        }
        let mut proj: Vec<TermId> = kept;
        for &l in &lowers {
            for &u in &uppers {
                let le = self.ctx.terms.mk_le(l, u);
                proj.push(le);
            }
        }
        if proj.is_empty() {
            // Unconstrained: `∃sk` is satisfiable for every value of the free vars.
            return Some(self.ctx.terms.mk_bool(true));
        }
        Some(self.ctx.terms.mk_and(proj))
    }

    /// DNF-aware EXACT projection of a single unit-coefficient `Int` Skolem out of a
    /// conjunctive body in which some conjuncts are DISJUNCTIONS that mention the
    /// Skolem (which the pure-conjunctive [`project_single_skolem`] rejects). `∃sk`
    /// distributes over `∨` but not `∧`, so expand the body's sk-containing
    /// conjuncts to DNF, FM-project `sk` from each disjunct's conjunction, and OR
    /// the results:  `∃sk.(A ∧ (B∨C)) = (∃sk.A∧B) ∨ (∃sk.A∧C)`. Each disjunction's
    /// alternatives must be sk-comparison atoms or sk-free terms (deeper sk-nesting
    /// bails). EXACT (neither relaxes nor strengthens), so a refuted projection
    /// refutes the original AND it can never manufacture a wrong-UNSAT on a
    /// genuinely-SAT alternation. Bounded cross-product keeps it off the hot path.
    ///
    /// Catches the alternation wrong-sats where the existential witness must thread
    /// a DISJUNCTIVE choice (`(forall q0 (exists q1 (and (> -1 (+ q1 q0))
    /// (or (< c (- 1 q0)) (= q1 -2)))))`, UNSAT): projects to
    /// `(forall q0. (or (< c (- 1 q0)) (<= q0 0)))`, decided UNSAT.
    fn project_single_skolem_dnf(&mut self, body: TermId) -> Option<TermId> {
        let mut sk_apps: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(body, &mut sk_apps);
        if sk_apps.len() != 1 {
            return None;
        }
        let sk = sk_apps[0];

        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        if conjuncts.is_empty() {
            return None;
        }

        // Partition: sk-free conjuncts (kept), sk-comparison atoms, sk-containing
        // disjunctions (each alternative an sk-comparison atom or sk-free term).
        let mut kept_free: Vec<TermId> = Vec::new();
        let mut sk_atoms: Vec<TermId> = Vec::new();
        let mut disjunctions: Vec<Vec<TermId>> = Vec::new();
        for c in conjuncts {
            if !self.term_contains_id(c, sk) {
                kept_free.push(c);
                continue;
            }
            if self.is_int_comparison_atom(c) {
                sk_atoms.push(c);
                continue;
            }
            match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if sym.name() == "or" => {
                    // Every alternative that mentions sk must be a plain
                    // comparison atom (no deeper nesting) so the cross-product
                    // FM stays exact; sk-free alternatives are kept verbatim.
                    for &a in &args {
                        if self.term_contains_id(a, sk) && !self.is_int_comparison_atom(a) {
                            return None;
                        }
                    }
                    disjunctions.push(args);
                }
                _ => return None,
            }
        }
        // A pure conjunction (no disjunction) is the exact-projection job of
        // `project_single_skolem`; only act when there is a real DNF to expand.
        if disjunctions.is_empty() {
            return None;
        }

        // Bound the cross-product.
        let mut combos = 1usize;
        for d in &disjunctions {
            combos = combos.saturating_mul(d.len());
        }
        if combos == 0 || combos > 32 {
            return None;
        }

        // Odometer over the disjunctions: each combination picks one alternative
        // per disjunction, joins with the shared sk-atoms, and FM-projects sk.
        let mut projected: Vec<TermId> = Vec::new();
        let mut idx = vec![0usize; disjunctions.len()];
        loop {
            let mut atoms = sk_atoms.clone();
            for (di, &ai) in idx.iter().enumerate() {
                atoms.push(disjunctions[di][ai]);
            }
            let proj = self.fm_project_sk_conjunction(&atoms, sk)?;
            // A `true` disjunct makes `∃sk.body` hold for all q0 -> nothing to
            // refute; abandon (the universal is satisfiable on this branch).
            if matches!(
                self.ctx.terms.get(proj),
                TermData::Const(ay_core::Constant::Bool(true))
            ) {
                return None;
            }
            projected.push(proj);
            // Advance the odometer.
            let mut k = 0;
            loop {
                if k == idx.len() {
                    // Wrapped past the most-significant digit: done.
                    let or_term = if projected.len() == 1 {
                        projected[0]
                    } else {
                        self.ctx.terms.mk_or(projected.clone())
                    };
                    let mut out = kept_free;
                    out.push(or_term);
                    return Some(self.ctx.terms.mk_and(out));
                }
                idx[k] += 1;
                if idx[k] < disjunctions[k].len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
        }
    }

    /// True iff `t` is a binary `Int` (in)equality comparison atom (`>=,>,<=,<,=`).
    fn is_int_comparison_atom(&self, t: TermId) -> bool {
        match self.ctx.terms.get(t) {
            TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                ">=" | ">" | "<=" | "<" => true,
                "=" => matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int),
                _ => false,
            },
            _ => false,
        }
    }

    /// Project ALL Skolem applications out of a conjunctive `Int` body by ITERATED
    /// Fourier-Motzkin, DROPPING any conjunct outside the unit-coefficient linear
    /// fragment (a disequality, a Skolem under a UF, a non-unit coefficient). Each
    /// drop only RELAXES the existential witness — it removes a constraint the
    /// witness must satisfy — so `(exists sk1..skn. body) => proj`, hence
    /// `(forall q (exists sk. body)) => (forall q. proj)` and an UNSAT projection
    /// refutes the original (relaxation is one-directional: sound for UNSAT only).
    /// Handles the multi-witness `(forall q (exists q1 q2 ...))` shapes the exact
    /// single-Skolem projection cannot, e.g. `(forall q0 (exists q1 q2 (and
    /// (< q1 (* 2 c0)) (<= 1 (+ q0 q1)) (< 2 (+ c0 q2)) (distinct ...))))` projects
    /// (after dropping the disequality and FM-eliminating q1,q2) to
    /// `(forall q0. (>= (+ (* 2 c0) q0 -2) 0))`, UNSAT.
    /// Repeatedly substitute any Skolem application uniquely DETERMINED by an
    /// equality conjunct `(= L R)` (over Int, where the Skolem occurs with unit
    /// coefficient so `sk = -rest`/`sk = rest`) by its forced value throughout the
    /// body. Exact: the existential witness is pinned by the equality, so this is
    /// neither a relaxation nor a strengthening. Iterates so a chain of equalities
    /// resolves. Bounded iteration count (each step removes one Skolem occurrence).
    fn substitute_equality_determined_skolems(&mut self, body: TermId) -> TermId {
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let mut cur = body;
        // At most one Skolem is removed per pass; cap passes by the Skolem count.
        let mut sk_all: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(cur, &mut sk_all);
        let max_passes = sk_all.len().min(8);
        for _ in 0..max_passes {
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, cur, &mut conjuncts);
            let mut substituted = false;
            'outer: for c in conjuncts {
                let TermData::App(sym, args) = self.ctx.terms.get(c).clone() else {
                    continue;
                };
                if sym.name() != "=" || args.len() != 2 {
                    continue;
                }
                if !matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) {
                    continue;
                }
                let d = self.ctx.terms.mk_sub(vec![args[0], args[1]]); // L - R
                let mut local_sk: Vec<TermId> = Vec::new();
                self.collect_skolem_apps(d, &mut local_sk);
                for sk in local_sk {
                    // SOUNDNESS (S2 disease): an equality NON-AFFINE in `sk`
                    // (`sk*sk = x`) does NOT determine `sk`; the difference
                    // probe would fold to a fake unit coefficient and
                    // "solve" `sk := x`, corrupting the (claimed-exact)
                    // substitution. Skip such equalities.
                    if self.var_under_nonarith(d, sk) {
                        continue;
                    }
                    // coeff of sk in d, and rest = d[sk:=0] (skolem-free in sk).
                    let d1 = self.subst_term(d, sk, one);
                    let d0 = self.subst_term(d, sk, zero);
                    let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
                    let cv = match self.ctx.terms.get(coeff) {
                        TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                        _ => continue, // sk nonlinear / under UF in this equality
                    };
                    let rest = d0; // d = coeff*sk + rest, atom is d = 0
                    let solved = if cv == num_bigint::BigInt::from(1) {
                        self.ctx.terms.mk_sub(vec![zero, rest]) // sk = -rest
                    } else if cv == num_bigint::BigInt::from(-1) {
                        rest // sk = rest
                    } else {
                        continue; // non-unit: not exactly solvable over the integers
                    };
                    // `solved` is built from d[sk:=0], hence free of `sk`; substitute
                    // the forced value for every occurrence of the witness.
                    cur = self.subst_term(cur, sk, solved);
                    substituted = true;
                    break 'outer;
                }
            }
            if !substituted {
                break;
            }
        }
        cur
    }

    fn project_multi_skolem(&mut self, body: TermId) -> Option<TermId> {
        const GE: u8 = 0; // d >= 0
        const GT: u8 = 1; // d > 0
        const EQ: u8 = 2; // d = 0

        // Phase 0: exactly eliminate any witness UNIQUELY DETERMINED by an
        // equality conjunct (`sk = T`). Substitution is exact (the witness is
        // forced), so it neither over- nor under-approximates AND it sidesteps the
        // FM fragment limits: a determined `sk` carried into a non-unit atom
        // (`2*sk <= ...`) or a disequality becomes a pure binder constraint instead
        // of being dropped. Decides the equality-determined family, e.g.
        // `(forall q0 (exists q1 q2 (and (= (- q0 3) (+ q2 c0)) (<= (* 2 q2) (+ q0
        // 3)) (> (+ q2 q0) (+ q1 q2)))))`: q2 is forced to q0-3-c0, the non-unit
        // bound becomes `2*(q0-3-c0) <= q0+3`, and q1 then FM-eliminates freely.
        let body = self.substitute_equality_determined_skolems(body);

        let mut sk_apps: Vec<TermId> = Vec::new();
        self.collect_skolem_apps(body, &mut sk_apps);
        if sk_apps.is_empty() {
            // Every witness was exactly eliminated by equality substitution; the
            // residual is a pure (skolem-free) universal body the ordinary
            // procedure decides.
            return Some(body);
        }
        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        if conjuncts.is_empty() {
            return None;
        }
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));

        // (d, kind) constraints; skolem-free non-linear conjuncts kept verbatim
        // (they constrain the binder), skolem-bearing non-fragment ones dropped.
        let mut cons: Vec<(TermId, u8)> = Vec::new();
        let mut kept_raw: Vec<TermId> = Vec::new();
        for c in conjuncts {
            let parsed = match self.ctx.terms.get(c).clone() {
                TermData::App(sym, args) if args.len() == 2 => match sym.name() {
                    ">=" => Some((self.ctx.terms.mk_sub(vec![args[0], args[1]]), GE)),
                    ">" => Some((self.ctx.terms.mk_sub(vec![args[0], args[1]]), GT)),
                    "<=" => Some((self.ctx.terms.mk_sub(vec![args[1], args[0]]), GE)),
                    "<" => Some((self.ctx.terms.mk_sub(vec![args[1], args[0]]), GT)),
                    "=" if matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) => {
                        Some((self.ctx.terms.mk_sub(vec![args[0], args[1]]), EQ))
                    }
                    _ => None,
                },
                _ => None,
            };
            match parsed {
                Some(dk) => cons.push(dk),
                None => {
                    if !sk_apps.iter().any(|&sk| self.term_contains_id(c, sk)) {
                        kept_raw.push(c);
                    }
                }
            }
        }

        // Eliminate each Skolem application in turn.
        for &sk in &sk_apps {
            let mut next: Vec<(TermId, u8)> = Vec::new();
            // (a>0, L): the bound `a*sk >= L`.  (b>0, U): the bound `b*sk <= U`.
            // Keeping the coefficient lets the FM combine use the REAL (rational)
            // shadow `a*U - b*L >= 0` for NON-UNIT coefficients (Omega real shadow),
            // instead of dropping non-unit atoms. The rational projection
            // over-approximates sk's integer solution set, so it can only add a
            // NECESSARY condition on the universal — never a wrong UNSAT.
            let mut lowers: Vec<(num_bigint::BigInt, TermId)> = Vec::new();
            let mut uppers: Vec<(num_bigint::BigInt, TermId)> = Vec::new();
            for (d, k) in cons.drain(..) {
                if !self.term_contains_id(d, sk) {
                    next.push((d, k));
                    continue;
                }
                // SOUNDNESS (S2 disease): a NON-AFFINE `sk` occurrence
                // (`sk*sk > -3`) folds the difference probe to a fake constant
                // coefficient, minting a bound the atom never implied. This
                // projector is a RELAXATION, so dropping the atom is sound (it
                // only enlarges the witness set) — drop, never mis-project.
                if self.var_under_nonarith(d, sk) {
                    continue;
                }
                let d1 = self.subst_term(d, sk, one);
                let d0 = self.subst_term(d, sk, zero);
                let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
                let coeff_val = match self.ctx.terms.get(coeff) {
                    TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
                    _ => continue, // sk nonlinear / under UF here -> drop (relax)
                };
                let rest = d0; // d = coeff_val*sk + rest, atom is `d (k) 0`
                use num_traits::Zero;
                if coeff_val.is_zero() {
                    next.push((rest, k)); // sk cancels; keep the sk-free atom
                    continue;
                }
                if coeff_val > num_bigint::BigInt::zero() {
                    // coeff*sk + rest (k) 0  =>  coeff*sk (k) -rest
                    let neg_rest = self.ctx.terms.mk_sub(vec![zero, rest]);
                    match k {
                        GE => lowers.push((coeff_val, neg_rest)),
                        // int-tighten `> 0` to `>= 1`: coeff*sk >= 1 - rest
                        GT => lowers.push((coeff_val, self.ctx.terms.mk_add(vec![neg_rest, one]))),
                        EQ => {
                            lowers.push((coeff_val.clone(), neg_rest));
                            uppers.push((coeff_val, neg_rest));
                        }
                        _ => unreachable!(),
                    }
                } else {
                    // coeff < 0: let a = -coeff > 0; -a*sk + rest (k) 0 => a*sk (k') rest
                    let a = -coeff_val;
                    match k {
                        GE => uppers.push((a, rest)),
                        GT => uppers.push((a, self.ctx.terms.mk_sub(vec![rest, one]))),
                        EQ => {
                            uppers.push((a.clone(), rest));
                            lowers.push((a, rest));
                        }
                        _ => unreachable!(),
                    }
                }
            }
            // Real-shadow FM: a*sk>=L and b*sk<=U give b*L <= a*b*sk <= a*U, hence
            // `a*U - b*L >= 0`. (Unit coeffs a=b=1 reduce to the prior `U-L>=0`.)
            for (a, l) in &lowers {
                for (b, u) in &uppers {
                    let a_t = self.ctx.terms.mk_int(a.clone());
                    let b_t = self.ctx.terms.mk_int(b.clone());
                    let a_u = self.ctx.terms.mk_mul(vec![a_t, *u]);
                    let b_l = self.ctx.terms.mk_mul(vec![b_t, *l]);
                    let d = self.ctx.terms.mk_sub(vec![a_u, b_l]); // a*U - b*L >= 0
                    next.push((d, GE));
                }
            }
            cons = next;
        }

        // Rebuild atoms. Any residual still mentioning a Skolem means elimination
        // was incomplete -> bail (never emit an over-tight body).
        let mut proj: Vec<TermId> = kept_raw;
        for (d, k) in &cons {
            if sk_apps.iter().any(|&sk| self.term_contains_id(*d, sk)) {
                return None;
            }
            let atom = match *k {
                GE => self.ctx.terms.mk_ge(*d, zero),
                GT => self.ctx.terms.mk_gt(*d, zero),
                EQ => self.ctx.terms.mk_eq(*d, zero),
                _ => unreachable!(),
            };
            proj.push(atom);
        }
        if proj.is_empty() {
            return None;
        }
        Some(self.ctx.terms.mk_and(proj))
    }

    /// Rewrite `term` so every `(+ ...)` node is re-normalized to a canonical
    /// argument order, recursively. Rebuilding each sum through `mk_add` puts the
    /// folded constant in a fixed position (Phase-3 partition: non-constant
    /// summands first, constant last), so a parse-built `(+ sk0 -2)` and a
    /// substitution/coefficient-collected `(+ -2 sk0)` — both denoting `sk0-2` —
    /// re-normalize to the SAME interned node. `+` is commutative, so this is
    /// semantics-preserving; its only effect is to make sums equal up to summand
    /// order hash-cons together, restoring E-graph congruence across
    /// `f(<sum1>)` / `f(<sum2>)`. Applied only to the alternation validation's
    /// throwaway instance set (never the global term graph, whose order other
    /// solver heuristics depend on).
    fn canonicalize_sums(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> =
                    args.iter().map(|&a| self.canonicalize_sums(a)).collect();
                if sym.name() == "+" && new_args.len() >= 2 {
                    self.ctx.terms.mk_add(new_args)
                } else if new_args == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let i = self.canonicalize_sums(inner);
                self.ctx.terms.mk_not(i)
            }
            TermData::Ite(c, t, e) => {
                let nc = self.canonicalize_sums(c);
                let nt = self.canonicalize_sums(t);
                let ne = self.canonicalize_sums(e);
                self.ctx.terms.mk_ite(nc, nt, ne)
            }
            _ => term,
        }
    }

    fn collect_skolem_apps(&self, root: TermId, out: &mut Vec<TermId>) {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__ay_sk_") {
                        if !out.contains(&t) {
                            out.push(t);
                        }
                    } else {
                        stack.extend(args.iter().copied());
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                _ => {}
            }
        }
    }

    fn term_contains_id(&self, root: TermId, target: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if t == target {
                return true;
            }
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, th, e) => {
                    stack.push(*c);
                    stack.push(*th);
                    stack.push(*e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                _ => {}
            }
        }
        false
    }

    fn subst_term(&mut self, root: TermId, target: TermId, repl: TermId) -> TermId {
        if root == target {
            return repl;
        }
        match self.ctx.terms.get(root).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.subst_term(a, target, repl))
                    .collect();
                if new == args {
                    root
                } else {
                    // Use SIMPLIFYING arithmetic constructors so a substituted
                    // product like `(* 1 2)` folds to `2`. Without this, the FM
                    // projection's coefficient probe `d[sk:=1] - d[sk:=0]` over a
                    // term `(* sk 2)` produced the non-constant `(* 1 2)` and the
                    // atom was wrongly dropped as non-linear (missing the `2*sk>=4`
                    // bound). Folding is semantics-preserving.
                    match sym.name() {
                        "+" => self.ctx.terms.mk_add(new),
                        "-" if new.len() == 1 => self.ctx.terms.mk_neg(new[0]),
                        "-" if new.len() == 2 => self.ctx.terms.mk_sub(new),
                        "*" => self.ctx.terms.mk_mul(new),
                        _ => {
                            let sort = self.ctx.terms.sort(root).clone();
                            self.ctx.terms.mk_app(sym, new, sort)
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                let i = self.subst_term(inner, target, repl);
                self.ctx.terms.mk_not(i)
            }
            TermData::Ite(c, t, e) => {
                let c2 = self.subst_term(c, target, repl);
                let t2 = self.subst_term(t, target, repl);
                let e2 = self.subst_term(e, target, repl);
                self.ctx.terms.mk_ite(c2, t2, e2)
            }
            _ => root,
        }
    }

    /// Replace each Skolem-function-containing atom in `term` with its
    /// polarity-permissive truth value (`true` in positive position, `false` in
    /// negative), tracking polarity through the boolean connectives. Returns
    /// `None` when a Skolem atom occurs in a non-monotonic position (an `ite`
    /// condition) where the weakening is not valid. The result is implied by the
    /// original (a necessary condition), so a `forall` over it that is UNSAT
    /// witnesses the original `forall`-`exists` UNSAT.
    fn abstract_skolem_atoms(&mut self, term: TermId, positive: bool) -> Option<TermId> {
        match self.ctx.terms.get(term).clone() {
            TermData::Not(inner) => {
                let a = self.abstract_skolem_atoms(inner, !positive)?;
                Some(self.ctx.terms.mk_not(a))
            }
            TermData::App(sym, args) if sym.name() == "and" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_skolem_atoms(a, positive)?);
                }
                Some(self.ctx.terms.mk_and(new))
            }
            TermData::App(sym, args) if sym.name() == "or" => {
                let mut new = Vec::with_capacity(args.len());
                for a in args {
                    new.push(self.abstract_skolem_atoms(a, positive)?);
                }
                Some(self.ctx.terms.mk_or(new))
            }
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => {
                let a = self.abstract_skolem_atoms(args[0], !positive)?;
                let b = self.abstract_skolem_atoms(args[1], positive)?;
                Some(self.ctx.terms.mk_implies(a, b))
            }
            TermData::Ite(c, t, e) => {
                if self.term_mentions_a_skolem_fn(c) {
                    return None; // non-monotonic condition
                }
                let t2 = self.abstract_skolem_atoms(t, positive)?;
                let e2 = self.abstract_skolem_atoms(e, positive)?;
                Some(self.ctx.terms.mk_ite(c, t2, e2))
            }
            // Atom / opaque sub-formula: if it mentions a Skolem function, replace
            // the whole thing with the polarity-permissive constant (weakening).
            _ => {
                if self.term_mentions_a_skolem_fn(term) {
                    Some(self.ctx.terms.mk_bool(positive))
                } else {
                    Some(term)
                }
            }
        }
    }

    fn term_mentions_a_skolem_fn(&self, root: TermId) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__ay_sk_") {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t2, e) => {
                    stack.push(*c);
                    stack.push(*t2);
                    stack.push(*e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
                _ => {}
            }
        }
        false
    }

    /// Fold linear equalities to constants inside every QUANTIFIED top-level
    /// assertion, before quantifier processing.
    ///
    /// `(= a b)` over Int/Real where `a - b` is a constant is `false`/`true`
    /// (e.g. `(= (- q1 0) (- q1 1))` -> `false`). The ground LIA/LRA solver
    /// decides these, but inside a `forall`/`exists` body the un-folded atom — if
    /// it mentions the bound variable — survives the quantifier classification as
    /// a live, existential-witness-dependent literal and can route a genuinely
    /// arithmetic universal down the (unsound-for-it) UF-completion path. Folding
    /// it here normalises the body so `body_is_pure_arith_bool` / CEGQI see the
    /// real shape. Restricted to quantified assertions so ground problems (and
    /// their proof structure) are untouched.
    pub(in crate::executor) fn fold_quantified_linear_eqs(&mut self) {
        let mut forall_provenance = Vec::new();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if contains_quantifier(&self.ctx.terms, a) {
                // The proof tracker has a dedicated, strict derivation for a
                // top-level negative single-binder forall: it starts from the
                // exact authored `not(forall ...)`, applies `sko_forall`, and
                // derives the Skolemized NNF body with Boolean rules. Folding
                // comparisons inside that source first would instead create a
                // semantically equivalent but unauthored Assume leaf. Preserve
                // the source shape only when it matches that certified lane;
                // Skolemization still performs the required NNF conversion.
                let preserve_certified_skolem_source = self.produce_proofs_enabled()
                    && match self.ctx.terms.get(a) {
                        TermData::Not(quantified) => match self.ctx.terms.get(*quantified) {
                            TermData::Forall(bindings, body, _) if bindings.len() == 1 => {
                                matches!(
                                    self.ctx.terms.get(*body),
                                    TermData::App(sym, args)
                                        if sym.name() == "or" && args.len() >= 2
                                ) && !contains_quantifier(&self.ctx.terms, *body)
                            }
                            _ => false,
                        },
                        _ => false,
                    };
                if preserve_certified_skolem_source {
                    continue;
                }
                let provenance_start = forall_provenance.len();
                let folded = self.fold_linear_eqs(a, &mut forall_provenance);
                let proof_translatable = if self.produce_proofs_enabled() && folded != a {
                    match (self.ctx.terms.get(a), self.ctx.terms.get(folded)) {
                        (
                            TermData::Forall(source_vars, source_body, source_triggers),
                            TermData::Forall(target_vars, target_body, target_triggers),
                        ) if source_vars == target_vars && source_triggers == target_triggers => {
                            matches!(
                                (
                                    self.ctx.terms.get(*source_body),
                                    self.ctx.terms.get(*target_body),
                                ),
                                (
                                    TermData::App(source_symbol, source_args),
                                    TermData::App(target_symbol, target_args),
                                ) if source_symbol.name() == "or"
                                    && target_symbol.name() == "or"
                                    && !source_args.is_empty()
                                    && source_args.len() == target_args.len()
                            )
                        }
                        _ => false,
                    }
                } else {
                    true
                };
                if proof_translatable {
                    self.ctx.assertions[i] = folded;
                } else {
                    // The rewrite is semantically valid, but the strict proof
                    // producer only certifies the flat-or normalization above.
                    // Retain the authored quantifier and discard every nested
                    // provenance record minted while probing this rewrite.
                    forall_provenance.truncate(provenance_start);
                }
            }
        }
        // B2 audit: pure proof bookkeeping (provenance registration only;
        // the assertion rewrite above already happened either way) — safe to
        // skip when the tracker is off, including under competition shedding.
        if !self.produce_proofs_enabled() || forall_provenance.is_empty() {
            return;
        }
        let Some(assertion_provenance) = self.proof_problem_assertion_provenance.as_mut() else {
            return;
        };
        for record in forall_provenance {
            // A nested/derived forall is not a free problem premise. Only an
            // exact constructor record rooted at an immutable authored
            // assertion may be consulted by E-matching proof registration.
            if !assertion_provenance
                .original_problem_assertions
                .contains(&record.source_forall)
            {
                continue;
            }
            let source_set = vec![record.source_forall];
            let entry = assertion_provenance
                .assertion_sources
                .entry(record.normalized_forall)
                .or_default();
            if !entry.contains(&source_set) {
                entry.push(source_set);
            }
        }
    }

    /// Drop bound variables that never occur in their quantifier body, and
    /// collapse a fully-vacuous quantifier to its body. Over non-empty SMT sorts,
    /// `(forall x. P) == P` and `(exists x. P) == P` when `P` does not mention `x`
    /// — an unconditionally valid equivalence, so this never changes
    /// satisfiability. It removes spurious quantifiers that otherwise misroute a
    /// ground constraint into the alternation/CEGQI machinery and yield a wrong
    /// SAT (e.g. a vacuous `(forall ((y Int)) (> b 0))` alongside a genuine
    /// `(forall ((y Int)) (< z (+ y 3)))`, #quant-alt-WS). Runs after
    /// `fold_quantified_linear_eqs`, so a body folded to a constant is then seen
    /// as vacuous and collapsed.
    pub(in crate::executor) fn simplify_vacuous_quantifiers(&mut self) {
        let proof_authority_active = self.produce_proofs_enabled();
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if contains_quantifier(&self.ctx.terms, a) {
                let mut simplified = self.drop_unused_bound_vars(a);
                if proof_authority_active && simplified != a {
                    // (#vacuous-quantifier-authority) Certify the collapse from
                    // the authored root (the tracker independently replays the
                    // vacuousness check), retaining the exact triple for the
                    // checked-SAT-refutation sidecar. The conservative
                    // `quantified_proof_translation_incomplete` marker is
                    // still set for EVERY rewrite unless the DEFAULT-OFF
                    // narrowing stage is armed: the landing audit found the
                    // marker's read site can route through
                    // `Unknown(QuantifierUnhandled)` into the phase-2.4/2.5
                    // SAT certificates, so un-setting it is a staged SAT-side
                    // behaviour change (#sat-grants-are-staged). With the
                    // stage off, a certified collapse is discharged instead by
                    // the pre-existing strict-proof gate at the marker's read
                    // site. `--no-quant-unit-authority` restores baseline
                    // exactly (marker always set, no certification attempt).
                    let certified = crate::quant_unit_authority::quant_unit_authority_enabled()
                        .then(|| {
                            self.proof_tracker.add_vacuous_quantifier_collapse(
                                &mut self.ctx.terms,
                                a,
                                simplified,
                            )
                        })
                        .flatten();
                    match certified {
                        Some(record) => {
                            self.skolem_instance_records.push(
                                crate::executor::SkolemInstanceRecord {
                                    source: a,
                                    quantified: record.quantified,
                                    witness: record.witness,
                                    instance: record.instance,
                                    asserted: simplified,
                                    positive: record.positive,
                                },
                            );
                            if self.vacuous_collapse_requires_translation_marker(simplified) {
                                self.quantified_proof_translation_incomplete = true;
                            }
                        }
                        None => {
                            self.quantified_proof_translation_incomplete = true;
                        }
                    }
                }
                if !proof_authority_active {
                    // Hoist conjuncts out of quantifiers they don't mention BEFORE
                    // the infeasibility check, so a deep binder-independent conjunct
                    // like `(= b (* 3 x))` buried under `(exists y (forall z ...))`
                    // reaches the outer `(forall x ...)` where its nonzero
                    // x-coefficient refutes.
                    //
                    // These two equivalence rewrites do not yet emit proof terms.
                    // Under public proof authority, collapsing an authored
                    // `forall` to `false` would strand that generated constant as a
                    // free Assume and erase the exact `forall_inst` route. Preserve
                    // the quantified source instead; downstream instantiation can
                    // derive a concrete contradiction from the authored binder.
                    simplified = self.hoist_binder_independent_conjuncts(simplified);
                    simplified = self.simplify_infeasible_forall_eq(simplified);
                }
                self.ctx.assertions[i] = simplified;
            }
        }
    }

    /// #quantprod-g2: fold `select` over a KNOWN-CONSTANT array inside
    /// quantified assertions, before quantifier classification.
    ///
    /// Two equivalence-preserving rewrites, applied only INSIDE assertions
    /// that contain a quantifier (ground problems and their proof structure
    /// are untouched):
    ///
    /// 1. `(select ((as const (Array I E)) k) i) -> k` — valid at any binder
    ///    depth and polarity (the const array maps every index to `k`).
    /// 2. When a TOP-LEVEL assertion pins a ground array term to a literal
    ///    constant array — `(= a ((as const …) k))` with `k` a literal — every
    ///    `(select a i)` elsewhere folds to `k`. The pin assertion itself is
    ///    KEPT (it is ground, so this pass never touches it): in every model
    ///    of the retained pin `select a i = k`, so the conjunction is
    ///    logically unchanged in both polarities, and the array solver still
    ///    produces/validates `a`'s model value from the pin.
    ///
    /// This makes `(forall ((x Int)) (= (select a x) k))` collapse to a
    /// vacuous-binder tautology that `simplify_vacuous_quantifiers` (which
    /// runs next) removes — instead of the whole problem failing closed
    /// through the deliberate MBQI-unsafe quantified-array degrade. Every
    /// non-foldable quantified-array shape flows on byte-identically, so that
    /// fail-close stays intact.
    pub(in crate::executor) fn fold_pinned_const_array_selects(&mut self) {
        use ay_core::kani_compat::DetHashMap;
        // Phase 1: collect literal const-array pins from top-level unit
        // equalities. Only a `Const`-element const-array qualifies; the
        // pinned side may be any ground array-sorted term that is not itself
        // a const-array literal. Conflicting pins keep the LAST one — sound
        // either way, because the retained pin equalities ground-refute the
        // problem regardless of which entailed fold was applied.
        let mut pins: DetHashMap<TermId, TermId> = Default::default();
        for &a in &self.ctx.assertions {
            let TermData::App(ay_core::term::Symbol::Named(op), args) = self.ctx.terms.get(a)
            else {
                continue;
            };
            if op != "=" || args.len() != 2 {
                continue;
            }
            for (x, y) in [(args[0], args[1]), (args[1], args[0])] {
                if self.ctx.terms.get_const_array(x).is_some() {
                    continue;
                }
                let Some(elem) = self.ctx.terms.get_const_array(y) else {
                    continue;
                };
                if matches!(self.ctx.terms.get(elem), TermData::Const(_)) {
                    pins.insert(x, elem);
                }
            }
        }
        // Phase 2: fold inside quantified assertions.
        for i in 0..self.ctx.assertions.len() {
            let a = self.ctx.assertions[i];
            if contains_quantifier(&self.ctx.terms, a) {
                self.ctx.assertions[i] = self.fold_const_array_selects_rec(a, &pins);
            }
        }
    }

    /// Recursive worker for [`Self::fold_pinned_const_array_selects`]:
    /// rewrite `(select arr i)` to the constant element when `arr` is a
    /// literal const-array or a pinned ground array term. Quantifiers are
    /// rebuilt with their trigger lists intact; `Let` is left untouched
    /// (conservative — a let-bound shadow could alias the pinned name).
    fn fold_const_array_selects_rec(
        &mut self,
        term: TermId,
        pins: &ay_core::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.fold_const_array_selects_rec(a, pins))
                    .collect();
                if let ay_core::term::Symbol::Named(name) = &sym {
                    if name == "select" && new.len() == 2 {
                        let arr = new[0];
                        // A pinned ground array (`pins` keys are ground
                        // TermIds, so a binder variable can never collide) or
                        // a direct const-array literal.
                        if let Some(&elem) = pins.get(&arr) {
                            return elem;
                        }
                        if let Some(elem) = self.ctx.terms.get_const_array(arr) {
                            if matches!(self.ctx.terms.get(elem), TermData::Const(_)) {
                                return elem;
                            }
                        }
                    }
                }
                if new == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new, sort)
                }
            }
            TermData::Not(inner) => {
                let ni = self.fold_const_array_selects_rec(inner, pins);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.fold_const_array_selects_rec(c, pins),
                    self.fold_const_array_selects_rec(t, pins),
                    self.fold_const_array_selects_rec(e, pins),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                let is_forall = matches!(self.ctx.terms.get(term), TermData::Forall(..));
                let nb = self.fold_const_array_selects_rec(body, pins);
                if nb == body {
                    term
                } else {
                    self.rebuild_quant(is_forall, vars, nb, triggers)
                }
            }
            _ => term,
        }
    }

    /// Recursively hoist conjuncts out of a quantifier whose binder they do not
    /// mention: `(Q vars. (and A B))` with `A` free of every `vars` binder equals
    /// `(and A (Q vars. (and B)))` for both `Q ∈ {forall, exists}` (the universal
    /// distributes over the conjunction, and a binder-independent conjunct passes
    /// through an existential unchanged). Sound and equivalence-preserving. Lifts a
    /// deep binder-independent atom to the enclosing scope so the infeasibility
    /// rewrite can see it as a top-level conjunct of an OUTER universal.
    fn hoist_binder_independent_conjuncts(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.hoist_binder_independent_conjuncts(a))
                    .collect();
                if new == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new, sort)
                }
            }
            TermData::Not(i) => {
                let ni = self.hoist_binder_independent_conjuncts(i);
                if ni == i {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.hoist_binder_independent_conjuncts(c),
                    self.hoist_binder_independent_conjuncts(t),
                    self.hoist_binder_independent_conjuncts(e),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                let is_forall = matches!(self.ctx.terms.get(term), TermData::Forall(..));
                let nb = self.hoist_binder_independent_conjuncts(body);
                let mut conjs = Vec::new();
                collect_and_conjuncts(&self.ctx.terms, nb, &mut conjs);
                if conjs.len() < 2 {
                    if nb == body {
                        return term;
                    }
                    return self.rebuild_quant(is_forall, vars, nb, triggers);
                }
                let (indep, dep): (Vec<TermId>, Vec<TermId>) = conjs
                    .into_iter()
                    .partition(|&c| !vars.iter().any(|(n, _)| self.term_mentions_name(c, n)));
                if indep.is_empty() {
                    if nb == body {
                        return term;
                    }
                    return self.rebuild_quant(is_forall, vars, nb, triggers);
                }
                // Re-wrap the dependent conjuncts under the quantifier; conjoin the
                // hoisted binder-independent ones at this (enclosing) level.
                let inner_body = if dep.is_empty() {
                    self.ctx.terms.mk_bool(true)
                } else if dep.len() == 1 {
                    dep[0]
                } else {
                    self.ctx.terms.mk_and(dep)
                };
                let mut out = indep;
                if !matches!(
                    self.ctx.terms.get(inner_body),
                    TermData::Const(ay_core::Constant::Bool(true))
                ) {
                    out.push(self.rebuild_quant(is_forall, vars, inner_body, triggers));
                }
                self.ctx.terms.mk_and(out)
            }
            TermData::Let(bindings, body) => {
                let nb = self.hoist_binder_independent_conjuncts(body);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_let(bindings, nb)
                }
            }
            _ => term,
        }
    }

    fn rebuild_quant(
        &mut self,
        is_forall: bool,
        vars: Vec<(String, ay_core::Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
    ) -> TermId {
        if is_forall {
            self.ctx.terms.mk_forall_with_triggers(vars, body, triggers)
        } else {
            self.ctx.terms.mk_exists_with_triggers(vars, body, triggers)
        }
    }

    /// Recursively rewrite `(forall vars. body)` to `false` when a TOP-LEVEL
    /// conjunct of `body` is an `Int` linear equality `(= L R)` whose difference
    /// `L - R` has a NONZERO constant coefficient in one of `vars`: such an
    /// equality cannot hold for every value of that binder, so the universal is
    /// false. Sound — a conjunct that is false for some binder value makes the
    /// whole `(forall ...)` false (forall distributes over the conjunction), and
    /// `false` then propagates through any enclosing quantifiers. Catches the
    /// inner `(forall z (and (= x (+ (* 3 b) z)) ...))` of a forall-exists-forall
    /// alternation that no existential witness can repair
    /// (#quant-inner-forall-infeasible-eq).
    fn simplify_infeasible_forall_eq(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.simplify_infeasible_forall_eq(a))
                    .collect();
                if new == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new, sort)
                }
            }
            TermData::Not(i) => {
                let ni = self.simplify_infeasible_forall_eq(i);
                if ni == i {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.simplify_infeasible_forall_eq(c),
                    self.simplify_infeasible_forall_eq(t),
                    self.simplify_infeasible_forall_eq(e),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb = self.simplify_infeasible_forall_eq(body);
                if self.forall_has_infeasible_linear_eq(nb, &vars) {
                    return self.ctx.terms.mk_bool(false);
                }
                // Disjunction-infeasible: `(forall v. (or A(v) B))` where EVERY
                // binder-DEPENDENT disjunct is a binder-infeasible linear equality
                // and the rest are binder-INDEPENDENT equals `(or <indep>)` —
                // `∀v.(or Ai(v) Bj) = (∀v.(or Ai)) ∨ (or Bj)`, and a finite union
                // of single-point exceptions cannot cover the infinite Int domain,
                // so `(∀v.(or Ai))` is false. Computed DIRECTLY (no intermediate
                // forall-in-disjunction, which the instantiation loop mishandles).
                if let Some(reduced) = self.forall_or_drop_infeasible_disjuncts(nb, &vars) {
                    return reduced;
                }
                // A universal whose (simplified) body is a boolean CONSTANT equals
                // that constant over a non-empty sort — collapse it so a nested
                // `(forall x false)` produced by the rewrite above propagates.
                if let TermData::Const(ay_core::Constant::Bool(_)) = self.ctx.terms.get(nb) {
                    return nb;
                }
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_forall_with_triggers(vars, nb, triggers)
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let nb = self.simplify_infeasible_forall_eq(body);
                // `(exists x <bool const>)` = that constant over a non-empty sort.
                if let TermData::Const(ay_core::Constant::Bool(_)) = self.ctx.terms.get(nb) {
                    return nb;
                }
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_exists_with_triggers(vars, nb, triggers)
                }
            }
            TermData::Let(bindings, body) => {
                let nb = self.simplify_infeasible_forall_eq(body);
                if nb == body {
                    term
                } else {
                    self.ctx.terms.mk_let(bindings, nb)
                }
            }
            _ => term,
        }
    }

    /// True when a top-level conjunct of `body` is an `Int` equality `(= L R)`
    /// whose `L - R` is LINEAR in some binder of `vars` with a nonzero constant
    /// coefficient (so `(forall <that binder>. (= L R))` is false). The
    /// coefficient is read by the same `d[v:=1] - d[v:=0]` probe as the FM
    /// projection; a non-constant result (binder under a UF / nonlinear) is
    /// skipped — fail open (never a wrong rewrite).
    fn forall_has_infeasible_linear_eq(
        &mut self,
        body: TermId,
        vars: &[(String, ay_core::Sort)],
    ) -> bool {
        let mut conjuncts = Vec::new();
        collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
        // `collect_and_conjuncts` only descends an `and`; a body that is itself a
        // single atom (e.g. a bare `(= L R)` or a single disjunct) is the lone
        // conjunct.
        if conjuncts.is_empty() {
            conjuncts.push(body);
        }
        // Conjunct position: a single conjunct false at SOME v makes the whole
        // `(forall v. (and ..))` false, so inequalities are admissible here (a
        // nonzero-coefficient inequality is false at an extreme v).
        conjuncts
            .into_iter()
            .any(|c| self.atom_is_binder_infeasible(c, vars, true))
    }

    /// True when `c` is an `Int` (in)equality `(REL L R)` (`REL ∈ {=,<,<=,>,>=}`)
    /// whose `L - R` has a NONZERO coefficient in some binder of `vars`, so
    /// `(forall <that binder>. c)` is false. For `=` the difference is not
    /// identically zero (fails at some v); for an inequality a nonzero
    /// v-coefficient makes `L-R` UNBOUNDED in v, so it crosses 0 and violates the
    /// bound at an extreme v. The coefficient is `d[v:=1] - d[v:=0]` evaluated with
    /// every OTHER free Int atom (Var or 0-ary constant) set to 0 — independent of
    /// them — so the probe folds even with a term like `(* x 4)`. A non-constant
    /// residue (binder under a UF / nonlinear in another var) yields no firing —
    /// fail open, never a wrong rewrite.
    fn atom_is_binder_infeasible(
        &mut self,
        c: TermId,
        vars: &[(String, ay_core::Sort)],
        allow_inequalities: bool,
    ) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(c).clone() else {
            return false;
        };
        let ineq = matches!(sym.name(), "<" | "<=" | ">" | ">=");
        if !(sym.name() == "=" || (allow_inequalities && ineq)) || args.len() != 2 {
            return false;
        }
        if !matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) {
            return false;
        }
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let d = self.ctx.terms.mk_sub(vec![args[0], args[1]]);
        for (name, sort) in vars {
            if !matches!(sort, ay_core::Sort::Int) {
                continue;
            }
            // The parser creates fresh per-scope bound vars, so `mk_var(name)`
            // does NOT recover the body's binder; find its actual hash-consed
            // `Var(name, _)` TermId inside the difference instead.
            let Some(v) = self.find_bound_var_id(d, name) else {
                continue;
            };
            if !self.term_contains_id(d, v) {
                continue;
            }
            // SOUNDNESS: the v-coefficient is only well-defined (and the UF-app
            // zeroing in int_const_zeroing_vars only sound) when v occurs PURELY
            // ARITHMETICALLY. If v sits under an uninterpreted/other app (e.g.
            // `z + f(z)`), then `f(1)` and `f(0)` differ and zeroing both would
            // manufacture a spurious nonzero coefficient (f could be `-z`, making
            // the universal SAT). Skip that binder.
            if self.var_under_nonarith(d, v) {
                continue;
            }
            let d1 = self.subst_term(d, v, one);
            let d0 = self.subst_term(d, v, zero);
            let (Some(c1), Some(c0)) = (
                self.int_const_zeroing_vars(d1),
                self.int_const_zeroing_vars(d0),
            ) else {
                continue;
            };
            if c1 != c0 {
                return true;
            }
        }
        false
    }

    /// True when binder `v` has any NON-AFFINE occurrence in `root` — i.e. the
    /// `d[v:=1] - d[v:=0]` probe in `atom_is_binder_infeasible` would NOT measure
    /// a genuine linear coefficient.
    ///
    /// SOUNDNESS (S2 wrong-UNSAT closure, 2026-07-08): the probe's argument ("a
    /// nonzero v-coefficient makes `L-R` unbounded in v, so it crosses 0") is
    /// only valid when `d` is AFFINE in v. The previous guard admitted every
    /// occurrence under `+ - * div mod abs` — so `(forall x. (>= (* x x) 0))`
    /// (VALID; d = x², d1−d0 = 1) was collapsed to FALSE and the whole assertion
    /// set refuted (RED suite S2). `abs(x) >= 0` and `(mod x k) >= 0` are the
    /// same disease: bounded-below terms with a fake "coefficient" of 1. Affine
    /// transparency is therefore restricted to `+`/`-`, and to `*` ONLY when v
    /// occurs in exactly one factor (v·v is quadratic); `div`/`mod`/`abs` are
    /// non-affine in their argument (floor steps / clamping break the
    /// crosses-zero argument entirely). Fail-open: a skipped binder just means
    /// no rewrite.
    fn var_under_nonarith(&self, root: TermId, v: TermId) -> bool {
        // stack of (term, currently-under-a-non-affine-position)
        let mut stack = vec![(root, false)];
        while let Some((t, under)) = stack.pop() {
            if t == v {
                if under {
                    return true;
                }
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let affine = match sym.name() {
                        "+" | "-" => true,
                        "*" => {
                            // Affine in v only when v occurs in AT MOST ONE factor;
                            // v in two factors is (at least) quadratic in v.
                            args.iter()
                                .filter(|&&a| self.term_contains_id(a, v))
                                .count()
                                <= 1
                        }
                        _ => false,
                    };
                    let child_under = under || !affine;
                    for &a in args {
                        stack.push((a, child_under));
                    }
                }
                TermData::Not(i) => stack.push((*i, true)),
                TermData::Ite(c, a, b) => {
                    stack.push((*c, true));
                    stack.push((*a, true));
                    stack.push((*b, true));
                }
                _ => {}
            }
        }
        false
    }

    /// Substitute every Int-sorted `Var` in `term` with 0 (folding) and return the
    /// resulting integer constant, or `None` if a non-constant residue remains
    /// (e.g. an uninterpreted application). Used to read a v-free coefficient term
    /// reliably regardless of which other free variables it mentions.
    fn int_const_zeroing_vars(&mut self, term: TermId) -> Option<num_bigint::BigInt> {
        let mut vars: Vec<TermId> = Vec::new();
        let mut stack = vec![term];
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let is_int = matches!(self.ctx.terms.sort(t), ay_core::Sort::Int);
            match self.ctx.terms.get(t) {
                // A free Int atom (a bound/free Var or a 0-ary declared constant)
                // is independent of the binder's coefficient, so zero it.
                TermData::Var(_, _) if is_int => {
                    if !vars.contains(&t) {
                        vars.push(t);
                    }
                }
                // An Int-sorted application: recurse into ARITHMETIC operators
                // (their args may hold the binder/atoms), but treat any OTHER Int
                // app (a declared 0-ary constant, an uninterpreted `(g ..)`, a
                // `seq.len`, etc.) as an OPAQUE atom and zero it. Since this is
                // called on `d[v:=1]`/`d[v:=0]` — the binder is already substituted
                // out — every such app is binder-free, so zeroing it is exact for
                // the v-coefficient and lets `g(-1,b-y) - z` resolve coeff -1.
                TermData::App(sym, args)
                    if is_int && matches!(sym.name(), "+" | "-" | "*" | "div" | "mod" | "abs") =>
                {
                    stack.extend(args.iter().copied());
                }
                TermData::App(_, _) if is_int => {
                    if !vars.contains(&t) {
                        vars.push(t);
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let mut t = term;
        for v in vars {
            t = self.subst_term(t, v, zero);
        }
        match self.ctx.terms.get(t) {
            TermData::Const(ay_core::Constant::Int(n)) => Some(n.clone()),
            _ => None,
        }
    }

    /// For `(forall vars. (or operands))`: when EVERY binder-dependent operand is a
    /// binder-infeasible linear equality, return `(or <binder-independent operands>)`
    /// (or `false` if none remain) — the universal of the infeasible disjuncts is
    /// false (finite single-point exceptions can't cover the infinite Int domain),
    /// so it drops out. Returns `None` (keep the forall) if the body is not an `or`,
    /// nothing infeasible drops, or a binder-dependent operand cannot be proven
    /// infeasible. Computing the result here — rather than hoisting `(∀v.(or Ai))`
    /// into a disjunction — avoids leaving a forall in a non-conjunctive position,
    /// where the instantiation loop conjoins instances unsoundly (#quant-or-infeasible).
    fn forall_or_drop_infeasible_disjuncts(
        &mut self,
        body: TermId,
        vars: &[(String, ay_core::Sort)],
    ) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(body).clone() else {
            return None;
        };
        if sym.name() != "or" || args.len() < 2 {
            return None;
        }
        let mut indep: Vec<TermId> = Vec::new();
        let mut dropped_any = false;
        for op in args {
            let mentions = vars.iter().any(|(n, _)| self.term_mentions_name(op, n));
            if !mentions {
                indep.push(op);
            } else if self.atom_is_binder_infeasible(op, vars, false) {
                // EQUALITY disjuncts only: an infeasible equality is true at <=1
                // point, so a finite set of them can't cover the infinite domain
                // and `(forall v. (or eqs))` is false. An INEQUALITY is true on a
                // half-line, so dropping it would be UNSOUND (e.g.
                // `(forall z. (or (> z 5) (<= z 6)))` is TRUE) — excluded here.
                dropped_any = true;
            } else {
                return None;
            }
        }
        if !dropped_any {
            return None;
        }
        Some(if indep.is_empty() {
            self.ctx.terms.mk_bool(false)
        } else if indep.len() == 1 {
            indep[0]
        } else {
            self.ctx.terms.mk_or(indep)
        })
    }

    /// Find the hash-consed `TermData::Var(name, _)` TermId for binder `name`
    /// inside `root` (all occurrences of a bound var in a body share one TermId).
    fn find_bound_var_id(&self, root: TermId, name: &str) -> Option<TermId> {
        let mut stack = vec![root];
        let mut seen: ay_core::kani_compat::DetHashSet<TermId> = Default::default();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(n, _) if n == name => return Some(t),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(i) => stack.push(*i),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(*v);
                    }
                    stack.push(*b);
                }
                _ => {}
            }
        }
        None
    }

    fn drop_unused_bound_vars(&mut self, term: TermId) -> TermId {
        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.drop_unused_bound_vars(a))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = self.ctx.terms.sort(term).clone();
                    self.ctx.terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let ni = self.drop_unused_bound_vars(inner);
                if ni == inner {
                    term
                } else {
                    self.ctx.terms.mk_not(ni)
                }
            }
            TermData::Ite(c, t, e) => {
                let (nc, nt, ne) = (
                    self.drop_unused_bound_vars(c),
                    self.drop_unused_bound_vars(t),
                    self.drop_unused_bound_vars(e),
                );
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    self.ctx.terms.mk_ite(nc, nt, ne)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let nb = self.drop_unused_bound_vars(body);
                let kept: Vec<(String, ay_core::Sort)> = vars
                    .iter()
                    .filter(|(n, _)| self.term_mentions_name(nb, n))
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    return nb;
                }
                if kept.len() == vars.len() && nb == body {
                    return term;
                }
                let new_triggers = self.retain_quant_triggers(&triggers, &vars, &kept);
                self.ctx
                    .terms
                    .mk_forall_with_triggers(kept, nb, new_triggers)
            }
            TermData::Exists(vars, body, triggers) => {
                let nb = self.drop_unused_bound_vars(body);
                let kept: Vec<(String, ay_core::Sort)> = vars
                    .iter()
                    .filter(|(n, _)| self.term_mentions_name(nb, n))
                    .cloned()
                    .collect();
                if kept.is_empty() {
                    return nb;
                }
                if kept.len() == vars.len() && nb == body {
                    return term;
                }
                let new_triggers = self.retain_quant_triggers(&triggers, &vars, &kept);
                self.ctx
                    .terms
                    .mk_exists_with_triggers(kept, nb, new_triggers)
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(n, v)| (n.clone(), self.drop_unused_bound_vars(*v)))
                    .collect();
                let nb = self.drop_unused_bound_vars(body);
                if new_bindings == bindings && nb == body {
                    term
                } else {
                    self.ctx.terms.mk_let(new_bindings, nb)
                }
            }
            _ => term,
        }
    }

    /// Keep only trigger groups whose every term avoids any DROPPED binder name
    /// (a trigger referencing an eliminated binder is invalid). Sound either way
    /// — triggers are E-matching hints, not semantics.
    fn retain_quant_triggers(
        &self,
        triggers: &[Vec<TermId>],
        all_vars: &[(String, ay_core::Sort)],
        kept: &[(String, ay_core::Sort)],
    ) -> Vec<Vec<TermId>> {
        let dropped: Vec<&str> = all_vars
            .iter()
            .filter(|(n, _)| !kept.iter().any(|(k, _)| k == n))
            .map(|(n, _)| n.as_str())
            .collect();
        triggers
            .iter()
            .filter(|grp| {
                grp.iter()
                    .all(|&t| !dropped.iter().any(|d| self.term_mentions_name(t, d)))
            })
            .cloned()
            .collect()
    }

    /// True when `name` occurs as a `Var` anywhere in `term`. Does not stop at
    /// shadowing inner quantifiers — that only CONSERVES the binder (never wrongly
    /// drops it), so the rewrite stays sound.
    fn term_mentions_name(&self, term: TermId, name: &str) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Var(n, _) => n == name,
            TermData::App(_, args) => args.iter().any(|&a| self.term_mentions_name(a, name)),
            TermData::Not(i) => self.term_mentions_name(*i, name),
            TermData::Ite(c, t, e) => {
                self.term_mentions_name(*c, name)
                    || self.term_mentions_name(*t, name)
                    || self.term_mentions_name(*e, name)
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => {
                self.term_mentions_name(*b, name)
            }
            TermData::Let(bindings, b) => {
                bindings
                    .iter()
                    .any(|(_, v)| self.term_mentions_name(*v, name))
                    || self.term_mentions_name(*b, name)
            }
            _ => false,
        }
    }

    /// `(= A (* k T))`: true when `A` is an Int constant, the product side is
    /// `(* k _)` with `k` an Int constant, `|k| >= 2`, and `k ∤ A` — so there is no
    /// integer `T` making the equality hold. Exact infeasibility over the integers.
    fn int_eq_divis_infeasible(&self, const_side: TermId, prod_side: TermId) -> bool {
        use num_traits::Zero;
        let a = match self.ctx.terms.get(const_side) {
            TermData::Const(ay_core::Constant::Int(n)) => n.clone(),
            _ => return false,
        };
        let margs = match self.ctx.terms.get(prod_side) {
            TermData::App(sym, margs) if sym.name() == "*" && margs.len() == 2 => margs.clone(),
            _ => return false,
        };
        for k_id in margs {
            if let TermData::Const(ay_core::Constant::Int(k)) = self.ctx.terms.get(k_id) {
                // |k| >= 2  <=>  k not in {-1, 0, 1}
                let unit_or_zero = k.is_zero()
                    || *k == num_bigint::BigInt::from(1)
                    || *k == num_bigint::BigInt::from(-1);
                if !unit_or_zero && (&a % k) != num_bigint::BigInt::zero() {
                    return true;
                }
            }
        }
        false
    }

    fn fold_linear_eqs(
        &mut self,
        term: TermId,
        provenance: &mut Vec<QuantifiedLinearNnfProvenance>,
    ) -> TermId {
        match self.ctx.terms.get(term).clone() {
            // Fold an Int comparison when `mk_sub` cancels like variable terms,
            // leaving a constant side difference whose truth can be evaluated.
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | ">" | ">=" | "<" | "<=")
                    && args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int) =>
            {
                let diff = self.ctx.terms.mk_sub(vec![args[0], args[1]]); // a - b
                if let TermData::Const(ay_core::Constant::Int(n)) = self.ctx.terms.get(diff) {
                    use num_traits::Zero;
                    let v = n.clone();
                    let truth = match sym.name() {
                        "=" => v.is_zero(),
                        ">" => v > num_bigint::BigInt::zero(),
                        ">=" => v >= num_bigint::BigInt::zero(),
                        "<" => v < num_bigint::BigInt::zero(),
                        "<=" => v <= num_bigint::BigInt::zero(),
                        _ => unreachable!(),
                    };
                    return self.ctx.terms.mk_bool(truth);
                }
                // Integer divisibility infeasibility: `(= A (* k T))` with `A`,`k`
                // Int constants, `|k| >= 2`, `k ∤ A` has NO integer solution for any
                // `T` — fold to false. Exact over Int (NOT over Real). Lets the dead
                // existential-witness branch collapse (`(= -1 (* 3 q2))` -> false).
                if sym.name() == "="
                    && (self.int_eq_divis_infeasible(args[0], args[1])
                        || self.int_eq_divis_infeasible(args[1], args[0]))
                {
                    return self.ctx.terms.mk_bool(false);
                }
                term
            }
            // NNF: push negations to atoms (De Morgan + comparison flips) so the
            // downstream FM projection / instantiation see a flat conjunction of
            // comparison atoms rather than `(not (or (distinct a b) p))`.
            TermData::Not(inner) => match self.ctx.terms.get(inner).clone() {
                TermData::Not(inner2) => self.fold_linear_eqs(inner2, provenance),
                TermData::App(s, a) if s.name() == "and" => {
                    let neg: Vec<TermId> = a.iter().map(|&x| self.ctx.terms.mk_not(x)).collect();
                    let or = self.ctx.terms.mk_or(neg);
                    self.fold_linear_eqs(or, provenance)
                }
                TermData::App(s, a) if s.name() == "or" => {
                    let neg: Vec<TermId> = a.iter().map(|&x| self.ctx.terms.mk_not(x)).collect();
                    let and = self.ctx.terms.mk_and(neg);
                    self.fold_linear_eqs(and, provenance)
                }
                TermData::App(s, a)
                    if a.len() == 2 && matches!(self.ctx.terms.sort(a[0]), ay_core::Sort::Int) =>
                {
                    let flipped = match s.name() {
                        ">" => Some(self.ctx.terms.mk_le(a[0], a[1])),
                        ">=" => Some(self.ctx.terms.mk_lt(a[0], a[1])),
                        "<" => Some(self.ctx.terms.mk_ge(a[0], a[1])),
                        "<=" => Some(self.ctx.terms.mk_lt(a[1], a[0])),
                        "distinct" => Some(self.ctx.terms.mk_eq(a[0], a[1])),
                        _ => None,
                    };
                    match flipped {
                        Some(f) => self.fold_linear_eqs(f, provenance),
                        None => {
                            let i = self.fold_linear_eqs(inner, provenance);
                            self.ctx.terms.mk_not(i)
                        }
                    }
                }
                _ => {
                    let i = self.fold_linear_eqs(inner, provenance);
                    self.ctx.terms.mk_not(i)
                }
            },
            TermData::App(sym, args) if matches!(sym.name(), "and" | "or") => {
                let new: Vec<TermId> = args
                    .iter()
                    .map(|&a| self.fold_linear_eqs(a, provenance))
                    .collect();
                if sym.name() == "and" {
                    self.ctx.terms.mk_and(new)
                } else {
                    self.ctx.terms.mk_or(new)
                }
            }
            TermData::App(sym, args) if sym.name() == "=>" && args.len() == 2 => {
                let a = self.fold_linear_eqs(args[0], provenance);
                let b = self.fold_linear_eqs(args[1], provenance);
                self.ctx.terms.mk_implies(a, b)
            }
            TermData::Ite(c, t, e) => {
                let c2 = self.fold_linear_eqs(c, provenance);
                let t2 = self.fold_linear_eqs(t, provenance);
                let e2 = self.fold_linear_eqs(e, provenance);
                self.ctx.terms.mk_ite(c2, t2, e2)
            }
            TermData::Forall(vars, body, trig) => {
                let b = self.fold_linear_eqs(body, provenance);
                if b == body {
                    term
                } else {
                    let normalized_forall = self.ctx.terms.mk_forall_with_triggers(vars, b, trig);
                    let terms = &mut self.ctx.terms;
                    terms.copy_quantifier_metadata(term, normalized_forall);
                    provenance.push(QuantifiedLinearNnfProvenance {
                        source_forall: term,
                        normalized_forall,
                    });
                    normalized_forall
                }
            }
            TermData::Exists(vars, body, trig) => {
                let b = self.fold_linear_eqs(body, provenance);
                if b == body {
                    term
                } else {
                    self.ctx.terms.mk_exists_with_triggers(vars, b, trig)
                }
            }
            _ => term,
        }
    }

    /// Instantiation values for a single `Int` binder derived by E-MATCHING the
    /// body's UF applications against ground UF applications in `ground`.
    ///
    /// For a body application `(uf a)` where `a` is linear in the binder and a
    /// ground `(uf g)` exists, return the binder value that makes `a == g` (so
    /// congruence merges the two): `a == bound ⟹ g`; `a == (+ bound e) ⟹ (- g
    /// e)`; `a == (- bound e) ⟹ (+ g e)` (and symmetric `+`). Used to reach the
    /// forall-over-UF-range contradiction a concrete value window cannot.
    fn ematching_binder_values(
        &mut self,
        body: TermId,
        bound_name: &str,
        ground: &[TermId],
    ) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();

        // Ground single-argument UF applications: (uf_name, arg).
        let mut ground_uf: Vec<(String, TermId)> = Vec::new();
        let mut gseen: HashSet<TermId> = HashSet::default();
        let mut gstack: Vec<TermId> = ground.to_vec();
        while let Some(t) = gstack.pop() {
            if !gseen.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t).clone() {
                if args.len() == 1
                    && !is_pure_arith_bool_symbol(sym.name())
                    && !self.term_mentions_bound_var(args[0], &bound_set)
                {
                    ground_uf.push((sym.name().to_string(), args[0]));
                }
                for a in args {
                    gstack.push(a);
                }
            }
        }
        if ground_uf.is_empty() {
            return Vec::new();
        }

        // Body single-argument UF applications whose arg mentions the binder.
        let mut values: Vec<TermId> = Vec::new();
        let mut bseen: HashSet<TermId> = HashSet::default();
        let mut bstack = vec![body];
        while let Some(t) = bstack.pop() {
            if !bseen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if args.len() == 1
                        && !is_pure_arith_bool_symbol(sym.name())
                        && self.term_mentions_bound_var(args[0], &bound_set)
                    {
                        for (gname, garg) in &ground_uf {
                            if *gname != sym.name() {
                                continue;
                            }
                            if let Some(v) = self.binder_value_for_arg(args[0], bound_name, *garg) {
                                values.push(v);
                            }
                        }
                    }
                    for a in args {
                        bstack.push(a);
                    }
                }
                TermData::Not(inner) => bstack.push(inner),
                TermData::Ite(c, th, e) => {
                    bstack.push(c);
                    bstack.push(th);
                    bstack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        bstack.push(v);
                    }
                    bstack.push(b);
                }
                _ => {}
            }
        }
        values
    }

    /// Ground witness-point bases: for each `Int`-sorted Skolem application
    /// `(__ay_sk_* a)` in `body` whose argument mentions the binder, substitute
    /// the binder with a few small concrete values to obtain GROUND Skolem terms
    /// `(__ay_sk_* c)`. Instantiating the binder near these aligns a whole-range
    /// universal conjunct with the existential witness point.
    fn skolem_app_bases(&mut self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_SK_APPS: usize = 3;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();

        // Collect Int-sorted Skolem applications whose arg mentions the binder.
        let mut sk_apps: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if sym.name().starts_with("__ay_sk_")
                        && matches!(self.ctx.terms.sort(t), ay_core::Sort::Int)
                        && self.term_mentions_bound_var(t, &bound_set)
                        && sk_apps.len() < MAX_SK_APPS
                        && !sk_apps.contains(&t)
                    {
                        sk_apps.push(t);
                    }
                    stack.extend(args);
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, e) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(v);
                    }
                    stack.push(b);
                }
                _ => {}
            }
        }
        if sk_apps.is_empty() {
            return Vec::new();
        }

        let mut out: Vec<TermId> = Vec::new();
        for &sk in &sk_apps {
            for c in [-1i64, 0, 1] {
                let cval = self.ctx.terms.mk_int(num_bigint::BigInt::from(c));
                let mut subst: HashMap<String, TermId> = HashMap::default();
                subst.insert(bound_name.to_string(), cval);
                let ground_sk = crate::ematching::subst_vars(&mut self.ctx.terms, sk, &subst);
                if !out.contains(&ground_sk) {
                    out.push(ground_sk);
                }
            }
        }
        out
    }

    /// Distinct free `Int` variables occurring in `body` other than the binder
    /// `bound_name` (outer-quantified vars / Skolem constants), capped to a small
    /// number. Used as bases for OFFSET instantiations of the binder.
    fn free_int_binder_bases(&self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_BASES: usize = 4;
        let mut out: Vec<TermId> = Vec::new();
        let mut seen_terms: HashSet<TermId> = HashSet::default();
        let mut seen_names: HashSet<String> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::Var(name, _) => {
                    if name != bound_name
                        && matches!(self.ctx.terms.sort(t), ay_core::Sort::Int)
                        && seen_names.insert(name)
                        && seen_terms.insert(t)
                    {
                        out.push(t);
                        if out.len() >= MAX_BASES {
                            break;
                        }
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, e) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(v);
                    }
                    stack.push(b);
                }
                _ => {}
            }
        }
        out
    }

    /// Boundary values of the binder: for each `Int` comparison atom in `body`
    /// that is linear in the binder with UNIT coefficient, the value at which the
    /// atom flips (`a < b` over `q0-2 < 3*c0` flips at `q0 = 3*c0 + 2`; `sk0-q1 >
    /// c0` flips at `q1 = sk0 - c0`). The falsifying instantiation of a universal
    /// over an unbounded binder is at (or just past) such a boundary — possibly a
    /// scaled/combined expression of the free variables that the per-variable
    /// offset bases cannot reach. Instantiating the binder at `boundary + k` makes
    /// the critical atom flip, exposing the conflict. Real instances ⇒ sound.
    fn atom_boundary_binder_bases(&mut self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_BASES: usize = 6;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();
        let zero = self.ctx.terms.mk_int(num_bigint::BigInt::from(0));
        let one = self.ctx.terms.mk_int(num_bigint::BigInt::from(1));
        let mut one_subst: HashMap<String, TermId> = HashMap::default();
        one_subst.insert(bound_name.to_string(), one);
        let mut zero_subst: HashMap<String, TermId> = HashMap::default();
        zero_subst.insert(bound_name.to_string(), zero);

        // Collect comparison atoms (any structural position).
        let mut atoms: Vec<TermId> = Vec::new();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t).clone() {
                TermData::App(sym, args) => {
                    if args.len() == 2
                        && matches!(sym.name(), "=" | ">" | ">=" | "<" | "<=")
                        && matches!(self.ctx.terms.sort(args[0]), ay_core::Sort::Int)
                        && self.term_mentions_bound_var(t, &bound_set)
                    {
                        atoms.push(t);
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(inner),
                TermData::Ite(c, th, e) => {
                    stack.push(c);
                    stack.push(th);
                    stack.push(e);
                }
                TermData::Let(binds, b) => {
                    for (_, v) in binds {
                        stack.push(v);
                    }
                    stack.push(b);
                }
                _ => {}
            }
        }

        let mut out: Vec<TermId> = Vec::new();
        for atom in atoms {
            let TermData::App(_, args) = self.ctx.terms.get(atom).clone() else {
                continue;
            };
            let d = self.ctx.terms.mk_sub(vec![args[0], args[1]]); // a - b
            let d1 = crate::ematching::subst_vars(&mut self.ctx.terms, d, &one_subst);
            let d0 = crate::ematching::subst_vars(&mut self.ctx.terms, d, &zero_subst);
            let coeff = self.ctx.terms.mk_sub(vec![d1, d0]);
            let TermData::Const(ay_core::Constant::Int(c)) = self.ctx.terms.get(coeff) else {
                continue;
            };
            let c = c.clone();
            use num_traits::{One, Zero};
            // d = c*binder + rest (rest = d0); flip at binder = -rest/c.
            let boundary = if c.is_one() {
                self.ctx.terms.mk_sub(vec![zero, d0]) // -rest
            } else if c == num_bigint::BigInt::from(-1) {
                d0 // rest
            } else if !c.is_zero() {
                // DIVISIBILITY boundary: integer point nearest the rational flip
                // `-rest/c`, via `div`. The ±k window around it (in the caller)
                // covers the residue classes for small |c|. `div`'s constant
                // divisor keeps this a real integer instantiation point.
                let (num, den) = if c > num_bigint::BigInt::zero() {
                    (self.ctx.terms.mk_sub(vec![zero, d0]), c.clone()) // (-rest)/c
                } else {
                    (d0, -c.clone()) // rest/|c|
                };
                let den_t = self.ctx.terms.mk_int(den);
                self.ctx.terms.mk_div(num, den_t)
            } else {
                continue;
            };
            if !out.contains(&boundary) {
                out.push(boundary);
                if out.len() >= MAX_BASES {
                    break;
                }
            }
        }
        out
    }

    /// Pairwise and limited-triple sums/differences of the binder's anchor
    /// expressions (free Int variables, binder-independent UF values, atom
    /// boundaries). The point at which SEVERAL atoms are simultaneously violated
    /// can be a linear COMBINATION of their individual boundaries that no single
    /// anchor reaches; instantiating the binder there is a real universal instance,
    /// so any resulting UNSAT is sound. Capped to keep the instance set bounded.
    fn combination_binder_bases(&mut self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_ANCHORS: usize = 5;
        const MAX_OUT: usize = 28;

        let mut anchors: Vec<TermId> = self.free_int_binder_bases(body, bound_name);
        for u in self.uf_value_binder_bases(body, bound_name) {
            if !anchors.contains(&u) {
                anchors.push(u);
            }
        }
        for b in self.atom_boundary_binder_bases(body, bound_name) {
            if !anchors.contains(&b) {
                anchors.push(b);
            }
        }
        anchors.truncate(MAX_ANCHORS);
        if anchors.len() < 2 {
            return Vec::new();
        }

        let mut seen: HashSet<TermId> = HashSet::default();
        let mut out: Vec<TermId> = Vec::new();
        // Pairwise: a_i + a_j and a_i - a_j (i < j; differences both orders).
        for i in 0..anchors.len() {
            for j in (i + 1)..anchors.len() {
                let combos = [
                    self.ctx.terms.mk_add(vec![anchors[i], anchors[j]]),
                    self.ctx.terms.mk_sub(vec![anchors[i], anchors[j]]),
                    self.ctx.terms.mk_sub(vec![anchors[j], anchors[i]]),
                ];
                for cmb in combos {
                    if seen.insert(cmb) && out.len() < MAX_OUT {
                        out.push(cmb);
                    }
                }
            }
        }
        // Limited triples: a_i + a_j - a_k over the first three anchors only.
        if anchors.len() >= 3 {
            let (a0, a1, a2) = (anchors[0], anchors[1], anchors[2]);
            let sum01 = self.ctx.terms.mk_add(vec![a0, a1]);
            let t0 = self.ctx.terms.mk_sub(vec![sum01, a2]);
            let sum02 = self.ctx.terms.mk_add(vec![a0, a2]);
            let t1 = self.ctx.terms.mk_sub(vec![sum02, a1]);
            let sum12 = self.ctx.terms.mk_add(vec![a1, a2]);
            let t2 = self.ctx.terms.mk_sub(vec![sum12, a0]);
            for cmb in [t0, t1, t2] {
                if seen.insert(cmb) && out.len() < MAX_OUT {
                    out.push(cmb);
                }
            }
        }
        out
    }

    /// Binder-INDEPENDENT `Int`-sorted uninterpreted/non-arith application terms
    /// in `body` (e.g. `(f 3)`, `(f sk0)` where the argument does not mention the
    /// binder). Their values are fixed unknown integers; the falsifying point of a
    /// universal over an unbounded binder is frequently AT one of these values
    /// (`q1 = f(3)`) or just past its negation (`q1 = 1 - f(sk0)` from `f(sk0) >
    /// -q1`). Instantiating the binder at `±base + k` turns the alignment into two
    /// concrete instances whose conjunction is contradictory — a SOUND refutation
    /// (real instances of the universal), no abstraction needed.
    fn uf_value_binder_bases(&self, body: TermId, bound_name: &str) -> Vec<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        const MAX_BASES: usize = 4;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();
        let mut out: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![body];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if let TermData::App(sym, args) = self.ctx.terms.get(t).clone() {
                let is_uf = !is_pure_arith_bool_symbol(sym.name());
                if is_uf
                    && matches!(self.ctx.terms.sort(t), ay_core::Sort::Int)
                    && !self.term_mentions_bound_var(t, &bound_set)
                    && seen.insert(t)
                {
                    out.push(t);
                    if out.len() >= MAX_BASES {
                        break;
                    }
                }
                stack.extend(args.iter().copied());
            } else {
                match self.ctx.terms.get(t).clone() {
                    TermData::Not(inner) => stack.push(inner),
                    TermData::Ite(c, th, e) => {
                        stack.push(c);
                        stack.push(th);
                        stack.push(e);
                    }
                    TermData::Let(binds, b) => {
                        for (_, v) in binds {
                            stack.push(v);
                        }
                        stack.push(b);
                    }
                    _ => {}
                }
            }
        }
        out
    }

    /// Solve `a[bound = v] == garg` for `v` when `a` is linear in `bound` with
    /// unit coefficient. Returns `None` for non-linear / higher-degree shapes.
    fn binder_value_for_arg(
        &mut self,
        a: TermId,
        bound_name: &str,
        garg: TermId,
    ) -> Option<TermId> {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let bound_set: HashSet<String> = std::iter::once(bound_name.to_string()).collect();
        let is_bound = |this: &Self, t: TermId| matches!(this.ctx.terms.get(t), TermData::Var(n, _) if n == bound_name);
        match self.ctx.terms.get(a).clone() {
            TermData::Var(n, _) if n == bound_name => Some(garg),
            TermData::App(sym, args) if sym.name() == "+" && args.len() == 2 => {
                if is_bound(self, args[0]) && !self.term_mentions_bound_var(args[1], &bound_set) {
                    Some(self.ctx.terms.mk_sub(vec![garg, args[1]]))
                } else if is_bound(self, args[1])
                    && !self.term_mentions_bound_var(args[0], &bound_set)
                {
                    Some(self.ctx.terms.mk_sub(vec![garg, args[0]]))
                } else {
                    None
                }
            }
            TermData::App(sym, args) if sym.name() == "-" && args.len() == 2 => {
                if is_bound(self, args[0]) && !self.term_mentions_bound_var(args[1], &bound_set) {
                    Some(self.ctx.terms.mk_add(vec![garg, args[1]]))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// SOUNDNESS (#forall-alternation wrong-sat): decide whether a CEGQI
    /// "forall valid ⟹ SAT" disambiguation over `snapshot` is UNRELIABLE because
    /// the snapshot contains a skolemized-alternation `forall` with a
    /// WITNESS-INDEPENDENT arithmetic conjunct.
    ///
    /// When an existential under a universal is skolemized into a Skolem FUNCTION
    /// (`__ay_sk_*`) of the bound variable, the arithmetic CE search treats that
    /// application as an opaque per-instance value. That is harmless for a body
    /// like `(> sk(x) x)` — for every `x` the existential witness `sk(x)` is free
    /// to satisfy it, so the universal genuinely holds (this is the canonical
    /// SAT `(forall x (exists y (> y x)))`). It is UNSOUND, however, when the
    /// body also has a conjunct that mentions the bound variable but NO Skolem
    /// function: such a conjunct is a hard universal constraint no existential
    /// witness can repair, and CEGQI's ground-SAT certificate can miss its
    /// falsifying instantiation. Example: `(forall x (and (>= sk(x) (- x 5))
    /// (<= -6 x)))` from `(forall x (exists y (and (>= y (- x 5)) (<= -6 x))))`
    /// is UNSAT (the sk-free conjunct `(<= -6 x)` fails at x = -7), yet
    /// disambiguation reports SAT. Fail closed only in that precise shape, so the
    /// witness-driven SAT cases (`(> sk(x) x)`) keep deciding SAT.
    fn snapshot_has_witness_independent_skolem_alternation(&mut self, snapshot: &[TermId]) -> bool {
        let mut quants: Vec<TermId> = Vec::new();
        for &a in snapshot {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, a, &mut quants);
        }
        quants.into_iter().any(|q| {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(q).clone() else {
                return false;
            };
            let bound: ay_core::kani_compat::DetHashSet<String> =
                vars.iter().map(|(n, _)| n.clone()).collect();
            // CEGQI's arithmetic counterexample search is incomplete over the
            // bound variable when the body applies an uninterpreted / non-arith
            // function to it — whether a Skolem function `__ay_sk_*(x)` from a
            // skolemized inner existential, or a declared `(f x)`. Such an
            // application is treated as an opaque per-instance value, so the
            // "ground SAT ⟹ forall valid" verdict can miss a falsifying
            // instantiation.
            if !self.term_mentions_uninterpreted_of_bound_var(body, &bound) {
                return false;
            }
            let mut conjuncts = Vec::new();
            collect_and_conjuncts(&self.ctx.terms, body, &mut conjuncts);
            // A conjunct that constrains a bound variable but applies no
            // uninterpreted/non-arith function to it is WITNESS-INDEPENDENT: it is
            // a hard universal arithmetic constraint no existential witness (or
            // opaque UF value) can repair, so CEGQI's "valid" verdict over it is
            // unreliable — fail closed. The witness-driven shape `(> sk(x) x)` has
            // no such conjunct (its only constraint applies the UF to `x`), so it
            // keeps deciding SAT.
            conjuncts.into_iter().any(|c| {
                self.term_mentions_bound_var(c, &bound)
                    && !self.term_mentions_uninterpreted_of_bound_var(c, &bound)
            })
        })
    }

    /// Whether a restored universal applies a declared/non-Skolem opaque
    /// function to one of its bound variables (possibly through an interpreted
    /// argument such as `f(x + 1)`). A ground graph samples only finitely many
    /// points of such a function and is not, by itself, a total interpretation.
    fn restored_has_bound_dependent_non_skolem_application(&mut self) -> bool {
        let assertions = self.ctx.assertions.clone();
        let mut quants = Vec::new();
        for assertion in assertions {
            crate::ematching::collect_quantifiers(&mut self.ctx.terms, assertion, &mut quants);
        }
        quants.into_iter().any(|quant| {
            let TermData::Forall(vars, body, _) = self.ctx.terms.get(quant).clone() else {
                return false;
            };
            let bound: ay_core::kani_compat::DetHashSet<String> =
                vars.into_iter().map(|(name, _)| name).collect();
            self.term_mentions_non_skolem_uninterpreted_of_bound_var(body, &bound)
        })
    }

    fn term_mentions_non_skolem_uninterpreted_of_bound_var(
        &self,
        root: TermId,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if !is_pure_arith_bool_symbol(sym.name())
                        && !self.ctx.terms.is_skolem_symbol(sym.name())
                        && args
                            .iter()
                            .any(|&arg| self.term_mentions_bound_var(arg, bound))
                    {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.push(*condition);
                    stack.push(*then_term);
                    stack.push(*else_term);
                }
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                TermData::Const(_) | TermData::Var(_, _) => {}
                _ => {}
            }
        }
        false
    }

    /// True when `root` applies an uninterpreted or non-arithmetic function — any
    /// symbol that is NOT a builtin LIA/LRA/Bool operator (so a UF, Skolem
    /// function, array/seq/string/bv/datatype op) — to a subterm that mentions a
    /// bound variable from `bound`. Marks where CEGQI's arithmetic CE search
    /// loses completeness over the bound variable.
    fn term_mentions_uninterpreted_of_bound_var(
        &self,
        root: TermId,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if !is_pure_arith_bool_symbol(sym.name())
                        && self.term_mentions_bound_var(term, bound)
                    {
                        return true;
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }

    fn term_mentions_bound_var(
        &self,
        root: TermId,
        bound: &ay_core::kani_compat::DetHashSet<String>,
    ) -> bool {
        use ay_core::kani_compat::DetHashSet as HashSet;
        let mut visited: HashSet<TermId> = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Var(name, _) if bound.contains(name) => return true,
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    for (_, v) in bindings {
                        stack.push(*v);
                    }
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                _ => {}
            }
        }
        false
    }
}

/// Red zone size for `stacker::maybe_grow` in the de-Skolemization rebuild.
const DESKOLEM_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for the de-Skolemization rebuild.
const DESKOLEM_STACK_SIZE: usize = 1024 * 1024;

/// Rebuild the DE-SKOLEMIZED counterexample obligation of a post-Skolemization
/// CEGQI universal (#quantified-ce-lemma).
///
/// `quant` is the stored `forall x⃗. B(x⃗)` where `B = psi0[y⃗ := sk(x⃗)]` is
/// the Skolemized body of an original `forall x⃗ (exists y⃗ psi0)`; `inst` is
/// its CEGQI instantiator (supplying the binder → counterexample-variable map
/// `x⃗ ↦ e⃗`). Returns the obligation `L_q = forall y⃗. ¬psi0(y⃗, e⃗)` as
/// `(binders, rho)` with `rho = ¬psi0(y⃗, e⃗)` over fresh binder variables —
/// the lemma the stored ground CE lemma `¬psi0(sk(e⃗), e⃗)` can never encode
/// (the free Skolem application keeps it satisfiable). For a universal with NO
/// Skolem applications the binder list is empty and `rho` IS the stored ground
/// CE lemma.
///
/// # Exactness
///
/// Skolem symbols are registered at their single creation site
/// (`skolemize_quantifier_body` → `TermStore::mark_skolem_symbol`) and are
/// globally fresh, so every occurrence in `B` originates from the one
/// substitution `y⃗ ↦ sk(x⃗)` on `psi0` — replacing each distinct Skolem
/// application by a fresh bound variable recovers `psi0` exactly (up to
/// hash-consing).
///
/// # v1 gates (fail-closed `None` on anything unrecognized)
///
/// - 1 or 2 binders, all `Int`, each with a CE variable;
/// - body within the `Const`/`Var`/`App`/`Not`/`Ite` fragment, quantifier-free;
/// - at most 2 distinct Skolem applications, each `Int`-sorted with every
///   argument a CE variable (`sk(e⃗)` — the shape the Skolemizer produces);
/// - NO Skolem *constant* occurrences: a Skolem constant stems from an OUTER
///   existential (`exists y forall x. psi`), and de-Skolemizing it into a
///   universal binder would be the invalid `∀∃ ⟸ ∃∀` quantifier swap.
pub(super) fn rebuild_quantified_ce_lemma(
    terms: &mut ay_core::TermStore,
    quant: TermId,
    inst: &CegqiInstantiator,
) -> Option<(Vec<(String, ay_core::Sort)>, TermId)> {
    use ay_core::kani_compat::DetHashSet as HashSet;
    const MAX_QUANT_BINDERS: usize = 2;
    const MAX_SKOLEM_APPS: usize = 2;

    let TermData::Forall(vars, body, _) = terms.get(quant).clone() else {
        return None;
    };
    if vars.is_empty() || vars.len() > MAX_QUANT_BINDERS {
        return None;
    }
    if !vars
        .iter()
        .all(|(_, sort)| matches!(sort, ay_core::Sort::Int))
    {
        return None;
    }
    let ce = inst.ce_variables();
    if !vars.iter().all(|(name, _)| ce.contains_key(name)) {
        return None;
    }
    let ce_vars: HashSet<TermId> = ce.values().copied().collect();

    // B(e⃗): the body at the counterexample variables — exactly the term the
    // stored CE lemma negates.
    let body_e = crate::ematching::subst_vars(terms, body, ce);

    // Collect the distinct registered-Skolem applications, enforcing the v1
    // fragment/provenance gates along the walk.
    let mut skolem_apps: Vec<TermId> = Vec::new();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack = vec![body_e];
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t).clone() {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if terms.is_skolem_symbol(&name) {
                    return None; // Skolem constant: outer existential — fail closed.
                }
            }
            TermData::App(sym, args) => {
                if terms.is_skolem_symbol(sym.name()) {
                    if matches!(terms.sort(t), ay_core::Sort::Int)
                        && !args.is_empty()
                        && args.iter().all(|arg| ce_vars.contains(arg))
                    {
                        if !skolem_apps.contains(&t) {
                            if skolem_apps.len() >= MAX_SKOLEM_APPS {
                                return None;
                            }
                            skolem_apps.push(t);
                        }
                        // Arguments are CE variables — nothing further below.
                        continue;
                    }
                    return None; // unrecognized Skolem occurrence — fail closed.
                }
                stack.extend(args);
            }
            TermData::Not(inner) => stack.push(inner),
            TermData::Ite(c, a, b) => {
                stack.push(c);
                stack.push(a);
                stack.push(b);
            }
            // Let bindings, nested quantifiers, or any future variant are
            // outside the exactly-rebuildable v1 fragment.
            _ => return None,
        }
    }

    let mut binders: Vec<(String, ay_core::Sort)> = Vec::with_capacity(skolem_apps.len());
    let mut replace: HashMap<TermId, TermId> = HashMap::default();
    for &app in &skolem_apps {
        let name = terms.mk_internal_symbol("deskolem");
        let fresh = terms.mk_var(name.clone(), ay_core::Sort::Int);
        binders.push((name, ay_core::Sort::Int));
        replace.insert(app, fresh);
    }
    let psi0_e = replace_mapped_terms(terms, body_e, &replace);
    Some((binders, terms.mk_not(psi0_e)))
}

/// Replace every occurrence of the map's key TERMS by their value terms,
/// rebuilding the containing structure. Total on the
/// `Const`/`Var`/`App`/`Not`/`Ite` fragment `rebuild_quantified_ce_lemma`
/// gates to; other variants are returned unchanged (the caller has already
/// failed closed on them). Uses `stacker::maybe_grow` for stack safety.
fn replace_mapped_terms(
    terms: &mut ay_core::TermStore,
    term: TermId,
    map: &HashMap<TermId, TermId>,
) -> TermId {
    stacker::maybe_grow(DESKOLEM_STACK_RED_ZONE, DESKOLEM_STACK_SIZE, || {
        if let Some(&mapped) = map.get(&term) {
            return mapped;
        }
        match terms.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| replace_mapped_terms(terms, arg, map))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let new_inner = replace_mapped_terms(terms, inner, map);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not(new_inner)
                }
            }
            TermData::Ite(c, a, b) => {
                let nc = replace_mapped_terms(terms, c, map);
                let na = replace_mapped_terms(terms, a, map);
                let nb = replace_mapped_terms(terms, b, map);
                if nc == c && na == a && nb == b {
                    term
                } else {
                    terms.mk_ite(nc, na, nb)
                }
            }
            _ => term,
        }
    }) // stacker::maybe_grow
}

#[allow(clippy::panic)]
#[cfg(test)]
mod rebuild_tests {
    use super::*;
    use ay_core::term::Symbol;
    use ay_core::{Sort, TermStore};
    use num_rational::BigRational;

    fn load_assertions(smt: &str) -> Executor {
        let commands = ay_frontend::parse(smt).expect("parse qpf fixture");
        let mut exec = Executor::new();
        for command in &commands {
            let output = exec.execute(command).expect("execute qpf fixture");
            assert!(output.is_none(), "fixture must not contain a query command");
        }
        exec
    }

    fn checked_model_transaction_fixture() -> (Executor, Vec<TermId>) {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= x 1))
            "#,
        );
        let roots = exec.ctx.assertions.clone();
        let sentinel = roots[0];

        let mut outer_model = Model::empty();
        outer_model
            .install_quantified_certificate_pins(
                &exec.ctx.terms,
                [(sentinel, EvalValue::Bool(false))],
            )
            .expect("outer sentinel pin can be model-bound");
        exec.last_model = Some(outer_model);
        exec.last_model_validated = true;
        let validation_stats = crate::executor::model::ValidationStats {
            checked: 7,
            total: 11,
            ..Default::default()
        };
        exec.last_validation_stats = Some(validation_stats);
        exec.dt_theory_model = Some(ay_dt::DtModel::default());
        exec.dt_validation_wants_egraph = true;
        exec.dt_egraph_building.set(true);
        exec.recorded_var_substitutions.insert(sentinel, sentinel);
        exec.model_validation_delegated_assertions.insert(sentinel);
        exec.last_result = Some(SolveResult::Unknown);
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        exec.defer_model_validation = true;
        exec.last_statistics.conflicts = 41;
        exec.last_statistics
            .set_string("checked-model.transaction", "outer");

        let evidence = crate::executor::mbqi::CheckedMbqiSatAuthority::for_test(&mut exec, &roots)
            .expect("outer sentinel model can be sealed");
        assert!(exec.install_mbqi_sat_authority(evidence));
        assert_checked_model_transaction_outer_state(&exec, &roots);
        (exec, roots)
    }

    fn assert_checked_model_transaction_outer_state(exec: &Executor, roots: &[TermId]) {
        let sentinel = roots[0];
        assert!(exec.last_model.is_some());
        assert!(exec.last_model_validated);
        assert_eq!(
            exec.last_validation_stats
                .as_ref()
                .map(|stats| (stats.checked, stats.total)),
            Some((7, 11))
        );
        assert!(exec.dt_theory_model.is_some());
        assert!(exec.dt_validation_wants_egraph);
        assert!(exec.dt_egraph_building.get());
        assert_eq!(exec.recorded_var_substitutions.len(), 1);
        assert_eq!(
            exec.recorded_var_substitutions.get(&sentinel),
            Some(&sentinel)
        );
        assert_eq!(exec.model_validation_delegated_assertions.len(), 1);
        assert!(exec
            .model_validation_delegated_assertions
            .contains(&sentinel));
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Incomplete));
        assert!(exec.defer_model_validation);
        assert_eq!(exec.last_statistics.conflicts, 41);
        assert_eq!(
            exec.last_statistics.get_string("checked-model.transaction"),
            Some("outer")
        );
        assert!(exec.mbqi_sat_cert_grant_active);
        assert_eq!(
            exec.current_quantified_sat_authority(roots),
            Some(CurrentQuantifiedSatAuthority::Mbqi)
        );
        let model = exec.last_model.as_ref().expect("outer sentinel model");
        assert_eq!(model.quantified_certificate_pin_count(), 1);
        assert_eq!(exec.evaluate_term(model, sentinel), EvalValue::Bool(false));
    }

    #[test]
    fn checked_model_transaction_rolls_back_mutated_postprocessor_decline() {
        let (mut exec, roots) = checked_model_transaction_fixture();
        let consumer_called = std::cell::Cell::new(false);

        let result = exec.with_checked_same_context_ground_model(
            roots.clone(),
            2_000,
            |executor, _checked_roots| {
                // Replacing x = 1's checked candidate with the empty model
                // makes the mandatory post-mutation root check fail. Scramble
                // the paired state too, so this tests the whole transaction
                // rather than only restoration of `last_model`.
                executor.last_model = Some(Model::empty());
                executor.last_model_validated = false;
                executor.last_validation_stats = None;
                executor.dt_theory_model = None;
                executor.dt_validation_wants_egraph = false;
                executor.dt_egraph_building.set(false);
                executor.recorded_var_substitutions.clear();
                executor.model_validation_delegated_assertions.clear();
                executor.last_result = Some(SolveResult::Sat);
                executor.last_unknown_reason = None;
                executor.defer_model_validation = false;
                executor.last_statistics.conflicts = 99;
                executor
                    .last_statistics
                    .set_string("checked-model.transaction", "mutated");
                Some(())
            },
            |_executor, _installed| {
                consumer_called.set(true);
                Some(())
            },
        );

        assert!(result.is_none());
        assert!(
            !consumer_called.get(),
            "a candidate that fails its post-mutation root check must not reach the consumer"
        );
        assert_checked_model_transaction_outer_state(&exec, &roots);
    }

    #[test]
    fn checked_model_transaction_rolls_back_consumer_decline_and_prior_mbqi_package() {
        let (mut exec, roots) = checked_model_transaction_fixture();
        let sentinel = roots[0];
        let consumer_called = std::cell::Cell::new(false);

        let result = exec.with_checked_same_context_ground_model(
            roots.clone(),
            2_000,
            |_executor, _checked_roots| Some(()),
            |executor, installed| {
                consumer_called.set(true);
                assert!(installed.is_current(executor));

                // Leave behind a bit-only, differently pinned MBQI package
                // and altered scalar state, then decline the candidate. The
                // outer typed grant must return current with its old model.
                executor.mbqi_sat_cert_grant_active = true;
                executor.mbqi_sat_cert_query_grant = None;
                executor
                    .last_model
                    .as_mut()
                    .expect("installed candidate model")
                    .install_quantified_certificate_pins(
                        &executor.ctx.terms,
                        [(sentinel, EvalValue::Bool(true))],
                    )?;
                executor.last_model_validated = false;
                executor.last_result = Some(SolveResult::Sat);
                executor.last_unknown_reason = None;
                executor.defer_model_validation = false;
                executor.last_statistics.conflicts = 73;
                None::<()>
            },
        );

        assert!(result.is_none());
        assert!(
            consumer_called.get(),
            "the regression must exercise rollback after token installation"
        );
        assert_checked_model_transaction_outer_state(&exec, &roots);
    }

    #[test]
    fn checked_model_transaction_restores_state_when_postprocessor_panics() {
        let (mut exec, roots) = checked_model_transaction_fixture();
        let sentinel = roots[0];
        let consumer_called = std::cell::Cell::new(false);

        let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _: Option<()> = exec.with_checked_same_context_ground_model(
                roots.clone(),
                2_000,
                |executor, _checked_roots| -> Option<()> {
                    executor.last_model = Some(Model::empty());
                    executor.last_model_validated = false;
                    executor.last_validation_stats = None;
                    executor.dt_theory_model = None;
                    executor.recorded_var_substitutions.clear();
                    executor.model_validation_delegated_assertions.clear();
                    executor.mbqi_sat_cert_grant_active = true;
                    executor.mbqi_sat_cert_query_grant = None;
                    executor
                        .last_model
                        .as_mut()
                        .expect("installed candidate model")
                        .install_quantified_certificate_pins(
                            &executor.ctx.terms,
                            [(sentinel, EvalValue::Bool(true))],
                        )
                        .expect("live candidate pin can be model-bound");
                    executor.last_result = Some(SolveResult::Sat);
                    executor.last_unknown_reason = None;
                    executor.defer_model_validation = false;
                    executor.last_statistics.conflicts = 101;
                    panic!("checked-model rollback canary");
                },
                |_executor, _installed| {
                    consumer_called.set(true);
                    Some(())
                },
            );
        }));

        assert!(unwind.is_err());
        assert!(
            !consumer_called.get(),
            "a panicking postprocessor must unwind before token consumption"
        );
        assert_checked_model_transaction_outer_state(&exec, &roots);
    }

    #[test]
    fn checked_model_transaction_commits_only_after_consumer_accepts() {
        let (mut exec, roots) = checked_model_transaction_fixture();

        let result = exec.with_checked_same_context_ground_model(
            roots.clone(),
            2_000,
            |_executor, _checked_roots| Some(()),
            |executor, installed| {
                assert!(installed.is_current(executor));
                executor.last_model_validated = true;
                let validation_stats = crate::executor::model::ValidationStats {
                    checked: 101,
                    total: 101,
                    ..Default::default()
                };
                executor.last_validation_stats = Some(validation_stats);
                executor.recorded_var_substitutions.clear();
                executor.model_validation_delegated_assertions.clear();
                executor.last_result = Some(SolveResult::Sat);
                executor.last_unknown_reason = None;
                executor.defer_model_validation = false;
                executor.last_statistics.conflicts = 103;
                executor
                    .last_statistics
                    .set_string("checked-model.transaction", "committed");
                Some(())
            },
        );

        assert_eq!(result, Some(()));
        assert!(installed_model_satisfies_roots(&exec, &roots));
        assert!(exec.last_model_validated);
        assert_eq!(
            exec.last_validation_stats
                .as_ref()
                .map(|stats| (stats.checked, stats.total)),
            Some((101, 101))
        );
        assert!(exec.recorded_var_substitutions.is_empty());
        assert!(exec.model_validation_delegated_assertions.is_empty());
        assert_eq!(exec.last_result, Some(SolveResult::Sat));
        assert_eq!(exec.last_unknown_reason, None);
        assert!(!exec.defer_model_validation);
        assert_eq!(exec.last_statistics.conflicts, 103);
        assert_eq!(
            exec.last_statistics.get_string("checked-model.transaction"),
            Some("committed")
        );
        assert!(!exec.mbqi_sat_cert_grant_active);
        assert!(exec.mbqi_sat_cert_query_grant.is_none());
        assert_eq!(
            exec.last_model
                .as_ref()
                .expect("committed candidate model")
                .quantified_certificate_pin_count(),
            0
        );
        assert_eq!(exec.current_quantified_sat_authority(&roots), None);
    }

    fn empty_ground_universe_refutation(proof_option: &str) -> Executor {
        load_assertions(&format!(
            r#"
                {proof_option}
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun p (U) Bool)
                (assert (forall ((x U)) (p x)))
                (assert (forall ((x U)) (not (p x))))
            "#,
        ))
    }

    fn execute_authored_check_sat(exec: &mut Executor) -> String {
        exec.execute_authored(&ay_frontend::Command::CheckSat)
            .expect("authored check-sat executes")
            .expect("check-sat produces a verdict")
    }

    fn assert_internal_strict_certified_unsat(
        exec: &mut Executor,
        policy: &str,
        retain_artifact: bool,
    ) {
        assert_eq!(execute_authored_check_sat(exec), "unsat", "{policy}");
        assert!(exec.last_result_is_unsat(), "{policy}");
        assert!(
            exec.last_command_unsat_was_strictly_verified(),
            "the public verdict must carry the internal StrictProof token: {policy}"
        );
        assert!(
            !exec.last_unsat_proof_reconstruction_suppressed,
            "a strict witnessed-forall certificate must remain publishable: {policy}"
        );
        if retain_artifact {
            let proof = exec
                .last_proof()
                .unwrap_or_else(|| panic!("strict witnessed-forall proof missing: {policy}"))
                .clone();
            assert!(
                exec.check_proof_strict_with_datatypes(&proof)
                    .is_ok_and(|quality| quality.is_complete()),
                "retained witnessed-forall proof must independently replay strictly: {policy}"
            );
        } else {
            assert!(
                exec.last_proof().is_none(),
                "an internal check-only policy need not retain an artifact: {policy}"
            );
        }
        assert!(exec.last_lrat_certificate().is_none(), "{policy}");
    }

    fn run_premise_probe(exec: &mut Executor) -> Option<Result<SolveResult>> {
        let snapshot = exec.ctx.assertions.clone();
        let mut quantifiers = Vec::new();
        for &assertion in &snapshot {
            crate::ematching::collect_quantifiers(&mut exec.ctx.terms, assertion, &mut quantifiers);
        }
        let foralls = quantifiers
            .into_iter()
            .filter(|&q| matches!(exec.ctx.terms.get(q), TermData::Forall(..)))
            .collect::<Vec<_>>();
        exec.premise_forced_binder_refutation(&foralls, &snapshot)
    }

    fn symbol_identities(exec: &Executor) -> Vec<String> {
        let mut names = exec
            .ctx
            .symbol_iter()
            .map(|(name, info)| exec.ctx.symbol_identity_name(name, info).to_string())
            .collect::<Vec<_>>();
        names.sort();
        names
    }

    fn exact_single_int_expansion_fixture() -> (Executor, Vec<TermId>, ExactFiniteExpansionEvidence)
    {
        let mut exec = load_assertions(
            r#"
                (set-logic LIA)
                (assert (forall ((i Int))
                    (=> (and (<= 0 i) (< i 1)) (= i 0))))
            "#,
        );
        let processed = exec.process_quantifiers();
        let original = processed
            .original_assertions
            .expect("fully expanded fixture retains authored roots");
        let expansion = processed
            .exact_finite_expansion
            .expect("single guarded Int forall records exact expansion evidence");
        assert!(processed.refinement_assertions.is_some());
        exec.last_model = Some(Model::empty());
        (exec, original, expansion)
    }

    #[test]
    fn finite_expansion_authority_is_bound_to_exact_model_and_root_order() {
        let (mut exec, roots, expansion) = exact_single_int_expansion_fixture();
        assert!(exec.install_exact_finite_expansion_sat_authority(&roots, &expansion));
        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            Some(CurrentQuantifiedSatAuthority::BvFullDomain)
        );
        assert!(exec.has_current_model_bound_quantified_sat_authority(&roots));

        let exact_model = exec.last_model.take();
        exec.last_model = exact_model.clone();
        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            None,
            "a semantic model clone must not inherit finite-expansion authority"
        );
        exec.last_model = exact_model;
        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            Some(CurrentQuantifiedSatAuthority::BvFullDomain),
            "moving the exact sealed model back preserves its identity"
        );

        let mut reordered = roots.clone();
        reordered.reverse();
        // A one-root vector cannot demonstrate order, so append a live ground
        // sibling and prove that retargeting is refused instead.
        if reordered == roots {
            reordered.push(exec.ctx.terms.true_term());
        }
        assert_eq!(
            exec.current_quantified_sat_authority(&reordered),
            None,
            "the grant is scoped to one exact ordered authored root window"
        );
    }

    #[test]
    fn finite_expansion_authority_builds_a_model_for_closed_ground_truth() {
        let (mut exec, roots, expansion) = exact_single_int_expansion_fixture();
        exec.last_model = None;
        let model_roots = exec
            .exact_finite_expansion_model_roots(&roots, &expansion)
            .expect("fixture expansion replays canonically");

        let token =
            CheckedFiniteExpansionSatAuthority::for_current(&mut exec, &roots, &model_roots)
                .expect("closed true expansion needs no pre-existing ground model");

        assert!(exec.last_model.is_some());
        assert!(token.into_current_roots(&mut exec).is_some());
    }

    #[test]
    fn finite_expansion_token_rejects_epoch_term_and_record_drift() {
        let (mut stale_epoch, epoch_roots, epoch_expansion) = exact_single_int_expansion_fixture();
        let epoch_model_roots = stale_epoch
            .exact_finite_expansion_model_roots(&epoch_roots, &epoch_expansion)
            .expect("fixture expansion replays canonically");
        let epoch_token = CheckedFiniteExpansionSatAuthority::for_current(
            &mut stale_epoch,
            &epoch_roots,
            &epoch_model_roots,
        )
        .expect("fixture model satisfies its expansion");
        stale_epoch.advance_query_authority_epoch();
        assert!(!stale_epoch.install_finite_expansion_sat_authority(epoch_token));
        assert!(!stale_epoch.bv_quantifier_full_domain_proof);

        let (mut stale_terms, term_roots, term_expansion) = exact_single_int_expansion_fixture();
        let term_model_roots = stale_terms
            .exact_finite_expansion_model_roots(&term_roots, &term_expansion)
            .expect("fixture expansion replays canonically");
        let term_token = CheckedFiniteExpansionSatAuthority::for_current(
            &mut stale_terms,
            &term_roots,
            &term_model_roots,
        )
        .expect("fixture model satisfies its expansion");
        let _fresh = stale_terms
            .ctx
            .terms
            .mk_var("finite-expansion-token-drift", Sort::Bool);
        assert!(!stale_terms.install_finite_expansion_sat_authority(term_token));
        assert!(!stale_terms.bv_quantifier_full_domain_proof);

        let (mut stale_record, record_roots, mut record_expansion) =
            exact_single_int_expansion_fixture();
        record_expansion.records[0].assertion_index += 1;
        assert!(
            stale_record
                .exact_finite_expansion_model_roots(&record_roots, &record_expansion)
                .is_none(),
            "record position is part of the exact expansion relation"
        );
        assert!(!stale_record.bv_quantifier_full_domain_proof);
    }

    #[test]
    fn finite_expansion_authority_rejects_contextual_evaluation_overrides() {
        let (mut mint, roots, expansion) = exact_single_int_expansion_fixture();
        let model_roots = mint
            .exact_finite_expansion_model_roots(&roots, &expansion)
            .expect("fixture expansion replays canonically");
        let override_term = roots[0];
        let minted = crate::executor::model::with_scoped_term_evaluation_override_for_test(
            override_term,
            EvalValue::Bool(true),
            || CheckedFiniteExpansionSatAuthority::for_current(&mut mint, &roots, &model_roots),
        );
        assert!(
            minted.is_none(),
            "contextual datatype evaluation must not mint source-semantic authority"
        );

        let (mut consume, roots, expansion) = exact_single_int_expansion_fixture();
        let model_roots = consume
            .exact_finite_expansion_model_roots(&roots, &expansion)
            .expect("fixture expansion replays canonically");
        let token =
            CheckedFiniteExpansionSatAuthority::for_current(&mut consume, &roots, &model_roots)
                .expect("fixture model satisfies its expansion without an override");
        let override_term = roots[0];
        let consumed = crate::executor::model::with_scoped_term_evaluation_override_for_test(
            override_term,
            EvalValue::Bool(true),
            || token.into_current_roots(&mut consume),
        );
        assert!(
            consumed.is_none(),
            "a contextual override arriving before consumption must stale the token"
        );
    }

    #[test]
    fn restoration_authority_accepts_only_current_typed_grants() {
        let mut exec = load_assertions(
            r#"
                (set-logic ALL)
                (declare-const p Bool)
                (assert p)
                (assert true)
            "#,
        );
        let roots = exec.ctx.assertions.clone();
        exec.last_model = Some(Model::empty());

        let dt_evidence = crate::executor::mbqi::CheckedDtSatAuthority::for_test(&mut exec, &roots)
            .expect("test model can be sealed");
        assert!(exec.install_dt_sat_authority(dt_evidence));
        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            Some(CurrentQuantifiedSatAuthority::Datatype)
        );
        exec.revoke_dt_sat_authority();

        let mbqi_evidence =
            crate::executor::mbqi::CheckedMbqiSatAuthority::for_test(&mut exec, &roots)
                .expect("test model can be sealed");
        assert!(exec.install_mbqi_sat_authority(mbqi_evidence));
        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            Some(CurrentQuantifiedSatAuthority::Mbqi)
        );
        exec.revoke_mbqi_sat_authority();

        let bv_evidence =
            crate::executor::bv_mbqi::CheckedBvFullDomainSatAuthority::for_test(&exec, &roots);
        assert!(exec.install_bv_full_domain_sat_authority(bv_evidence));
        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            Some(CurrentQuantifiedSatAuthority::BvFullDomain)
        );
    }

    #[test]
    fn restoration_authority_rejects_legacy_bits_without_typed_evidence() {
        let mut exec = load_assertions("(set-logic ALL) (assert true)");
        let roots = exec.ctx.assertions.clone();

        exec.dt_cert_grant_active = true;
        exec.finite_table_cert_grant_active = true;
        exec.const_interp_cert_grant_active = true;
        exec.mbqi_sat_cert_grant_active = true;
        exec.bv_quantifier_full_domain_proof = true;
        exec.last_model = Some(Model::empty());

        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            None,
            "routing bits alone must never suppress assertion-restoration failure"
        );
        assert!(
            !exec.has_current_model_free_mbqi_authority(&roots),
            "the final model-less CEGQI SAT postflight must reject a raw MBQI bit"
        );

        let evidence = crate::executor::mbqi::CheckedMbqiSatAuthority::for_test(&mut exec, &roots)
            .expect("test model can be sealed");
        assert!(exec.install_mbqi_sat_authority(evidence));
        assert!(
            !exec.has_current_model_free_mbqi_authority(&roots),
            "a model-bound MBQI grant must not be misclassified as model-free"
        );
    }

    fn sealed_disposable_probe_fixture() -> (Executor, Vec<TermId>) {
        let mut exec = load_assertions(
            r#"
                (set-logic UFLIA)
                (declare-fun p (Int) Bool)
                (assert (forall ((x Int)) (p x)))
            "#,
        );
        let roots = exec.ctx.assertions.clone();
        exec.last_model = Some(Model::empty());
        exec.last_model_validated = true;
        exec.last_result = Some(SolveResult::Sat);
        let evidence = crate::executor::mbqi::CheckedDtSatAuthority::for_test(&mut exec, &roots)
            .expect("fixture model can be sealed");
        assert!(exec.install_dt_sat_authority(evidence));
        (exec, roots)
    }

    fn assert_exact_dt_probe_predecessor(exec: &Executor, roots: &[TermId]) {
        assert_eq!(
            exec.current_quantified_sat_authority(roots),
            Some(CurrentQuantifiedSatAuthority::Datatype),
            "a nondecisive disposable probe must restore the exact sealed predecessor"
        );
    }

    #[test]
    fn disposable_mbqi_probes_move_restore_exact_model_authority() {
        // A semantic clone deliberately does not carry the predecessor seal.
        // Moving the original object back does.
        let (mut clone_check, clone_roots) = sealed_disposable_probe_fixture();
        let exact = clone_check.last_model.take();
        clone_check.last_model = exact.clone();
        assert_eq!(
            clone_check.current_quantified_sat_authority(&clone_roots),
            None,
            "Model::clone must not manufacture DT/MBQI publication authority"
        );
        clone_check.last_model = exact;
        assert_exact_dt_probe_predecessor(&clone_check, &clone_roots);

        let (mut refinement, refinement_roots) = sealed_disposable_probe_fixture();
        assert!(refinement
            .try_skipped_quantifier_mbqi_refinement(&[], LogicCategory::Uflia)
            .is_none());
        assert_exact_dt_probe_predecessor(&refinement, &refinement_roots);

        let (mut certification, certification_roots) = sealed_disposable_probe_fixture();
        assert!(certification
            .try_mbqi_sat_certification(&[], LogicCategory::Uflia, true, false)
            .is_none());
        assert_exact_dt_probe_predecessor(&certification, &certification_roots);

        let (mut disambiguation, disambiguation_roots) = sealed_disposable_probe_fixture();
        let snapshot = disambiguation.ctx.assertions.clone();
        assert!(disambiguation
            .disambiguate_cegqi_valid_via_mbqi_ext(&snapshot, LogicCategory::Uflia, false,)
            .is_none());
        assert_exact_dt_probe_predecessor(&disambiguation, &disambiguation_roots);
    }

    #[test]
    fn accepted_mbqi_probe_discards_predecessor_authority() {
        let mut exec = load_assertions(
            r#"
                (set-logic UFLIA)
                (declare-fun identity (Int) Int)
            "#,
        );
        // Build the already-elaborated internal identity form expected at this
        // late mapper stage. A surface parser term has not yet been rebound to
        // its stable declaration identity and is intentionally rejected by the
        // positive projection checker.
        let info = exec
            .ctx
            .symbol_info("identity")
            .expect("identity declaration is live");
        let identity = exec.ctx.symbol_identity_name("identity", info).to_string();
        let variable = exec.ctx.terms.mk_fresh_var("x", Sort::Int);
        let TermData::Var(variable_name, _) = exec.ctx.terms.get(variable) else {
            panic!("fresh binder is a variable")
        };
        let variable_name = variable_name.clone();
        let application = exec
            .ctx
            .terms
            .mk_app(Symbol::named(identity), [variable], Sort::Int);
        let body = exec.ctx.terms.mk_eq(application, variable);
        let quant = exec
            .ctx
            .terms
            .mk_forall(vec![(variable_name, Sort::Int)], body);
        exec.ctx.assertions.push(quant);
        let roots = exec.ctx.assertions.clone();
        exec.last_model = Some(Model::empty());
        exec.last_model_validated = true;
        exec.last_result = Some(SolveResult::Sat);
        let predecessor = crate::executor::mbqi::CheckedDtSatAuthority::for_test(&mut exec, &roots)
            .expect("predecessor model can be sealed");
        assert!(exec.install_dt_sat_authority(predecessor));

        assert!(exec
            .try_mbqi_sat_certification(&[], LogicCategory::Uflia, false, true)
            .is_some());
        assert!(!exec.dt_cert_grant_active);
        assert!(exec.dt_cert_query_grant.is_none());
        assert_eq!(
            exec.current_quantified_sat_authority(&roots),
            Some(CurrentQuantifiedSatAuthority::Mbqi),
            "the accepted replacement may carry only its freshly checked authority"
        );
    }

    #[test]
    fn canonical_clear_revokes_every_quantified_authority_and_model_seal() {
        let mut exec = load_assertions("(set-logic ALL) (assert true)");
        let mut model = Model::empty();
        let cegqi_model_epoch = model.seal_cegqi_uf_recompletion();
        let quantified_model_epoch = model.seal_quantified_grant_model();
        exec.last_model = Some(model);
        exec.dt_cert_grant_active = true;
        exec.finite_table_cert_grant_active = true;
        exec.const_interp_cert_grant_active = true;
        exec.mbqi_sat_cert_grant_active = true;
        exec.bv_quantifier_full_domain_proof = true;

        exec.clear_quantified_sat_authority();

        assert!(!exec.dt_cert_grant_active);
        assert!(exec.dt_cert_query_grant.is_none());
        assert!(!exec.finite_table_cert_grant_active);
        assert!(exec.finite_table_cert_witness_state.is_none());
        assert!(!exec.const_interp_cert_grant_active);
        assert!(exec.const_interp_cert_witness_state.is_none());
        assert!(!exec.mbqi_sat_cert_grant_active);
        assert!(exec.mbqi_sat_cert_query_grant.is_none());
        assert!(!exec.bv_quantifier_full_domain_proof);
        assert!(exec.bv_quantifier_full_domain_pending_evidence.is_none());
        assert!(exec.bv_quantifier_full_domain_query_grant.is_none());
        assert!(exec.cegqi_uf_recompletion_grant.is_none());
        let model = exec.last_model.as_ref().expect("model remains installed");
        assert!(!model.carries_cegqi_uf_recompletion(&cegqi_model_epoch));
        assert!(!model.carries_quantified_grant_model(&quantified_model_epoch));
    }

    #[test]
    fn public_table_rescue_requires_authority_for_clean_quantified_sat() {
        let sat = Ok(SolveResult::Sat);

        assert!(exact_public_table_rescue_needed(
            &sat, None, true, true, false, false, false, None,
        ));
        assert!(
            !exact_public_table_rescue_needed(&sat, None, false, true, false, false, false, None,),
            "a quantifier-free SAT must not enter the quantified table rescue"
        );
    }

    #[test]
    fn public_table_rescue_extends_beyond_cegqi_only_for_table_routing() {
        let sat = Ok(SolveResult::Sat);

        assert!(exact_public_table_rescue_needed(
            &sat, None, true, false, false, true, false, None,
        ));
        assert!(!exact_public_table_rescue_needed(
            &sat, None, true, false, false, false, false, None,
        ));
    }

    #[test]
    fn public_table_rescue_preserves_other_exact_quantified_authorities_only_on_sat() {
        let sat = Ok(SolveResult::Sat);
        let unknown = Ok(SolveResult::Unknown);

        for authority in [
            CurrentQuantifiedSatAuthority::Datatype,
            CurrentQuantifiedSatAuthority::Mbqi,
            CurrentQuantifiedSatAuthority::BvFullDomain,
            CurrentQuantifiedSatAuthority::CegqiUfRecompletion,
        ] {
            assert!(
                !exact_public_table_rescue_needed(
                    &sat,
                    None,
                    true,
                    true,
                    true,
                    true,
                    false,
                    Some(authority),
                ),
                "a current {authority:?} proof must not be replaced on Sat"
            );
            assert!(
                exact_public_table_rescue_needed(
                    &unknown,
                    Some(UnknownReason::QuantifierCegqiIncomplete),
                    true,
                    true,
                    true,
                    true,
                    false,
                    Some(authority),
                ),
                "a current {authority:?} quantified proof cannot upgrade a whole-query Unknown"
            );
        }
    }

    #[test]
    fn public_table_rescue_reuses_exact_transport_and_rejects_stale_bits() {
        let unknown = Ok(SolveResult::Unknown);
        assert!(exact_public_table_rescue_needed(
            &unknown,
            Some(UnknownReason::QuantifierCegqiIncomplete),
            true,
            false,
            false,
            true,
            true,
            Some(CurrentQuantifiedSatAuthority::FiniteTable),
        ));

        let sat = Ok(SolveResult::Sat);
        assert!(exact_public_table_rescue_needed(
            &sat, None, true, false, false, true, false, None,
        ));
    }

    #[test]
    fn public_table_rescue_rejects_non_quantifier_unknowns_and_non_candidates() {
        let unknown = Ok(SolveResult::Unknown);
        for reason in [
            None,
            Some(UnknownReason::Timeout),
            Some(UnknownReason::MemoryLimit),
            Some(UnknownReason::Incomplete),
        ] {
            assert!(!exact_public_table_rescue_needed(
                &unknown, reason, true, true, true, true, false, None,
            ));
        }
        assert!(!exact_public_table_rescue_needed(
            &unknown,
            Some(UnknownReason::QuantifierCegqiIncomplete),
            false,
            true,
            true,
            true,
            false,
            None,
        ));

        let unsat = Ok(SolveResult::unsat());
        assert!(!exact_public_table_rescue_needed(
            &unsat, None, true, true, true, true, false, None,
        ));
        let error: Result<SolveResult> = Err(crate::executor_types::ExecutorError::ArtifactExport(
            "test-only rescue refusal".to_string(),
        ));
        assert!(!exact_public_table_rescue_needed(
            &error, None, true, true, true, true, false, None,
        ));
    }

    #[test]
    fn cegqi_postflight_accepts_fresh_authority_but_never_waives_stop_or_model() {
        let safe = CegqiSatPostflightFacts {
            final_result_is_sat: true,
            should_abort: false,
            cegqi_has_forall: true,
            has_retained_model: true,
            has_pending_certificate_model: false,
            has_current_model_free_mbqi_authority: false,
            cegqi_source_stamp_is_stale: false,
            has_current_quantified_sat_authority: false,
        };

        assert!(cegqi_sat_postflight_must_fail_closed(
            CegqiSatPostflightFacts {
                cegqi_source_stamp_is_stale: true,
                ..safe
            }
        ));
        assert!(
            !cegqi_sat_postflight_must_fail_closed(CegqiSatPostflightFacts {
                cegqi_source_stamp_is_stale: true,
                has_current_quantified_sat_authority: true,
                ..safe
            }),
            "a typed authority checked against the live source supersedes the old CEGQI stamp"
        );
        assert!(cegqi_sat_postflight_must_fail_closed(
            CegqiSatPostflightFacts {
                should_abort: true,
                has_pending_certificate_model: true,
                has_current_model_free_mbqi_authority: true,
                has_current_quantified_sat_authority: true,
                ..safe
            }
        ));
        assert!(
            cegqi_sat_postflight_must_fail_closed(CegqiSatPostflightFacts {
                has_retained_model: false,
                has_current_quantified_sat_authority: true,
                ..safe
            }),
            "a non-model-free authority does not waive the retained-model premise"
        );
        assert!(
            !cegqi_sat_postflight_must_fail_closed(CegqiSatPostflightFacts {
                has_retained_model: false,
                has_pending_certificate_model: true,
                has_current_quantified_sat_authority: true,
                ..safe
            }),
            "exact pending certificate transport supplies the publication model"
        );
        assert!(
            !cegqi_sat_postflight_must_fail_closed(CegqiSatPostflightFacts {
                has_retained_model: false,
                has_current_model_free_mbqi_authority: true,
                has_current_quantified_sat_authority: true,
                ..safe
            }),
            "the exact model-free MBQI theorem retains its narrow exception"
        );
        assert!(!cegqi_sat_postflight_must_fail_closed(
            CegqiSatPostflightFacts {
                final_result_is_sat: false,
                should_abort: true,
                cegqi_source_stamp_is_stale: true,
                ..safe
            }
        ));
    }

    #[test]
    fn restoration_authority_rejects_stale_epoch_source_and_root_windows() {
        let mut stale_epoch = load_assertions("(set-logic ALL) (assert true)");
        let epoch_roots = stale_epoch.ctx.assertions.clone();
        stale_epoch.last_model = Some(Model::empty());
        let evidence =
            crate::executor::mbqi::CheckedDtSatAuthority::for_test(&mut stale_epoch, &epoch_roots)
                .expect("test model can be sealed");
        assert!(stale_epoch.install_dt_sat_authority(evidence));
        stale_epoch.advance_query_authority_epoch();
        assert_eq!(
            stale_epoch.current_quantified_sat_authority(&epoch_roots),
            None,
            "a later query must not reuse a prior DT grant"
        );

        let mut stale_source = load_assertions("(set-logic ALL) (assert true)");
        let source_roots = stale_source.ctx.assertions.clone();
        stale_source.last_model = Some(Model::empty());
        let evidence = crate::executor::mbqi::CheckedMbqiSatAuthority::for_test(
            &mut stale_source,
            &source_roots,
        )
        .expect("test model can be sealed");
        assert!(stale_source.install_mbqi_sat_authority(evidence));
        let source_epoch = stale_source.query_authority_epoch.clone();
        let stale_grant = stale_source
            .mbqi_sat_cert_query_grant
            .take()
            .expect("activation installs a typed MBQI grant");
        assert!(stale_source
            .execute(&ay_frontend::Command::Push(1))
            .expect("scope mutation succeeds")
            .is_none());
        // Reinstall the deliberately stashed grant and its original query
        // epoch so this check isolates the source-scope component rather than
        // passing because normal lifecycle invalidation cleared the package.
        stale_source.query_authority_epoch = source_epoch;
        stale_source.mbqi_sat_cert_grant_active = true;
        stale_source.mbqi_sat_cert_query_grant = Some(stale_grant);
        assert_eq!(
            stale_source.current_quantified_sat_authority(&source_roots),
            None,
            "a frontend scope mutation must revoke MBQI authority"
        );

        let mut stale_roots = load_assertions(
            r#"
                (set-logic ALL)
                (declare-const p Bool)
                (assert p)
                (assert true)
            "#,
        );
        let checked_roots = stale_roots.ctx.assertions.clone();
        let evidence = crate::executor::bv_mbqi::CheckedBvFullDomainSatAuthority::for_test(
            &stale_roots,
            &checked_roots,
        );
        assert!(stale_roots.install_bv_full_domain_sat_authority(evidence));
        let mut reordered_roots = checked_roots.clone();
        reordered_roots.reverse();
        assert_ne!(reordered_roots, checked_roots);
        assert_eq!(
            stale_roots.current_quantified_sat_authority(&reordered_roots),
            None,
            "the exact ordered root window is part of BV authority"
        );
    }

    #[test]
    fn cegqi_unsat_certificate_rejects_ce_free_added_false_with_snapshot_preserved() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (declare-const p Bool)
                (assert p)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        let false_term = exec.ctx.terms.mk_bool(false);
        let live_probe = vec![snapshot[0], false_term];
        exec.ctx.assertions = live_probe.clone();
        exec.last_result = Some(SolveResult::Sat);
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        exec.last_model_validated = true;

        let certificate =
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf);

        assert!(
            certificate.is_none(),
            "a CE-free live `false` with no authorized provenance must not publish UNSAT"
        );
        assert_eq!(
            exec.ctx.assertions, live_probe,
            "the independent check must restore the enclosing live probe"
        );
        assert_eq!(exec.last_result, Some(SolveResult::Sat));
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Incomplete));
        assert!(exec.last_model_validated);
    }

    #[test]
    fn cegqi_unsat_certificate_accepts_fresh_snapshot_ground_refutation() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();

        let certificate =
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf);

        assert!(
            certificate.is_some(),
            "an independently re-solved UNSAT snapshot ground core is authoritative"
        );
    }

    #[test]
    fn cegqi_ground_witness_validation_scopes_the_sat_result_marker() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= x 1))
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        exec.last_result = Some(SolveResult::unsat());
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        exec.last_statistics.conflicts = 17;
        exec.last_statistics
            .set_string("cegqi.snapshot.outer-state", "preserve");
        exec.set_best_effort_produce_proofs(100);
        exec.last_unsat_proof_reconstruction_suppressed = true;
        let statistics_before = exec.last_statistics.clone();
        let proof_enabled_before = exec.proof_tracker.is_enabled();
        let proof_steps_before = exec.proof_tracker.num_steps();
        let proof_required_before = exec.proof_artifact_required;
        let proof_budget_before = exec.proof_reconstruction_step_budget;

        let installed = exec
            .install_authenticated_snapshot_ground_model(&snapshot, LogicCategory::QfLia)
            .expect("fresh G0 SAT must validate independently of a preceding inner UNSAT marker");
        assert!(installed.is_current(&exec));
        assert_eq!(
            exec.last_result,
            Some(SolveResult::unsat()),
            "the temporary G0 SAT marker must not overwrite the enclosing result state"
        );
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Incomplete));
        assert_eq!(exec.last_statistics, statistics_before);
        assert_eq!(exec.proof_tracker.is_enabled(), proof_enabled_before);
        assert_eq!(exec.proof_tracker.num_steps(), proof_steps_before);
        assert_eq!(exec.proof_artifact_required, proof_required_before);
        assert_eq!(exec.proof_reconstruction_step_budget, proof_budget_before);
        assert!(
            exec.last_unsat_proof_reconstruction_suppressed,
            "the disposable G0 solve must not clear an enclosing proof firewall marker"
        );
        assert!(exec.last_model.is_some());
    }

    fn scoped_cegqi_ground_witness() -> (Executor, Vec<TermId>, cegqi_sat_authority::GroundWitness)
    {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= x 1))
            "#,
        );
        let roots = exec.ctx.assertions.clone();
        let witness = cegqi_sat_authority::install(&mut exec, &roots, LogicCategory::QfLia)
            .expect("the satisfiable ground snapshot installs an authenticated witness");
        (exec, roots, witness)
    }

    #[test]
    fn cegqi_ground_witness_binds_query_source_roots_and_model() {
        let (mut exact, roots, witness) = scoped_cegqi_ground_witness();
        assert!(witness.is_current(&exact, &roots));

        let mut different_roots = roots.clone();
        different_roots.push(exact.ctx.terms.mk_bool(true));
        assert!(
            !witness.is_current(&exact, &different_roots),
            "even a redundant extra root is outside the checked ordered window"
        );
        assert!(witness.is_current(&exact, &roots));

        exact.advance_query_authority_epoch();
        assert!(
            !witness.is_current(&exact, &roots),
            "a later public decision cannot reuse the ground witness"
        );

        let (mut stale_source, source_roots, source_witness) = scoped_cegqi_ground_witness();
        let source_epoch = stale_source.query_authority_epoch.clone();
        let source_model = stale_source
            .last_model
            .take()
            .expect("ground witness installed a model");
        assert!(stale_source
            .execute(&ay_frontend::Command::Push(1))
            .expect("scope mutation succeeds")
            .is_none());
        // Restore the other two bindings so this assertion isolates the
        // frontend source/scope stamp rather than passing through lifecycle
        // invalidation or model replacement.
        stale_source.query_authority_epoch = source_epoch;
        stale_source.last_model = Some(source_model);
        assert!(
            !source_witness.is_current(&stale_source, &source_roots),
            "a frontend scope mutation invalidates the source-bound witness"
        );

        let (mut stale_model, model_roots, model_witness) = scoped_cegqi_ground_witness();
        let replacement = stale_model
            .last_model
            .as_ref()
            .expect("ground witness installed a model")
            .clone();
        stale_model.last_model = Some(replacement);
        assert!(
            !model_witness.is_current(&stale_model, &model_roots),
            "a cloned/replaced model cannot inherit the sealed witness identity"
        );
    }

    #[test]
    fn completion_ground_witness_replaces_retained_invalid_candidate() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= x 1))
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        let stamp = exec.ctx.source_context_stamp();
        exec.last_model = Some(Model::empty());
        exec.last_model_validated = true;

        assert!(exec.ensure_snapshot_ground_model_for_completion(&snapshot, LogicCategory::QfLia,));
        let installed = exec
            .last_model
            .as_ref()
            .expect("fresh authenticated ground witness is retained");
        assert!(snapshot
            .iter()
            .all(|&term| matches!(exec.evaluate_term(installed, term), EvalValue::Bool(true))));
        assert_eq!(exec.ctx.source_context_stamp(), stamp);
        assert!(
            !exec.last_model_validated,
            "ground-only validation cannot pre-authorize quantified publication"
        );
    }

    #[test]
    fn cegqi_uf_recompletion_grant_is_query_root_and_model_scoped() {
        let mut exec = load_assertions(
            r#"
                (set-logic ALL)
                (declare-fun rem (Int Int) Int)
                (assert (forall ((x Int)) (= (rem x 2) 0)))
            "#,
        );
        assert_eq!(execute_authored_check_sat(&mut exec), "sat");
        let grant = exec
            .cegqi_uf_recompletion_grant
            .take()
            .expect("the checked UF re-completion route owns this SAT");
        assert!(grant.is_current(&exec));

        let extra_root = exec.ctx.terms.mk_bool(true);
        exec.ctx.assertions.push(extra_root);
        assert!(
            !grant.is_current(&exec),
            "even a redundant extra root is a different authored query"
        );
        exec.ctx.assertions.pop();
        assert!(grant.is_current(&exec));

        let original_query_epoch = exec.query_authority_epoch.clone();
        exec.advance_query_authority_epoch();
        assert!(
            !grant.is_current(&exec),
            "a later textually identical public query cannot reuse the grant"
        );
        exec.query_authority_epoch = original_query_epoch;
        assert!(grant.is_current(&exec));

        exec.last_model
            .as_mut()
            .expect("checked completion installed a model")
            .install_certified_total_uf(
                "unrelated".to_string(),
                vec![Sort::Int],
                Sort::Int,
                Vec::new(),
                EvalValue::Rational(BigRational::from_integer(0.into())),
            )
            .expect("well-typed replacement table");
        assert!(
            !grant.is_current(&exec),
            "changing any certified interpretation revokes the exact model identity"
        );
    }

    #[test]
    fn cegqi_uf_recompletion_model_definition_backstop_and_repair_revocation() {
        let mut exec = load_assertions(
            r#"
                (set-logic ALL)
                (declare-const p Bool)
                (declare-fun rem (Int Int) Int)
                (assert (forall ((x Int)) (= (rem x 2) 0)))
            "#,
        );
        assert_eq!(execute_authored_check_sat(&mut exec), "sat");
        let mut grant = exec
            .cegqi_uf_recompletion_grant
            .take()
            .expect("the checked UF re-completion route owns this SAT");
        let p = exec
            .ctx
            .symbol_iter()
            .find_map(|(name, info)| (name == "p").then_some(info.term).flatten())
            .expect("declared Bool constant");
        // Extend the real grant with unconstrained p, probing model-definition
        // revision while leaving query, source, binding, root, and model identities untouched.
        let p_var = {
            let model = exec.last_model.as_mut().expect("checked model");
            let var = model.sat_model.len() as u32;
            model.sat_model.push(true);
            model.term_to_var.insert(p, var);
            var
        };
        grant.model_definition = vec![p].into_boxed_slice();
        grant.model_definition_entries = [exec.ctx.terms.entry_stamp(p)].into();
        assert_eq!(
            grant.model_definition.as_ref(),
            [p],
            "the regression must exercise exactly one Bool M_def premise"
        );
        assert!(grant.is_current(&exec));

        // Bypass every supported mutation API and flip the effective SAT slot
        // directly. The exact M_def recheck is the final semantic backstop: it
        // must reject the grant even though no epoch or explicit revocation ran.
        {
            let model = exec.last_model.as_mut().expect("checked model");
            let slot = model
                .sat_model
                .get_mut(p_var as usize)
                .expect("mapped SAT slot");
            *slot = false;
        }
        crate::executor::model::eval_memo_clear();
        assert!(matches!(
            exec.evaluate_term(exec.last_model.as_ref().expect("checked model"), p),
            EvalValue::Bool(false)
        ));
        assert!(
            exec.last_model
                .as_ref()
                .expect("checked model")
                .carries_cegqi_uf_recompletion(&grant.model_epoch),
            "the raw slot write must leave epoch identity intact so M_def is the rejecting check"
        );
        assert!(
            !grant.is_current(&exec),
            "M_def must catch a direct theorem-premise mutation"
        );

        // Exercise the real post-seal repair primitive while keeping the
        // authored root vector intact at the authority observation point.
        let authored_roots = exec.ctx.assertions.clone();
        exec.ctx.assertions = vec![p];
        exec.repair_asserted_bool_leaf_polarities();
        exec.ctx.assertions = authored_roots;

        assert!(matches!(
            exec.evaluate_term(exec.last_model.as_ref().expect("repaired model"), p),
            EvalValue::Bool(true)
        ));
        assert!(
            !exec
                .last_model
                .as_ref()
                .expect("repaired model")
                .carries_cegqi_uf_recompletion(&grant.model_epoch),
            "the supported repair must revoke the sealed model identity"
        );
        assert!(
            !grant.is_current(&exec),
            "a production scalar repair must invalidate the sealed theorem"
        );
    }

    #[test]
    fn witnessed_forall_unsat_best_effort_retains_strict_certificate() {
        let mut exec = empty_ground_universe_refutation("");
        exec.set_best_effort_produce_proofs(100);

        assert_internal_strict_certified_unsat(&mut exec, "best-effort proof request", true);
    }

    #[test]
    fn witnessed_forall_unsat_all_internal_proof_policies_certify() {
        let mut explicit = empty_ground_universe_refutation("");
        explicit.set_produce_proofs(true);
        explicit.set_proof_reconstruction_step_budget(Some(100));
        assert!(
            explicit.proof_reconstruction_step_budget.is_none(),
            "a later budget call must not downgrade an explicit API proof request"
        );
        assert_internal_strict_certified_unsat(&mut explicit, "explicit API proof request", true);

        let mut script = empty_ground_universe_refutation("(set-option :produce-proofs true)");
        script.set_proof_reconstruction_step_budget(Some(100));
        assert_internal_strict_certified_unsat(&mut script, "SMT-LIB proof request", true);

        let mut strict = empty_ground_universe_refutation("(set-option :check-proofs-strict true)");
        strict.set_proof_reconstruction_step_budget(Some(100));
        assert_internal_strict_certified_unsat(&mut strict, "strict proof checking", false);

        let mut self_check = empty_ground_universe_refutation("");
        self_check.set_best_effort_produce_proofs(100);
        self_check.set_self_check(true);
        assert_internal_strict_certified_unsat(&mut self_check, "self-check", true);
    }

    #[test]
    fn cegqi_unsat_certificate_publish_rejects_stale_source_scope() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        let certificate =
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf)
                .expect("fixture independently certifies UNSAT");

        assert!(exec
            .execute(&ay_frontend::Command::Push(1))
            .expect("scope mutation succeeds")
            .is_none());
        let result = certificate.publish(&mut exec);

        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::QuantifierCegqiIncomplete)
        );
        assert!(!exec.last_unsat_proof_reconstruction_suppressed);
    }

    #[test]
    fn cegqi_unsat_certificate_publish_observes_late_interrupt() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;

        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        let certificate =
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf)
                .expect("fixture independently certifies UNSAT");
        let interrupt = Arc::new(AtomicBool::new(false));
        exec.set_interrupt(Arc::clone(&interrupt));
        interrupt.store(true, Ordering::Relaxed);

        let result = certificate.publish(&mut exec);

        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(exec.last_unknown_reason, Some(UnknownReason::Interrupted));
        assert!(!exec.last_unsat_proof_reconstruction_suppressed);
    }

    #[test]
    fn cegqi_unsat_certificate_declines_for_mandatory_explicit_proof() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        exec.set_produce_proofs(true);

        let certificate =
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf);

        assert!(
            certificate.is_none(),
            "a consequence re-solve cannot publish UNSAT in proof mode until its proof is translated"
        );
    }

    #[test]
    fn cegqi_unsat_certificate_publishes_default_verdict_without_proof_authority() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        exec.set_best_effort_produce_proofs(100);

        let certificate =
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf)
                .expect("best-effort default may certify the semantic verdict");
        let result = certificate.publish(&mut exec);

        assert!(result.is_unsat());
        assert!(exec.last_unsat_proof_reconstruction_suppressed);
        assert!(exec.last_proof().is_none());
        assert!(
            !exec.unsat_proof_self_certified(),
            "the self-check gate must not bypass verdict-only proof suppression"
        );
        assert!(exec.last_lrat_certificate().is_none());
        exec.build_unsat_proof();
        assert!(
            exec.last_proof().is_none(),
            "the outer trace must remain unusable after verdict-only publication"
        );
        assert!(exec.get_proof().contains("independently certified result"));
    }

    #[test]
    fn cegqi_unsat_certificate_declines_for_script_proof_despite_default_budget() {
        let mut exec = load_assertions(
            r#"
                (set-option :produce-proofs true)
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        exec.set_proof_reconstruction_step_budget(Some(100));

        assert!(
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf)
                .is_none(),
            "an SMT-LIB proof request is mandatory, even with a stale default budget"
        );
    }

    #[test]
    fn explicit_api_proof_request_cannot_be_downgraded_by_budget() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        exec.set_produce_proofs(true);
        exec.set_proof_reconstruction_step_budget(Some(100));

        assert!(
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf)
                .is_none(),
            "an explicit API proof request remains mandatory regardless of budget call order"
        );
        assert!(exec.proof_reconstruction_step_budget.is_none());
    }

    #[test]
    fn cegqi_unsat_certificate_declines_for_self_check_despite_default_budget() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (assert false)
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        exec.set_produce_proofs(true);
        exec.set_proof_reconstruction_step_budget(Some(100));
        exec.set_self_check(true);

        assert!(
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf)
                .is_none(),
            "self-check must never consume verdict-only CEGQI authority"
        );
    }

    #[test]
    fn cegqi_unsat_certificate_accepts_authorized_instance_closure() {
        let mut exec = load_assertions(
            r#"
                (set-logic UF)
                (declare-sort U 0)
                (declare-fun p (U) Bool)
                (declare-const a U)
                (assert (forall ((x U)) (p x)))
                (assert (not (p a)))
            "#,
        );
        let snapshot = exec.ctx.assertions.clone();
        assert!(
            !exec.ground_core_is_unsat(&snapshot, LogicCategory::QfUf),
            "the snapshot ground core alone is satisfiable"
        );
        let p_a = snapshot
            .iter()
            .find_map(|&term| match exec.ctx.terms.get(term) {
                TermData::Not(inner) => Some(*inner),
                _ => None,
            })
            .expect("fixture contains (not (p a))");
        exec.ctx.assertions.push(p_a);
        exec.push_active_support_axiom(p_a);
        let live_probe = exec.ctx.assertions.clone();

        let certificate =
            cegqi_unsat_authority::certify(&mut exec, Some(&snapshot), LogicCategory::QfUf);

        assert!(
            certificate.is_some(),
            "the tagged instance p(a) closes the authorized consequence set"
        );
        assert_eq!(
            exec.ctx.assertions, live_probe,
            "the disposable verifier must not mutate the enclosing assertion set"
        );
    }

    #[test]
    fn qpf_probe_refutes_only_a_verified_concrete_instance_and_preserves_outer_state() {
        let mut exec = load_assertions(
            r#"
                (set-logic UFBV)
                (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
                (assert (forall ((x (_ BitVec 1)))
                  (=> (= x #b0)
                      (and (= (f x) #b0) (= (f x) #b1)))))
            "#,
        );
        exec.original_problem_had_quantifiers = true;
        exec.last_result = Some(SolveResult::Sat);
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);
        let symbols_before = symbol_identities(&exec);
        let assertions_before = exec.ctx.assertions.clone();
        let parsed_before = exec.ctx.assertions_parsed().to_vec();
        let proof_enabled_before = exec.proof_tracker.is_enabled();
        let proof_steps_before = exec.proof_tracker.num_steps();
        let core_before = exec.last_assumption_core.clone();
        let core_names_before = exec.last_core_term_to_name.clone();

        let result = run_premise_probe(&mut exec);

        assert!(
            matches!(result, Some(Ok(SolveResult::Unsat(_)))),
            "the x=#b0 instance is ground-UNSAT"
        );
        assert!(
            exec.original_problem_had_quantifiers,
            "a disposable ground probe must not enable QF-only outer routes"
        );
        assert!(
            matches!(exec.last_result, Some(SolveResult::Sat)),
            "a probe must preserve the outer verdict bookkeeping"
        );
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::Incomplete),
            "a probe must preserve the outer diagnostic"
        );
        assert_eq!(
            symbol_identities(&exec),
            symbols_before,
            "fresh qpf constants must stay inside the disposable context"
        );
        assert_eq!(exec.ctx.assertions, assertions_before);
        assert_eq!(exec.ctx.assertions_parsed(), parsed_before);
        assert_eq!(exec.proof_tracker.is_enabled(), proof_enabled_before);
        assert_eq!(exec.proof_tracker.num_steps(), proof_steps_before);
        assert_eq!(exec.last_assumption_core, core_before);
        assert_eq!(exec.last_core_term_to_name, core_names_before);

        let repeated = run_premise_probe(&mut exec);
        assert!(matches!(repeated, Some(Ok(SolveResult::Unsat(_)))));
        assert_eq!(symbol_identities(&exec), symbols_before);
        assert_eq!(exec.ctx.assertions, assertions_before);
        assert_eq!(exec.ctx.assertions_parsed(), parsed_before);
    }

    #[test]
    fn qpf_probe_rejects_nonconjunctive_and_non_bv_carrier_adversaries() {
        for (label, smt) in [
            (
                "nonconjunctive",
                r#"
                    (set-logic UFBV)
                    (declare-const g Bool)
                    (declare-fun p ((_ BitVec 1)) Bool)
                    (assert (or g
                      (forall ((x (_ BitVec 1)))
                        (=> (= x x) (and (p x) (not (p x)))))))
                "#,
            ),
            (
                "model-varying carrier",
                r#"
                    (set-logic UF)
                    (declare-sort U 0)
                    (declare-const a U)
                    (declare-fun p (U U) Bool)
                    (assert (forall ((z U)) (= z a)))
                    (assert (forall ((x U) (y U))
                      (=> (distinct x y) (and (p x y) (not (p x y))))))
                "#,
            ),
            (
                "underspecified division",
                r#"
                    (set-logic UFNIA)
                    (declare-fun p (Int) Bool)
                    (assert (distinct (div 0 0) 0))
                    (assert (forall ((x Int))
                      (=> (and (= x 0) (= (div x 0) 0)) (p x))))
                "#,
            ),
            (
                "user bv-prefix direct",
                r#"
                    (set-logic UFBV)
                    (declare-fun bvtrap ((_ BitVec 1)) Bool)
                    (declare-fun p ((_ BitVec 1)) Bool)
                    (assert (not (bvtrap #b0)))
                    (assert (not (bvtrap #b1)))
                    (assert (forall ((x (_ BitVec 1)))
                      (=> (bvtrap x) (p x))))
                "#,
            ),
            (
                "user bv-prefix De Morgan",
                r#"
                    (set-logic UFBV)
                    (declare-fun bvtrap ((_ BitVec 1)) Bool)
                    (declare-fun p ((_ BitVec 1)) Bool)
                    (assert (not (bvtrap #b0)))
                    (assert (not (bvtrap #b1)))
                    (assert (forall ((x (_ BitVec 1)))
                      (or (not (bvtrap x)) (p x))))
                "#,
            ),
        ] {
            let mut exec = load_assertions(smt);
            assert!(
                run_premise_probe(&mut exec).is_none(),
                "{label} must stay outside the concrete-BV-instance refutation"
            );
        }
    }

    #[test]
    fn qpf_probe_skips_an_ineligible_first_forall_and_reaches_a_later_refutation() {
        let mut exec = load_assertions(
            r#"
                (set-logic UFBV)
                (declare-fun f ((_ BitVec 1)) (_ BitVec 1))
                (assert (forall ((unused (_ BitVec 1))) (=> true true)))
                (assert (forall ((x (_ BitVec 1)))
                  (=> (= x #b0)
                      (and (= (f x) #b0) (= (f x) #b1)))))
            "#,
        );

        assert!(
            matches!(
                run_premise_probe(&mut exec),
                Some(Ok(SolveResult::Unsat(_)))
            ),
            "an ineligible first forall must not abort the remaining forall scan"
        );
    }

    /// #probe-last-result: a disposable nested probe must not publish ITS OWN
    /// verdict into the enclosing solve's `last_result`.
    ///
    /// `finalize_sat_model_validation` refuses outright unless
    /// `last_result == Some(Sat)` (`SmtGroundAssertion: "Model validation
    /// requires SAT result"`), so a leaked probe verdict silently disarmed the
    /// quantifier lane's own model validation and `restore_assertions` degraded
    /// a genuine `Sat` to `Unknown(Incomplete)`.
    ///
    /// Both directions are exercised on purpose: the probe must be preserved
    /// when it ACCEPTS (returns `true` on a refutable formula — the direction
    /// that used to overwrite the outer verdict with `Unsat`) and when it
    /// DECLINES (returns `false` — the direction that used to overwrite it with
    /// `Sat`/`Unknown`). Each fixture's expected probe verdict is asserted too,
    /// so a fixture that folded away before the probe ran would fail here
    /// instead of vacuously passing.
    #[test]
    fn isolated_ground_probe_preserves_the_outer_last_result() {
        for (label, smt, expect_unsat) in [
            (
                "refutable ground formula",
                r#"(set-logic LIA)
                   (declare-fun x () Int)
                   (assert (and (>= x 0) (<= (+ x 1) 0)))"#,
                true,
            ),
            (
                "satisfiable ground formula",
                r#"(set-logic LIA)
                   (declare-fun x () Int)
                   (assert (and (>= x 0) (<= x 7)))"#,
                false,
            ),
        ] {
            let mut exec = load_assertions(smt);
            assert_eq!(
                exec.ctx.assertions.len(),
                1,
                "{label}: the fixture must survive to the probe as one assertion"
            );
            let formula = exec.ctx.assertions[0];
            assert!(
                !matches!(
                    exec.ctx.terms.get(formula),
                    TermData::Const(ay_core::Constant::Bool(_))
                ),
                "{label}: the fixture folded to a constant before the probe — it \
                 would test nothing"
            );
            for outer in [
                Some(SolveResult::Sat),
                Some(SolveResult::Unknown),
                Some(SolveResult::unsat()),
                None,
            ] {
                exec.last_result = outer.clone();
                let obligation = vec![formula];
                let refuted = exec
                    .checked_ground_solve(obligation.clone(), LogicCategory::Lia, 2_000)
                    .is_some_and(|decision| match decision {
                        CheckedGroundDecision::Unsat(checked) => {
                            checked.consume(&mut exec, &obligation)
                        }
                        CheckedGroundDecision::Sat(_) => false,
                    });
                assert_eq!(refuted, expect_unsat, "{label}: probe verdict");
                assert_eq!(
                    exec.last_result, outer,
                    "{label}: a disposable probe must not publish its verdict into \
                     the enclosing solve's last_result"
                );
            }
        }
    }

    #[test]
    fn checked_ground_tokens_accept_only_the_exact_current_scope() {
        let mut sat_exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (declare-const p Bool)
                (assert p)
            "#,
        );
        let sat_roots = sat_exec.ctx.assertions.clone();
        let sat = match sat_exec.checked_ground_solve(sat_roots.clone(), LogicCategory::QfUf, 2_000)
        {
            Some(CheckedGroundDecision::Sat(checked)) => checked,
            other => panic!("expected checked SAT authority, got {other:?}"),
        };
        assert!(sat.consume(&mut sat_exec, &sat_roots));

        let mut unsat_exec = load_assertions(
            r#"
                (set-logic QF_UF)
                (declare-const p Bool)
                (assert p)
                (assert (not p))
            "#,
        );
        let unsat_roots = unsat_exec.ctx.assertions.clone();
        let unsat = match unsat_exec.checked_ground_solve(
            unsat_roots.clone(),
            LogicCategory::QfUf,
            2_000,
        ) {
            Some(CheckedGroundDecision::Unsat(checked)) => checked,
            other => panic!("expected strict checked UNSAT authority, got {other:?}"),
        };
        assert!(unsat.consume(&mut unsat_exec, &unsat_roots));
    }

    #[test]
    fn checked_ground_token_rejects_epoch_source_root_and_term_drift() {
        fn sat_fixture() -> Executor {
            load_assertions(
                r#"
                    (set-logic QF_UF)
                    (declare-const p Bool)
                    (assert p)
                "#,
            )
        }

        let mut stale_epoch = sat_fixture();
        let roots = stale_epoch.ctx.assertions.clone();
        let checked =
            match stale_epoch.checked_ground_solve(roots.clone(), LogicCategory::QfUf, 2_000) {
                Some(CheckedGroundDecision::Sat(checked)) => checked,
                other => panic!("expected checked SAT authority, got {other:?}"),
            };
        stale_epoch.advance_query_authority_epoch();
        assert!(!checked.consume(&mut stale_epoch, &roots));

        let mut stale_source = sat_fixture();
        let roots = stale_source.ctx.assertions.clone();
        let source_epoch = stale_source.query_authority_epoch.clone();
        let checked =
            match stale_source.checked_ground_solve(roots.clone(), LogicCategory::QfUf, 2_000) {
                Some(CheckedGroundDecision::Sat(checked)) => checked,
                other => panic!("expected checked SAT authority, got {other:?}"),
            };
        assert!(stale_source
            .execute(&ay_frontend::Command::Push(1))
            .expect("scope mutation succeeds")
            .is_none());
        // Restore only the query epoch so this assertion specifically exercises
        // the frontend source/scope stamp carried by the token.
        stale_source.query_authority_epoch = source_epoch;
        assert!(!checked.consume(&mut stale_source, &roots));

        let mut stale_roots = load_assertions(
            r#"
                (set-logic QF_UF)
                (declare-const p Bool)
                (declare-const q Bool)
                (assert p)
                (assert q)
            "#,
        );
        let roots = stale_roots.ctx.assertions.clone();
        let checked =
            match stale_roots.checked_ground_solve(roots.clone(), LogicCategory::QfUf, 2_000) {
                Some(CheckedGroundDecision::Sat(checked)) => checked,
                other => panic!("expected checked SAT authority, got {other:?}"),
            };
        let mut reordered = roots.clone();
        reordered.reverse();
        assert_ne!(reordered, roots);
        assert!(!checked.consume(&mut stale_roots, &reordered));

        let mut stale_terms = sat_fixture();
        let roots = stale_terms.ctx.assertions.clone();
        let checked =
            match stale_terms.checked_ground_solve(roots.clone(), LogicCategory::QfUf, 2_000) {
                Some(CheckedGroundDecision::Sat(checked)) => checked,
                other => panic!("expected checked SAT authority, got {other:?}"),
            };
        let _unused = stale_terms
            .ctx
            .terms
            .mk_fresh_var("__checked_ground_stale", Sort::Bool);
        assert!(!checked.consume(&mut stale_terms, &roots));
    }

    #[test]
    fn checked_quantified_probe_rejects_sat_and_preserves_outer_state() {
        let mut exec = load_assertions(
            r#"
                (set-logic ALL)
                (assert (forall ((b Bool)) (= b b)))
            "#,
        );
        let roots = exec.ctx.assertions.clone();
        let assertions_before = roots.clone();
        exec.last_result = Some(SolveResult::Unknown);
        exec.last_unknown_reason = Some(UnknownReason::Incomplete);

        let checked = exec.checked_exact_unsat_solve(roots, 2_000);

        assert!(
            checked.is_none(),
            "a satisfiable quantified auxiliary theorem cannot mint UNSAT authority"
        );
        assert_eq!(exec.ctx.assertions, assertions_before);
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
        assert_eq!(
            exec.last_unknown_reason,
            Some(UnknownReason::Incomplete),
            "the disposable public-query transaction must not leak diagnostics"
        );
    }

    /// An isolated probe whose exact roots contain the Boolean constant `false`
    /// must not install a working set it cannot publish.
    ///
    /// The probe used to receive its roots by a raw `probe_ctx.assertions = ...`
    /// write performed after `ResetAssertions`. That left `authored_assertions`
    /// and `assertions_parsed` EMPTY against N live roots, so inside the probe
    /// `boolean_constant_premises_authored()` answered "nothing authored here",
    /// `proof_export_scope_assertions` stripped `false` out of the strict-proof
    /// problem (`#rewritten-constant-premise`), and
    /// `authored_corroboration_scope` — which reads `ctx.assertions` — still
    /// carried it. Its `debug_assert!` then fired on a scope that is not a
    /// subset of the problem, surfacing to deductive-checks as a `SolverPanic`.
    ///
    /// Here the enclosing query really does author `false`, so the probe
    /// inherits publication rights over it and the two views agree.
    ///
    /// This asserts the PRODUCER postcondition directly rather than waiting for
    /// the downstream panic: reaching `authored_corroboration_scope` needs the
    /// full `minimize_assumption_core` -> `checked_exact_unsat_solve` descent,
    /// but the state it trips over is created right here, and a probe whose
    /// working set is not a subset of its own publishable problem is already
    /// broken whether or not a later stage looks.
    #[test]
    fn isolated_probe_roots_stay_inside_the_publishable_problem() {
        let exec = load_assertions(
            r#"
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= x 1))
                (assert false)
            "#,
        );
        assert!(
            exec.boolean_constant_premises_authored().1,
            "fixture precondition: the enclosing query must author literal false"
        );
        let roots = exec.ctx.assertions.clone();
        assert!(
            roots.contains(&exec.ctx.terms.false_term()),
            "fixture precondition: the probe roots must carry the constant"
        );

        let mut probe_ctx = exec.ctx.clone();
        probe_ctx
            .process_command(&ay_frontend::Command::ResetAssertions)
            .expect("reset the probe context");
        exec.install_isolated_probe_roots(&mut probe_ctx, &roots);
        let probe = exec.qpf_probe_executor(probe_ctx, 2_000);

        assert_eq!(
            probe.ctx.assertions, roots,
            "the probe must decide exactly the roots it was handed"
        );
        // THE primary invariant — the one `authored_corroboration_scope`'s
        // `debug_assert!` polices — checked where the state is built.
        let problem = probe.complete_problem_assertions_for_strict_proof();
        for root in &probe.ctx.assertions {
            assert!(
                problem.contains(root),
                "probe root {root:?} is outside the strict-proof problem it would \
                 publish; the corroboration re-solve would answer a question the \
                 publication never claimed"
            );
        }
        // Second, independent stack the raw field write corrupted.
        assert_eq!(
            probe.ctx.assertions.len(),
            probe.ctx.assertion_finite_set_metadata().len(),
            "finite-set metadata must stay aligned with the assertion stack"
        );
    }

    /// Same invariant where the enclosing query authors NO literal `false` and
    /// the constant reaches the probe only as one of its exact roots — the shape
    /// the alternation and independent-gate lanes raise, sometimes as the single
    /// root of the whole probe.
    ///
    /// The probe still has to hold together: `#rewritten-constant-premise`
    /// withholds publication rights for `false` at the OUTER export boundary,
    /// but a probe that stripped its own live root would go on to decide a
    /// strictly smaller problem than the one it was handed. With a lone `false`
    /// root that means deciding the EMPTY problem, which is trivially SAT.
    #[test]
    fn isolated_probe_roots_survive_without_outer_false_authority() {
        let exec = load_assertions(
            r#"
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= x 1))
            "#,
        );
        assert!(
            !exec.boolean_constant_premises_authored().1,
            "fixture precondition: the enclosing query must NOT author literal false"
        );
        let roots = vec![exec.ctx.terms.false_term()];

        let mut probe_ctx = exec.ctx.clone();
        probe_ctx
            .process_command(&ay_frontend::Command::ResetAssertions)
            .expect("reset the probe context");
        exec.install_isolated_probe_roots(&mut probe_ctx, &roots);
        let probe = exec.qpf_probe_executor(probe_ctx, 2_000);

        assert_eq!(
            probe.ctx.assertions, roots,
            "the probe must decide exactly the roots it was handed"
        );
        let problem = probe.complete_problem_assertions_for_strict_proof();
        for root in &probe.ctx.assertions {
            assert!(
                problem.contains(root),
                "probe root {root:?} is outside the strict-proof problem it would \
                 publish; a probe that drops its only root decides the empty \
                 problem instead of the question it was asked"
            );
        }
    }

    /// The narrowness pin for the two tests above: the probe's private
    /// literal-false authority must NOT leak outward.
    ///
    /// Installing roots through the native-API route marks each one
    /// literal-false-sourced (the `__ay_api_assertion__` placeholder). That is
    /// safe only because the probe's context is a clone whose artifacts die with
    /// it, so the enclosing query must re-derive publication rights from its own
    /// authored record and still be refused them.
    #[test]
    fn isolated_probe_false_authority_does_not_leak_to_the_enclosing_query() {
        let mut exec = load_assertions(
            r#"
                (set-logic QF_LIA)
                (declare-const x Int)
                (assert (= x 1))
            "#,
        );
        let assertions_before = exec.ctx.assertions.clone();
        let mut roots = assertions_before.clone();
        roots.push(exec.ctx.terms.false_term());

        let _ = exec.checked_exact_unsat_solve(roots, 2_000);

        assert!(
            !exec.boolean_constant_premises_authored().1,
            "the probe must not hand the enclosing query authority over `false`"
        );
        assert_eq!(
            exec.ctx.assertions, assertions_before,
            "the disposable probe must not disturb the enclosing query"
        );
    }

    #[test]
    fn checked_exact_unsat_probe_accepts_exact_semantic_authority() {
        let mut exec = load_assertions(
            r#"
                (set-logic UFLIA)
                (assert (forall ((y Int)) (= (rem 2 y) 0)))
            "#,
        );
        let roots = exec.ctx.assertions.clone();

        let checked = exec
            .checked_exact_unsat_solve(roots.clone(), 2_000)
            .expect("the exact false instance must cross the disposable boundary");
        assert!(
            checked.consume(&mut exec, &roots),
            "exact semantic authority must remain bound to its outer query and roots"
        );
    }

    /// Build `forall x. B` where `B = psi0[y := sk_y(x)]` the way the
    /// Skolemizer does (registered internal symbol), plus its instantiator.
    fn skolemized_alternation(
        terms: &mut TermStore,
        mk_psi0: impl Fn(
            &mut TermStore,
            TermId, /* y-slot (sk app) */
            TermId, /* x */
        ) -> TermId,
    ) -> (TermId, CegqiInstantiator) {
        let x = terms.mk_var("x", Sort::Int);
        let sk_name = terms.mk_internal_symbol("sk_y");
        terms.mark_skolem_symbol(sk_name.clone());
        let sk_app = terms.mk_app(Symbol::named(sk_name), vec![x], Sort::Int);
        let body = mk_psi0(terms, sk_app, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, terms).expect("CEGQI instantiator");
        (forall, inst)
    }

    fn negative_single_forall_with_foldable_comparison(exec: &mut Executor) -> (TermId, TermId) {
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let lower = exec.ctx.terms.mk_var("lower", Sort::Int);
        let predicate = exec.ctx.terms.mk_var("predicate", Sort::Bool);
        let le = exec.ctx.terms.mk_le(lower, x);
        let not_le = exec.ctx.terms.mk_not(le);
        let body = exec.ctx.terms.mk_or(vec![predicate, not_le]);
        let forall = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let negative = exec.ctx.terms.mk_not(forall);
        (negative, forall)
    }

    #[test]
    fn proof_fold_preserves_sources_without_strict_rewrite_provenance() {
        let mut proof_exec = Executor::new();
        proof_exec.set_produce_proofs(true);
        let (negative, positive) = negative_single_forall_with_foldable_comparison(&mut proof_exec);
        proof_exec.ctx.assertions = vec![negative, positive];

        proof_exec.fold_quantified_linear_eqs();

        assert_eq!(
            proof_exec.ctx.assertions[0], negative,
            "proof mode must retain the exact authored source for sko_forall"
        );
        assert_ne!(
            proof_exec.ctx.assertions[1], positive,
            "positive foralls must retain the existing linear folding"
        );

        let outer_x = proof_exec.ctx.terms.mk_var("outer_x", Sort::Int);
        let inner_y = proof_exec.ctx.terms.mk_var("inner_y", Sort::Int);
        let lower = proof_exec.ctx.terms.mk_var("nested_lower", Sort::Int);
        let outer_atom = proof_exec.ctx.terms.mk_le(lower, outer_x);
        let le = proof_exec.ctx.terms.mk_le(lower, inner_y);
        let not_le = proof_exec.ctx.terms.mk_not(le);
        let exists = proof_exec
            .ctx
            .terms
            .mk_exists(vec![("inner_y".to_string(), Sort::Int)], not_le);
        let nested_body = proof_exec.ctx.terms.mk_or(vec![outer_atom, exists]);
        let nested_forall = proof_exec
            .ctx
            .terms
            .mk_forall(vec![("outer_x".to_string(), Sort::Int)], nested_body);
        let nested_negative = proof_exec.ctx.terms.mk_not(nested_forall);
        proof_exec.ctx.assertions = vec![nested_negative];

        proof_exec.fold_quantified_linear_eqs();

        assert_eq!(
            proof_exec.ctx.assertions[0], nested_negative,
            "nested quantified rewrites have no strict provenance translation and must retain the authored source"
        );

        let mut ordinary_exec = Executor::new();
        let (ordinary_negative, _) =
            negative_single_forall_with_foldable_comparison(&mut ordinary_exec);
        ordinary_exec.ctx.assertions = vec![ordinary_negative];

        ordinary_exec.fold_quantified_linear_eqs();

        assert_ne!(
            ordinary_exec.ctx.assertions[0], ordinary_negative,
            "non-proof solving must retain the existing NNF folding"
        );
    }

    /// 1-binder exact reconstruction: `forall x. sk(x) > x` (from
    /// `forall x exists y. y > x`) rebuilds to `forall y'. ¬(y' > e)`.
    #[test]
    fn rebuild_one_binder_alternation_exact() {
        let mut terms = TermStore::new();
        let (forall, inst) = skolemized_alternation(&mut terms, |t, y, x| t.mk_gt(y, x));
        let (binders, rho) = rebuild_quantified_ce_lemma(&mut terms, forall, &inst)
            .expect("rebuild must succeed on the canonical 1-binder alternation");
        assert_eq!(binders.len(), 1);
        assert_eq!(binders[0].1, Sort::Int);
        // rho = ¬(y' > e): the fresh binder replaces the Skolem app and the CE
        // variable replaces the universal binder.
        let e = *inst.ce_variables().get("x").expect("CE var for x");
        let fresh = terms.mk_var(binders[0].0.clone(), Sort::Int);
        let expected_inner = terms.mk_gt(fresh, e);
        let expected = terms.mk_not(expected_inner);
        assert_eq!(rho, expected, "exact syntactic reconstruction expected");
    }

    /// 2-binder exact reconstruction: `forall x. sk1(x) + sk2(x) = x` (from
    /// `forall x exists y1 y2. y1 + y2 = x`) rebuilds with two fresh binders.
    #[test]
    fn rebuild_two_binder_alternation_exact() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let sk1_name = terms.mk_internal_symbol("sk_y1");
        terms.mark_skolem_symbol(sk1_name.clone());
        let sk2_name = terms.mk_internal_symbol("sk_y2");
        terms.mark_skolem_symbol(sk2_name.clone());
        let sk1 = terms.mk_app(Symbol::named(sk1_name), vec![x], Sort::Int);
        let sk2 = terms.mk_app(Symbol::named(sk2_name), vec![x], Sort::Int);
        let sum = terms.mk_add(vec![sk1, sk2]);
        let body = terms.mk_eq(sum, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let (binders, rho) = rebuild_quantified_ce_lemma(&mut terms, forall, &inst)
            .expect("rebuild must succeed on the 2-binder alternation");
        assert_eq!(binders.len(), 2);
        let e = *inst.ce_variables().get("x").expect("CE var for x");
        let y1 = terms.mk_var(binders[0].0.clone(), Sort::Int);
        let y2 = terms.mk_var(binders[1].0.clone(), Sort::Int);
        // Discovery order of the two sk apps is deterministic but not
        // spec'd here; accept either assignment.
        let sum_a = terms.mk_add(vec![y1, y2]);
        let eq_a = terms.mk_eq(sum_a, e);
        let expected_a = terms.mk_not(eq_a);
        let sum_b = terms.mk_add(vec![y2, y1]);
        let eq_b = terms.mk_eq(sum_b, e);
        let expected_b = terms.mk_not(eq_b);
        assert!(
            rho == expected_a || rho == expected_b,
            "exact syntactic reconstruction expected"
        );
    }

    /// Fail-closed: non-Int binder.
    #[test]
    fn rebuild_fails_closed_on_non_int_binder() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let sk_name = terms.mk_internal_symbol("sk_y");
        terms.mark_skolem_symbol(sk_name.clone());
        let sk_app = terms.mk_app(Symbol::named(sk_name), vec![x], Sort::Real);
        let body = terms.mk_gt(sk_app, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Real)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// Fail-closed: more than two binders.
    #[test]
    fn rebuild_fails_closed_on_three_binders() {
        let mut terms = TermStore::new();
        let x1 = terms.mk_var("x1", Sort::Int);
        let x2 = terms.mk_var("x2", Sort::Int);
        let x3 = terms.mk_var("x3", Sort::Int);
        let s12 = terms.mk_add(vec![x1, x2]);
        let sum = terms.mk_add(vec![s12, x3]);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(sum, zero);
        let forall = terms.mk_forall(
            vec![
                ("x1".to_string(), Sort::Int),
                ("x2".to_string(), Sort::Int),
                ("x3".to_string(), Sort::Int),
            ],
            body,
        );
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// Fail-closed: a Skolem application whose argument is NOT a CE variable
    /// (here a ground constant) — outside the exact-provenance fragment.
    #[test]
    fn rebuild_fails_closed_on_skolem_app_over_non_ce_args() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(5.into());
        let sk_name = terms.mk_internal_symbol("sk_y");
        terms.mark_skolem_symbol(sk_name.clone());
        let sk_app = terms.mk_app(Symbol::named(sk_name), vec![five], Sort::Int);
        let sum = terms.mk_add(vec![sk_app, x]);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(sum, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// Fail-closed: a Skolem CONSTANT (outer existential `exists y forall x`)
    /// must never be de-Skolemized into a universal binder (`∀∃ ⇒ ∃∀` swap).
    #[test]
    fn rebuild_fails_closed_on_skolem_constant() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let sk = terms.mk_fresh_var("sk!y", Sort::Int);
        if let TermData::Var(name, _) = terms.get(sk) {
            let name = name.clone();
            terms.mark_skolem_symbol(name);
        }
        let body = terms.mk_gt(sk, x);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        assert!(rebuild_quantified_ce_lemma(&mut terms, forall, &inst).is_none());
    }

    /// No Skolem occurrences at all: the obligation degenerates to the stored
    /// ground CE lemma (empty binder list).
    #[test]
    fn rebuild_ground_lemma_degenerate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_ge(x, zero);
        let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let inst = CegqiInstantiator::new(forall, &mut terms).expect("CEGQI instantiator");
        let (binders, rho) = rebuild_quantified_ce_lemma(&mut terms, forall, &inst)
            .expect("ground universal must rebuild to its ground CE lemma");
        assert!(binders.is_empty());
        let expected = inst
            .create_ce_lemma(&mut terms)
            .expect("stored CE lemma must build");
        assert_eq!(rho, expected, "must equal the stored ground CE lemma");
    }

    #[test]
    fn pin_eval_const_preserves_expected_scalar_sort() {
        let mut terms = TermStore::new();

        let bool_term = pin_eval_const_for_sort(&mut terms, &Sort::Bool, &EvalValue::Bool(true))
            .expect("Bool value must rebuild as Bool");
        assert_eq!(terms.sort(bool_term), &Sort::Bool);

        let two = BigRational::from_integer(2.into());
        let int_term =
            pin_eval_const_for_sort(&mut terms, &Sort::Int, &EvalValue::Rational(two.clone()))
                .expect("integral rational must rebuild as Int when Int is expected");
        assert_eq!(terms.sort(int_term), &Sort::Int);

        let integral_real =
            pin_eval_const_for_sort(&mut terms, &Sort::Real, &EvalValue::Rational(two))
                .expect("integral Real must remain Real");
        assert_eq!(terms.sort(integral_real), &Sort::Real);

        let half = BigRational::new(1.into(), 2.into());
        let fractional_real =
            pin_eval_const_for_sort(&mut terms, &Sort::Real, &EvalValue::Rational(half))
                .expect("nonintegral Real must rebuild exactly");
        assert_eq!(terms.sort(fractional_real), &Sort::Real);

        let bv8 = Sort::bitvec(8);
        let bv_term = pin_eval_const_for_sort(
            &mut terms,
            &bv8,
            &EvalValue::BitVec {
                value: 0x1ff.into(),
                width: 8,
            },
        )
        .expect("matching bit-vector width must rebuild");
        assert_eq!(terms.sort(bv_term), &bv8);
    }

    #[test]
    fn pin_eval_const_rejects_incompatible_value_sort_pairs() {
        let mut terms = TermStore::new();
        let half = EvalValue::Rational(BigRational::new(1.into(), 2.into()));

        assert!(pin_eval_const_for_sort(&mut terms, &Sort::Int, &half).is_none());
        assert!(pin_eval_const_for_sort(&mut terms, &Sort::Bool, &half).is_none());
        assert!(pin_eval_const_for_sort(&mut terms, &Sort::Real, &EvalValue::Bool(true)).is_none());
        assert!(pin_eval_const_for_sort(
            &mut terms,
            &Sort::bitvec(8),
            &EvalValue::BitVec {
                value: 7.into(),
                width: 16,
            },
        )
        .is_none());
    }
}
