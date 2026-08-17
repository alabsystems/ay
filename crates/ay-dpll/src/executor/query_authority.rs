// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Opaque authority for one caller-authored, plain hard `check-sat` query.
//!
//! A bare call to [`Executor::check_sat`](super::Executor::check_sat) is not
//! evidence that the current assertions came from a public query: quantifier
//! retries, optimization, CHC adapters, proof checkers, and model repair all
//! reuse that entrypoint.  This module gives the two audited authored front
//! doors a linear capability that records the exact query before any solve-time
//! rewriting begins.  Candidate production remains untrusted; later steering
//! code must consume this capability together with independently checked
//! semantic and source-declaration evidence.

mod model_bound_install;

use std::sync::Arc;

use ay_core::term::TermEntryStamp;
use ay_core::TermId;
use ay_frontend::{CheckedProjectionBindings, Objective, SoftAssertion, SourceContextStamp};

use super::bv_mbqi::CheckedBvFullDomainSatAuthority;
use super::mbqi::{CheckedDtSatAuthority, CheckedExactClosedSentenceSat};
use super::model::QuantifiedGrantModelEpoch;
use super::Executor;
use crate::executor_types::{Result, SolveResult};

/// One API-owned soft constraint as it contributes to an exact native query.
///
/// API soft constraints live above the frontend [`Context`](ay_frontend::Context),
/// so the native authored boundary must supply them explicitly.  The first
/// projection-certificate version accepts only an empty set, but retaining the
/// complete ordered representation makes that emptiness an authenticated query
/// fact instead of an assumption made by a downstream checker.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeSoftQueryBinding {
    pub(crate) term: TermId,
    pub(crate) weight: u64,
    pub(crate) group: Option<String>,
}

/// Fresh identity for one public decision attempt.
///
/// Pointer identity avoids counter wraparound.  Cloning preserves one epoch;
/// starting any later public decision replaces the executor's marker with a
/// fresh allocation, so a stashed permit cannot become current again even when
/// every visible query component happens to be byte-for-byte identical.
#[derive(Clone, Debug)]
pub(crate) struct QueryAuthorityEpoch(Arc<QueryAuthorityEpochMarker>);

#[derive(Debug)]
struct QueryAuthorityEpochMarker;

impl QueryAuthorityEpoch {
    pub(in crate::executor) fn fresh() -> Self {
        Self(Arc::new(QueryAuthorityEpochMarker))
    }

    pub(in crate::executor) fn is_same_epoch(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Exact query/source/root scope of one independently checked quantified-SAT
/// certificate.
///
/// The legacy Boolean fields on [`Executor`] remain useful as local routing
/// state, but they are deliberately insufficient at a SAT publication gate.
/// A gate accepts a certificate only when it is paired with this opaque grant
/// and the grant still denotes the same public decision attempt, frontend
/// source scope, and ordered authored-root window.
#[derive(Debug)]
pub(in crate::executor) struct QuantifiedSatAuthorityGrant {
    epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[Option<TermEntryStamp>]>,
    projection_bindings: QuantifiedProjectionBindings,
    model_epoch: Option<QuantifiedGrantModelEpoch>,
}

#[derive(Debug)]
enum QuantifiedProjectionBindings {
    None,
    /// Aggregate evidence also freezes the reachable root graph.
    Aggregate(CheckedProjectionBindings),
    /// DT's legacy declaration checker currently returns individually checked
    /// identities. Retain them affinely rather than dropping positive
    /// declaration kind/signature authority at publication.
    Individual(Box<[ay_frontend::CheckedProjectionBinding]>),
}

impl QuantifiedProjectionBindings {
    fn is_current_for(&self, executor: &Executor, roots: &[TermId]) -> bool {
        match self {
            Self::None => true,
            Self::Aggregate(bindings) => executor
                .ctx
                .projection_bindings_still_current(bindings, roots),
            Self::Individual(bindings) => bindings
                .iter()
                .all(|binding| executor.ctx.projection_binding_still_current(binding)),
        }
    }
}

impl QuantifiedSatAuthorityGrant {
    /// Record the exact roots discharged by a successful certificate.
    ///
    /// Callers must invoke this only in the success arm of the corresponding
    /// checker. The private fields prevent a raw Boolean routing marker from
    /// being retargeted later by a gate consumer.
    fn for_checked_roots(executor: &Executor, roots: &[TermId]) -> Self {
        Self {
            epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            projection_bindings: QuantifiedProjectionBindings::None,
            model_epoch: None,
        }
    }

    /// Record roots discharged relative to one exact installed model.
    fn for_checked_model_roots(
        executor: &Executor,
        roots: &[TermId],
        model_epoch: QuantifiedGrantModelEpoch,
        projection_bindings: QuantifiedProjectionBindings,
    ) -> Option<Self> {
        if !executor
            .last_model
            .as_ref()
            .is_some_and(|model| model.carries_quantified_grant_model(&model_epoch))
        {
            return None;
        }
        Some(Self {
            epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            roots: roots.into(),
            root_entries: roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            projection_bindings,
            model_epoch: Some(model_epoch),
        })
    }

    /// Whether this grant still covers exactly the roots a gate will check.
    #[must_use]
    pub(in crate::executor) fn is_current_for(
        &self,
        executor: &Executor,
        roots: &[TermId],
    ) -> bool {
        self.scope_is_current_for(executor, roots)
            && self.projection_bindings.is_current_for(executor, roots)
            && self.model_epoch.as_ref().is_none_or(|model_epoch| {
                executor.last_model.as_ref().is_some_and(|model| {
                    model.carries_quantified_grant_model(model_epoch)
                        && model.quantified_certificate_pins_are_current(&executor.ctx.terms)
                        && model.formula_neutral_function_defaults_are_current(&executor.ctx)
                })
            })
    }

    /// Whether the immutable query/source/root half remains current. The sole
    /// caller is [`Self::is_current_for`], which additionally checks positive
    /// projection bindings and the exact installed-model seal when present.
    fn scope_is_current_for(&self, executor: &Executor, roots: &[TermId]) -> bool {
        self.epoch.is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.roots.as_ref() == roots
            && self.root_entries.iter().all(Option::is_some)
            && self.root_entries.iter().copied().eq(roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
    }
}

/// Exact ordered inventory captured at the authored query boundary.
#[derive(Debug, PartialEq, Eq)]
struct PlainHardQueryInventory {
    hard_roots: Vec<TermId>,
    hard_root_entries: Vec<Option<TermEntryStamp>>,
    assumptions: Vec<TermId>,
    objectives: Vec<Objective>,
    parsed_softs: Vec<SoftAssertion>,
    native_softs: Vec<NativeSoftQueryBinding>,
    scope_depth: usize,
    term_count: usize,
}

impl PlainHardQueryInventory {
    fn capture(executor: &Executor, native_softs: &[NativeSoftQueryBinding]) -> Self {
        Self {
            hard_roots: executor.ctx.assertions.clone(),
            hard_root_entries: executor
                .ctx
                .assertions
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root))
                .collect(),
            // The type is minted only for the `check-sat` command, never for
            // `check-sat-assuming` (including its empty spelling).
            assumptions: Vec::new(),
            objectives: executor.ctx.objectives().to_vec(),
            parsed_softs: executor.ctx.soft_constraints().to_vec(),
            native_softs: native_softs.to_vec(),
            scope_depth: executor.ctx.scope_depth(),
            term_count: executor.ctx.terms.len(),
        }
    }

    fn is_plain_hard(&self) -> bool {
        self.assumptions.is_empty()
            && self.objectives.is_empty()
            && self.parsed_softs.is_empty()
            && self.native_softs.is_empty()
    }

    fn matches_live_executor(&self, executor: &Executor) -> bool {
        self.is_plain_hard()
            && self.hard_roots == executor.ctx.assertions
            && self.hard_root_entries.iter().all(Option::is_some)
            && self.hard_root_entries.iter().copied().eq(self
                .hard_roots
                .iter()
                .map(|&root| executor.ctx.terms.entry_stamp(root)))
            && self.objectives == executor.ctx.objectives()
            && self.parsed_softs == executor.ctx.soft_constraints()
            && executor.ctx.scope_depth() == self.scope_depth
            && executor.ctx.terms.len() == self.term_count
    }
}

/// Linear proof that one exact query entered through an audited authored,
/// plain-hard `check-sat` front door.
///
/// The fields and constructor are private and this type deliberately does not
/// implement [`Clone`].  A downstream candidate cannot manufacture, duplicate,
/// or refresh it.  It is not SAT authority by itself: the SAT chokepoint must
/// additionally consume independently checked projection semantics and source
/// declaration bindings while [`Self::is_current`] still holds.
#[must_use = "dropping authored query authority disables the checked projection path"]
#[derive(Debug)]
pub(in crate::executor) struct AuthoredPlainHardQueryPermit {
    epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    inventory: PlainHardQueryInventory,
}

/// Borrow-bound authored query transaction.
///
/// Holding this value exclusively borrows its [`Executor`], so safe code cannot
/// append and restore assertions, rotate scopes, or start another solve between
/// authority capture and consumption. The underlying permit never leaves this
/// module: callers can only consume the transaction through [`Self::solve`] or
/// [`Self::solve_interruptible`].
#[must_use = "an authored query transaction must be consumed by its solve"]
struct AuthoredPlainHardQuery<'a> {
    executor: &'a mut Executor,
    permit: AuthoredPlainHardQueryPermit,
}

impl AuthoredPlainHardQuery<'_> {
    /// Consume this transaction in the ordinary authored solve path.
    fn solve(self) -> Result<SolveResult> {
        self.executor.check_sat_with_authored_query(self.permit)
    }
}

impl AuthoredPlainHardQueryPermit {
    /// Exact ordered hard-assertion roots captured for this query.
    pub(crate) fn roots(&self) -> &[TermId] {
        &self.inventory.hard_roots
    }

    /// Opaque frontend context/scope stamp captured for this query.
    #[must_use]
    pub(crate) fn source_context_stamp(&self) -> &SourceContextStamp {
        &self.source_context_stamp
    }

    /// Whether this linear permit still denotes the executor's active exact
    /// query and term/source snapshot.
    #[must_use]
    pub(crate) fn is_current(&self, executor: &Executor) -> bool {
        self.epoch.is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.inventory.matches_live_executor(executor)
    }

    #[cfg(test)]
    fn inventory(&self) -> &PlainHardQueryInventory {
        &self.inventory
    }
}

impl Executor {
    /// Rotate the live public-query identity before any decision preflight or
    /// elaboration can fail.
    pub(in crate::executor) fn advance_query_authority_epoch(&mut self) {
        self.query_authority_epoch = QueryAuthorityEpoch::fresh();
    }

    /// Consume a successful DT certificate and install its exact checked root
    /// window. Raw roots or a Boolean success marker cannot mint this authority.
    pub(in crate::executor) fn install_dt_sat_authority(
        &mut self,
        evidence: CheckedDtSatAuthority,
    ) -> bool {
        self.revoke_dt_sat_authority();
        let Some((roots, model_epoch, projection_bindings)) = evidence.into_current_roots(self)
        else {
            return false;
        };
        let Some(grant) = QuantifiedSatAuthorityGrant::for_checked_model_roots(
            self,
            &roots,
            model_epoch,
            QuantifiedProjectionBindings::Individual(projection_bindings),
        ) else {
            return false;
        };
        self.dt_cert_grant_active = true;
        self.dt_cert_query_grant = Some(grant);
        true
    }

    /// Revoke both halves of the DT certificate authority.
    pub(in crate::executor) fn revoke_dt_sat_authority(&mut self) {
        self.dt_cert_grant_active = false;
        self.dt_cert_query_grant = None;
    }

    /// Consume exact structural theorem evidence and install its bound roots
    /// as the MBQI-compatible publication grant.
    ///
    /// No root parameter is accepted here: the caller cannot retarget checked
    /// evidence onto another ordered assertion window. A stale query epoch or
    /// frontend source/scope stamp consumes the token, revokes any prior MBQI
    /// authority, and returns `false`.
    pub(in crate::executor) fn install_exact_closed_sentence_sat_authority(
        &mut self,
        evidence: CheckedExactClosedSentenceSat,
    ) -> bool {
        self.revoke_mbqi_sat_authority();
        let Some(roots) = evidence.into_current_roots(self) else {
            return false;
        };
        let grant = QuantifiedSatAuthorityGrant::for_checked_roots(self, &roots);

        // This exact theorem owns the complete authored root window. Retire
        // every competing quantified routing bit, parked model, and typed
        // grant as one lifecycle unit before publishing it. In particular, a
        // stale finite/default-table bit must not win the finite-first branch
        // in the SAT funnel and hide this current theorem behind a missing
        // parked witness.
        self.clear_quantified_sat_authority();
        self.mbqi_sat_cert_grant_active = true;
        self.mbqi_sat_cert_query_grant = Some(grant);
        true
    }

    /// Revoke both halves of the MBQI certificate authority.
    pub(in crate::executor) fn revoke_mbqi_sat_authority(&mut self) {
        self.mbqi_sat_cert_grant_active = false;
        self.mbqi_sat_cert_query_grant = None;
    }

    /// Whether a live DT/MBQI/finite-expansion theorem is bound to the exact
    /// installed model.
    /// Model-free exact-closed MBQI grants deliberately remain outside this
    /// classification and are never consumed or rewritten by SAT emission.
    pub(in crate::executor) fn has_current_model_bound_quantified_sat_authority(
        &self,
        roots: &[TermId],
    ) -> bool {
        (self.dt_cert_grant_active
            && self.dt_cert_query_grant.as_ref().is_some_and(|grant| {
                grant.model_epoch.is_some() && grant.is_current_for(self, roots)
            }))
            || (self.mbqi_sat_cert_grant_active
                && self
                    .mbqi_sat_cert_query_grant
                    .as_ref()
                    .is_some_and(|grant| {
                        grant.model_epoch.is_some() && grant.is_current_for(self, roots)
                    }))
            || (self.bv_quantifier_full_domain_proof
                && self
                    .bv_quantifier_full_domain_query_grant
                    .as_ref()
                    .is_some_and(|grant| {
                        grant.model_epoch.is_some() && grant.is_current_for(self, roots)
                    }))
    }

    /// Whether the exact closed-sentence theorem currently owns `roots`
    /// without naming a particular model.
    ///
    /// Ordinary MBQI grants are model-bound. Checking the absent model epoch
    /// here is load-bearing: SAT emission may replace an arbitrary leftover
    /// candidate with a canonical output witness only for a theorem that is
    /// valid under every interpretation.
    pub(in crate::executor) fn has_current_model_free_mbqi_sat_authority(
        &self,
        roots: &[TermId],
    ) -> bool {
        self.mbqi_sat_cert_grant_active
            && self
                .mbqi_sat_cert_query_grant
                .as_ref()
                .is_some_and(|grant| {
                    grant.model_epoch.is_none() && grant.is_current_for(self, roots)
                })
    }

    fn install_bv_sat_authority_roots(&mut self, roots: Box<[TermId]>) {
        let grant = QuantifiedSatAuthorityGrant::for_checked_roots(self, &roots);
        self.bv_quantifier_full_domain_proof = true;
        self.bv_quantifier_full_domain_query_grant = Some(grant);
    }

    /// Consume a BV-MBQI full-domain proof. No caller-supplied root window is
    /// accepted, so a raw result or routing bit cannot be retargeted.
    pub(in crate::executor) fn install_bv_full_domain_sat_authority(
        &mut self,
        evidence: CheckedBvFullDomainSatAuthority,
    ) -> bool {
        self.revoke_bv_full_domain_sat_authority();
        let Some(roots) = evidence.into_current_roots(self) else {
            return false;
        };
        self.install_bv_sat_authority_roots(roots);
        true
    }

    /// Revoke both halves of the BV full-domain authority.
    pub(in crate::executor) fn revoke_bv_full_domain_sat_authority(&mut self) {
        self.bv_quantifier_full_domain_proof = false;
        self.bv_quantifier_full_domain_pending_evidence = None;
        self.bv_quantifier_full_domain_query_grant = None;
    }

    /// Revoke both the installed-model identity and executor-side CEGQI grant
    /// before a theorem-relevant semantic model repair.
    pub(in crate::executor) fn revoke_cegqi_uf_recompletion_authority(&mut self) {
        if let Some(model) = self.last_model.as_mut() {
            model.revoke_cegqi_uf_recompletion();
        }
        self.cegqi_uf_recompletion_grant = None;
    }

    /// Mint an authored plain-hard capability for the exact live query.
    ///
    /// Callers are intentionally limited to the explicit text and native
    /// authored wrappers.  Generic `execute`, assumptions, optimization,
    /// MaxSMT, CHC, and nested solver paths never call this method and therefore
    /// can pass only `None` to the shared solve implementation.
    fn begin_authored_plain_hard_query(
        &mut self,
        inventory: PlainHardQueryInventory,
    ) -> AuthoredPlainHardQuery<'_> {
        debug_assert!(inventory.is_plain_hard());
        let permit = AuthoredPlainHardQueryPermit {
            epoch: self.query_authority_epoch.clone(),
            source_context_stamp: self.ctx.source_context_stamp(),
            inventory,
        };
        AuthoredPlainHardQuery {
            executor: self,
            permit,
        }
    }

    /// Atomically capture and consume one authored plain-hard query.
    ///
    /// No permit is returned to the caller, and the borrow-bound transaction
    /// prevents state mutation between capture and solve.
    pub(crate) fn solve_authored_plain_hard_query(
        &mut self,
        native_softs: &[NativeSoftQueryBinding],
    ) -> Result<SolveResult> {
        let inventory = PlainHardQueryInventory::capture(self, native_softs);
        if !inventory.is_plain_hard() {
            return self.check_sat();
        }
        self.begin_authored_plain_hard_query(inventory).solve()
    }

    #[cfg(test)]
    pub(crate) fn last_check_saw_authored_query_authority(&self) -> bool {
        self.last_authored_query_authority_seen
    }

    /// Test-only detached permit for stale-evidence mutation checks.
    ///
    /// Production can obtain a permit only through the borrow-bound transaction
    /// above. Tests that deliberately mutate the executor after certification
    /// need to hold the opaque permit independently in order to prove those
    /// mutations retire the derived evidence.
    #[cfg(test)]
    pub(in crate::executor) fn detached_authored_plain_hard_permit_for_test(
        &self,
    ) -> Option<AuthoredPlainHardQueryPermit> {
        let inventory = PlainHardQueryInventory::capture(self, &[]);
        inventory
            .is_plain_hard()
            .then(|| AuthoredPlainHardQueryPermit {
                epoch: self.query_authority_epoch.clone(),
                source_context_stamp: self.ctx.source_context_stamp(),
                inventory,
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::{parse, Command};

    /// Test-only detached construction for currentness mutation checks. The
    /// production API deliberately exposes only the borrow-bound atomic solve.
    fn detached_test_permit(
        executor: &Executor,
        native_softs: &[NativeSoftQueryBinding],
    ) -> Option<AuthoredPlainHardQueryPermit> {
        let inventory = PlainHardQueryInventory::capture(executor, native_softs);
        inventory
            .is_plain_hard()
            .then(|| AuthoredPlainHardQueryPermit {
                epoch: executor.query_authority_epoch.clone(),
                source_context_stamp: executor.ctx.source_context_stamp(),
                inventory,
            })
    }

    fn execute_setup(executor: &mut Executor, script: &str) {
        let commands = parse(script).expect("valid authority test script");
        executor
            .execute_all(&commands)
            .expect("authority test setup executes");
    }

    #[test]
    fn permit_binds_exact_ordered_plain_hard_inventory() {
        let mut executor = Executor::new();
        execute_setup(
            &mut executor,
            "(set-logic UFBV) (assert true) (assert false)",
        );
        executor.begin_public_solve(false);

        let permit = detached_test_permit(&executor, &[]).expect("plain hard query is eligible");

        assert_eq!(permit.roots(), executor.ctx.assertions);
        assert!(permit.inventory().assumptions.is_empty());
        assert!(permit.inventory().objectives.is_empty());
        assert!(permit.inventory().parsed_softs.is_empty());
        assert!(permit.inventory().native_softs.is_empty());
        assert!(permit.is_current(&executor));

        executor.ctx.assertions.swap(0, 1);
        assert!(!permit.is_current(&executor), "root order is authoritative");
    }

    #[test]
    fn later_public_query_epoch_retires_identical_permit() {
        let mut executor = Executor::new();
        execute_setup(&mut executor, "(set-logic UFBV) (assert true)");
        executor.begin_public_solve(false);
        let permit = detached_test_permit(&executor, &[]).expect("plain hard query is eligible");
        assert!(permit.is_current(&executor));

        executor.begin_public_solve(false);

        assert_eq!(permit.roots(), executor.ctx.assertions);
        assert_eq!(
            permit.source_context_stamp(),
            &executor.ctx.source_context_stamp()
        );
        assert!(
            !permit.is_current(&executor),
            "an identical later decision still has a fresh authority epoch"
        );
    }

    #[test]
    fn quantified_grant_authenticates_term_entries_not_numeric_slots() {
        let mut executor = Executor::new();
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let root = executor
            .ctx
            .terms
            .mk_fresh_var("grant_root", ay_core::Sort::Bool);
        let grant = QuantifiedSatAuthorityGrant::for_checked_roots(&executor, &[root]);

        let _suffix = executor
            .ctx
            .terms
            .mk_fresh_var("grant_suffix", ay_core::Sort::Bool);
        assert!(
            grant.is_current_for(&executor, &[root]),
            "append-only term growth preserves the authenticated root entry"
        );

        // Deliberately violate the rollback API's external-TermId contract to
        // model a future buggy speculative caller. The authority object must
        // still fail closed when the discarded numeric slot is reused.
        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor
            .ctx
            .terms
            .mk_fresh_var("replacement_root", ay_core::Sort::Bool);
        assert_eq!(replacement, root, "the canary must exercise slot reuse");
        assert!(
            !grant.is_current_for(&executor, &[replacement]),
            "a new term entry cannot inherit authority from a reused TermId"
        );
    }

    #[test]
    fn authored_permit_authenticates_term_entries_not_numeric_slots() {
        let mut executor = Executor::new();
        let checkpoint = executor.ctx.terms.rollback_checkpoint();
        let root = executor
            .ctx
            .terms
            .mk_fresh_var("authored_permit_root", ay_core::Sort::Bool);
        executor.ctx.assertions = vec![root];
        executor.begin_public_solve(false);
        let permit = detached_test_permit(&executor, &[]).expect("plain hard query is eligible");
        assert!(permit.is_current(&executor));

        // Deliberately violate the rollback API's external-TermId contract.
        // The replacement has the same numeric slot and leaves the captured
        // term count unchanged, so only entry identity can distinguish it.
        executor.ctx.terms.rollback_to(checkpoint);
        let replacement = executor
            .ctx
            .terms
            .mk_fresh_var("replacement_authored_permit_root", ay_core::Sort::Bool);
        assert_eq!(replacement, root, "the canary must exercise slot reuse");
        assert_eq!(executor.ctx.terms.len(), permit.inventory().term_count);
        assert!(
            !permit.is_current(&executor),
            "a new root entry cannot inherit authored-query authority"
        );
    }

    #[test]
    fn semantic_mutation_retires_permit() {
        let mut executor = Executor::new();
        execute_setup(&mut executor, "(set-logic UFBV) (assert true)");
        executor.begin_public_solve(false);
        let permit = detached_test_permit(&executor, &[]).expect("plain hard query is eligible");

        executor
            .execute(&Command::Push(1))
            .expect("push executes without a decision");
        executor
            .execute(&Command::Pop(1))
            .expect("pop restores the visible roots");

        assert_eq!(permit.roots(), executor.ctx.assertions);
        assert!(
            !permit.is_current(&executor),
            "the source stamp rejects a push/pop cycle with identical roots"
        );
    }

    #[test]
    fn term_growth_and_declaration_mutation_retire_detached_snapshots() {
        let mut term_growth = Executor::new();
        execute_setup(&mut term_growth, "(set-logic UFBV) (assert true)");
        term_growth.begin_public_solve(false);
        let permit = detached_test_permit(&term_growth, &[]).expect("plain hard query is eligible");
        let _ = term_growth
            .ctx
            .terms
            .mk_fresh_var("authority_suffix", ay_core::Sort::Bool);
        assert!(
            !permit.is_current(&term_growth),
            "term-store growth changes the exact authored inventory"
        );

        let mut declaration = Executor::new();
        execute_setup(&mut declaration, "(set-logic UFBV) (assert true)");
        declaration.begin_public_solve(false);
        let permit = detached_test_permit(&declaration, &[]).expect("plain hard query is eligible");
        declaration
            .execute(
                &parse("(declare-fun later ((_ BitVec 1)) (_ BitVec 1))")
                    .expect("parse declaration")[0],
            )
            .expect("declaration executes");
        assert!(
            !permit.is_current(&declaration),
            "a declaration mutation changes the source context stamp"
        );
    }

    #[test]
    fn objectives_and_both_soft_ownership_classes_are_ineligible() {
        let mut parsed = Executor::new();
        execute_setup(
            &mut parsed,
            "(set-logic QF_LIA) (assert-soft true :weight 2)",
        );
        parsed.begin_public_solve(false);
        assert!(detached_test_permit(&parsed, &[]).is_none());

        let mut objective = Executor::new();
        execute_setup(&mut objective, "(set-logic QF_LIA) (maximize 0)");
        objective.begin_public_solve(false);
        assert!(detached_test_permit(&objective, &[]).is_none());

        let mut native = Executor::new();
        native.begin_public_solve(false);
        let native_soft = NativeSoftQueryBinding {
            term: native.ctx.terms.true_term(),
            weight: 3,
            group: Some("g".to_string()),
        };
        assert!(detached_test_permit(&native, &[native_soft]).is_none());
    }

    #[test]
    fn command_origin_not_command_shape_controls_authority() {
        let mut executor = Executor::new();

        let commands = [Command::CheckSat];
        executor
            .execute_all(&commands)
            .expect("generic command stream executes");
        assert!(
            !executor.last_authored_query_authority_seen,
            "generic Executor::execute_all is used by CHC/internal adapters"
        );

        executor
            .execute(&Command::CheckSat)
            .expect("generic check-sat executes");
        assert!(
            !executor.last_authored_query_authority_seen,
            "generic Executor::execute is used by CHC/internal adapters"
        );

        executor
            .execute_authored(&Command::CheckSat)
            .expect("authored check-sat executes");
        assert!(executor.last_authored_query_authority_seen);

        executor
            .execute_authored(&Command::CheckSatAssuming(Vec::new()))
            .expect("empty check-sat-assuming executes");
        assert!(
            !executor.last_authored_query_authority_seen,
            "even an empty assumption command has a distinct, ineligible origin"
        );
    }
}
