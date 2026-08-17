// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native reducer/replay export for downstream consumers.

mod identity_validation;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use std::collections::VecDeque;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::str::FromStr;
use std::time::Duration;
// `SystemTime`/`UNIX_EPOCH` provide the wall-clock creation timestamp, which has
// no meaning inside a wasm sandbox (and `SystemTime::now()` panics there); the
// wasm build stamps the artifact with 0 instead.
#[cfg(not(target_arch = "wasm32"))]
use std::time::{SystemTime, UNIX_EPOCH};

use ay_core::panic_payload_to_string;
use ay_core::term::{Constant, RationalWrapper, Symbol, TermData};
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

use crate::api::types::{
    FrontendFuncDeclIdentity, FuncDecl, LimitKind, Logic, NativeReplayAdmissionToken,
    NativeReplayArtifact, NativeReplayAssertion, NativeReplayCheckedReplaySummary,
    NativeReplayDeclaration, NativeReplayEvent, NativeReplayEventKind,
    NativeReplayEvidenceManifest, NativeReplayFunctionDeclaration, NativeReplayMetadata,
    NativeReplayModelSummary, NativeReplayProofSummary, NativeReplayResourceUsage,
    NativeReplaySolveSummary, NativeReplaySolverIdentity, NativeReplayStatistics,
    NativeReplaySymbolIdentity, NativeReplaySymbolKind, NativeReplayTermNode,
    NativeReplayUnknownProgress, Term, NATIVE_REPLAY_EVIDENCE_MANIFEST_SCHEMA,
    NATIVE_REPLAY_SCHEMA,
};
use crate::api::{ProofAcceptanceMode, Solver, SolverError, UnsatProofArtifact};

/// Wall-clock creation timestamp for the replay artifact, in Unix epoch
/// milliseconds.
#[cfg(not(target_arch = "wasm32"))]
fn created_unix_ms() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_millis())
}

/// A wasm sandbox has no wall clock; stamp the artifact with 0.
#[cfg(target_arch = "wasm32")]
fn created_unix_ms() -> u128 {
    0
}

impl Solver {
    pub(crate) fn record_native_replay_event(&mut self, kind: NativeReplayEventKind) {
        let index = self.native_replay_events.len();
        self.native_replay_events
            .push(NativeReplayEvent::new(index, kind, self.scope_level));
    }

    /// Return the native API event trace captured so far.
    #[must_use]
    pub fn native_replay_events(&self) -> &[NativeReplayEvent] {
        &self.native_replay_events
    }

    /// Export a native reducer/replay artifact for the current solver state.
    ///
    /// Pass the `SolveDetails` returned by the just-completed solve to attach
    /// the exact Unknown/proof/model evidence from that call.
    #[must_use]
    pub fn export_native_replay_artifact(
        &self,
        metadata: NativeReplayMetadata,
        solve: Option<&crate::api::types::SolveDetails>,
    ) -> NativeReplayArtifact {
        // Normalize an accepted-but-unmapped declared logic (a z3-recognized
        // token AY does not map to a category) to `None` for export: the
        // session was routed by content detection exactly as the unset case, and
        // recording it verbatim would make replay's `Logic::from_str`
        // (native_replay.rs:~204) error on the unmapped token. Recording
        // `None` → `"ALL"` on replay is semantically exact. The fail-closed
        // combined logics are NOT `declared_logic_routes_as_all`, so they are
        // preserved verbatim.
        let logic = self
            .executor
            .logic()
            .filter(|l| !crate::logic_detection::declared_logic_routes_as_all(l))
            .map(str::to_string);
        let selected_route = logic.as_deref().map(|logic| format!("native-api:{logic}"));
        let mut replay_gaps = Vec::new();
        let mut declarations: Vec<_> = self
            .var_names
            .iter()
            .filter_map(|(&term, name)| {
                self.var_sorts
                    .get(&term)
                    .cloned()
                    .map(|sort| {
                        let core_name =
                            authenticated_native_constant_core_name(self, name, term).unwrap_or_else(
                                || {
                                    replay_gaps.push(format!(
                                        "native declaration `{name}` lacks exact live frontend identity metadata"
                                    ));
                                    // Deliberately cannot authenticate as an allocator-private
                                    // declaration. The replay validator will reject this artifact
                                    // instead of guessing an identity relation.
                                    format!("__ay_native_replay_unauthenticated_{}", term.0)
                                },
                            );
                        NativeReplayDeclaration {
                            name: name.clone(),
                            core_name,
                            term,
                            sort,
                        }
                    })
            })
            .collect();
        declarations.sort_by_key(|decl| decl.term);

        let depths = self.executor.context().active_assertion_min_scope_depths();
        let mut active_assertion_metadata =
            active_assertion_metadata_from_events(&self.native_replay_events);
        let mut assertion_occurrences = HashMap::default();
        let assertions: Vec<_> = self
            .executor
            .context()
            .assertions
            .iter()
            .enumerate()
            .map(|(index, &term)| {
                let occurrence = assertion_occurrences.entry(term).or_insert(0usize);
                let metadata = active_assertion_metadata
                    .get_mut(&term)
                    .and_then(VecDeque::pop_front);
                let (name, scope_depth) = if let Some(metadata) = metadata {
                    (metadata.name, metadata.scope_depth)
                } else {
                    (
                        assertion_name_for(&self.native_replay_events, term, *occurrence),
                        depths.get(&term).copied().unwrap_or_default(),
                    )
                };
                *occurrence += 1;
                NativeReplayAssertion {
                    index,
                    term,
                    name,
                    scope_depth,
                }
            })
            .collect();
        let mut roots: Vec<TermId> = assertions.iter().map(|assertion| assertion.term).collect();
        if let Some(assumptions) = final_check_sat_assumptions(&self.native_replay_events) {
            roots.extend_from_slice(assumptions);
        }
        let replay_terms = replay_term_dependency_closure(self.terms(), &roots);
        let reachable: HashSet<TermId> = replay_terms.iter().copied().collect();
        declarations.retain(|declaration| reachable.contains(&declaration.term));

        let mut needed_functions: HashSet<String> = HashSet::default();
        for &term in &replay_terms {
            if let TermData::App(Symbol::Named(name), _) = self.terms().get(term) {
                needed_functions.insert(name.clone());
            }
            // Higher-order array wrappers encode the referenced declaration in
            // their symbol token rather than as a child term.
            if let Some(name) = self.terms().get_as_array_func(term) {
                needed_functions.insert(name.to_string());
            }
            if let Some((name, _)) = self.terms().get_array_map(term) {
                needed_functions.insert(name.to_string());
            }
        }
        let datatype_declarations = datatype_declarations_from_events(&self.native_replay_events);
        let function_declarations = function_declarations_from_events(
            self,
            &self.native_replay_events,
            &needed_functions,
            &mut replay_gaps,
        );
        let symbol_identities = export_native_replay_symbol_identities(
            self,
            &declarations,
            &function_declarations,
            &datatype_declarations,
            &mut replay_gaps,
        );

        let terms = replay_terms
            .into_iter()
            .map(|id| NativeReplayTermNode {
                id,
                sort: self.terms().sort(id).clone(),
                data: self.terms().get(id).clone(),
                is_datatype_constructor: match self.terms().get(id) {
                    TermData::Var(name, _) => {
                        self.executor.context().is_constructor(name).is_some()
                            && self
                                .executor
                                .context()
                                .symbol_info_by_identity(name)
                                .is_some_and(|info| info.term == Some(id))
                    }
                    _ => false,
                },
            })
            .collect();
        let timeout_ms = self.timeout.map(|duration| duration.as_millis());
        let solve_summary = solve.map(|details| solve_summary_from_details(details, timeout_ms));
        let unsupported_atoms = solve
            .and_then(|details| details.executor_error.as_ref())
            .filter(|detail| detail.to_ascii_lowercase().contains("unsupported"))
            .map(|detail| vec![detail.clone()])
            .unwrap_or_default();
        if solve.is_none() {
            replay_gaps.push("solve details were not captured".to_string());
        }

        NativeReplayArtifact {
            schema: NATIVE_REPLAY_SCHEMA.to_string(),
            ay_revision: ay_revision(),
            ay_version: env!("CARGO_PKG_VERSION").to_string(),
            created_unix_ms: created_unix_ms(),
            metadata,
            logic,
            selected_route,
            scope_depth: self.scope_level,
            timeout_ms,
            events: self.native_replay_events.clone(),
            declarations,
            function_declarations,
            symbol_identities,
            assertions,
            terms,
            solve: solve_summary,
            checked_replay: None,
            admission_token: None,
            panic_payload: None,
            unsupported_atoms,
            replay_gaps,
        }
    }

    /// Run `check_sat_with_details` through a panic boundary and return a
    /// replay artifact even when the solve panics.
    #[must_use]
    pub fn try_check_sat_with_native_replay(
        &mut self,
        metadata: NativeReplayMetadata,
    ) -> NativeReplayArtifact {
        match catch_unwind(AssertUnwindSafe(|| self.check_sat_with_details())) {
            Ok(details) => self.export_native_replay_artifact(metadata, Some(&details)),
            Err(payload) => {
                let mut artifact = self.export_native_replay_artifact(metadata, None);
                artifact.panic_payload = Some(panic_payload_to_string(payload.as_ref()));
                artifact
                    .replay_gaps
                    .push("solve panicked before SolveDetails was available".to_string());
                artifact
            }
        }
    }

    /// Replay an exported native artifact in a fresh solver and return the new
    /// solve envelope.
    ///
    /// The replay uses the captured active assertion set as the executable
    /// slice. The event trace remains attached to the artifact for diagnosing
    /// push/pop history and reducer minimization.
    ///
    /// # Errors
    ///
    /// Returns an error when the artifact has an unsupported logic, missing
    /// term node, or contains a future term kind this version cannot rebuild.
    pub fn replay_native_replay_artifact(
        artifact: &NativeReplayArtifact,
    ) -> Result<crate::api::types::SolveDetails, SolverError> {
        let (details, _) = Self::replay_native_replay_artifact_impl(artifact, None, false)?;
        Ok(details)
    }

    /// Replay an exported native artifact with a caller-bounded, strict proof
    /// check for any UNSAT result.
    ///
    /// The effective wall-clock bound is the smaller of `timeout` and the
    /// artifact's recorded timeout (when present). An `Ok` UNSAT result is
    /// therefore an authority-bearing result: strict proof checking ran, a
    /// complete non-empty proof artifact exists, every proof step was checked,
    /// and the checker recorded no failures, holes, or trust fallbacks. Missing
    /// or partial evidence returns an error instead of exposing plain UNSAT.
    /// SAT and Unknown remain diagnostic `SolveDetails`.
    ///
    /// The ordinary [`Self::replay_native_replay_artifact`] entrypoint remains
    /// unchanged and does not opt into proof production.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed replay artifacts, option setup failures,
    /// or an UNSAT result that does not meet the strict proof-authority
    /// postcondition.
    pub fn replay_native_replay_artifact_with_proofs(
        artifact: &NativeReplayArtifact,
        timeout: Duration,
    ) -> Result<crate::api::types::SolveDetails, SolverError> {
        let (details, _) = Self::replay_native_replay_artifact_impl(artifact, Some(timeout), true)?;
        Self::require_native_replay_proof_authority(details)
    }

    /// Replay a native artifact once and return its checked UNSAT proof
    /// artifact alongside the solve envelope.
    ///
    /// This has the same strict proof-authority contract and timeout behavior
    /// as [`Self::replay_native_replay_artifact_with_proofs`]. For an accepted
    /// UNSAT result, the second tuple element is guaranteed to be `Some` and
    /// its [`UnsatProofArtifact::strict_verdict`] is verified. SAT and Unknown
    /// remain diagnostic results and return `None` for the proof artifact.
    /// The artifact is exported from the solver instance that performed this
    /// replay; the obligation is not solved a second time.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed replay artifacts, option setup failures,
    /// or an UNSAT result that lacks a complete strict proof artifact.
    pub fn replay_native_replay_artifact_with_checked_proof(
        artifact: &NativeReplayArtifact,
        timeout: Duration,
    ) -> Result<(crate::api::types::SolveDetails, Option<UnsatProofArtifact>), SolverError> {
        let (details, replay_solver) =
            Self::replay_native_replay_artifact_impl(artifact, Some(timeout), true)?;
        let details = Self::require_native_replay_proof_authority(details)?;
        if !details.result.is_unsat() {
            return Ok((details, None));
        }

        let proof = replay_solver.export_last_unsat_artifact().ok_or_else(|| {
            native_replay_proof_error(
                "strict UNSAT replay did not retain an exportable proof artifact".to_string(),
            )
        })?;
        proof
            .accept_for_consumer(ProofAcceptanceMode::Strict)
            .map_err(|error| native_replay_proof_error(error.to_string()))?;
        Ok((details, Some(proof)))
    }

    /// Strictly replay an artifact and seal the resulting evidence in memory.
    ///
    /// This is the only workflow that can make
    /// [`NativeReplayEvidenceManifest::admitted`] true. The supplied identity
    /// may contribute the owning backend's executable SHA-256, but its engine,
    /// AY revision, and AY version must exactly match this replay build and the
    /// artifact's native route. This API validates and binds the SHA-256 claim;
    /// measuring the owning executable remains the backend's responsibility.
    /// The effective timeout is recorded into the returned artifact before
    /// replay so the sealed options digest describes the execution that
    /// actually ran.
    ///
    /// Diagnostic [`NativeReplayArtifact::with_checked_replay`] summaries do
    /// not carry this authority, and diagnostic JSON deliberately cannot
    /// serialize or restore it.
    ///
    /// # Errors
    ///
    /// Returns an error when the solver identity is not the current replay
    /// identity, its binary SHA-256 is missing or malformed, the artifact is
    /// malformed, or an UNSAT result lacks complete strict proof authority.
    pub fn replay_native_replay_artifact_for_evidence(
        mut artifact: NativeReplayArtifact,
        solver_identity: NativeReplaySolverIdentity,
        timeout: Duration,
    ) -> Result<NativeReplayArtifact, SolverError> {
        validate_native_replay_evidence_solver_identity(&artifact, &solver_identity)?;
        require_native_replay_evidence_identity_table(&artifact)?;

        // A caller-supplied summary/token is never an input to the authoritative
        // execution. Record the exact effective millisecond timeout and rerun.
        artifact.checked_replay = None;
        artifact.admission_token = None;
        let caller_timeout_ms = timeout.as_millis().min(u128::from(u64::MAX));
        artifact.timeout_ms = Some(artifact.timeout_ms.map_or(caller_timeout_ms, |recorded| {
            recorded.min(caller_timeout_ms)
        }));

        let (details, _) = Self::replay_native_replay_artifact_impl(&artifact, None, true)?;
        let details = Self::require_native_replay_proof_authority(details)?;
        artifact.checked_replay = Some(checked_replay_summary_from_details(
            artifact.solve.as_ref(),
            &details,
        ));
        artifact.admission_token = Some(native_replay_admission_token(&artifact, solver_identity)?);
        Ok(artifact)
    }

    fn replay_native_replay_artifact_impl(
        artifact: &NativeReplayArtifact,
        caller_timeout: Option<Duration>,
        require_proofs: bool,
    ) -> Result<(crate::api::types::SolveDetails, Self), SolverError> {
        let logic = Logic::from_str(artifact.logic.as_deref().unwrap_or("ALL"))?;
        validate_native_replay_identity_tables(artifact)?;
        let mut solver = Self::try_new(logic)?;

        if require_proofs {
            solver.set_produce_proofs(true);
            solver.try_set_option(":check-proofs-strict", "true")?;
        }

        let artifact_timeout = artifact
            .timeout_ms
            .map(|timeout_ms| Duration::from_millis(timeout_ms.min(u128::from(u64::MAX)) as u64));
        let effective_timeout = match (caller_timeout, artifact_timeout) {
            (Some(caller), Some(recorded)) => Some(caller.min(recorded)),
            (Some(caller), None) => Some(caller),
            (None, recorded) => recorded,
        };
        if let Some(timeout) = effective_timeout {
            solver.set_timeout(Some(timeout));
        }

        let (identity_remap, predeclared_constants) =
            replay_native_declarations_in_event_order(artifact, &mut solver)?;
        validate_native_replay_declaration_sorts(artifact, &solver, &identity_remap)?;

        let declarations: HashMap<_, _> = artifact
            .declarations
            .iter()
            .map(|decl| (decl.term, decl))
            .collect();
        let source_nodes: HashMap<_, _> =
            artifact.terms.iter().map(|node| (node.id, node)).collect();
        let mut term_map: HashMap<TermId, TermId> = HashMap::default();
        // Export stores the dependency closure in deterministic topological
        // order. Preserve it here instead of cloning/sorting the entire slice.
        for node in &artifact.terms {
            if term_map.contains_key(&node.id) {
                return Err(native_replay_artifact_error(format!(
                    "duplicate term node id {}",
                    node.id.0
                )));
            }
            let remapped_node = identity_remap.remap_term_node(node)?;
            let replayed = rebuild_term_node(
                &mut solver,
                node,
                &remapped_node,
                &declarations,
                &source_nodes,
                &term_map,
                &predeclared_constants,
            )?;
            let actual_sort = solver.terms().sort(replayed);
            if actual_sort != &remapped_node.sort {
                return Err(SolverError::InvalidArgument {
                    operation: "native_replay",
                    message: format!(
                        "term {} records sort {}, but reconstruction produced {actual_sort}",
                        node.id.0, remapped_node.sort
                    ),
                });
            }
            term_map.insert(node.id, replayed);
        }

        let mut assertions = artifact.assertions.clone();
        assertions.sort_by_key(|assertion| assertion.index);
        for assertion in assertions {
            let term = map_term(assertion.term, &term_map)?;
            let term = solver.wrap_term(term);
            if let Some(name) = assertion.name {
                solver.try_assert_named(term, &name)?;
            } else {
                solver.try_assert_term(term)?;
            }
        }

        let details = if let Some(assumptions) = final_check_sat_assumptions(&artifact.events) {
            let assumptions = assumptions
                .iter()
                .map(|&term| map_term(term, &term_map).map(|id| solver.wrap_term(id)))
                .collect::<Result<Vec<_>, SolverError>>()?;
            solver.check_sat_assuming_with_details(&assumptions).solve
        } else {
            solver.check_sat_with_details()
        };
        Ok((details, solver))
    }

    fn require_native_replay_proof_authority(
        details: crate::api::types::SolveDetails,
    ) -> Result<crate::api::types::SolveDetails, SolverError> {
        if !details.result.is_unsat() {
            return Ok(details);
        }

        let stats = &details.statistics;
        let checker_failures = stats.get_int("proof_checker_failures");
        let checked_steps = stats.get_int("proof_checker_checked_steps");
        let total_steps = stats.get_int("proof_checker_total_steps");
        let skipped_holes = stats.get_int("proof_checker_skipped_hole_steps");
        let trust_fallbacks = stats.get_int("proof_trust");
        let proof_checking_active =
            cfg!(feature = "proof-checker") && details.verification_level.has_proof_checking();
        let all_steps_checked = matches!(
            (checked_steps, total_steps),
            (Some(checked), Some(total)) if total > 0 && checked == total
        );
        let accepted = proof_checking_active
            && details.verification.unsat_proof_available
            && details.verification.unsat_proof_strictly_verified
            && details.verification.unsat_proof_checker_failures == 0
            && checker_failures == Some(0)
            && stats.proof_complete
            && trust_fallbacks == Some(0)
            && skipped_holes == Some(0)
            && all_steps_checked;

        if accepted {
            return Ok(details);
        }

        Err(SolverError::InvalidArgument {
            operation: "native_replay_with_proofs",
            message: format!(
                "UNSAT replay lacks strict proof authority \
                 (checker_active={proof_checking_active}, \
                 artifact_available={}, summary_checker_failures={}, \
                 strictly_verified={}, \
                 raw_checker_failures={checker_failures:?}, \
                 proof_complete={}, proof_trust={trust_fallbacks:?}, \
                 checked_steps={checked_steps:?}, total_steps={total_steps:?}, \
                 skipped_holes={skipped_holes:?})",
                details.verification.unsat_proof_available,
                details.verification.unsat_proof_checker_failures,
                details.verification.unsat_proof_strictly_verified,
                stats.proof_complete,
            ),
        })
    }

    /// Parse and replay an exported native replay JSON document.
    ///
    /// # Errors
    ///
    /// Returns an error when the JSON is malformed, uses an unsupported schema,
    /// or contains a term/sort shape this version cannot rebuild.
    pub fn replay_native_replay_json_str(
        json: &str,
    ) -> Result<crate::api::types::SolveDetails, SolverError> {
        let artifact = NativeReplayArtifact::from_json_str(json)?;
        Self::replay_native_replay_artifact(&artifact)
    }
}

/// Resolve a native constant's public API key to its exact live core identity.
///
/// Export must not infer this relation from spelling alone: the private core
/// name is meaningful only when the frontend records one unique, live,
/// nullary uninterpreted declaration whose bound term is the exported Var.
fn authenticated_native_constant_core_name(
    solver: &Solver,
    public_name: &str,
    term: TermId,
) -> Option<String> {
    let context = solver.executor.context();
    let mut matches = context.symbols_iter().filter(|(surface, info)| {
        surface.as_str() == public_name
            && info.term == Some(term)
            && info.arg_sorts.is_empty()
            && info.sort == *solver.terms().sort(term)
            && info.declaration_kind() == ay_frontend::DeclarationKind::Uninterpreted
            && context.effective_declaration_kind(info.declaration_id())
                == Some(ay_frontend::DeclarationKind::Uninterpreted)
    });
    let (surface, info) = matches.next()?;
    if matches.next().is_some() {
        return None;
    }

    let core_name = context.symbol_identity_name(surface, info);
    if !matches!(solver.terms().get(term), TermData::Var(name, _) if name == core_name) {
        return None;
    }

    let mut owners = context.symbols_iter().filter(|(surface, candidate)| {
        context.symbol_identity_name(surface, candidate) == core_name
    });
    let (owner_surface, owner) = owners.next()?;
    if owner_surface.as_str() != public_name
        || owner.declaration_id() != info.declaration_id()
        || owner.declaration_kind() != info.declaration_kind()
        || owners.next().is_some()
    {
        return None;
    }
    Some(core_name.to_string())
}

fn is_allocator_private_declaration_identity(name: &str) -> bool {
    name.strip_prefix("__ay_overload_").is_some_and(|suffix| {
        !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
    })
}

#[cfg(test)]
mod proof_required_authority_tests {
    use super::*;
    use crate::api::{Logic, Sort};

    fn strict_boolean_unsat_details() -> crate::api::types::SolveDetails {
        let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
        solver.set_produce_proofs(true);
        solver
            .try_set_option(":check-proofs-strict", "true")
            .expect("strict proof option");
        let p = solver.declare_const("p", Sort::Bool);
        let not_p = solver.not(p);
        solver.assert_term(p);
        solver.assert_term(not_p);
        solver.check_sat_with_details()
    }

    #[cfg(feature = "proof-checker")]
    #[test]
    fn proof_required_authority_rejects_holes_and_checker_failures() {
        let details = strict_boolean_unsat_details();
        assert!(details.verification.unsat_proof_strictly_verified);
        let _ = Solver::require_native_replay_proof_authority(details.clone())
            .expect("strict complete Boolean proof must carry authority");
        let assert_rejected = |details| {
            assert!(matches!(
                Solver::require_native_replay_proof_authority(details),
                Err(SolverError::InvalidArgument {
                    operation: "native_replay_with_proofs",
                    ..
                })
            ));
        };

        let total = details
            .statistics
            .get_int("proof_checker_total_steps")
            .expect("strict checker total");
        assert!(total > 0);

        let mut ordinary_authority = details.clone();
        ordinary_authority
            .verification
            .unsat_proof_strictly_verified = false;
        assert_rejected(ordinary_authority);

        // Model the partial checker's intentional Hole behavior: it can report
        // zero failures while skipping one step. The proof-required boundary
        // must reject that evidence even though the summary failure count is 0.
        let mut holey = details.clone();
        holey.statistics.proof_complete = false;
        holey.statistics.set_int("proof_checker_failures", 0);
        holey
            .statistics
            .set_int("proof_checker_skipped_hole_steps", 1);
        holey
            .statistics
            .set_int("proof_checker_checked_steps", total - 1);
        assert_rejected(holey);

        let mut checker_failed = details.clone();
        checker_failed
            .statistics
            .set_int("proof_checker_failures", 1);
        checker_failed.verification.unsat_proof_checker_failures = 1;
        assert_rejected(checker_failed);

        let mut missing_raw_stats = details.clone();
        for key in [
            "proof_checker_failures",
            "proof_checker_checked_steps",
            "proof_checker_total_steps",
            "proof_checker_skipped_hole_steps",
        ] {
            missing_raw_stats.statistics.extra.remove(key);
        }
        assert_rejected(missing_raw_stats);

        let mut trusted = details.clone();
        trusted.statistics.set_int("proof_trust", 1);
        assert_rejected(trusted);

        let mut incomplete = details.clone();
        incomplete.statistics.proof_complete = false;
        assert_rejected(incomplete);

        let mut empty = details.clone();
        empty.statistics.set_int("proof_checker_total_steps", 0);
        empty.statistics.set_int("proof_checker_checked_steps", 0);
        assert_rejected(empty);

        let mut unavailable = details;
        unavailable.verification.unsat_proof_available = false;
        assert_rejected(unavailable);
    }

    #[cfg(not(feature = "proof-checker"))]
    #[test]
    fn proof_required_authority_rejects_build_without_checker() {
        let details = strict_boolean_unsat_details();
        assert!(matches!(
            Solver::require_native_replay_proof_authority(details),
            Err(SolverError::InvalidArgument {
                operation: "native_replay_with_proofs",
                ..
            })
        ));
    }
}

impl NativeReplayArtifact {
    /// Attach diagnostic checked-replay status supplied by the caller.
    ///
    /// This convenience method is intentionally non-authoritative: it clears
    /// any in-memory admission token. Use
    /// [`Solver::replay_native_replay_artifact_for_evidence`] when a compiler
    /// verifier backend needs an admissible manifest.
    #[must_use]
    pub fn with_checked_replay(mut self, replay: &crate::api::types::SolveDetails) -> Self {
        self.admission_token = None;
        self.checked_replay = Some(checked_replay_summary_from_details(
            self.solve.as_ref(),
            replay,
        ));
        self
    }

    /// Build a fail-closed content-addressed evidence manifest for this artifact.
    #[must_use]
    pub fn evidence_manifest(&self) -> NativeReplayEvidenceManifest {
        let solver_identity = self
            .admission_token
            .as_ref()
            .map(|token| token.solver_identity.clone())
            .unwrap_or_else(|| {
                NativeReplaySolverIdentity::current_for_engine(native_replay_expected_engine(self))
            });
        self.evidence_manifest_with_solver_identity(solver_identity)
    }

    /// Build a fail-closed content-addressed evidence manifest with an explicit
    /// solver identity supplied by the owning verifier backend.
    #[must_use]
    pub fn evidence_manifest_with_solver_identity(
        &self,
        solver_identity: NativeReplaySolverIdentity,
    ) -> NativeReplayEvidenceManifest {
        NativeReplayEvidenceManifest::from_artifact(self, solver_identity)
    }

    /// Convert the artifact to diagnostic JSON.
    #[must_use]
    pub fn to_json_value(&self) -> Value {
        json!({
            "schema": self.schema,
            "ay_revision": self.ay_revision,
            "ay_version": self.ay_version,
            "created_unix_ms": u128_json(self.created_unix_ms),
            "metadata": metadata_json(&self.metadata),
            "logic": self.logic,
            "selected_route": self.selected_route,
            "scope_depth": self.scope_depth,
            "timeout_ms": self.timeout_ms.map(u128_json),
            "events": self.events.iter().map(event_json).collect::<Vec<_>>(),
            "declarations": self.declarations.iter().map(declaration_json).collect::<Vec<_>>(),
            "function_declarations": self
                .function_declarations
                .iter()
                .map(function_declaration_json)
                .collect::<Vec<_>>(),
            "symbol_identities": self
                .symbol_identities
                .iter()
                .map(symbol_identity_json)
                .collect::<Vec<_>>(),
            "assertions": self.assertions.iter().map(assertion_json).collect::<Vec<_>>(),
            "terms": self.terms.iter().map(term_node_json).collect::<Vec<_>>(),
            "solve": self.solve.as_ref().map(solve_json),
            "checked_replay": self.checked_replay.as_ref().map(checked_replay_json),
            "panic_payload": self.panic_payload,
            "unsupported_atoms": self.unsupported_atoms,
            "replay_gaps": self.replay_gaps,
        })
    }

    /// Convert the artifact to pretty-printed diagnostic JSON.
    #[must_use]
    pub fn to_pretty_json(&self) -> String {
        serde_json::to_string_pretty(&self.to_json_value())
            .expect("native replay artifact JSON value must serialize")
    }

    /// Parse a native replay artifact from its diagnostic JSON representation.
    ///
    /// # Errors
    ///
    /// Returns an error when required fields are absent, when the schema is not
    /// `ay.native-replay.v1`, or when a captured term/sort is outside the
    /// replayable JSON subset.
    pub fn from_json_value(value: &Value) -> Result<Self, SolverError> {
        native_replay_artifact_from_json(value)
    }

    /// Parse a native replay artifact from a JSON string.
    ///
    /// # Errors
    ///
    /// Returns an error when the string is not valid JSON or when
    /// [`Self::from_json_value`] rejects the decoded value.
    pub fn from_json_str(json: &str) -> Result<Self, SolverError> {
        let value = serde_json::from_str(json)
            .map_err(|err| native_replay_json_error(format!("invalid JSON: {err}")))?;
        Self::from_json_value(&value)
    }
}

impl NativeReplaySolverIdentity {
    /// Build a solver identity for the current AY native API route.
    #[must_use]
    pub fn current_for_engine(engine: impl Into<String>) -> Self {
        Self {
            engine: engine.into(),
            ay_revision: ay_revision(),
            ay_version: env!("CARGO_PKG_VERSION").to_string(),
            solver_binary_sha256: None,
        }
    }

    /// Override the recorded AY revision.
    #[must_use]
    pub fn with_ay_revision(mut self, ay_revision: impl Into<String>) -> Self {
        self.ay_revision = ay_revision.into();
        self
    }

    /// Attach the SHA-256 of the solver binary or owning package.
    #[must_use]
    pub fn with_solver_binary_sha256(mut self, solver_binary_sha256: impl Into<String>) -> Self {
        self.solver_binary_sha256 = Some(solver_binary_sha256.into());
        self
    }

    /// Convert the solver identity to stable JSON.
    #[must_use]
    pub fn to_json_value(&self) -> Value {
        solver_identity_json(self)
    }

    /// SHA-256 of the stable solver identity JSON.
    #[must_use]
    pub fn identity_sha256(&self) -> String {
        sha256_json(&self.to_json_value())
    }
}

impl NativeReplayEvidenceManifest {
    fn from_artifact(
        artifact: &NativeReplayArtifact,
        solver_identity: NativeReplaySolverIdentity,
    ) -> Self {
        let checked = artifact.checked_replay.as_ref();
        let solver_identity_sha256 = solver_identity.identity_sha256();
        let problem_sha256 = sha256_json(&native_replay_problem_binding_json(artifact));
        let options_sha256 = sha256_json(&native_replay_options_binding_json(artifact));
        let replay_artifact_sha256 = sha256_json(&artifact.to_json_value());
        let checked_summary_sha256 = native_replay_checked_summary_sha256(checked);
        let checked_result = native_replay_checked_result(checked);
        let admission_rejection_reasons = native_replay_manifest_rejection_reasons(
            artifact,
            &solver_identity,
            checked,
            &solver_identity_sha256,
            &problem_sha256,
            &options_sha256,
            &checked_summary_sha256,
            &replay_artifact_sha256,
        );
        let unknown_reason = checked
            .and_then(|summary| {
                summary
                    .replay_unknown_reason
                    .clone()
                    .or_else(|| summary.original_unknown_reason.clone())
            })
            .or_else(|| {
                artifact
                    .solve
                    .as_ref()
                    .and_then(|solve| solve.unknown_reason.clone())
            });
        let mut manifest = Self {
            schema: NATIVE_REPLAY_EVIDENCE_MANIFEST_SCHEMA.to_string(),
            solver_identity,
            solver_identity_sha256,
            problem_sha256,
            options_sha256,
            replay_artifact_sha256,
            checked_result,
            original_result: checked
                .and_then(|summary| summary.original_result.clone())
                .or_else(|| artifact.solve.as_ref().map(|solve| solve.result.clone())),
            replay_result: checked.map(|summary| summary.replay_result.clone()),
            proof_status: checked.map(|summary| summary.replay_proof_status.clone()),
            model_status: checked.map(|summary| summary.replay_model_status.clone()),
            unknown_reason,
            unsupported_atoms: artifact.unsupported_atoms.clone(),
            replay_gaps: artifact.replay_gaps.clone(),
            admission_rejection_reasons,
            manifest_sha256: String::new(),
            admission_seal_sha256: None,
        };
        let may_admit = manifest.admission_rejection_reasons.is_empty();
        let body_sha256 = sha256_json(&manifest.to_json_body_with_admitted(may_admit));
        manifest.manifest_sha256.clone_from(&body_sha256);
        if may_admit {
            manifest.admission_seal_sha256 = Some(body_sha256);
        }
        manifest
    }

    /// Whether a compiler verifier backend may admit this manifest.
    #[must_use]
    pub fn admitted(&self) -> bool {
        if !self.admission_rejection_reasons.is_empty() {
            return false;
        }
        let expected = sha256_json(&self.to_json_body_with_admitted(true));
        self.admission_seal_sha256.as_deref() == Some(expected.as_str())
            && self.manifest_sha256 == expected
    }

    /// Convert the manifest to stable JSON.
    #[must_use]
    pub fn to_json_value(&self) -> Value {
        let mut value = self.to_json_body();
        value
            .as_object_mut()
            .expect("native replay evidence manifest body must be an object")
            .insert(
                "manifest_sha256".to_string(),
                Value::String(self.manifest_sha256.clone()),
            );
        value
    }

    /// Convert the manifest to pretty-printed stable JSON.
    #[must_use]
    pub fn to_pretty_json(&self) -> String {
        serde_json::to_string_pretty(&self.to_json_value())
            .expect("native replay evidence manifest JSON value must serialize")
    }

    fn to_json_body(&self) -> Value {
        self.to_json_body_with_admitted(self.admitted())
    }

    fn to_json_body_with_admitted(&self, admitted: bool) -> Value {
        json!({
            "schema": self.schema,
            "solver_identity": solver_identity_json(&self.solver_identity),
            "solver_identity_sha256": self.solver_identity_sha256,
            "problem_sha256": self.problem_sha256,
            "options_sha256": self.options_sha256,
            "replay_artifact_sha256": self.replay_artifact_sha256,
            "checked_result": self.checked_result,
            "original_result": self.original_result,
            "replay_result": self.replay_result,
            "proof_status": self.proof_status,
            "model_status": self.model_status,
            "unknown_reason": self.unknown_reason,
            "unsupported_atoms": self.unsupported_atoms,
            "replay_gaps": self.replay_gaps,
            "admission_rejection_reasons": self.admission_rejection_reasons,
            "admitted": admitted,
        })
    }
}

fn ay_revision() -> String {
    option_env!("AY_BUILD_COMMIT")
        .or(option_env!("VERGEN_GIT_SHA"))
        .or(option_env!("GIT_SHA"))
        .unwrap_or("unknown")
        .to_string()
}

fn native_replay_expected_selected_route(artifact: &NativeReplayArtifact) -> Option<String> {
    artifact
        .logic
        .as_deref()
        .map(|logic| format!("native-api:{logic}"))
}

fn native_replay_expected_engine(artifact: &NativeReplayArtifact) -> String {
    native_replay_expected_selected_route(artifact).unwrap_or_else(|| "native-api".to_string())
}

fn well_formed_sha256(hash: &str) -> bool {
    hash.len() == 64 && hash.chars().all(|ch| ch.is_ascii_hexdigit())
}

fn validate_native_replay_evidence_solver_identity(
    artifact: &NativeReplayArtifact,
    solver_identity: &NativeReplaySolverIdentity,
) -> Result<(), SolverError> {
    let expected_route = native_replay_expected_selected_route(artifact);
    if artifact.selected_route.as_deref() != expected_route.as_deref() {
        return Err(native_replay_evidence_error(format!(
            "artifact selected route {:?} does not match its current native route {:?}",
            artifact.selected_route, expected_route
        )));
    }

    let expected =
        NativeReplaySolverIdentity::current_for_engine(native_replay_expected_engine(artifact));
    if solver_identity.engine != expected.engine
        || solver_identity.ay_revision != expected.ay_revision
        || solver_identity.ay_version != expected.ay_version
    {
        return Err(native_replay_evidence_error(format!(
            "solver identity does not match the current replay build/route \
             (expected engine={}, revision={}, version={})",
            expected.engine, expected.ay_revision, expected.ay_version
        )));
    }
    match solver_identity.solver_binary_sha256.as_deref() {
        Some(hash) if well_formed_sha256(hash) => Ok(()),
        Some(_) => Err(native_replay_evidence_error(
            "solver binary sha256 is malformed",
        )),
        None => Err(native_replay_evidence_error(
            "solver binary sha256 is missing",
        )),
    }
}

fn native_replay_evidence_requires_identity_table(artifact: &NativeReplayArtifact) -> bool {
    !artifact.declarations.is_empty()
        || !artifact.function_declarations.is_empty()
        || artifact
            .events
            .iter()
            .any(|event| matches!(&event.kind, NativeReplayEventKind::DeclareDatatype { .. }))
}

fn require_native_replay_evidence_identity_table(
    artifact: &NativeReplayArtifact,
) -> Result<(), SolverError> {
    if native_replay_evidence_requires_identity_table(artifact)
        && artifact.symbol_identities.is_empty()
    {
        return Err(native_replay_evidence_error(
            "compiler evidence requires an authenticated symbol identity table",
        ));
    }
    Ok(())
}

fn native_replay_checked_summary_sha256(
    checked: Option<&NativeReplayCheckedReplaySummary>,
) -> String {
    let value = checked.map_or(Value::Null, checked_replay_json);
    sha256_json(&value)
}

fn native_replay_admission_token(
    artifact: &NativeReplayArtifact,
    solver_identity: NativeReplaySolverIdentity,
) -> Result<NativeReplayAdmissionToken, SolverError> {
    if artifact.checked_replay.is_none() {
        return Err(native_replay_evidence_error(
            "strict replay did not produce a checked replay summary",
        ));
    }
    Ok(NativeReplayAdmissionToken {
        solver_identity_sha256: solver_identity.identity_sha256(),
        problem_sha256: sha256_json(&native_replay_problem_binding_json(artifact)),
        options_sha256: sha256_json(&native_replay_options_binding_json(artifact)),
        checked_summary_sha256: native_replay_checked_summary_sha256(
            artifact.checked_replay.as_ref(),
        ),
        replay_artifact_sha256: sha256_json(&artifact.to_json_value()),
        solver_identity,
    })
}

fn native_replay_problem_binding_json(artifact: &NativeReplayArtifact) -> Value {
    json!({
        "artifact_schema": artifact.schema,
        "logic": artifact.logic,
        "scope_depth": artifact.scope_depth,
        "events": artifact.events.iter().map(event_json).collect::<Vec<_>>(),
        "declarations": artifact.declarations.iter().map(declaration_json).collect::<Vec<_>>(),
        "function_declarations": artifact
            .function_declarations
            .iter()
            .map(function_declaration_json)
            .collect::<Vec<_>>(),
        "symbol_identities": artifact
            .symbol_identities
            .iter()
            .map(symbol_identity_json)
            .collect::<Vec<_>>(),
        "assertions": artifact.assertions.iter().map(assertion_json).collect::<Vec<_>>(),
        "terms": artifact.terms.iter().map(term_node_json).collect::<Vec<_>>(),
    })
}

fn native_replay_options_binding_json(artifact: &NativeReplayArtifact) -> Value {
    json!({
        "artifact_schema": artifact.schema,
        "logic": artifact.logic,
        "selected_route": artifact.selected_route,
        "timeout_ms": artifact.timeout_ms.map(u128_json),
    })
}

fn native_replay_checked_result(checked: Option<&NativeReplayCheckedReplaySummary>) -> String {
    let Some(checked) = checked else {
        return "unchecked".to_string();
    };
    if !checked.result_matches {
        return "replay-mismatch".to_string();
    }
    match checked.replay_result.as_str() {
        "sat" if checked.replay_model_status == "validated" => "checked-sat".to_string(),
        "sat" => "demoted-sat".to_string(),
        "unsat" if checked.replay_proof_status == "checked" => "checked-unsat".to_string(),
        "unsat" => "demoted-unsat".to_string(),
        "unknown" => "unknown".to_string(),
        other => format!("unsupported-result:{other}"),
    }
}

fn native_replay_manifest_rejection_reasons(
    artifact: &NativeReplayArtifact,
    solver_identity: &NativeReplaySolverIdentity,
    checked: Option<&NativeReplayCheckedReplaySummary>,
    solver_identity_sha256: &str,
    problem_sha256: &str,
    options_sha256: &str,
    checked_summary_sha256: &str,
    replay_artifact_sha256: &str,
) -> Vec<String> {
    let mut reasons = Vec::new();
    if native_replay_evidence_requires_identity_table(artifact)
        && artifact.symbol_identities.is_empty()
    {
        reasons.push(
            "artifact lacks the authenticated symbol identity table required for evidence"
                .to_string(),
        );
    }
    let expected_route = native_replay_expected_selected_route(artifact);
    if artifact.selected_route.as_deref() != expected_route.as_deref() {
        reasons.push("artifact selected route does not match its native logic route".to_string());
    }
    let expected_identity =
        NativeReplaySolverIdentity::current_for_engine(native_replay_expected_engine(artifact));
    if solver_identity.engine != expected_identity.engine {
        reasons.push("solver identity engine does not match the current replay route".to_string());
    }
    if solver_identity.ay_revision != expected_identity.ay_revision {
        reasons
            .push("solver identity revision does not match the current replay build".to_string());
    }
    if solver_identity.ay_version != expected_identity.ay_version {
        reasons.push("solver identity version does not match the current replay build".to_string());
    }
    if solver_identity.ay_revision.is_empty() || solver_identity.ay_revision == "unknown" {
        reasons.push("solver identity ay revision is unknown".to_string());
    }
    match &solver_identity.solver_binary_sha256 {
        Some(hash) if well_formed_sha256(hash) => {}
        Some(_) => reasons.push("solver binary sha256 is malformed".to_string()),
        None => reasons.push("solver binary sha256 is missing".to_string()),
    }
    match artifact.admission_token.as_ref() {
        Some(token) => {
            if &token.solver_identity != solver_identity
                || token.solver_identity_sha256.as_str() != solver_identity_sha256
            {
                reasons.push(
                    "authoritative replay token solver identity binding does not match".to_string(),
                );
            }
            if token.problem_sha256.as_str() != problem_sha256 {
                reasons
                    .push("authoritative replay token problem binding does not match".to_string());
            }
            if token.options_sha256.as_str() != options_sha256 {
                reasons
                    .push("authoritative replay token options binding does not match".to_string());
            }
            if token.checked_summary_sha256.as_str() != checked_summary_sha256 {
                reasons.push(
                    "authoritative replay token checked-summary binding does not match".to_string(),
                );
            }
            if token.replay_artifact_sha256.as_str() != replay_artifact_sha256 {
                reasons.push(
                    "authoritative replay token full-artifact binding does not match".to_string(),
                );
            }
        }
        None => reasons.push("authoritative replay token is missing".to_string()),
    }
    if let Some(payload) = &artifact.panic_payload {
        reasons.push(format!("artifact captured panic payload: {payload}"));
    }
    if !artifact.unsupported_atoms.is_empty() {
        reasons.push("artifact contains unsupported atoms".to_string());
    }
    if !artifact.replay_gaps.is_empty() {
        reasons.push("artifact contains replay gaps".to_string());
    }

    let Some(checked) = checked else {
        reasons.push("checked replay summary is missing".to_string());
        return reasons;
    };
    if !checked.result_matches {
        reasons.push("checked replay result does not match original result".to_string());
    }
    if !checked.proof_status_matches {
        reasons
            .push("checked replay proof status does not match original proof status".to_string());
    }
    if !checked.model_status_matches {
        reasons
            .push("checked replay model status does not match original model status".to_string());
    }
    if let Some(error) = &checked.replay_executor_error {
        reasons.push(format!("checked replay executor error: {error}"));
    }
    if checked.original_unknown_reason.is_some() || checked.replay_unknown_reason.is_some() {
        reasons.push("checked replay carries unknown reason".to_string());
    }
    match checked.replay_result.as_str() {
        "sat" if checked.replay_model_status == "validated" => {}
        "sat" => reasons.push("sat result lacks validated model evidence".to_string()),
        "unsat" if checked.replay_proof_status == "checked" => {}
        "unsat" => reasons.push("unsat result lacks checked proof evidence".to_string()),
        "unknown" => reasons.push("checked result is unknown".to_string()),
        other => reasons.push(format!("unsupported checked result `{other}`")),
    }
    reasons
}

fn function_declarations_from_events(
    solver: &Solver,
    events: &[NativeReplayEvent],
    needed_functions: &HashSet<String>,
    replay_gaps: &mut Vec<String>,
) -> Vec<NativeReplayFunctionDeclaration> {
    let mut declarations = Vec::new();
    for event in events {
        if let NativeReplayEventKind::DeclareFun {
            name,
            domain,
            range,
        } = &event.kind
        {
            // Native applications carry the frontend-assigned core identity,
            // not the caller-visible spelling. In particular, a declaration
            // named `=` owns a private core while a builtin equality retains
            // the raw canonical `=` head. Matching both against the surface
            // spelling would retain an unused declaration and let replay put a
            // shadowing symbol into scope unnecessarily.
            let is_needed = solver.native_fun_signatures.get(name).map_or_else(
                || needed_functions.contains(name),
                |registration| needed_functions.contains(&registration.core_name),
            );
            if !is_needed {
                continue;
            }
            if declarations
                .iter()
                .any(|decl: &NativeReplayFunctionDeclaration| {
                    decl.name == *name && decl.domain == *domain && decl.range == *range
                })
            {
                continue;
            }
            let core_name = authenticated_native_function_core_name(solver, name, domain, range)
                .unwrap_or_else(|| {
                    replay_gaps.push(format!(
                        "native function `{name}` lacks exact live frontend identity metadata"
                    ));
                    format!(
                        "__ay_native_replay_unauthenticated_function_{}",
                        declarations.len()
                    )
                });
            declarations.push(NativeReplayFunctionDeclaration {
                name: name.clone(),
                core_name,
                domain: domain.clone(),
                range: range.clone(),
            });
        }
    }
    declarations
}

fn authenticated_native_function_core_name(
    solver: &Solver,
    surface_name: &str,
    domain: &[Sort],
    range: &Sort,
) -> Option<String> {
    let registration = solver.native_fun_signatures.get(surface_name)?;
    if registration.domain != domain || registration.range != *range {
        return None;
    }
    let handle = FuncDecl::with_frontend_identity(
        surface_name.to_string(),
        registration.core_name.clone(),
        domain.to_vec(),
        range.clone(),
        registration.identity.clone(),
    );
    if !solver.function_handle_is_current(&handle) {
        return None;
    }

    let engine_domain: Vec<_> = domain
        .iter()
        .map(|sort| solver.lower_live_sort(sort))
        .collect();
    let engine_range = solver.lower_live_sort(range);
    let context = solver.executor.context();
    let mut matches = context.symbols_iter().filter(|(surface, info)| {
        surface.as_str() == surface_name
            && context.symbol_identity_name(surface, info) == registration.core_name
            && info.arg_sorts == engine_domain
            && info.sort == engine_range
    });
    let (_, info) = matches.next()?;
    if matches.next().is_some()
        || context.effective_declaration_kind(info.declaration_id())
            != Some(info.declaration_kind())
        || native_replay_symbol_kind(info.declaration_kind()).is_none()
    {
        return None;
    }
    Some(registration.core_name.clone())
}

fn datatype_declarations_from_events(events: &[NativeReplayEvent]) -> Vec<DatatypeSort> {
    let mut declarations = Vec::new();
    for event in events {
        if let NativeReplayEventKind::DeclareDatatype { datatype } = &event.kind {
            if declarations
                .iter()
                .any(|existing: &DatatypeSort| existing == datatype)
            {
                continue;
            }
            declarations.push(datatype.clone());
        }
    }
    declarations
}

fn native_replay_symbol_kind(kind: ay_frontend::DeclarationKind) -> Option<NativeReplaySymbolKind> {
    match kind {
        ay_frontend::DeclarationKind::Uninterpreted => Some(NativeReplaySymbolKind::Uninterpreted),
        ay_frontend::DeclarationKind::Theory => Some(NativeReplaySymbolKind::Theory),
        ay_frontend::DeclarationKind::DatatypeConstructor => {
            Some(NativeReplaySymbolKind::DatatypeConstructor)
        }
        ay_frontend::DeclarationKind::DatatypeSelector => {
            Some(NativeReplaySymbolKind::DatatypeSelector)
        }
        ay_frontend::DeclarationKind::DatatypeTester => {
            Some(NativeReplaySymbolKind::DatatypeTester)
        }
        ay_frontend::DeclarationKind::Defined
        | ay_frontend::DeclarationKind::AdoptedDefinition
        | ay_frontend::DeclarationKind::SolverInternal => None,
    }
}

fn replay_symbol_identity(
    surface_name: &str,
    core_name: &str,
    api_domain: &[Sort],
    api_range: &Sort,
    info: &ay_frontend::SymbolInfo,
    datatype: Option<(&str, &str)>,
) -> Option<NativeReplaySymbolIdentity> {
    Some(NativeReplaySymbolIdentity {
        surface_name: surface_name.to_string(),
        core_name: core_name.to_string(),
        api_domain: api_domain.to_vec(),
        api_range: api_range.clone(),
        public_domain: info.public_arg_sorts.clone(),
        public_range: info.public_sort.clone(),
        engine_domain: info.arg_sorts.clone(),
        engine_range: info.sort.clone(),
        kind: native_replay_symbol_kind(info.declaration_kind())?,
        datatype_surface: datatype.map(|(surface, _)| surface.to_string()),
        datatype_core: datatype.map(|(_, core)| core.to_string()),
    })
}

fn export_native_replay_symbol_identities(
    solver: &Solver,
    declarations: &[NativeReplayDeclaration],
    function_declarations: &[NativeReplayFunctionDeclaration],
    datatypes: &[DatatypeSort],
    replay_gaps: &mut Vec<String>,
) -> Vec<NativeReplaySymbolIdentity> {
    let context = solver.executor.context();
    let mut identities = Vec::new();

    for declaration in declarations {
        let authenticated_core =
            authenticated_native_constant_core_name(solver, &declaration.name, declaration.term);
        let identity = authenticated_core
            .as_deref()
            .filter(|core_name| *core_name == declaration.core_name)
            .and_then(|core_name| {
                let mut matches = context.symbols_iter().filter(|(surface, info)| {
                    surface.as_str() == declaration.name.as_str()
                        && context.symbol_identity_name(surface, info) == core_name
                        && info.term == Some(declaration.term)
                        && info.declaration_kind() == ay_frontend::DeclarationKind::Uninterpreted
                });
                let (_, info) = matches.next()?;
                if matches.next().is_none() {
                    replay_symbol_identity(
                        &declaration.name,
                        core_name,
                        &[],
                        &declaration.sort,
                        info,
                        None,
                    )
                } else {
                    None
                }
            });
        if let Some(identity) = identity {
            identities.push(identity);
        } else {
            replay_gaps.push(format!(
                "native constant `{}` could not populate the authenticated identity table",
                declaration.name
            ));
        }
    }

    for declaration in function_declarations {
        let identity = authenticated_native_function_core_name(
            solver,
            &declaration.name,
            &declaration.domain,
            &declaration.range,
        )
        .filter(|core_name| core_name == &declaration.core_name)
        .and_then(|core_name| {
            context
                .symbols_iter()
                .find(|(surface, info)| {
                    surface.as_str() == declaration.name.as_str()
                        && context.symbol_identity_name(surface, info) == core_name
                })
                .and_then(|(_, info)| {
                    replay_symbol_identity(
                        &declaration.name,
                        &core_name,
                        &declaration.domain,
                        &declaration.range,
                        info,
                        None,
                    )
                })
        });
        if let Some(identity) = identity {
            identities.push(identity);
        } else {
            replay_gaps.push(format!(
                "native function `{}` could not populate the authenticated identity table",
                declaration.name
            ));
        }
    }

    for datatype in datatypes {
        let datatype_api_sort = Sort::Datatype(datatype.clone());
        let carrier_sort = solver.lower_live_sort(&Sort::Datatype(datatype.clone()));
        let Sort::Uninterpreted(carrier_core) = &carrier_sort else {
            replay_gaps.push(format!(
                "datatype `{}` lacks one exact engine carrier",
                datatype.name
            ));
            continue;
        };
        if !context.is_live_datatype_carrier(carrier_core) {
            replay_gaps.push(format!(
                "datatype `{}` engine carrier `{carrier_core}` is not live",
                datatype.name
            ));
            continue;
        }

        for constructor in &datatype.constructors {
            let constructor_domain: Vec<_> = constructor
                .fields
                .iter()
                .map(|field| solver.lower_live_sort(&field.sort))
                .collect();
            let Some(constructor_info) = context.symbol_info_with_signature(
                &constructor.name,
                &constructor_domain,
                &carrier_sort,
            ) else {
                replay_gaps.push(format!(
                    "datatype constructor `{}::{}` lacks an exact live signature",
                    datatype.name, constructor.name
                ));
                continue;
            };
            let constructor_core = context
                .symbol_identity_name(&constructor.name, constructor_info)
                .to_string();
            let constructor_is_exact = constructor_info.declaration_kind()
                == ay_frontend::DeclarationKind::DatatypeConstructor
                && context
                    .is_constructor(&constructor_core)
                    .is_some_and(|(carrier, _)| carrier.as_str() == carrier_core.as_str())
                && context
                    .exact_datatype_member_info(&constructor_core)
                    .is_some_and(|exact| {
                        exact.declaration_id() == constructor_info.declaration_id()
                    });
            if !constructor_is_exact {
                replay_gaps.push(format!(
                    "datatype constructor `{}::{}` lacks exact member provenance",
                    datatype.name, constructor.name
                ));
                continue;
            }
            if let Some(identity) = replay_symbol_identity(
                &constructor.name,
                &constructor_core,
                &constructor
                    .fields
                    .iter()
                    .map(|field| field.sort.clone())
                    .collect::<Vec<_>>(),
                &datatype_api_sort,
                constructor_info,
                Some((&datatype.name, carrier_core)),
            ) {
                identities.push(identity);
            }

            let Some(selector_cores) = context.constructor_selectors(&constructor_core) else {
                replay_gaps.push(format!(
                    "datatype constructor `{}::{}` lacks selector identity metadata",
                    datatype.name, constructor.name
                ));
                continue;
            };
            if selector_cores.len() != constructor.fields.len() {
                replay_gaps.push(format!(
                    "datatype constructor `{}::{}` selector identity count disagrees with its declaration",
                    datatype.name, constructor.name
                ));
                continue;
            }
            for (field, selector_core) in constructor.fields.iter().zip(selector_cores) {
                let Some(selector_info) = context.exact_datatype_member_info(selector_core) else {
                    replay_gaps.push(format!(
                        "datatype selector `{}::{}` lacks exact member metadata",
                        datatype.name, field.name
                    ));
                    continue;
                };
                if selector_info.declaration_kind()
                    != ay_frontend::DeclarationKind::DatatypeSelector
                    || context
                        .dt_surface_name(selector_core)
                        .unwrap_or(selector_core)
                        != field.name
                    || selector_info.arg_sorts.as_slice() != std::slice::from_ref(&carrier_sort)
                    || selector_info.sort != solver.lower_live_sort(&field.sort)
                {
                    replay_gaps.push(format!(
                        "datatype selector `{}::{}` has inconsistent live provenance",
                        datatype.name, field.name
                    ));
                    continue;
                }
                if let Some(identity) = replay_symbol_identity(
                    &field.name,
                    selector_core,
                    std::slice::from_ref(&datatype_api_sort),
                    &field.sort,
                    selector_info,
                    Some((&datatype.name, carrier_core)),
                ) {
                    identities.push(identity);
                }
            }

            let tester_surface = format!("is-{}", constructor.name);
            let tester_core = format!("is-{constructor_core}");
            let Some(tester_info) = context.exact_datatype_member_info(&tester_core) else {
                replay_gaps.push(format!(
                    "datatype tester `{tester_surface}` lacks exact member metadata"
                ));
                continue;
            };
            if tester_info.declaration_kind() != ay_frontend::DeclarationKind::DatatypeTester
                || context
                    .dt_surface_name(&tester_core)
                    .unwrap_or(&tester_core)
                    != tester_surface
                || tester_info.arg_sorts.as_slice() != std::slice::from_ref(&carrier_sort)
                || tester_info.sort != Sort::Bool
            {
                replay_gaps.push(format!(
                    "datatype tester `{tester_surface}` has inconsistent live provenance"
                ));
                continue;
            }
            if let Some(identity) = replay_symbol_identity(
                &tester_surface,
                &tester_core,
                std::slice::from_ref(&datatype_api_sort),
                &Sort::Bool,
                tester_info,
                Some((&datatype.name, carrier_core)),
            ) {
                identities.push(identity);
            }
        }
    }

    identities.sort_by(|left, right| left.core_name.cmp(&right.core_name));
    identities
}

struct ActiveAssertionMetadata {
    name: Option<String>,
    scope_depth: usize,
}

fn active_assertion_metadata_from_events(
    events: &[NativeReplayEvent],
) -> HashMap<TermId, VecDeque<ActiveAssertionMetadata>> {
    let mut scopes = Vec::new();
    let mut active = Vec::new();
    for event in events {
        match &event.kind {
            NativeReplayEventKind::Assert { term, name } => {
                active.push((
                    *term,
                    ActiveAssertionMetadata {
                        name: name.clone(),
                        scope_depth: event.scope_depth as usize,
                    },
                ));
            }
            NativeReplayEventKind::Push => scopes.push(active.len()),
            NativeReplayEventKind::Pop => {
                if let Some(start) = scopes.pop() {
                    active.truncate(start);
                }
            }
            NativeReplayEventKind::Reset | NativeReplayEventKind::ResetAssertions => {
                scopes.clear();
                active.clear();
            }
            NativeReplayEventKind::SetLogic { .. }
            | NativeReplayEventKind::DeclareConst { .. }
            | NativeReplayEventKind::DeclareFun { .. }
            | NativeReplayEventKind::DeclareDatatype { .. }
            | NativeReplayEventKind::CheckSat
            | NativeReplayEventKind::CheckSatAssuming { .. } => {}
        }
    }

    let mut by_term: HashMap<TermId, VecDeque<ActiveAssertionMetadata>> = HashMap::default();
    for (term, metadata) in active {
        by_term.entry(term).or_default().push_back(metadata);
    }
    by_term
}

fn assertion_name_for(
    events: &[NativeReplayEvent],
    term: TermId,
    occurrence: usize,
) -> Option<String> {
    events
        .iter()
        .filter_map(|event| match &event.kind {
            NativeReplayEventKind::Assert {
                term: event_term,
                name,
            } if *event_term == term => name.clone(),
            _ => None,
        })
        .nth(occurrence)
}

fn final_check_sat_assumptions(events: &[NativeReplayEvent]) -> Option<&[TermId]> {
    for event in events.iter().rev() {
        match &event.kind {
            NativeReplayEventKind::CheckSatAssuming { assumptions } => {
                return Some(assumptions.as_slice());
            }
            NativeReplayEventKind::CheckSat => return None,
            _ => {}
        }
    }
    None
}

/// Deterministic child-before-parent slice of the term DAG needed to replay the
/// active assertions and the final check-sat assumptions. Discarded native term
/// construction history is intentionally absent: besides shrinking artifacts,
/// this prevents an unreachable future/unsupported node from blocking replay of
/// an otherwise supported active problem.
fn replay_term_dependency_closure(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut ordered = Vec::new();

    for &root in roots {
        if visited.contains(&root) {
            continue;
        }
        let mut stack = vec![(root, false)];
        while let Some((term, expanded)) = stack.pop() {
            if expanded {
                ordered.push(term);
                continue;
            }
            if !visited.insert(term) {
                continue;
            }
            stack.push((term, true));
            let dependencies = replay_term_dependencies(terms.get(term));
            for dependency in dependencies.into_iter().rev() {
                if !visited.contains(&dependency) {
                    stack.push((dependency, false));
                }
            }
        }
    }
    ordered
}

fn replay_term_dependencies(data: &TermData) -> Vec<TermId> {
    match data {
        TermData::Const(_) | TermData::Var(_, _) => Vec::new(),
        TermData::App(_, args) => args.clone(),
        TermData::Let(bindings, body) => bindings
            .iter()
            .map(|(_, term)| *term)
            .chain(std::iter::once(*body))
            .collect(),
        TermData::Not(inner) => vec![*inner],
        TermData::Ite(cond, then_term, else_term) => vec![*cond, *then_term, *else_term],
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            std::iter::once(*body)
                .chain(triggers.iter().flatten().copied())
                .collect()
        }
        _ => Vec::new(),
    }
}

fn solve_summary_from_details(
    details: &crate::api::types::SolveDetails,
    wall_time_budget_ms: Option<u128>,
) -> NativeReplaySolveSummary {
    let statistics = &details.statistics;
    let unknown_phase = details
        .unknown_diagnostic
        .as_ref()
        .and_then(|diagnostic| diagnostic.phase.clone())
        .or_else(|| {
            details
                .resource_usage
                .limit_hit
                .map(limit_phase)
                .or_else(|| {
                    details
                        .unknown_reason
                        .map(|reason| reason_phase(&reason).to_string())
                })
        });
    NativeReplaySolveSummary {
        result: details.result.result().to_string(),
        unknown_reason: details.unknown_reason.map(|reason| reason.to_string()),
        unknown_phase,
        unknown_progress: details
            .unknown_reason
            .map(|reason| NativeReplayUnknownProgress {
                reason: reason.to_string(),
                responsible_phase: details
                    .unknown_diagnostic
                    .as_ref()
                    .and_then(|diagnostic| diagnostic.phase.clone())
                    .or_else(|| {
                        details
                            .resource_usage
                            .limit_hit
                            .map(limit_phase)
                            .or_else(|| Some(reason_phase(&reason).to_string()))
                    }),
                wall_time_budget_ms,
                wall_time_elapsed_ms: details.resource_usage.wall_time.as_millis(),
            }),
        executor_error: details.executor_error.clone(),
        elapsed_ms: details.resource_usage.wall_time.as_millis(),
        verification_level: details.verification_level.to_string(),
        proof: NativeReplayProofSummary {
            available: details.verification.unsat_proof_available,
            clause_count: statistics.proof_clause_count,
            complete: statistics.proof_complete,
            strictly_verified: details.verification.unsat_proof_strictly_verified,
            checker_failures: details.verification.unsat_proof_checker_failures,
            trust_fallbacks: statistics.get_int("proof_trust").unwrap_or(0),
        },
        model: NativeReplayModelSummary {
            validated: details.verification.sat_model_validated,
            independent_checks: details.verification.sat_independent_checks,
            delegated_checks: details.verification.sat_delegated_checks,
            incomplete_checks: details.verification.sat_incomplete_checks,
            validation_failures: statistics.model_validation_failures,
            validation_skips: statistics.model_validation_skips,
        },
        statistics: NativeReplayStatistics {
            conflicts: statistics.conflicts,
            decisions: statistics.decisions,
            propagations: statistics.propagations,
            restarts: statistics.restarts,
            learned_clauses: statistics.learned_clauses,
            theory_conflicts: statistics.theory_conflicts,
            theory_propagations: statistics.theory_propagations,
            theory_unknown_count: statistics.theory_unknown_count,
            partial_clause_count: statistics.partial_clause_count,
            ematching_rounds_completed: statistics.ematching_rounds_completed,
            ematching_instances_created: statistics.ematching_instances_created,
            refinement_count: statistics.refinement_count,
        },
        resources: NativeReplayResourceUsage {
            rss_bytes: details.resource_usage.rss_bytes,
            term_bytes: details.resource_usage.term_bytes,
            term_count: details.resource_usage.term_count,
            learned_clause_count: details.resource_usage.learned_clause_count,
            limit_hit: details
                .resource_usage
                .limit_hit
                .map(|limit| format!("{limit:?}")),
        },
    }
}

fn checked_replay_summary_from_details(
    original: Option<&NativeReplaySolveSummary>,
    replay: &crate::api::types::SolveDetails,
) -> NativeReplayCheckedReplaySummary {
    let replay_summary = solve_summary_from_details(replay, None);
    let original_result = original.map(|solve| solve.result.clone());
    let original_proof_status =
        original.map(|solve| proof_evidence_status(&solve.result, &solve.proof).to_string());
    let replay_proof_status =
        proof_evidence_status(&replay_summary.result, &replay_summary.proof).to_string();
    let original_model_status =
        original.map(|solve| model_evidence_status(&solve.result, &solve.model).to_string());
    let replay_model_status =
        model_evidence_status(&replay_summary.result, &replay_summary.model).to_string();

    NativeReplayCheckedReplaySummary {
        result_matches: original_result
            .as_ref()
            .is_some_and(|result| result == &replay_summary.result),
        proof_status_matches: original_proof_status
            .as_ref()
            .is_some_and(|status| status == &replay_proof_status),
        model_status_matches: original_model_status
            .as_ref()
            .is_some_and(|status| status == &replay_model_status),
        original_result,
        replay_result: replay_summary.result,
        original_unknown_reason: original.and_then(|solve| solve.unknown_reason.clone()),
        replay_unknown_reason: replay_summary.unknown_reason,
        original_proof_status,
        replay_proof_status,
        original_model_status,
        replay_model_status,
        replay_executor_error: replay_summary.executor_error,
    }
}

fn proof_evidence_status(result: &str, proof: &NativeReplayProofSummary) -> &'static str {
    if result != "unsat" {
        return "not-applicable";
    }
    if proof.checker_failures > 0 {
        return "checker-failed";
    }
    if proof.available && proof.complete && proof.strictly_verified {
        return "checked";
    }
    if proof.available && proof.complete {
        return "available-unchecked";
    }
    if proof.available {
        return "available-incomplete";
    }
    "missing"
}

fn model_evidence_status(result: &str, model: &NativeReplayModelSummary) -> &'static str {
    if result != "sat" {
        return "not-applicable";
    }
    if model.validation_failures > 0 {
        return "failed";
    }
    if model.validated {
        return "validated";
    }
    if model.incomplete_checks > 0 || model.validation_skips > 0 {
        return "incomplete";
    }
    "missing"
}

fn limit_phase(limit: LimitKind) -> String {
    match limit {
        LimitKind::Timeout | LimitKind::Interrupted => "search-control",
        LimitKind::MemoryLimit
        | LimitKind::TermMemoryLimit
        | LimitKind::LearnedClauseLimit
        | LimitKind::ClauseDbBytesLimit => "resource-control",
    }
    .to_string()
}

/// Authenticate the two identity tables before replaying any node.
///
/// Artifact term IDs are graph identities, while declaration names are solver
/// identities. Allowing either table to be last-wins (or allowing two term IDs
/// to declare one name) can collapse distinct variables and change the replayed
/// formula. Export produces one canonical entry in each table, so every
/// ambiguity or metadata mismatch is malformed input and fails closed.
fn validate_native_replay_identity_tables(
    artifact: &NativeReplayArtifact,
) -> Result<(), SolverError> {
    let mut node_ids = HashSet::default();
    let mut nodes = HashMap::default();
    for node in &artifact.terms {
        if !node_ids.insert(node.id) {
            return Err(native_replay_artifact_error(format!(
                "duplicate term node id {}",
                node.id.0
            )));
        }
        if node.is_datatype_constructor && !matches!(node.data, TermData::Var(..)) {
            return Err(native_replay_artifact_error(format!(
                "term {} claims datatype-constructor identity but is not a variable node",
                node.id.0
            )));
        }
        nodes.insert(node.id, node);
    }

    validate_native_replay_symbol_identity_table(artifact, &nodes)?;

    let declaration_names = identity_validation::validate_constant_identities(artifact, &nodes)?;

    let mut function_names = HashSet::default();
    for declaration in &artifact.function_declarations {
        if !function_names.insert(declaration.name.as_str()) {
            return Err(native_replay_artifact_error(format!(
                "duplicate native function declaration name `{}`",
                declaration.name
            )));
        }
        if declaration_names.contains(declaration.name.as_str()) {
            return Err(native_replay_artifact_error(format!(
                "symbol `{}` is declared as both a constant and a function",
                declaration.name
            )));
        }
    }
    Ok(())
}

fn serialized_symbol_uses_private_allocator_identity(name: &str) -> bool {
    is_allocator_private_declaration_identity(name)
        || name
            .strip_prefix("is-")
            .is_some_and(is_allocator_private_declaration_identity)
}

fn is_allocator_private_datatype_carrier_identity(name: &str) -> bool {
    name.strip_prefix("__ay_datatype_sort_")
        .is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn embedded_replay_function_identity(name: &str) -> Option<&str> {
    name.strip_prefix("as-array[")
        .and_then(|name| name.strip_suffix(']'))
        .or_else(|| {
            name.strip_prefix("map[")
                .and_then(|name| name.strip_suffix(']'))
        })
}

fn sort_uses_private_datatype_carrier(sort: &Sort) -> bool {
    match sort {
        Sort::Uninterpreted(name) => is_allocator_private_datatype_carrier_identity(name),
        Sort::Array(array) => {
            sort_uses_private_datatype_carrier(&array.index_sort)
                || sort_uses_private_datatype_carrier(&array.element_sort)
        }
        Sort::Datatype(datatype) => datatype.constructors.iter().any(|constructor| {
            constructor
                .fields
                .iter()
                .any(|field| sort_uses_private_datatype_carrier(&field.sort))
        }),
        Sort::Seq(element) => sort_uses_private_datatype_carrier(element),
        _ => false,
    }
}

fn legacy_artifact_uses_private_declaration_identity(artifact: &NativeReplayArtifact) -> bool {
    artifact.terms.iter().any(|node| {
        sort_uses_private_datatype_carrier(&node.sort)
            || match &node.data {
                TermData::Var(name, _) => {
                    node.is_datatype_constructor
                        && serialized_symbol_uses_private_allocator_identity(name)
                }
                TermData::App(Symbol::Named(name), _) => {
                    serialized_symbol_uses_private_allocator_identity(name)
                        || embedded_replay_function_identity(name)
                            .is_some_and(serialized_symbol_uses_private_allocator_identity)
                }
                TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => vars
                    .iter()
                    .any(|(_, sort)| sort_uses_private_datatype_carrier(sort)),
                _ => false,
            }
    })
}

fn validate_native_replay_symbol_identity_table(
    artifact: &NativeReplayArtifact,
    nodes: &HashMap<TermId, &NativeReplayTermNode>,
) -> Result<(), SolverError> {
    let datatype_declarations = datatype_declarations_from_events(&artifact.events);
    let datatype_member_count: usize = datatype_declarations
        .iter()
        .map(|datatype| {
            datatype
                .constructors
                .iter()
                .map(|constructor| 2 + constructor.fields.len())
                .sum::<usize>()
        })
        .sum();
    let expected_count =
        artifact.declarations.len() + artifact.function_declarations.len() + datatype_member_count;

    // v1 artifacts before identity-table capture are compatible only when all
    // declaration identities remained public. A private allocator spelling is
    // not stable across replay declaration order and must fail closed.
    if artifact.symbol_identities.is_empty() {
        if artifact
            .terms
            .iter()
            .any(|node| node.is_datatype_constructor)
        {
            return Err(native_replay_artifact_error(
                "legacy artifact claims nullary datatype-constructor provenance without an authenticated identity row",
            ));
        }
        if artifact.declarations.iter().any(|declaration| {
            declaration.core_name != declaration.name
                || ay_frontend::is_canonical_theory_operator_identity(&declaration.core_name)
        }) || artifact.function_declarations.iter().any(|declaration| {
            declaration.core_name != declaration.name
                || ay_frontend::is_canonical_theory_operator_identity(&declaration.core_name)
        }) || legacy_artifact_uses_private_declaration_identity(artifact)
        {
            return Err(native_replay_artifact_error(
                "legacy artifact uses an unauthenticated private or canonical-theory declaration identity",
            ));
        }
        return Ok(());
    }

    if artifact.symbol_identities.len() != expected_count {
        return Err(native_replay_artifact_error(format!(
            "native replay identity table has {} rows, expected {expected_count}",
            artifact.symbol_identities.len()
        )));
    }

    let mut core_names = HashSet::default();
    let mut stable_keys = HashSet::default();
    let mut datatype_carriers: HashMap<&str, &str> = HashMap::default();
    let mut carrier_surfaces: HashMap<&str, &str> = HashMap::default();
    for identity in &artifact.symbol_identities {
        if !core_names.insert(identity.core_name.as_str()) {
            return Err(native_replay_artifact_error(format!(
                "duplicate replay symbol core identity `{}`",
                identity.core_name
            )));
        }
        if !stable_keys.insert((
            identity.surface_name.as_str(),
            identity.api_domain.as_slice(),
            &identity.api_range,
            identity.public_domain.as_slice(),
            &identity.public_range,
            identity.kind,
        )) {
            return Err(native_replay_artifact_error(format!(
                "duplicate stable replay symbol identity for `{}`",
                identity.surface_name
            )));
        }
        let canonical_theory_core =
            ay_frontend::is_canonical_theory_operator_identity(&identity.core_name);
        if identity.kind == NativeReplaySymbolKind::Theory {
            if !canonical_theory_core || identity.core_name != identity.surface_name {
                return Err(native_replay_artifact_error(format!(
                    "theory symbol `{}` does not own one raw canonical theory identity",
                    identity.surface_name
                )));
            }
        } else if canonical_theory_core {
            return Err(native_replay_artifact_error(format!(
                "non-theory symbol `{}` claims canonical theory identity `{}`",
                identity.surface_name, identity.core_name
            )));
        }
        let authorized_private_core =
            is_allocator_private_declaration_identity(&identity.core_name)
                || (identity.kind == NativeReplaySymbolKind::DatatypeTester
                    && identity
                        .core_name
                        .strip_prefix("is-")
                        .is_some_and(is_allocator_private_declaration_identity));
        if identity.core_name != identity.surface_name && !authorized_private_core {
            return Err(native_replay_artifact_error(format!(
                "symbol `{}` claims unauthorized private core identity `{}`",
                identity.surface_name, identity.core_name
            )));
        }

        let is_datatype_member = matches!(
            identity.kind,
            NativeReplaySymbolKind::DatatypeConstructor
                | NativeReplaySymbolKind::DatatypeSelector
                | NativeReplaySymbolKind::DatatypeTester
        );
        match (
            is_datatype_member,
            identity.datatype_surface.as_deref(),
            identity.datatype_core.as_deref(),
        ) {
            (true, Some(surface), Some(core)) => {
                if core != surface && !is_allocator_private_datatype_carrier_identity(core) {
                    return Err(native_replay_artifact_error(format!(
                        "datatype `{surface}` claims unauthorized private carrier `{core}`"
                    )));
                }
                let carrier_sort = Sort::Uninterpreted(core.to_string());
                let owns_member = match identity.kind {
                    NativeReplaySymbolKind::DatatypeConstructor => {
                        identity.engine_range == carrier_sort
                    }
                    NativeReplaySymbolKind::DatatypeSelector
                    | NativeReplaySymbolKind::DatatypeTester => {
                        identity.engine_domain.as_slice() == std::slice::from_ref(&carrier_sort)
                    }
                    _ => false,
                };
                if !owns_member {
                    return Err(native_replay_artifact_error(format!(
                        "datatype member `{}` does not use its claimed carrier `{core}`",
                        identity.surface_name
                    )));
                }
                if let Some(previous) = datatype_carriers.insert(surface, core) {
                    if previous != core {
                        return Err(native_replay_artifact_error(format!(
                            "datatype `{surface}` claims multiple exported carrier identities"
                        )));
                    }
                }
                if let Some(previous) = carrier_surfaces.insert(core, surface) {
                    if previous != surface {
                        return Err(native_replay_artifact_error(format!(
                            "datatype carrier `{core}` is claimed by multiple public datatypes"
                        )));
                    }
                }
            }
            (false, None, None) => {}
            _ => {
                return Err(native_replay_artifact_error(format!(
                    "symbol `{}` has inconsistent datatype provenance",
                    identity.surface_name
                )));
            }
        }
    }

    for declaration in &artifact.declarations {
        let node = nodes.get(&declaration.term).ok_or_else(|| {
            native_replay_artifact_error(format!(
                "declaration `{}` references missing term {}",
                declaration.name, declaration.term.0
            ))
        })?;
        let matching: Vec<_> = artifact
            .symbol_identities
            .iter()
            .filter(|identity| {
                identity.surface_name.eq(&declaration.name)
                    && identity.core_name == declaration.core_name
                    && identity.kind == NativeReplaySymbolKind::Uninterpreted
                    && identity.api_domain.is_empty()
                    && identity.api_range == declaration.sort
                    && identity.public_domain.is_empty()
                    && identity.engine_domain.is_empty()
                    && identity.engine_range == node.sort
            })
            .collect();
        if matching.len() != 1 {
            return Err(native_replay_artifact_error(format!(
                "constant declaration `{}` lacks one exact identity-table row",
                declaration.name
            )));
        }
    }

    for declaration in &artifact.function_declarations {
        let matching = artifact.symbol_identities.iter().filter(|identity| {
            identity.surface_name.eq(&declaration.name)
                && identity.core_name == declaration.core_name
                && identity.api_domain == declaration.domain
                && identity.api_range == declaration.range
                && matches!(
                    identity.kind,
                    NativeReplaySymbolKind::Uninterpreted | NativeReplaySymbolKind::Theory
                )
                && identity.datatype_surface.is_none()
        });
        if matching.count() != 1 {
            return Err(native_replay_artifact_error(format!(
                "function declaration `{}` lacks one exact identity-table row",
                declaration.name
            )));
        }
    }

    let mut expected_datatype_members: HashMap<(String, String, NativeReplaySymbolKind), usize> =
        HashMap::default();
    for datatype in &datatype_declarations {
        for constructor in &datatype.constructors {
            *expected_datatype_members
                .entry((
                    datatype.name.clone(),
                    constructor.name.clone(),
                    NativeReplaySymbolKind::DatatypeConstructor,
                ))
                .or_default() += 1;
            *expected_datatype_members
                .entry((
                    datatype.name.clone(),
                    format!("is-{}", constructor.name),
                    NativeReplaySymbolKind::DatatypeTester,
                ))
                .or_default() += 1;
            for field in &constructor.fields {
                *expected_datatype_members
                    .entry((
                        datatype.name.clone(),
                        field.name.clone(),
                        NativeReplaySymbolKind::DatatypeSelector,
                    ))
                    .or_default() += 1;
            }
        }
    }
    for identity in artifact.symbol_identities.iter().filter(|identity| {
        matches!(
            identity.kind,
            NativeReplaySymbolKind::DatatypeConstructor
                | NativeReplaySymbolKind::DatatypeSelector
                | NativeReplaySymbolKind::DatatypeTester
        )
    }) {
        let datatype_surface = identity.datatype_surface.as_deref().unwrap_or_default();
        let datatype = datatype_declarations
            .iter()
            .find(|datatype| datatype.name == datatype_surface)
            .ok_or_else(|| {
                native_replay_artifact_error(format!(
                    "identity row `{}` names missing datatype `{datatype_surface}`",
                    identity.surface_name
                ))
            })?;
        let datatype_sort = Sort::Datatype(datatype.clone());
        let api_signature_matches = match identity.kind {
            NativeReplaySymbolKind::DatatypeConstructor => datatype
                .constructors
                .iter()
                .find(|constructor| constructor.name == identity.surface_name)
                .is_some_and(|constructor| {
                    identity.api_domain
                        == constructor
                            .fields
                            .iter()
                            .map(|field| field.sort.clone())
                            .collect::<Vec<_>>()
                        && identity.api_range == datatype_sort
                }),
            NativeReplaySymbolKind::DatatypeSelector => {
                let mut fields = datatype
                    .constructors
                    .iter()
                    .flat_map(|constructor| &constructor.fields)
                    .filter(|field| field.name == identity.surface_name);
                fields.next().is_some_and(|field| {
                    fields.next().is_none()
                        && identity.api_domain.as_slice() == std::slice::from_ref(&datatype_sort)
                        && identity.api_range == field.sort
                })
            }
            NativeReplaySymbolKind::DatatypeTester => identity
                .surface_name
                .strip_prefix("is-")
                .and_then(|constructor_name| {
                    datatype
                        .constructors
                        .iter()
                        .find(|constructor| constructor.name == constructor_name)
                })
                .is_some_and(|_| {
                    identity.api_domain.as_slice() == std::slice::from_ref(&datatype_sort)
                        && identity.api_range == Sort::Bool
                }),
            _ => false,
        };
        if !api_signature_matches {
            return Err(native_replay_artifact_error(format!(
                "datatype member `{}` has an API signature inconsistent with `{datatype_surface}`",
                identity.surface_name
            )));
        }
        let key = (
            datatype_surface.to_string(),
            identity.surface_name.clone(),
            identity.kind,
        );
        let Some(remaining) = expected_datatype_members.get_mut(&key) else {
            return Err(native_replay_artifact_error(format!(
                "identity row `{}` is not a member of its claimed datatype",
                identity.surface_name
            )));
        };
        let Some(next) = remaining.checked_sub(1) else {
            return Err(native_replay_artifact_error(format!(
                "identity table repeats datatype member `{}`",
                identity.surface_name
            )));
        };
        *remaining = next;
    }
    if expected_datatype_members
        .values()
        .any(|&remaining| remaining != 0)
    {
        return Err(native_replay_artifact_error(
            "native replay identity table omits a declared datatype member",
        ));
    }

    // A positive nullary-constructor marker changes a Var from a free value to
    // a datatype inhabitant. Authenticate that claim against one exact row;
    // ordinary constants with the same spelling must never be accepted here.
    for node in artifact
        .terms
        .iter()
        .filter(|node| node.is_datatype_constructor)
    {
        let TermData::Var(core_name, _) = &node.data else {
            // The outer identity-table validator already reports this shape.
            continue;
        };
        let mut matching = artifact.symbol_identities.iter().filter(|identity| {
            identity.core_name == core_name.as_str()
                && identity.kind == NativeReplaySymbolKind::DatatypeConstructor
                && identity.api_domain.is_empty()
                && identity.engine_domain.is_empty()
                && identity.engine_range == node.sort
                && identity.datatype_surface.is_some()
                && identity.datatype_core.is_some()
        });
        if matching.next().is_none() || matching.next().is_some() {
            return Err(native_replay_artifact_error(format!(
                "term {} lacks one exact nullary datatype-constructor identity row for `{core_name}`",
                node.id.0
            )));
        }
    }
    Ok(())
}

#[derive(Default)]
struct NativeReplayIdentityRemap {
    cores: HashMap<String, String>,
    reverse_cores: HashMap<String, String>,
    nullary_constructors: HashMap<String, String>,
    carriers: HashMap<String, String>,
    reverse_carriers: HashMap<String, String>,
}

impl NativeReplayIdentityRemap {
    fn insert_core(&mut self, old: &str, new: &str) -> Result<(), SolverError> {
        if let Some(existing) = self.cores.insert(old.to_string(), new.to_string()) {
            if existing != new {
                return Err(native_replay_artifact_error(format!(
                    "exported core identity `{old}` maps to both `{existing}` and `{new}`"
                )));
            }
        }
        if let Some(existing) = self.reverse_cores.insert(new.to_string(), old.to_string()) {
            if existing != old {
                return Err(native_replay_artifact_error(format!(
                    "rebuilt core identity `{new}` is claimed by both `{existing}` and `{old}`"
                )));
            }
        }
        Ok(())
    }

    fn insert_carrier(&mut self, old: &str, new: &str) -> Result<(), SolverError> {
        if let Some(existing) = self.carriers.insert(old.to_string(), new.to_string()) {
            if existing != new {
                return Err(native_replay_artifact_error(format!(
                    "exported datatype carrier `{old}` maps to both `{existing}` and `{new}`"
                )));
            }
        }
        if let Some(existing) = self
            .reverse_carriers
            .insert(new.to_string(), old.to_string())
        {
            if existing != old {
                return Err(native_replay_artifact_error(format!(
                    "rebuilt datatype carrier `{new}` is claimed by both `{existing}` and `{old}`"
                )));
            }
        }
        Ok(())
    }

    fn insert_nullary_constructor(&mut self, old: &str, new: &str) -> Result<(), SolverError> {
        if self.cores.get(old).map(String::as_str) != Some(new) {
            return Err(native_replay_artifact_error(format!(
                "nullary datatype constructor `{old}` lacks its exact authenticated core remap"
            )));
        }
        if let Some(existing) = self
            .nullary_constructors
            .insert(old.to_string(), new.to_string())
        {
            if existing != new {
                return Err(native_replay_artifact_error(format!(
                    "nullary datatype constructor `{old}` maps to both `{existing}` and `{new}`"
                )));
            }
        }
        Ok(())
    }

    fn remap_sort(&self, sort: &Sort) -> Result<Sort, SolverError> {
        match sort {
            Sort::Uninterpreted(name) => {
                if let Some(mapped) = self.carriers.get(name) {
                    Ok(Sort::Uninterpreted(mapped.clone()))
                } else if is_allocator_private_datatype_carrier_identity(name) {
                    Err(native_replay_artifact_error(format!(
                        "private datatype carrier `{name}` lacks an authenticated remap row"
                    )))
                } else {
                    Ok(sort.clone())
                }
            }
            Sort::Array(array) => Ok(Sort::array(
                self.remap_sort(&array.index_sort)?,
                self.remap_sort(&array.element_sort)?,
            )),
            Sort::Datatype(datatype) => Ok(Sort::Datatype(DatatypeSort {
                name: datatype.name.clone(),
                constructors: datatype
                    .constructors
                    .iter()
                    .map(|constructor| {
                        Ok(DatatypeConstructor {
                            name: constructor.name.clone(),
                            fields: constructor
                                .fields
                                .iter()
                                .map(|field| {
                                    Ok(DatatypeField {
                                        name: field.name.clone(),
                                        sort: self.remap_sort(&field.sort)?,
                                    })
                                })
                                .collect::<Result<Vec<_>, SolverError>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, SolverError>>()?,
            })),
            Sort::Seq(element) => Ok(Sort::seq(self.remap_sort(element)?)),
            _ => Ok(sort.clone()),
        }
    }

    fn remap_public_sort(
        &self,
        sort: &ay_frontend::PublicSort,
    ) -> Result<ay_frontend::PublicSort, SolverError> {
        match sort {
            ay_frontend::PublicSort::Core(sort) => {
                Ok(ay_frontend::PublicSort::Core(self.remap_sort(sort)?))
            }
            ay_frontend::PublicSort::Array(index, element) => Ok(ay_frontend::PublicSort::Array(
                Box::new(self.remap_public_sort(index)?),
                Box::new(self.remap_public_sort(element)?),
            )),
            ay_frontend::PublicSort::Seq(element) => Ok(ay_frontend::PublicSort::Seq(Box::new(
                self.remap_public_sort(element)?,
            ))),
            ay_frontend::PublicSort::FiniteSet(element) => Ok(ay_frontend::PublicSort::FiniteSet(
                Box::new(self.remap_public_sort(element)?),
            )),
            ay_frontend::PublicSort::AmbiguousSet(element) => Ok(
                ay_frontend::PublicSort::AmbiguousSet(Box::new(self.remap_public_sort(element)?)),
            ),
            ay_frontend::PublicSort::Unknown => Ok(ay_frontend::PublicSort::Unknown),
            _ => Ok(sort.clone()),
        }
    }

    fn remap_application_name(&self, name: &str) -> Result<String, SolverError> {
        if let Some(mapped) = self.cores.get(name) {
            return Ok(mapped.clone());
        }
        if let Some(function) = name
            .strip_prefix("as-array[")
            .and_then(|name| name.strip_suffix(']'))
        {
            if let Some(mapped) = self.cores.get(function) {
                return Ok(format!("as-array[{mapped}]"));
            }
            if serialized_symbol_uses_private_allocator_identity(function) {
                return Err(native_replay_artifact_error(format!(
                    "embedded as-array identity `{function}` lacks an authenticated remap row"
                )));
            }
        }
        if let Some(function) = name
            .strip_prefix("map[")
            .and_then(|name| name.strip_suffix(']'))
        {
            if let Some(mapped) = self.cores.get(function) {
                return Ok(format!("map[{mapped}]"));
            }
            if serialized_symbol_uses_private_allocator_identity(function) {
                return Err(native_replay_artifact_error(format!(
                    "embedded array-map identity `{function}` lacks an authenticated remap row"
                )));
            }
        }
        if serialized_symbol_uses_private_allocator_identity(name) {
            return Err(native_replay_artifact_error(format!(
                "private application identity `{name}` lacks an authenticated remap row"
            )));
        }
        Ok(name.to_string())
    }

    fn remap_term_node(
        &self,
        node: &NativeReplayTermNode,
    ) -> Result<NativeReplayTermNode, SolverError> {
        let data = match &node.data {
            TermData::Var(name, id) if node.is_datatype_constructor => {
                let Some(mapped) = self.nullary_constructors.get(name).cloned() else {
                    return Err(native_replay_artifact_error(format!(
                        "nullary datatype constructor identity `{name}` lacks an exact authenticated remap row"
                    )));
                };
                TermData::Var(mapped, *id)
            }
            TermData::App(Symbol::Named(name), args) => TermData::App(
                Symbol::Named(self.remap_application_name(name)?),
                args.clone(),
            ),
            // Binder spellings are not declaration identities. Replay gives
            // every binder a fresh alpha identity after rebuilding its
            // children, then rewrites only the exact source Var nodes captured
            // by that lexical scope. Keeping the authored spelling here is
            // necessary for that source-graph capture analysis.
            TermData::Let(bindings, body) => TermData::Let(bindings.clone(), *body),
            TermData::Forall(vars, body, triggers) => {
                let vars = vars
                    .iter()
                    .map(|(name, sort)| Ok((name.clone(), self.remap_sort(sort)?)))
                    .collect::<Result<Vec<_>, SolverError>>()?;
                TermData::Forall(vars, *body, triggers.clone())
            }
            TermData::Exists(vars, body, triggers) => {
                let vars = vars
                    .iter()
                    .map(|(name, sort)| Ok((name.clone(), self.remap_sort(sort)?)))
                    .collect::<Result<Vec<_>, SolverError>>()?;
                TermData::Exists(vars, *body, triggers.clone())
            }
            data => data.clone(),
        };
        Ok(NativeReplayTermNode {
            id: node.id,
            sort: self.remap_sort(&node.sort)?,
            data,
            is_datatype_constructor: node.is_datatype_constructor,
        })
    }
}

fn frontend_symbol_kind(kind: NativeReplaySymbolKind) -> ay_frontend::DeclarationKind {
    match kind {
        NativeReplaySymbolKind::Uninterpreted => ay_frontend::DeclarationKind::Uninterpreted,
        NativeReplaySymbolKind::Theory => ay_frontend::DeclarationKind::Theory,
        NativeReplaySymbolKind::DatatypeConstructor => {
            ay_frontend::DeclarationKind::DatatypeConstructor
        }
        NativeReplaySymbolKind::DatatypeSelector => ay_frontend::DeclarationKind::DatatypeSelector,
        NativeReplaySymbolKind::DatatypeTester => ay_frontend::DeclarationKind::DatatypeTester,
    }
}

fn exact_replayed_nullary_constructor_term(
    solver: &Solver,
    identity: &str,
    expected_sort: &Sort,
) -> Option<TermId> {
    let context = solver.executor.context();
    let (carrier, _) = context.is_constructor(identity)?;
    if !context.is_live_datatype_carrier(&carrier) {
        return None;
    }
    let info = context.symbol_info_by_identity(identity)?;
    let exact = context.exact_datatype_member_info(identity)?;
    let expected_kind = ay_frontend::DeclarationKind::DatatypeConstructor;
    if info.declaration_id() != exact.declaration_id()
        || info.declaration_kind() != expected_kind
        || exact.declaration_kind() != expected_kind
        || context.effective_declaration_kind(info.declaration_id()) != Some(expected_kind)
        || !info.arg_sorts.is_empty()
        || !exact.arg_sorts.is_empty()
        || &info.sort != expected_sort
        || &exact.sort != expected_sort
        || info.term != exact.term
    {
        return None;
    }
    let term = info.term?;
    if solver.terms().sort(term) != expected_sort
        || !matches!(solver.terms().get(term), TermData::Var(name, _) if name == identity)
    {
        return None;
    }
    Some(term)
}

fn replay_native_declarations_in_event_order(
    artifact: &NativeReplayArtifact,
    solver: &mut Solver,
) -> Result<(NativeReplayIdentityRemap, HashMap<TermId, TermId>), SolverError> {
    let mut remap = NativeReplayIdentityRemap::default();
    let constants: HashMap<_, _> = artifact
        .declarations
        .iter()
        .map(|declaration| (declaration.term, declaration))
        .collect();
    let functions: HashMap<_, _> = artifact
        .function_declarations
        .iter()
        .map(|declaration| (declaration.name.as_str(), declaration))
        .collect();
    let nodes: HashMap<_, _> = artifact.terms.iter().map(|node| (node.id, node)).collect();
    let expected_datatypes = datatype_declarations_from_events(&artifact.events);
    let mut rebuilt_constants = HashMap::default();
    let mut seen_constants = HashSet::default();
    let mut seen_functions = HashSet::default();
    let mut seen_datatypes = Vec::new();

    for event in &artifact.events {
        match &event.kind {
            NativeReplayEventKind::DeclareConst { name, term, sort } => {
                let Some(declaration) = constants.get(term).copied() else {
                    continue;
                };
                let node = nodes.get(term).copied().ok_or_else(|| {
                    native_replay_artifact_error(format!(
                        "constant declaration event `{name}` references missing term {}",
                        term.0
                    ))
                })?;
                if name != &declaration.name || sort != &node.sort {
                    return Err(native_replay_artifact_error(format!(
                        "constant declaration event for term {} disagrees with its retained declaration",
                        term.0
                    )));
                }
                if !seen_constants.insert(*term) {
                    return Err(native_replay_artifact_error(format!(
                        "constant term {} has duplicate declaration events",
                        term.0
                    )));
                }
                let rebuilt = solver
                    .try_declare_const(&declaration.name, declaration.sort.clone())?
                    .id();
                let rebuilt_core =
                    authenticated_native_constant_core_name(solver, &declaration.name, rebuilt)
                        .ok_or_else(|| {
                            native_replay_artifact_error(format!(
                        "replayed declaration `{}` lacks exact live frontend identity metadata",
                        declaration.name
                    ))
                        })?;
                authenticate_replayed_constant_identity(
                    artifact,
                    solver,
                    declaration,
                    rebuilt,
                    &rebuilt_core,
                    &mut remap,
                )?;
                rebuilt_constants.insert(*term, rebuilt);
            }
            NativeReplayEventKind::DeclareFun {
                name,
                domain,
                range,
            } => {
                let Some(declaration) = functions.get(name.as_str()).copied() else {
                    continue;
                };
                if domain != &declaration.domain || range != &declaration.range {
                    return Err(native_replay_artifact_error(format!(
                        "function declaration event `{name}` disagrees with its retained declaration"
                    )));
                }
                if !seen_functions.insert(name.clone()) {
                    return Err(native_replay_artifact_error(format!(
                        "function `{name}` has duplicate declaration events"
                    )));
                }
                let rebuilt =
                    solver.try_declare_fun(name, &declaration.domain, declaration.range.clone())?;
                authenticate_replayed_function_identity(
                    artifact,
                    solver,
                    declaration,
                    &rebuilt,
                    &mut remap,
                )?;
            }
            NativeReplayEventKind::DeclareDatatype { datatype } => {
                if seen_datatypes.contains(datatype) {
                    continue;
                }
                solver.try_declare_datatype(datatype)?;
                authenticate_replayed_datatype_identity(artifact, solver, datatype, &mut remap)?;
                seen_datatypes.push(datatype.clone());
            }
            _ => {}
        }
    }

    if seen_constants.len() != artifact.declarations.len() {
        return Err(native_replay_artifact_error(
            "retained native constant lacks one declaration event",
        ));
    }
    if seen_functions.len() != artifact.function_declarations.len() {
        return Err(native_replay_artifact_error(
            "retained native function lacks one declaration event",
        ));
    }
    if seen_datatypes.len() != expected_datatypes.len() {
        return Err(native_replay_artifact_error(
            "retained native datatype lacks one declaration event",
        ));
    }
    Ok((remap, rebuilt_constants))
}

fn authenticate_replayed_datatype_identity(
    artifact: &NativeReplayArtifact,
    solver: &Solver,
    datatype: &DatatypeSort,
    remap: &mut NativeReplayIdentityRemap,
) -> Result<(), SolverError> {
    if artifact.symbol_identities.is_empty() {
        return Ok(());
    }

    let identities: Vec<_> = artifact
        .symbol_identities
        .iter()
        .filter(|identity| identity.datatype_surface.as_deref() == Some(datatype.name.as_str()))
        .collect();
    let old_core = identities
        .first()
        .and_then(|identity| identity.datatype_core.as_deref())
        .ok_or_else(|| {
            native_replay_artifact_error(format!(
                "replayed datatype `{}` lacks an authenticated carrier row",
                datatype.name
            ))
        })?;
    let rebuilt = solver.lower_live_sort(&Sort::Uninterpreted(datatype.name.clone()));
    let Sort::Uninterpreted(new_carrier_core) = rebuilt else {
        return Err(native_replay_artifact_error(format!(
            "replayed datatype `{}` lacks one nominal engine carrier",
            datatype.name
        )));
    };
    if !solver
        .executor
        .context()
        .is_live_datatype_carrier(&new_carrier_core)
    {
        return Err(native_replay_artifact_error(format!(
            "replayed datatype `{}` carrier `{new_carrier_core}` is not live",
            datatype.name
        )));
    }
    remap.insert_carrier(old_core, &new_carrier_core)?;
    let _ = remap.remap_sort(&Sort::Datatype(datatype.clone()))?;

    for identity in identities {
        for sort in &identity.api_domain {
            let _ = remap.remap_sort(sort)?;
        }
        let _ = remap.remap_sort(&identity.api_range)?;
        let engine_domain: Vec<_> = identity
            .engine_domain
            .iter()
            .map(|sort| remap.remap_sort(sort))
            .collect::<Result<Vec<_>, SolverError>>()?;
        let engine_range = remap.remap_sort(&identity.engine_range)?;
        let public_domain: Vec<_> = identity
            .public_domain
            .iter()
            .map(|sort| remap.remap_public_sort(sort))
            .collect::<Result<Vec<_>, SolverError>>()?;
        let public_range = remap.remap_public_sort(&identity.public_range)?;
        let expected_kind = frontend_symbol_kind(identity.kind);
        let context = solver.executor.context();
        let mut matches = context.symbols_iter().filter(|(surface, info)| {
            surface.as_str() == identity.surface_name.as_str()
                && info.arg_sorts == engine_domain
                && info.sort == engine_range
                && info.public_arg_sorts == public_domain
                && info.public_sort == public_range
                && info.declaration_kind() == expected_kind
                && context.effective_declaration_kind(info.declaration_id()) == Some(expected_kind)
        });
        let (surface, info) = matches.next().ok_or_else(|| {
            native_replay_artifact_error(format!(
                "datatype member `{}` has no exact rebuilt declaration",
                identity.surface_name
            ))
        })?;
        if matches.next().is_some() {
            return Err(native_replay_artifact_error(format!(
                "datatype member `{}` has an ambiguous rebuilt declaration",
                identity.surface_name
            )));
        }
        let new_member_core = context.symbol_identity_name(surface, info).to_string();
        let exact = context
            .exact_datatype_member_info(&new_member_core)
            .is_some_and(|exact| {
                exact.declaration_id() == info.declaration_id()
                    && exact.declaration_kind() == expected_kind
                    && exact.arg_sorts == engine_domain
                    && exact.sort == engine_range
            });
        if !exact {
            return Err(native_replay_artifact_error(format!(
                "datatype member `{}` lacks exact rebuilt member provenance",
                identity.surface_name
            )));
        }
        let rebuilt_carrier = Sort::Uninterpreted(new_carrier_core.clone());
        let carrier_matches = match identity.kind {
            NativeReplaySymbolKind::DatatypeConstructor => engine_range == rebuilt_carrier,
            NativeReplaySymbolKind::DatatypeSelector | NativeReplaySymbolKind::DatatypeTester => {
                engine_domain.as_slice() == std::slice::from_ref(&rebuilt_carrier)
            }
            _ => false,
        };
        if !carrier_matches {
            return Err(native_replay_artifact_error(format!(
                "datatype member `{}` is not owned by its claimed carrier `{carrier}`",
                identity.surface_name,
                carrier = datatype.name
            )));
        }
        let is_nullary_constructor = identity.kind == NativeReplaySymbolKind::DatatypeConstructor
            && identity.api_domain.is_empty();
        if is_nullary_constructor
            && exact_replayed_nullary_constructor_term(solver, &new_member_core, &engine_range)
                .is_none()
        {
            return Err(native_replay_artifact_error(format!(
                "datatype constructor `{}` lacks exact live nullary-term provenance",
                identity.surface_name
            )));
        }
        remap.insert_core(&identity.core_name, &new_member_core)?;
        if is_nullary_constructor {
            remap.insert_nullary_constructor(&identity.core_name, &new_member_core)?;
        }
    }
    Ok(())
}

fn authenticate_replayed_function_identity(
    artifact: &NativeReplayArtifact,
    solver: &Solver,
    declaration: &NativeReplayFunctionDeclaration,
    rebuilt: &FuncDecl,
    remap: &mut NativeReplayIdentityRemap,
) -> Result<(), SolverError> {
    let identity = artifact.symbol_identities.iter().find(|identity| {
        identity.core_name == declaration.core_name
            && identity.surface_name.eq(&declaration.name)
            && matches!(
                identity.kind,
                NativeReplaySymbolKind::Uninterpreted | NativeReplaySymbolKind::Theory
            )
    });
    if artifact.symbol_identities.is_empty() {
        remap.insert_core(&declaration.core_name, rebuilt.core_name())?;
        return Ok(());
    }
    let Some(identity) = identity else {
        return Err(native_replay_artifact_error(format!(
            "function `{}` lacks an authenticated identity row",
            declaration.name
        )));
    };
    if identity.api_domain != declaration.domain
        || identity.api_range != declaration.range
        || rebuilt.domain != declaration.domain
        || rebuilt.range != declaration.range
    {
        return Err(native_replay_artifact_error(format!(
            "function `{}` has inconsistent exact native API sort identity",
            declaration.name
        )));
    }
    for sort in &identity.api_domain {
        let _ = remap.remap_sort(sort)?;
    }
    let _ = remap.remap_sort(&identity.api_range)?;
    let engine_domain: Vec<_> = identity
        .engine_domain
        .iter()
        .map(|sort| remap.remap_sort(sort))
        .collect::<Result<Vec<_>, SolverError>>()?;
    let engine_range = remap.remap_sort(&identity.engine_range)?;
    let public_domain: Vec<_> = identity
        .public_domain
        .iter()
        .map(|sort| remap.remap_public_sort(sort))
        .collect::<Result<Vec<_>, SolverError>>()?;
    let public_range = remap.remap_public_sort(&identity.public_range)?;
    let expected_kind = frontend_symbol_kind(identity.kind);
    let context = solver.executor.context();
    let mut matches = context.symbols_iter().filter(|(surface, info)| {
        surface.as_str() == declaration.name.as_str()
            && context.symbol_identity_name(surface, info) == rebuilt.core_name()
            && info.arg_sorts == engine_domain
            && info.sort == engine_range
            && info.public_arg_sorts == public_domain
            && info.public_sort == public_range
            && info.declaration_kind() == expected_kind
            && context.effective_declaration_kind(info.declaration_id()) == Some(expected_kind)
    });
    if matches.next().is_none() || matches.next().is_some() {
        return Err(native_replay_artifact_error(format!(
            "function `{}` did not rebuild to one exact live identity",
            declaration.name
        )));
    }
    remap.insert_core(&identity.core_name, rebuilt.core_name())
}

fn authenticate_replayed_constant_identity(
    artifact: &NativeReplayArtifact,
    solver: &Solver,
    declaration: &NativeReplayDeclaration,
    rebuilt: TermId,
    rebuilt_core_name: &str,
    remap: &mut NativeReplayIdentityRemap,
) -> Result<(), SolverError> {
    if artifact.symbol_identities.is_empty() {
        return remap.insert_core(&declaration.core_name, rebuilt_core_name);
    }
    let identity = artifact
        .symbol_identities
        .iter()
        .find(|identity| {
            identity.core_name == declaration.core_name
                && identity.surface_name.eq(&declaration.name)
                && identity.kind == NativeReplaySymbolKind::Uninterpreted
                && identity.engine_domain.is_empty()
        })
        .ok_or_else(|| {
            native_replay_artifact_error(format!(
                "constant `{}` lacks an authenticated identity row",
                declaration.name
            ))
        })?;
    if !identity.api_domain.is_empty() || identity.api_range != declaration.sort {
        return Err(native_replay_artifact_error(format!(
            "constant `{}` has inconsistent exact native API sort identity",
            declaration.name
        )));
    }
    let _ = remap.remap_sort(&identity.api_range)?;
    let engine_range = remap.remap_sort(&identity.engine_range)?;
    let public_range = remap.remap_public_sort(&identity.public_range)?;
    let context = solver.executor.context();
    let mut matches = context.symbols_iter().filter(|(surface, info)| {
        surface.as_str() == declaration.name.as_str()
            && info.term == Some(rebuilt)
            && context.symbol_identity_name(surface, info) == rebuilt_core_name
            && info.arg_sorts.is_empty()
            && info.public_arg_sorts.is_empty()
            && info.sort == engine_range
            && info.public_sort == public_range
            && info.declaration_kind() == ay_frontend::DeclarationKind::Uninterpreted
            && context.effective_declaration_kind(info.declaration_id())
                == Some(ay_frontend::DeclarationKind::Uninterpreted)
    });
    if matches.next().is_none() || matches.next().is_some() {
        return Err(native_replay_artifact_error(format!(
            "constant `{}` did not rebuild to its exact live identity",
            declaration.name
        )));
    }
    remap.insert_core(&identity.core_name, rebuilt_core_name)
}

/// Validate public declaration sorts only after replay has reconstructed the
/// live nominal-sort registry.  Context-free lowering cannot distinguish two
/// scoped datatype incarnations with the same surface name.
fn validate_native_replay_declaration_sorts(
    artifact: &NativeReplayArtifact,
    solver: &Solver,
    remap: &NativeReplayIdentityRemap,
) -> Result<(), SolverError> {
    let nodes: HashMap<_, _> = artifact.terms.iter().map(|node| (node.id, node)).collect();
    for declaration in &artifact.declarations {
        let node = nodes.get(&declaration.term).ok_or_else(|| {
            native_replay_artifact_error(format!(
                "declaration `{}` references missing term {}",
                declaration.name, declaration.term.0
            ))
        })?;
        let _ = remap.remap_sort(&declaration.sort)?;
        let lowered = solver.lower_live_sort(&declaration.sort);
        let recorded_sort = remap.remap_sort(&node.sort)?;
        if lowered != recorded_sort {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` lowers in the replay context to sort {lowered}, but term {} records {recorded_sort}",
                declaration.name, declaration.term.0
            )));
        }
    }
    Ok(())
}

fn reason_phase(reason: &crate::UnknownReason) -> &'static str {
    match reason {
        crate::UnknownReason::Timeout
        | crate::UnknownReason::Interrupted
        | crate::UnknownReason::MemoryLimit => "search-control",
        crate::UnknownReason::InternalError => "executor",
        crate::UnknownReason::Unsupported => "theory-combination",
        _ => "unknown",
    }
}

fn rebuild_term_node(
    solver: &mut Solver,
    source_node: &NativeReplayTermNode,
    node: &NativeReplayTermNode,
    declarations: &HashMap<TermId, &NativeReplayDeclaration>,
    source_nodes: &HashMap<TermId, &NativeReplayTermNode>,
    term_map: &HashMap<TermId, TermId>,
    predeclared_constants: &HashMap<TermId, TermId>,
) -> Result<TermId, SolverError> {
    match &node.data {
        TermData::Const(constant) => match constant {
            Constant::Bool(value) => Ok(solver.terms_mut().mk_bool(*value)),
            Constant::Int(value) => Ok(solver.terms_mut().mk_int(value.clone())),
            Constant::Rational(value) => Ok(solver.terms_mut().mk_rational(value.0.clone())),
            Constant::BitVec { value, width } => {
                Ok(solver.terms_mut().mk_bitvec(value.clone(), *width))
            }
            Constant::String(value) => Ok(solver.terms_mut().mk_string(value.clone())),
            _ => unreplayable_term("constant", node.id),
        },
        TermData::Var(name, _) => {
            if let Some(decl) = declarations.get(&node.id) {
                predeclared_constants.get(&node.id).copied().ok_or_else(|| {
                    native_replay_artifact_error(format!(
                        "constant `{}` was not rebuilt at its declaration event",
                        decl.name
                    ))
                })
            } else if node.is_datatype_constructor {
                // Nullary datatype constructors are stored as Vars. Reuse the
                // exact term registered by the authenticated replayed datatype
                // declaration. A same-named ordinary constant is not enough.
                exact_replayed_nullary_constructor_term(solver, name, &node.sort).ok_or_else(|| {
                    native_replay_artifact_error(format!(
                        "term {} claims nullary datatype-constructor provenance without one exact live constructor `{name}`",
                        node.id.0
                    ))
                })
            } else {
                // An artifact Var not owned by a declaration is an identity in
                // its own right, even when its old spelling happens to equal a
                // declaration core allocated in this fresh replay. Reusing the
                // spelling would let it alias that live declaration through
                // name-based quantifier machinery. Give every such node a
                // replay-local identity; enclosing binders subsequently replace
                // the exact source nodes they capture with their own alpha vars.
                Ok(solver
                    .terms_mut()
                    .mk_fresh_var("__ay_native_replay_var", node.sort.clone()))
            }
        }
        TermData::App(symbol, args) => {
            let mapped = map_terms(args, term_map)?;
            rebuild_application(solver, node, symbol, args, mapped)
        }
        TermData::Let(bindings, body) => {
            let mapped_values = bindings
                .iter()
                .map(|(_, term)| map_term(*term, term_map))
                .collect::<Result<Vec<_>, SolverError>>()?;
            let source_bindings = match &source_node.data {
                TermData::Let(source_bindings, source_body) if source_body == body => {
                    source_bindings
                }
                _ => {
                    return Err(native_replay_term_error(
                        node.id,
                        "identity remap changed the shape of a let expression",
                    ));
                }
            };
            let source_expected = source_bindings
                .iter()
                .map(|(name, value)| {
                    let value_node = source_nodes.get(value).ok_or_else(|| {
                        native_replay_term_error(
                            node.id,
                            format!("let binding references missing term {}", value.0),
                        )
                    })?;
                    Ok((name.clone(), value_node.sort.clone()))
                })
                .collect::<Result<Vec<_>, SolverError>>()?;
            let captures =
                capture_source_bound_terms(source_nodes, node.id, &source_expected, &[*body])?;
            let replay_sorts = mapped_values
                .iter()
                .map(|value| solver.terms().sort(*value).clone())
                .collect::<Vec<_>>();
            let (alpha_names, substitutions) =
                build_replay_alpha_bindings(solver, node.id, &replay_sorts, &captures, term_map)?;
            let mapped_bindings = alpha_names
                .into_iter()
                .zip(mapped_values)
                .collect::<Vec<_>>();
            let rebuilt_body = map_term(*body, term_map)?;
            let mapped_body = alpha_substitute_replay_term(
                solver.terms_mut(),
                rebuilt_body,
                &substitutions,
                node.id,
            )?;
            if solver.terms().sort(mapped_body) != &node.sort {
                return Err(native_replay_term_error(
                    node.id,
                    "let expression result sort does not match its body",
                ));
            }
            validate_replay_let(solver, node.id, &mapped_bindings, mapped_body)?;
            Ok(solver.terms_mut().mk_let(mapped_bindings, mapped_body))
        }
        TermData::Not(inner) => {
            let inner = map_term(*inner, term_map)?;
            require_replay_sort(solver, node.id, inner, &Sort::Bool, "not operand")?;
            Ok(solver.terms_mut().mk_not(inner))
        }
        TermData::Ite(cond, then_term, else_term) => {
            let cond = map_term(*cond, term_map)?;
            let then_term = map_term(*then_term, term_map)?;
            let else_term = map_term(*else_term, term_map)?;
            require_replay_sort(solver, node.id, cond, &Sort::Bool, "ite condition")?;
            let then_sort = solver.terms().sort(then_term);
            let else_sort = solver.terms().sort(else_term);
            if then_sort != else_sort || then_sort != &node.sort {
                return Err(native_replay_term_error(
                    node.id,
                    format!(
                        "ite branch sorts must match the recorded result sort (then {then_sort}, else {else_sort}, result {})",
                        node.sort
                    ),
                ));
            }
            Ok(solver.terms_mut().mk_ite(cond, then_term, else_term))
        }
        TermData::Forall(vars, body, triggers) => {
            let (vars, body, triggers) = rebuild_alpha_quantifier(
                solver,
                source_node,
                node,
                vars,
                *body,
                triggers,
                source_nodes,
                term_map,
            )?;
            validate_replay_quantifier(solver, node.id, &vars, body, &triggers)?;
            Ok(solver
                .terms_mut()
                .mk_forall_with_triggers(vars, body, triggers))
        }
        TermData::Exists(vars, body, triggers) => {
            let (vars, body, triggers) = rebuild_alpha_quantifier(
                solver,
                source_node,
                node,
                vars,
                *body,
                triggers,
                source_nodes,
                term_map,
            )?;
            validate_replay_quantifier(solver, node.id, &vars, body, &triggers)?;
            Ok(solver
                .terms_mut()
                .mk_exists_with_triggers(vars, body, triggers))
        }
        _ => unreplayable_term("future term kind", node.id),
    }
}

/// Rebuild one quantifier with a replay-local alpha identity for every binder.
///
/// Capture is computed over the serialized source DAG, before declaration-core
/// remapping. That distinction is essential: a private declaration core can be
/// rebuilt under a public spelling that happens to equal an unrelated binder.
/// Matching after remapping would capture it accidentally. Conversely, a native
/// caller may deliberately use a declared constant as a quantifier variable;
/// the source TermId capture set lets us replace that occurrence contextually
/// without ever reusing the live declaration term as the bound variable.
fn rebuild_alpha_quantifier(
    solver: &mut Solver,
    source_node: &NativeReplayTermNode,
    node: &NativeReplayTermNode,
    replay_vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
    source_nodes: &HashMap<TermId, &NativeReplayTermNode>,
    term_map: &HashMap<TermId, TermId>,
) -> Result<(Vec<(String, Sort)>, TermId, Vec<Vec<TermId>>), SolverError> {
    let (source_vars, source_body, source_triggers) = match (&source_node.data, &node.data) {
        (
            TermData::Forall(source_vars, source_body, source_triggers),
            TermData::Forall(_, replay_body, replay_triggers),
        )
        | (
            TermData::Exists(source_vars, source_body, source_triggers),
            TermData::Exists(_, replay_body, replay_triggers),
        ) if source_body == replay_body && source_triggers == replay_triggers => {
            (source_vars, *source_body, source_triggers)
        }
        _ => {
            return Err(native_replay_term_error(
                node.id,
                "identity remap changed the shape of a quantifier",
            ));
        }
    };
    if source_body != body || source_triggers != triggers || source_vars.len() != replay_vars.len()
    {
        return Err(native_replay_term_error(
            node.id,
            "quantifier source and replay signatures disagree",
        ));
    }

    let mut roots = Vec::with_capacity(1 + source_triggers.iter().map(Vec::len).sum::<usize>());
    roots.push(source_body);
    roots.extend(source_triggers.iter().flatten().copied());
    let captures = capture_source_bound_terms(source_nodes, node.id, source_vars, &roots)?;
    let replay_sorts = replay_vars
        .iter()
        .map(|(_, sort)| sort.clone())
        .collect::<Vec<_>>();
    let (alpha_names, substitutions) =
        build_replay_alpha_bindings(solver, node.id, &replay_sorts, &captures, term_map)?;
    let alpha_vars = alpha_names
        .into_iter()
        .zip(replay_sorts)
        .collect::<Vec<_>>();

    let mapped_body = map_term(body, term_map)?;
    let body =
        alpha_substitute_replay_term(solver.terms_mut(), mapped_body, &substitutions, node.id)?;
    let mapped_triggers = map_triggers(triggers, term_map)?;
    let triggers = mapped_triggers
        .into_iter()
        .map(|multi| {
            multi
                .into_iter()
                .map(|trigger| {
                    alpha_substitute_replay_term(
                        solver.terms_mut(),
                        trigger,
                        &substitutions,
                        node.id,
                    )
                })
                .collect::<Result<Vec<_>, SolverError>>()
        })
        .collect::<Result<Vec<_>, SolverError>>()?;
    Ok((alpha_vars, body, triggers))
}

/// Mint one fresh bound Var per lexical binder and translate serialized capture
/// TermIds into substitutions over the already-rebuilt child DAG.
fn build_replay_alpha_bindings(
    solver: &mut Solver,
    owner: TermId,
    replay_sorts: &[Sort],
    captures: &[Vec<TermId>],
    term_map: &HashMap<TermId, TermId>,
) -> Result<(Vec<String>, HashMap<TermId, TermId>), SolverError> {
    if replay_sorts.len() != captures.len() {
        return Err(native_replay_term_error(
            owner,
            "binder capture table has the wrong arity",
        ));
    }

    let mut alpha_names = Vec::with_capacity(replay_sorts.len());
    let mut substitutions = HashMap::default();
    for (sort, captured) in replay_sorts.iter().zip(captures) {
        let alpha = solver
            .terms_mut()
            .mk_fresh_var("__ay_native_replay_bound", sort.clone());
        let alpha_name = match solver.terms().get(alpha) {
            TermData::Var(name, _) => name.clone(),
            _ => {
                return Err(native_replay_term_error(
                    owner,
                    "fresh replay binder did not produce a variable",
                ));
            }
        };
        alpha_names.push(alpha_name);

        for &source_term in captured {
            let replay_term = map_term(source_term, term_map)?;
            if let Some(previous) = substitutions.insert(replay_term, alpha) {
                if previous != alpha {
                    return Err(native_replay_term_error(
                        owner,
                        format!("source term {} is captured by two bindings", source_term.0),
                    ));
                }
            }
        }
    }
    Ok((alpha_names, substitutions))
}

/// Simultaneously replace exact child identities throughout a rebuilt replay
/// term, including quantifier triggers. Nested binders have already undergone
/// their own alpha reconstruction because replay nodes are topologically
/// ordered, so a replacement left in a nested body is precisely an occurrence
/// captured by the current outer binder.
fn alpha_substitute_replay_term(
    terms: &mut TermStore,
    root: TermId,
    substitutions: &HashMap<TermId, TermId>,
    owner: TermId,
) -> Result<TermId, SolverError> {
    fn visit(
        terms: &mut TermStore,
        term: TermId,
        substitutions: &HashMap<TermId, TermId>,
        cache: &mut HashMap<TermId, TermId>,
        owner: TermId,
    ) -> Result<TermId, SolverError> {
        if let Some(&replacement) = substitutions.get(&term) {
            return Ok(replacement);
        }
        if let Some(&rebuilt) = cache.get(&term) {
            return Ok(rebuilt);
        }

        let data = terms.get(term).clone();
        let sort = terms.sort(term).clone();
        let rebuilt = match data {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(symbol, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| visit(terms, arg, substitutions, cache, owner))
                    .collect::<Result<Vec<_>, SolverError>>()?;
                terms.mk_app(symbol, args, sort)
            }
            TermData::Let(bindings, body) => {
                let bindings = bindings
                    .into_iter()
                    .map(|(name, value)| {
                        Ok((name, visit(terms, value, substitutions, cache, owner)?))
                    })
                    .collect::<Result<Vec<_>, SolverError>>()?;
                let body = visit(terms, body, substitutions, cache, owner)?;
                terms.mk_let(bindings, body)
            }
            TermData::Not(inner) => {
                let inner = visit(terms, inner, substitutions, cache, owner)?;
                terms.mk_not(inner)
            }
            TermData::Ite(condition, then_term, else_term) => {
                let condition = visit(terms, condition, substitutions, cache, owner)?;
                let then_term = visit(terms, then_term, substitutions, cache, owner)?;
                let else_term = visit(terms, else_term, substitutions, cache, owner)?;
                terms.mk_ite(condition, then_term, else_term)
            }
            TermData::Forall(vars, body, triggers) => {
                let body = visit(terms, body, substitutions, cache, owner)?;
                let triggers = triggers
                    .into_iter()
                    .map(|multi| {
                        multi
                            .into_iter()
                            .map(|trigger| visit(terms, trigger, substitutions, cache, owner))
                            .collect::<Result<Vec<_>, SolverError>>()
                    })
                    .collect::<Result<Vec<_>, SolverError>>()?;
                let quantifier = terms.mk_forall_with_triggers(vars, body, triggers);
                terms.copy_quantifier_metadata(term, quantifier);
                quantifier
            }
            TermData::Exists(vars, body, triggers) => {
                let body = visit(terms, body, substitutions, cache, owner)?;
                let triggers = triggers
                    .into_iter()
                    .map(|multi| {
                        multi
                            .into_iter()
                            .map(|trigger| visit(terms, trigger, substitutions, cache, owner))
                            .collect::<Result<Vec<_>, SolverError>>()
                    })
                    .collect::<Result<Vec<_>, SolverError>>()?;
                let quantifier = terms.mk_exists_with_triggers(vars, body, triggers);
                terms.copy_quantifier_metadata(term, quantifier);
                quantifier
            }
            _ => {
                return Err(native_replay_term_error(
                    owner,
                    "alpha-renaming encountered an unsupported future term kind",
                ));
            }
        };
        cache.insert(term, rebuilt);
        Ok(rebuilt)
    }

    if substitutions.is_empty() {
        return Ok(root);
    }
    let mut cache = HashMap::default();
    visit(terms, root, substitutions, &mut cache, owner)
}

fn rebuild_application(
    solver: &mut Solver,
    node: &NativeReplayTermNode,
    symbol: &Symbol,
    raw_args: &[TermId],
    mapped_args: Vec<TermId>,
) -> Result<TermId, SolverError> {
    let term_count = solver.terms().len();
    if let Some((&raw, &mapped)) = raw_args
        .iter()
        .zip(&mapped_args)
        .find(|(_, mapped)| mapped.index() >= term_count)
    {
        return Err(native_replay_term_error(
            node.id,
            format!(
                "application argument {} mapped to invalid replay term {}",
                raw.0, mapped.0
            ),
        ));
    }

    match symbol {
        Symbol::Named(name) => {
            // `const-array` is stored as a named application in the native
            // term DAG, but its SMT-LIB surface form is a qualified `const`
            // identifier.  Reconstruct it directly: the value alone does not
            // carry the array's index sort, so recover that authority from the
            // recorded result sort and let the fallible native constructor
            // rebuild the exact node.
            if name == "const-array" {
                return rebuild_const_array(solver, node, &mapped_args);
            }

            // A programmatic declaration owns its exact symbol identity even
            // when the spelling resembles one of the core encodings used for
            // higher-order array operators. In particular, native nullary UFs
            // are registered in the frontend as constant-like symbols, but
            // `try_apply` still represents their calls as zero-argument Apps.
            // Authenticate registered declarations before interpreting the
            // `as-array[...]` / `map[...]` encodings.
            let declaration = solver
                .executor
                .context()
                .symbol_info_by_identity(name)
                .cloned();
            if let Some(declaration) = declaration {
                let is_native_function = solver
                    .native_fun_signatures
                    .values()
                    .any(|registration| registration.core_name == *name);
                if declaration.term.is_some() && !is_native_function {
                    return Err(native_replay_term_error(
                        node.id,
                        format!("application head `{name}` denotes a registered nullary constant"),
                    ));
                }
                let actual_domain: Vec<Sort> = mapped_args
                    .iter()
                    .map(|&arg| solver.terms().sort(arg).clone())
                    .collect();
                let function = replayed_function_declaration(
                    solver,
                    node.id,
                    name,
                    &declaration,
                    &actual_domain,
                    &node.sort,
                )?;
                let args: Vec<Term> = mapped_args
                    .iter()
                    .copied()
                    .map(|id| solver.wrap_term(id))
                    .collect();
                let rebuilt = solver.try_apply(&function, &args).map_err(|error| {
                    native_replay_term_error(
                        node.id,
                        format!(
                            "registered application `{name}` does not match its declaration: {error}"
                        ),
                    )
                })?;
                return validate_rebuilt_application(
                    solver,
                    node,
                    symbol,
                    &mapped_args,
                    rebuilt.id(),
                );
            }

            if let Some(function) = name
                .strip_prefix("as-array[")
                .and_then(|name| name.strip_suffix(']'))
            {
                return rebuild_as_array(solver, node, function, &mapped_args);
            }
            if let Some(function) = name
                .strip_prefix("map[")
                .and_then(|name| name.strip_suffix(']'))
            {
                return rebuild_array_map(solver, node, function, &mapped_args);
            }
        }
        Symbol::Indexed(_, _) => {}
        _ => return unreplayable_term("future application symbol", node.id),
    }

    rebuild_builtin_application(solver, node, symbol, &mapped_args)
}

fn rebuild_const_array(
    solver: &mut Solver,
    node: &NativeReplayTermNode,
    args: &[TermId],
) -> Result<TermId, SolverError> {
    let [value] = args else {
        return Err(native_replay_term_error(
            node.id,
            format!(
                "`const-array` requires exactly one value argument, got {}",
                args.len()
            ),
        ));
    };
    let Sort::Array(array) = &node.sort else {
        return Err(native_replay_term_error(
            node.id,
            "`const-array` must have an array result sort",
        ));
    };

    let value = solver.wrap_term(*value);
    let rebuilt = solver
        .try_const_array(array.index_sort.clone(), value)
        .map_err(|error| {
            native_replay_term_error(
                node.id,
                format!("cannot reconstruct `const-array`: {error}"),
            )
        })?;
    let actual_sort = solver.terms().sort(rebuilt.id());
    if actual_sort != &node.sort {
        return Err(native_replay_term_error(
            node.id,
            format!(
                "`const-array` records result sort {}, but its value reconstructs {actual_sort}",
                node.sort
            ),
        ));
    }
    Ok(rebuilt.id())
}

fn rebuild_as_array(
    solver: &mut Solver,
    node: &NativeReplayTermNode,
    function: &str,
    args: &[TermId],
) -> Result<TermId, SolverError> {
    if !args.is_empty() {
        return Err(native_replay_term_error(
            node.id,
            format!("`as-array[{function}]` requires zero arguments"),
        ));
    }
    let Sort::Array(array) = &node.sort else {
        return Err(native_replay_term_error(
            node.id,
            format!("`as-array[{function}]` must have an array result sort"),
        ));
    };
    authenticate_function_signature(
        solver,
        node.id,
        function,
        std::slice::from_ref(&array.index_sort),
        &array.element_sort,
    )?;
    Ok(solver.terms_mut().mk_as_array(function, node.sort.clone()))
}

fn rebuild_array_map(
    solver: &mut Solver,
    node: &NativeReplayTermNode,
    function: &str,
    args: &[TermId],
) -> Result<TermId, SolverError> {
    if args.is_empty() {
        return Err(native_replay_term_error(
            node.id,
            format!("`map[{function}]` requires at least one array argument"),
        ));
    }
    let Sort::Array(result) = &node.sort else {
        return Err(native_replay_term_error(
            node.id,
            format!("`map[{function}]` must have an array result sort"),
        ));
    };
    let mut domain = Vec::with_capacity(args.len());
    for &arg in args {
        let Sort::Array(array) = solver.terms().sort(arg) else {
            return Err(native_replay_term_error(
                node.id,
                format!("`map[{function}]` argument {} is not an array", arg.0),
            ));
        };
        if array.index_sort != result.index_sort {
            return Err(native_replay_term_error(
                node.id,
                format!(
                    "`map[{function}]` argument {} has the wrong index sort",
                    arg.0
                ),
            ));
        }
        domain.push(array.element_sort.clone());
    }
    authenticate_function_signature(solver, node.id, function, &domain, &result.element_sort)?;
    Ok(solver
        .terms_mut()
        .mk_array_map(function, args.to_vec(), node.sort.clone()))
}

fn authenticate_function_signature(
    solver: &mut Solver,
    node: TermId,
    name: &str,
    domain: &[Sort],
    range: &Sort,
) -> Result<(), SolverError> {
    let mut arguments = Vec::with_capacity(domain.len());
    for sort in domain {
        arguments.push(
            solver
                .try_fresh_var("native_replay_validation", sort.clone())
                .map_err(|error| {
                    native_replay_term_error(
                        node,
                        format!("cannot validate function `{name}`: {error}"),
                    )
                })?,
        );
    }
    let registered = solver
        .executor
        .context()
        .symbol_info_by_identity(name)
        .cloned();
    if let Some(registered) = registered {
        let declaration =
            replayed_function_declaration(solver, node, name, &registered, domain, range)?;
        solver
            .try_apply(&declaration, &arguments)
            .map_err(|error| {
                native_replay_term_error(
                    node,
                    format!("function `{name}` does not match a replayed declaration: {error}"),
                )
            })?;
        return Ok(());
    }

    let bindings: Vec<(String, TermId)> = arguments
        .iter()
        .enumerate()
        .map(|(index, argument)| (format!("native_replay_function_arg_{index}"), argument.id()))
        .collect();
    let parsed = ay_frontend::Term::App(
        name.to_string(),
        bindings
            .iter()
            .map(|(name, _)| ay_frontend::Term::Symbol(name.clone()))
            .collect(),
    );
    let application = solver
        .executor
        .context_mut_internal()
        .elaborate_surface_subterm_with_bindings(&parsed, &bindings)
        .ok_or_else(|| {
            native_replay_term_error(
                node,
                format!("function `{name}` is neither declared nor a valid named builtin"),
            )
        })?;
    let actual_range = solver.terms().sort(application);
    if actual_range != range {
        return Err(native_replay_term_error(
            node,
            format!("function `{name}` has result sort {actual_range}, expected {range}"),
        ));
    }
    Ok(())
}

fn replayed_function_declaration(
    solver: &Solver,
    node: TermId,
    name: &str,
    registered: &ay_frontend::SymbolInfo,
    actual_domain: &[Sort],
    actual_range: &Sort,
) -> Result<FuncDecl, SolverError> {
    let native_registration = solver
        .native_fun_signatures
        .iter()
        .find(|(_, registration)| registration.core_name == name);
    let Some((surface_name, registration)) = native_registration else {
        if registered.arg_sorts != actual_domain || &registered.sort != actual_range {
            return Err(native_replay_term_error(
                node,
                format!("registered datatype member `{name}` has a different signature"),
            ));
        }
        let context = solver.executor.context();
        let surface_name = context
            .symbols_iter()
            .find_map(|(surface, info)| {
                (context.symbol_identity_name(surface, info) == name).then(|| surface.clone())
            })
            .ok_or_else(|| {
                native_replay_term_error(
                    node,
                    format!("registered function identity `{name}` has no public binding"),
                )
            })?;
        let identity = FrontendFuncDeclIdentity::new(
            context.source_context_stamp(),
            registered.declaration_id().clone(),
            registered.declaration_kind(),
        );
        return Ok(FuncDecl::with_frontend_identity(
            surface_name,
            name.to_string(),
            registered.arg_sorts.clone(),
            registered.sort.clone(),
            identity,
        ));
    };
    let declared_domain = &registration.domain;
    let declared_range = &registration.range;
    if declared_domain.len() != actual_domain.len() {
        return Err(native_replay_term_error(
            node,
            format!(
                "function `{name}` expects {} arguments, got {}",
                declared_domain.len(),
                actual_domain.len()
            ),
        ));
    }
    let mut type_bindings: HashMap<String, Sort> = HashMap::default();
    let domain_matches = declared_domain
        .iter()
        .zip(actual_domain)
        .all(|(declared, actual)| {
            bind_native_replay_sort(solver, declared, actual, &mut type_bindings)
        });
    if !domain_matches
        || !bind_native_replay_sort(solver, declared_range, actual_range, &mut type_bindings)
    {
        return Err(native_replay_term_error(
            node,
            format!("function `{name}` has a different replayed signature"),
        ));
    }
    Ok(FuncDecl::with_frontend_identity(
        surface_name.clone(),
        registration.core_name.clone(),
        declared_domain
            .iter()
            .map(|sort| instantiate_native_replay_sort(sort, &type_bindings))
            .collect(),
        instantiate_native_replay_sort(declared_range, &type_bindings),
        registration.identity.clone(),
    ))
}

fn bind_native_replay_sort(
    solver: &Solver,
    declared: &Sort,
    actual: &Sort,
    bindings: &mut HashMap<String, Sort>,
) -> bool {
    match declared {
        Sort::TypeVar(name) => match bindings.get(name) {
            Some(bound) => bound == actual,
            None => {
                bindings.insert(name.clone(), actual.clone());
                true
            }
        },
        Sort::Array(declared) => match actual {
            Sort::Array(actual) => {
                bind_native_replay_sort(solver, &declared.index_sort, &actual.index_sort, bindings)
                    && bind_native_replay_sort(
                        solver,
                        &declared.element_sort,
                        &actual.element_sort,
                        bindings,
                    )
            }
            _ => false,
        },
        Sort::Seq(declared) => match actual {
            Sort::Seq(actual) => bind_native_replay_sort(solver, declared, actual, bindings),
            _ => false,
        },
        _ => solver.lower_live_sort(declared) == *actual,
    }
}

fn instantiate_native_replay_sort(sort: &Sort, bindings: &HashMap<String, Sort>) -> Sort {
    match sort {
        Sort::TypeVar(name) => bindings.get(name).cloned().unwrap_or_else(|| sort.clone()),
        Sort::Array(array) => Sort::array(
            instantiate_native_replay_sort(&array.index_sort, bindings),
            instantiate_native_replay_sort(&array.element_sort, bindings),
        ),
        Sort::Seq(element) => Sort::seq(instantiate_native_replay_sort(element, bindings)),
        _ => sort.clone(),
    }
}

fn rebuild_builtin_application(
    solver: &mut Solver,
    node: &NativeReplayTermNode,
    symbol: &Symbol,
    args: &[TermId],
) -> Result<TermId, SolverError> {
    // A serialized named head is a core identity, not surface syntax. Reusing
    // surface elaboration for a raw canonical operator after replaying a
    // same-spelled private declaration changes its meaning: e.g. builtin `=`
    // becomes the user UF named `=`. Bypass declaration lookup for canonical
    // heads and invoke the frontend's shared builtin dispatcher directly.
    if let Symbol::Named(name) = symbol {
        if ay_frontend::is_canonical_theory_operator_identity(name) {
            let rebuilt = solver
                .executor
                .context_mut_internal()
                .elaborate_canonical_theory_application(name, args)
                .map_err(|error| {
                    native_replay_term_error(
                        node.id,
                        format!(
                            "unrecognized or ill-sorted canonical application `{symbol}`: {error}"
                        ),
                    )
                })?;
            return validate_rebuilt_builtin_sort(solver, node, symbol, rebuilt);
        }
    }

    let bindings: Vec<(String, TermId)> = args
        .iter()
        .enumerate()
        .map(|(index, &arg)| (format!("native_replay_arg_{index}"), arg))
        .collect();
    let parsed_args = bindings
        .iter()
        .map(|(name, _)| ay_frontend::Term::Symbol(name.clone()))
        .collect();
    let parsed = match symbol {
        Symbol::Named(name) => ay_frontend::Term::App(name.clone(), parsed_args),
        Symbol::Indexed(name, indices) => ay_frontend::Term::IndexedApp(
            name.clone(),
            indices
                .iter()
                .map(|index| ay_frontend::Index::Numeral(index.to_string()))
                .collect(),
            parsed_args,
        ),
        _ => return unreplayable_term("future application symbol", node.id),
    };
    let rebuilt = solver
        .executor
        .context_mut_internal()
        .elaborate_surface_subterm_with_bindings(&parsed, &bindings)
        .ok_or_else(|| {
            native_replay_term_error(
                node.id,
                format!("unrecognized or ill-sorted builtin application `{symbol}`"),
            )
        })?;
    validate_rebuilt_builtin_sort(solver, node, symbol, rebuilt)
}

fn validate_rebuilt_builtin_sort(
    solver: &Solver,
    node: &NativeReplayTermNode,
    symbol: &Symbol,
    rebuilt: TermId,
) -> Result<TermId, SolverError> {
    let actual_sort = solver.terms().sort(rebuilt);
    if actual_sort != &node.sort {
        return Err(native_replay_term_error(
            node.id,
            format!(
                "builtin application `{symbol}` records result sort {}, but validation produced {actual_sort}",
                node.sort
            ),
        ));
    }
    Ok(rebuilt)
}

fn validate_rebuilt_application(
    solver: &Solver,
    node: &NativeReplayTermNode,
    expected_symbol: &Symbol,
    expected_args: &[TermId],
    rebuilt: TermId,
) -> Result<TermId, SolverError> {
    let actual_sort = solver.terms().sort(rebuilt);
    let exact_shape = matches!(
        solver.terms().get(rebuilt),
        TermData::App(actual_symbol, actual_args)
            if actual_symbol == expected_symbol && actual_args == expected_args
    );
    if actual_sort != &node.sort || !exact_shape {
        return Err(native_replay_term_error(
            node.id,
            format!(
                "registered application `{expected_symbol}` did not reconstruct its exact recorded signature"
            ),
        ));
    }
    Ok(rebuilt)
}

fn native_replay_term_error(node: TermId, message: impl Into<String>) -> SolverError {
    SolverError::InvalidArgument {
        operation: "native_replay",
        message: format!("cannot rebuild term {}: {}", node.0, message.into()),
    }
}

fn native_replay_artifact_error(message: impl Into<String>) -> SolverError {
    SolverError::InvalidArgument {
        operation: "native_replay",
        message: message.into(),
    }
}

fn native_replay_proof_error(message: impl Into<String>) -> SolverError {
    SolverError::InvalidArgument {
        operation: "native_replay_with_checked_proof",
        message: message.into(),
    }
}

fn native_replay_evidence_error(message: impl Into<String>) -> SolverError {
    SolverError::InvalidArgument {
        operation: "native_replay_for_evidence",
        message: message.into(),
    }
}

fn require_replay_sort(
    solver: &Solver,
    node: TermId,
    term: TermId,
    expected: &Sort,
    role: &str,
) -> Result<(), SolverError> {
    let actual = solver.terms().sort(term);
    if actual != expected {
        return Err(native_replay_term_error(
            node,
            format!("{role} must have sort {expected}, got {actual}"),
        ));
    }
    Ok(())
}

const NATIVE_REPLAY_BINDER_SCAN_BUDGET: usize = 100_000;

fn validate_replay_let(
    solver: &Solver,
    node: TermId,
    bindings: &[(String, TermId)],
    body: TermId,
) -> Result<(), SolverError> {
    let mut names = HashSet::default();
    if let Some((name, _)) = bindings.iter().find(|(name, _)| !names.insert(name)) {
        return Err(native_replay_term_error(
            node,
            format!("let expression repeats binding `{name}`"),
        ));
    }
    let expected: Vec<(String, Sort)> = bindings
        .iter()
        .map(|(name, value)| (name.clone(), solver.terms().sort(*value).clone()))
        .collect();
    validate_bound_name_occurrences(solver.terms(), node, &expected, &[body])?;
    Ok(())
}

fn validate_replay_quantifier(
    solver: &Solver,
    node: TermId,
    vars: &[(String, Sort)],
    body: TermId,
    triggers: &[Vec<TermId>],
) -> Result<(), SolverError> {
    require_replay_sort(solver, node, body, &Sort::Bool, "quantifier body")?;
    let mut names = HashSet::default();
    if let Some((name, _)) = vars.iter().find(|(name, _)| !names.insert(name)) {
        return Err(native_replay_term_error(
            node,
            format!("quantifier repeats binding `{name}`"),
        ));
    }

    let mut roots = Vec::with_capacity(1 + triggers.iter().map(Vec::len).sum::<usize>());
    roots.push(body);
    for multi_trigger in triggers {
        if multi_trigger.is_empty() {
            return Err(native_replay_term_error(
                node,
                "quantifier contains an empty trigger group",
            ));
        }
        for &trigger in multi_trigger {
            if !matches!(solver.terms().get(trigger), TermData::App(_, _)) {
                return Err(native_replay_term_error(
                    node,
                    "quantifier trigger is not an application",
                ));
            }
            roots.push(trigger);
        }
    }

    let expected: Vec<(String, Sort)> = vars
        .iter()
        .map(|(name, sort)| (name.clone(), sort.clone()))
        .collect();
    let coverage = validate_bound_name_occurrences(solver.terms(), node, &expected, &roots)?;
    if coverage
        .iter()
        .skip(1)
        .any(|contains_bound| !contains_bound)
    {
        return Err(native_replay_term_error(
            node,
            "quantifier trigger contains no variable bound by this quantifier",
        ));
    }
    Ok(())
}

#[derive(Default)]
struct NativeReplayShadowScope {
    parent: Option<usize>,
    names: HashSet<usize>,
}

enum NativeReplayBinderGraph<'a> {
    Live(&'a TermStore),
    Source(&'a HashMap<TermId, &'a NativeReplayTermNode>),
}

impl NativeReplayBinderGraph<'_> {
    fn node(&self, term: TermId) -> Option<(TermData, Sort)> {
        match self {
            Self::Live(terms) => Some((terms.get(term).clone(), terms.sort(term).clone())),
            Self::Source(nodes) => nodes
                .get(&term)
                .map(|node| (node.data.clone(), node.sort.clone())),
        }
    }
}

struct NativeReplayBinderScan<'a> {
    graph: NativeReplayBinderGraph<'a>,
    owner: TermId,
    expected: HashMap<String, (usize, Sort)>,
    captured: Vec<HashSet<TermId>>,
    scopes: Vec<NativeReplayShadowScope>,
    shadow_cache: HashMap<(usize, usize), bool>,
    work: usize,
}

impl<'a> NativeReplayBinderScan<'a> {
    fn new_live(
        terms: &'a TermStore,
        owner: TermId,
        bindings: &[(String, Sort)],
    ) -> Result<Self, SolverError> {
        Self::new(NativeReplayBinderGraph::Live(terms), owner, bindings)
    }

    fn new_source(
        nodes: &'a HashMap<TermId, &'a NativeReplayTermNode>,
        owner: TermId,
        bindings: &[(String, Sort)],
    ) -> Result<Self, SolverError> {
        Self::new(NativeReplayBinderGraph::Source(nodes), owner, bindings)
    }

    fn new(
        graph: NativeReplayBinderGraph<'a>,
        owner: TermId,
        bindings: &[(String, Sort)],
    ) -> Result<Self, SolverError> {
        let mut scan = Self {
            graph,
            owner,
            expected: HashMap::default(),
            captured: (0..bindings.len()).map(|_| HashSet::default()).collect(),
            scopes: Vec::new(),
            shadow_cache: HashMap::default(),
            work: 0,
        };
        for (index, (name, sort)) in bindings.iter().enumerate() {
            scan.charge()?;
            if scan
                .expected
                .insert(name.clone(), (index, sort.clone()))
                .is_some()
            {
                return Err(native_replay_term_error(
                    owner,
                    format!("binder repeats binding `{name}`"),
                ));
            }
        }
        Ok(scan)
    }

    fn charge(&mut self) -> Result<(), SolverError> {
        if self.work >= NATIVE_REPLAY_BINDER_SCAN_BUDGET {
            return Err(native_replay_term_error(
                self.owner,
                format!(
                    "binder validation exceeds {NATIVE_REPLAY_BINDER_SCAN_BUDGET} aggregate work units"
                ),
            ));
        }
        self.work += 1;
        Ok(())
    }

    /// Add one lexical scope containing only names relevant to the outer
    /// binder. The linked representation avoids cloning a binder-sized bitset
    /// at every nested quantifier; shadow lookups consume the same aggregate
    /// work budget as term traversal.
    fn extend_scope<'b>(
        &mut self,
        parent: Option<usize>,
        names: impl IntoIterator<Item = &'b str>,
    ) -> Result<Option<usize>, SolverError> {
        let mut shadowed = HashSet::default();
        for name in names {
            self.charge()?;
            if let Some(&(index, _)) = self.expected.get(name) {
                shadowed.insert(index);
            }
        }
        if shadowed.is_empty() {
            return Ok(parent);
        }
        let id = self.scopes.len();
        self.scopes.push(NativeReplayShadowScope {
            parent,
            names: shadowed,
        });
        Ok(Some(id))
    }

    fn is_shadowed(&mut self, scope: Option<usize>, target: usize) -> Result<bool, SolverError> {
        let Some(mut current) = scope else {
            return Ok(false);
        };
        if let Some(&cached) = self.shadow_cache.get(&(current, target)) {
            return Ok(cached);
        }

        let mut traversed = Vec::new();
        let result = loop {
            if let Some(&cached) = self.shadow_cache.get(&(current, target)) {
                break cached;
            }
            self.charge()?;
            traversed.push(current);
            let frame = &self.scopes[current];
            if frame.names.contains(&target) {
                break true;
            }
            let Some(parent) = frame.parent else {
                break false;
            };
            current = parent;
        };
        for scope_id in traversed {
            self.shadow_cache.insert((scope_id, target), result);
        }
        Ok(result)
    }

    /// Scan one body or trigger once against the complete binder name map.
    /// The memo key includes lexical shadow scope because a hash-consed DAG
    /// node may be reached both inside and outside a nested same-name binder.
    fn scan_root(&mut self, root: TermId) -> Result<bool, SolverError> {
        let mut found = false;
        let mut seen = HashSet::default();
        let mut pending = vec![(root, None)];

        while let Some((term, scope)) = pending.pop() {
            if !seen.insert((term, scope)) {
                continue;
            }
            self.charge()?;
            let Some((data, actual_sort)) = self.graph.node(term) else {
                return Err(native_replay_term_error(
                    self.owner,
                    format!("binder references missing term {}", term.0),
                ));
            };
            match data {
                TermData::Const(_) => {}
                TermData::Var(candidate, _) => {
                    if let Some((index, expected)) = self.expected.get(&candidate).cloned() {
                        if !self.is_shadowed(scope, index)? {
                            if actual_sort != expected {
                                return Err(native_replay_term_error(
                                    self.owner,
                                    format!(
                                        "bound variable `{candidate}` is declared as {expected} but occurs as {actual_sort}"
                                    ),
                                ));
                            }
                            self.captured[index].insert(term);
                            found = true;
                        }
                    }
                }
                TermData::App(_, args) => {
                    pending.extend(args.into_iter().map(|arg| (arg, scope)));
                }
                TermData::Not(inner) => pending.push((inner, scope)),
                TermData::Ite(condition, then_term, else_term) => {
                    pending.push((condition, scope));
                    pending.push((then_term, scope));
                    pending.push((else_term, scope));
                }
                TermData::Let(bindings, body) => {
                    pending.extend(bindings.iter().map(|(_, value)| (*value, scope)));
                    let nested =
                        self.extend_scope(scope, bindings.iter().map(|(name, _)| name.as_str()))?;
                    pending.push((body, nested));
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    let nested =
                        self.extend_scope(scope, vars.iter().map(|(name, _)| name.as_str()))?;
                    pending.push((body, nested));
                    pending.extend(
                        triggers
                            .iter()
                            .flatten()
                            .copied()
                            .map(|trigger| (trigger, nested)),
                    );
                }
                _ => {
                    return Err(native_replay_term_error(
                        self.owner,
                        "binder validation encountered an unsupported future term kind",
                    ));
                }
            }
        }
        Ok(found)
    }
}

/// Validate all unshadowed occurrences against the complete binder signature
/// in one traversal per body/trigger root, under one aggregate work envelope.
/// Returns bound-variable coverage for each root in the same order.
fn validate_bound_name_occurrences(
    terms: &TermStore,
    owner: TermId,
    expected: &[(String, Sort)],
    roots: &[TermId],
) -> Result<Vec<bool>, SolverError> {
    let mut scan = NativeReplayBinderScan::new_live(terms, owner, expected)?;
    let mut root_cache = HashMap::default();
    roots
        .iter()
        .map(|&root| {
            if let Some(&found) = root_cache.get(&root) {
                return Ok(found);
            }
            let found = scan.scan_root(root)?;
            root_cache.insert(root, found);
            Ok(found)
        })
        .collect()
}

/// Return the exact serialized Var TermIds captured by each binding, preserving
/// binding order. Capture is resolved before declaration remapping and respects
/// nested let/quantifier shadowing.
fn capture_source_bound_terms(
    nodes: &HashMap<TermId, &NativeReplayTermNode>,
    owner: TermId,
    expected: &[(String, Sort)],
    roots: &[TermId],
) -> Result<Vec<Vec<TermId>>, SolverError> {
    let mut scan = NativeReplayBinderScan::new_source(nodes, owner, expected)?;
    let mut root_cache = HashSet::default();
    for &root in roots {
        if root_cache.insert(root) {
            let _ = scan.scan_root(root)?;
        }
    }
    Ok(scan
        .captured
        .into_iter()
        .map(|captured| {
            let mut captured = captured.into_iter().collect::<Vec<_>>();
            captured.sort_by_key(|term| term.0);
            captured
        })
        .collect())
}

fn map_term(id: TermId, term_map: &HashMap<TermId, TermId>) -> Result<TermId, SolverError> {
    term_map
        .get(&id)
        .copied()
        .ok_or_else(|| SolverError::InvalidArgument {
            operation: "native_replay",
            message: format!("artifact references missing term {}", id.0),
        })
}

fn map_terms(
    ids: &[TermId],
    term_map: &HashMap<TermId, TermId>,
) -> Result<Vec<TermId>, SolverError> {
    ids.iter().map(|&id| map_term(id, term_map)).collect()
}

fn map_triggers(
    triggers: &[Vec<TermId>],
    term_map: &HashMap<TermId, TermId>,
) -> Result<Vec<Vec<TermId>>, SolverError> {
    triggers
        .iter()
        .map(|trigger| map_terms(trigger, term_map))
        .collect()
}

fn unreplayable_term(kind: &str, id: TermId) -> Result<TermId, SolverError> {
    Err(SolverError::InvalidArgument {
        operation: "native_replay",
        message: format!("cannot rebuild {kind} term {}", id.0),
    })
}

fn metadata_json(metadata: &NativeReplayMetadata) -> Value {
    json!({
        "consumer": metadata.consumer,
        "consumer_revision": metadata.consumer_revision,
        "fixture_path": metadata.fixture_path,
        "function_path": metadata.function_path,
        "source_span": metadata.source_span,
        "obligation_kind": metadata.obligation_kind,
        "notes": metadata.notes,
    })
}

fn u128_json(value: u128) -> Value {
    Value::String(value.to_string())
}

fn solver_identity_json(identity: &NativeReplaySolverIdentity) -> Value {
    json!({
        "engine": identity.engine,
        "ay_revision": identity.ay_revision,
        "ay_version": identity.ay_version,
        "solver_binary_sha256": identity.solver_binary_sha256,
    })
}

/// Lossless machine representation of every sort variant understood by this
/// replay schema. The adjacent textual fields remain for humans and legacy
/// readers; replay always prefers this structural form when present.
fn sort_json(sort: &Sort) -> Value {
    match sort {
        Sort::Bool => json!({ "kind": "bool" }),
        Sort::Int => json!({ "kind": "int" }),
        Sort::Real => json!({ "kind": "real" }),
        Sort::BitVec(sort) => json!({ "kind": "bitvec", "width": sort.width }),
        Sort::Array(sort) => json!({
            "kind": "array",
            "index": sort_json(&sort.index_sort),
            "element": sort_json(&sort.element_sort),
        }),
        Sort::String => json!({ "kind": "string" }),
        Sort::RegLan => json!({ "kind": "reglan" }),
        Sort::FloatingPoint(exponent, significand) => json!({
            "kind": "floating_point",
            "exponent": exponent,
            "significand": significand,
        }),
        Sort::Uninterpreted(name) => json!({ "kind": "uninterpreted", "name": name }),
        Sort::Datatype(datatype) => json!({
            "kind": "datatype",
            "datatype": datatype_sort_json(datatype),
        }),
        Sort::Seq(element) => json!({ "kind": "seq", "element": sort_json(element) }),
        Sort::Char => json!({ "kind": "char" }),
        Sort::FiniteDomain(name, size) => json!({
            "kind": "finite_domain",
            "name": name,
            "size": size,
        }),
        Sort::TypeVar(name) => json!({ "kind": "type_var", "name": name }),
        _ => json!({ "kind": "future", "debug": format!("{sort:?}") }),
    }
}

fn datatype_sort_json(datatype: &DatatypeSort) -> Value {
    json!({
        "name": datatype.name,
        "constructors": datatype.constructors.iter().map(|constructor| json!({
            "name": constructor.name,
            "fields": constructor.fields.iter().map(|field| json!({
                "name": field.name,
                "sort": field.sort.to_string(),
                "sort_data": sort_json(&field.sort),
            })).collect::<Vec<_>>(),
        })).collect::<Vec<_>>(),
    })
}

fn declaration_json(declaration: &NativeReplayDeclaration) -> Value {
    json!({
        "name": declaration.name,
        "core_name": declaration.core_name,
        "term": declaration.term.0,
        "sort": declaration.sort.to_string(),
        "sort_data": sort_json(&declaration.sort),
    })
}

fn function_declaration_json(declaration: &NativeReplayFunctionDeclaration) -> Value {
    json!({
        "name": declaration.name,
        "core_name": declaration.core_name,
        "domain": declaration.domain.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "domain_data": declaration.domain.iter().map(sort_json).collect::<Vec<_>>(),
        "range": declaration.range.to_string(),
        "range_data": sort_json(&declaration.range),
    })
}

fn symbol_kind_json(kind: NativeReplaySymbolKind) -> &'static str {
    match kind {
        NativeReplaySymbolKind::Uninterpreted => "uninterpreted",
        NativeReplaySymbolKind::Theory => "theory",
        NativeReplaySymbolKind::DatatypeConstructor => "datatype_constructor",
        NativeReplaySymbolKind::DatatypeSelector => "datatype_selector",
        NativeReplaySymbolKind::DatatypeTester => "datatype_tester",
    }
}

fn public_sort_json(sort: &ay_frontend::PublicSort) -> Value {
    match sort {
        ay_frontend::PublicSort::Core(sort) => {
            json!({ "kind": "core", "sort": sort_json(sort) })
        }
        ay_frontend::PublicSort::Array(index, element) => json!({
            "kind": "array",
            "index": public_sort_json(index),
            "element": public_sort_json(element),
        }),
        ay_frontend::PublicSort::Seq(element) => {
            json!({ "kind": "seq", "element": public_sort_json(element) })
        }
        ay_frontend::PublicSort::FiniteSet(element) => {
            json!({ "kind": "finite_set", "element": public_sort_json(element) })
        }
        ay_frontend::PublicSort::AmbiguousSet(element) => {
            json!({ "kind": "ambiguous_set", "element": public_sort_json(element) })
        }
        ay_frontend::PublicSort::Unknown => json!({ "kind": "unknown" }),
        _ => json!({ "kind": "future", "debug": format!("{sort:?}") }),
    }
}

fn symbol_identity_json(identity: &NativeReplaySymbolIdentity) -> Value {
    json!({
        "surface_name": identity.surface_name,
        "core_name": identity.core_name,
        "api_domain": identity.api_domain.iter().map(sort_json).collect::<Vec<_>>(),
        "api_range": sort_json(&identity.api_range),
        "public_domain": identity.public_domain.iter().map(public_sort_json).collect::<Vec<_>>(),
        "public_range": public_sort_json(&identity.public_range),
        "engine_domain": identity.engine_domain.iter().map(sort_json).collect::<Vec<_>>(),
        "engine_range": sort_json(&identity.engine_range),
        "kind": symbol_kind_json(identity.kind),
        "datatype_surface": identity.datatype_surface,
        "datatype_core": identity.datatype_core,
    })
}

fn assertion_json(assertion: &NativeReplayAssertion) -> Value {
    json!({
        "index": assertion.index,
        "term": assertion.term.0,
        "name": assertion.name,
        "scope_depth": assertion.scope_depth,
    })
}

fn term_node_json(node: &NativeReplayTermNode) -> Value {
    json!({
        "id": node.id.0,
        "sort": node.sort.to_string(),
        "sort_data": sort_json(&node.sort),
        "data": term_data_json(&node.data),
        "is_datatype_constructor": node.is_datatype_constructor,
    })
}

fn event_json(event: &NativeReplayEvent) -> Value {
    json!({
        "index": event.index,
        "scope_depth": event.scope_depth,
        "kind": event_kind_json(&event.kind),
    })
}

fn event_kind_json(kind: &NativeReplayEventKind) -> Value {
    match kind {
        NativeReplayEventKind::SetLogic { logic } => json!({
            "event": "set_logic",
            "logic": logic,
        }),
        NativeReplayEventKind::DeclareConst { name, term, sort } => json!({
            "event": "declare_const",
            "name": name,
            "term": term.0,
            "sort": sort.to_string(),
            "sort_data": sort_json(sort),
        }),
        NativeReplayEventKind::DeclareFun {
            name,
            domain,
            range,
        } => json!({
            "event": "declare_fun",
            "name": name,
            "domain": domain.iter().map(ToString::to_string).collect::<Vec<_>>(),
            "domain_data": domain.iter().map(sort_json).collect::<Vec<_>>(),
            "range": range.to_string(),
            "range_data": sort_json(range),
        }),
        NativeReplayEventKind::DeclareDatatype { datatype } => json!({
            "event": "declare_datatype",
            "name": datatype.name,
            "constructors": datatype.constructors.iter().map(|constructor| json!({
                "name": constructor.name,
                "fields": constructor.fields.iter().map(|field| json!({
                    "name": field.name,
                    "sort": field.sort.to_string(),
                    "sort_data": sort_json(&field.sort),
                })).collect::<Vec<_>>(),
            })).collect::<Vec<_>>(),
        }),
        NativeReplayEventKind::Assert { term, name } => json!({
            "event": "assert",
            "term": term.0,
            "name": name,
        }),
        NativeReplayEventKind::Push => json!({ "event": "push" }),
        NativeReplayEventKind::Pop => json!({ "event": "pop" }),
        NativeReplayEventKind::Reset => json!({ "event": "reset" }),
        NativeReplayEventKind::ResetAssertions => json!({ "event": "reset_assertions" }),
        NativeReplayEventKind::CheckSat => json!({ "event": "check_sat" }),
        NativeReplayEventKind::CheckSatAssuming { assumptions } => json!({
            "event": "check_sat_assuming",
            "assumptions": assumptions.iter().map(|term| term.0).collect::<Vec<_>>(),
        }),
    }
}

fn solve_json(solve: &NativeReplaySolveSummary) -> Value {
    json!({
        "result": solve.result,
        "unknown_reason": solve.unknown_reason,
        "unknown_phase": solve.unknown_phase,
        "unknown_progress": solve.unknown_progress.as_ref().map(|progress| json!({
            "reason": progress.reason,
            "responsible_phase": progress.responsible_phase,
            "wall_time_budget_ms": progress.wall_time_budget_ms.map(u128_json),
            "wall_time_elapsed_ms": u128_json(progress.wall_time_elapsed_ms),
        })),
        "executor_error": solve.executor_error,
        "elapsed_ms": u128_json(solve.elapsed_ms),
        "verification_level": solve.verification_level,
        "proof": {
            "available": solve.proof.available,
            "clause_count": solve.proof.clause_count,
            "complete": solve.proof.complete,
            "strictly_verified": solve.proof.strictly_verified,
            "checker_failures": solve.proof.checker_failures,
            "trust_fallbacks": solve.proof.trust_fallbacks,
        },
        "model": {
            "validated": solve.model.validated,
            "independent_checks": solve.model.independent_checks,
            "delegated_checks": solve.model.delegated_checks,
            "incomplete_checks": solve.model.incomplete_checks,
            "validation_failures": solve.model.validation_failures,
            "validation_skips": solve.model.validation_skips,
        },
        "statistics": statistics_json(&solve.statistics),
        "resources": resource_usage_json(&solve.resources),
    })
}

fn checked_replay_json(summary: &NativeReplayCheckedReplaySummary) -> Value {
    json!({
        "original_result": summary.original_result,
        "replay_result": summary.replay_result,
        "result_matches": summary.result_matches,
        "original_unknown_reason": summary.original_unknown_reason,
        "replay_unknown_reason": summary.replay_unknown_reason,
        "original_proof_status": summary.original_proof_status,
        "replay_proof_status": summary.replay_proof_status,
        "proof_status_matches": summary.proof_status_matches,
        "original_model_status": summary.original_model_status,
        "replay_model_status": summary.replay_model_status,
        "model_status_matches": summary.model_status_matches,
        "replay_executor_error": summary.replay_executor_error,
    })
}

fn statistics_json(statistics: &NativeReplayStatistics) -> Value {
    json!({
        "conflicts": statistics.conflicts,
        "decisions": statistics.decisions,
        "propagations": statistics.propagations,
        "restarts": statistics.restarts,
        "learned_clauses": statistics.learned_clauses,
        "theory_conflicts": statistics.theory_conflicts,
        "theory_propagations": statistics.theory_propagations,
        "theory_unknown_count": statistics.theory_unknown_count,
        "partial_clause_count": statistics.partial_clause_count,
        "ematching_rounds_completed": statistics.ematching_rounds_completed,
        "ematching_instances_created": statistics.ematching_instances_created,
        "refinement_count": statistics.refinement_count,
    })
}

fn resource_usage_json(resources: &NativeReplayResourceUsage) -> Value {
    json!({
        "rss_bytes": resources.rss_bytes,
        "term_bytes": resources.term_bytes,
        "term_count": resources.term_count,
        "learned_clause_count": resources.learned_clause_count,
        "limit_hit": resources.limit_hit,
    })
}

fn sha256_json(value: &Value) -> String {
    let bytes = serde_json::to_vec(value).expect("native replay JSON value must serialize");
    sha256_bytes(&bytes)
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push(hex_digit(byte >> 4));
        out.push(hex_digit(byte & 0x0f));
    }
    out
}

fn hex_digit(nibble: u8) -> char {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    HEX[usize::from(nibble)] as char
}

fn term_data_json(data: &TermData) -> Value {
    match data {
        TermData::Const(value) => json!({
            "kind": "const",
            "value": constant_json(value),
        }),
        TermData::Var(name, id) => json!({
            "kind": "var",
            "name": name,
            "var_id": id,
        }),
        TermData::App(symbol, args) => json!({
            "kind": "app",
            "symbol": symbol_json(symbol),
            "args": args.iter().map(|term| term.0).collect::<Vec<_>>(),
        }),
        TermData::Let(bindings, body) => json!({
            "kind": "let",
            "bindings": bindings
                .iter()
                .map(|(name, term)| json!({"name": name, "term": term.0}))
                .collect::<Vec<_>>(),
            "body": body.0,
        }),
        TermData::Not(inner) => json!({
            "kind": "not",
            "inner": inner.0,
        }),
        TermData::Ite(cond, then_term, else_term) => json!({
            "kind": "ite",
            "cond": cond.0,
            "then": then_term.0,
            "else": else_term.0,
        }),
        TermData::Forall(vars, body, triggers) => json!({
            "kind": "forall",
            "vars": vars_json(vars),
            "body": body.0,
            "triggers": triggers_json(triggers),
        }),
        TermData::Exists(vars, body, triggers) => json!({
            "kind": "exists",
            "vars": vars_json(vars),
            "body": body.0,
            "triggers": triggers_json(triggers),
        }),
        _ => json!({
            "kind": "future",
            "debug": format!("{data:?}"),
        }),
    }
}

fn constant_json(value: &Constant) -> Value {
    match value {
        Constant::Bool(value) => json!({
            "kind": "bool",
            "value": value,
        }),
        Constant::Int(value) => json!({
            "kind": "int",
            "value": value.to_string(),
        }),
        Constant::Rational(value) => json!({
            "kind": "rational",
            "numerator": value.0.numer().to_string(),
            "denominator": value.0.denom().to_string(),
        }),
        Constant::BitVec { value, width } => json!({
            "kind": "bitvec",
            "value": value.to_string(),
            "width": width,
        }),
        Constant::String(value) => json!({
            "kind": "string",
            "value": value,
        }),
        _ => json!({
            "kind": "future",
            "debug": format!("{value:?}"),
        }),
    }
}

fn symbol_json(symbol: &Symbol) -> Value {
    match symbol {
        Symbol::Named(name) => json!({
            "kind": "named",
            "name": name,
        }),
        Symbol::Indexed(name, indices) => json!({
            "kind": "indexed",
            "name": name,
            "indices": indices,
        }),
        _ => json!({
            "kind": "future",
            "debug": format!("{symbol:?}"),
        }),
    }
}

fn vars_json(vars: &[(String, Sort)]) -> Vec<Value> {
    vars.iter()
        .map(|(name, sort)| {
            json!({
                "name": name,
                "sort": sort.to_string(),
                "sort_data": sort_json(sort),
            })
        })
        .collect()
}

fn triggers_json(triggers: &[Vec<TermId>]) -> Vec<Vec<u32>> {
    triggers
        .iter()
        .map(|trigger| trigger.iter().map(|term| term.0).collect())
        .collect()
}

fn native_replay_artifact_from_json(value: &Value) -> Result<NativeReplayArtifact, SolverError> {
    let object = json_object(value, "artifact")?;
    let schema = required_string(object, "schema")?;
    if schema != NATIVE_REPLAY_SCHEMA {
        return Err(native_replay_json_error(format!(
            "unsupported native replay schema `{schema}`"
        )));
    }
    Ok(NativeReplayArtifact {
        schema,
        ay_revision: required_string(object, "ay_revision")?,
        ay_version: required_string(object, "ay_version")?,
        created_unix_ms: required_u128(object, "created_unix_ms")?,
        metadata: metadata_from_json(optional_field(object, "metadata")?)?,
        logic: optional_string(object, "logic")?,
        selected_route: optional_string(object, "selected_route")?,
        scope_depth: required_u32(object, "scope_depth")?,
        timeout_ms: optional_u128(object, "timeout_ms")?,
        events: required_array(object, "events")?
            .iter()
            .map(event_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        declarations: required_array(object, "declarations")?
            .iter()
            .map(declaration_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        function_declarations: required_array(object, "function_declarations")?
            .iter()
            .map(function_declaration_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        symbol_identities: match optional_field(object, "symbol_identities")? {
            Some(value) => value
                .as_array()
                .ok_or_else(|| {
                    native_replay_json_error(
                        "native replay field `symbol_identities` must be an array".to_string(),
                    )
                })?
                .iter()
                .map(symbol_identity_from_json)
                .collect::<Result<Vec<_>, SolverError>>()?,
            None => Vec::new(),
        },
        assertions: required_array(object, "assertions")?
            .iter()
            .map(assertion_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        terms: required_array(object, "terms")?
            .iter()
            .map(term_node_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        solve: optional_field(object, "solve")?
            .map(solve_summary_from_json)
            .transpose()?,
        checked_replay: optional_field(object, "checked_replay")?
            .map(checked_replay_from_json)
            .transpose()?,
        // Diagnostic JSON may retain a comparison summary, but never the
        // in-process authority proving which exact artifact was replayed.
        admission_token: None,
        panic_payload: optional_string(object, "panic_payload")?,
        unsupported_atoms: string_array(object, "unsupported_atoms")?,
        replay_gaps: string_array(object, "replay_gaps")?,
    })
}

fn metadata_from_json(value: Option<&Value>) -> Result<NativeReplayMetadata, SolverError> {
    let Some(value) = value else {
        return Ok(NativeReplayMetadata::default());
    };
    let object = json_object(value, "metadata")?;
    Ok(NativeReplayMetadata {
        consumer: optional_string(object, "consumer")?,
        consumer_revision: optional_string(object, "consumer_revision")?,
        fixture_path: optional_string(object, "fixture_path")?,
        function_path: optional_string(object, "function_path")?,
        source_span: optional_string(object, "source_span")?,
        obligation_kind: optional_string(object, "obligation_kind")?,
        notes: optional_string(object, "notes")?,
    })
}

fn declaration_from_json(value: &Value) -> Result<NativeReplayDeclaration, SolverError> {
    let object = json_object(value, "declaration")?;
    let name = required_string(object, "name")?;
    Ok(NativeReplayDeclaration {
        // v1 artifacts predating explicit private-core capture used the public
        // name as their only identity. Preserve that safe legacy case; an old
        // artifact whose node actually uses a private name fails validation.
        core_name: optional_string(object, "core_name")?.unwrap_or_else(|| name.clone()),
        name,
        term: required_term_id(object, "term")?,
        sort: sort_field(object, "sort", "sort_data")?,
    })
}

fn function_declaration_from_json(
    value: &Value,
) -> Result<NativeReplayFunctionDeclaration, SolverError> {
    let object = json_object(value, "function_declaration")?;
    let name = required_string(object, "name")?;
    Ok(NativeReplayFunctionDeclaration {
        core_name: optional_string(object, "core_name")?.unwrap_or_else(|| name.clone()),
        name,
        domain: sort_array_field(object, "domain", "domain_data")?,
        range: sort_field(object, "range", "range_data")?,
    })
}

fn symbol_kind_from_json(value: &str) -> Result<NativeReplaySymbolKind, SolverError> {
    match value {
        "uninterpreted" => Ok(NativeReplaySymbolKind::Uninterpreted),
        "theory" => Ok(NativeReplaySymbolKind::Theory),
        "datatype_constructor" => Ok(NativeReplaySymbolKind::DatatypeConstructor),
        "datatype_selector" => Ok(NativeReplaySymbolKind::DatatypeSelector),
        "datatype_tester" => Ok(NativeReplaySymbolKind::DatatypeTester),
        other => Err(native_replay_json_error(format!(
            "unsupported native replay symbol kind `{other}`"
        ))),
    }
}

fn public_sort_from_json(value: &Value) -> Result<ay_frontend::PublicSort, SolverError> {
    let object = json_object(value, "public_sort")?;
    match required_string(object, "kind")?.as_str() {
        "core" => Ok(ay_frontend::PublicSort::Core(sort_from_json(
            required_field(object, "sort")?,
        )?)),
        "array" => Ok(ay_frontend::PublicSort::Array(
            Box::new(public_sort_from_json(required_field(object, "index")?)?),
            Box::new(public_sort_from_json(required_field(object, "element")?)?),
        )),
        "seq" => Ok(ay_frontend::PublicSort::Seq(Box::new(
            public_sort_from_json(required_field(object, "element")?)?,
        ))),
        "finite_set" => Ok(ay_frontend::PublicSort::FiniteSet(Box::new(
            public_sort_from_json(required_field(object, "element")?)?,
        ))),
        "ambiguous_set" => Ok(ay_frontend::PublicSort::AmbiguousSet(Box::new(
            public_sort_from_json(required_field(object, "element")?)?,
        ))),
        "unknown" => Ok(ay_frontend::PublicSort::Unknown),
        other => Err(native_replay_json_error(format!(
            "unsupported native replay public sort kind `{other}`"
        ))),
    }
}

fn symbol_identity_from_json(value: &Value) -> Result<NativeReplaySymbolIdentity, SolverError> {
    let object = json_object(value, "symbol_identity")?;
    Ok(NativeReplaySymbolIdentity {
        surface_name: required_string(object, "surface_name")?,
        core_name: required_string(object, "core_name")?,
        api_domain: required_array(object, "api_domain")?
            .iter()
            .map(sort_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        api_range: sort_from_json(required_field(object, "api_range")?)?,
        public_domain: required_array(object, "public_domain")?
            .iter()
            .map(public_sort_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        public_range: public_sort_from_json(required_field(object, "public_range")?)?,
        engine_domain: required_array(object, "engine_domain")?
            .iter()
            .map(sort_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
        engine_range: sort_from_json(required_field(object, "engine_range")?)?,
        kind: symbol_kind_from_json(&required_string(object, "kind")?)?,
        datatype_surface: optional_string(object, "datatype_surface")?,
        datatype_core: optional_string(object, "datatype_core")?,
    })
}

fn assertion_from_json(value: &Value) -> Result<NativeReplayAssertion, SolverError> {
    let object = json_object(value, "assertion")?;
    Ok(NativeReplayAssertion {
        index: required_usize(object, "index")?,
        term: required_term_id(object, "term")?,
        name: optional_string(object, "name")?,
        scope_depth: required_usize(object, "scope_depth")?,
    })
}

fn term_node_from_json(value: &Value) -> Result<NativeReplayTermNode, SolverError> {
    let object = json_object(value, "term")?;
    Ok(NativeReplayTermNode {
        id: required_term_id(object, "id")?,
        sort: sort_field(object, "sort", "sort_data")?,
        data: term_data_from_json(required_field(object, "data")?)?,
        is_datatype_constructor: optional_bool(object, "is_datatype_constructor")?.unwrap_or(false),
    })
}

fn event_from_json(value: &Value) -> Result<NativeReplayEvent, SolverError> {
    let object = json_object(value, "event")?;
    let kind = event_kind_from_json(required_field(object, "kind")?)?;
    Ok(NativeReplayEvent {
        index: required_usize(object, "index")?,
        scope_depth: required_u32(object, "scope_depth")?,
        kind,
    })
}

fn datatype_constructor_from_json(value: &Value) -> Result<DatatypeConstructor, SolverError> {
    let object = json_object(value, "event.kind.datatype.constructor")?;
    Ok(DatatypeConstructor {
        name: required_string(object, "name")?,
        fields: required_array(object, "fields")?
            .iter()
            .map(|value| {
                let field = json_object(value, "event.kind.datatype.field")?;
                Ok(DatatypeField {
                    name: required_string(field, "name")?,
                    sort: sort_field(field, "sort", "sort_data")?,
                })
            })
            .collect::<Result<Vec<_>, SolverError>>()?,
    })
}

fn event_kind_from_json(value: &Value) -> Result<NativeReplayEventKind, SolverError> {
    let object = json_object(value, "event.kind")?;
    match required_string(object, "event")?.as_str() {
        "set_logic" => Ok(NativeReplayEventKind::SetLogic {
            logic: required_string(object, "logic")?,
        }),
        "declare_const" => Ok(NativeReplayEventKind::DeclareConst {
            name: required_string(object, "name")?,
            term: required_term_id(object, "term")?,
            sort: sort_field(object, "sort", "sort_data")?,
        }),
        "declare_fun" => Ok(NativeReplayEventKind::DeclareFun {
            name: required_string(object, "name")?,
            domain: sort_array_field(object, "domain", "domain_data")?,
            range: sort_field(object, "range", "range_data")?,
        }),
        "declare_datatype" => Ok(NativeReplayEventKind::DeclareDatatype {
            datatype: DatatypeSort {
                name: required_string(object, "name")?,
                constructors: required_array(object, "constructors")?
                    .iter()
                    .map(datatype_constructor_from_json)
                    .collect::<Result<Vec<_>, SolverError>>()?,
            },
        }),
        "assert" => Ok(NativeReplayEventKind::Assert {
            term: required_term_id(object, "term")?,
            name: optional_string(object, "name")?,
        }),
        "push" => Ok(NativeReplayEventKind::Push),
        "pop" => Ok(NativeReplayEventKind::Pop),
        "reset" => Ok(NativeReplayEventKind::Reset),
        "reset_assertions" => Ok(NativeReplayEventKind::ResetAssertions),
        "check_sat" => Ok(NativeReplayEventKind::CheckSat),
        "check_sat_assuming" => Ok(NativeReplayEventKind::CheckSatAssuming {
            assumptions: required_array(object, "assumptions")?
                .iter()
                .map(required_term_id_value)
                .collect::<Result<Vec<_>, SolverError>>()?,
        }),
        other => Err(native_replay_json_error(format!(
            "unsupported native replay event `{other}`"
        ))),
    }
}

fn solve_summary_from_json(value: &Value) -> Result<NativeReplaySolveSummary, SolverError> {
    let object = json_object(value, "solve")?;
    Ok(NativeReplaySolveSummary {
        result: required_string(object, "result")?,
        unknown_reason: optional_string(object, "unknown_reason")?,
        unknown_phase: optional_string(object, "unknown_phase")?,
        unknown_progress: optional_field(object, "unknown_progress")?
            .map(unknown_progress_from_json)
            .transpose()?,
        executor_error: optional_string(object, "executor_error")?,
        elapsed_ms: required_u128(object, "elapsed_ms")?,
        verification_level: required_string(object, "verification_level")?,
        proof: proof_summary_from_json(required_field(object, "proof")?)?,
        model: model_summary_from_json(required_field(object, "model")?)?,
        statistics: statistics_from_json(required_field(object, "statistics")?)?,
        resources: resources_from_json(required_field(object, "resources")?)?,
    })
}

fn checked_replay_from_json(
    value: &Value,
) -> Result<NativeReplayCheckedReplaySummary, SolverError> {
    let object = json_object(value, "checked_replay")?;
    Ok(NativeReplayCheckedReplaySummary {
        original_result: optional_string(object, "original_result")?,
        replay_result: required_string(object, "replay_result")?,
        result_matches: required_bool(object, "result_matches")?,
        original_unknown_reason: optional_string(object, "original_unknown_reason")?,
        replay_unknown_reason: optional_string(object, "replay_unknown_reason")?,
        original_proof_status: optional_string(object, "original_proof_status")?,
        replay_proof_status: required_string(object, "replay_proof_status")?,
        proof_status_matches: required_bool(object, "proof_status_matches")?,
        original_model_status: optional_string(object, "original_model_status")?,
        replay_model_status: required_string(object, "replay_model_status")?,
        model_status_matches: required_bool(object, "model_status_matches")?,
        replay_executor_error: optional_string(object, "replay_executor_error")?,
    })
}

fn unknown_progress_from_json(value: &Value) -> Result<NativeReplayUnknownProgress, SolverError> {
    let object = json_object(value, "unknown_progress")?;
    Ok(NativeReplayUnknownProgress {
        reason: required_string(object, "reason")?,
        responsible_phase: optional_string(object, "responsible_phase")?,
        wall_time_budget_ms: optional_u128(object, "wall_time_budget_ms")?,
        wall_time_elapsed_ms: required_u128(object, "wall_time_elapsed_ms")?,
    })
}

fn proof_summary_from_json(value: &Value) -> Result<NativeReplayProofSummary, SolverError> {
    let object = json_object(value, "proof")?;
    Ok(NativeReplayProofSummary {
        available: required_bool(object, "available")?,
        clause_count: required_u64(object, "clause_count")?,
        complete: required_bool(object, "complete")?,
        strictly_verified: optional_bool(object, "strictly_verified")?.unwrap_or(false),
        checker_failures: required_u64(object, "checker_failures")?,
        trust_fallbacks: required_u64(object, "trust_fallbacks")?,
    })
}

fn model_summary_from_json(value: &Value) -> Result<NativeReplayModelSummary, SolverError> {
    let object = json_object(value, "model")?;
    Ok(NativeReplayModelSummary {
        validated: required_bool(object, "validated")?,
        independent_checks: required_u64(object, "independent_checks")?,
        delegated_checks: required_u64(object, "delegated_checks")?,
        incomplete_checks: required_u64(object, "incomplete_checks")?,
        validation_failures: required_u64(object, "validation_failures")?,
        validation_skips: required_u64(object, "validation_skips")?,
    })
}

fn statistics_from_json(value: &Value) -> Result<NativeReplayStatistics, SolverError> {
    let object = json_object(value, "statistics")?;
    Ok(NativeReplayStatistics {
        conflicts: required_u64(object, "conflicts")?,
        decisions: required_u64(object, "decisions")?,
        propagations: required_u64(object, "propagations")?,
        restarts: required_u64(object, "restarts")?,
        learned_clauses: required_u64(object, "learned_clauses")?,
        theory_conflicts: required_u64(object, "theory_conflicts")?,
        theory_propagations: required_u64(object, "theory_propagations")?,
        theory_unknown_count: required_u64(object, "theory_unknown_count")?,
        partial_clause_count: required_u64(object, "partial_clause_count")?,
        ematching_rounds_completed: required_u64(object, "ematching_rounds_completed")?,
        ematching_instances_created: required_u64(object, "ematching_instances_created")?,
        refinement_count: required_u64(object, "refinement_count")?,
    })
}

fn resources_from_json(value: &Value) -> Result<NativeReplayResourceUsage, SolverError> {
    let object = json_object(value, "resources")?;
    Ok(NativeReplayResourceUsage {
        rss_bytes: required_usize(object, "rss_bytes")?,
        term_bytes: required_usize(object, "term_bytes")?,
        term_count: required_usize(object, "term_count")?,
        learned_clause_count: required_usize(object, "learned_clause_count")?,
        limit_hit: optional_string(object, "limit_hit")?,
    })
}

fn term_data_from_json(value: &Value) -> Result<TermData, SolverError> {
    let object = json_object(value, "term.data")?;
    match required_string(object, "kind")?.as_str() {
        "const" => Ok(TermData::Const(constant_from_json(required_field(
            object, "value",
        )?)?)),
        "var" => Ok(TermData::Var(
            required_string(object, "name")?,
            required_u32(object, "var_id")?,
        )),
        "app" => Ok(TermData::App(
            symbol_from_json(required_field(object, "symbol")?)?,
            term_id_array(object, "args")?,
        )),
        "let" => Ok(TermData::Let(
            required_array(object, "bindings")?
                .iter()
                .map(binding_from_json)
                .collect::<Result<Vec<_>, SolverError>>()?,
            required_term_id(object, "body")?,
        )),
        "not" => Ok(TermData::Not(required_term_id(object, "inner")?)),
        "ite" => Ok(TermData::Ite(
            required_term_id(object, "cond")?,
            required_term_id(object, "then")?,
            required_term_id(object, "else")?,
        )),
        "forall" => Ok(TermData::Forall(
            vars_from_json(required_array(object, "vars")?)?,
            required_term_id(object, "body")?,
            triggers_from_json(required_array(object, "triggers")?)?,
        )),
        "exists" => Ok(TermData::Exists(
            vars_from_json(required_array(object, "vars")?)?,
            required_term_id(object, "body")?,
            triggers_from_json(required_array(object, "triggers")?)?,
        )),
        other => Err(native_replay_json_error(format!(
            "unsupported native replay term kind `{other}`"
        ))),
    }
}

fn constant_from_json(value: &Value) -> Result<Constant, SolverError> {
    let object = json_object(value, "constant")?;
    match required_string(object, "kind")?.as_str() {
        "bool" => Ok(Constant::Bool(required_bool(object, "value")?)),
        "int" => Ok(Constant::Int(parse_big_int(&required_string(
            object, "value",
        )?)?)),
        "rational" => {
            let numerator = parse_big_int(&required_string(object, "numerator")?)?;
            let denominator = parse_big_int(&required_string(object, "denominator")?)?;
            Ok(Constant::Rational(RationalWrapper(BigRational::new(
                numerator,
                denominator,
            ))))
        }
        "bitvec" => Ok(Constant::BitVec {
            value: parse_big_int(&required_string(object, "value")?)?,
            width: required_u32(object, "width")?,
        }),
        "string" => Ok(Constant::String(required_string(object, "value")?)),
        other => Err(native_replay_json_error(format!(
            "unsupported native replay constant kind `{other}`"
        ))),
    }
}

fn symbol_from_json(value: &Value) -> Result<Symbol, SolverError> {
    let object = json_object(value, "symbol")?;
    match required_string(object, "kind")?.as_str() {
        "named" => Ok(Symbol::Named(required_string(object, "name")?)),
        "indexed" => Ok(Symbol::Indexed(
            required_string(object, "name")?,
            required_array(object, "indices")?
                .iter()
                .map(required_u32_value)
                .collect::<Result<Vec<_>, SolverError>>()?,
        )),
        other => Err(native_replay_json_error(format!(
            "unsupported native replay symbol kind `{other}`"
        ))),
    }
}

fn binding_from_json(value: &Value) -> Result<(String, TermId), SolverError> {
    let object = json_object(value, "binding")?;
    Ok((
        required_string(object, "name")?,
        required_term_id(object, "term")?,
    ))
}

fn vars_from_json(values: &[Value]) -> Result<Vec<(String, Sort)>, SolverError> {
    values
        .iter()
        .map(|value| {
            let object = json_object(value, "var")?;
            Ok((
                required_string(object, "name")?,
                sort_field(object, "sort", "sort_data")?,
            ))
        })
        .collect()
}

fn triggers_from_json(values: &[Value]) -> Result<Vec<Vec<TermId>>, SolverError> {
    values
        .iter()
        .map(|value| {
            let trigger = value.as_array().ok_or_else(|| {
                native_replay_json_error("native replay trigger must be an array")
            })?;
            trigger
                .iter()
                .map(required_term_id_value)
                .collect::<Result<Vec<_>, SolverError>>()
        })
        .collect()
}

fn sort_field(
    object: &serde_json::Map<String, Value>,
    legacy_key: &str,
    structural_key: &str,
) -> Result<Sort, SolverError> {
    if let Some(value) = optional_field(object, structural_key)? {
        sort_from_json(value)
    } else {
        parse_sort_text(&required_string(object, legacy_key)?)
    }
}

fn sort_array_field(
    object: &serde_json::Map<String, Value>,
    legacy_key: &str,
    structural_key: &str,
) -> Result<Vec<Sort>, SolverError> {
    if let Some(values) = optional_field(object, structural_key)? {
        values
            .as_array()
            .ok_or_else(|| {
                native_replay_json_error(format!(
                    "native replay field `{structural_key}` must be an array"
                ))
            })?
            .iter()
            .map(sort_from_json)
            .collect()
    } else {
        required_array(object, legacy_key)?
            .iter()
            .map(required_string_value)
            .map(|sort| sort.and_then(|sort| parse_sort_text(&sort)))
            .collect()
    }
}

fn sort_from_json(value: &Value) -> Result<Sort, SolverError> {
    let object = json_object(value, "sort_data")?;
    match required_string(object, "kind")?.as_str() {
        "bool" => Ok(Sort::Bool),
        "int" => Ok(Sort::Int),
        "real" => Ok(Sort::Real),
        "bitvec" => Ok(Sort::bitvec(required_u32(object, "width")?)),
        "array" => Ok(Sort::array(
            sort_from_json(required_field(object, "index")?)?,
            sort_from_json(required_field(object, "element")?)?,
        )),
        "string" => Ok(Sort::String),
        "reglan" => Ok(Sort::RegLan),
        "floating_point" => Ok(Sort::FloatingPoint(
            required_u32(object, "exponent")?,
            required_u32(object, "significand")?,
        )),
        "uninterpreted" => Ok(Sort::Uninterpreted(required_string(object, "name")?)),
        "datatype" => Ok(Sort::Datatype(datatype_sort_from_json(required_field(
            object, "datatype",
        )?)?)),
        "seq" => Ok(Sort::seq(sort_from_json(required_field(
            object, "element",
        )?)?)),
        "char" => Ok(Sort::Char),
        "finite_domain" => {
            let size = required_u64(object, "size")?;
            if size == 0 {
                return Err(native_replay_json_error(
                    "finite-domain replay sort must have positive cardinality",
                ));
            }
            Ok(Sort::FiniteDomain(required_string(object, "name")?, size))
        }
        "type_var" => Ok(Sort::TypeVar(required_string(object, "name")?)),
        other => Err(native_replay_json_error(format!(
            "unsupported native replay structural sort kind `{other}`"
        ))),
    }
}

fn datatype_sort_from_json(value: &Value) -> Result<DatatypeSort, SolverError> {
    let object = json_object(value, "datatype sort")?;
    Ok(DatatypeSort {
        name: required_string(object, "name")?,
        constructors: required_array(object, "constructors")?
            .iter()
            .map(datatype_constructor_from_json)
            .collect::<Result<Vec<_>, SolverError>>()?,
    })
}

fn term_id_array(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<Vec<TermId>, SolverError> {
    required_array(object, key)?
        .iter()
        .map(required_term_id_value)
        .collect()
}

fn string_array(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<Vec<String>, SolverError> {
    required_array(object, key)?
        .iter()
        .map(required_string_value)
        .collect()
}

fn parse_sort_text(text: &str) -> Result<Sort, SolverError> {
    let text = text.trim();
    match text {
        "Bool" => return Ok(Sort::Bool),
        "Int" => return Ok(Sort::Int),
        "Real" => return Ok(Sort::Real),
        "String" => return Ok(Sort::String),
        "RegLan" => return Ok(Sort::RegLan),
        "Char" => return Ok(Sort::Char),
        _ => {}
    }
    if let Some(width) = text
        .strip_prefix("(_ BitVec ")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        return Ok(Sort::bitvec(parse_u32_text(width, "bit-vector width")?));
    }
    if let Some(parts) = text
        .strip_prefix("(_ FloatingPoint ")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        let args = split_top_level_args(parts);
        if args.len() == 2 {
            return Ok(Sort::FloatingPoint(
                parse_u32_text(args[0], "floating-point exponent width")?,
                parse_u32_text(args[1], "floating-point significand width")?,
            ));
        }
    }
    if let Some(body) = text
        .strip_prefix("(Seq ")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        return Ok(Sort::seq(parse_sort_text(body)?));
    }
    if let Some(body) = text
        .strip_prefix("(Array ")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        let args = split_top_level_args(body);
        if args.len() == 2 {
            return Ok(Sort::array(
                parse_sort_text(args[0])?,
                parse_sort_text(args[1])?,
            ));
        }
    }
    Ok(Sort::Uninterpreted(text.to_string()))
}

fn split_top_level_args(text: &str) -> Vec<&str> {
    let mut args = Vec::new();
    let mut depth = 0i32;
    let mut start = None;
    for (index, ch) in text.char_indices() {
        match ch {
            '(' => {
                if start.is_none() {
                    start = Some(index);
                }
                depth += 1;
            }
            ')' => depth -= 1,
            ch if ch.is_whitespace() && depth == 0 => {
                if let Some(start_index) = start.take() {
                    args.push(text[start_index..index].trim());
                }
            }
            _ => {
                if start.is_none() {
                    start = Some(index);
                }
            }
        }
    }
    if let Some(start_index) = start {
        args.push(text[start_index..].trim());
    }
    args.into_iter().filter(|arg| !arg.is_empty()).collect()
}

fn parse_big_int(text: &str) -> Result<BigInt, SolverError> {
    BigInt::from_str(text).map_err(|err| {
        native_replay_json_error(format!("invalid native replay integer `{text}`: {err}"))
    })
}

fn parse_u32_text(text: &str, context: &str) -> Result<u32, SolverError> {
    text.trim().parse::<u32>().map_err(|err| {
        native_replay_json_error(format!("invalid native replay {context} `{text}`: {err}"))
    })
}

fn json_object<'a>(
    value: &'a Value,
    context: &str,
) -> Result<&'a serde_json::Map<String, Value>, SolverError> {
    value.as_object().ok_or_else(|| {
        native_replay_json_error(format!("native replay {context} must be a JSON object"))
    })
}

fn required_field<'a>(
    object: &'a serde_json::Map<String, Value>,
    key: &str,
) -> Result<&'a Value, SolverError> {
    object
        .get(key)
        .ok_or_else(|| native_replay_json_error(format!("missing native replay field `{key}`")))
}

fn optional_field<'a>(
    object: &'a serde_json::Map<String, Value>,
    key: &str,
) -> Result<Option<&'a Value>, SolverError> {
    Ok(match object.get(key) {
        Some(Value::Null) | None => None,
        Some(value) => Some(value),
    })
}

fn required_array<'a>(
    object: &'a serde_json::Map<String, Value>,
    key: &str,
) -> Result<&'a [Value], SolverError> {
    required_field(object, key)?
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| {
            native_replay_json_error(format!("native replay field `{key}` must be an array"))
        })
}

fn required_string(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<String, SolverError> {
    required_string_value(required_field(object, key)?)
}

fn optional_string(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<Option<String>, SolverError> {
    optional_field(object, key)?
        .map(required_string_value)
        .transpose()
}

fn required_string_value(value: &Value) -> Result<String, SolverError> {
    value
        .as_str()
        .map(str::to_string)
        .ok_or_else(|| native_replay_json_error("native replay value must be a string"))
}

fn required_bool(object: &serde_json::Map<String, Value>, key: &str) -> Result<bool, SolverError> {
    required_field(object, key)?.as_bool().ok_or_else(|| {
        native_replay_json_error(format!("native replay field `{key}` must be a boolean"))
    })
}

fn optional_bool(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<Option<bool>, SolverError> {
    optional_field(object, key)?
        .map(|value| {
            value.as_bool().ok_or_else(|| {
                native_replay_json_error(format!("native replay field `{key}` must be a boolean"))
            })
        })
        .transpose()
}

fn required_u64(object: &serde_json::Map<String, Value>, key: &str) -> Result<u64, SolverError> {
    required_field(object, key)?.as_u64().ok_or_else(|| {
        native_replay_json_error(format!(
            "native replay field `{key}` must be an unsigned integer"
        ))
    })
}

fn required_u32(object: &serde_json::Map<String, Value>, key: &str) -> Result<u32, SolverError> {
    u32::try_from(required_u64(object, key)?).map_err(|_| {
        native_replay_json_error(format!("native replay field `{key}` does not fit in u32"))
    })
}

fn required_usize(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<usize, SolverError> {
    usize::try_from(required_u64(object, key)?).map_err(|_| {
        native_replay_json_error(format!("native replay field `{key}` does not fit in usize"))
    })
}

fn required_u128(object: &serde_json::Map<String, Value>, key: &str) -> Result<u128, SolverError> {
    let value = required_field(object, key)?;
    if let Some(value) = value.as_u64() {
        return Ok(u128::from(value));
    }
    value
        .as_str()
        .ok_or_else(|| {
            native_replay_json_error(format!(
                "native replay field `{key}` must be an unsigned integer or decimal string"
            ))
        })?
        .parse::<u128>()
        .map_err(|error| {
            native_replay_json_error(format!(
                "native replay field `{key}` is not a valid u128: {error}"
            ))
        })
}

fn optional_u128(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<Option<u128>, SolverError> {
    optional_field(object, key)?
        .map(|_| required_u128(object, key))
        .transpose()
}

fn required_term_id(
    object: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<TermId, SolverError> {
    required_term_id_value(required_field(object, key)?)
}

fn required_term_id_value(value: &Value) -> Result<TermId, SolverError> {
    Ok(TermId(required_u32_value(value)?))
}

fn required_u32_value(value: &Value) -> Result<u32, SolverError> {
    let raw = value.as_u64().ok_or_else(|| {
        native_replay_json_error("native replay value must be an unsigned integer")
    })?;
    u32::try_from(raw)
        .map_err(|_| native_replay_json_error("native replay value does not fit in u32"))
}

fn native_replay_json_error(message: impl Into<String>) -> SolverError {
    SolverError::InvalidArgument {
        operation: "native_replay_json",
        message: message.into(),
    }
}
