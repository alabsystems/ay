// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native reducer/replay export for downstream consumers.

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
    FuncDecl, LimitKind, Logic, NativeReplayArtifact, NativeReplayAssertion,
    NativeReplayCheckedReplaySummary, NativeReplayDeclaration, NativeReplayEvent,
    NativeReplayEventKind, NativeReplayEvidenceManifest, NativeReplayFunctionDeclaration,
    NativeReplayMetadata, NativeReplayModelSummary, NativeReplayProofSummary,
    NativeReplayResourceUsage, NativeReplaySolveSummary, NativeReplaySolverIdentity,
    NativeReplayStatistics, NativeReplayTermNode, NativeReplayUnknownProgress, Term,
    NATIVE_REPLAY_EVIDENCE_MANIFEST_SCHEMA, NATIVE_REPLAY_SCHEMA,
};
use crate::api::{Solver, SolverError};

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
        let mut declarations: Vec<_> = self
            .var_names
            .iter()
            .filter_map(|(&term, name)| {
                self.var_sorts
                    .get(&term)
                    .cloned()
                    .map(|sort| NativeReplayDeclaration {
                        name: name.clone(),
                        term,
                        sort,
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
        let mut function_declarations =
            function_declarations_from_events(&self.native_replay_events);
        function_declarations.retain(|declaration| needed_functions.contains(&declaration.name));

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
        let mut replay_gaps = Vec::new();
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
            assertions,
            terms,
            solve: solve_summary,
            checked_replay: None,
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
        let logic = Logic::from_str(artifact.logic.as_deref().unwrap_or("ALL"))?;
        validate_native_replay_identity_tables(artifact)?;
        let mut solver = Self::try_new(logic)?;
        if let Some(timeout_ms) = artifact.timeout_ms {
            solver.set_timeout(Some(Duration::from_millis(
                timeout_ms.min(u128::from(u64::MAX)) as u64,
            )));
        }

        for datatype in datatype_declarations_from_events(&artifact.events) {
            solver.try_declare_datatype(&datatype)?;
        }
        for fun in &artifact.function_declarations {
            solver.try_declare_fun(&fun.name, &fun.domain, fun.range.clone())?;
        }

        let declarations: HashMap<_, _> = artifact
            .declarations
            .iter()
            .map(|decl| (decl.term, decl))
            .collect();
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
            let replayed = rebuild_term_node(&mut solver, node, &declarations, &term_map)?;
            let actual_sort = solver.terms().sort(replayed);
            if actual_sort != &node.sort {
                return Err(SolverError::InvalidArgument {
                    operation: "native_replay",
                    message: format!(
                        "term {} records sort {}, but reconstruction produced {actual_sort}",
                        node.id.0, node.sort
                    ),
                });
            }
            term_map.insert(node.id, replayed);
        }

        let mut assertions = artifact.assertions.clone();
        assertions.sort_by_key(|assertion| assertion.index);
        for assertion in assertions {
            let term = map_term(assertion.term, &term_map)?;
            if let Some(name) = assertion.name {
                solver.try_assert_named(Term(term), &name)?;
            } else {
                solver.try_assert_term(Term(term))?;
            }
        }

        if let Some(assumptions) = final_check_sat_assumptions(&artifact.events) {
            let assumptions = assumptions
                .iter()
                .map(|&term| map_term(term, &term_map).map(Term))
                .collect::<Result<Vec<_>, SolverError>>()?;
            Ok(solver.check_sat_assuming_with_details(&assumptions).solve)
        } else {
            Ok(solver.check_sat_with_details())
        }
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

impl NativeReplayArtifact {
    /// Attach checked replay status produced from replaying this artifact.
    #[must_use]
    pub fn with_checked_replay(mut self, replay: &crate::api::types::SolveDetails) -> Self {
        self.checked_replay = Some(checked_replay_summary_from_details(
            self.solve.as_ref(),
            replay,
        ));
        self
    }

    /// Build a fail-closed content-addressed evidence manifest for this artifact.
    #[must_use]
    pub fn evidence_manifest(&self) -> NativeReplayEvidenceManifest {
        let engine = self.selected_route.as_deref().unwrap_or("native-api");
        self.evidence_manifest_with_solver_identity(NativeReplaySolverIdentity::current_for_engine(
            engine,
        ))
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
        let checked_result = native_replay_checked_result(checked);
        let admission_rejection_reasons =
            native_replay_manifest_rejection_reasons(artifact, &solver_identity, checked);
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
        };
        manifest.manifest_sha256 = sha256_json(&manifest.to_json_body());
        manifest
    }

    /// Whether a compiler verifier backend may admit this manifest.
    #[must_use]
    pub fn admitted(&self) -> bool {
        self.admission_rejection_reasons.is_empty()
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
            "admitted": self.admitted(),
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
) -> Vec<String> {
    let mut reasons = Vec::new();
    if solver_identity.ay_revision.is_empty() || solver_identity.ay_revision == "unknown" {
        reasons.push("solver identity ay revision is unknown".to_string());
    }
    match &solver_identity.solver_binary_sha256 {
        Some(hash) if hash.len() == 64 && hash.chars().all(|ch| ch.is_ascii_hexdigit()) => {}
        Some(_) => reasons.push("solver binary sha256 is malformed".to_string()),
        None => reasons.push("solver binary sha256 is missing".to_string()),
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
    events: &[NativeReplayEvent],
) -> Vec<NativeReplayFunctionDeclaration> {
    let mut declarations = Vec::new();
    for event in events {
        if let NativeReplayEventKind::DeclareFun {
            name,
            domain,
            range,
        } = &event.kind
        {
            if declarations
                .iter()
                .any(|decl: &NativeReplayFunctionDeclaration| {
                    decl.name == *name && decl.domain == *domain && decl.range == *range
                })
            {
                continue;
            }
            declarations.push(NativeReplayFunctionDeclaration {
                name: name.clone(),
                domain: domain.clone(),
                range: range.clone(),
            });
        }
    }
    declarations
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
    if proof.available && proof.complete {
        return "checked";
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

    let mut declaration_terms = HashSet::default();
    let mut declaration_names = HashSet::default();
    for declaration in &artifact.declarations {
        if !declaration_terms.insert(declaration.term) {
            return Err(native_replay_artifact_error(format!(
                "duplicate declaration for term {}",
                declaration.term.0
            )));
        }
        if !declaration_names.insert(declaration.name.as_str()) {
            return Err(native_replay_artifact_error(format!(
                "duplicate native constant declaration name `{}`",
                declaration.name
            )));
        }
        let Some(node) = nodes.get(&declaration.term) else {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` references missing term {}",
                declaration.name, declaration.term.0
            )));
        };
        let TermData::Var(node_name, _) = &node.data else {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` targets non-variable term {}",
                declaration.name, declaration.term.0
            )));
        };
        if node_name != &declaration.name {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` disagrees with term {} variable identity `{node_name}`",
                declaration.name, declaration.term.0
            )));
        }
        if declaration.sort.as_term_sort() != node.sort {
            return Err(native_replay_artifact_error(format!(
                "declaration `{}` lowers to sort {}, but term {} records {}",
                declaration.name,
                declaration.sort.as_term_sort(),
                declaration.term.0,
                node.sort
            )));
        }
        if node.is_datatype_constructor {
            return Err(native_replay_artifact_error(format!(
                "term {} cannot be both a native constant and a datatype constructor",
                declaration.term.0
            )));
        }
    }

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
    node: &NativeReplayTermNode,
    declarations: &HashMap<TermId, &NativeReplayDeclaration>,
    term_map: &HashMap<TermId, TermId>,
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
                Ok(solver.try_declare_const(&decl.name, decl.sort.clone())?.0)
            } else if node.is_datatype_constructor {
                // Nullary datatype constructors are stored as Vars. Reuse the
                // term registered by the replayed datatype declaration so
                // constructor distinctness/exhaustiveness applies to this node.
                solver
                    .executor
                    .context()
                    .symbol_info_by_identity(name)
                    .and_then(|info| info.term)
                    .ok_or_else(|| {
                        native_replay_json_error(format!(
                            "term {} claims nullary datatype-constructor provenance for missing constructor `{name}`",
                            node.id
                        ))
                    })
            } else {
                if ay_frontend::is_reserved_symbol(name) {
                    return Err(SolverError::InvalidArgument {
                        operation: "native_replay",
                        message: format!(
                            "artifact contains undeclared variable in reserved namespace `{name}`"
                        ),
                    });
                }
                Ok(solver
                    .terms_mut()
                    .mk_fresh_named_var(name.clone(), node.sort.clone()))
            }
        }
        TermData::App(symbol, args) => {
            let mapped = map_terms(args, term_map)?;
            rebuild_application(solver, node, symbol, args, mapped)
        }
        TermData::Let(bindings, body) => {
            let mapped_bindings = bindings
                .iter()
                .map(|(name, term)| Ok((name.clone(), map_term(*term, term_map)?)))
                .collect::<Result<Vec<_>, SolverError>>()?;
            let mapped_body = map_term(*body, term_map)?;
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
            let body = map_term(*body, term_map)?;
            let triggers = map_triggers(triggers, term_map)?;
            validate_replay_quantifier(solver, node.id, vars, body, &triggers)?;
            Ok(solver
                .terms_mut()
                .mk_forall_with_triggers(vars.clone(), body, triggers))
        }
        TermData::Exists(vars, body, triggers) => {
            let body = map_term(*body, term_map)?;
            let triggers = map_triggers(triggers, term_map)?;
            validate_replay_quantifier(solver, node.id, vars, body, &triggers)?;
            Ok(solver
                .terms_mut()
                .mk_exists_with_triggers(vars.clone(), body, triggers))
        }
        _ => unreplayable_term("future term kind", node.id),
    }
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
                let is_native_function = solver.native_fun_signatures.contains_key(name);
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
                let args: Vec<Term> = mapped_args.iter().copied().map(Term).collect();
                let rebuilt = solver.try_apply(&function, &args).map_err(|error| {
                    native_replay_term_error(
                        node.id,
                        format!(
                            "registered application `{name}` does not match its declaration: {error}"
                        ),
                    )
                })?;
                return validate_rebuilt_application(solver, node, symbol, &mapped_args, rebuilt.0);
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

    let rebuilt = solver
        .try_const_array(array.index_sort.clone(), Term(*value))
        .map_err(|error| {
            native_replay_term_error(
                node.id,
                format!("cannot reconstruct `const-array`: {error}"),
            )
        })?;
    let actual_sort = solver.terms().sort(rebuilt.0);
    if actual_sort != &node.sort {
        return Err(native_replay_term_error(
            node.id,
            format!(
                "`const-array` records result sort {}, but its value reconstructs {actual_sort}",
                node.sort
            ),
        ));
    }
    Ok(rebuilt.0)
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
        .map(|(index, argument)| (format!("native_replay_function_arg_{index}"), argument.0))
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
        .context_mut()
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
    let Some((declared_domain, declared_range)) = solver.native_fun_signatures.get(name) else {
        if registered.arg_sorts != actual_domain || &registered.sort != actual_range {
            return Err(native_replay_term_error(
                node,
                format!("registered datatype member `{name}` has a different signature"),
            ));
        }
        return Ok(FuncDecl::new(
            name.to_string(),
            registered.arg_sorts.clone(),
            registered.sort.clone(),
        ));
    };
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
        .all(|(declared, actual)| bind_native_replay_sort(declared, actual, &mut type_bindings));
    if !domain_matches || !bind_native_replay_sort(declared_range, actual_range, &mut type_bindings)
    {
        return Err(native_replay_term_error(
            node,
            format!("function `{name}` has a different replayed signature"),
        ));
    }
    Ok(FuncDecl::new(
        name.to_string(),
        declared_domain
            .iter()
            .map(|sort| instantiate_native_replay_sort(sort, &type_bindings))
            .collect(),
        instantiate_native_replay_sort(declared_range, &type_bindings),
    ))
}

fn bind_native_replay_sort(
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
                bind_native_replay_sort(&declared.index_sort, &actual.index_sort, bindings)
                    && bind_native_replay_sort(
                        &declared.element_sort,
                        &actual.element_sort,
                        bindings,
                    )
            }
            _ => false,
        },
        Sort::Seq(declared) => match actual {
            Sort::Seq(actual) => bind_native_replay_sort(declared, actual, bindings),
            _ => false,
        },
        _ => declared.as_term_sort() == actual.clone(),
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
        .context_mut()
        .elaborate_surface_subterm_with_bindings(&parsed, &bindings)
        .ok_or_else(|| {
            native_replay_term_error(
                node.id,
                format!("unrecognized or ill-sorted builtin application `{symbol}`"),
            )
        })?;
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
        .map(|(name, sort)| (name.clone(), sort.as_term_sort()))
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

struct NativeReplayBinderScan<'a> {
    terms: &'a TermStore,
    owner: TermId,
    expected: HashMap<String, (usize, Sort)>,
    scopes: Vec<NativeReplayShadowScope>,
    shadow_cache: HashMap<(usize, usize), bool>,
    work: usize,
}

impl<'a> NativeReplayBinderScan<'a> {
    fn new(
        terms: &'a TermStore,
        owner: TermId,
        bindings: &[(String, Sort)],
    ) -> Result<Self, SolverError> {
        let mut scan = Self {
            terms,
            owner,
            expected: HashMap::default(),
            scopes: Vec::new(),
            shadow_cache: HashMap::default(),
            work: 0,
        };
        for (index, (name, sort)) in bindings.iter().enumerate() {
            scan.charge()?;
            scan.expected.insert(name.clone(), (index, sort.clone()));
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
            match self.terms.get(term).clone() {
                TermData::Const(_) => {}
                TermData::Var(candidate, _) => {
                    if let Some((index, expected)) = self.expected.get(&candidate).cloned() {
                        if !self.is_shadowed(scope, index)? {
                            let actual = self.terms.sort(term);
                            if actual != &expected {
                                return Err(native_replay_term_error(
                                    self.owner,
                                    format!(
                                        "bound variable `{candidate}` is declared as {expected} but occurs as {actual}"
                                    ),
                                ));
                            }
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
    let mut scan = NativeReplayBinderScan::new(terms, owner, expected)?;
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
        "term": declaration.term.0,
        "sort": declaration.sort.to_string(),
        "sort_data": sort_json(&declaration.sort),
    })
}

fn function_declaration_json(declaration: &NativeReplayFunctionDeclaration) -> Value {
    json!({
        "name": declaration.name,
        "domain": declaration.domain.iter().map(ToString::to_string).collect::<Vec<_>>(),
        "domain_data": declaration.domain.iter().map(sort_json).collect::<Vec<_>>(),
        "range": declaration.range.to_string(),
        "range_data": sort_json(&declaration.range),
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
    Ok(NativeReplayDeclaration {
        name: required_string(object, "name")?,
        term: required_term_id(object, "term")?,
        sort: sort_field(object, "sort", "sort_data")?,
    })
}

fn function_declaration_from_json(
    value: &Value,
) -> Result<NativeReplayFunctionDeclaration, SolverError> {
    let object = json_object(value, "function_declaration")?;
    Ok(NativeReplayFunctionDeclaration {
        name: required_string(object, "name")?,
        domain: sort_array_field(object, "domain", "domain_data")?,
        range: sort_field(object, "range", "range_data")?,
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
