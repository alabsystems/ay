// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_chc::engines::ExternalInvariantValidationOwner;
use serde::Serialize;

use super::{capture, chc_error, R34Archive, R34Witness};
use crate::{BenchError, Result};

mod reconstruction;

/// Every blocker withholds witness execution and any source-level verdict.
#[derive(Debug, PartialEq, Eq, Serialize)]
pub enum R34WitnessBlocker {
    MissingOriginalRemainingBudget,
    MissingAggregatePreparation,
    MissingPredecessorFactRecipe,
    IdentityMigration { captured: String, current: String },
    FormulaDebugIdentity { captured: String, current: String },
    OwnerRefused { observed: String },
    ReconstructionError { reason: String },
}

#[derive(Debug, Serialize)]
pub struct R34WitnessBinding {
    pub case: R34Witness,
    pub sequence: u64,
    pub clause_index: u64,
    pub archive_sha256: String,
    pub source_sha256: String,
    pub original_query_sha256: String,
    pub original_result: String,
    pub current_query_schema: Option<String>,
    pub current_query_sha256: Option<String>,
    pub datatype_definitions: usize,
    /// Exact aggregate source-fact indices, in body-premise order. No solver
    /// or inferred reachability is used to select this reconstruction recipe.
    pub predecessor_fact_indices: Vec<usize>,
    /// Complete reconstructed query/registry equals the authenticated capture,
    /// either directly or via the shared exact historical-v1 serializer.
    pub historical_query_authenticated: bool,
    /// AY's qualified production renderer, NEVER ChcExpr Display-as-SMT.
    /// This expression alone is not a standalone declared SMT script.
    pub qualified_expression: Option<String>,
    pub captured_smtlib_sha256: Option<String>,
    pub blockers: Vec<R34WitnessBlocker>,
    /// No original witness grant was captured. Binding never runs a solver.
    pub solver_invoked: bool,
    pub promotable_for_ask_closure: bool,
}

impl R34Archive {
    /// Reconstruct under an ALREADY captured original owner; no grant is made.
    /// The archive has no per-invocation remaining witness wall/work allowance.
    /// Therefore even a perfectly bound formula is NOT executed. Its missing
    /// record must be recaptured by the consumer, not supplied as a guessed cap.
    pub fn inspect_witness(
        &self,
        case: R34Witness,
        owner: &ExternalInvariantValidationOwner,
    ) -> Result<R34WitnessBinding> {
        let witness = self
            .capture
            .witnesses
            .get(case.index())
            .ok_or_else(|| BenchError::msg("R34 witness identity missing"))?;
        let source = self
            .capture
            .sources
            .get(&witness.source)
            .ok_or_else(|| BenchError::msg("R34 witness source missing"))?;
        let mut binding = initial(self, case, witness, source)?;
        let attempt = owner.with_resources(|| {
            reconstruction::reconstruct(self, witness, source, &mut binding, &mut || {
                owner.check().is_none()
            })
            .map_err(chc_error)
        });
        match attempt {
            Err(error) => binding
                .blockers
                .push(R34WitnessBlocker::ReconstructionError {
                    reason: error.to_string(),
                }),
            Ok(Err(kind)) => binding.blockers.push(R34WitnessBlocker::OwnerRefused {
                observed: format!("{kind:?}"),
            }),
            Ok(Ok(())) => {
                if let Some(kind) = owner.check() {
                    binding.blockers.push(R34WitnessBlocker::OwnerRefused {
                        observed: format!("{kind:?}"),
                    });
                }
            }
        }
        Ok(binding)
    }
}

fn initial(
    archive: &R34Archive,
    case: R34Witness,
    witness: &capture::Witness,
    source: &capture::Source,
) -> Result<R34WitnessBinding> {
    // There is deliberately no caller-settable "budget supplied" bypass.
    if witness.remaining_budget_recorded {
        return Err(BenchError::msg(
            "R34 capture changed: original budget schema requires review",
        ));
    }
    Ok(R34WitnessBinding {
        case,
        sequence: capture::number(&witness.record, "seq")?,
        clause_index: capture::number(&witness.record, "clause_index")?,
        archive_sha256: archive.capture.archive.sha256.clone(),
        source_sha256: capture::string(&source.source, "sha256")?.to_owned(),
        original_query_sha256: capture::string(
            &witness.record["constraint_query"],
            "normalized_input_sha256",
        )?
        .to_owned(),
        original_result: capture::string(&witness.record, "result")?.to_owned(),
        current_query_schema: None,
        current_query_sha256: None,
        datatype_definitions: 0,
        predecessor_fact_indices: Vec::new(),
        historical_query_authenticated: false,
        qualified_expression: None,
        captured_smtlib_sha256: witness.record["smtlib"]["sha256"]
            .as_str()
            .map(str::to_owned),
        blockers: vec![R34WitnessBlocker::MissingOriginalRemainingBudget],
        solver_invoked: false,
        promotable_for_ask_closure: false,
    })
}
