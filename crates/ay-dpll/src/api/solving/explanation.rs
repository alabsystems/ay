// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Natural-language explanation report assembly.

use crate::api::types::{
    CoreConstraintExplanation, ExplanationReport, ModelAssignmentExplanation, SatExplanation,
    SolverError, UnsatCoreSource, UnsatExplanation,
};
use crate::api::Solver;

impl Solver {
    /// Structured explanation for the last `check_sat` result.
    ///
    /// This composes existing production evidence:
    /// - SAT: structured model values plus assignment provenance.
    /// - UNSAT: named core entries plus proof-derived theory attributions when
    ///   proof data is available.
    /// - Unknown: the structured unknown reason.
    ///
    /// Returns `None` if no `check_sat` has run or if SAT model extraction
    /// fails. Use [`try_explain_last_result`](Self::try_explain_last_result)
    /// to distinguish these failure modes.
    #[must_use]
    pub fn explain_last_result(&self) -> Option<ExplanationReport> {
        self.try_explain_last_result().ok()
    }

    /// Fallible version of [`explain_last_result`](Self::explain_last_result).
    ///
    /// SAT explanations require model extraction because otherwise the report
    /// would be misleading. UNSAT explanations degrade gracefully: when
    /// annotated cores are unavailable, the report falls back to named core
    /// entries and records the missing proof attribution in diagnostics.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_explain_last_result(&self) -> Result<ExplanationReport, SolverError> {
        let result = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if result.is_sat() {
            self.explain_sat_result()
        } else if result.is_unsat() {
            Ok(self.explain_unsat_result())
        } else {
            Ok(ExplanationReport::unknown(self.reason_unknown_smtlib()))
        }
    }

    fn explain_sat_result(&self) -> Result<ExplanationReport, SolverError> {
        let model = self.try_get_model_map()?;
        let provenance = self.try_model_provenance()?;
        let mut diagnostics = Vec::new();
        let assignments = provenance
            .entries()
            .iter()
            .map(|entry| {
                let value = model.get(&entry.name).cloned();
                if value.is_none() {
                    diagnostics.push(format!(
                        "model value unavailable for declared variable `{}`",
                        entry.name
                    ));
                }
                ModelAssignmentExplanation::new(entry.name.clone(), value, entry.reason.clone())
            })
            .collect();

        Ok(ExplanationReport::sat(
            SatExplanation::new(assignments),
            diagnostics,
        ))
    }

    fn explain_unsat_result(&self) -> ExplanationReport {
        let mut diagnostics = Vec::new();
        match self.try_annotated_unsat_core() {
            Ok(core) => {
                let entries = core
                    .entries()
                    .iter()
                    .map(|entry| {
                        CoreConstraintExplanation::new(
                            entry.name.clone(),
                            entry.attributions.clone(),
                        )
                    })
                    .collect();
                ExplanationReport::unsat(
                    UnsatExplanation::new(
                        entries,
                        core.theories_involved().to_vec(),
                        UnsatCoreSource::AnnotatedCore,
                    ),
                    diagnostics,
                )
            }
            Err(annotated_err) => {
                diagnostics.push(format!("annotated unsat core unavailable: {annotated_err}"));
                match self.try_get_unsat_core() {
                    Ok(core_names) => {
                        let entries = core_names
                            .into_iter()
                            .map(|name| CoreConstraintExplanation::new(name, Vec::new()))
                            .collect();
                        ExplanationReport::unsat(
                            UnsatExplanation::new(
                                entries,
                                Vec::new(),
                                UnsatCoreSource::NamedCoreOnly,
                            ),
                            diagnostics,
                        )
                    }
                    Err(core_err) => {
                        diagnostics.push(format!("named unsat core unavailable: {core_err}"));
                        ExplanationReport::unsat(
                            UnsatExplanation::new(
                                Vec::new(),
                                Vec::new(),
                                UnsatCoreSource::Unavailable,
                            ),
                            diagnostics,
                        )
                    }
                }
            }
        }
    }
}
