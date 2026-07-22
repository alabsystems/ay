// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured natural-language explanation reports.
//!
//! These types compose the existing model-provenance and annotated-core
//! surfaces into a single production-facing report. The report is deliberately
//! diagnostic: it records what evidence was available, what was missing, and a
//! concise text rendering suitable for benchmark triage logs.

use super::{AssignmentReason, ModelValue, TheoryAttribution};

/// Structured explanation for the last solver result.
#[derive(Debug, Clone, PartialEq)]
pub struct ExplanationReport {
    kind: ExplanationKind,
    diagnostics: Vec<String>,
}

/// Result-specific explanation payload.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ExplanationKind {
    /// Explanation for a SAT result.
    Sat(SatExplanation),
    /// Explanation for an UNSAT result.
    Unsat(UnsatExplanation),
    /// Explanation for an Unknown result.
    Unknown(UnknownExplanation),
}

/// SAT explanation based on model values and assignment provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatExplanation {
    assignments: Vec<ModelAssignmentExplanation>,
}

/// Explanation for one model assignment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelAssignmentExplanation {
    name: String,
    value: Option<ModelValue>,
    reason: AssignmentReason,
}

/// UNSAT explanation based on named core entries and optional theory
/// attributions.
#[derive(Debug, Clone, PartialEq)]
pub struct UnsatExplanation {
    core: Vec<CoreConstraintExplanation>,
    theories_involved: Vec<String>,
    core_source: UnsatCoreSource,
}

/// Where the UNSAT-core portion of an explanation came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnsatCoreSource {
    /// Named core plus proof-derived theory attributions were available.
    AnnotatedCore,
    /// Named core was available, but proof-derived attributions were not.
    NamedCoreOnly,
    /// No named core was available for this UNSAT result.
    Unavailable,
}

/// Explanation for one named constraint in an UNSAT core.
#[derive(Debug, Clone, PartialEq)]
pub struct CoreConstraintExplanation {
    name: String,
    attributions: Vec<TheoryAttribution>,
}

/// Explanation for an Unknown result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownExplanation {
    reason: Option<String>,
}

impl ExplanationReport {
    pub(crate) fn sat(explanation: SatExplanation, diagnostics: Vec<String>) -> Self {
        Self {
            kind: ExplanationKind::Sat(explanation),
            diagnostics,
        }
    }

    pub(crate) fn unsat(explanation: UnsatExplanation, diagnostics: Vec<String>) -> Self {
        Self {
            kind: ExplanationKind::Unsat(explanation),
            diagnostics,
        }
    }

    pub(crate) fn unknown(reason: Option<String>) -> Self {
        Self {
            kind: ExplanationKind::Unknown(UnknownExplanation { reason }),
            diagnostics: Vec::new(),
        }
    }

    /// Result-specific explanation payload.
    #[must_use]
    pub fn kind(&self) -> &ExplanationKind {
        &self.kind
    }

    /// Diagnostics about missing optional evidence.
    ///
    /// Examples include unavailable proof-attribution data for an UNSAT core or
    /// a model variable that could not be evaluated through the structured
    /// model map.
    #[must_use]
    pub fn diagnostics(&self) -> &[String] {
        &self.diagnostics
    }

    /// Return the SAT payload, if this explains a SAT result.
    #[must_use]
    pub fn sat_explanation(&self) -> Option<&SatExplanation> {
        match &self.kind {
            ExplanationKind::Sat(explanation) => Some(explanation),
            _ => None,
        }
    }

    /// Return the UNSAT payload, if this explains an UNSAT result.
    #[must_use]
    pub fn unsat_explanation(&self) -> Option<&UnsatExplanation> {
        match &self.kind {
            ExplanationKind::Unsat(explanation) => Some(explanation),
            _ => None,
        }
    }

    /// Return the Unknown payload, if this explains an Unknown result.
    #[must_use]
    pub fn unknown_explanation(&self) -> Option<&UnknownExplanation> {
        match &self.kind {
            ExplanationKind::Unknown(explanation) => Some(explanation),
            _ => None,
        }
    }

    /// Render a deterministic plain-text report.
    ///
    /// This is intended for benchmark logs, issue comments, and diagnostic
    /// bundles where a stable, grep-friendly text format is more useful than
    /// prose paragraphs.
    #[must_use]
    pub fn render_text(&self) -> String {
        let mut out = String::new();
        match &self.kind {
            ExplanationKind::Sat(explanation) => explanation.render_into(&mut out),
            ExplanationKind::Unsat(explanation) => explanation.render_into(&mut out),
            ExplanationKind::Unknown(explanation) => explanation.render_into(&mut out),
        }
        if !self.diagnostics.is_empty() {
            out.push_str("Diagnostics:\n");
            for diagnostic in &self.diagnostics {
                out.push_str("  - ");
                out.push_str(diagnostic);
                out.push('\n');
            }
        }
        out
    }
}

impl std::fmt::Display for ExplanationReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.render_text())
    }
}

impl SatExplanation {
    pub(crate) fn new(assignments: Vec<ModelAssignmentExplanation>) -> Self {
        Self { assignments }
    }

    /// Model assignments with provenance.
    #[must_use]
    pub fn assignments(&self) -> &[ModelAssignmentExplanation] {
        &self.assignments
    }

    /// Number of assignments whose values were introduced as defaults.
    #[must_use]
    pub fn default_assignment_count(&self) -> usize {
        self.assignments
            .iter()
            .filter(|assignment| matches!(assignment.reason, AssignmentReason::Default))
            .count()
    }

    /// Number of assignments with non-default provenance.
    #[must_use]
    pub fn explained_assignment_count(&self) -> usize {
        self.assignments.len() - self.default_assignment_count()
    }

    fn render_into(&self, out: &mut String) {
        out.push_str("SAT explanation:\n");
        out.push_str(&format!(
            "  {} assignment(s), {} non-default, {} default/unconstrained\n",
            self.assignments.len(),
            self.explained_assignment_count(),
            self.default_assignment_count(),
        ));
        if self.assignments.is_empty() {
            out.push_str("  Model has no declared-variable assignments.\n");
            return;
        }
        out.push_str("Assignments:\n");
        for assignment in &self.assignments {
            out.push_str("  - ");
            assignment.render_into(out);
            out.push('\n');
        }
    }
}

impl ModelAssignmentExplanation {
    pub(crate) fn new(name: String, value: Option<ModelValue>, reason: AssignmentReason) -> Self {
        Self {
            name,
            value,
            reason,
        }
    }

    /// Declared variable name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Model value for the variable, when structured value extraction
    /// succeeded.
    #[must_use]
    pub fn value(&self) -> Option<&ModelValue> {
        self.value.as_ref()
    }

    /// Why the solver assigned this value.
    #[must_use]
    pub fn reason(&self) -> &AssignmentReason {
        &self.reason
    }

    fn render_into(&self, out: &mut String) {
        out.push_str(&self.name);
        match &self.value {
            Some(value) => {
                out.push_str(" = ");
                out.push_str(&value.to_string());
            }
            None => out.push_str(" = <value unavailable>"),
        }
        out.push_str(": ");
        out.push_str(&assignment_reason_sentence(&self.reason));
    }
}

impl UnsatExplanation {
    pub(crate) fn new(
        core: Vec<CoreConstraintExplanation>,
        theories_involved: Vec<String>,
        core_source: UnsatCoreSource,
    ) -> Self {
        Self {
            core,
            theories_involved,
            core_source,
        }
    }

    /// Named core constraints.
    #[must_use]
    pub fn core(&self) -> &[CoreConstraintExplanation] {
        &self.core
    }

    /// Theory names observed in proof-derived attributions.
    #[must_use]
    pub fn theories_involved(&self) -> &[String] {
        &self.theories_involved
    }

    /// Source of core evidence used in this explanation.
    #[must_use]
    pub fn core_source(&self) -> UnsatCoreSource {
        self.core_source
    }

    fn render_into(&self, out: &mut String) {
        out.push_str("UNSAT explanation:\n");
        out.push_str(&format!(
            "  Core evidence: {}\n",
            self.core_source.description()
        ));
        if self.theories_involved.is_empty() {
            out.push_str("  Theories involved: <not available>\n");
        } else {
            out.push_str("  Theories involved: ");
            out.push_str(&self.theories_involved.join(", "));
            out.push('\n');
        }
        if self.core.is_empty() {
            out.push_str("Core constraints: <not available>\n");
            return;
        }
        out.push_str("Core constraints:\n");
        for constraint in &self.core {
            out.push_str("  - ");
            constraint.render_into(out);
            out.push('\n');
        }
    }
}

impl UnsatCoreSource {
    fn description(self) -> &'static str {
        match self {
            Self::AnnotatedCore => "named core with proof-derived theory attribution",
            Self::NamedCoreOnly => "named core without proof-derived theory attribution",
            Self::Unavailable => "no named core available",
        }
    }
}

impl CoreConstraintExplanation {
    pub(crate) fn new(name: String, attributions: Vec<TheoryAttribution>) -> Self {
        Self { name, attributions }
    }

    /// Assertion name from the UNSAT core.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Theory/proof attributions for this core constraint.
    #[must_use]
    pub fn attributions(&self) -> &[TheoryAttribution] {
        &self.attributions
    }

    fn render_into(&self, out: &mut String) {
        out.push_str(&self.name);
        if self.attributions.is_empty() {
            out.push_str(": no theory attribution available");
            return;
        }
        out.push_str(": ");
        for (idx, attribution) in self.attributions.iter().enumerate() {
            if idx > 0 {
                out.push_str("; ");
            }
            out.push_str(&theory_attribution_sentence(attribution));
        }
    }
}

impl UnknownExplanation {
    /// Structured Unknown reason rendered as an SMT-LIB-compatible string when
    /// available.
    #[must_use]
    pub fn reason(&self) -> Option<&str> {
        self.reason.as_deref()
    }

    fn render_into(&self, out: &mut String) {
        out.push_str("Unknown explanation:\n");
        match &self.reason {
            Some(reason) => {
                out.push_str("  Reason: ");
                out.push_str(reason);
                out.push('\n');
            }
            None => out.push_str("  Reason: <not available>\n"),
        }
    }
}

fn assignment_reason_sentence(reason: &AssignmentReason) -> String {
    match reason {
        AssignmentReason::Decision { level } => {
            format!("chosen by CDCL decision at level {level}")
        }
        AssignmentReason::Propagation { antecedent_terms } => format!(
            "forced by propagation from {} antecedent term(s)",
            antecedent_terms.len()
        ),
        AssignmentReason::Default => "default value for an unconstrained variable".to_string(),
    }
}

fn theory_attribution_sentence(attribution: &TheoryAttribution) -> String {
    match attribution {
        TheoryAttribution::Farkas { coefficients } => format!(
            "linear arithmetic Farkas certificate with {} coefficient(s)",
            coefficients.len()
        ),
        TheoryAttribution::LiaGeneric {
            coefficients,
            lia_kind,
        } => match coefficients {
            Some(coefficients) => format!(
                "integer arithmetic {lia_kind} certificate with {} coefficient(s)",
                coefficients.len()
            ),
            None => format!("integer arithmetic {lia_kind} certificate"),
        },
        TheoryAttribution::EufTransitive { chain } => {
            format!("EUF transitivity chain with {} step(s)", chain.len())
        }
        TheoryAttribution::EufCongruent { chain } => {
            format!("EUF congruence chain with {} step(s)", chain.len())
        }
        TheoryAttribution::BvBitBlast => "bit-vector bit-blasting lemma".to_string(),
        TheoryAttribution::StringAxiom => "string-theory axiom".to_string(),
        TheoryAttribution::DatatypeAxiom => "datatype axiom".to_string(),
        TheoryAttribution::QuantifierInstantiation {
            substitution,
            method,
            ..
        } => format!(
            "quantifier instantiation by {method} with {} binding(s)",
            substitution.len()
        ),
        TheoryAttribution::Generic { theory } => format!("{theory} theory lemma"),
    }
}
