// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Completed proof checks, distinct from merely parsed or weakened derivations.

use std::io::{self, Write};

use veripb_checker::checked_result::{CheckedStatement, StatementAssurance};

use crate::RunOutcome;

/// Default input and output-path checks selected, separate from proof rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InputAdmission {
    Strict,
    LenientHeaderCounts,
    UncheckedOutputPaths,
    LenientHeadersAndUncheckedOutputPaths,
}

/// A report exists only after parsing, checking and elaboration output complete.
#[derive(Debug)]
pub struct CheckReport {
    pub(crate) statements: Vec<CheckedStatement>,
    pub(crate) diagnostics: Vec<String>,
    pub(crate) outcome: RunOutcome,
    pub(crate) input_admission: InputAdmission,
}

impl CheckReport {
    /// The semantic statements and assurance established by this run.
    pub fn statements(&self) -> &[CheckedStatement] {
        &self.statements
    }

    /// Whether the report contains a substantive certificate with no weakened
    /// checks or unproved assertions. `NO CONCLUSION` alone is not a certificate.
    pub fn is_fully_verified(&self) -> bool {
        self.input_admission == InputAdmission::Strict
            && self.outcome == RunOutcome::Verified
            && self.statements.iter().any(CheckedStatement::is_substantive)
            && self
                .statements
                .iter()
                .all(|statement| statement.assurance() == StatementAssurance::Verified)
    }

    /// Legacy checker exit semantics, separate from certificate completeness.
    pub fn outcome(&self) -> RunOutcome {
        self.outcome
    }

    pub fn input_admission(&self) -> InputAdmission {
        self.input_admission
    }

    /// Whether an output rule actually compared the supplied output file.
    /// An IMPLICIT claim is about the checker's core set, not a named file.
    pub fn checked_output_file(&self) -> bool {
        self.statements
            .iter()
            .any(CheckedStatement::checks_output_file)
    }

    /// Write the established statements only after the whole check completed.
    /// Output errors remain errors; they are never reported as successful checks.
    pub fn write_to(&self, writer: &mut impl Write) -> io::Result<()> {
        for statement in self
            .statements
            .iter()
            .filter(|statement| statement.should_emit())
        {
            writeln!(writer, "{statement}")?;
        }
        for line in &self.diagnostics {
            writeln!(writer, "{line}")?;
        }
        writer.flush()
    }
}
