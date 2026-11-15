// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fixed-capacity, borrowed formatting for the actual decision diagnostics.

use super::*;
use std::fmt::{self, Write as _};

const OUTPUT_CAPACITY: usize = 512;

pub(in crate::solver) struct TriageLine<'a> {
    pub lit: Literal,
    pub level: u32,
    pub pass: DiagnosticPass,
    pub reason: &'a str,
}

impl fmt::Display for TriageLine<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TRIAGE_ASSIGN: lit_idx={} level={} pass={:?} reason {}",
            self.lit.index(),
            self.level,
            self.pass,
            self.reason
        )
    }
}

#[cfg(any(ay_logging, test))]
pub(crate) struct LiteralLabel {
    pub lit: Literal,
    pub level: u32,
    pub reason: &'static str,
    pub value: &'static str,
}

#[cfg(any(ay_logging, test))]
impl fmt::Display for LiteralLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}@{}{}{}",
            self.lit.to_dimacs(),
            self.level,
            self.reason,
            self.value
        )
    }
}

pub(super) struct PreparedOutput {
    bytes: [u8; OUTPUT_CAPACITY],
    len: usize,
}

impl fmt::Write for PreparedOutput {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        let end = self.len.checked_add(text.len()).ok_or(fmt::Error)?;
        let destination = self.bytes.get_mut(self.len..end).ok_or(fmt::Error)?;
        destination.copy_from_slice(text.as_bytes());
        self.len = end;
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Logging {
    Disabled,
    #[cfg(any(ay_logging, test))]
    Enabled,
}

impl PreparedOutput {
    pub(super) fn prepare(
        s: &Solver,
        lit: Literal,
        level: u32,
        owner: &CountedAdmission,
    ) -> AdmissionResult<Option<Self>> {
        let target = ay_core::captured_misc_cli_flags()
            .and_then(|flags| flags.ab_triage_var)
            .and_then(|n| usize::try_from(n).ok());
        #[cfg(ay_logging)]
        let logging = if s.log_enabled {
            Logging::Enabled
        } else {
            Logging::Disabled
        };
        #[cfg(not(ay_logging))]
        let logging = Logging::Disabled;
        Self::prepare_with(s, lit, level, target, logging, owner)
    }

    fn prepare_with(
        s: &Solver,
        lit: Literal,
        level: u32,
        target: Option<usize>,
        logging: Logging,
        owner: &CountedAdmission,
    ) -> AdmissionResult<Option<Self>> {
        let triage = target == Some(lit.variable().index() + 1);
        if !triage && matches!(logging, Logging::Disabled) {
            return Ok(None);
        }
        // At most three lines of bounded integers, enum names and constants.
        // Pay initialization, formatting and output BEFORE touching the array.
        owner.admit(3 * OUTPUT_CAPACITY, OUTPUT_CAPACITY)?;
        let mut output = Self {
            bytes: [0; OUTPUT_CAPACITY],
            len: 0,
        };
        if triage {
            writeln!(
                output,
                "{}",
                TriageLine {
                    lit,
                    level,
                    pass: s.cold.diagnostic_pass,
                    reason: "NONE"
                }
            )
            .map_err(|_| invalid(owner, "decision diagnostic exceeds fixed capacity"))?;
        }
        #[cfg(any(ay_logging, test))]
        if matches!(logging, Logging::Enabled) {
            writeln!(
                output,
                "[SAT d{}c{}] assign {} at level {} (dl={}) reason None",
                level,
                s.num_conflicts,
                lit.to_dimacs(),
                level,
                level
            )
            .map_err(|_| invalid(owner, "decision diagnostic exceeds fixed capacity"))?;
            let label = LiteralLabel {
                lit,
                level,
                reason: "+",
                value: "1",
            };
            writeln!(
                output,
                "[SAT d{}c{}] decide {} level {}",
                level, s.num_conflicts, label, level
            )
            .map_err(|_| invalid(owner, "decision diagnostic exceeds fixed capacity"))?;
        }
        Ok(Some(output))
    }

    pub(super) fn bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

#[cfg(test)]
mod tests;
