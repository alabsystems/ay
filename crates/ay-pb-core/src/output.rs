// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fmt;
use std::io::{self, Write};

/// PB competition status codes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PbStatus {
    /// A satisfying assignment was found for a decision problem.
    Satisfiable,
    /// The instance is unsatisfiable.
    Unsatisfiable,
    /// An optimal assignment was found for an optimization problem.
    OptimumFound,
    /// The solver could not determine the final answer.
    Unknown,
    /// The solver does not support the instance.
    Unsupported,
}

impl fmt::Display for PbStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let status = match self {
            Self::Satisfiable => "SATISFIABLE",
            Self::Unsatisfiable => "UNSATISFIABLE",
            Self::OptimumFound => "OPTIMUM FOUND",
            Self::Unknown => "UNKNOWN",
            Self::Unsupported => "UNSUPPORTED",
        };
        f.write_str(status)
    }
}

/// A complete or partial PB result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbSolution {
    /// Solver status.
    pub status: PbStatus,
    /// Variable assignment indexed by `var - 1`.
    pub assignment: Vec<bool>,
    /// Objective value, if known.
    pub objective: Option<i128>,
}

/// A complete or partial PB result with an exact objective value.
///
/// This is the output-layer bridge for the staged exact-objective migration.
/// Callers should only populate objectives outside `i128` after the objective
/// evaluation, incumbent tracking, proof, and bound-search path is exact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbExactSolution {
    /// Solver status.
    pub status: PbStatus,
    /// Variable assignment indexed by `var - 1`.
    pub assignment: Vec<bool>,
    /// Objective value, if known.
    pub objective: Option<i128>,
}

impl PbSolution {
    /// Returns the competition-safe rendering of this result.
    ///
    /// Hardening rules for interrupted partial results:
    /// - a concrete witness upgrades `UNKNOWN` to `SATISFIABLE`
    /// - final non-witness statuses suppress stale assignments and objectives;
    ///   anytime `o` lines should have already been emitted explicitly
    #[must_use]
    pub fn normalized_for_competition(&self) -> Self {
        let (status, assignment, objective) =
            normalized_competition_parts(self.status, &self.assignment, self.objective);
        Self {
            status,
            assignment,
            objective,
        }
    }

    /// Converts this legacy i128-objective result into the exact output shape.
    #[must_use]
    pub fn to_exact_solution(&self) -> PbExactSolution {
        PbExactSolution::from(self)
    }
}

impl PbExactSolution {
    /// Returns the competition-safe rendering of this exact-objective result.
    ///
    /// This mirrors `PbSolution::normalized_for_competition` so exact output
    /// keeps the same interruption hardening as the legacy path.
    #[must_use]
    pub fn normalized_for_competition(&self) -> Self {
        let (status, assignment, objective) =
            normalized_competition_parts(self.status, &self.assignment, self.objective);
        Self {
            status,
            assignment,
            objective,
        }
    }
}

impl From<&PbSolution> for PbExactSolution {
    fn from(solution: &PbSolution) -> Self {
        Self {
            status: solution.status,
            assignment: solution.assignment.clone(),
            objective: solution.objective,
        }
    }
}

impl From<PbSolution> for PbExactSolution {
    fn from(solution: PbSolution) -> Self {
        Self {
            status: solution.status,
            assignment: solution.assignment,
            objective: solution.objective,
        }
    }
}

fn normalized_competition_parts<T: Copy>(
    status: PbStatus,
    assignment: &[bool],
    objective: Option<T>,
) -> (PbStatus, Vec<bool>, Option<T>) {
    if status == PbStatus::Unknown && !assignment.is_empty() {
        return (PbStatus::Satisfiable, assignment.to_vec(), objective);
    }

    if status == PbStatus::Unknown && assignment.is_empty() {
        return (PbStatus::Unknown, Vec::new(), None);
    }

    if !matches!(status, PbStatus::Satisfiable | PbStatus::OptimumFound) {
        return (status, Vec::new(), None);
    }

    (status, assignment.to_vec(), objective)
}

/// PB competition output writer.
#[derive(Debug)]
pub struct PbOutputWriter<W: Write> {
    writer: W,
}

impl<W: Write> PbOutputWriter<W> {
    /// Creates a writer wrapper.
    pub fn new(writer: W) -> Self {
        Self { writer }
    }

    /// Returns the wrapped writer.
    pub fn into_inner(self) -> W {
        self.writer
    }

    /// Writes a PB competition comment line.
    pub fn write_comment(&mut self, msg: &str) -> io::Result<()> {
        if msg.is_empty() {
            return writeln!(self.writer, "c");
        }

        for line in msg.lines() {
            if line.is_empty() {
                writeln!(self.writer, "c")?;
            } else {
                writeln!(self.writer, "c {line}")?;
            }
        }
        Ok(())
    }

    /// Writes a PB competition status line.
    pub fn write_status(&mut self, status: PbStatus) -> io::Result<()> {
        writeln!(self.writer, "s {status}")
    }

    /// Writes an objective line and flushes immediately.
    pub fn write_objective(&mut self, value: i128) -> io::Result<()> {
        self.write_objective_exact(value)
    }

    /// Writes an exact objective line and flushes immediately.
    pub fn write_objective_exact(&mut self, value: i128) -> io::Result<()> {
        writeln!(self.writer, "o {value}")?;
        self.writer.flush()
    }

    /// Writes a complete assignment using PB competition `v` lines.
    ///
    /// For non-empty assignments, variables are 1-indexed and space-separated:
    /// `v x1 -x2 x3 ...` with line wrapping at 80 columns.
    /// For empty assignments (0-variable instances), emits `v ` so the line
    /// still has the competition-required witness payload separator.
    pub fn write_solution(&mut self, assignment: &[bool]) -> io::Result<()> {
        if assignment.is_empty() {
            return writeln!(self.writer, "v ");
        }

        let mut line = String::from("v");

        for (index, value) in assignment.iter().copied().enumerate() {
            let var = index + 1;
            let lit = if value {
                format!("x{var}")
            } else {
                format!("-x{var}")
            };

            if line.len() + 1 + lit.len() > 80 && line.len() > 1 {
                writeln!(self.writer, "{line}")?;
                line.clear();
                line.push('v');
            }

            line.push(' ');
            line.push_str(&lit);
        }

        writeln!(self.writer, "{line}")
    }

    /// Writes the objective, status, and assignment in competition order.
    ///
    /// Competition output format:
    /// - `o <value>` line for objective (if present)
    /// - `s <STATUS>` line always
    /// - `v <assignment>` line(s) for SAT/OPTIMUM, and for interrupted
    ///   partial results only after they normalize to SATISFIABLE
    ///
    /// For 0-variable instances with SAT status, a `v ` line is still emitted
    /// (empty assignment is valid per the PB competition spec).
    pub fn write_full_result(&mut self, solution: &PbSolution) -> io::Result<()> {
        self.write_full_result_exact(&solution.to_exact_solution())
    }

    /// Writes an exact objective, status, and assignment in competition order.
    ///
    /// This exact-output variant is intended for callers whose full objective
    /// path is exact. Legacy callers should keep using `write_full_result`, so
    /// the existing fail-closed range guard still owns non-exact paths.
    pub fn write_full_result_exact(&mut self, solution: &PbExactSolution) -> io::Result<()> {
        let solution = solution.normalized_for_competition();

        if let Some(value) = solution.objective {
            self.write_objective_exact(value)?;
        }

        self.write_status(solution.status)?;

        // SAT/OPTIMUM must always have a v-line, even if empty for 0-variable instances.
        let needs_solution = matches!(
            solution.status,
            PbStatus::Satisfiable | PbStatus::OptimumFound
        );
        if needs_solution {
            self.write_solution(&solution.assignment)?;
        }

        self.writer.flush()
    }
}

#[cfg(test)]
mod tests;
