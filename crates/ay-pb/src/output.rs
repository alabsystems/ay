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
mod tests {
    use super::*;

    fn render<F>(f: F) -> String
    where
        F: FnOnce(&mut PbOutputWriter<Vec<u8>>) -> io::Result<()>,
    {
        let mut writer = PbOutputWriter::new(Vec::new());
        f(&mut writer).expect("write should succeed");
        String::from_utf8(writer.into_inner()).expect("output should be utf-8")
    }

    #[test]
    fn test_status_display_matches_competition_strings() {
        assert_eq!(PbStatus::Satisfiable.to_string(), "SATISFIABLE");
        assert_eq!(PbStatus::Unsatisfiable.to_string(), "UNSATISFIABLE");
        assert_eq!(PbStatus::OptimumFound.to_string(), "OPTIMUM FOUND");
        assert_eq!(PbStatus::Unknown.to_string(), "UNKNOWN");
        assert_eq!(PbStatus::Unsupported.to_string(), "UNSUPPORTED");
    }

    #[test]
    fn test_write_comment_prefixes_each_line() {
        let out = render(|writer| writer.write_comment("first\nsecond\n"));
        assert_eq!(out, "c first\nc second\n");
    }

    #[test]
    fn test_write_status() {
        let out = render(|writer| writer.write_status(PbStatus::Unsatisfiable));
        assert_eq!(out, "s UNSATISFIABLE\n");
    }

    #[test]
    fn test_write_objective() {
        let out = render(|writer| writer.write_objective(-42));
        assert_eq!(out, "o -42\n");
    }

    #[test]
    fn test_write_solution_outputs_all_variables() {
        let out = render(|writer| writer.write_solution(&[true, false, true]));
        assert_eq!(out, "v x1 -x2 x3\n");
    }

    #[test]
    fn test_write_solution_wraps_at_80_columns() {
        let assignment = vec![true; 24];
        let out = render(|writer| writer.write_solution(&assignment));
        let lines: Vec<&str> = out.lines().collect();
        let flattened: Vec<&str> = lines
            .iter()
            .flat_map(|line| line.split_whitespace().skip(1))
            .collect();

        assert!(lines.len() > 1);
        assert!(lines.iter().all(|line| line.starts_with('v')));
        assert!(lines.iter().all(|line| line.len() <= 80));
        assert_eq!(
            flattened.join(" "),
            "x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24"
        );
    }

    #[test]
    fn test_write_full_result_orders_objective_status_and_solution() {
        let solution = PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true, false],
            objective: Some(7),
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "o 7\ns OPTIMUM FOUND\nv x1 -x2\n");
    }

    #[test]
    fn test_write_full_result_exact_keeps_positive_i64_overflow_objective() {
        let objective = i128::from(i64::MAX) + 1;
        let solution = PbExactSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true, true],
            objective: Some(objective),
        };
        let out = render(|writer| writer.write_full_result_exact(&solution));
        assert_eq!(out, format!("o {objective}\ns OPTIMUM FOUND\nv x1 x2\n"));
    }

    #[test]
    fn test_write_full_result_exact_keeps_negative_i64_overflow_objective() {
        let objective = i128::from(i64::MIN) - 1;
        let solution = PbExactSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true, true],
            objective: Some(objective),
        };
        let out = render(|writer| writer.write_full_result_exact(&solution));
        assert_eq!(out, format!("o {objective}\ns OPTIMUM FOUND\nv x1 x2\n"));
    }

    #[test]
    fn test_write_full_result_upgrades_unknown_with_partial_solution_to_sat() {
        let solution = PbSolution {
            status: PbStatus::Unknown,
            assignment: vec![false, true],
            objective: Some(11),
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "o 11\ns SATISFIABLE\nv -x1 x2\n");
    }

    #[test]
    fn test_write_full_result_skips_empty_unknown_assignment() {
        let solution = PbSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: None,
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "s UNKNOWN\n");
    }

    #[test]
    fn test_write_full_result_exact_unknown_with_objective_only_drops_final_o_line() {
        let solution = PbExactSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: Some(i128::from(i64::MAX) + 1),
        };
        let out = render(|writer| writer.write_full_result_exact(&solution));
        assert_eq!(out, "s UNKNOWN\n");
    }

    #[test]
    fn test_write_full_result_unknown_with_objective_only_drops_final_o_line() {
        let solution = PbSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: Some(13),
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "s UNKNOWN\n");
    }

    #[test]
    fn test_write_solution_empty_assignment_zero_variables() {
        let out = render(|writer| writer.write_solution(&[]));
        assert_eq!(out, "v \n");
    }

    #[test]
    fn test_write_full_result_satisfiable_zero_variables() {
        // 0-variable SAT instance: should emit s SATISFIABLE and a `v ` line.
        let solution = PbSolution {
            status: PbStatus::Satisfiable,
            assignment: Vec::new(),
            objective: None,
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "s SATISFIABLE\nv \n");
    }

    #[test]
    fn test_write_full_result_optimum_zero_variables() {
        let solution = PbSolution {
            status: PbStatus::OptimumFound,
            assignment: Vec::new(),
            objective: Some(0),
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "o 0\ns OPTIMUM FOUND\nv \n");
    }

    #[test]
    fn test_write_full_result_unsatisfiable_no_v_line() {
        let solution = PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: Vec::new(),
            objective: None,
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "s UNSATISFIABLE\n");
    }

    #[test]
    fn test_write_full_result_unsatisfiable_suppresses_stale_witness_and_objective() {
        let solution = PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: vec![true, false],
            objective: Some(17),
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "s UNSATISFIABLE\n");
    }

    #[test]
    fn test_write_full_result_unsupported_suppresses_stale_witness_and_objective() {
        let solution = PbSolution {
            status: PbStatus::Unsupported,
            assignment: vec![false, true],
            objective: Some(23),
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "s UNSUPPORTED\n");
    }

    #[test]
    fn test_write_solution_single_variable() {
        let out = render(|writer| writer.write_solution(&[true]));
        assert_eq!(out, "v x1\n");

        let out = render(|writer| writer.write_solution(&[false]));
        assert_eq!(out, "v -x1\n");
    }

    #[test]
    fn test_write_objective_large_values() {
        let out = render(|writer| writer.write_objective(i128::MAX));
        assert_eq!(out, format!("o {}\n", i128::MAX));

        let out = render(|writer| writer.write_objective(i128::MIN));
        assert_eq!(out, format!("o {}\n", i128::MIN));
    }

    #[test]
    fn test_write_objective_exact_beyond_i64() {
        let positive = i128::from(i64::MAX) + 1;
        let out = render(|writer| writer.write_objective_exact(positive));
        assert_eq!(out, format!("o {positive}\n"));

        let negative = i128::from(i64::MIN) - 1;
        let out = render(|writer| writer.write_objective_exact(negative));
        assert_eq!(out, format!("o {negative}\n"));
    }

    #[test]
    fn test_write_full_result_unknown_with_partial_objective_and_assignment_becomes_sat() {
        // SIGTERM during optimization: best-known solution with UNKNOWN status.
        let solution = PbSolution {
            status: PbStatus::Unknown,
            assignment: vec![true, false, true],
            objective: Some(42),
        };
        let out = render(|writer| writer.write_full_result(&solution));
        assert_eq!(out, "o 42\ns SATISFIABLE\nv x1 -x2 x3\n");
    }

    #[test]
    fn test_normalized_for_competition_upgrades_unknown_with_witness() {
        let solution = PbSolution {
            status: PbStatus::Unknown,
            assignment: vec![true, false],
            objective: Some(5),
        };

        assert_eq!(
            solution.normalized_for_competition(),
            PbSolution {
                status: PbStatus::Satisfiable,
                assignment: vec![true, false],
                objective: Some(5),
            }
        );
    }

    #[test]
    fn test_normalized_for_competition_strips_objective_only_unknown() {
        let solution = PbSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: Some(5),
        };

        assert_eq!(
            solution.normalized_for_competition(),
            PbSolution {
                status: PbStatus::Unknown,
                assignment: Vec::new(),
                objective: None,
            }
        );
    }

    #[test]
    fn test_normalized_for_competition_strips_non_witness_status_payloads() {
        let solution = PbSolution {
            status: PbStatus::Unsupported,
            assignment: vec![true],
            objective: Some(5),
        };

        assert_eq!(
            solution.normalized_for_competition(),
            PbSolution {
                status: PbStatus::Unsupported,
                assignment: Vec::new(),
                objective: None,
            }
        );
    }

    #[test]
    fn test_exact_solution_from_legacy_solution_preserves_competition_normalization() {
        let solution = PbSolution {
            status: PbStatus::Unknown,
            assignment: vec![true],
            objective: Some(5),
        };

        assert_eq!(
            PbExactSolution::from(&solution).normalized_for_competition(),
            PbExactSolution {
                status: PbStatus::Satisfiable,
                assignment: vec![true],
                objective: Some(5),
            }
        );
    }

    #[test]
    fn test_write_status_unsupported() {
        let out = render(|writer| writer.write_status(PbStatus::Unsupported));
        assert_eq!(out, "s UNSUPPORTED\n");
    }

    #[test]
    fn test_write_comment_empty() {
        let out = render(|writer| writer.write_comment(""));
        assert_eq!(out, "c\n");
    }
}
