// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MPS / CPLEX LP format parser plus a Phase 1 MIP/LP solver driver.
//!
//! The crate provides:
//!
//! - [`parse_mps`] and [`parse_lp`] parsers that normalize either format into
//!   a shared [`Problem`] representation.
//! - [`mod@solve`] which applies a small revised simplex for the LP relaxation
//!   and depth-first branch-and-bound for integer variables.
//!
//! # Example
//!
//! ```
//! use ay_lp::{parse_lp, solve};
//!
//! let input = "\
//! Minimize
//!  x + y
//! Subject To
//!  c1: x + y >= 4
//! Bounds
//!  x >= 0
//!  y >= 0
//! End
//! ";
//! let problem = parse_lp(input).unwrap();
//! let solution = solve(&problem).unwrap();
//! assert!((solution.objective - 4.0).abs() < 1e-4);
//! ```

#![forbid(unsafe_code)]

pub mod error;
pub mod model;
mod parser;
pub mod simplex;
pub mod solve;

pub use error::LpError;
pub use model::{Constraint, Problem, RowKind, Sense, Solution, VarKind, Variable};
pub use parser::{parse_lp, parse_mps};
pub use simplex::{solve_lp_relaxation, solve_lp_relaxation_budgeted, LpRelaxation};
pub use solve::solve;

/// Detects whether `input` looks like MPS or CPLEX LP format.
///
/// Inspects the first non-comment, non-blank line. Used by the CLI when the
/// file extension is ambiguous.
#[must_use]
pub fn detect_format(input: &str) -> InputFormat {
    for raw in input.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('\\') || line.starts_with('*') {
            continue;
        }
        let upper = line.to_ascii_uppercase();
        if upper.starts_with("NAME") || upper.starts_with("ROWS") || upper.starts_with("OBJSENSE") {
            return InputFormat::Mps;
        }
        if upper.starts_with("MINIMIZE")
            || upper.starts_with("MAXIMIZE")
            || upper.starts_with("MINIMISE")
            || upper.starts_with("MAXIMISE")
            || upper == "MIN"
            || upper == "MAX"
        {
            return InputFormat::Lp;
        }
        break;
    }
    InputFormat::Lp
}

/// Enumeration of supported input formats.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum InputFormat {
    /// MPS fixed-column format (tokenized free-form).
    Mps,
    /// CPLEX LP human-readable format.
    Lp,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_format_mps() {
        assert_eq!(detect_format("NAME TRIV\nROWS\n"), InputFormat::Mps);
    }

    #[test]
    fn test_detect_format_lp() {
        assert_eq!(detect_format("Minimize\n x + y\n"), InputFormat::Lp);
    }
}
