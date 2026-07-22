// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended DIMACS parser with XOR support.
//!
//! Delegates header/comment/clause tokenization to [`ay_sat::dimacs_core`]
//! and handles XOR-tagged lines (`x...`) locally.

use crate::{XorConstraint, XorExtension};
use ay_sat::dimacs_core::{self, DimacsCoreError, DimacsRecord};
use ay_sat::{Literal, Variable};

// ============================================================================
// Extended DIMACS Parser with XOR Support
// ============================================================================

/// Error type for extended DIMACS parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtDimacsError {
    /// Missing problem line (p cnf ...)
    MissingProblemLine,
    /// Invalid problem line format
    InvalidProblemLine(String),
    /// Invalid literal in clause
    InvalidLiteral(String),
    /// Invalid XOR constraint
    InvalidXor(String),
    /// I/O error description
    IoError(String),
    /// Variable exceeds declared count
    VariableOutOfRange {
        /// The variable that was out of range
        var: u32,
        /// Maximum allowed variable
        max: u32,
    },
    /// Actual content would require an impractically large dense solver.
    VariableCountTooLarge {
        /// Highest one-based variable index used by the input.
        actual: usize,
        /// Maximum supported dense variable count.
        max: usize,
    },
}

impl std::fmt::Display for ExtDimacsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingProblemLine => write!(f, "Missing problem line (p cnf ...)"),
            Self::InvalidProblemLine(s) => write!(f, "Invalid problem line: {s}"),
            Self::InvalidLiteral(s) => write!(f, "Invalid literal: {s}"),
            Self::InvalidXor(s) => write!(f, "Invalid XOR constraint: {s}"),
            Self::IoError(s) => write!(f, "I/O error: {s}"),
            Self::VariableOutOfRange { var, max } => {
                write!(f, "Variable {var} out of range (max {max})")
            }
            Self::VariableCountTooLarge { actual, max } => write!(
                f,
                "actual variable count {actual} exceeds the maximum supported {max}; refusing to allocate"
            ),
        }
    }
}

impl std::error::Error for ExtDimacsError {}

impl From<DimacsCoreError> for ExtDimacsError {
    fn from(e: DimacsCoreError) -> Self {
        match e {
            DimacsCoreError::MissingHeader => Self::MissingProblemLine,
            DimacsCoreError::InvalidHeader { line_content, .. } => {
                Self::InvalidProblemLine(line_content)
            }
            DimacsCoreError::InvalidLiteral { token, .. } => Self::InvalidLiteral(token),
            DimacsCoreError::IoError(s) => Self::IoError(s),
            DimacsCoreError::VariableOutOfRange { var, max, .. } => {
                Self::VariableOutOfRange { var, max }
            }
            _ => Self::IoError(format!("{e}")),
        }
    }
}

/// Result of parsing an extended DIMACS file with XOR constraints.
///
/// The extended DIMACS format used by CryptoMiniSat adds XOR constraints
/// with the syntax `x<lit> <lit> ... 0` where:
/// - `x` prefix indicates an XOR line
/// - Positive literals contribute their variable to the XOR
/// - Negative literals contribute their variable AND flip the RHS
///
/// For example:
/// - `x1 2 3 0` means x1 XOR x2 XOR x3 = 1 (odd parity)
/// - `x-1 0` means x1 = 0 (negation of x1, so rhs flips)
/// - `x1 -2 0` means x1 XOR x2 = 0 (one negation flips rhs from default 1 to 0)
#[derive(Debug)]
pub struct ExtDimacsFormula {
    /// Number of variables declared
    pub num_vars: usize,
    /// Number of clauses declared (CNF only, not XOR)
    pub num_clauses: usize,
    /// The CNF clauses
    pub clauses: Vec<Vec<Literal>>,
    /// The XOR constraints
    pub xors: Vec<XorConstraint>,
}

impl ExtDimacsFormula {
    /// Checked variant of [`Self::into_solver_with_xor`].
    ///
    /// Public fields allow callers to construct formulas without going through
    /// the parser, so this boundary revalidates the actual variable count before
    /// allocating dense SAT state.
    pub fn try_into_solver_with_xor(
        self,
    ) -> Result<(ay_sat::Solver, Option<XorExtension>), ExtDimacsError> {
        let solver_vars = checked_actual_variable_count(&self.clauses, &self.xors)?;
        // Extract features before moving clauses into the solver.
        let features = ay_sat::SatFeatures::extract(solver_vars, &self.clauses);
        let class = ay_sat::InstanceClass::classify(&features);

        let mut solver = ay_sat::Solver::new(solver_vars);

        // Apply adaptive inprocessing adjustments via unified profile (#8149).
        let mut profile = solver.inprocessing_feature_profile();
        if ay_sat::adjust_features_for_instance(&features, &class, &mut profile) {
            solver.apply_feature_profile(&profile);
        }

        for clause in self.clauses {
            solver.add_clause(clause);
        }

        let xor_ext = if self.xors.is_empty() {
            None
        } else {
            Some(XorExtension::new(self.xors))
        };

        Ok((solver, xor_ext))
    }

    /// Create a solver with XOR extension from this formula.
    ///
    /// Applies adaptive inprocessing gating based on syntactic features
    /// of the CNF portion. This matches the adaptive gating applied by
    /// the DIMACS entry point in `ay-sat`.
    ///
    /// Returns the solver and optionally an XOR extension if there are XOR constraints.
    ///
    /// # Panics
    ///
    /// Panics before allocating if a formula constructed through the public
    /// fields exceeds the supported dense-variable limit. Call
    /// [`Self::try_into_solver_with_xor`] to handle that error explicitly.
    pub fn into_solver_with_xor(self) -> (ay_sat::Solver, Option<XorExtension>) {
        self.try_into_solver_with_xor()
            .expect("extended DIMACS formula exceeds supported solver limits")
    }

    /// Checked solve for formulas created directly through the public fields.
    pub fn try_solve(self) -> Result<ay_sat::VerifiedSatResult, ExtDimacsError> {
        let (mut solver, xor_ext) = self.try_into_solver_with_xor()?;

        Ok(match xor_ext {
            Some(mut ext) => {
                // XOR-derived lemmas are logically implied by the original
                // formula (Gauss-Jordan over GF(2)). Mark as trusted so DRAT/LRAT
                // proof emission uses TrustedTransform instead of Axiom (#4533).
                solver.set_extension_trusted_lemmas(true);
                solver.solve_with_extension(&mut ext)
            }
            None => solver.solve(),
        })
    }

    /// Solve this formula using XOR-aware solving.
    ///
    /// # Panics
    ///
    /// Panics before allocating if a directly constructed formula exceeds the
    /// supported dense-variable limit. Prefer [`Self::try_solve`] for native
    /// formulas that have not passed through [`parse_ext_dimacs`].
    pub fn solve(self) -> ay_sat::VerifiedSatResult {
        self.try_solve()
            .expect("extended DIMACS formula exceeds supported solver limits")
    }
}

/// Convert a raw i32 DIMACS literal to a 0-indexed Literal.
fn dimacs_lit_to_literal(lit: i32) -> Literal {
    let var = lit.unsigned_abs();
    let variable = Variable::new(var - 1);
    if lit > 0 {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    }
}

/// Convert raw i32 XOR values to an XorConstraint.
///
/// Each value is a signed literal: positive contributes its variable,
/// negative contributes its variable AND flips the RHS.
/// Variables are converted from 1-indexed DIMACS to 0-indexed.
fn xor_values_to_constraint(
    values: &[i32],
    max_var: u32,
) -> Result<Option<XorConstraint>, ExtDimacsError> {
    let mut vars = Vec::new();
    let mut rhs = true; // Default: odd parity (XOR = 1)

    for &lit_val in values {
        let var = lit_val.unsigned_abs();
        if var > max_var {
            return Err(ExtDimacsError::VariableOutOfRange { var, max: max_var });
        }
        // DIMACS is 1-indexed
        vars.push(var - 1);
        // Negative literal flips the RHS
        if lit_val < 0 {
            rhs = !rhs;
        }
    }

    if vars.is_empty() {
        // CryptoMiniSat extended DIMACS treats `x0` as an empty XOR record
        // and ignores it. It is not the contradictory equation 0 = 1.
        return Ok(None);
    }

    Ok(Some(XorConstraint::new(vars, rhs)))
}

/// Parse an extended DIMACS file with XOR support.
///
/// This parser handles both standard DIMACS CNF and CryptoMiniSat's XOR extension.
///
/// # XOR Syntax
///
/// XOR lines start with `x` followed by literals and terminated by `0`:
/// - `x1 2 3 0` - means x1 XOR x2 XOR x3 = 1 (default: odd parity required)
/// - `x-1 0` - means x1 = 0 (single negated var means var must be false)
/// - `x1 -2 3 0` - means x1 XOR x2 XOR x3 = 0 (one negation flips the parity)
///
/// The RHS is computed as: start with 1 (odd parity), flip for each negative literal.
///
/// # Example
///
/// ```
/// use ay_xor::parse_ext_dimacs_str;
///
/// let input = r"
/// p cnf 3 0
/// x1 2 0
/// x2 3 0
/// ";
///
/// let formula = parse_ext_dimacs_str(input).unwrap();
/// assert_eq!(formula.xors.len(), 2);
/// assert!(formula.clauses.is_empty());
/// ```
pub fn parse_ext_dimacs<R: std::io::Read>(reader: R) -> Result<ExtDimacsFormula, ExtDimacsError> {
    let (header, records) = dimacs_core::parse_dimacs_records(reader)?;
    let max_var = u32::try_from(header.num_vars).unwrap_or(u32::MAX);

    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    let mut xors: Vec<XorConstraint> = Vec::new();

    for record in records {
        match record {
            DimacsRecord::Clause(raw) => {
                // Preserve an explicit empty clause: it is an immediate CNF
                // contradiction and must reach the SAT core unchanged.
                let clause: Vec<Literal> = raw.iter().map(|&l| dimacs_lit_to_literal(l)).collect();
                clauses.push(clause);
            }
            DimacsRecord::Tagged { tag: 'x', values } => {
                if let Some(xor) = xor_values_to_constraint(&values, max_var)? {
                    xors.push(xor);
                }
            }
            DimacsRecord::Tagged { tag, .. } => {
                return Err(ExtDimacsError::InvalidLiteral(format!(
                    "unexpected tagged line '{tag}' in extended DIMACS input"
                )));
            }
            _ => {
                return Err(ExtDimacsError::InvalidLiteral(
                    "unexpected record type in extended DIMACS input".to_string(),
                ));
            }
        }
    }

    checked_actual_variable_count(&clauses, &xors)?;

    Ok(ExtDimacsFormula {
        num_vars: header.num_vars,
        num_clauses: header.num_clauses,
        clauses,
        xors,
    })
}

/// Highest one-based variable index used by either the CNF or XOR matrix.
fn checked_actual_variable_count(
    clauses: &[Vec<Literal>],
    xors: &[XorConstraint],
) -> Result<usize, ExtDimacsError> {
    let actual_u64 = clauses
        .iter()
        .flat_map(|clause| clause.iter())
        .map(|literal| u64::from(literal.variable().id()) + 1)
        .chain(
            xors.iter()
                .flat_map(|xor| xor.vars.iter())
                .map(|&variable| u64::from(variable) + 1),
        )
        .max()
        .unwrap_or(0);
    if actual_u64 > dimacs_core::MAX_DIMACS_VARS as u64 {
        return Err(ExtDimacsError::VariableCountTooLarge {
            actual: usize::try_from(actual_u64).unwrap_or(usize::MAX),
            max: dimacs_core::MAX_DIMACS_VARS,
        });
    }
    Ok(actual_u64 as usize)
}

/// Parse an extended DIMACS formula from a string.
///
/// See `parse_ext_dimacs` for format details.
pub fn parse_ext_dimacs_str(input: &str) -> Result<ExtDimacsFormula, ExtDimacsError> {
    parse_ext_dimacs(input.as_bytes())
}

/// Write an extended DIMACS formula with XOR constraints.
///
/// Outputs both CNF clauses and XOR constraints in CryptoMiniSat format.
pub fn write_ext_dimacs<W: std::io::Write>(
    writer: &mut W,
    num_vars: usize,
    clauses: &[Vec<Literal>],
    xors: &[XorConstraint],
) -> std::io::Result<()> {
    // An internally constructed empty XOR with rhs=true is the contradiction
    // 0=1. CryptoMiniSat interprets `x0` as a no-op, so serialize such rows as
    // ordinary empty CNF clauses and include them in the CNF header count.
    let empty_xor_conflicts = xors
        .iter()
        .filter(|xor| xor.vars.is_empty() && xor.rhs)
        .count();
    let cnf_clause_count = clauses
        .len()
        .checked_add(empty_xor_conflicts)
        .ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "extended DIMACS CNF clause count overflows usize",
            )
        })?;

    // Validate the entire formula before writing the header.  In particular,
    // `u32 as i32 + 1` can wrap (or panic in debug builds), and emitting a
    // variable beyond the declared header creates corrupt DIMACS.  Returning
    // `InvalidInput` with an untouched writer is deterministic and fail-closed.
    let checked_var = |zero_based: u32| -> std::io::Result<i32> {
        let one_based = usize::try_from(zero_based)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or_else(|| {
                std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "extended DIMACS variable index overflows usize",
                )
            })?;
        if one_based > num_vars {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!(
                    "extended DIMACS variable {one_based} exceeds declared variable count {num_vars}"
                ),
            ));
        }
        if one_based > dimacs_core::MAX_DIMACS_VARS {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!(
                    "extended DIMACS variable {one_based} exceeds supported maximum {}",
                    dimacs_core::MAX_DIMACS_VARS
                ),
            ));
        }
        i32::try_from(one_based).map_err(|_| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                format!("extended DIMACS variable {one_based} is not representable as i32"),
            )
        })
    };
    for clause in clauses {
        for lit in clause {
            checked_var(lit.variable().id())?;
        }
    }
    for xor in xors {
        for &var in &xor.vars {
            checked_var(var)?;
        }
    }

    writeln!(writer, "p cnf {num_vars} {cnf_clause_count}")?;

    // Write CNF clauses
    for clause in clauses {
        for lit in clause {
            // Convert back to 1-indexed DIMACS format
            let var = checked_var(lit.variable().id())?;
            let dimacs_lit = if lit.is_positive() { var } else { -var };
            write!(writer, "{dimacs_lit} ")?;
        }
        writeln!(writer, "0")?;
    }
    for _ in 0..empty_xor_conflicts {
        writeln!(writer, "0")?;
    }

    // Write XOR constraints
    for xor in xors.iter().filter(|xor| !xor.vars.is_empty()) {
        write!(writer, "x")?;
        // First variable determines base polarity
        // If rhs=true (odd parity), first var is positive
        // If rhs=false (even parity), first var is negative
        let mut first = true;
        for &var in &xor.vars {
            // Convert to 1-indexed
            let dimacs_var = checked_var(var)?;
            if first && !xor.rhs {
                // First variable negative to indicate even parity
                write!(writer, "-{dimacs_var} ")?;
            } else {
                write!(writer, "{dimacs_var} ")?;
            }
            first = false;
        }
        writeln!(writer, "0")?;
    }

    Ok(())
}

/// Solve an extended DIMACS file with XOR constraints.
///
/// Convenience function to parse and solve in one step.
pub fn solve_ext_dimacs<R: std::io::Read>(
    reader: R,
) -> Result<ay_sat::VerifiedSatResult, ExtDimacsError> {
    let formula = parse_ext_dimacs(reader)?;
    formula.try_solve()
}

/// Solve an extended DIMACS formula from a string.
pub fn solve_ext_dimacs_str(input: &str) -> Result<ay_sat::VerifiedSatResult, ExtDimacsError> {
    solve_ext_dimacs(input.as_bytes())
}
