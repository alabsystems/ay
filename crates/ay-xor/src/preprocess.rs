// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! XOR preprocessing and convenience solve functions.

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_sat::{Literal, PreparedExtension, Solver, Variable};

use crate::extension::XorExtension;
use crate::finder::XorFinder;
use crate::VarId;

// ---------------------------------------------------------------------------
// XOR density heuristic for Gaussian elimination enablement (#7928)
// ---------------------------------------------------------------------------

/// XOR density threshold: enable Gaussian elimination when at least 5% (1/20)
/// of clauses are consumed by XOR extraction. The old 512-clause hard limit
/// prevented XOR GE from firing on large crypto benchmarks (asconhash, BV
/// encodings) where XOR density is typically 10-50%. A 5% floor catches real
/// crypto instances while still filtering out noise (accidental binary-clause
/// XOR matches).
const XOR_MIN_CLAUSE_DENSITY_NUMERATOR: usize = 1;
const XOR_MIN_CLAUSE_DENSITY_DENOMINATOR: usize = 20;

/// Minimum number of XOR constraints to justify the overhead of Gaussian
/// elimination. Set to 1 so that density is the sole gating criterion --
/// even a single XOR in a small pure-XOR formula (100% density) should
/// activate GE. The density threshold already filters accidental matches.
const XOR_MIN_CONSTRAINT_COUNT: usize = 1;

// ---------------------------------------------------------------------------
// Per-component matrix size limits (ported from CryptoMiniSat)
// ---------------------------------------------------------------------------
// Reference: `reference/cryptominisat/src/solverconf.h:176-188`
//
// CMS default: max_matrix_rows=2000, max_matrix_columns=1000, min_matrix_rows=3.
// These prevent pathological O(n^2*m) overhead from very large GF(2) matrices
// while still handling real crypto benchmarks (which typically decompose into
// many small components after splitting).

/// Maximum number of rows (XOR constraints) per component matrix. Components
/// exceeding this are skipped because GE cost is O(rows * cols * words).
/// CMS default: 2000.
pub(crate) const MAX_MATRIX_ROWS: usize = 2000;

/// Maximum number of columns (variables) per component matrix. CMS default: 1000.
pub(crate) const MAX_MATRIX_COLUMNS: usize = 1000;

/// Minimum number of rows per component matrix. CMS default: 3. AY uses 1
/// (effectively no minimum) because the density heuristic already filters out
/// noise, and even unit XOR constraints (a = 1) provide useful propagation
/// through the GE framework at negligible cost. The upper bounds
/// (`MAX_MATRIX_ROWS`, `MAX_MATRIX_COLUMNS`) are the meaningful guards.
pub(crate) const MIN_MATRIX_ROWS: usize = 1;

/// Maximum number of component matrices to create. CMS default: 5.
/// After component splitting, only the largest N components are kept.
pub(crate) const MAX_NUM_MATRICES: usize = 5;

/// Check whether a single component's dimensions are within GE limits.
///
/// Returns `true` if the component is neither too small (< `MIN_MATRIX_ROWS`)
/// nor too large (> `MAX_MATRIX_ROWS` or `MAX_MATRIX_COLUMNS`).
pub(crate) fn component_within_limits(num_rows: usize, num_cols: usize) -> bool {
    (MIN_MATRIX_ROWS..=MAX_MATRIX_ROWS).contains(&num_rows) && num_cols <= MAX_MATRIX_COLUMNS
}

/// Decide whether Gaussian elimination should be enabled based on XOR density.
///
/// Returns `true` when the detected XOR constraints consume a meaningful
/// fraction of the clause database, indicating that the instance is
/// XOR-heavy enough to benefit from native GF(2) solving.
///
/// # Arguments
///
/// * `consumed` - Number of CNF clauses consumed by XOR detection.
/// * `remaining` - Number of CNF clauses NOT consumed (remaining for SAT).
/// * `xor_count` - Number of XOR constraints detected.
///
/// # Heuristic
///
/// The function requires all three conditions:
/// 1. At least one clause was consumed (`consumed > 0`).
/// 2. At least `XOR_MIN_CONSTRAINT_COUNT` XOR constraints were found.
/// 3. The consumed fraction is at least `XOR_MIN_CLAUSE_DENSITY_NUMERATOR /
///    XOR_MIN_CLAUSE_DENSITY_DENOMINATOR` (currently 5%) of the total clause
///    count.
///
/// # Example
///
/// ```
/// use ay_xor::should_enable_gauss_elimination;
///
/// // Large crypto benchmark: 1M clauses, 30% XOR-derived.
/// assert!(should_enable_gauss_elimination(300_000, 700_000, 5_000));
///
/// // Below 5% density: accidental XOR matches.
/// assert!(!should_enable_gauss_elimination(100, 9_900, 10));
///
/// // No XOR constraints at all.
/// assert!(!should_enable_gauss_elimination(0, 1_000, 0));
///
/// // Small pure-XOR formula (100% density) still qualifies.
/// assert!(should_enable_gauss_elimination(4, 0, 2));
/// ```
#[allow(clippy::suspicious_operation_groupings)] // cross-multiplication: consumed/total >= NUM/DEN
pub fn should_enable_gauss_elimination(
    consumed: usize,
    remaining: usize,
    xor_count: usize,
) -> bool {
    let total = consumed.saturating_add(remaining);
    consumed > 0
        && xor_count >= XOR_MIN_CONSTRAINT_COUNT
        && consumed.saturating_mul(XOR_MIN_CLAUSE_DENSITY_DENOMINATOR)
            >= total.saturating_mul(XOR_MIN_CLAUSE_DENSITY_NUMERATOR)
}

/// Preprocess CNF clauses to extract XOR constraints.
///
/// This function detects XOR patterns encoded in CNF clauses and extracts them
/// into an XorExtension for more efficient solving. The remaining clauses
/// (those not part of XOR patterns) are returned along with the extension.
///
/// # Arguments
///
/// * `clauses` - The input CNF clauses
///
/// # Returns
///
/// A tuple of (remaining_clauses, xor_extension) where:
/// - `remaining_clauses` are clauses that weren't part of detected XOR patterns
/// - `xor_extension` contains the detected XOR constraints (None if no XORs found)
///
/// # Example
///
/// ```
/// use ay_xor::preprocess_clauses;
/// use ay_sat::{Literal, Variable, Solver, SatResult};
///
/// // CNF encoding of x0 XOR x1 = 1
/// let clauses = vec![
///     vec![Literal::negative(Variable::new(0)), Literal::negative(Variable::new(1))],
///     vec![Literal::positive(Variable::new(0)), Literal::positive(Variable::new(1))],
/// ];
///
/// let (remaining, xor_ext) = preprocess_clauses(&clauses);
/// assert!(remaining.is_empty()); // All clauses were XOR encoding
/// assert!(xor_ext.is_some());    // Detected 1 XOR constraint
/// ```
pub fn preprocess_clauses(clauses: &[Vec<Literal>]) -> (Vec<Vec<Literal>>, Option<XorExtension>) {
    let mut finder = XorFinder::new();
    let (xors, used_indices) = finder.find_xors_with_indices(clauses);

    if xors.is_empty() {
        // No XORs found - return original clauses
        return (clauses.to_vec(), None);
    }

    // Filter out clauses that were part of XOR patterns
    let remaining: Vec<Vec<Literal>> = clauses
        .iter()
        .enumerate()
        .filter(|(idx, _)| !used_indices.contains(idx))
        .map(|(_, clause)| clause.clone())
        .collect();

    let extension = XorExtension::new(xors);

    (remaining, Some(extension))
}

/// Statistics from XOR preprocessing
#[derive(Debug, Clone, Default)]
pub struct XorPreprocessStats {
    /// Number of XOR constraints detected
    pub xors_detected: usize,
    /// Number of clauses consumed (removed from CNF)
    pub clauses_consumed: usize,
    /// Number of variables in XOR constraints
    pub xor_variables: usize,
}

/// Preprocess CNF clauses and return statistics.
///
/// This is like `preprocess_clauses` but also returns statistics about
/// what was detected.
pub fn preprocess_clauses_with_stats(
    clauses: &[Vec<Literal>],
) -> (Vec<Vec<Literal>>, Option<XorExtension>, XorPreprocessStats) {
    let mut finder = XorFinder::new();
    let (xors, used_indices) = finder.find_xors_with_indices(clauses);

    let mut stats = XorPreprocessStats {
        xors_detected: xors.len(),
        clauses_consumed: used_indices.len(),
        xor_variables: 0,
    };

    if xors.is_empty() {
        return (clauses.to_vec(), None, stats);
    }

    // Count unique variables in XOR constraints
    let mut all_vars: HashSet<VarId> = HashSet::default();
    for xor in &xors {
        for &var in &xor.vars {
            all_vars.insert(var);
        }
    }
    stats.xor_variables = all_vars.len();

    // Filter out consumed clauses
    let remaining: Vec<Vec<Literal>> = clauses
        .iter()
        .enumerate()
        .filter(|(idx, _)| !used_indices.contains(idx))
        .map(|(_, clause)| clause.clone())
        .collect();

    let extension = XorExtension::new(xors);

    (remaining, Some(extension), stats)
}

/// Solve a CNF formula with automatic XOR detection and Gauss-Jordan solving.
///
/// This is a convenience function that:
/// 1. Detects XOR patterns in the input clauses
/// 2. Applies the XOR density heuristic to decide if GE is worthwhile
/// 3. Solves using the XOR extension for detected XORs (or pure SAT if density
///    is too low)
///
/// # Arguments
///
/// * `num_vars` - Number of variables in the formula
/// * `clauses` - The CNF clauses
///
/// # Returns
///
/// The solve result (Sat with model, Unsat, or Unknown)
///
/// # Preprocessing policy
///
/// XOR extraction transfers ownership of exact source-clause positions to the
/// extension. This helper therefore disables the SAT solver's independent
/// initial preprocessor, which could rewrite those positions before the
/// extension transaction commits. When XOR extraction declines, the fallback
/// is ordinary CDCL without that optional initial simplification.
///
/// # Example
///
/// ```
/// use ay_xor::solve_with_xor_detection;
/// use ay_sat::{Literal, Variable, SatResult};
///
/// // XOR chain: x0 XOR x1 = 1, x1 XOR x2 = 0
/// // This implies x0 XOR x2 = 1
/// let clauses = vec![
///     // x0 XOR x1 = 1
///     vec![Literal::negative(Variable::new(0)), Literal::negative(Variable::new(1))],
///     vec![Literal::positive(Variable::new(0)), Literal::positive(Variable::new(1))],
///     // x1 XOR x2 = 0
///     vec![Literal::negative(Variable::new(1)), Literal::positive(Variable::new(2))],
///     vec![Literal::positive(Variable::new(1)), Literal::negative(Variable::new(2))],
/// ];
///
/// let result = solve_with_xor_detection(3, &clauses);
/// assert!(result.is_sat());
/// if let SatResult::Sat(model) = result.into_inner() {
///     // x0 XOR x2 should be 1
///     let x0 = model[0];
///     let x2 = model[2];
///     assert_ne!(x0, x2);
/// }
/// ```
pub fn solve_with_xor_detection(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> ay_sat::SolverSatResult {
    let mut solver = source_stable_solver(num_vars, clauses);

    solver.solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
        let total = active_clauses.len();
        let mut finder = XorFinder::new();
        let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
        build_prepared_extension(xors, used_indices, total)
    })
}

/// Result of XOR-aware solving with statistics
#[derive(Debug)]
pub struct XorSatResult {
    /// The solver-origin result. See [`ay_sat::SolverSatResult`] for authority scope.
    pub result: ay_sat::SolverSatResult,
    /// Preprocessing statistics
    pub stats: XorPreprocessStats,
}

/// Solve with XOR detection and return statistics.
///
/// This is like `solve_with_xor_detection` but also returns statistics
/// about the XOR detection phase. It uses the same source-stable preprocessing
/// policy documented by [`solve_with_xor_detection`].
pub fn solve_with_xor_detection_stats(num_vars: usize, clauses: &[Vec<Literal>]) -> XorSatResult {
    let mut stats = XorPreprocessStats::default();
    let mut solver = source_stable_solver(num_vars, clauses);

    let result = solver.solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
        let total = active_clauses.len();
        let mut finder = XorFinder::new();
        let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
        stats.xors_detected = xors.len();
        stats.clauses_consumed = used_indices.len();
        stats.xor_variables = xors
            .iter()
            .flat_map(|xor| xor.vars.iter().copied())
            .collect::<HashSet<VarId>>()
            .len();
        build_prepared_extension(xors, used_indices, total)
    });

    XorSatResult { result, stats }
}

/// Build the private solver used by the XOR convenience entry points.
///
/// The configuration is deliberately local: global SAT callers keep their
/// ordinary preprocessing policy.
fn source_stable_solver(num_vars: usize, clauses: &[Vec<Literal>]) -> Solver {
    let mut solver = Solver::new(num_vars);
    solver.set_preprocess_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver
}

pub(crate) fn build_prepared_extension(
    xors: Vec<crate::constraint::XorConstraint>,
    used_indices: HashSet<usize>,
    total_clauses: usize,
) -> Option<PreparedExtension<XorExtension>> {
    if xors.is_empty() {
        return None;
    }

    let consumed = used_indices.len();
    let remaining = total_clauses.saturating_sub(consumed);

    if !should_enable_gauss_elimination(consumed, remaining, xors.len()) {
        return None;
    }

    let frozen_variables = xors
        .iter()
        .flat_map(|xor| xor.vars.iter().copied())
        .collect::<HashSet<VarId>>()
        .into_iter()
        .map(Variable::new)
        .collect();

    Some(PreparedExtension::new(
        XorExtension::new(xors),
        used_indices.into_iter().collect(),
        frozen_variables,
    ))
}
