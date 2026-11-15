//! Configuration data structure for the [`ForwardsChecker`](crate::checker::ForwardsChecker).

use std::{
    ffi::OsStr,
    ops::{Bound, RangeBounds},
    path::{Path, PathBuf},
};

/// A set of (possibly open-ended) integer ranges, used to select which proof
/// file lines or constraint IDs should be traced.
///
/// The textual syntax (e.g. `20..=30,40,50..`) is parsed on the argument side;
/// this type only stores the resulting ranges and answers membership queries.
#[derive(Debug, Clone, Default)]
pub struct RangeSet {
    /// Each entry is a range over the selected values. Open-ended ranges use
    /// [`Bound::Unbounded`] rather than a sentinel value, so `..B` and `A..`
    /// are represented directly.
    ranges: Vec<(Bound<usize>, Bound<usize>)>,
}

impl RangeSet {
    /// Build a [`RangeSet`] from its constituent ranges.
    pub fn new(ranges: Vec<(Bound<usize>, Bound<usize>)>) -> Self {
        RangeSet { ranges }
    }

    /// Returns `true` if `n` falls within any of the contained ranges.
    pub fn contains(&self, n: usize) -> bool {
        self.ranges.iter().any(|range| range.contains(&n))
    }
}

/// The formula file formats the checker can parse.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(clippy::upper_case_acronyms)]
pub enum FormulaFormat {
    /// Pseudo-Boolean (OPB); also the fallback when no format can be inferred.
    OPB,
    /// DIMACS CNF.
    CNF,
    /// Weighted CNF.
    WCNF,
}

impl FormulaFormat {
    /// Resolve the concrete format for `path`. An explicit `override_` always
    /// wins; otherwise the format is inferred from the file extension, falling
    /// back to [`FormulaFormat::OPB`].
    pub fn resolve(override_: Option<FormulaFormat>, path: &Path) -> FormulaFormat {
        override_.unwrap_or_else(|| match path.extension().and_then(OsStr::to_str) {
            Some("cnf") => FormulaFormat::CNF,
            Some("wcnf") => FormulaFormat::WCNF,
            _ => FormulaFormat::OPB,
        })
    }
}

/// Static configuration for the checker, typically derived from the
/// command-line arguments. Unlike the mutable verifier state in
/// [`Context`](crate::context::Context), these options are fixed for the
/// duration of a run.
#[derive(Debug, Default)]
pub struct CheckerConfig {
    /// Path to derivation file.
    pub derivation_path: PathBuf,
    /// The formula file this run was given.
    ///
    /// The checker itself never re-reads it — the formula is parsed once,
    /// before the checker exists. It is kept here for `--kernel-verify`,
    /// whose formula cross-check reads the file a *second* time, through
    /// `veripb-second-reader`, and compares the result against what the
    /// checker stored (see [`crate::kernel_bridge::shadow_init`]).
    pub formula_path: PathBuf,
    /// Path to elaborated proof file.
    pub elaboration_path: Option<PathBuf>,
    /// If unchecked deletion should be preferred.
    pub unchecked_deletion: bool,
    /// If failed propagations should be traced in detail.
    pub trace_failed: bool,
    /// If forwards proof checking should be traced (each step print its results).
    pub trace: bool,
    /// Set of ranges of lines that should be traced.
    pub trace_lines: Option<RangeSet>,
    /// Set of ranges of constraint IDs, where the rules producing these constraints should be traced.
    pub trace_ids: Option<RangeSet>,
    /// If `pol`-rule lines should be traced in detail.
    pub trace_pol: bool,
    /// If the result of the checking process should be printed.
    pub print_verification_result: bool,
    /// If a failed checked deletion should result in an error instead of switching to weaker guarantees.
    pub force_checked_deletion: bool,
    /// Cross-check pol/RUP derivations and final verdicts through the proved
    /// kernel (`veripb-core-proved`); any divergence is a checking error.
    pub kernel_verify: bool,
    /// The output formula for a reformulation proof.
    pub output_formula: Option<PathBuf>,
    /// Forced formula format; `None` means infer from the file extension.
    pub formula_format_override: Option<FormulaFormat>,
    /// Flag to enable recording statistics.
    pub record_stats: bool,
}
