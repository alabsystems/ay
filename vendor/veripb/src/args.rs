//! Command line arguments and settings for VeriPB checker.

use std::ops::Bound;
use std::path::{Path, PathBuf};

use clap::{ArgAction, Parser};
use clap_verbosity_flag::{InfoLevel, Verbosity};
use log::LevelFilter;
use veripb_checker::config::{CheckerConfig, FormulaFormat, RangeSet};
use veripb_parser::pbp_parser::parser::ParserArgs;

/// Command line arguments for the VeriPB tool.
#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
pub struct Args {
    /// Input formula file
    pub formula: PathBuf,

    /// Proof file
    pub derivation: PathBuf,

    /// Output formula file for problem reformulation
    pub output_formula: Option<PathBuf>,

    /// Force formula parsing to use the OPB parser
    #[arg(long, default_value_t, group = "formula_format")]
    pub opb: bool,

    /// Force formula parsing to use the DIMACS CNF parser
    #[arg(long, default_value_t, group = "formula_format")]
    pub cnf: bool,

    /// Force formula parsing to use the WCNF parser
    #[arg(long, default_value_t, group = "formula_format")]
    pub wcnf: bool,

    /// Elaborate to PATH; if PATH is a directory, write `<derivation>.elab.pbp` inside it; if no PATH specified, write next to derivation
    #[arg(short, long, value_name = "PATH", num_args = 0..=1)]
    pub elaborate: Option<Option<PathBuf>>,

    /// Enable trace mode
    #[arg(short, long, default_value_t = false, group = "progress")]
    pub trace: bool,

    /// Enable trace mode only for the given (1-based) proof file lines, e.g. `20..=30,40,50..`
    #[arg(long = "trace-lines", value_name = "RANGES", value_parser = parse_range_set, conflicts_with = "show_progress")]
    pub trace_lines: Option<RangeSet>,

    /// Enable trace mode only for the rules deriving the given constraint IDs, e.g. `20..=30,40,50..`
    #[arg(long = "trace-ids", value_name = "RANGES", value_parser = parse_range_set, conflicts_with = "show_progress")]
    pub trace_ids: Option<RangeSet>,

    /// When tracing a pol rule, also print a step-by-step trace of its derivation
    #[arg(long = "trace-pol", default_value_t = false)]
    pub trace_pol: bool,

    /// Print the propagation trail for failed propagations
    #[arg(short = 'f', long)]
    pub trace_failed: bool,

    /// Use unchecked deletion by default
    #[arg(short = 'u', long = "unchecked-deletion")]
    pub unchecked_deletion: bool,

    /// Fail proof if checked deletion check fails
    #[arg(short = 'c', long = "force-checked-deletion")]
    pub force_checked_deletion: bool,

    /// Disable printing the verification result
    #[arg(long = "disable-result-printing", action=ArgAction::SetFalse, default_value_t = true)]
    pub print_verification_result: bool,

    /// Only warn (instead of aborting) when a DIMACS CNF `p cnf <vars> <clauses>`
    /// header disagrees with the file contents.
    ///
    /// By default a mismatch is an error, because a CNF file truncated at a
    /// clause boundary is otherwise indistinguishable from a complete one and
    /// would make the checker verify a proof against a weaker formula.
    #[arg(long = "lenient-header-counts", default_value_t = false)]
    pub lenient_header_counts: bool,

    /// Control log verbosity. Pass `-v` or `-vv` to see info/debug output,
    /// `-q` to silence warnings, `-qq` to silence everything but errors.
    #[command(flatten)]
    pub verbosity: Verbosity<InfoLevel>,

    /// Disable printing of warnings.
    ///
    /// Deprecated: use `-q` instead. Kept for backwards compatibility; if
    /// passed, caps the effective log level at `error` regardless of `-v`.
    #[arg(long = "hide-warnings", action = ArgAction::SetFalse, default_value_t = true, hide = true)]
    pub show_warnings: bool,

    /// Disables the check that the canonical file path for the elaborated proof
    /// is different from the input files.
    #[arg(long = "ignore-file-path-check", default_value_t = false)]
    pub ignore_file_path_check: bool,

    /// Enables printing of the progress (only for proof version 3 and above).
    #[arg(short = 'p', long, default_value_t = false, group = "progress")]
    pub show_progress: bool,

    /// Enables collection and printing of checking statistics:
    /// Currently only supported statistic is total time (s)
    #[arg(short = 's', long, default_value_t = false)]
    pub stats: bool,

    /// Cross-check the soundness-critical steps (cutting-planes derivations,
    /// RUP propagation conflicts, stored contradictions and logged solutions)
    /// through the machine-checked proved kernel. Any divergence between the
    /// checker and the kernel is reported as an error. Steps the kernel
    /// cannot represent (coefficients beyond 64 bits, rules outside the
    /// proved fragment) are counted and reported, never silently trusted.
    #[arg(long = "kernel-verify", default_value_t = false)]
    pub kernel_verify: bool,
}

impl Args {
    /// The formula format forced by `--opb`/`--cnf`/`--wcnf`, or `None` if the
    /// format should be inferred from the file extension. The flags are mutually
    /// exclusive (enforced by the `formula_format` clap group).
    pub fn formula_format_override(&self) -> Option<FormulaFormat> {
        if self.opb {
            Some(FormulaFormat::OPB)
        } else if self.cnf {
            Some(FormulaFormat::CNF)
        } else if self.wcnf {
            Some(FormulaFormat::WCNF)
        } else {
            None
        }
    }

    /// Decide on the elaboration output path from `--elaborate`, using the
    /// default `<derivation>.elab.pbp` name when no file is given.
    pub fn elaboration_path(&self) -> Option<PathBuf> {
        let target = self.elaborate.as_ref()?;
        let name = default_elaboration_name(&self.derivation);
        Some(match target {
            None => self.derivation.parent().unwrap_or(Path::new("")).join(name),
            Some(path) if path.is_dir() => path.join(name),
            Some(path) => path.clone(),
        })
    }

    /// The effective log level after combining `-v` or `-q` with the
    /// deprecated `--hide-warnings` flag.
    pub fn log_level_filter(&self) -> LevelFilter {
        let level = self.verbosity.log_level_filter();
        if self.show_warnings {
            level
        } else {
            level.min(LevelFilter::Error)
        }
    }

    /// Build the proof-parser arguments implied by these options.
    pub fn parser_args(&self) -> ParserArgs {
        ParserArgs {
            show_progress: self.show_progress,
            trace_enabled: self.trace || self.trace_lines.is_some() || self.trace_ids.is_some(),
            store_assertion_annotations: false, // mainline VeriPB doesn't need annotations
        }
    }
}

/// Generate a default name for the elaborated proof.
fn default_elaboration_name(derivation: &Path) -> PathBuf {
    match derivation.file_stem() {
        Some(stem) => {
            let mut name = stem.to_os_string();
            name.push(".elab.pbp");
            name.into()
        }
        None => "elab.pbp".into(),
    }
}

impl Default for Args {
    fn default() -> Self {
        Args {
            unchecked_deletion: false,
            force_checked_deletion: false,
            print_verification_result: true,
            formula: PathBuf::default(),
            derivation: PathBuf::default(),
            output_formula: None,
            elaborate: None,
            trace: false,
            opb: false,
            cnf: false,
            wcnf: false,
            trace_failed: false,
            verbosity: Verbosity::default(),
            show_warnings: true,
            show_progress: false,
            ignore_file_path_check: false,
            stats: false,
            trace_lines: None,
            trace_ids: None,
            trace_pol: false,
            lenient_header_counts: false,
            kernel_verify: false,
        }
    }
}

impl From<Args> for CheckerConfig {
    fn from(args: Args) -> Self {
        let formula_format_override = args.formula_format_override();
        let elaboration_path = args.elaboration_path();
        CheckerConfig {
            derivation_path: args.derivation,
            formula_path: args.formula,
            elaboration_path,
            unchecked_deletion: args.unchecked_deletion,
            trace_failed: args.trace_failed,
            trace: args.trace,
            trace_lines: args.trace_lines,
            trace_ids: args.trace_ids,
            trace_pol: args.trace_pol,
            print_verification_result: args.print_verification_result,
            force_checked_deletion: args.force_checked_deletion,
            kernel_verify: args.kernel_verify,
            output_formula: args.output_formula,
            formula_format_override,
            record_stats: args.stats,
        }
    }
}

/// Parse a comma-separated list of ranges like `20..=30,40,50..` into a [`RangeSet`].
///
/// Each comma-separated entry uses Rust range syntax and is one of:
/// - `A`     a single value,
/// - `A..B`  a half-open range from `A` up to (but not including) `B`,
/// - `A..=B` an inclusive range from `A` to `B`,
/// - `A..`   everything from `A` onwards, and
/// - `..B` / `..=B`  everything up to (and including, for `..=B`) `B`.
fn parse_range_set(input: &str) -> Result<RangeSet, String> {
    let parse_bound = |value: &str, part: &str| {
        value
            .parse::<usize>()
            .map_err(|_| format!("`{value}` in range `{part}` is not a valid number"))
    };

    let mut ranges = Vec::new();
    for part in input.split(',') {
        let part = part.trim();
        if part.is_empty() {
            return Err(format!("found an empty range in `{input}`"));
        }
        let range = if let Some((start, end)) = part.split_once("..") {
            let start = if start.is_empty() {
                Bound::Unbounded
            } else {
                Bound::Included(parse_bound(start, part)?)
            };
            // An `=` prefix on the upper bound makes the range inclusive.
            let (end, inclusive) = match end.strip_prefix('=') {
                Some(end) => (end, true),
                None => (end, false),
            };
            let end = if end.is_empty() {
                if inclusive {
                    return Err(format!(
                        "range `{part}` is missing an upper bound after `..=`"
                    ));
                }
                Bound::Unbounded
            } else {
                let end = parse_bound(end, part)?;
                if inclusive {
                    Bound::Included(end)
                } else {
                    Bound::Excluded(end)
                }
            };
            // Reject ranges that end before they start.
            if let (Bound::Included(start), Bound::Included(end) | Bound::Excluded(end)) =
                (&start, &end)
                && end < start
            {
                return Err(format!("range `{part}` ends before it starts"));
            }
            (start, end)
        } else {
            // A bare value `A` selects exactly that value, i.e. `A..=A`.
            let value = parse_bound(part, part)?;
            (Bound::Included(value), Bound::Included(value))
        };
        ranges.push(range);
    }
    Ok(RangeSet::new(ranges))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_single_value() {
        let set = parse_range_set("40").unwrap();
        assert!(!set.contains(39));
        assert!(set.contains(40));
        assert!(!set.contains(41));
    }

    #[test]
    fn parses_inclusive_range() {
        let set = parse_range_set("20..=30").unwrap();
        assert!(!set.contains(19));
        assert!(set.contains(20));
        assert!(set.contains(25));
        assert!(set.contains(30));
        assert!(!set.contains(31));
    }

    #[test]
    fn parses_exclusive_range() {
        let set = parse_range_set("20..30").unwrap();
        assert!(!set.contains(19));
        assert!(set.contains(20));
        assert!(set.contains(29));
        assert!(!set.contains(30));
    }

    #[test]
    fn parses_open_ended_range() {
        let set = parse_range_set("50..").unwrap();
        assert!(!set.contains(49));
        assert!(set.contains(50));
        assert!(set.contains(1_000_000));
    }

    #[test]
    fn parses_open_start_inclusive_range() {
        let set = parse_range_set("..=10").unwrap();
        assert!(set.contains(0));
        assert!(set.contains(10));
        assert!(!set.contains(11));
    }

    #[test]
    fn parses_open_start_exclusive_range() {
        let set = parse_range_set("..10").unwrap();
        assert!(set.contains(0));
        assert!(set.contains(9));
        assert!(!set.contains(10));
    }

    #[test]
    fn parses_combination() {
        let set = parse_range_set("20..=30,40,50..").unwrap();
        assert!(!set.contains(19));
        assert!(set.contains(25));
        assert!(!set.contains(35));
        assert!(set.contains(40));
        assert!(!set.contains(45));
        assert!(set.contains(50));
        assert!(set.contains(99));
    }

    #[test]
    fn rejects_empty_entry() {
        assert!(parse_range_set("20,,30").is_err());
        assert!(parse_range_set("").is_err());
    }

    #[test]
    fn rejects_inverted_range() {
        assert!(parse_range_set("30..=20").is_err());
        assert!(parse_range_set("30..20").is_err());
    }

    #[test]
    fn rejects_inclusive_range_without_upper_bound() {
        assert!(parse_range_set("5..=").is_err());
    }

    #[test]
    fn rejects_non_numeric() {
        assert!(parse_range_set("abc").is_err());
        assert!(parse_range_set("1..x").is_err());
    }
}
