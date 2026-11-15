//! This is the frontend crate for the VeriPB checker containing the main functions to use VeriPB as a CLI. To check a `<proof>` file for an `<problem>` file using the VeriPB CLI use
//! ```bash
//! veripb <problem> <proof>
//! ```
//!
//! For further options, see
//! ```bash
//! veripb --help
//! ```
//!
//! Furthermore, the [`run_checker`] function provides a way to call the VeriPB checker from another program with out using the CLI.
//!
//! VeriPB is designed to be modular and reusable. For only using parts of VeriPB and reusing functionality already implemented you can use the following crates:
//! - [`veripb_checker`]: Forward checker for VeriPB proofs implementing forward checking for each rule.
//! - [`veripb_formula`]: Basic data structures for variables, literals, constraints, assignments, substitutions, and formulas.
//! - [`veripb_parser`]: Parsers for pseudo-Boolean VeriPB proofs and supported input formula input formats.
//! - [`veripb_propagator`](https://docs.rs/veripb-propagator/): Library for propagating pseudo-Boolean constraints.
//! - [`veripb_rules`](https://docs.rs/veripb-rules/): Definitions of VeriPB rules.

use std::{
    fs::{self},
    path::Path,
    time::Instant,
};

use crate::args::Args;
use ahash::AHashMap;
use anyhow::anyhow;
use veripb_checker::{
    checker::ForwardsChecker,
    config::FormulaFormat,
    error::{CheckingError, ForwardsCheckerError},
    prelude::Context,
};
use veripb_formula::prelude::*;
use veripb_parser::{
    cnf_parser::{CnfParserOptions, parse_cnf_from_file_with_options},
    io::open_maybe_compressed,
    opb_parser::parse_opb_from_file,
    pbp_parser::{legacy_v2::parser::Version2Parser, parser::parse_proof},
    wcnf_parser::parse_wcnf_from_file,
};

/// Version of the integrated checking library. AY release provenance identifies
/// its exact maintained source and integration changes.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub mod args;
pub mod error;
pub mod report;
pub use report::{CheckReport, InputAdmission};

/// A parsed input formula together with its variable and label bookkeeping.
struct ParsedFormula {
    formula: Formula,
    variables: VarNameManager,
    labels: AHashMap<String, isize>,
    preserved_vars: Option<ahash::AHashSet<usize>>,
}

/// How a completed run should be reported to whoever invoked VeriPB.
///
/// A run that did not fail can still have given less than it was asked for, and
/// that has to be visible both in the verdict on stdout and in the exit code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunOutcome {
    /// Everything the verdict rests on was checked.
    Verified,
    /// The proof checked out, but only under a weaker guarantee: VeriPB could
    /// not prove a checked deletion and fell back to unchecked deletion on its
    /// own, so a solution-dependent verdict (`SAT`, `BOUNDS`, enumeration) no
    /// longer means what an unqualified `s VERIFIED ...` would mean.
    ///
    /// This is *not* reported when the user asked for unchecked deletion with
    /// `--unchecked-deletion`; then the weaker guarantee is what was requested
    /// and only the verdict line is qualified.
    WeakenedGuarantees,
}

impl RunOutcome {
    /// The process exit code for this outcome.
    ///
    /// `2` is distinct from `1` (proof rejected or checker error) so that a
    /// caller can tell "your proof is wrong" from "I could not check all of your
    /// proof".
    pub fn exit_code(self) -> i32 {
        match self {
            RunOutcome::Verified => 0,
            RunOutcome::WeakenedGuarantees => 2,
        }
    }
}

/// Run the standalone frontend while preserving its documented verdict format.
pub fn run_checker(args: Args) -> Result<RunOutcome, anyhow::Error> {
    let report = check(args)?;
    report.write_to(&mut std::io::stdout().lock())?;
    if report.outcome() == RunOutcome::WeakenedGuarantees {
        log::warn!(
            "The verdict above holds only under a weaker guarantee, because a checked deletion \
             could not be proven and VeriPB fell back to unchecked deletion. Rerun with \
             --force-checked-deletion to reject such proofs, or with --unchecked-deletion to \
             accept the weaker guarantee on purpose."
        );
    }
    Ok(report.outcome())
}

/// Check in-process without printing a verdict. A report is returned only when
/// every rule and the final elaboration flush have completed successfully.
pub fn check(args: Args) -> Result<CheckReport, anyhow::Error> {
    let input_admission = match (args.lenient_header_counts, args.ignore_file_path_check) {
        (false, false) => InputAdmission::Strict,
        (true, false) => InputAdmission::LenientHeaderCounts,
        (false, true) => InputAdmission::UncheckedOutputPaths,
        (true, true) => InputAdmission::LenientHeadersAndUncheckedOutputPaths,
    };
    let statistics = args.stats.then(Instant::now);

    validate_input_paths(&args)?;

    let (mut derivation_reader, file_size) = open_maybe_compressed(&args.derivation)?;
    let derivation_path = args.derivation.clone();
    let args_elaboration_path = args.elaboration_path();
    let parser_args = args.parser_args();

    let ParsedFormula {
        formula,
        variables,
        labels,
        preserved_vars,
    } = parse_formula(
        &args.formula,
        args.formula_format_override(),
        if args.lenient_header_counts {
            CnfParserOptions::lenient()
        } else {
            CnfParserOptions::strict()
        },
    )?;

    // Set up context and forwards-checker.
    let context = Context::new(args, variables, preserved_vars);
    let mut checker = ForwardsChecker::new(context, formula)?;

    // Version 2 signals itself via a parse error. All other errors propagate.
    let mut is_version2 = false;

    // Parse version 3 and run checking: the parser dispatches rules to the checker.
    if let Err(err) = parse_proof(
        file_size,
        &mut derivation_reader,
        &mut checker,
        labels,
        parser_args,
    ) {
        match err {
            ForwardsCheckerError::Parse(e) if e.is_version_error() => is_version2 = true,
            other => return Err(other.into()),
        }
    }

    if is_version2 {
        log::info!(
            "Switched to proof version 2.0 (it is recommended to migrate to proof version 3.0)."
        );
        let mut v2_parser = Version2Parser::new(&mut checker);
        v2_parser.parse(derivation_path, derivation_reader)?;

        if !checker.context.has_end_proof {
            return Err(CheckingError::EndProofMissing.into());
        }
    }

    // Finish the elaborated proof before anything is reported: `BufWriter`
    // flushes on drop and throws the error away, so a kernel proof that never
    // made it to disk would otherwise be accompanied by a success verdict and
    // exit code 0.
    if let Some(elaborator) = checker.context.elaborator.as_mut() {
        elaborator.finish().map_err(|err| {
            anyhow!(
                "Failed to write the elaborated proof{}: {err}",
                match args_elaboration_path {
                    Some(path) => format!(" to '{}'", path.display()),
                    None => String::new(),
                }
            )
        })?;
    }

    let mut diagnostics = Vec::new();
    if checker.context.config.kernel_verify {
        diagnostics.push(checker.context.kernel_stats.summary());
        if let Some(line) = veripb_checker::kernel_bridge::composition_summary(&checker.context) {
            diagnostics.push(line);
        }
    }
    if let Some(started) = statistics {
        diagnostics.push(format!(
            "\nc statistic: time total: {} s",
            started.elapsed().as_secs_f64()
        ));
        diagnostics.extend(checker.context.custom_timer_lines());
    }
    let outcome = if checker.context.guarantee_was_silently_weakened() {
        RunOutcome::WeakenedGuarantees
    } else {
        RunOutcome::Verified
    };
    Ok(CheckReport {
        input_admission,
        statements: checker.context.take_checked_statements(),
        diagnostics,
        outcome,
    })
}

/// Check if the elaborated proof path is different from the formula or derivation path.
///
/// This does not actually check if the elaborated proof file is the same as the formula or derivation file, but only compares the canonical paths of these files.
fn validate_input_paths(args: &Args) -> anyhow::Result<()> {
    if args.ignore_file_path_check {
        return Ok(());
    }
    let Some(elaborate) = args.elaboration_path() else {
        return Ok(());
    };
    let elaborate_path = match fs::canonicalize(&elaborate) {
        Ok(path) => path,
        Err(_) => return Ok(()),
    };
    let formula_path = fs::canonicalize(&args.formula).map_err(|_| {
        anyhow!(
            "The formula file '{}' does not exist.\n\n
            Rerun with --ignore-file-path-check to proceed anyway.",
            args.formula.display()
        )
    })?;
    let derivation_path = fs::canonicalize(&args.derivation).map_err(|_| {
        anyhow!(
            "The derivation file '{}' does not exist.\n\n
            Rerun with --ignore-file-path-check to proceed anyway.",
            args.derivation.display()
        )
    })?;

    let bad_path = if formula_path == elaborate_path {
        "formula"
    } else if derivation_path == elaborate_path {
        "derivation"
    } else {
        return Ok(());
    };

    log::error!(
        "The canonical path of {bad_path} is identical to the canonical path of elaboration output. \n\
        Reading and writing to the same file can cause VeriPB to behave unpredictably. \n\n\
        Rerun with --ignore-file-path-check to proceed anyway."
    );

    Err(anyhow!(
        "Canonical paths are both: {}",
        elaborate_path.display()
    ))
}

/// Parse the input formula from one of the supported formats (cnf, wcnf, or opb).
fn parse_formula(
    formula_path: &Path,
    format_override: Option<FormulaFormat>,
    cnf_options: CnfParserOptions,
) -> Result<ParsedFormula, anyhow::Error> {
    let (formula, variables, labels, preserved_vars) =
        match FormulaFormat::resolve(format_override, formula_path) {
            FormulaFormat::CNF => {
                let (formula, num_vars) =
                    parse_cnf_from_file_with_options(formula_path, cnf_options)?;
                let mut variables = VarNameManager::with_capacity(num_vars + 1);
                variables.add_by_name("");
                for i in 1..=num_vars {
                    variables.add_by_name(&format!("x{i}"));
                }
                (formula, variables, AHashMap::new(), None)
            }
            FormulaFormat::WCNF => {
                let (formula, var_names) = parse_wcnf_from_file(formula_path)?;
                (formula, var_names, AHashMap::new(), None)
            }
            FormulaFormat::OPB => parse_opb_from_file(formula_path)?,
        };
    Ok(ParsedFormula {
        formula,
        variables,
        labels,
        preserved_vars,
    })
}
