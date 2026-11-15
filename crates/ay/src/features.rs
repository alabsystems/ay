// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compile-time feature reporting for ay.
//!
//! Zero runtime overhead: all feature detection uses `cfg!()` which evaluates
//! at compile time. The report is a structured key=value format for LLM and
//! machine consumption.

/// Feature status as a structured entry.
pub(crate) struct Feature {
    pub name: &'static str,
    pub enabled: bool,
    /// Human-readable description. Available for diagnostic tooling; not
    /// included in the JSON `--features` output. Kept as structured data for
    /// future --version or --help integration.
    #[allow(dead_code)] // Retained for future --version/--help integration
    pub description: &'static str,
}

/// Returns all ay feature flags and their compile-time status.
///
/// This is a const-evaluable function with zero runtime overhead.
/// Each entry reports whether the feature was enabled at compile time.
pub(crate) fn all_features() -> &'static [Feature] {
    &[
        // SAT engine features
        Feature {
            name: "raw-pointer-bcp",
            enabled: ay_sat::feature_flags::RAW_POINTER_BCP,
            description: "Raw-pointer implementation of watched-literal BCP",
        },
        Feature {
            name: "sat-jit",
            enabled: ay_sat::feature_flags::JIT,
            description: "Native-code SAT helper kernels (non-BCP)",
        },
        // DPLL(T) features
        Feature {
            name: "proof-checker",
            enabled: ay_dpll::feature_flags::PROOF_CHECKER,
            description: "Internal Alethe proof checker (unconditional since 2026-07-14)",
        },
    ]
}

/// Names of enabled feature flags.
pub(crate) fn enabled_feature_names() -> Vec<&'static str> {
    all_features()
        .iter()
        .filter(|f| f.enabled)
        .map(|f| f.name)
        .collect()
}

/// Supported SMT-LIB logics.
///
/// This is the authoritative list of logics ay accepts via `(set-logic ...)`.
/// Kept in SMT-LIB alphabetical order. HORN is listed last as a non-standard
/// extension for CHC solving.
pub(crate) const SUPPORTED_LOGICS: &[&str] = &[
    "ALL",
    "AUFDT",
    "AUFDTLIA",
    "AUFDTLIRA",
    "AUFLIA",
    "AUFLIRA",
    "AUFLRA",
    "LIA",
    "LIRA",
    "LRA",
    "NIA",
    "NIRA",
    "NRA",
    "QF_ABV",
    "QF_AUFBV",
    "QF_AUFBVLIA",
    "QF_AUFLIA",
    "QF_AUFLIRA",
    "QF_AUFLRA",
    "QF_AX",
    "QF_BV",
    "QF_BVFP",
    "QF_DT",
    "QF_EIA",
    "QF_FP",
    "QF_LIA",
    "QF_LIRA",
    "QF_LRA",
    "QF_NIA",
    "QF_NIRA",
    "QF_NRA",
    "QF_S",
    "QF_SEQ",
    "QF_SLIA",
    "QF_SNIA",
    "QF_UF",
    "QF_UFBV",
    "QF_UFBVLIA",
    "QF_UFLIA",
    "QF_UFLRA",
    "QF_UFNIA",
    "QF_UFNIRA",
    "QF_UFNRA",
    "UF",
    "UFDT",
    "UFDTLIA",
    "UFDTLIRA",
    "UFDTLRA",
    "UFDTNIA",
    "UFDTNIRA",
    "UFDTNRA",
    "UFLIA",
    "UFLRA",
    "UFNIA",
    "UFNIRA",
    "UFNRA",
    "HORN",
];

/// Supported proof output formats.
///
/// See [`crate::proof_emission`] and the repository's `LIMITATIONS.md` for what
/// each format can represent and how certification depends on trust-free
/// output plus acceptance by the intended independent checker. Callers trigger
/// emission with `--proof FILE`, `--proof-format`, or the SMT-LIB `(get-proof)`
/// command.
pub(crate) const PROOF_FORMATS: &[&str] = &["DRAT", "LRAT", "Lean4", "Alethe"];

/// Theories for which ay implements Alethe proof-step rendering.
///
/// Presence in this list does not establish that every proof in the theory is
/// trust-free or checker-accepted. Callers must also inspect proof quality,
/// require successful export, and run the intended independent checker. The
/// list is surfaced in the `--features` JSON report and mirrors the
/// theory-specific `AletheRule` families in `ay_core::AletheRule` and the
/// `TheoryLemmaKind` variants in `ay_core::proof`:
///
/// - `LIA` / `LRA` / `LIRA` — `la_generic` / `lia_generic` with Farkas
///   coefficients emitted as `:args` (missing coefficients fail loud, never a
///   silent trust step; see #8821).
/// - `UF` — `refl` / `symm` / `trans` / `cong` / `eq_congruent` congruence.
/// - `BV` — `bv_bitblast` plus the versioned bit-blast refutation export
///   (`ay_proof::bv_blast_export`, `FORMAT_VERSION`).
/// - `Arrays` — `read_over_write_pos/neg`, `extensionality`.
/// - `FP` — `fp_to_bv` lowering that composes with `bv_bitblast`.
/// - `NIA` / `NRA` — nonlinear arithmetic lemmas.
/// - `Strings` — `string_length` / `string_decompose` / `string_code_inj`.
/// - `Quantifiers` — `forall_inst` / `sko_forall` (Skolemization).
/// - `SAT` — the propositional core emits DRAT/LRAT (see [`PROOF_FORMATS`]).
pub(crate) const PROOF_THEORIES: &[&str] = &[
    "LIA",
    "LRA",
    "LIRA",
    "UF",
    "BV",
    "Arrays",
    "FP",
    "NIA",
    "NRA",
    "Strings",
    "Quantifiers",
    "SAT",
];

/// Print a JSON feature report to stdout (`--features`).
///
/// Output is a single JSON object for machine consumption.
/// Uses serde_json for correct escaping and valid JSON output.
pub(crate) fn print_feature_report() {
    let version = env!("CARGO_PKG_VERSION");
    let build_increment = env!("AY_BUILD_INCREMENT");
    let commit = env!("AY_GIT_HASH");
    let build_date = env!("AY_BUILD_DATE");
    let build_stamp = env!("AY_BUILD_STAMP");
    let profile = env!("AY_BUILD_PROFILE");

    let enabled: Vec<&str> = enabled_feature_names();

    let obj = serde_json::json!({
        "version": version,
        "build_increment": build_increment,
        "commit": commit,
        "build_date": build_date,
        "build_stamp": build_stamp,
        "features": enabled,
        "supported_logics": SUPPORTED_LOGICS,
        "proof_formats": PROOF_FORMATS,
        "proof_theories": PROOF_THEORIES,
        "build_profile": profile,
    });
    safe_println!(
        "{}",
        serde_json::to_string_pretty(&obj).unwrap_or_else(|_| "{}".to_string())
    );
}

/// The screen a bare `ay` opens with on a terminal.
///
/// z3 answers a bare invocation with "input file was not specified", which is
/// true and useless: the person typing it wanted to know what this program is
/// and what to type next. This screen answers both, and it is the only place
/// most users will ever be told that the prompt they are looking at IS `z3 -in`.
///
/// Every line is load-bearing, and every claim on it is checked somewhere:
///
/// - Line 1 doubles as provenance. It carries the version, build increment and
///   date, which is why the interactive path suppresses `c ay.session.start` —
///   printing the stamp twice on the one surface where a human can read it was
///   the old banner's worst habit.
/// - The `try` line is a REAL transcript. Pasting it prints `sat` and a model
///   with `x = 42`; a test pins that, so the screen cannot come to lie.
/// - The logic count comes from [`SUPPORTED_LOGICS`], not from a literal, so it
///   moves when the list does.
///
/// Plain text with styling applied here, through the shared gate, so a
/// NO_COLOR terminal sees the same words in the same columns.
pub(crate) fn interactive_banner() -> String {
    use crate::help_style::{dim, literal};

    let build = crate::build_info::BUILD_INFO;
    // `2026-09-01T04:21:46Z` -> `2026-09-01`. A time-of-day on a start screen is
    // noise; the date answers "how old is this binary?" on its own.
    let date = build.datetime_utc.split('T').next().unwrap_or("");
    let logics = SUPPORTED_LOGICS.len();

    let mut out = String::new();
    out.push_str(&format!(
        "{} {} — proof-oriented SMT · SAT · CHC solver\n",
        literal(&format!("ay {}", build.version)),
        dim(&format!("(build {} · {date})", build.increment)),
    ));
    out.push_str(&format!(
        "A live SMT-LIB 2.6 session — this prompt is {}, made visible. {} exits.\n\n",
        literal("z3 -in"),
        literal("Ctrl-D"),
    ));

    let row = |label: &str, body: String| format!("  {}  {body}\n", dim(&format!("{label:<5}")));
    out.push_str(&row(
        "try",
        literal("(declare-const x Int) (assert (> x 41)) (check-sat)"),
    ));
    out.push_str(&format!(
        "         {}\n",
        dim("→ sat, and a model where x = 42")
    ));
    out.push_str(&row(
        "file",
        format!(
            "{} {}",
            literal("ay problem.smt2"),
            dim("— SMT-LIB2, DIMACS, CHC, WCNF, OPB, LP"),
        ),
    ));
    out.push_str(&row(
        "z3?",
        format!(
            "{} {} {}",
            dim("your flags are accepted —"),
            literal("-t: -T: -st -model"),
            literal("· ay help z3"),
        ),
    ));
    out.push_str(&row(
        "logic",
        format!(
            "{} {} {}",
            dim("ALL until you pin one:"),
            literal("(set-logic QF_LIA)"),
            dim(&format!("— {logics} logics")),
        ),
    ));
    out.push_str(&row(
        "learn",
        format!(
            "{} {} {} {}",
            literal("ay tutorial"),
            dim("· in here:"),
            literal("(help)"),
            dim("· from a shell: ay -h"),
        ),
    ));
    out
}

#[cfg(test)]
mod start_screen_tests {
    use super::*;

    fn strip_ansi(s: &str) -> String {
        let mut out = String::new();
        let mut chars = s.chars();
        while let Some(c) = chars.next() {
            if c == '\u{1b}' {
                for c in chars.by_ref() {
                    if c.is_ascii_alphabetic() {
                        break;
                    }
                }
            } else {
                out.push(c);
            }
        }
        out
    }

    /// The start screen is the one place ay controls its own first impression,
    /// and an 80-column terminal is still the floor. Measured in CHARACTERS:
    /// the screen is full of `—` and `·`, and counting their bytes would report
    /// a fitting line as four columns too wide.
    #[test]
    fn every_line_fits_an_eighty_column_terminal() {
        for (n, line) in strip_ansi(&interactive_banner()).lines().enumerate() {
            assert!(
                line.chars().count() <= 79,
                "start screen line {} is {} columns:\n{line}",
                n + 1,
                line.chars().count()
            );
        }
    }

    /// The screen must read identically with color off — same words, same
    /// columns — because that is what a NO_COLOR user and a redirected pty
    /// capture both see.
    #[test]
    fn the_screen_survives_having_its_color_stripped() {
        let plain = strip_ansi(&interactive_banner());
        assert!(plain.contains("proof-oriented SMT"), "{plain}");
        assert!(plain.contains("z3 -in"), "{plain}");
        assert!(!plain.contains('\u{1b}'));
    }

    /// The logic count is interpolated, never typed. A literal would be correct
    /// exactly until someone adds a logic, and the screen would then be lying
    /// in the one place a newcomer is most likely to check it.
    #[test]
    fn the_logic_count_tracks_the_supported_list() {
        let banner = strip_ansi(&interactive_banner());
        assert!(
            banner.contains(&format!("{} logics", SUPPORTED_LOGICS.len())),
            "the screen does not state the real logic count ({}):\n{banner}",
            SUPPORTED_LOGICS.len()
        );
    }

    /// Every command the screen names must be one the binary answers to. The
    /// screen's whole job is telling a newcomer what to type next, and a dead
    /// pointer there is worse than no pointer.
    #[test]
    fn every_command_the_screen_offers_actually_exists() {
        use clap::CommandFactory;
        let banner = strip_ansi(&interactive_banner());
        let root = crate::Cli::command();
        for offered in ["tutorial", "help"] {
            assert!(
                banner.contains(&format!("ay {offered}")),
                "the screen no longer offers `ay {offered}`"
            );
            assert!(
                root.get_subcommands().any(|s| s.get_name() == offered),
                "the screen offers `ay {offered}`, which is not a subcommand"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SUPPORTED_LOGICS;

    #[test]
    fn supported_logics_include_named_bv_lia_combinations() {
        assert!(SUPPORTED_LOGICS.contains(&"QF_UFBVLIA"));
        assert!(SUPPORTED_LOGICS.contains(&"QF_AUFBVLIA"));
    }

    #[test]
    fn supported_logics_are_sorted_and_unique_before_horn_extension() {
        let (standard, extension) = SUPPORTED_LOGICS.split_at(SUPPORTED_LOGICS.len() - 1);
        assert_eq!(extension, ["HORN"]);
        assert!(standard.windows(2).all(|pair| pair[0] < pair[1]));
    }
}
