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
        Feature {
            name: "sat-gpu",
            enabled: ay_sat::feature_flags::GPU,
            description: "GPU compute infrastructure (wgpu: Vulkan/DX12/Metal)",
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

/// Interactive mode banner printed when ay is run on a TTY without arguments.
pub(crate) fn interactive_banner() -> String {
    // Show a compact subset of commonly used logics in the banner.
    let common_logics = [
        "QF_LIA", "QF_LRA", "QF_BV", "QF_ABV", "QF_UF", "QF_UFLIA", "QF_UFLRA", "QF_FP", "HORN",
        "ALL",
    ];
    let logics_str = common_logics.join(" ");
    format!(
        "ay {} -- Rust constraint-solving toolkit\n\
         Type SMT-LIB 2.6 commands. Ctrl-D to exit.\n\
         Supported: {}",
        env!("AY_BUILD_STAMP"),
        logics_str,
    )
}
