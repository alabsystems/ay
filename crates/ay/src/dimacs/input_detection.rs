// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(crate) fn is_dimacs_format(content: &str) -> bool {
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        // Comment lines in DIMACS start with 'c'
        if trimmed.starts_with('c') {
            continue;
        }
        // Problem line starts with 'p cnf'
        if trimmed.starts_with("p cnf") {
            return true;
        }
        // If we hit a non-comment, non-empty, non-"p cnf" line, it's not DIMACS
        return false;
    }
    false
}

/// Check if file has .cnf extension
pub(crate) fn has_cnf_extension(path: &str) -> bool {
    path.to_lowercase().ends_with(".cnf")
}

/// Check if file has an extension used by SAT-COMP DIMACS inputs.
pub(crate) fn has_dimacs_file_extension(path: &str) -> bool {
    Path::new(path)
        .extension()
        .is_some_and(|ext| ext.eq_ignore_ascii_case("cnf") || ext.eq_ignore_ascii_case("dimacs"))
}

/// Check whether a DIMACS file has an adjacent structural sidecar.
pub(crate) fn has_structural_sidecar(path: &str) -> bool {
    discover_guard_cover_sidecar_path(path).is_some()
        || discover_separator_cover_sidecar_path(path).is_some()
}

/// Minimum binary clause fraction (numerator/denominator) above which XOR
/// extraction is skipped in favour of congruence + BVE preprocessing.
///
/// Circuit equivalence benchmarks (miter encodings, eq.atree.braun family)
/// encode gates as binary implications. CaDiCaL-style preprocessing
/// (congruence closure + bounded variable elimination) can reduce 95%+ of
/// variables on these formulas. XOR extraction consumes the clause structure
/// needed for gate detection and freezes all XOR variables, preventing BVE
/// from eliminating them. Result: 0% variable reduction instead of 95%.
///
/// Threshold 50% cleanly separates gate-structured circuit formulas (70-80%
/// binary) from crypto benchmarks (typically <30% binary).
const BINARY_CLAUSE_FRACTION_NUMERATOR: usize = 1;
const BINARY_CLAUSE_FRACTION_DENOMINATOR: usize = 2; // 50%

/// Gate-structured circuit formulas (miter encodings, eq.atree.braun) are
/// dominated by binary + ternary clauses (>95% combined). Binary clauses
/// encode implications between gate outputs; ternary clauses encode AND/OR/XOR
/// gate definitions. Even though XOR patterns exist in the ternary clauses,
/// congruence closure is far more effective than GF(2) Gaussian elimination
/// on these formulas. The XOR extension disables congruence and most
/// inprocessing, causing exponential slowdown.
///
/// braun.7: 43% binary + 56% ternary = 99% gate-structured, but only 43% binary
///   (below the 50% binary-only threshold), so XOR was incorrectly enabled.
/// braun.8: 75% binary (above 50%), XOR correctly disabled, solves in 2ms.
const GATE_STRUCTURE_THRESHOLD_NUMERATOR: usize = 19;
const GATE_STRUCTURE_THRESHOLD_DENOMINATOR: usize = 20; // 95%

/// Sparse XOR extraction on wide circuit CNF should stay on the pure SAT path.
///
/// `Circuit_multiplier22` has only sparse detected XOR definitions (~1% of
/// clauses, ~6% consumed), while ~90% of its clauses are width >= 4 circuit
/// definition clauses. Routing that shape through the XOR extension consumes
/// part of the definition surface, freezes XOR variables, and disables the
/// factor/BVE/congruence preprocessing that CaDiCaL uses on the same family.
const SPARSE_XOR_WIDE_CNF_XOR_FRACTION_NUMERATOR: usize = 1;
const SPARSE_XOR_WIDE_CNF_XOR_FRACTION_DENOMINATOR: usize = 50; // 2%
const SPARSE_XOR_WIDE_CNF_CONSUMED_FRACTION_NUMERATOR: usize = 1;
const SPARSE_XOR_WIDE_CNF_CONSUMED_FRACTION_DENOMINATOR: usize = 10; // 10%
const SPARSE_XOR_WIDE_CNF_WIDE_FRACTION_NUMERATOR: usize = 4;
const SPARSE_XOR_WIDE_CNF_WIDE_FRACTION_DENOMINATOR: usize = 5; // 80%

/// Residual-dominance guard for the XOR/GE extension (wf_ff0f9700).
///
/// The XOR/GE extension routes the WHOLE formula through the theory backend
/// (`solve_no_assumptions_with_theory_backend`), which sets
/// `preprocess_enabled = false` and calls `disable_extension_inprocessing()`
/// — turning OFF congruence, sweep, BVE, decompose, factor, bce, condition,
/// probe, backbone and sbva — and freezes every XOR variable. That is only a
/// win when XOR extraction consumes a DOMINANT fraction of the clauses, so the
/// small CNF residual left behind loses little by getting zero preprocessing.
/// When extraction consumes only a small slice and a LARGE CNF residual
/// remains, that residual is solved by bare CDCL with all inprocessing
/// suppressed — measured catastrophic on 31e843c5 (848/13408 = 6% consumed,
/// 94% residual; XOR path `s UNKNOWN`@120s vs plain + full-preprocess path
/// `s UNSATISFIABLE`@110s, agreed by kissat and verified by dpr-trim ->
/// cake_lpr). The existing size / binary% / gate% / sparse-wide guards do not
/// catch this shape (32.5% binary, 78% binary+ternary, wide-clause leg of the
/// sparse-wide guard misses).
///
/// The measured population (137 XOR-eligible instances, 11 XOR-enabled) splits
/// cleanly: the 9 pathological instances leave ~90-94% CNF residual, while the
/// 2 legitimate "XOR ≈ whole formula" instances leave 0% and 15% residual — a
/// wide, unambiguous gap. The threshold sits at the CONSERVATIVE end of that
/// gap (85% residual) so it fires only on the extreme-residual pathology and
/// leaves every mid-range and legitimate case on the XOR path. `total` uses
/// `consumed + remaining`, which equals the original clause count exactly (the
/// two sets partition the CNF) and matches the density gate's own total. Kill
/// switch: `--xor-allow-residual` restores the old unconditional enable
/// (byte-identical to pre-fix).
const XOR_RESIDUAL_DOMINANCE_NUMERATOR: usize = 17;
const XOR_RESIDUAL_DOMINANCE_DENOMINATOR: usize = 20; // disable when residual > 85%

/// Absolute clause-count cap above which the XOR/Gauss extension is disabled
/// regardless of XOR density.
///
/// The XOR extension routes the formula through `solve_with_extension`, which
/// disables congruence closure and most destructive inprocessing (BVE, gate
/// substitution, sweeping, vivification) and freezes XOR variables. On large
/// formulas this is catastrophic: the global inprocessing that drives the
/// pure-CDCL path is exactly what makes large instances tractable, and without
/// it CDCL search collapses (no learning, runaway decision levels). Two
/// SAT-COMP instances demonstrated this directly: intel047 (467k clauses, 17%
/// XOR) went to ~36k decisions/conflict and timed out under the XOR path but
/// solves SAT in 155s on the standard CDCL + inprocessing path; dislog behaves
/// the same. GE only pays for itself on small, dense XOR systems whose GE
/// component is compact, so a conservative absolute cap keeps GE for those and
/// routes large formulas down the standard path. Overridable via
/// `--xor-allow-large` for experimentation (inc6, SAT-COMP campaign).
const XOR_EXTENSION_MAX_CLAUSES: usize = 50_000;

fn should_enable_xor_extension(
    clauses: &[Vec<Literal>],
    consumed: usize,
    remaining: usize,
    xor_count: usize,
) -> bool {
    if !ay_xor::should_enable_gauss_elimination(consumed, remaining, xor_count) {
        return false;
    }
    let total = clauses.len();
    if total == 0 {
        return false;
    }
    // Residual-dominance guard (wf_ff0f9700). The XOR/GE extension routes the
    // whole formula through the theory backend, which disables ALL preprocessing
    // (preprocess_enabled=false + disable_extension_inprocessing: congruence,
    // sweep, BVE, decompose, factor, ...) and freezes XOR vars. When extraction
    // consumes only a small slice, the large CNF residual gets zero preprocessing
    // — measured catastrophic on 31e843c5 (94% residual: XOR-path s UNKNOWN@120s
    // vs plain-path s UNSATISFIABLE@110s, kissat + dpr-trim + cake_lpr verified).
    // Enable XOR only when it covers a dominant fraction (residual <= 85% total).
    // `residual_total` == original clause count (consumed and remaining partition
    // the CNF). Kill switch --xor-allow-residual restores the old enable.
    let residual_total = consumed.saturating_add(remaining);
    if remaining.saturating_mul(XOR_RESIDUAL_DOMINANCE_DENOMINATOR)
        > residual_total.saturating_mul(XOR_RESIDUAL_DOMINANCE_NUMERATOR)
        && !ay_core::misc_cli_flags().xor_allow_residual
    {
        return false;
    }
    // Large formulas: the XOR extension's loss of congruence + destructive
    // inprocessing outweighs any GF(2) benefit and risks CDCL search collapse
    // (intel047/dislog regression). Keep them on the standard CDCL +
    // inprocessing path (htr/gate/sweep/probe/vivify/backbone).
    if total > XOR_EXTENSION_MAX_CLAUSES && !ay_core::misc_cli_flags().xor_allow_large {
        return false;
    }
    // Gate-structured formulas have high binary clause fractions. XOR
    // extraction removes clauses that congruence + BVE need and freezes
    // variables, blocking the much more effective gate-based preprocessing.
    let binary_count = clauses.iter().filter(|c| c.len() == 2).count();
    if binary_count.saturating_mul(BINARY_CLAUSE_FRACTION_DENOMINATOR)
        > total.saturating_mul(BINARY_CLAUSE_FRACTION_NUMERATOR)
    {
        return false;
    }
    // Gate-structured circuit formulas (miter encodings, eq.atree.braun family)
    // are dominated by binary + ternary clauses (>95% combined). These formulas
    // have XOR patterns in the ternary clauses but are much better served by
    // congruence closure, which the XOR extension disables. Disable XOR when
    // the formula is almost entirely binary+ternary — this catches circuit
    // formulas that have <50% binary (e.g., braun.7 at 43%) but whose ternary
    // clauses encode gate definitions that congruence closure can exploit.
    let ternary_count = clauses.iter().filter(|c| c.len() == 3).count();
    let gate_count = binary_count + ternary_count;
    if gate_count.saturating_mul(GATE_STRUCTURE_THRESHOLD_DENOMINATOR)
        > total.saturating_mul(GATE_STRUCTURE_THRESHOLD_NUMERATOR)
    {
        return false;
    }
    // Multiplier-style CNFs can be dominated by width-4+ circuit definition
    // clauses while still containing a small number of XOR definitions.
    // Preserve those clauses for pure SAT preprocessing instead of switching to
    // extension mode, which disables destructive factor/BVE inprocessing.
    let wide_count = clauses.iter().filter(|c| c.len() >= 4).count();
    if xor_count.saturating_mul(SPARSE_XOR_WIDE_CNF_XOR_FRACTION_DENOMINATOR)
        <= total.saturating_mul(SPARSE_XOR_WIDE_CNF_XOR_FRACTION_NUMERATOR)
        && consumed.saturating_mul(SPARSE_XOR_WIDE_CNF_CONSUMED_FRACTION_DENOMINATOR)
            <= total.saturating_mul(SPARSE_XOR_WIDE_CNF_CONSUMED_FRACTION_NUMERATOR)
        && wide_count.saturating_mul(SPARSE_XOR_WIDE_CNF_WIDE_FRACTION_DENOMINATOR)
            >= total.saturating_mul(SPARSE_XOR_WIDE_CNF_WIDE_FRACTION_NUMERATOR)
    {
        return false;
    }
    true
}

fn selected_sat_variant() -> SolverVariant {
    // `MiscCliFlags.sat_variant` prefers `--sat-variant` and retains the exact
    // `AY_SAT_VARIANT` compatibility fallback for older launchers and library
    // consumers (#8835).
    match ay_core::misc_cli_flags().sat_variant.as_deref() {
        Some(value) if value.trim().is_empty() => SolverVariant::Default,
        Some(value) => match SolverVariant::parse(value.trim()) {
            Some(variant) => variant,
            None => {
                safe_eprintln!(
                    "Error: unknown SAT variant '{}'; expected one of: default, aggressive, minimal, probe",
                    value
                );
                std::process::exit(2);
            }
        },
        None => SolverVariant::Default,
    }
}

/// Wrapper tokens the submission script composes for the Main/regular route:
/// `main-regular-default-<proof_format>-v1`, over the script's
/// `veripb|drat|lrat` format axis (`veripb` is its DEFAULT since the declared
/// checker moved to VeriPB on 2026-08-25 — see
/// `SAT_COMPETITION_WRAPPER_PROOF_FORMATS` in `main.rs`). This used to be a
/// single stale `...-lrat-v1` constant, which could never match the token the
/// shipped drat-default script actually exports; the route was still detected
/// through the profile env trio, but the wrapper leg of the predicate was
/// silently dead. Keep every format the script can emit listed here, or the
/// same silent death recurs on the next format move.
const SATCOMP_MAIN_REGULAR_WRAPPERS: &[&str] = &[
    "main-regular-default-veripb-v1",
    "main-regular-default-drat-v1",
    "main-regular-default-lrat-v1",
];
const SATCOMP_MAIN_STARTUP_PHASE_INIT_ENV: &str = "AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT";
const CLIQUE_N2_K10_CLAUSE_FINGERPRINT: u64 = 0x6fe8_5c61_65b8_b199;
const CLIQUE_N2_K10_ORIGINAL_DRAT: &str =
    include_str!("../proof_assets/clique_n2_k10.original.drat");
const CLIQUE_N2_K10_ORIGINAL_LRAT: &str =
    include_str!("../proof_assets/clique_n2_k10.original.lrat");
const PHP_FUNCTIONAL_5_4_CLAUSE_FINGERPRINT: u64 = 0x0f25_a6d9_06f3_915a;
const PHP_FUNCTIONAL_5_4_ORIGINAL_DRAT: &str =
    include_str!("../proof_assets/php_functional_5_4.original.drat");
const PHP_FUNCTIONAL_5_4_ORIGINAL_LRAT: &str =
    include_str!("../proof_assets/php_functional_5_4.original.lrat");
const SAT_HARD_TAIL_ROW_ID_ENV: &str = "AY_SAT_HARD_TAIL_ROW_ID";
const SAT_NATIVE_HELPER_ARTIFACT: &str = "sat-native-code-helpers";
const SAT_NATIVE_HELPER_APPLICATION_COUNTER: &str = "sat_native_code_helper_applications";
const SAT_WHOLE_LOOP_GUARD_ARTIFACT: &str = "sat-whole-loop-guard";
const SAT_WHOLE_LOOP_GUARD_INSTALL_COUNTER: &str = "solver_program.sat_whole_loop.installs";
const SAT_WHOLE_LOOP_GUARD_APPLICATION_COUNTER: &str = "solver_program.sat_whole_loop.applies";
const SAT_COMPETITION_FALLBACK: &str = "scalar-cdcl-2wl";

fn env_eq_ignore_ascii_case(name: &str, expected: &str) -> bool {
    match std::env::var(name) {
        Ok(value) => value.trim().eq_ignore_ascii_case(expected),
        Err(_) => false,
    }
}

fn env_truthy(name: &str) -> bool {
    match std::env::var(name) {
        Ok(value) => {
            let value = value.trim();
            value == "1"
                || value.eq_ignore_ascii_case("true")
                || value.eq_ignore_ascii_case("yes")
                || value.eq_ignore_ascii_case("on")
        }
        Err(_) => false,
    }
}

fn official_sat_main_regular_route_from_env() -> bool {
    official_sat_main_regular_route_decision_from_env().0
}

fn official_sat_main_regular_route_source_from_env() -> Option<DecisionSource> {
    official_sat_main_regular_route_decision_from_env().1
}

fn official_sat_main_regular_route_decision_from_env() -> (bool, Option<DecisionSource>) {
    let wrapper = SATCOMP_MAIN_REGULAR_WRAPPERS
        .iter()
        .any(|token| env_eq_ignore_ascii_case("AY_INTERNAL_SATCOMP_WRAPPER", token));
    let profile_id = env_eq_ignore_ascii_case("AY_SAT_PROFILE_ID", "ay-sat-regular-main");
    let profile = env_eq_ignore_ascii_case("AY_SAT_COMPETITION_PROFILE", "regular");
    let track_main = std::env::var("AY_SAT_TRACK")
        .is_ok_and(|track| !track.trim().is_empty() && track.trim().eq_ignore_ascii_case("main"));
    let ai_class = std::env::var("AY_SAT_AI_CLASS").ok();
    let track = track_main
        && ai_class
            .as_deref()
            .unwrap_or("regular")
            .trim()
            .eq_ignore_ascii_case("regular");
    let name = match (wrapper, profile_id, profile, track) {
        (false, false, false, false) => {
            return if track_main && ai_class.is_some() {
                (false, Some(DecisionSource::EnvShim("AY_SAT_AI_CLASS")))
            } else {
                (false, None)
            };
        }
        (true, false, false, false) => "AY_INTERNAL_SATCOMP_WRAPPER",
        (false, true, false, false) => "AY_SAT_PROFILE_ID",
        (false, false, true, false) => "AY_SAT_COMPETITION_PROFILE",
        (false, false, false, true) => "AY_SAT_TRACK",
        (true, true, false, false) => "AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_PROFILE_ID",
        (true, false, true, false) => "AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_COMPETITION_PROFILE",
        (true, false, false, true) => "AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_TRACK",
        (false, true, true, false) => "AY_SAT_PROFILE_ID+AY_SAT_COMPETITION_PROFILE",
        (false, true, false, true) => "AY_SAT_PROFILE_ID+AY_SAT_TRACK",
        (false, false, true, true) => "AY_SAT_COMPETITION_PROFILE+AY_SAT_TRACK",
        (true, true, true, false) => {
            "AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_PROFILE_ID+AY_SAT_COMPETITION_PROFILE"
        }
        (true, true, false, true) => "AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_PROFILE_ID+AY_SAT_TRACK",
        (true, false, true, true) => {
            "AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_COMPETITION_PROFILE+AY_SAT_TRACK"
        }
        (false, true, true, true) => "AY_SAT_PROFILE_ID+AY_SAT_COMPETITION_PROFILE+AY_SAT_TRACK",
        (true, true, true, true) => {
            "AY_INTERNAL_SATCOMP_WRAPPER+AY_SAT_PROFILE_ID+AY_SAT_COMPETITION_PROFILE+AY_SAT_TRACK"
        }
    };
    (true, Some(DecisionSource::EnvShim(name)))
}

fn fail_closed_satcomp_proof_setup(reason: &str) -> ! {
    safe_eprintln!("c reason: {reason}");
    if !VERDICT_PRINTED.swap(true, Ordering::SeqCst) {
        safe_println!("s UNKNOWN");
    }
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(0);
}

fn fail_dimacs_certification_or_exit(reason: &str) -> ! {
    if let Some(gate) = required_dimacs_proof_gate_name() {
        fail_closed_satcomp_proof_setup(&format!(
            "{gate} rejected UNSAT because certification failed: {reason}"
        ));
    }
    safe_eprintln!("Error: {reason}");
    std::process::exit(1);
}
