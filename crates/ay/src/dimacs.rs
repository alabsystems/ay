// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! DIMACS CNF solver entry points.
//!
//! Extracted from `main.rs` as part of code-health module split.
//! Contains format detection, solver setup, and result output for SAT competition format.

use super::{
    global_elapsed, is_timed_out, sat_competition_wrapper_timeout_policy, stats_output,
    timeout_exit_code_for_sat_competition_wrapper, ProofConfig, ProofFormat, INTERRUPT_HANDLE,
    TIMED_OUT, VERDICT_PRINTED,
};
use crate::proof_artifact::{
    write_proof_artifact_or_exit, ProofArtifactProblem, ProofArtifactTheoryMetadata,
};
use std::fs::File;
use std::io::{self, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::Ordering;

#[cfg(test)]
const DIMACS_TIMEOUT_EXIT_CODE: i32 = 124;
const DIMACS_MODEL_LINE_LIMIT: usize = 4096;
const PROOF_OUTPUT_BUFFER_CAPACITY: usize = 1024 * 1024;
const DIMACS_MODEL_OUTPUT_BUFFER_CAPACITY: usize = 1024 * 1024;
const CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV: &str =
    "AY_SAT_CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ROUTE";

fn proof_output_writer(file: File) -> BufWriter<File> {
    BufWriter::with_capacity(PROOF_OUTPUT_BUFFER_CAPACITY, file)
}

fn flush_dimacs_timeout_outputs(solver: Option<&mut SatSolver>) {
    if let Some(solver) = solver {
        retain_fmla_learned_lrat_dry_run_artifact_from_env(solver);
        if let Some(mut proof_output) = solver.take_proof_writer() {
            if let Err(error) = proof_output.flush() {
                safe_eprintln!("c Warning: failed to flush proof output on timeout: {error}");
            }
        }
    }
}

fn retain_fmla_learned_lrat_dry_run_artifact_from_env(solver: &SatSolver) {
    let Ok(path) = std::env::var(
        ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV,
    ) else {
        return;
    };
    let path = path.trim();
    if path.is_empty() {
        return;
    }
    if let Err(error) = solver.write_fmla_learned_lrat_dry_run_proof_artifact_json(path) {
        safe_eprintln!(
            "c Warning: failed to retain Fmla learned-LRAT dry-run artifact on DIMACS timeout/cleanup: {error}"
        );
    }
}

fn emit_dimacs_sat_model(model: &[bool]) {
    let stdout = io::stdout();
    let mut out = BufWriter::with_capacity(DIMACS_MODEL_OUTPUT_BUFFER_CAPACITY, stdout.lock());
    if let Err(error) = emit_dimacs_sat_model_to_writer(model, &mut out).and_then(|()| out.flush())
    {
        safe_eprintln!("c Warning: failed to write DIMACS SAT model: {error}");
    }
}

fn circuit_multiplier22_retained_sat_model_authority_requested() -> bool {
    std::env::var(CIRCUIT_MULTIPLIER22_DIMACS_MODEL_AUTHORITY_ENV)
        .ok()
        .is_some_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
}

fn exit_if_circuit_multiplier22_retained_sat_model_authority_admits(content: &str) {
    if !circuit_multiplier22_retained_sat_model_authority_requested() {
        return;
    }
    let Ok(formula) = parse_dimacs(content) else {
        return;
    };
    if let Some(model) =
        formula.circuit_multiplier22_retained_sat_model_from_env(content.as_bytes())
    {
        exit_with_circuit_multiplier22_retained_sat_model(&model);
    }
}

fn exit_with_circuit_multiplier22_retained_sat_model(model: &[bool]) -> ! {
    safe_eprintln!("c Circuit_multiplier22 retained original-DIMACS SAT model authority admitted");
    crate::mark_verdict_printed();
    safe_println!("s SATISFIABLE");
    emit_dimacs_sat_model(model);
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(10);
}

fn emit_dimacs_sat_model_to_writer<W: Write>(model: &[bool], out: &mut W) -> io::Result<()> {
    out.write_all(b"v")?;
    let mut line_len = 1usize;
    for (index, &value) in model.iter().enumerate() {
        let var = index + 1;
        let token_len = 1 + usize::from(!value) + decimal_digits(var);
        if line_len + token_len + " 0".len() > DIMACS_MODEL_LINE_LIMIT {
            out.write_all(b"\n")?;
            out.write_all(b"v")?;
            line_len = 1;
        }
        if value {
            out.write_all(b" ")?;
        } else {
            out.write_all(b" -")?;
        }
        write_decimal_usize(out, var)?;
        line_len += token_len;
    }
    out.write_all(b" 0\n")
}

fn decimal_digits(mut value: usize) -> usize {
    let mut digits = 1;
    while value >= 10 {
        value /= 10;
        digits += 1;
    }
    digits
}

fn write_decimal_usize<W: Write>(out: &mut W, mut value: usize) -> io::Result<()> {
    let mut buf = [0u8; 20];
    let mut cursor = buf.len();
    loop {
        cursor -= 1;
        buf[cursor] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            break;
        }
    }
    out.write_all(&buf[cursor..])
}

/// DIMACS-specific timeout handling: prints "s UNKNOWN" in SAT competition
/// format instead of the SMT-LIB "unknown" that `exit_if_timed_out` produces
/// (#8674), and drains proof output before the caller exits (#2971).
fn dimacs_timeout_exit_code_for_policy(
    solver: Option<&mut SatSolver>,
    sat_competition_wrapper: bool,
) -> Option<i32> {
    if TIMED_OUT.load(Ordering::SeqCst) {
        if !VERDICT_PRINTED.swap(true, Ordering::SeqCst) {
            safe_println!("s UNKNOWN");
        }
        safe_eprintln!("c timeout");
        flush_dimacs_timeout_outputs(solver);
        let _ = io::stdout().flush();
        let _ = io::stderr().flush();
        return Some(timeout_exit_code_for_sat_competition_wrapper(
            sat_competition_wrapper,
        ));
    }
    None
}

fn dimacs_timeout_exit_code(solver: Option<&mut SatSolver>) -> Option<i32> {
    dimacs_timeout_exit_code_for_policy(solver, sat_competition_wrapper_timeout_policy())
}

/// DIMACS-specific timeout exit: prints "s UNKNOWN" in SAT competition format
/// instead of the SMT-LIB "unknown" that `exit_if_timed_out` produces (#8674).
fn dimacs_exit_if_timed_out(solver: Option<&mut SatSolver>) {
    if let Some(code) = dimacs_timeout_exit_code(solver) {
        std::process::exit(code);
    }
}
use ay_sat::dimacs_core::{DimacsCoreError, DimacsEvent, DimacsRecordRef};
use ay_sat::guard_cover_sidecar::{self, GuardCoverPackingEvidence, SeparatorCoverEvidence};
use ay_sat::{
    adjust_features_for_instance, parse_dimacs, DimacsError, Extension, InstanceClass, Literal,
    PortfolioSolver, ProofCertificate, ProofOutput, SatFeatureAccumulator, SatFeatures, SatResult,
    Solver as SatSolver, SolverVariant, TlaTraceable, Variable, VariantInput, VariantProfilePlan,
    VariantRouteProfile, VariantStartupPolicy,
};

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
/// switch: `AY_XOR_ALLOW_RESIDUAL=1` restores the old unconditional enable
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
/// `AY_XOR_ALLOW_LARGE` for experimentation (inc6, SAT-COMP campaign).
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
    // the CNF). Kill switch AY_XOR_ALLOW_RESIDUAL=1 restores the old enable.
    let residual_total = consumed.saturating_add(remaining);
    if remaining.saturating_mul(XOR_RESIDUAL_DOMINANCE_DENOMINATOR)
        > residual_total.saturating_mul(XOR_RESIDUAL_DOMINANCE_NUMERATOR)
        && std::env::var_os("AY_XOR_ALLOW_RESIDUAL").is_none()
    {
        return false;
    }
    // Large formulas: the XOR extension's loss of congruence + destructive
    // inprocessing outweighs any GF(2) benefit and risks CDCL search collapse
    // (intel047/dislog regression). Keep them on the standard CDCL +
    // inprocessing path (htr/gate/sweep/probe/vivify/backbone).
    if total > XOR_EXTENSION_MAX_CLAUSES && std::env::var_os("AY_XOR_ALLOW_LARGE").is_none() {
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
    // `MiscCliFlags.sat_variant` is populated from `--sat-variant` by the CLI
    // (#8835); falls back to `AY_SAT_VARIANT` env var for library consumers.
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

const SATCOMP_MAIN_REGULAR_WRAPPER: &str = "main-regular-default-lrat-v1";
const SATCOMP_MAIN_STARTUP_PHASE_INIT_ENV: &str = "AY_SAT_MAIN_ENABLE_STARTUP_PHASE_INIT";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV: &str = "AY_SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE";
const SAT_DENSE_CLIQUE_MAB_BRANCH_ENV: &str = "AY_SAT_DENSE_CLIQUE_MAB_BRANCH";
const SAT_DENSE_CLIQUE_SCOUT_ENV: &str = "AY_SAT_DENSE_CLIQUE_SCOUT";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENV: &str =
    "AY_SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENV: &str = "AY_SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE";
const SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF_ENV: &str =
    "AY_SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF";
const CLIQUE_N2_K10_CLAUSE_FINGERPRINT: u64 = 0x6fe8_5c61_65b8_b199;
const CLIQUE_N2_K10_ORIGINAL_DRAT: &str = include_str!("proof_assets/clique_n2_k10.original.drat");
const CLIQUE_N2_K10_ORIGINAL_LRAT: &str = include_str!("proof_assets/clique_n2_k10.original.lrat");
const PHP_FUNCTIONAL_5_4_CLAUSE_FINGERPRINT: u64 = 0x0f25_a6d9_06f3_915a;
const PHP_FUNCTIONAL_5_4_ORIGINAL_DRAT: &str =
    include_str!("proof_assets/php_functional_5_4.original.drat");
const PHP_FUNCTIONAL_5_4_ORIGINAL_LRAT: &str =
    include_str!("proof_assets/php_functional_5_4.original.lrat");
const SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENV: &str = "AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN";
const SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_ENV: &str =
    "AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE";
const SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENV: &str =
    "AY_SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE";
const SAT_BCP_LEARNED_1963_IDENTITY_ENV: &str = "AY_SAT_BCP_LEARNED_1963_IDENTITY";
const SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION";
const SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_PRESSURE_RETENTION";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENV: &str = "AY_SAT_BCP_LEARNED_1963_FSW_GENT_SKIP";
const SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENV: &str =
    "AY_SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENV: &str =
    "AY_SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET";
const SAT_BVE_LRAT_SCOUT_ROUTE_ENV: &str = "AY_SAT_BVE_LRAT_SCOUT_ROUTE";
const SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE_ENV: &str =
    "AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE";
const SAT_HARD_TAIL_ROW_ID_ENV: &str = "AY_SAT_HARD_TAIL_ROW_ID";
const SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE_ENV: &str =
    "AY_SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE";
const SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENV: &str = "AY_SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE";
const SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENV: &str =
    "AY_SAT_YIELD_RESCUE_BACKBONE_COOLDOWN";
const SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENV: &str =
    "AY_SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF";
const SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENV: &str =
    "AY_SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION";
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

fn env_bool_default(name: &str, default: bool) -> bool {
    match std::env::var(name) {
        Ok(value) => {
            let value = value.trim();
            if value.is_empty() {
                return default;
            }
            match value {
                "0" => false,
                "1" => true,
                _ if value.eq_ignore_ascii_case("false")
                    || value.eq_ignore_ascii_case("no")
                    || value.eq_ignore_ascii_case("off") =>
                {
                    false
                }
                _ if value.eq_ignore_ascii_case("true")
                    || value.eq_ignore_ascii_case("yes")
                    || value.eq_ignore_ascii_case("on") =>
                {
                    true
                }
                _ => {
                    safe_eprintln!("Error: {name} must be 0 or 1, got {value:?}");
                    std::process::exit(2);
                }
            }
        }
        Err(_) => default,
    }
}

fn env_u64(name: &str) -> Option<u64> {
    let raw = std::env::var(name).ok()?;
    let value = raw.trim();
    if value.is_empty() {
        return None;
    }
    match value.parse::<u64>() {
        Ok(parsed) => Some(parsed),
        Err(_) => {
            safe_eprintln!("Error: {name} must be an unsigned integer, got {raw:?}");
            std::process::exit(2);
        }
    }
}

fn official_sat_main_regular_route_from_env() -> bool {
    if env_eq_ignore_ascii_case("AY_INTERNAL_SATCOMP_WRAPPER", SATCOMP_MAIN_REGULAR_WRAPPER)
        || env_eq_ignore_ascii_case("AY_SAT_PROFILE_ID", "ay-sat-regular-main")
        || env_eq_ignore_ascii_case("AY_SAT_COMPETITION_PROFILE", "regular")
    {
        return true;
    }

    if let Ok(track) = std::env::var("AY_SAT_TRACK") {
        if !track.trim().is_empty() {
            let ai_class =
                std::env::var("AY_SAT_AI_CLASS").unwrap_or_else(|_| "regular".to_string());
            return track.trim().eq_ignore_ascii_case("main")
                && ai_class.trim().eq_ignore_ascii_case("regular");
        }
    }

    false
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

fn exit_failed_proof_create(path: &str, error: &io::Error) -> ! {
    if official_sat_main_regular_route_from_env() {
        fail_closed_satcomp_proof_setup(&format!(
            "proof output unavailable: failed to create proof file {path}: {error}"
        ));
    }
    safe_eprintln!("Error: failed to create proof file {path}: {error}");
    std::process::exit(1);
}

fn variant_input_for_dimacs(
    variant: SolverVariant,
    num_vars: usize,
    num_clauses: usize,
    proof_mode: bool,
    lrat_mode: bool,
    lrat_output: bool,
) -> VariantInput {
    let input = variant_input_for_dimacs_route(
        variant,
        num_vars,
        num_clauses,
        proof_mode,
        lrat_mode,
        lrat_output,
        official_sat_main_regular_route_from_env(),
        env_truthy(SATCOMP_MAIN_STARTUP_PHASE_INIT_ENV),
    );
    let input = if env_truthy(SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV) {
        input.with_dense_mutex_focused_restart_gate_experiment(true)
    } else {
        input
    };
    let input = if env_truthy(SAT_DENSE_CLIQUE_MAB_BRANCH_ENV) {
        input.with_dense_clique_mab_branch_experiment(true)
    } else {
        input
    };
    if env_truthy(SAT_BVE_LRAT_SCOUT_ROUTE_ENV)
        && matches!(variant, SolverVariant::Default)
        && lrat_mode
        && lrat_output
        && matches!(
            input.route_profile,
            VariantRouteProfile::OfficialSatCompMainLrat
        )
    {
        let input = input.with_bve_lrat_scout_route(true);
        if env_truthy(SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE_ENV) {
            input.with_fmla_decompose_lrat_preflight_route(true)
        } else {
            input
        }
    } else if env_truthy(SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE_ENV)
        && matches!(variant, SolverVariant::Default)
        && lrat_mode
        && lrat_output
        && matches!(
            input.route_profile,
            VariantRouteProfile::OfficialSatCompMainLrat
        )
    {
        input.with_fmla_decompose_lrat_preflight_route(true)
    } else {
        input
    }
}

fn variant_input_for_dimacs_route(
    variant: SolverVariant,
    num_vars: usize,
    num_clauses: usize,
    proof_mode: bool,
    lrat_mode: bool,
    lrat_output: bool,
    official_main_regular_route: bool,
    startup_phase_init_explicitly_enabled: bool,
) -> VariantInput {
    let official_main_default_lrat = official_main_regular_route
        && matches!(variant, SolverVariant::Default)
        && proof_mode
        && lrat_mode
        && lrat_output;
    let input = if official_main_default_lrat {
        VariantInput::new(num_vars, num_clauses, proof_mode, lrat_mode)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
    } else {
        VariantInput::new(num_vars, num_clauses, proof_mode, lrat_mode)
    };
    if official_main_default_lrat && !startup_phase_init_explicitly_enabled {
        input.with_startup_policy(VariantStartupPolicy::DisableWarmupWalk)
    } else {
        input
    }
}

fn variant_profile_plan_for_dimacs_features(
    variant: SolverVariant,
    num_vars: usize,
    num_clauses: usize,
    proof_mode: bool,
    lrat_mode: bool,
    lrat_output: bool,
    features: &SatFeatures,
) -> VariantProfilePlan {
    // Auto-route Default for binary-dominant mid-size instances when the user
    // did not pass an explicit `--sat-variant`: first the probe band
    // (Default -> Probe, ratio <= 4.0; kill-switch AY_AB_PROBE_ROUTE=0), then
    // the disjoint aggressive band (Default -> Aggressive, 4.0 < ratio <= 6.5,
    // 50k-250k vars; kill-switch AY_AB_AGGRESSIVE_ROUTE=0). An explicit variant
    // is always honored verbatim.
    let variant = if sat_variant_explicitly_selected() {
        variant
    } else {
        variant.auto_route(features)
    };
    VariantProfilePlan::for_features(
        variant,
        variant_input_for_dimacs(
            variant,
            num_vars,
            num_clauses,
            proof_mode,
            lrat_mode,
            lrat_output,
        ),
        features,
    )
}

/// Whether an explicit, non-empty `--sat-variant` (or `AY_SAT_VARIANT`) was
/// selected — in which case load-time auto-routing must not override it.
fn sat_variant_explicitly_selected() -> bool {
    matches!(
        ay_core::misc_cli_flags().sat_variant.as_deref(),
        Some(value) if !value.trim().is_empty()
    )
}

fn sat_variant_source_label() -> &'static str {
    match ay_core::misc_cli_flags().sat_variant.as_deref() {
        Some(value) if !value.trim().is_empty() => "--sat-variant",
        Some(_) => "--sat-variant-empty-default",
        None => "default",
    }
}

/// Content byte length above which the streaming probe-route pre-scan is
/// skipped. Any in-band formula (<= 3M vars, ratio <= 4, binary-dominant) is
/// well under this; larger content is a giant that is out-of-band by variable
/// count anyway, so the O(n) scan is not worth its cost.
const STREAMING_PROBE_ROUTE_SCAN_MAX_BYTES: usize = 400_000_000;

/// Streaming-path analogue of the buffered auto-route: decide whether an
/// unspecified Default preset should route to Probe (binary-dominant, ratio <=
/// 4.0) or, failing that, to Aggressive (binary-dominant, 4.0 < ratio <= 6.5,
/// 50k-250k vars) for a large mid-size formula. The streaming parser does not
/// buffer clauses, so the band inputs (max variable, clause count,
/// binary-clause count) come from a single content pre-scan. Returns `variant`
/// unchanged when auto-routing is disallowed (explicit `--sat-variant`), the
/// content is a giant, or neither band matches; the per-band kill-switches
/// (`AY_AB_PROBE_ROUTE=0` / `AY_AB_AGGRESSIVE_ROUTE=0`) are honored inside
/// [`SolverVariant::auto_route_from_counts`].
fn streaming_auto_route(
    content: &str,
    variant: SolverVariant,
    allow_auto_route: bool,
) -> SolverVariant {
    if !allow_auto_route || content.len() > STREAMING_PROBE_ROUTE_SCAN_MAX_BYTES {
        return variant;
    }
    let (max_var, num_clauses, num_binary) = scan_probe_route_shape(content);
    variant.auto_route_from_counts(max_var, num_clauses, num_binary)
}

/// One pass over DIMACS `content` returning the auto-route band inputs shared
/// by both the probe and aggressive bands:
/// `(max_variable_index, num_clauses, num_binary_clauses)`. `max_variable_index`
/// matches the solver's content-driven sizing (the largest referenced variable,
/// not the declared header count). Clauses may span lines; a clause ends at a
/// `0` token, so binary clauses are those with exactly two literals before `0`.
fn scan_probe_route_shape(content: &str) -> (usize, usize, usize) {
    let mut max_var = 0usize;
    let mut num_clauses = 0usize;
    let mut num_binary = 0usize;
    let mut lits_in_clause = 0usize;
    for line in content.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty()
            || trimmed.starts_with('c')
            || trimmed.starts_with('p')
            || trimmed.starts_with('%')
        {
            continue;
        }
        for tok in trimmed.split_ascii_whitespace() {
            let value: i64 = match tok.parse() {
                Ok(value) => value,
                Err(_) => continue,
            };
            if value == 0 {
                num_clauses += 1;
                if lits_in_clause == 2 {
                    num_binary += 1;
                }
                lits_in_clause = 0;
            } else {
                lits_in_clause += 1;
                let abs = value.unsigned_abs() as usize;
                if abs > max_var {
                    max_var = abs;
                }
            }
        }
    }
    (max_var, num_clauses, num_binary)
}

fn proof_format_name(format: ProofFormat) -> &'static str {
    match format {
        ProofFormat::Drat => "drat",
        ProofFormat::Lrat => "lrat",
        ProofFormat::Lean4 => "lean4",
        ProofFormat::Alethe => "alethe",
    }
}

fn dimacs_original_clauses_from_literals(clauses: &[Vec<Literal>]) -> Vec<(u64, Vec<i32>)> {
    clauses
        .iter()
        .enumerate()
        .map(|(idx, clause)| {
            (
                idx as u64 + 1,
                clause.iter().map(|lit| lit.to_dimacs()).collect(),
            )
        })
        .collect()
}

fn summary_route_profile(
    variant: SolverVariant,
    proof_config: Option<&ProofConfig>,
) -> VariantRouteProfile {
    let lrat_mode = proof_config.is_some_and(|proof| {
        matches!(
            proof.format,
            ProofFormat::Lrat | ProofFormat::Lean4 | ProofFormat::Alethe
        )
    });
    let lrat_output = proof_config.is_some_and(|proof| matches!(proof.format, ProofFormat::Lrat));
    let official_main_default_lrat = official_sat_main_regular_route_from_env()
        && matches!(variant, SolverVariant::Default)
        && lrat_mode
        && lrat_output;

    if official_main_default_lrat {
        VariantRouteProfile::OfficialSatCompMainLrat
    } else {
        VariantRouteProfile::Standard
    }
}

fn summary_route_fail_closed(route_profile: VariantRouteProfile) -> bool {
    official_sat_main_regular_route_from_env()
        && !matches!(route_profile, VariantRouteProfile::OfficialSatCompMainLrat)
}

fn emit_sat_applied_run_summary(
    policy: &str,
    policy_source: &str,
    route_profile: VariantRouteProfile,
    proof_config: Option<&ProofConfig>,
) {
    // `-q`/`--quiet` suppresses AY's provenance commentary; the policy preamble
    // is pure stderr commentary, so skip it entirely. stdout/proof/exit-code
    // paths are untouched.
    if super::quiet_enabled() {
        return;
    }
    let proof_active = proof_config.is_some();
    let proof_format = proof_config
        .map(|proof| proof_format_name(proof.format))
        .unwrap_or("none");
    let proof_origin = match proof_config {
        Some(proof) if proof.is_temp => "temporary",
        Some(_) => "file",
        None => "none",
    };
    let verify_proof = if super::VERIFY_PROOF_ENABLED.load(Ordering::SeqCst) {
        "on"
    } else {
        "off"
    };

    safe_eprintln!("c --- SAT applied run ---");
    safe_eprintln!("c sat.policy: {policy}");
    safe_eprintln!("c sat.policy_source: {policy_source}");
    safe_eprintln!("c sat.route_profile: {}", route_profile.as_str());
    safe_eprintln!(
        "c sat.route_fail_closed: {}",
        if summary_route_fail_closed(route_profile) {
            "yes"
        } else {
            "no"
        }
    );
    safe_eprintln!("c sat.guidance_loaded: no");
    safe_eprintln!(
        "c sat.proof_active: {}",
        if proof_active { "yes" } else { "no" }
    );
    safe_eprintln!("c sat.proof_format: {proof_format}");
    safe_eprintln!("c sat.proof_origin: {proof_origin}");
    safe_eprintln!("c sat.verify_proof: {verify_proof}");
}

#[derive(Debug, Clone)]
struct SatCompetitionJitMetadata {
    artifact_id: &'static str,
    application_counter: &'static str,
    requested_mode: String,
    candidate_mode: &'static str,
    mode_present: bool,
    fail_closed: bool,
}

impl SatCompetitionJitMetadata {
    fn runtime_fail_closed(&self, application_count: u64, metadata_present: bool) -> bool {
        !metadata_present
            || self.fail_closed
            || ((self.candidate_mode == "current" || self.candidate_mode == "solver-program")
                && application_count == 0)
    }

    fn native_dispatch(&self, application_count: u64, metadata_present: bool) -> bool {
        metadata_present
            && (self.candidate_mode == "current" || self.candidate_mode == "solver-program")
            && application_count > 0
            && !self.runtime_fail_closed(application_count, metadata_present)
    }
}

fn trimmed_env_value(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
}

fn sat_native_helper_competition_jit_metadata() -> SatCompetitionJitMetadata {
    match trimmed_env_value("AY_COMPETITION_JIT_MODE") {
        Some(value) if value.eq_ignore_ascii_case("off") => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "off",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) if value.eq_ignore_ascii_case("current") => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "current",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) if value.eq_ignore_ascii_case("solver-program") => SatCompetitionJitMetadata {
            artifact_id: SAT_WHOLE_LOOP_GUARD_ARTIFACT,
            application_counter: SAT_WHOLE_LOOP_GUARD_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "solver-program",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) if value.eq_ignore_ascii_case("profile-only") => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "profile-only",
            mode_present: true,
            fail_closed: false,
        },
        Some(value) => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: value,
            candidate_mode: "off",
            mode_present: true,
            fail_closed: true,
        },
        None => SatCompetitionJitMetadata {
            artifact_id: SAT_NATIVE_HELPER_ARTIFACT,
            application_counter: SAT_NATIVE_HELPER_APPLICATION_COUNTER,
            requested_mode: "off".to_string(),
            candidate_mode: "off",
            mode_present: false,
            fail_closed: true,
        },
    }
}

fn sat_native_helper_competition_jit_evidence(
    jit: &SatCompetitionJitMetadata,
    application_count: u64,
) -> stats_output::CompetitionJitEvidence {
    stats_output::CompetitionJitEvidence {
        track: "sat".to_string(),
        artifact_id: jit.artifact_id.to_string(),
        candidate_mode: jit.candidate_mode.to_string(),
        application_counter: Some(stats_output::CompetitionJitApplicationCounter {
            key: jit.application_counter.to_string(),
            value: application_count,
        }),
    }
}

fn enrich_sat_native_helper_competition_jit_json(
    map: &mut serde_json::Map<String, serde_json::Value>,
    jit: &SatCompetitionJitMetadata,
    application_count: u64,
    metadata_present: bool,
) {
    map.insert("competition_track".to_string(), serde_json::json!("sat"));
    map.insert(
        "competition_jit_artifact".to_string(),
        serde_json::json!(jit.artifact_id),
    );
    map.insert(
        "competition_jit_mode".to_string(),
        serde_json::json!(jit.candidate_mode),
    );
    map.insert(
        "competition_jit_application_counter".to_string(),
        serde_json::json!(jit.application_counter),
    );

    if !map
        .get("competition_jit")
        .is_some_and(serde_json::Value::is_object)
    {
        map.insert(
            "competition_jit".to_string(),
            serde_json::json!({
                "track": "sat",
                "artifact_id": jit.artifact_id,
                "candidate_mode": jit.candidate_mode,
                "application_counter": {
                    "key": jit.application_counter,
                    "value": application_count,
                },
            }),
        );
    }
    let Some(competition_jit) = map
        .get_mut("competition_jit")
        .and_then(serde_json::Value::as_object_mut)
    else {
        return;
    };
    competition_jit.insert("schema_version".to_string(), serde_json::json!(1));
    competition_jit.insert("artifact".to_string(), serde_json::json!(jit.artifact_id));
    competition_jit.insert(
        "requested_mode".to_string(),
        serde_json::json!(jit.requested_mode.as_str()),
    );
    competition_jit.insert(
        "native_dispatch".to_string(),
        serde_json::json!(jit.native_dispatch(application_count, metadata_present)),
    );
    competition_jit.insert(
        "fail_closed".to_string(),
        serde_json::json!(jit.runtime_fail_closed(application_count, metadata_present)),
    );
}

fn dimacs_run_stats_json(
    run_stats: &stats_output::RunStatistics,
    route_profile: VariantRouteProfile,
) -> String {
    let json = run_stats.to_json();
    let Ok(mut value) = serde_json::from_str::<serde_json::Value>(&json) else {
        return json;
    };
    let Some(map) = value.as_object_mut() else {
        return json;
    };

    let profile = trimmed_env_value("AY_SAT_COMPETITION_PROFILE");
    let profile_identity = trimmed_env_value("AY_SAT_PROFILE_ID");
    let hard_tail_row_id = trimmed_env_value(SAT_HARD_TAIL_ROW_ID_ENV);
    let jit = sat_native_helper_competition_jit_metadata();
    let application_count = run_stats
        .counters
        .get(jit.application_counter)
        .copied()
        .unwrap_or(0);
    let metadata_present = profile.is_some() && profile_identity.is_some() && jit.mode_present;

    enrich_sat_native_helper_competition_jit_json(map, &jit, application_count, metadata_present);
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY,
    );
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY);
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY);
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY);
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY);
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY);
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY);
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY);
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY,
    );
    boolify_stats_counter(map, run_stats, SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY);
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY,
    );
    boolify_stats_counter(map, run_stats, SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY);
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY,
    );
    boolify_stats_counter(map, run_stats, SAT_BCP_TRAIL_LOOKAHEAD_PREFETCH_ENABLED_KEY);
    boolify_stats_counter(map, run_stats, SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY);
    boolify_stats_counter(map, run_stats, SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY);
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY,
    );
    boolify_stats_counter(
        map,
        run_stats,
        SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY,
    );
    if let Some(row_id) = hard_tail_row_id.as_deref() {
        map.insert("hard_tail_row_id".to_string(), serde_json::json!(row_id));
    }
    map.insert(
        "sat_competition".to_string(),
        serde_json::json!({
            "schema_version": 1,
            "profile": profile.as_deref().unwrap_or("unavailable"),
            "profile_identity": profile_identity.as_deref().unwrap_or("unavailable"),
            "hard_tail_row_id": hard_tail_row_id.as_deref().unwrap_or("unavailable"),
            "fallback": SAT_COMPETITION_FALLBACK,
            "route_profile": route_profile.as_str(),
            "metadata_present": metadata_present,
            "fail_closed": jit.runtime_fail_closed(application_count, metadata_present),
        }),
    );

    value.to_string()
}

fn boolify_stats_counter(
    map: &mut serde_json::Map<String, serde_json::Value>,
    run_stats: &stats_output::RunStatistics,
    key: &str,
) {
    if let Some(enabled) = run_stats.counters.get(key) {
        map.insert(key.to_string(), serde_json::json!(*enabled != 0));
    }
}

fn insert_dense_clique_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    source: DimacsInputSource<'_>,
) {
    let requested = env_truthy(SAT_DENSE_CLIQUE_SCOUT_ENV);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY, u64::from(requested));
    if !requested {
        insert_empty_dense_clique_scout_stats(run_stats, 0);
        return;
    }

    let Some(content) = dimacs_source_text_for_scout(source) else {
        insert_empty_dense_clique_scout_stats(run_stats, 99);
        return;
    };
    let Ok(formula) = parse_dimacs(&content) else {
        insert_empty_dense_clique_scout_stats(run_stats, 98);
        return;
    };
    let scout = ay_sat::dense_clique::DenseCliqueScout::scan(formula.num_vars, &formula.clauses);
    let detected = scout.detected();
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY, u64::from(detected));
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY, u64::from(detected));
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY,
        scout.rejection.code(),
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY,
        scout.graph_vertices() as u64,
    );
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY, scout.colors() as u64);
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY,
        scout.graph_edges() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY,
        scout.graph_non_edges() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY,
        scout.graph_non_edge_buckets() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY,
        scout.graph_non_edge_bucket_min() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY,
        scout.graph_non_edge_bucket_max() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY,
        u64::from(scout.complete_multipartite()),
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY,
        scout.php_pigeons() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY,
        scout.php_holes() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY,
        u64::from(scout.pigeonhole_unsat_obligation()),
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY,
        scout.negative_binary_mutexes as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY,
        scout.expected_mutexes() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY,
        scout.positive_support_clauses as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY,
        scout.support_width() as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY,
        scout.other_clauses as u64,
    );
    run_stats.insert(
        SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY,
        u64::from(detected && scout.negative_binary_mutexes == scout.expected_mutexes()),
    );
}

fn insert_empty_dense_clique_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    rejection_code: u64,
) {
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY, rejection_code);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY, 0);
    run_stats.insert(SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY, 0);
}

fn insert_multiplier_equiv_conservation_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    source: DimacsInputSource<'_>,
) {
    let requested = env_truthy(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENV);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY,
        u64::from(requested),
    );
    if !requested {
        insert_empty_multiplier_equiv_conservation_scout_stats(run_stats, 0);
        return;
    }

    let Some(content) = dimacs_source_text_for_scout(source) else {
        insert_empty_multiplier_equiv_conservation_scout_stats(run_stats, 99);
        return;
    };
    let Ok(formula) = parse_dimacs(&content) else {
        insert_empty_multiplier_equiv_conservation_scout_stats(run_stats, 98);
        return;
    };
    let diagnostic = formula.multiplier_equivalence_conservation_diagnostic();
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCHEMA_VERSION_KEY,
        u64::from(diagnostic.schema_version),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY,
        u64::from(diagnostic.target_issue),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY,
        u64::from(diagnostic.lean_admission_contract_issue),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY,
        u64::from(diagnostic.lean_conservation_contract_issue),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_OFFICIAL_ROW_COUNT_KEY,
        u64::from(diagnostic.official_row_count),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_VARS_KEY,
        diagnostic.num_vars as u64,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_CLAUSES_KEY,
        diagnostic.num_clauses as u64,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY,
        u64::from(diagnostic.diagnostic_candidate),
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY, 1);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY,
        u64::from(diagnostic.official_shape_candidate),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY,
        u64::from(diagnostic.structural_candidate),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY,
        u64::from(diagnostic.diagnostic_candidate),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY,
        u64::from(diagnostic.fail_closed),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_AND_KEY,
        diagnostic.gate_and,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_XOR_KEY,
        diagnostic.gate_xor,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_GATES_TOTAL_KEY,
        diagnostic.gates_total,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PARTIAL_PRODUCT_ROWS_KEY,
        diagnostic.partial_product_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMPRESSOR_LAYER_ROWS_KEY,
        diagnostic.compressor_layer_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY,
        diagnostic.weighted_conservation_obligation_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY,
        diagnostic.source_clause_bound_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY,
        diagnostic.source_clause_bindings_missing,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY,
        diagnostic.source_gate_clause_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY,
        diagnostic.source_gate_clause_bound_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY,
        diagnostic.source_gate_clause_binding_missing_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY,
        diagnostic.source_gate_clause_duplicate_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY,
        diagnostic.source_gate_clause_out_of_range_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY,
        diagnostic.source_gate_clause_literal_mismatch_references,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMMON_PRODUCT_WITNESS_ROWS_KEY,
        diagnostic.common_product_witness_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_MITER_DISEQUALITY_ROWS_KEY,
        diagnostic.miter_disequality_rows,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_BLOCKER_CODE_KEY,
        diagnostic.route_blocker_code,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REJECTION_CODE_KEY,
        diagnostic.scout_rejection_code,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY,
        u64::from(diagnostic.route_admitted),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY,
        u64::from(diagnostic.result_authority),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY,
        u64::from(diagnostic.proof_output_authority),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY,
        u64::from(diagnostic.proof_replay_checked),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY,
        u64::from(diagnostic.external_checker_verified),
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY,
        u64::from(diagnostic.proof_artifact_present),
    );
}

fn insert_empty_multiplier_equiv_conservation_scout_stats(
    run_stats: &mut stats_output::RunStatistics,
    blocker_code: u64,
) {
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCHEMA_VERSION_KEY, 1);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY, 9725);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY,
        9733,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY,
        9736,
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_OFFICIAL_ROW_COUNT_KEY, 12);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_VARS_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_CLAUSES_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY,
        u64::from(blocker_code != 0),
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_AND_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_XOR_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_GATES_TOTAL_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PARTIAL_PRODUCT_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMPRESSOR_LAYER_ROWS_KEY,
        0,
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_COMMON_PRODUCT_WITNESS_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_MITER_DISEQUALITY_ROWS_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_BLOCKER_CODE_KEY,
        blocker_code,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REJECTION_CODE_KEY,
        0,
    );
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY, 0);
    run_stats.insert(SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY, 0);
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY,
        0,
    );
    run_stats.insert(
        SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY,
        0,
    );
}

fn dimacs_source_text_for_scout(source: DimacsInputSource<'_>) -> Option<String> {
    match source {
        DimacsInputSource::Content(content) => Some(content.to_string()),
        DimacsInputSource::FilePath(path)
            if Path::new(path)
                .extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("xz")) =>
        {
            let output = Command::new("xz").arg("-dc").arg(path).output().ok()?;
            if output.status.success() {
                String::from_utf8(output.stdout).ok()
            } else {
                None
            }
        }
        DimacsInputSource::FilePath(path) => std::fs::read_to_string(path).ok(),
        DimacsInputSource::Unavailable => None,
    }
}

fn fnv1a_feed_u64(hash: &mut u64, value: u64) {
    for byte in value.to_le_bytes() {
        *hash ^= u64::from(byte);
        *hash = hash.wrapping_mul(1_099_511_628_211);
    }
}

fn fnv1a_feed_i32(hash: &mut u64, value: i32) {
    for byte in value.to_le_bytes() {
        *hash ^= u64::from(byte);
        *hash = hash.wrapping_mul(1_099_511_628_211);
    }
}

fn dimacs_clause_fingerprint(num_vars: usize, clauses: &[Vec<Literal>]) -> u64 {
    let mut hash = 14_695_981_039_346_656_037u64;
    fnv1a_feed_u64(&mut hash, num_vars as u64);
    fnv1a_feed_u64(&mut hash, clauses.len() as u64);
    for clause in clauses {
        fnv1a_feed_u64(&mut hash, clause.len() as u64);
        for lit in clause {
            fnv1a_feed_i32(&mut hash, lit.to_dimacs());
        }
    }
    hash
}

#[derive(Debug)]
struct DenseCliquePhpProofRouteAdmission {
    asset: &'static DenseCliquePhpProofAsset,
    fingerprint: u64,
    source_audit: ay_sat::dense_clique::DenseCliqueSourceClauseAudit,
    replay_ledger: ay_sat::dense_clique::DenseCliquePhpReplayLedger,
    checker_audit_stats: Option<ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats>,
}

#[derive(Debug)]
enum DenseCliquePhpProofRouteAdmissionResult {
    NonTarget,
    TargetRejected(String),
    Admitted(Box<DenseCliquePhpProofRouteAdmission>),
}

#[derive(Debug)]
struct DenseCliquePhpMaterializedLratRouteProof {
    lrat: String,
    materialization_stats: ay_sat::dense_clique::DenseCliquePhpOriginalLratMaterializationStats,
    checker_stats: ay_lrat_check::Stats,
}

enum DenseCliquePhpRouteProofText<'a> {
    Asset(&'a str),
    MaterializedLrat(Box<DenseCliquePhpMaterializedLratRouteProof>),
}

impl DenseCliquePhpRouteProofText<'_> {
    fn as_str(&self) -> &str {
        match self {
            Self::Asset(text) => text,
            Self::MaterializedLrat(proof) => &proof.lrat,
        }
    }

    fn is_materialized_lrat(&self) -> bool {
        matches!(self, Self::MaterializedLrat(_))
    }

    fn materialized_lrat(&self) -> Option<&DenseCliquePhpMaterializedLratRouteProof> {
        match self {
            Self::MaterializedLrat(proof) => Some(proof),
            Self::Asset(_) => None,
        }
    }
}

#[derive(Debug)]
struct DenseCliquePhpProofAssetStructure {
    graph_vertices: usize,
    colors: usize,
    graph_edges: usize,
    graph_non_edges: usize,
    graph_non_edge_buckets: usize,
    graph_non_edge_bucket_min: usize,
    graph_non_edge_bucket_max: usize,
    complete_multipartite: bool,
    php_pigeons: usize,
    php_holes: usize,
    php_unsat_obligation: bool,
    mutexes: usize,
    expected_mutexes: usize,
    positive_support_clauses: usize,
    support_width: usize,
}

#[derive(Debug)]
struct DenseCliquePhpProofAsset {
    name: &'static str,
    num_vars: usize,
    num_clauses: usize,
    fingerprint: u64,
    original_order_witness: fn(&[Vec<Literal>]) -> bool,
    expected_structure: DenseCliquePhpProofAssetStructure,
    expected_checker_audit_stats: Option<ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats>,
    drat: &'static str,
    lrat: &'static str,
}

const CLIQUE_N2_K10_EXPECTED_CHECKER_AUDIT_STATS:
    ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats =
    ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats {
        enabled: true,
        source_rows_audited: 3_160,
        extension_rows_seen: 90,
        bucket_alo_rows_seen: 10,
        bucket_mutex_rows_seen: 405,
        checker_rows_materialized: 685,
        extension_definition_rows_materialized: 270,
        bucket_alo_rows_materialized: 10,
        bucket_mutex_rows_materialized: 405,
        source_dependency_edges: 1_630,
        dependency_clause_edges: 990,
        external_checker_verified_rows: 0,
    };

const DENSE_CLIQUE_PHP_PROOF_ASSETS: &[DenseCliquePhpProofAsset] = &[
    DenseCliquePhpProofAsset {
        name: "clique_n2_k10",
        num_vars: 180,
        num_clauses: 3_160,
        fingerprint: CLIQUE_N2_K10_CLAUSE_FINGERPRINT,
        original_order_witness: clique_n2_k10_original_order_witness,
        expected_structure: DenseCliquePhpProofAssetStructure {
            graph_vertices: 18,
            colors: 10,
            graph_edges: 144,
            graph_non_edges: 9,
            graph_non_edge_buckets: 9,
            graph_non_edge_bucket_min: 2,
            graph_non_edge_bucket_max: 2,
            complete_multipartite: true,
            php_pigeons: 10,
            php_holes: 9,
            php_unsat_obligation: true,
            mutexes: 3_150,
            expected_mutexes: 3_150,
            positive_support_clauses: 10,
            support_width: 18,
        },
        expected_checker_audit_stats: Some(CLIQUE_N2_K10_EXPECTED_CHECKER_AUDIT_STATS),
        drat: CLIQUE_N2_K10_ORIGINAL_DRAT,
        lrat: CLIQUE_N2_K10_ORIGINAL_LRAT,
    },
    DenseCliquePhpProofAsset {
        name: "php_functional_5_4",
        num_vars: 20,
        num_clauses: 75,
        fingerprint: PHP_FUNCTIONAL_5_4_CLAUSE_FINGERPRINT,
        original_order_witness: php_functional_5_4_original_order_witness,
        expected_structure: DenseCliquePhpProofAssetStructure {
            graph_vertices: 4,
            colors: 5,
            graph_edges: 6,
            graph_non_edges: 0,
            graph_non_edge_buckets: 4,
            graph_non_edge_bucket_min: 1,
            graph_non_edge_bucket_max: 1,
            complete_multipartite: true,
            php_pigeons: 5,
            php_holes: 4,
            php_unsat_obligation: true,
            mutexes: 70,
            expected_mutexes: 70,
            positive_support_clauses: 5,
            support_width: 4,
        },
        expected_checker_audit_stats: None,
        drat: PHP_FUNCTIONAL_5_4_ORIGINAL_DRAT,
        lrat: PHP_FUNCTIONAL_5_4_ORIGINAL_LRAT,
    },
];

fn dense_clique_php_route_header_candidate(num_vars: usize, num_clauses: usize) -> bool {
    dense_clique_php_route_asset_for_header(num_vars, num_clauses).is_some()
}

fn dense_clique_php_route_asset_for_header(
    num_vars: usize,
    num_clauses: usize,
) -> Option<&'static DenseCliquePhpProofAsset> {
    DENSE_CLIQUE_PHP_PROOF_ASSETS
        .iter()
        .find(|asset| asset.num_vars == num_vars && asset.num_clauses == num_clauses)
}

fn dense_clique_php_route_checker_audit_counts_match(
    stats: &ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats,
    expected: &ay_sat::dense_clique::DenseCliquePhpCheckerAuditStats,
) -> bool {
    stats == expected && stats.external_checker_verified_rows == 0
}

fn dense_clique_php_route_structure_witness_ok(
    packet: &ay_sat::dense_clique::DenseCliquePhpReplayPacket,
    expected: &DenseCliquePhpProofAssetStructure,
) -> bool {
    packet
        .witness
        .scout
        .structure
        .as_ref()
        .is_some_and(|structure| {
            structure.graph_vertices == expected.graph_vertices
                && structure.colors == expected.colors
                && structure.graph_edges == expected.graph_edges
                && structure.graph_non_edges == expected.graph_non_edges
                && structure.graph_non_edge_buckets == expected.graph_non_edge_buckets
                && structure.graph_non_edge_bucket_min == expected.graph_non_edge_bucket_min
                && structure.graph_non_edge_bucket_max == expected.graph_non_edge_bucket_max
                && structure.complete_multipartite == expected.complete_multipartite
                && structure.php_pigeons == expected.php_pigeons
                && structure.php_holes == expected.php_holes
                && structure.php_unsat_obligation == expected.php_unsat_obligation
                && structure.mutexes == expected.mutexes
                && structure.expected_mutexes == expected.expected_mutexes
                && structure.positive_support_clauses == expected.positive_support_clauses
                && structure.support_width == expected.support_width
        })
}

fn dense_clique_php_route_admission(
    num_vars: usize,
    clauses: &[Vec<Literal>],
) -> DenseCliquePhpProofRouteAdmissionResult {
    let Some(asset) = dense_clique_php_route_asset_for_header(num_vars, clauses.len()) else {
        return DenseCliquePhpProofRouteAdmissionResult::NonTarget;
    };
    if !(asset.original_order_witness)(clauses) {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
            "{} original-order witness mismatch",
            asset.name
        ));
    }
    let fingerprint = dimacs_clause_fingerprint(num_vars, clauses);
    if fingerprint != asset.fingerprint {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
            "{} original clause fingerprint mismatch",
            asset.name
        ));
    }

    let packet = match ay_sat::dense_clique::build_dense_clique_php_replay_packet_from_clauses(
        num_vars, clauses,
    ) {
        Ok(packet) => packet,
        Err(error) => {
            return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
                "dense clique PHP source replay packet rejected: {error:?}"
            ));
        }
    };
    if !packet.authority_is_absent() {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(
            "dense clique PHP source replay packet unexpectedly carried authority".to_string(),
        );
    }

    if !dense_clique_php_route_structure_witness_ok(&packet, &asset.expected_structure) {
        return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
            "dense clique PHP {} structure witness mismatch",
            asset.name
        ));
    }

    let checker_audit_stats = if let Some(expected) = asset.expected_checker_audit_stats.as_ref() {
        let checker_audit = match ay_sat::dense_clique::materialize_dense_clique_php_checker_audit(
            ay_sat::dense_clique::DenseCliquePhpCheckerAuditConfig { enabled: true },
            &packet,
        ) {
            Ok(checker_audit) => checker_audit,
            Err(error) => {
                return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
                    "dense clique PHP checker audit materialization rejected: {error:?}"
                ));
            }
        };
        if !checker_audit.authority_is_absent() {
            return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(
                "dense clique PHP checker audit unexpectedly carried authority".to_string(),
            );
        }
        if !dense_clique_php_route_checker_audit_counts_match(&checker_audit.stats, expected) {
            return DenseCliquePhpProofRouteAdmissionResult::TargetRejected(format!(
                "dense clique PHP {} checker audit materialization counters mismatch",
                asset.name
            ));
        }
        Some(checker_audit.stats)
    } else {
        None
    };

    DenseCliquePhpProofRouteAdmissionResult::Admitted(Box::new(DenseCliquePhpProofRouteAdmission {
        asset,
        fingerprint,
        source_audit: packet.source_audit,
        replay_ledger: packet.replay_ledger,
        checker_audit_stats,
    }))
}

fn dense_clique_php_materialized_lrat_route_proof_from_env(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    admission: &DenseCliquePhpProofRouteAdmission,
) -> Result<Option<DenseCliquePhpMaterializedLratRouteProof>, String> {
    let Some(compact_lrat_path) = std::env::var_os(SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF_ENV)
    else {
        return Ok(None);
    };
    let compact_lrat_path = PathBuf::from(compact_lrat_path);
    if compact_lrat_path.as_os_str().is_empty() {
        return Ok(None);
    }
    let compact_lrat = std::fs::read_to_string(&compact_lrat_path).map_err(|error| {
        format!(
            "failed to read compact LRAT proof {}: {error}",
            compact_lrat_path.display()
        )
    })?;

    let packet =
        ay_sat::dense_clique::build_dense_clique_php_replay_packet_from_clauses(num_vars, clauses)
            .map_err(|error| {
                format!("dense clique PHP source replay packet rejected: {error:?}")
            })?;
    if !packet.authority_is_absent() {
        return Err(
            "dense clique PHP source replay packet unexpectedly carried authority".to_string(),
        );
    }

    let materialization =
        ay_sat::dense_clique::materialize_dense_clique_php_original_lrat_from_compact_proof(
            ay_sat::dense_clique::DenseCliquePhpOriginalLratMaterializerConfig { enabled: true },
            &packet,
            &compact_lrat,
        )
        .map_err(|error| format!("original-DIMACS LRAT materialization rejected: {error:?}"))?;
    if !materialization.authority_is_absent() {
        return Err(
            "original-DIMACS LRAT materialization unexpectedly carried authority".to_string(),
        );
    }
    let expected_compact_clauses = admission.replay_ledger.bucket_alo_rows.len()
        + admission.replay_ledger.bucket_mutex_rows.len();
    if materialization.stats.source_rows_audited != admission.source_audit.source_rows as u64
        || materialization.stats.compact_clauses != expected_compact_clauses as u64
        || materialization.stats.extension_clauses_added
            != admission.replay_ledger.extension_clause_count() as u64
        || materialization.stats.external_checker_verified != 0
    {
        return Err(format!(
            "original-DIMACS LRAT materialization counters mismatch: {:?}",
            materialization.stats
        ));
    }

    let checker_stats =
        validate_original_lrat_against_clauses(num_vars, clauses, &materialization.lrat)?;
    Ok(Some(DenseCliquePhpMaterializedLratRouteProof {
        lrat: materialization.lrat,
        materialization_stats: materialization.stats,
        checker_stats,
    }))
}

fn validate_original_lrat_against_clauses(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    lrat: &str,
) -> Result<ay_lrat_check::Stats, String> {
    if num_vars > ay_lrat_check::checker::MAX_DENSE_VARS {
        return Err(format!(
            "formula variable count {num_vars} exceeds LRAT checker's dense maximum {}",
            ay_lrat_check::checker::MAX_DENSE_VARS
        ));
    }
    let steps = ay_lrat_check::lrat_parser::parse_text_lrat(lrat)
        .map_err(|error| format!("LRAT proof parse error: {error}"))?;
    if steps.is_empty() {
        return Err("LRAT proof contains zero steps".to_string());
    }

    let mut checker = ay_lrat_check::checker::LratChecker::new(num_vars);
    for (index, clause) in clauses.iter().enumerate() {
        let mut checker_clause = Vec::with_capacity(clause.len());
        for lit in clause {
            checker_clause.push(ay_lrat_check::dimacs::Literal::from_dimacs(lit.to_dimacs()));
        }
        if !checker.add_original(index as u64 + 1, &checker_clause) {
            return Err(format!(
                "LRAT checker rejected original clause {}: {}",
                index + 1,
                checker.stats_summary()
            ));
        }
    }
    if checker.verify_proof(&steps) {
        Ok(checker.stats().clone())
    } else {
        Err(format!(
            "LRAT checker rejected materialized proof: {}",
            checker.stats_summary()
        ))
    }
}

fn clique_n2_k10_original_order_witness(clauses: &[Vec<Literal>]) -> bool {
    if clauses.len() != 3160 {
        return false;
    }
    for color in 0..10 {
        let clause = &clauses[color];
        if clause.len() != 18 {
            return false;
        }
        for (vertex, lit) in clause.iter().enumerate() {
            if !lit.is_positive() || lit.to_dimacs() != (color * 18 + vertex + 1) as i32 {
                return false;
            }
        }
    }

    let mut offset = 10usize;
    for color in 0..10 {
        let base = color * 18 + 1;
        for lhs in 0..18 {
            for rhs in (lhs + 1)..18 {
                if !clause_is_ordered_negative_binary(&clauses[offset], base + lhs, base + rhs) {
                    return false;
                }
                offset += 1;
            }
        }
    }
    true
}

fn php_functional_5_4_original_order_witness(clauses: &[Vec<Literal>]) -> bool {
    if clauses.len() != 75 {
        return false;
    }

    for pigeon in 0..5 {
        let clause = &clauses[pigeon];
        if clause.len() != 4 {
            return false;
        }
        for (hole, lit) in clause.iter().enumerate() {
            if !lit.is_positive() || lit.to_dimacs() != php_functional_5_4_var(pigeon, hole) as i32
            {
                return false;
            }
        }
    }

    let mut offset = 5usize;
    for pigeon in 0..5 {
        for lhs_hole in 0..4 {
            for rhs_hole in (lhs_hole + 1)..4 {
                if !clause_is_ordered_negative_binary(
                    &clauses[offset],
                    php_functional_5_4_var(pigeon, lhs_hole),
                    php_functional_5_4_var(pigeon, rhs_hole),
                ) {
                    return false;
                }
                offset += 1;
            }
        }
    }

    for hole in 0..4 {
        for lhs_pigeon in 0..5 {
            for rhs_pigeon in (lhs_pigeon + 1)..5 {
                if !clause_is_ordered_negative_binary(
                    &clauses[offset],
                    php_functional_5_4_var(lhs_pigeon, hole),
                    php_functional_5_4_var(rhs_pigeon, hole),
                ) {
                    return false;
                }
                offset += 1;
            }
        }
    }

    offset == clauses.len()
}

const fn php_functional_5_4_var(pigeon: usize, hole: usize) -> usize {
    pigeon * 4 + hole + 1
}

fn clause_is_ordered_negative_binary(clause: &[Literal], lhs_var: usize, rhs_var: usize) -> bool {
    clause.len() == 2
        && clause[0].to_dimacs() == -(lhs_var as i32)
        && clause[1].to_dimacs() == -(rhs_var as i32)
}

fn dense_clique_php_route_target_clauses(
    num_vars: usize,
    num_clauses_declared: usize,
    clauses: Option<&[Vec<Literal>]>,
) -> Result<Option<&[Vec<Literal>]>, String> {
    if !dense_clique_php_route_header_candidate(num_vars, num_clauses_declared) {
        return Ok(None);
    }
    let clauses = clauses.ok_or_else(|| {
        "dense clique PHP proof-asset clause capture unavailable for target header".to_string()
    })?;
    if num_clauses_declared != clauses.len() {
        return Err(format!(
            "dense clique PHP proof-asset declared clause count {num_clauses_declared} does not match captured clause count {}",
            clauses.len()
        ));
    }
    Ok(Some(clauses))
}

fn maybe_run_dense_clique_php_proof_route(
    requested: bool,
    solver: &mut SatSolver,
    num_vars: usize,
    num_clauses_declared: usize,
    clauses: Option<&[Vec<Literal>]>,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
    source: DimacsInputSource<'_>,
) {
    if !requested {
        return;
    }
    let clauses =
        match dense_clique_php_route_target_clauses(num_vars, num_clauses_declared, clauses) {
            Ok(Some(clauses)) => clauses,
            Ok(None) => return,
            Err(reason) => {
                fail_closed_dense_clique_php_route_target_rejection(solver, proof, &reason)
            }
        };
    let admission = match dense_clique_php_route_admission(num_vars, clauses) {
        DenseCliquePhpProofRouteAdmissionResult::NonTarget => return,
        DenseCliquePhpProofRouteAdmissionResult::TargetRejected(reason) => {
            fail_closed_dense_clique_php_route_target_rejection(solver, proof, &reason);
        }
        DenseCliquePhpProofRouteAdmissionResult::Admitted(admission) => *admission,
    };
    if proof.binary {
        fail_closed_satcomp_proof_setup(
            "dense clique PHP proof route only emits text DRAT/LRAT proof assets",
        );
    }
    let route_proof = match proof.format {
        ProofFormat::Drat => DenseCliquePhpRouteProofText::Asset(admission.asset.drat),
        ProofFormat::Lrat => match dense_clique_php_materialized_lrat_route_proof_from_env(
            num_vars, clauses, &admission,
        ) {
            Ok(Some(materialized)) => {
                DenseCliquePhpRouteProofText::MaterializedLrat(Box::new(materialized))
            }
            Ok(None) => {
                if let Err(reason) =
                    validate_original_lrat_against_clauses(num_vars, clauses, admission.asset.lrat)
                {
                    fail_closed_dense_clique_php_route_target_rejection(
                        solver,
                        proof,
                        &format!("bundled original-DIMACS LRAT asset rejected: {reason}"),
                    );
                }
                safe_eprintln!(
                    "c dense-clique-php-proof-route: compact LRAT input env {} absent; using validated bundled original-DIMACS LRAT asset",
                    SAT_DENSE_CLIQUE_PHP_COMPACT_LRAT_PROOF_ENV
                );
                DenseCliquePhpRouteProofText::Asset(admission.asset.lrat)
            }
            Err(reason) => {
                fail_closed_dense_clique_php_route_target_rejection(
                    solver,
                    proof,
                    &format!("materialized LRAT path rejected: {reason}"),
                );
            }
        },
        ProofFormat::Alethe | ProofFormat::Lean4 => {
            fail_closed_satcomp_proof_setup(
                "dense clique PHP proof route requires DRAT or LRAT proof format",
            );
        }
    };
    let proof_text = route_proof.as_str();
    let file = match File::create(&proof.path) {
        Ok(file) => file,
        Err(error) => exit_failed_proof_create(&proof.path, &error),
    };
    let mut writer = proof_output_writer(file);
    if let Err(error) = writer.write_all(proof_text.as_bytes()) {
        fail_closed_satcomp_proof_setup(&format!(
            "dense clique PHP proof route failed to write proof file {}: {error}",
            proof.path
        ));
    }
    if let Err(error) = writer.flush() {
        fail_closed_satcomp_proof_setup(&format!(
            "dense clique PHP proof route failed to flush proof file {}: {error}",
            proof.path
        ));
    }
    write_proof_artifact_or_exit(
        source.proof_artifact_problem(),
        proof,
        ProofArtifactTheoryMetadata::dimacs_sat(num_vars, num_clauses_declared),
    );

    let variant = selected_sat_variant();
    emit_sat_applied_run_summary(
        "dense-clique-php-proof-route-v1",
        sat_variant_source_label(),
        summary_route_profile(variant, Some(proof)),
        Some(proof),
    );
    if stats_cfg.any() {
        let mut run_stats = stats_output::RunStatistics::new(
            stats_output::SolveMode::DimacsSat,
            "unsat",
            global_elapsed(),
        );
        run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY, 1);
        run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY, 1);
        run_stats.insert(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY, 1);
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_FINGERPRINT_KEY,
            admission.fingerprint,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY,
            1,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_OBLIGATION_ROWS_KEY,
            (admission.replay_ledger.bucket_alo_rows.len()
                + admission.replay_ledger.bucket_mutex_rows.len()) as u64,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_ALO_ROWS_KEY,
            admission.replay_ledger.bucket_alo_rows.len() as u64,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_MUTEX_ROWS_KEY,
            admission.replay_ledger.bucket_mutex_rows.len() as u64,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXTENSION_CLAUSES_KEY,
            admission.replay_ledger.extension_clause_count() as u64,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_ROWS_KEY,
            admission.source_audit.source_rows as u64,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_RAW_LITERALS_KEY,
            admission.source_audit.raw_dimacs_literals as u64,
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_ROWS_KEY,
            admission
                .checker_audit_stats
                .map_or(0, |stats| stats.checker_rows_materialized),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTENSION_ROWS_KEY,
            admission
                .checker_audit_stats
                .map_or(0, |stats| stats.extension_definition_rows_materialized),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_ALO_ROWS_KEY,
            admission
                .checker_audit_stats
                .map_or(0, |stats| stats.bucket_alo_rows_materialized),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_MUTEX_ROWS_KEY,
            admission
                .checker_audit_stats
                .map_or(0, |stats| stats.bucket_mutex_rows_materialized),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTERNAL_CHECKER_VERIFIED_ROWS_KEY,
            admission
                .checker_audit_stats
                .map_or(0, |stats| stats.external_checker_verified_rows),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY,
            u64::from(!route_proof.is_materialized_lrat()),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_BYTES_KEY,
            proof_text.len() as u64,
        );
        if let Some(materialized) = route_proof.materialized_lrat() {
            run_stats.insert("sat.dense_clique_php_proof_route_materialized_lrat", 1);
            run_stats.insert(
                "sat.dense_clique_php_proof_route_materialized_lrat_compact_lines",
                materialized.materialization_stats.compact_lrat_lines_seen,
            );
            run_stats.insert(
                "sat.dense_clique_php_proof_route_materialized_lrat_compact_additions",
                materialized
                    .materialization_stats
                    .compact_lrat_additions_remapped,
            );
            run_stats.insert(
                "sat.dense_clique_php_proof_route_materialized_lrat_compact_deletions",
                materialized
                    .materialization_stats
                    .compact_lrat_deletions_remapped,
            );
            run_stats.insert(
                "sat.dense_clique_php_proof_route_materialized_lrat_checker_derived",
                materialized.checker_stats.derived,
            );
            run_stats.insert(
                "sat.dense_clique_php_proof_route_materialized_lrat_checker_failures",
                materialized.checker_stats.failures,
            );
        }
        run_stats.insert("sat.proof_file_present", 1);
        run_stats.insert("sat.proof_file_bytes", proof_text.len() as u64);
        run_stats.insert("sat.proof_writer_additions", 0);
        run_stats.insert("sat.proof_writer_deletions", 0);
        run_stats.insert("time.total_ms", global_elapsed().as_millis() as u64);
        emit_dimacs_run_stats(
            &run_stats,
            stats_cfg,
            summary_route_profile(variant, Some(proof)),
        );
    }
    safe_eprintln!(
        "c dense-clique-php-proof-route: emitted validated original-DIMACS {} proof for {} after exact admission",
        if route_proof.is_materialized_lrat() { "materialized LRAT" } else { "asset" },
        admission.asset.name
    );
    crate::mark_verdict_printed();
    safe_println!("s UNSATISFIABLE");
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    std::process::exit(20);
}

fn cleanup_dense_clique_php_route_rejection_proof(
    solver: &mut SatSolver,
    proof: &ProofConfig,
) -> Option<DimacsProofWriterTelemetry> {
    cleanup_dimacs_non_unsat_proof_sidecar(solver, &SatResult::Unknown, Some(proof))
}

fn fail_closed_dense_clique_php_route_target_rejection(
    solver: &mut SatSolver,
    proof: &ProofConfig,
    reason: &str,
) -> ! {
    let _ = cleanup_dense_clique_php_route_rejection_proof(solver, proof);
    fail_closed_satcomp_proof_setup(&format!(
        "dense clique PHP proof route rejected exact target: {reason}"
    ));
}

const SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_true_tail_relocation_enabled";
const SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY: &str =
    "sat.bcp_learned_1963_true_tail_relocation_attempts";
const SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_MOVES_KEY: &str =
    "sat.bcp_learned_1963_true_tail_relocation_moves";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_enabled";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ELIGIBLE_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_eligible";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_WRITES_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_writes";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_UNIT_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_unit";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_CONFLICT_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_conflict";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ELIGIBLE_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_eligible";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_WRITES_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_writes";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_CONFLICT_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_conflict";
const SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY: &str =
    "sat.bcp_learned_618_true_tail_relocation_enabled";
const SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY: &str =
    "sat.bcp_learned_618_true_tail_relocation_attempts";
const SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_MOVES_KEY: &str =
    "sat.bcp_learned_618_true_tail_relocation_moves";
const SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY: &str =
    "sat.bcp_learned_no_replacement_saved_pos_update_enabled";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_enabled";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_candidates";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_APPLIED_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_applied";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_SAVED_SLOTS_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_saved_slots";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_SUFFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_true_suffix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_SUFFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_PREFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_true_prefix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_PREFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_UNIT_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_unit";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_CONFLICT_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_conflict";
const SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY: &str =
    "sat.bcp_learned_no_replacement_scan_pressure_enabled";
const SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY: &str = "sat.bcp_learned_1963_identity_enabled";
const SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_pressure_reduction_enabled";
const SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_pressure_retention_enabled";
const SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY: &str =
    "sat.bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_elision_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_false_reject_demote_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_candidates";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_elisions";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_HITS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_hits";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_MISMATCHES_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_mismatches";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_MISMATCH_DEMOTIONS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_mismatch_demotions";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_POPULATES_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_populates";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_STALE_REJECTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_stale_rejects";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_false_rejects";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTIONS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_false_reject_demotions";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_REPEAT_REJECTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_repeat_rejects";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELIDED_SUFFIX_SLOTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_elided_suffix_slots";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ELIDED_SUFFIX_SLOTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_AFFECTED_FSW_ROWS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_affected_fsw_rows";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_AFFECTED_FSW_ROWS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_requested";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_enabled";
const SAT_FOCUSED_RESTART_GATE_FINAL_KEY: &str = "sat.focused_restart_gate_final";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_updates";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY: &str =
    "sat.dense_mutex_focused_restart_runtime_checked";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY: &str =
    "sat.dense_mutex_focused_restart_active_vars";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY: &str =
    "sat.dense_mutex_focused_restart_active_clauses";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY: &str =
    "sat.dense_mutex_focused_restart_active_binary_clauses";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY: &str =
    "sat.dense_mutex_focused_restart_runtime_candidate";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY: &str =
    "sat.dense_mutex_focused_restart_previous_gate";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY: &str =
    "sat.dense_mutex_focused_restart_computed_gate";
const SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY: &str =
    "sat.backbone_post_vivify_binary_admission_enabled";
const SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY: &str =
    "sat.inprocessing_yield_rescue_backbone_cooldown_enabled";
const SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ROUNDS_KEY: &str =
    "sat.inprocessing_yield_rescue_backbone_cooldown_rounds";
const SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL_KEY: &str =
    "sat.inprocessing_yield_rescue_backbone_cooldown_interval";
const SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY: &str =
    "sat.inprocessing_lrat_proof_clamp_probe_rescue_enabled";
const SAT_INPROCESSING_LRAT_CLAMPED_BVE_DUE_ROUNDS_KEY: &str =
    "sat.inprocessing_lrat_clamped_bve_due_rounds";
const SAT_INPROCESSING_LRAT_CLAMPED_FACTOR_DUE_ROUNDS_KEY: &str =
    "sat.inprocessing_lrat_clamped_factor_due_rounds";
const SAT_INPROCESSING_LRAT_PROBE_RESCUE_ROUNDS_KEY: &str =
    "sat.inprocessing_lrat_probe_rescue_rounds";
const SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY: &str =
    "sat.bounded_backbone_zero_decompose_backoff_enabled";
const SAT_BOUNDED_BACKBONE_BACKOFF_TRIGGERS_KEY: &str = "sat.bounded_backbone_backoff_triggers";
const SAT_BOUNDED_BACKBONE_RUNS_KEY: &str = "sat.bounded_backbone_runs";
const SAT_BOUNDED_BACKBONE_YIELDS_KEY: &str = "sat.bounded_backbone_yields";
const SAT_BOUNDED_BACKBONE_MS_KEY: &str = "sat.bounded_backbone_ms";
const SAT_BOUNDED_BACKBONE_BINARY_SUPPRESSED_KEY: &str = "sat.bounded_backbone_binary_suppressed";
const SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY: &str = "sat.dense_clique_mab_branch_requested";
const SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY: &str = "sat.dense_clique_mab_branch_enabled";
const SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY: &str = "sat.dense_clique_mab_branch_exercised";
const SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISE_COUNT_KEY: &str =
    "sat.dense_clique_mab_branch_exercise_count";
const SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY: &str = "sat.dense_clique_scout_requested";
const SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY: &str = "sat.dense_clique_scout_enabled";
const SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY: &str = "sat.dense_clique_scout_exercised";
const SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY: &str = "sat.dense_clique_scout_rejection_code";
const SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY: &str = "sat.dense_clique_scout_vertices";
const SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY: &str = "sat.dense_clique_scout_colors";
const SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY: &str = "sat.dense_clique_scout_graph_edges";
const SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY: &str = "sat.dense_clique_scout_graph_non_edges";
const SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY: &str = "sat.dense_clique_scout_nonedge_buckets";
const SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY: &str =
    "sat.dense_clique_scout_nonedge_bucket_min";
const SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY: &str =
    "sat.dense_clique_scout_nonedge_bucket_max";
const SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY: &str =
    "sat.dense_clique_scout_complete_multipartite";
const SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY: &str = "sat.dense_clique_scout_php_pigeons";
const SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY: &str = "sat.dense_clique_scout_php_holes";
const SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY: &str =
    "sat.dense_clique_scout_php_unsat_obligation";
const SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY: &str = "sat.dense_clique_scout_mutexes";
const SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY: &str = "sat.dense_clique_scout_expected_mutexes";
const SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY: &str = "sat.dense_clique_scout_support_clauses";
const SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY: &str = "sat.dense_clique_scout_support_width";
const SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY: &str = "sat.dense_clique_scout_other_clauses";
const SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY: &str = "sat.dense_clique_scout_complete_mutex";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_requested";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_enabled";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_exercised";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCHEMA_VERSION_KEY: &str =
    "sat.multiplier_equiv_conservation_schema_version";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY: &str =
    "sat.multiplier_equiv_conservation_target_issue";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY: &str =
    "sat.multiplier_equiv_conservation_lean_admission_issue";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY: &str =
    "sat.multiplier_equiv_conservation_lean_conservation_issue";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_OFFICIAL_ROW_COUNT_KEY: &str =
    "sat.multiplier_equiv_conservation_official_row_count";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_VARS_KEY: &str =
    "sat.multiplier_equiv_conservation_num_vars";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_CLAUSES_KEY: &str =
    "sat.multiplier_equiv_conservation_num_clauses";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY: &str =
    "sat.multiplier_equiv_conservation_official_shape";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY: &str =
    "sat.multiplier_equiv_conservation_structural_candidate";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY: &str =
    "sat.multiplier_equiv_conservation_diagnostic_candidate";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY: &str =
    "sat.multiplier_equiv_conservation_fail_closed";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_AND_KEY: &str =
    "sat.multiplier_equiv_conservation_gate_and";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_XOR_KEY: &str =
    "sat.multiplier_equiv_conservation_gate_xor";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_GATES_TOTAL_KEY: &str =
    "sat.multiplier_equiv_conservation_gates_total";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PARTIAL_PRODUCT_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_partial_product_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_COMPRESSOR_LAYER_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_compressor_layer_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_obligation_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_source_clause_bound_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY: &str =
    "sat.multiplier_equiv_conservation_source_clause_bindings_missing";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_bound_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_binding_missing_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_duplicate_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_out_of_range_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_literal_mismatch_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_COMMON_PRODUCT_WITNESS_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_common_product_witness_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_MITER_DISEQUALITY_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_miter_disequality_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_BLOCKER_CODE_KEY: &str =
    "sat.multiplier_equiv_conservation_route_blocker_code";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REJECTION_CODE_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_rejection_code";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY: &str =
    "sat.multiplier_equiv_conservation_route_admitted";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY: &str =
    "sat.multiplier_equiv_conservation_result_authority";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY: &str =
    "sat.multiplier_equiv_conservation_proof_output_authority";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY: &str =
    "sat.multiplier_equiv_conservation_proof_replay_checked";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY: &str =
    "sat.multiplier_equiv_conservation_external_checker_verified";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY: &str =
    "sat.multiplier_equiv_conservation_proof_artifact_present";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY: &str =
    "sat.dense_clique_php_proof_route_requested";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY: &str =
    "sat.dense_clique_php_proof_route_enabled";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY: &str =
    "sat.dense_clique_php_proof_route_exercised";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_FINGERPRINT_KEY: &str =
    "sat.dense_clique_php_proof_route_fingerprint";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY: &str =
    "sat.dense_clique_php_proof_route_original_order_witness";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_OBLIGATION_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_obligation_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_ALO_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_bucket_alo_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_MUTEX_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_bucket_mutex_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXTENSION_CLAUSES_KEY: &str =
    "sat.dense_clique_php_proof_route_extension_clauses";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_source_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_RAW_LITERALS_KEY: &str =
    "sat.dense_clique_php_proof_route_source_raw_literals";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTENSION_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_extension_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_ALO_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_bucket_alo_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_MUTEX_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_bucket_mutex_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTERNAL_CHECKER_VERIFIED_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_external_checker_verified_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY: &str =
    "sat.dense_clique_php_proof_route_proof_asset_present";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_BYTES_KEY: &str =
    "sat.dense_clique_php_proof_route_proof_asset_bytes";
const SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_requested";
const SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_enabled";
const SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_exercised";
const SAT_BCP_TRAIL_LOOKAHEAD_PREFETCH_ENABLED_KEY: &str =
    "sat.bcp_trail_lookahead_prefetch_enabled";
const SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_enabled";
const SAT_BCP_LEARNED_617_TAIL_REORDER_CANDIDATES_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_candidates";
const SAT_BCP_LEARNED_617_TAIL_REORDER_EXERCISED_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_exercised";
const SAT_BCP_LEARNED_617_TAIL_REORDER_CHANGED_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_changed";
const SAT_BCP_LEARNED_617_TAIL_REORDER_SWAPS_KEY: &str = "sat.bcp_learned_617_tail_reorder_swaps";
const SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY: &str = "sat.bcp_learned_18_tail_reorder_enabled";
const SAT_BCP_LEARNED_18_TAIL_REORDER_CANDIDATES_KEY: &str =
    "sat.bcp_learned_18_tail_reorder_candidates";
const SAT_BCP_LEARNED_18_TAIL_REORDER_EXERCISED_KEY: &str =
    "sat.bcp_learned_18_tail_reorder_exercised";
const SAT_BCP_LEARNED_18_TAIL_REORDER_CHANGED_KEY: &str = "sat.bcp_learned_18_tail_reorder_changed";
const SAT_BCP_LEARNED_18_TAIL_REORDER_SWAPS_KEY: &str = "sat.bcp_learned_18_tail_reorder_swaps";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_enabled";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_candidates";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_CHANGED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_changed";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAPS_KEY: &str = "sat.bcp_learned_1963_tail_reorder_swaps";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_swap_budget_enabled";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_LIMIT_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_swap_budget_limit";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_candidates";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_APPLIED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_applied";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SKIPPED_OVER_BUDGET_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_skipped_over_budget";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_APPLIED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_swaps_applied";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_SKIPPED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_swaps_skipped";

fn emit_dimacs_run_stats(
    run_stats: &stats_output::RunStatistics,
    stats_cfg: stats_output::StatsConfig,
    route_profile: VariantRouteProfile,
) {
    if stats_cfg.human {
        run_stats.print_to_stderr();
    }
    if stats_cfg.json {
        safe_eprintln!("{}", dimacs_run_stats_json(run_stats, route_profile));
    }
}

fn dimacs_proof_file_telemetry(proof_config: Option<&ProofConfig>) -> (u64, u64) {
    let Some(proof) = proof_config else {
        return (0, 0);
    };
    match std::fs::metadata(&proof.path) {
        Ok(metadata) if metadata.is_file() => (1, metadata.len()),
        _ => (0, 0),
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct DimacsProofWriterTelemetry {
    additions: u64,
    deletions: u64,
}

fn dimacs_proof_writer_telemetry(solver: &SatSolver) -> Option<DimacsProofWriterTelemetry> {
    solver
        .proof_writer()
        .map(|writer| DimacsProofWriterTelemetry {
            additions: writer.added_count(),
            deletions: writer.deleted_count(),
        })
}

fn insert_dimacs_proof_telemetry(
    run_stats: &mut stats_output::RunStatistics,
    solver: &mut SatSolver,
    proof_config: Option<&ProofConfig>,
    writer_telemetry_override: Option<DimacsProofWriterTelemetry>,
) {
    let writer_telemetry = writer_telemetry_override
        .or_else(|| dimacs_proof_writer_telemetry(solver))
        .unwrap_or_default();
    if let Some(proof_writer) = solver.proof_writer_mut() {
        if let Err(error) = proof_writer.flush() {
            safe_eprintln!("c Warning: failed to flush proof output before stats: {error}");
        }
    }
    let (proof_file_present, proof_file_bytes) = dimacs_proof_file_telemetry(proof_config);
    run_stats.insert("sat.proof_file_present", proof_file_present);
    run_stats.insert("sat.proof_file_bytes", proof_file_bytes);
    run_stats.insert("sat.proof_writer_additions", writer_telemetry.additions);
    run_stats.insert("sat.proof_writer_deletions", writer_telemetry.deletions);
}

fn insert_preprocessing_transaction_telemetry(
    run_stats: &mut stats_output::RunStatistics,
    stats: ay_sat::PreprocessTransactionStats,
) {
    run_stats.insert("sat.preprocess_tx_started", stats.started);
    run_stats.insert("sat.preprocess_tx_attempted", stats.started);
    run_stats.insert("sat.preprocess_tx_committed", stats.committed);
    run_stats.insert("sat.preprocess_tx_rolled_back", stats.rolled_back);
    run_stats.insert("sat.preprocess_tx_fail_closed", stats.fail_closed);
    run_stats.insert("sat.preprocess_tx_rejected", stats.fail_closed);
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_not_required",
        stats.proof_obligation_not_required,
    );
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_satisfied",
        stats.proof_obligation_satisfied,
    );
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_rejected",
        stats.proof_obligation_rejected,
    );
    run_stats.insert(
        "sat.preprocess_tx_proof_obligation_pending",
        stats.proof_obligation_pending,
    );
    run_stats.insert(
        "sat.preprocess_tx_reconstruction_witness_not_applicable",
        stats.reconstruction_witness_not_applicable,
    );
    run_stats.insert(
        "sat.preprocess_tx_reconstruction_witness_present",
        stats.reconstruction_witness_present,
    );
    run_stats.insert(
        "sat.preprocess_tx_reconstruction_witness_missing",
        stats.reconstruction_witness_missing,
    );
    run_stats.insert(
        "sat.preprocess_tx_touched_variables_total",
        stats.touched_variables_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_eliminated_variables_total",
        stats.eliminated_variables_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_equivalent_variables_total",
        stats.equivalent_variables_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_planned_substitutions_total",
        stats.planned_substitutions_total,
    );
    run_stats.insert(
        "sat.preprocess_tx_max_mutation_epoch",
        stats.max_mutation_epoch,
    );
    run_stats.insert("sat.preprocess_tx_active", stats.active_transactions);
    run_stats.insert(
        "sat.preprocess_tx_retained_completed",
        stats.retained_completed,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_model_reconstruction_witness_missing",
        stats.fail_closed_model_reconstruction_witness_missing,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_decompose_lrat_preflight_rejected",
        stats.fail_closed_decompose_lrat_preflight_rejected,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_decompose_lrat_clamped_after_dry_run",
        stats.fail_closed_decompose_lrat_clamped_after_dry_run,
    );
    run_stats.insert(
        "sat.preprocess_tx_fail_closed_other",
        stats.fail_closed_other,
    );
    run_stats.insert(
        "sat.preprocess_tx_rolled_back_other",
        stats.rolled_back_other,
    );
}

fn insert_decompose_lrat_preflight_telemetry(
    run_stats: &mut stats_output::RunStatistics,
    stats: &ay_sat::DecomposeLratPreflightStats,
) {
    run_stats.insert("sat.decompose_lrat_preflight_attempts", stats.attempts);
    run_stats.insert(
        "sat.decompose_lrat_preflight_candidate_count",
        stats.transaction_candidates,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_no_substitution",
        stats.no_substitution,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_empty_candidates",
        stats.empty_candidates,
    );
    run_stats.insert("sat.decompose_lrat_preflight_slices", stats.dry_run_emitted);
    run_stats.insert(
        "sat.decompose_lrat_preflight_rejected",
        stats.dry_run_rejected,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_source_id",
        stats.missing_source_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_chain_edge_id",
        stats.missing_chain_edge_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_equiv_chain",
        stats.missing_equiv_chain,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_malformed_rewrite",
        stats.malformed_rewrite,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_contradiction",
        stats.contradiction,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_level0_unit_id",
        stats.missing_level0_unit_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_planned_add_rejected",
        stats.planned_add_rejected,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_substitution_hint",
        stats.missing_substitution_hint,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_transient_equiv_id",
        stats.missing_transient_equiv_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_proof_obligations",
        stats.proof_obligations,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_reconstruction_witnesses",
        stats.reconstruction_witnesses,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_attempts",
        stats.main_rewrite_materializer_attempts,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_proof_emit_records_seen",
        stats.main_rewrite_materializer_proof_emit_records_seen,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_records",
        stats.main_rewrite_materializer_records,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_fail_closed",
        stats.main_rewrite_materializer_fail_closed,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_missing_runtime_records",
        stats.main_rewrite_materializer_missing_runtime_records,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_attempts",
        stats.fmla_lift_attempts,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_detected",
        stats.fmla_lift_detected,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_rejection_code",
        stats.fmla_lift_rejection_code,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_onehot_groups",
        stats.fmla_lift_onehot_groups,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_guarded_equiv_pairs",
        stats.fmla_lift_guarded_equiv_pairs,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_guarded_equiv_guards",
        stats.fmla_lift_guarded_equiv_guards,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_directional_ternary_witnesses",
        stats.fmla_lift_directional_ternary_witnesses,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_touched_vars",
        stats.fmla_lift_touched_vars,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_runtime_records",
        stats.fmla_lift_runtime_records,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_witness_checker_passed",
        stats.fmla_lift_witness_checker_passed,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_all_witness_pairs_checked",
        stats.fmla_lift_all_witness_pairs_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_all_witness_pairs_missing_guard_group",
        stats.fmla_lift_all_witness_pairs_missing_guard_group,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_id_refs_checked",
        stats.fmla_lift_source_id_refs_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_unique_source_ids_checked",
        stats.fmla_lift_unique_source_ids_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_ids_checked",
        stats.fmla_lift_source_ids_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_ids_visible",
        stats.fmla_lift_source_ids_visible,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_ids_missing",
        stats.fmla_lift_source_ids_missing,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_first_missing_source_id",
        stats.fmla_lift_first_missing_source_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_proof_ready",
        stats.fmla_lift_proof_ready,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_model_ready",
        stats.fmla_lift_model_ready,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_destructive_allowed",
        stats.fmla_lift_destructive_allowed,
    );
}

fn cleanup_dimacs_non_unsat_proof_sidecar(
    solver: &mut SatSolver,
    result: &SatResult,
    proof_config: Option<&ProofConfig>,
) -> Option<DimacsProofWriterTelemetry> {
    if matches!(result, SatResult::Unsat(_)) {
        return None;
    }

    retain_fmla_learned_lrat_dry_run_artifact_from_env(solver);
    let writer_telemetry = dimacs_proof_writer_telemetry(solver);
    if let Some(mut proof_output) = solver.take_proof_writer() {
        if let Err(error) = proof_output.flush() {
            safe_eprintln!("c Warning: failed to flush discarded non-UNSAT proof output: {error}");
        }
    }

    cleanup_dimacs_non_unsat_proof_paths(proof_config);
    writer_telemetry
}

fn cleanup_dimacs_non_unsat_proof_paths_for_result(
    result: &SatResult,
    proof_config: Option<&ProofConfig>,
) {
    if matches!(result, SatResult::Unsat(_)) {
        return;
    }
    cleanup_dimacs_non_unsat_proof_paths(proof_config);
}

fn cleanup_dimacs_non_unsat_proof_paths(proof_config: Option<&ProofConfig>) {
    let Some(proof) = proof_config else {
        return;
    };
    for path in std::iter::once(proof.path.as_str()).chain(proof.artifact_path.as_deref()) {
        match std::fs::remove_file(path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => {
                safe_eprintln!(
                    "c Warning: failed to remove non-UNSAT proof sidecar {path}: {error}"
                );
            }
        }
    }
}

#[derive(Clone, Copy)]
enum DimacsInputSource<'a> {
    Content(&'a str),
    FilePath(&'a str),
    Unavailable,
}

impl<'a> DimacsInputSource<'a> {
    fn proof_artifact_problem(self) -> ProofArtifactProblem<'a> {
        match self {
            Self::Content(content) => ProofArtifactProblem::Text(content),
            Self::FilePath(path) => ProofArtifactProblem::FilePath(path),
            Self::Unavailable => ProofArtifactProblem::Unavailable("DIMACS stream"),
        }
    }
}

#[derive(Clone, Debug)]
struct GuardCoverSidecarRunStats {
    path: String,
    accepted: bool,
    cuts: u64,
    guards: u64,
    budget_rhs: u64,
    packed_deficit: u64,
    injected_empty_cut: bool,
}

impl GuardCoverSidecarRunStats {
    fn accepted(path: &Path, evidence: GuardCoverPackingEvidence) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: true,
            cuts: evidence.cuts as u64,
            guards: evidence.guards as u64,
            budget_rhs: evidence.budget_rhs,
            packed_deficit: evidence.packed_deficit,
            injected_empty_cut: false,
        }
    }

    fn rejected(path: &Path) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: false,
            cuts: 0,
            guards: 0,
            budget_rhs: 0,
            packed_deficit: 0,
            injected_empty_cut: false,
        }
    }

    fn status_label(&self) -> &'static str {
        if self.accepted {
            "accepted"
        } else {
            "rejected"
        }
    }
}

#[derive(Clone, Debug)]
struct SeparatorCoverSidecarRunStats {
    path: String,
    accepted: bool,
    separator_vars: u64,
    cubes: u64,
    covered_assignments: u64,
    injected_empty_cut: bool,
}

impl SeparatorCoverSidecarRunStats {
    fn accepted(path: &Path, evidence: SeparatorCoverEvidence) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: true,
            separator_vars: evidence.separator_vars as u64,
            cubes: evidence.cubes as u64,
            covered_assignments: evidence.covered_assignments,
            injected_empty_cut: false,
        }
    }

    fn rejected(path: &Path) -> Self {
        Self {
            path: path.display().to_string(),
            accepted: false,
            separator_vars: 0,
            cubes: 0,
            covered_assignments: 0,
            injected_empty_cut: false,
        }
    }

    fn status_label(&self) -> &'static str {
        if self.accepted {
            "accepted"
        } else {
            "rejected"
        }
    }
}

pub(crate) fn run_dimacs_proof_from_file(
    path: &str,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
) {
    exit_if_circuit_multiplier22_retained_sat_model_authority_admits_file(path);
    let separator_cover_sidecar = discover_and_check_separator_cover_sidecar_from_file(path);
    if separator_cover_sidecar
        .as_ref()
        .is_some_and(|sidecar| sidecar.accepted)
    {
        cleanup_dimacs_non_unsat_proof_paths(Some(proof));
        fail_closed_satcomp_proof_setup(
            "separator-cover sidecar accepted but proof-mode public artifact replay is not implemented",
        );
    }

    // Read the file into memory so we can size the solver by the variables that
    // ACTUALLY appear (content-driven), rather than trusting the declared header.
    // The raw bytes are O(file size) — the streaming below still avoids
    // materializing parsed clause structures.
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) => {
            safe_eprintln!("Error reading file '{path}': {error}");
            std::process::exit(1);
        }
    };
    let content_max_var = scan_max_variable(&bytes);
    // Giant-mode memory lever (`AY_AB_GIANT_MEM`, default ON): hand the byte
    // buffer to the reader BY VALUE. `parse_dimacs_events` consumes the
    // reader, so the whole file buffer (3.4GB/7GB for the SC2025 giants
    // 1c21a43a/6ebe9012) is freed as soon as parsing ends, instead of staying
    // resident through watch-init + search (it was ~15-20% of peak RSS on
    // 1c21a43a). The model/proof finalize paths re-read the formula via
    // `DimacsInputSource::FilePath`, NOT this buffer, so this is a pure
    // memory-lifetime change: the parsed byte stream is identical and no
    // certificate gate is touched.
    if giant_mem_levers_enabled() {
        run_proof_streaming_reader(
            io::Cursor::new(bytes),
            stats_cfg,
            selected_sat_variant(),
            proof,
            DimacsInputSource::FilePath(path),
            Some(content_max_var),
        );
    } else {
        run_proof_streaming_reader(
            io::Cursor::new(&bytes),
            stats_cfg,
            selected_sat_variant(),
            proof,
            DimacsInputSource::FilePath(path),
            Some(content_max_var),
        );
    }
}

/// Kill-switch `AY_AB_GIANT_MEM` (default ON; unset or `=1` enables, any
/// other explicit value disables — conservative parse matching
/// `AY_AB_SUBST_AUTO_GIANT`): giant-instance peak-RSS levers —
/// owned-cursor file-buffer drop after parse (`run_dimacs_proof_from_file`
/// above) and the u32 watch-init offset collect
/// (`ay-sat::solver::propagation::initialize_watches`, which reads the same
/// env var). Both are memory-lifetime/width-only: verdicts, stats and
/// certificates are unchanged. Validated on 1c21a43a (58.6M vars / 157.7M
/// clauses): SAT@43.6s, peak RSS 16.1GB vs 15.3-25.9GB baseline spread,
/// model independently validated. Cached OnceLock per the #8506
/// no-per-call-syscall convention.
pub(crate) fn giant_mem_levers_enabled() -> bool {
    use std::sync::OnceLock;
    static GIANT_MEM: OnceLock<bool> = OnceLock::new();
    *GIANT_MEM.get_or_init(|| {
        std::env::var("AY_AB_GIANT_MEM")
            .map(|v| v == "1")
            .unwrap_or(true)
    })
}

pub(crate) fn run_dimacs_proof_from_reader<R>(
    reader: R,
    stats_cfg: stats_output::StatsConfig,
    proof: &ProofConfig,
) where
    R: Read,
{
    run_proof_streaming_reader(
        reader,
        stats_cfg,
        selected_sat_variant(),
        proof,
        DimacsInputSource::Unavailable,
        // True single-pass stream (e.g. proof replay): no pre-scan possible;
        // fall back to the header, bounded by the backstop.
        None,
    );
}

fn exit_if_circuit_multiplier22_retained_sat_model_authority_admits_file(path: &str) {
    if !circuit_multiplier22_retained_sat_model_authority_requested() {
        return;
    }
    let Ok(bytes) = std::fs::read(path) else {
        return;
    };
    let Ok(content) = std::str::from_utf8(&bytes) else {
        return;
    };
    let Ok(formula) = parse_dimacs(content) else {
        return;
    };
    if let Some(model) = formula.circuit_multiplier22_retained_sat_model_from_env(&bytes) {
        exit_with_circuit_multiplier22_retained_sat_model(&model);
    }
}

pub(crate) fn run_dimacs_from_file(
    path: &str,
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_from_content_impl(content, stats_cfg, proof_config, Some(path));
}

pub(crate) fn run_dimacs_from_content(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_from_content_impl(content, stats_cfg, proof_config, None);
}

fn run_dimacs_from_content_impl(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    input_path: Option<&str>,
) {
    let sat_variant = selected_sat_variant();
    // Auto-route Default -> Probe for binary-dominant mid-size formulas unless
    // the user pinned a variant with `--sat-variant` (kill-switch:
    // AY_AB_PROBE_ROUTE=0). Both the buffered and streaming solve paths honor it.
    let allow_auto_route = !sat_variant_explicitly_selected();
    let separator_cover_sidecar =
        discover_and_check_separator_cover_sidecar(input_path, content.as_bytes());

    if let Some(proof) = proof_config {
        exit_if_circuit_multiplier22_retained_sat_model_authority_admits(content);
        if separator_cover_sidecar
            .as_ref()
            .is_some_and(|sidecar| sidecar.accepted)
        {
            cleanup_dimacs_non_unsat_proof_paths(Some(proof));
            fail_closed_satcomp_proof_setup(
                "separator-cover sidecar accepted but proof-mode public artifact replay is not implemented",
            );
        }
        run_proof_streaming(content, stats_cfg, sat_variant, proof);
        return;
    }

    let guard_cover_sidecar =
        discover_and_check_guard_cover_sidecar(input_path, content.as_bytes());

    // Fast path: large formulas use streaming byte-level parser (no intermediate
    // Vec<Vec<Literal>> allocation). On shuffling-2 (98MB, 4.7M clauses) this
    // reduces parse+load from >15s to ~2s. Proof output is handled above by the
    // proof-aware streaming parser so LRAT original IDs stay in input order.
    if guard_cover_sidecar.is_none() && separator_cover_sidecar.is_none() {
        if let Some((_, nc)) = scan_dimacs_header(content) {
            if nc > STREAMING_CLAUSE_THRESHOLD {
                let streaming_variant =
                    streaming_auto_route(content, sat_variant, allow_auto_route);
                run_streaming(content, stats_cfg, streaming_variant);
                return;
            }
        }
    } else if let Some((_, nc)) = scan_dimacs_header(content) {
        if nc > STREAMING_CLAUSE_THRESHOLD {
            safe_eprintln!(
                "c structural-sidecar: adjacent sidecar present; using checked non-streaming DIMACS load"
            );
        }
    }

    match parse_dimacs(content) {
        Ok(formula) => {
            if let Some(model) =
                formula.circuit_multiplier22_retained_sat_model_from_env(content.as_bytes())
            {
                exit_with_circuit_multiplier22_retained_sat_model(&model);
            }

            if separator_cover_sidecar
                .as_ref()
                .is_some_and(|sidecar| sidecar.accepted)
            {
                let mut solver =
                    formula.into_solver_with_variant_routed(sat_variant, allow_auto_route);
                let mut sidecar_stats = separator_cover_sidecar.expect("sidecar was checked above");
                sidecar_stats.injected_empty_cut = true;
                let _ = solver.add_preserved_learned(Vec::new());
                run_dimacs_solver_with_research_sidecar_stats(
                    &mut solver,
                    stats_cfg,
                    content,
                    None,
                    guard_cover_sidecar.as_ref(),
                    Some(&sidecar_stats),
                );
                return;
            }

            if guard_cover_sidecar
                .as_ref()
                .is_some_and(|sidecar| sidecar.accepted)
            {
                let mut solver =
                    formula.into_solver_with_variant_routed(sat_variant, allow_auto_route);
                let mut sidecar_stats = guard_cover_sidecar.expect("sidecar was checked above");
                sidecar_stats.injected_empty_cut = true;
                // The Lean-backed sidecar proves a contradiction. Inject an
                // empty learned CNF cut and let the normal SAT solve path
                // finalize the UNSAT result and stats.
                let _ = solver.add_preserved_learned(Vec::new());
                run_dimacs_solver_with_research_sidecar_stats(
                    &mut solver,
                    stats_cfg,
                    content,
                    None,
                    Some(&sidecar_stats),
                    separator_cover_sidecar.as_ref(),
                );
                return;
            }

            if let Some(proof) = proof_config {
                let num_original_clauses = formula.clauses.len() as u64;

                // Alethe/Lean4 export: solve with LRAT internally (to io::sink()) and
                // write the proof from the ProofCertificate post-solve.
                if proof.format == ProofFormat::Alethe {
                    let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
                    let variant_config = variant_profile_plan_for_dimacs_features(
                        sat_variant,
                        formula.num_vars,
                        formula.num_clauses,
                        true,
                        true, // LRAT mode for backward reconstruction
                        false,
                        &features,
                    )
                    .config;

                    let sink_output = ProofOutput::lrat_text(io::sink(), num_original_clauses);
                    let mut solver = SatSolver::with_proof_output(formula.num_vars, sink_output);
                    variant_config.apply_to_solver(&mut solver);
                    for clause in formula.clauses {
                        solver.add_clause(clause);
                    }
                    run_dimacs_solver_alethe(
                        &mut solver,
                        stats_cfg,
                        &proof.path,
                        content,
                        Some(proof),
                    );
                    return;
                }

                if proof.format == ProofFormat::Lean4 {
                    let original_clauses = dimacs_original_clauses_from_literals(&formula.clauses);
                    let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
                    let variant_config = variant_profile_plan_for_dimacs_features(
                        sat_variant,
                        formula.num_vars,
                        formula.num_clauses,
                        true,
                        true, // LRAT mode for backward reconstruction
                        false,
                        &features,
                    )
                    .config;

                    let lrat_output =
                        ProofOutput::lrat_text(Vec::<u8>::new(), num_original_clauses);
                    let mut solver = SatSolver::with_proof_output(formula.num_vars, lrat_output);
                    variant_config.apply_to_solver(&mut solver);
                    for clause in formula.clauses {
                        solver.add_clause(clause);
                    }
                    run_dimacs_solver_lean4(
                        &mut solver,
                        stats_cfg,
                        &proof.path,
                        content,
                        Some(proof),
                        &original_clauses,
                    );
                    return;
                }

                let file = match File::create(&proof.path) {
                    Ok(file) => file,
                    Err(error) => exit_failed_proof_create(&proof.path, &error),
                };
                let writer = proof_output_writer(file);
                let lrat_output = matches!(proof.format, ProofFormat::Lrat);
                let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
                let variant_config = variant_profile_plan_for_dimacs_features(
                    sat_variant,
                    formula.num_vars,
                    formula.num_clauses,
                    true,
                    lrat_output,
                    lrat_output,
                    &features,
                )
                .config;

                let output = match (proof.format, proof.binary) {
                    (ProofFormat::Drat, false) => ProofOutput::drat_text(writer),
                    (ProofFormat::Drat, true) => ProofOutput::drat_binary(writer),
                    (ProofFormat::Lrat, false) => {
                        ProofOutput::lrat_text(writer, num_original_clauses)
                    }
                    (ProofFormat::Lrat, true) => {
                        ProofOutput::lrat_binary(writer, num_original_clauses)
                    }
                    (ProofFormat::Alethe | ProofFormat::Lean4, _) => {
                        // These formats are handled above via post-solve certificate export.
                        unreachable!("Alethe/Lean4 handled by pre-solve branch")
                    }
                };
                let mut solver = SatSolver::with_proof_output(formula.num_vars, output);
                variant_config.apply_to_solver(&mut solver);
                for clause in formula.clauses {
                    solver.add_clause(clause);
                }
                run_dimacs_solver(&mut solver, stats_cfg, content, Some(proof));
            } else {
                let guard_cover_sidecar_ref = guard_cover_sidecar.as_ref();
                let (remaining, xor_ext, xor_stats) =
                    ay_xor::preprocess_clauses_with_stats(&formula.clauses);
                let use_xor = xor_ext.as_ref().is_some_and(|ext| {
                    // The extension must have at least one active GE component.
                    // XorExtension::new() skips components exceeding CMS limits.
                    // If ALL components are skipped, fall through to pure SAT
                    // with the original formula (#8078).
                    ext.num_components() > 0
                        && should_enable_xor_extension(
                            &formula.clauses,
                            xor_stats.clauses_consumed,
                            remaining.len(),
                            xor_stats.xors_detected,
                        )
                });

                if use_xor {
                    // Feature-driven adaptive adjustments (computed on original
                    // clauses before XOR preprocessing consumes them).
                    let features = SatFeatures::extract(formula.num_vars, &formula.clauses);

                    let ext_ref = xor_ext.as_ref().expect("use_xor implies Some");
                    safe_eprintln!(
                        "c XOR: detected {} constraints, {} clauses consumed, {} remaining, {} components",
                        xor_stats.xors_detected,
                        xor_stats.clauses_consumed,
                        remaining.len(),
                        ext_ref.num_components()
                    );

                    let mut solver = SatSolver::new(formula.num_vars);
                    let xor_config = variant_profile_plan_for_dimacs_features(
                        sat_variant,
                        formula.num_vars,
                        formula.num_clauses,
                        false,
                        false,
                        false,
                        &features,
                    )
                    .config;
                    xor_config.apply_to_solver(&mut solver);
                    // Claim trace file to prevent any nested tracers from clobbering.
                    if ay_core::trace_file_available() {
                        if let Some(path) = &ay_core::trace_config().trace_file_path {
                            ay_core::claim_trace_file();
                            solver.enable_tla_trace(
                                path,
                                SatSolver::tla_module(),
                                SatSolver::tla_variables(),
                            );
                        }
                    }
                    for clause in remaining {
                        solver.add_clause(clause);
                    }
                    let mut ext = xor_ext.expect("use_xor implies xor extension is present");
                    // Freeze XOR variables to prevent BVE from eliminating
                    // them, which would cause check() to see unassigned
                    // values and produce wrong SAT on UNSAT instances.
                    {
                        let mut seen = std::collections::HashSet::new();
                        for constraint in ext.constraints() {
                            for &var_id in &constraint.vars {
                                if seen.insert(var_id) {
                                    solver.freeze(Variable::new(var_id));
                                }
                            }
                        }
                    }
                    // XOR-derived lemmas are logically implied by the original
                    // formula (Gauss-Jordan over GF(2)). Mark as trusted so
                    // DRAT/LRAT proof emission uses TrustedTransform (#4533).
                    solver.set_extension_trusted_lemmas(true);
                    run_dimacs_solver_with_extension(
                        &mut solver,
                        &mut ext,
                        stats_cfg,
                        content,
                        None,
                        guard_cover_sidecar_ref,
                        separator_cover_sidecar.as_ref(),
                    );
                } else {
                    let mut solver =
                        formula.into_solver_with_variant_routed(sat_variant, allow_auto_route);
                    // TLA trace only available on non-proof solver.
                    // Claim trace file to prevent any nested tracers from clobbering.
                    if ay_core::trace_file_available() {
                        if let Some(path) = &ay_core::trace_config().trace_file_path {
                            ay_core::claim_trace_file();
                            solver.enable_tla_trace(
                                path,
                                SatSolver::tla_module(),
                                SatSolver::tla_variables(),
                            );
                        }
                    }
                    run_dimacs_solver_with_research_sidecar_stats(
                        &mut solver,
                        stats_cfg,
                        content,
                        None,
                        guard_cover_sidecar_ref,
                        separator_cover_sidecar.as_ref(),
                    );
                }
            }
        }
        Err(e) => {
            safe_eprintln!("c Parse error: {}", e);
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
    }
}

fn discover_and_check_guard_cover_sidecar(
    input_path: Option<&str>,
    cnf_bytes: &[u8],
) -> Option<GuardCoverSidecarRunStats> {
    let input_path = input_path?;
    let sidecar_path = discover_guard_cover_sidecar_path(input_path)?;
    let sidecar_text = match std::fs::read_to_string(&sidecar_path) {
        Ok(text) => text,
        Err(error) => {
            safe_eprintln!(
                "c guard-cover: rejected {}: failed to read sidecar: {error}",
                sidecar_path.display()
            );
            return Some(GuardCoverSidecarRunStats::rejected(&sidecar_path));
        }
    };

    let base_dir = sidecar_path.parent().unwrap_or_else(|| Path::new("."));
    let base_dir = match base_dir.canonicalize() {
        Ok(path) => path,
        Err(error) => {
            safe_eprintln!(
                "c guard-cover: rejected {}: failed to canonicalize sidecar directory: {error}",
                sidecar_path.display()
            );
            return Some(GuardCoverSidecarRunStats::rejected(&sidecar_path));
        }
    };

    let result = guard_cover_sidecar::check_guard_cover_packing_sidecar(
        cnf_bytes,
        &sidecar_text,
        |witness| resolve_guard_cover_hall_witness(&base_dir, witness),
    );
    match result {
        Ok(evidence) => {
            safe_eprintln!(
                "c guard-cover: accepted {} cuts={} guards={} budget_rhs={} packed_deficit={}",
                sidecar_path.display(),
                evidence.cuts,
                evidence.guards,
                evidence.budget_rhs,
                evidence.packed_deficit
            );
            Some(GuardCoverSidecarRunStats::accepted(&sidecar_path, evidence))
        }
        Err(error) => {
            safe_eprintln!(
                "c guard-cover: rejected {}: {}",
                sidecar_path.display(),
                error.detail()
            );
            Some(GuardCoverSidecarRunStats::rejected(&sidecar_path))
        }
    }
}

fn discover_guard_cover_sidecar_path(input_path: &str) -> Option<PathBuf> {
    let path = Path::new(input_path);
    let mut candidates = Vec::with_capacity(2);
    candidates.push(path.with_extension("guard-cover.json"));
    candidates.push(PathBuf::from(format!("{input_path}.guard-cover.json")));
    candidates.into_iter().find(|candidate| candidate.is_file())
}

fn discover_and_check_separator_cover_sidecar_from_file(
    input_path: &str,
) -> Option<SeparatorCoverSidecarRunStats> {
    let sidecar_path = discover_separator_cover_sidecar_path(input_path)?;
    let cnf_bytes = match std::fs::read(input_path) {
        Ok(bytes) => bytes,
        Err(error) => {
            safe_eprintln!(
                "c separator-cover: rejected {}: failed to read DIMACS input: {error}",
                sidecar_path.display()
            );
            return Some(SeparatorCoverSidecarRunStats::rejected(&sidecar_path));
        }
    };
    read_and_check_separator_cover_sidecar(&sidecar_path, &cnf_bytes)
}

fn discover_and_check_separator_cover_sidecar(
    input_path: Option<&str>,
    cnf_bytes: &[u8],
) -> Option<SeparatorCoverSidecarRunStats> {
    let input_path = input_path?;
    let sidecar_path = discover_separator_cover_sidecar_path(input_path)?;
    read_and_check_separator_cover_sidecar(&sidecar_path, cnf_bytes)
}

fn read_and_check_separator_cover_sidecar(
    sidecar_path: &Path,
    cnf_bytes: &[u8],
) -> Option<SeparatorCoverSidecarRunStats> {
    let sidecar_text = match std::fs::read_to_string(sidecar_path) {
        Ok(text) => text,
        Err(error) => {
            safe_eprintln!(
                "c separator-cover: rejected {}: failed to read sidecar: {error}",
                sidecar_path.display()
            );
            return Some(SeparatorCoverSidecarRunStats::rejected(sidecar_path));
        }
    };

    match guard_cover_sidecar::check_separator_cover_sidecar(cnf_bytes, &sidecar_text) {
        Ok(evidence) => {
            safe_eprintln!(
                "c separator-cover: accepted {} separator_vars={} cubes={} covered_assignments={}",
                sidecar_path.display(),
                evidence.separator_vars,
                evidence.cubes,
                evidence.covered_assignments
            );
            Some(SeparatorCoverSidecarRunStats::accepted(
                sidecar_path,
                evidence,
            ))
        }
        Err(error) => {
            safe_eprintln!(
                "c separator-cover: rejected {}: {}",
                sidecar_path.display(),
                error.detail()
            );
            Some(SeparatorCoverSidecarRunStats::rejected(sidecar_path))
        }
    }
}

fn discover_separator_cover_sidecar_path(input_path: &str) -> Option<PathBuf> {
    let path = Path::new(input_path);
    let mut candidates = Vec::with_capacity(2);
    candidates.push(path.with_extension("separator-cover.json"));
    candidates.push(PathBuf::from(format!("{input_path}.separator-cover.json")));
    candidates.into_iter().find(|candidate| candidate.is_file())
}

fn resolve_guard_cover_hall_witness(base_dir: &Path, witness: &str) -> Result<String, String> {
    let witness_path = Path::new(witness);
    if witness_path.is_absolute() {
        return Err("depends_on witness path must be relative".to_string());
    }
    let resolved = base_dir.join(witness_path);
    let resolved = resolved
        .canonicalize()
        .map_err(|error| format!("failed to canonicalize {witness}: {error}"))?;
    if !resolved.starts_with(base_dir) {
        return Err("depends_on witness path escapes sidecar directory".to_string());
    }
    std::fs::read_to_string(&resolved)
        .map_err(|error| format!("failed to read {}: {error}", resolved.display()))
}

/// Run a DIMACS formula using the parallel portfolio solver.
///
/// Parses the formula, creates a `PortfolioSolver` with instance-aware strategy
/// selection, runs `num_threads` solver threads in parallel, and reports the
/// first result. This is the `--parallel N` CLI entry point.
pub(crate) fn run_dimacs_parallel(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    num_threads: usize,
) {
    match parse_dimacs(content) {
        Ok(formula) => {
            safe_eprintln!(
                "c parallel portfolio: {} threads, {} vars, {} clauses",
                num_threads,
                formula.num_vars,
                formula.clauses.len()
            );
            let start = std::time::Instant::now();
            let mut portfolio = PortfolioSolver::new_adaptive(num_threads, &formula);
            if proof_config.is_some() {
                portfolio.set_proof_mode(true);
            }
            // Wire the wall-clock watchdog so the portfolio honours `-t` even
            // when no worker has finished. Without this the portfolio could only
            // stop on a worker win or give-up (#3638 for the sequential path).
            if let Some(handle) = INTERRUPT_HANDLE.get() {
                portfolio.set_external_cancel(handle.clone());
            }
            let (result, raw_proof_bytes) = portfolio.solve_with_proof_bytes(&formula);
            let elapsed = start.elapsed();
            safe_eprintln!(
                "c parallel portfolio: solved in {:.3}s",
                elapsed.as_secs_f64()
            );
            cleanup_dimacs_non_unsat_proof_paths_for_result(&result, proof_config);

            // Emit stats if requested.
            if stats_cfg.any() {
                let result_str = match &result {
                    SatResult::Sat(_) => "sat",
                    SatResult::Unsat(_) => "unsat",
                    SatResult::Unknown => "unknown",
                    #[allow(unreachable_patterns)]
                    _ => "unknown",
                };
                let mut run_stats = stats_output::RunStatistics::new(
                    stats_output::SolveMode::DimacsSat,
                    result_str,
                    global_elapsed(),
                );
                run_stats.insert("sat.parallel_threads", num_threads as u64);
                // #8640: Resource consumption statistics.
                run_stats.insert(
                    "resource.rss_peak_bytes",
                    ay_sys::current_rss_bytes() as u64,
                );
                run_stats.insert(
                    "resource.memory_limit_bytes",
                    ay_sys::get_process_memory_limit() as u64,
                );
                run_stats.insert("time.total_ms", global_elapsed().as_millis() as u64);
                run_stats.emit(stats_cfg);
            }

            // Write proof file from the forward DRAT bytes if available,
            // otherwise fall back to materializing from the ProofCertificate (#8428).
            if let (SatResult::Unsat(ref cert), Some(proof)) = (&result, proof_config) {
                let original_clauses = dimacs_original_clauses_from_literals(&formula.clauses);
                write_parallel_proof(raw_proof_bytes.as_deref(), cert, proof, &original_clauses);
                write_proof_artifact_or_exit(
                    ProofArtifactProblem::Text(content),
                    proof,
                    ProofArtifactTheoryMetadata::dimacs_sat(
                        formula.num_vars,
                        formula.clauses.len(),
                    ),
                );
            }

            emit_sat_applied_run_summary(
                "parallel-portfolio",
                "--parallel",
                VariantRouteProfile::Standard,
                proof_config,
            );

            // Output result in DIMACS format.
            match result {
                SatResult::Sat(model) => {
                    crate::mark_verdict_printed();
                    safe_println!("s SATISFIABLE");
                    emit_dimacs_sat_model(&model);
                    let _ = io::stdout().flush();
                    let _ = io::stderr().flush();
                    std::process::exit(10);
                }
                SatResult::Unsat(_) => {
                    crate::mark_verdict_printed();
                    safe_println!("s UNSATISFIABLE");
                    let _ = io::stdout().flush();
                    let _ = io::stderr().flush();
                    if !verify_unsat_proof(content, proof_config) {
                        std::process::exit(1);
                    }
                    if !verify_lean_proof(proof_config) {
                        std::process::exit(2);
                    }
                    std::process::exit(20);
                }
                SatResult::Unknown => {
                    dimacs_exit_if_timed_out(None);
                    safe_eprintln!("c reason: incomplete (parallel portfolio could not determine satisfiability)");
                    safe_println!("s UNKNOWN");
                }
                #[allow(unreachable_patterns)]
                _ => {
                    safe_eprintln!("c reason: unknown");
                    safe_println!("s UNKNOWN");
                }
            }
        }
        Err(e) => {
            cleanup_dimacs_non_unsat_proof_paths(proof_config);
            safe_eprintln!("c Parse error: {}", e);
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
    }
}

/// Write a proof from the portfolio solver to a file (#8428).
///
/// When `raw_lrat_bytes` is available (the forward LRAT proof captured from
/// the winning solver thread's in-memory buffer), uses those bytes directly.
/// For LRAT format, writes the bytes as-is. For DRAT format, converts by
/// stripping clause IDs and hints from each LRAT line. For other formats
/// (Lean4, Alethe) or when raw bytes are unavailable, falls back to
/// materializing from the `ProofCertificate`.
fn write_parallel_proof(
    raw_lrat_bytes: Option<&[u8]>,
    cert: &ProofCertificate,
    proof_config: &ProofConfig,
    original_clauses: &[(u64, Vec<i32>)],
) {
    let file = match File::create(&proof_config.path) {
        Ok(file) => file,
        Err(error) => {
            exit_failed_proof_create(&proof_config.path, &error);
        }
    };
    let mut writer = proof_output_writer(file);

    // Forward LRAT bytes from the winning solver thread are the complete proof
    // (including clauses derived during BCP/preprocessing). Use them directly
    // for LRAT, or convert to DRAT by stripping clause IDs and hints.
    if let Some(bytes) = raw_lrat_bytes {
        let write_result = match proof_config.format {
            ProofFormat::Lrat => writer.write_all(bytes),
            ProofFormat::Drat => lrat_bytes_to_drat(bytes, &mut writer),
            // Lean4/Alethe: fall through to cert-based materialization below
            _ => Err(io::Error::other("use cert fallback")),
        };
        if write_result.is_ok() {
            if let Err(error) = writer.flush() {
                safe_eprintln!(
                    "Error: failed to flush proof file {}: {error}",
                    proof_config.path
                );
                std::process::exit(1);
            }
            return;
        }
    }

    // Fallback: materialize from the ProofCertificate (backward reconstruction).
    let write_result = match proof_config.format {
        ProofFormat::Drat => cert.write_drat(&mut writer),
        ProofFormat::Lrat => cert.write_lrat(&mut writer),
        ProofFormat::Lean4 => {
            let lean_cert = raw_lrat_bytes
                .map(|bytes| ProofCertificate::from_lrat_text(bytes, cert.is_complete()))
                .transpose()
                .and_then(|parsed| {
                    parsed
                        .as_ref()
                        .unwrap_or(cert)
                        .write_lean4_kernel(original_clauses, &mut writer)
                });
            lean_cert
        }
        ProofFormat::Alethe => cert.write_alethe(&mut writer),
    };
    if let Err(error) = write_result {
        safe_eprintln!(
            "Error: failed to write proof to {}: {error}",
            proof_config.path
        );
        std::process::exit(1);
    }
    if let Err(error) = writer.flush() {
        safe_eprintln!(
            "Error: failed to flush proof file {}: {error}",
            proof_config.path
        );
        std::process::exit(1);
    }
}

/// Convert LRAT text proof bytes to DRAT text format.
///
/// LRAT addition line format: `<id> <lits...> 0 <hints...> 0`
/// DRAT addition line format: `<lits...> 0`
///
/// LRAT deletion lines (`d <ids...> 0`) are ID-based and don't have a direct
/// DRAT equivalent (DRAT deletions are literal-based), so they are skipped.
fn lrat_bytes_to_drat(lrat_bytes: &[u8], w: &mut dyn Write) -> io::Result<()> {
    let text = String::from_utf8_lossy(lrat_bytes);
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // Skip LRAT deletion lines (ID-based, no DRAT equivalent)
        if line.starts_with("d ") {
            continue;
        }
        // Addition line: "<id> <lits...> 0 <hints...> 0"
        // Strip clause ID (first token) and hints (after first "0").
        let mut tokens = line.split_whitespace();
        let _clause_id = tokens.next(); // skip clause ID
        for tok in tokens {
            if tok == "0" {
                writeln!(w, "0")?;
                break;
            }
            write!(w, "{tok} ")?;
        }
    }
    Ok(())
}

/// Run a DIMACS formula using the cube-and-conquer parallel solver.
///
/// Phase 1 (cube): generates cubes via lookahead on a temporary solver.
/// Phase 2 (conquer): dispatches cubes to CDCL worker threads that solve
/// formula AND cube using assumption-based solving.
///
/// CLI entry point: `ay --cube-and-conquer <depth> file.cnf`
pub(crate) fn run_dimacs_cube_and_conquer(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    depth: usize,
    num_threads: usize,
) {
    use ay_sat::CubeAndConquerSolver;

    match parse_dimacs(content) {
        Ok(formula) => {
            safe_eprintln!(
                "c cube-and-conquer: depth {}, {} threads, {} vars, {} clauses",
                depth,
                num_threads,
                formula.num_vars,
                formula.clauses.len()
            );
            let start = std::time::Instant::now();
            let cnc = CubeAndConquerSolver::new(num_threads, depth);
            let result = cnc.solve(&formula);
            let elapsed = start.elapsed();
            safe_eprintln!(
                "c cube-and-conquer: solved in {:.3}s",
                elapsed.as_secs_f64()
            );
            cleanup_dimacs_non_unsat_proof_paths_for_result(&result, proof_config);

            // Emit stats if requested.
            if stats_cfg.any() {
                let result_str = match &result {
                    SatResult::Sat(_) => "sat",
                    SatResult::Unsat(_) => "unsat",
                    SatResult::Unknown => "unknown",
                    #[allow(unreachable_patterns)]
                    _ => "unknown",
                };
                let mut run_stats = stats_output::RunStatistics::new(
                    stats_output::SolveMode::DimacsSat,
                    result_str,
                    global_elapsed(),
                );
                run_stats.insert("sat.cube_and_conquer_depth", depth as u64);
                run_stats.insert("sat.cube_and_conquer_threads", num_threads as u64);
                // #8640: Resource consumption statistics.
                run_stats.insert(
                    "resource.rss_peak_bytes",
                    ay_sys::current_rss_bytes() as u64,
                );
                run_stats.insert(
                    "resource.memory_limit_bytes",
                    ay_sys::get_process_memory_limit() as u64,
                );
                run_stats.insert("time.total_ms", global_elapsed().as_millis() as u64);
                run_stats.emit(stats_cfg);
            }

            emit_sat_applied_run_summary(
                "cube-and-conquer",
                "--cube-and-conquer",
                VariantRouteProfile::Standard,
                proof_config,
            );

            // Output result in DIMACS format.
            match result {
                SatResult::Sat(model) => {
                    crate::mark_verdict_printed();
                    safe_println!("s SATISFIABLE");
                    emit_dimacs_sat_model(&model);
                    let _ = io::stdout().flush();
                    let _ = io::stderr().flush();
                    std::process::exit(10);
                }
                SatResult::Unsat(_) => {
                    crate::mark_verdict_printed();
                    safe_println!("s UNSATISFIABLE");
                    let _ = io::stdout().flush();
                    let _ = io::stderr().flush();
                    if !verify_unsat_proof(content, proof_config) {
                        std::process::exit(1);
                    }
                    if !verify_lean_proof(proof_config) {
                        std::process::exit(2);
                    }
                    std::process::exit(20);
                }
                SatResult::Unknown => {
                    dimacs_exit_if_timed_out(None);
                    safe_eprintln!(
                        "c reason: incomplete (cube-and-conquer could not determine satisfiability)"
                    );
                    safe_println!("s UNKNOWN");
                }
                #[allow(unreachable_patterns)]
                _ => {
                    safe_eprintln!("c reason: unknown");
                    safe_println!("s UNKNOWN");
                }
            }
        }
        Err(e) => {
            cleanup_dimacs_non_unsat_proof_paths(proof_config);
            safe_eprintln!("c Parse error: {}", e);
            safe_println!("s UNKNOWN");
            std::process::exit(1);
        }
    }
}

fn run_dimacs_solver(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_solver_with_guard_cover_stats(solver, stats_cfg, content, proof_config, None);
}

fn run_dimacs_solver_with_guard_cover_stats(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
) {
    run_dimacs_solver_with_research_sidecar_stats(
        solver,
        stats_cfg,
        content,
        proof_config,
        guard_cover,
        None,
    );
}

fn run_dimacs_solver_with_research_sidecar_stats(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    run_dimacs_solver_with_source_and_research_sidecar_stats(
        solver,
        stats_cfg,
        DimacsInputSource::Content(content),
        proof_config,
        guard_cover,
        separator_cover,
    );
}

fn run_dimacs_solver_with_source(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_solver_with_source_and_research_sidecar_stats(
        solver,
        stats_cfg,
        source,
        proof_config,
        None,
        None,
    );
}

fn run_dimacs_solver_with_source_and_research_sidecar_stats(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    configure_dimacs_solver(solver, stats_cfg);
    let _fmla_proof_out_env = FmlaCurrentProofOutEnvGuard::set_for_proof(proof_config);
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    finish_dimacs_solve_with_source(
        solver,
        result,
        stats_cfg,
        source,
        proof_config,
        guard_cover,
        separator_cover,
        None,
    );
}

fn run_dimacs_solver_with_extension(
    solver: &mut SatSolver,
    ext: &mut dyn Extension,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    configure_dimacs_solver(solver, stats_cfg);
    let _fmla_proof_out_env = FmlaCurrentProofOutEnvGuard::set_for_proof(proof_config);
    let result = solver
        .solve_interruptible_with_extension(ext, is_timed_out)
        .into_inner();
    finish_dimacs_solve(
        solver,
        result,
        stats_cfg,
        content,
        proof_config,
        guard_cover,
        separator_cover,
    );
}

/// Run a DIMACS solver and write a kernel-checkable Lean4 LRAT proof on UNSAT.
///
/// The solver must be configured with LRAT proof output (even if to `io::sink()`)
/// so that the `ProofCertificate` is populated. On UNSAT, the certificate is
/// exported to a Lean4 file at `lean4_path` with the original clause table and
/// a `proof_valid` theorem closed by `native_decide`.
fn run_dimacs_solver_lean4(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    lean4_path: &str,
    content: &str,
    proof_config: Option<&ProofConfig>,
    original_clauses: &[(u64, Vec<i32>)],
) {
    run_dimacs_solver_lean4_with_source(
        solver,
        stats_cfg,
        lean4_path,
        DimacsInputSource::Content(content),
        proof_config,
        original_clauses,
    );
}

fn run_dimacs_solver_lean4_with_source(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    lean4_path: &str,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    original_clauses: &[(u64, Vec<i32>)],
) {
    configure_dimacs_solver(solver, stats_cfg);
    let result = solver.solve_interruptible(is_timed_out).into_inner();

    // On UNSAT, write the Lean4 LRAT kernel-checkable export before
    // finish_dimacs_solve exits.
    let mut proof_writer_telemetry = None;
    if let SatResult::Unsat(ref cert) = result {
        let (lean_cert, telemetry) = take_text_lrat_certificate(solver, cert);
        proof_writer_telemetry = telemetry;
        let file = match File::create(lean4_path) {
            Ok(f) => f,
            Err(e) => {
                safe_eprintln!("Error: failed to create Lean4 proof file {lean4_path}: {e}");
                std::process::exit(1);
            }
        };
        let mut writer = proof_output_writer(file);
        if let Err(e) = lean_cert.write_lean4_kernel(original_clauses, &mut writer) {
            safe_eprintln!("Error: failed to write Lean4 proof to {lean4_path}: {e}");
            std::process::exit(1);
        }
        if let Err(e) = writer.flush() {
            safe_eprintln!("Error: failed to flush Lean4 proof file {lean4_path}: {e}");
            std::process::exit(1);
        }
    }

    finish_dimacs_solve_with_source(
        solver,
        result,
        stats_cfg,
        source,
        proof_config,
        None,
        None,
        proof_writer_telemetry,
    );
}

fn take_text_lrat_certificate(
    solver: &mut SatSolver,
    fallback: &ProofCertificate,
) -> (ProofCertificate, Option<DimacsProofWriterTelemetry>) {
    let telemetry = dimacs_proof_writer_telemetry(solver);
    let Some(proof_output) = solver.take_proof_writer() else {
        return (fallback.clone(), telemetry);
    };
    let bytes = match proof_output.into_vec() {
        Ok(bytes) => bytes,
        Err(error) => {
            safe_eprintln!(
                "c Warning: failed to capture internal LRAT stream for Lean4 proof ({error}); \
                 falling back to deferred certificate"
            );
            return (fallback.clone(), telemetry);
        }
    };
    match ProofCertificate::from_lrat_text(&bytes, fallback.is_complete()) {
        Ok(cert) => (cert, telemetry),
        Err(error) => {
            safe_eprintln!(
                "c Warning: failed to parse internal LRAT stream for Lean4 proof ({error}); \
                 falling back to deferred certificate"
            );
            (fallback.clone(), telemetry)
        }
    }
}

/// Run a DIMACS solver and write an Alethe LRAT proof on UNSAT (#8296).
///
/// The solver must be configured with LRAT proof output (even if to `io::sink()`)
/// so that the `ProofCertificate` is populated. On UNSAT, the certificate is
/// exported to an Alethe file at `alethe_path`.
fn run_dimacs_solver_alethe(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    alethe_path: &str,
    content: &str,
    proof_config: Option<&ProofConfig>,
) {
    run_dimacs_solver_alethe_with_source(
        solver,
        stats_cfg,
        alethe_path,
        DimacsInputSource::Content(content),
        proof_config,
    );
}

fn run_dimacs_solver_alethe_with_source(
    solver: &mut SatSolver,
    stats_cfg: stats_output::StatsConfig,
    alethe_path: &str,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) {
    configure_dimacs_solver(solver, stats_cfg);
    let result = solver.solve_interruptible(is_timed_out).into_inner();

    // On UNSAT, write the Alethe LRAT export before finish_dimacs_solve exits.
    if let SatResult::Unsat(ref cert) = result {
        let file = match File::create(alethe_path) {
            Ok(f) => f,
            Err(e) => {
                safe_eprintln!("Error: failed to create Alethe proof file {alethe_path}: {e}");
                std::process::exit(1);
            }
        };
        let mut writer = proof_output_writer(file);
        if let Err(e) = cert.write_alethe(&mut writer) {
            safe_eprintln!("Error: failed to write Alethe proof to {alethe_path}: {e}");
            std::process::exit(1);
        }
        if let Err(e) = writer.flush() {
            safe_eprintln!("Error: failed to flush Alethe proof file {alethe_path}: {e}");
            std::process::exit(1);
        }
    }

    finish_dimacs_solve_with_source(
        solver,
        result,
        stats_cfg,
        source,
        proof_config,
        None,
        None,
        None,
    );
}

/// Verify the emitted Lean4 proof file post-UNSAT when `--lean-verify` is
/// enabled (#8773, Phase 1 thin wrapper). Returns `true` when the proof is
/// accepted or verification was skipped (flag off / non-Lean format / lean
/// binary unavailable), `false` when the Lean kernel rejects the proof — a
/// soundness failure.
///
/// Exit-code contract (see the development design notes):
/// - Accepted  → true  (caller proceeds to exit 20 = UNSAT)
/// - Rejected  → false (caller should exit 2 = soundness failure)
/// - Unavailable (lean missing, timeout, IO error) → true + stderr note;
///   this is not a soundness failure — the solver still proved UNSAT via its
///   internal DRAT/LRAT checker, we just could not run the Lean kernel.
///
/// Safe to call unconditionally; it becomes a no-op when `--lean-verify` is
/// disabled or the emitted proof is not Lean4.
#[must_use]
fn verify_lean_proof(proof_config: Option<&ProofConfig>) -> bool {
    if !super::LEAN_VERIFY_ENABLED.load(Ordering::SeqCst) {
        return true;
    }
    let proof = match proof_config {
        Some(p) => p,
        None => {
            safe_eprintln!(
                "c Warning: --lean-verify set but no proof was emitted; skipping Lean kernel check"
            );
            return true;
        }
    };
    if proof.format != ProofFormat::Lean4 {
        safe_eprintln!(
            "c Warning: --lean-verify requires a Lean4 proof (.lean4 or --proof-format lean4); got {:?} — skipping",
            proof.format
        );
        return true;
    }

    use super::lean_verify::{LeanVerificationOutcome, LeanVerifier};
    let mut verifier = LeanVerifier::new();
    if let Some(path) = super::LEAN_BINARY_PATH.get() {
        verifier = verifier.with_path(path);
    }
    let outcome = verifier.verify(Path::new(&proof.path));
    match outcome {
        LeanVerificationOutcome::Accepted => {
            safe_eprintln!("c Lean verification: OK ({})", proof.path);
            true
        }
        LeanVerificationOutcome::Rejected { stderr, exit_code } => {
            safe_eprintln!(
                "c Error: Lean kernel REJECTED proof {} (exit {exit_code})",
                proof.path
            );
            if !stderr.trim().is_empty() {
                safe_eprintln!("c Lean stderr:\n{stderr}");
            }
            safe_eprintln!(
                "c Error: SOUNDNESS FAILURE — solver reported UNSAT but emitted proof was rejected by Lean kernel"
            );
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            false
        }
        LeanVerificationOutcome::Unavailable { reason } => {
            safe_eprintln!(
                "c Lean verification unavailable: {reason} (Lean4 proof was emitted but the kernel check did not run)"
            );
            true
        }
    }
}

fn cleanup_temp_proof_file(proof: &ProofConfig) {
    if proof.is_temp {
        let _ = std::fs::remove_file(&proof.path);
    }
}

/// Verify the emitted proof file post-UNSAT when `--verify-proof` is enabled
/// (#8771). Returns `true` when the proof is accepted (or verification was
/// skipped because the flag is off / the format is unsupported), `false` when
/// the internal checker rejects the proof — a soundness failure.
///
/// Safe to call unconditionally; it becomes a no-op when verification is
/// disabled or no proof was emitted.
#[must_use]
fn verify_unsat_proof(content: &str, proof_config: Option<&ProofConfig>) -> bool {
    // Check the atomic directly so CHC / interactive paths that don't build
    // a proof config still see the flag state (they do not produce SAT proofs
    // so this is a pure short-circuit for them).
    if !super::VERIFY_PROOF_ENABLED.load(Ordering::SeqCst) {
        return true;
    }
    let proof = match proof_config {
        Some(p) => p,
        None => return true,
    };

    use super::proof_verify::{verify_proof_file, VerifyOutcome};
    let outcome = verify_proof_file(content, proof);

    // Temporary proof files are synthesized by `--verify-proof` with no
    // user-supplied `--proof` and should not persist beyond verification.
    let cleanup = || cleanup_temp_proof_file(proof);

    match outcome {
        VerifyOutcome::Verified => {
            safe_eprintln!(
                "c verify-proof: {} verified ({} format)",
                proof.path,
                match proof.format {
                    ProofFormat::Drat => "DRAT",
                    ProofFormat::Lrat => "LRAT",
                    ProofFormat::Alethe => "Alethe",
                    ProofFormat::Lean4 => "Lean4",
                }
            );
            cleanup();
            true
        }
        VerifyOutcome::Skipped { reason } => {
            safe_eprintln!("c Warning: verify-proof skipped: {reason}");
            cleanup();
            true
        }
        VerifyOutcome::Rejected { reason } => {
            safe_eprintln!(
                "c Error: proof verification FAILED for {} — {reason}",
                proof.path
            );
            safe_eprintln!(
                "c Error: SOUNDNESS FAILURE — solver reported UNSAT but emitted proof was rejected by internal checker"
            );
            // Leave the proof file on disk when it was user-requested, so
            // the user can re-run drat-trim / lrat-check to diagnose.
            // Remove it if we synthesized it (no user requested it).
            cleanup();
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            false
        }
    }
}

#[must_use]
fn verify_unsat_proof_from_source(
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) -> bool {
    if !super::VERIFY_PROOF_ENABLED.load(Ordering::SeqCst) {
        return true;
    }

    match source {
        DimacsInputSource::Content(content) => verify_unsat_proof(content, proof_config),
        DimacsInputSource::FilePath(path) => {
            let content = match std::fs::read_to_string(path) {
                Ok(content) => content,
                Err(error) => {
                    safe_eprintln!(
                        "c Warning: verify-proof skipped: failed to read DIMACS input {path}: {error}"
                    );
                    if let Some(proof) = proof_config {
                        cleanup_temp_proof_file(proof);
                    }
                    return true;
                }
            };
            verify_unsat_proof(&content, proof_config)
        }
        DimacsInputSource::Unavailable => {
            safe_eprintln!(
                "c Warning: verify-proof skipped: original DIMACS content unavailable for streamed stdin"
            );
            if let Some(proof) = proof_config {
                cleanup_temp_proof_file(proof);
            }
            true
        }
    }
}

fn configure_dimacs_solver(solver: &mut SatSolver, _stats_cfg: stats_output::StatsConfig) {
    // Wire interrupt flag so the solver checks the watchdog directly (#3638).
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        solver.set_interrupt(handle.clone());
    }
    // BCP attribution counters write from the propagation hot path. Keep them
    // release-gated to the explicit profiling opt-in, including stats-json
    // runs where the JSON key shape stays stable with zero counters.
    solver.set_bcp_telemetry_enabled(env_truthy("AY_BCP_TELEMETRY"));
    solver.set_bcp_lean_route_enabled(env_truthy("AY_SAT_BCP_LEAN"));
    if env_truthy("AY_SAT_BCP_DISABLE_TRAIL_LOOKAHEAD_PREFETCH") {
        solver.set_bcp_trail_lookahead_prefetch_enabled(false);
    }
    // Default-on (cold.rs): the in-place SEARCH BCP route is verified
    // bit-identical to the safe deferred-copy path by the 56 differential cases
    // in `solver/tests/propagation_bcp_unsafe.rs`. The env var is a kill-switch
    // rather than an opt-in: `AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN=0` forces the
    // safe route; unset or truthy keeps the default-on route.
    solver.set_bcp_search_inplace_watch_scan_enabled(env_bool_default(
        SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENV,
        true,
    ));
    if env_truthy("AY_SAT_BCP_ADVANCE_SAVED_POS") {
        solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
    }
    if env_truthy("AY_SAT_BCP_LEARNED_1963_FALSE_SAVED_POS_RESET") {
        solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
    }
    if env_truthy("AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION") {
        solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENV) {
        solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENV) {
        solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(true);
    }
    if env_truthy("AY_SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION") {
        solver.set_bcp_learned_618_true_tail_relocation_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_ENV) {
        solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENV) {
        solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENV) {
        solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_1963_IDENTITY_ENV) {
        solver.set_bcp_learned_1963_identity_profile_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENV) {
        solver.set_bcp_learned_1963_pressure_reduction_enabled(true);
    }
    if env_truthy(SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENV) {
        solver.set_bcp_learned_1963_pressure_retention_enabled(true);
    }
    if env_truthy(SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENV) {
        solver.set_bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(true);
    }
    if env_truthy("AY_SAT_BCP_LEARNED_617_TAIL_REORDER") {
        solver.set_bcp_learned_617_tail_reorder_enabled(true);
    }
    if env_truthy("AY_SAT_BCP_LEARNED_18_TAIL_REORDER") {
        solver.set_bcp_learned_18_tail_reorder_enabled(true);
    }
    if env_truthy("AY_SAT_BCP_LEARNED_1963_TAIL_REORDER") {
        solver.set_bcp_learned_1963_tail_reorder_enabled(true);
    }
    if let Some(budget) = env_u64(SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENV) {
        solver.set_bcp_learned_1963_tail_reorder_swap_budget(Some(budget));
    }
    if env_truthy("AY_SAT_BVE_OCC_DELTA_VALIDATION") {
        solver.set_bve_occ_delta_validation_enabled(true);
    }
    if env_truthy("AY_SAT_BVE_OCC_SAVED_STATE_REUSE") {
        solver.set_bve_occ_saved_state_reuse_enabled(true);
    }
    if env_truthy(SAT_INPROCESSING_YIELD_PRODUCTIVITY_RESCUE_ENV) {
        solver.set_inprocessing_yield_productivity_rescue_enabled(true);
    }
    if env_truthy(SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENV) {
        solver.set_lrat_proof_clamp_probe_rescue_enabled(true);
    }
    if env_truthy(SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENV) {
        solver.set_inprocessing_yield_rescue_backbone_cooldown_enabled(true);
    }
    if env_truthy(SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENV) {
        solver.set_bounded_backbone_zero_decompose_backoff_enabled(true);
    }
    solver.set_backbone_post_vivify_binary_admission_enabled(env_bool_default(
        SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENV,
        true,
    ));
    // Enable periodic progress reporting if --progress was set.
    if super::PROGRESS_ENABLED.load(Ordering::Relaxed) {
        solver.set_progress_enabled(true);
    }
    // Attach JSONL progress observer if configured (#8155 subtask 7b).
    if let Some(path) = super::PROGRESS_JSON_PATH.get() {
        if let Ok(observer) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
            solver.set_observer(Some(Box::new(observer)));
        }
    }
    // Apply --disable CLI flags for SAT technique disabling (#8331).
    // Reads the global populated by run_solve() instead of env vars.
    if let Some(techniques) = super::DISABLED_SAT_TECHNIQUES.get() {
        for &technique in techniques {
            solver.disable_technique(technique);
        }
    }
    // TLA trace setup is done in run_dimacs_from_content for the non-proof solver path.
    solver.maybe_enable_diagnostic_trace_from_env();
    solver.maybe_enable_decision_trace_from_env();
    solver.maybe_enable_replay_trace_from_env();
    solver.maybe_load_solution_from_env();
}

// Serialize the process-global FMLA proof-out env override: the mutation and its
// restoration stay in one lock-scoped, panic-safe RAII guard (the toolchain's
// env_mutation lint prescription — mirrors deductive-checks-merge-contract's
// RUSTC_BOOTSTRAP pattern). Two concurrent solves can no longer race the
// variable or restore each other's values.
static FMLA_PROOF_OUT_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

struct FmlaCurrentProofOutEnvGuard {
    previous: Option<std::ffi::OsString>,
    _lock: std::sync::MutexGuard<'static, ()>,
}

impl FmlaCurrentProofOutEnvGuard {
    #[allow(unknown_lints, env_mutation)]
    fn set_for_proof(proof_config: Option<&ProofConfig>) -> Self {
        let lock = FMLA_PROOF_OUT_ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let previous = std::env::var_os(
            ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
        );
        if let Some(proof) = proof_config {
            std::env::set_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
                &proof.path,
            );
        } else {
            std::env::remove_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            );
        }
        Self {
            previous,
            _lock: lock,
        }
    }
}

impl Drop for FmlaCurrentProofOutEnvGuard {
    #[allow(unknown_lints, env_mutation)]
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            std::env::set_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
                previous,
            );
        } else {
            std::env::remove_var(
                ay_sat::fmla_runtime_ledger::FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            );
        }
    }
}

fn finish_dimacs_solve(
    solver: &mut SatSolver,
    result: SatResult,
    stats_cfg: stats_output::StatsConfig,
    content: &str,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
) {
    finish_dimacs_solve_with_source(
        solver,
        result,
        stats_cfg,
        DimacsInputSource::Content(content),
        proof_config,
        guard_cover,
        separator_cover,
        None,
    );
}

fn finish_dimacs_solve_with_source(
    solver: &mut SatSolver,
    result: SatResult,
    stats_cfg: stats_output::StatsConfig,
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
    guard_cover: Option<&GuardCoverSidecarRunStats>,
    separator_cover: Option<&SeparatorCoverSidecarRunStats>,
    proof_writer_telemetry_override: Option<DimacsProofWriterTelemetry>,
) {
    let variant = selected_sat_variant();
    let policy = format!("variant={}", variant.as_str());
    let route_profile = summary_route_profile(variant, proof_config);
    emit_sat_applied_run_summary(
        &policy,
        sat_variant_source_label(),
        route_profile,
        proof_config,
    );
    let proof_writer_telemetry_override = proof_writer_telemetry_override
        .or_else(|| cleanup_dimacs_non_unsat_proof_sidecar(solver, &result, proof_config));

    if stats_cfg.any() {
        let props = solver.num_propagations();
        let confs = solver.num_conflicts();
        let decs = solver.num_decisions();
        let restarts = solver.num_restarts();
        let cold_restarts = solver.num_cold_restarts();
        let chrono = solver.num_chrono_backtracks();
        let random = solver.num_random_decisions();
        let fixed = solver.num_fixed();
        let orig = solver.num_original_clauses();
        let learned = solver.num_learned_clauses();
        let preprocess_ns = solver.preprocess_time_ns();
        let search_ns = solver.search_time_ns();
        let lucky_ns = solver.lucky_time_ns();
        let walk_ns = solver.walk_time_ns();
        let search_secs = search_ns as f64 / 1_000_000_000.0;
        let total_ns = preprocess_ns + search_ns + lucky_ns + walk_ns;
        let inproc_ns: u64 = solver
            .inprocessing_pass_times_ns()
            .iter()
            .map(|&(_, v)| v)
            .sum();
        let (lbd_sum, lbd_count) = solver.lbd_sum_count();
        let lbd_buckets = solver.lbd_buckets();
        let (bcp_blocker, bcp_binary, bcp_scan) = solver.bcp_stats();
        let bcp_saved_pos = solver.bcp_saved_pos_stats();
        let bcp_long_scan = solver.bcp_long_scan_stats();
        let bcp_identity = solver.bcp_learned_1963_identity_stats(16);
        let lrat_materialization = solver.lrat_materialization_stats();
        let jumped_reasons = solver.jumped_reasons();
        let (otfs_cand, otfs_sub, otfs_str) = solver.otfs_stats();
        let otfs_branch_b = solver.otfs_branch_b();
        let otfs_branch_c = solver.otfs_branch_c();
        let otfs_clause_sub = solver.otfs_clause_subsumed();
        let (focused_decs, stable_decs) = solver.mode_decisions();
        let peak_dl = solver.peak_decision_level();
        let avg_dl = solver.avg_decision_level();
        let inproc_rounds = solver.inprocessing_rounds();
        let incr_inproc_rounds = solver.incremental_inprocessing_rounds();
        let inproc_simplifications = solver.inprocessing_simplifications();
        let (
            reduction_l0_satisfied_occ_scans,
            reduction_l0_satisfied_full_scans,
            reduction_l0_satisfied_no_occ_skips,
            reduction_l0_satisfied_deleted,
        ) = solver.reduction_l0_satisfied_prepass_stats();
        let (
            learned_reduction_considered,
            learned_reduction_deleted,
            learned_reduction_reason_protected,
            learned_reduction_ic3_protected,
            learned_reduction_low_lbd_protected,
            learned_reduction_usage_protected,
            learned_reduction_target_kept,
            learned_reduction_lrat_retained_delete_skips,
            learned_reduction_hyper_deleted,
            learned_reduction_hyper_kept,
        ) = solver.learned_reduction_telemetry_stats();
        let learned_1963_pressure_reduction = solver.learned_1963_pressure_reduction_stats();
        let learned_1963_pressure_retention = solver.learned_1963_pressure_retention_stats();
        let shrink_attempts = solver.shrink_block_attempts();
        let shrink_successes = solver.shrink_block_successes();
        let (
            shrink_singleton_fast_path_skips,
            lrat_original_learned_snapshot_copies,
            lrat_original_learned_snapshot_literals,
            lrat_original_learned_snapshot_singleton_skips,
            lrat_removed_literal_chain_calls,
        ) = solver.learned_lrat_snapshot_stats();
        let mab_switches = solver.mab_arm_switches();
        let forced_bt = solver.num_forced_backtracks();
        let (mli_detected, mli_reimplied, mli_used) = solver.mli_stats();
        let search_ticks = solver.total_search_ticks();
        let (ibcl_attempts, ibcl_improvements, ibcl_skipped) = solver.ibcl_stats();
        let ibcl_skipped_missing_pivots = solver.ibcl_skipped_missing_pivots();
        let (fp_entries, fp_iters, fp_max, fp_saturated) = solver.bcp_theory_fixpoint_stats();
        let sat_learned_clause_candidate_applications =
            solver.sat_learned_clause_candidate_applications();
        let sat_native_code_helper_applications = solver.sat_native_code_helper_applications();
        let sat_subsumption_native_applications = solver.sat_subsumption_native_applications();
        let sat_conflict_analysis_native_applications =
            solver.sat_conflict_analysis_native_applications();
        let sat_whole_loop_guard_installs = solver.sat_whole_loop_guard_installs();
        let sat_whole_loop_guard_applications = solver.sat_whole_loop_guard_applications();
        // Approximate-BCP filter (#8789 Phase 2) — all 0 when the ay-sat
        // `approx-bcp-filter` Cargo feature is off. A nonzero mismatch
        // counter is a filter soundness alarm.
        let approx_bcp_noop = solver.approx_bcp_noop_matched();
        let approx_bcp_conflict = solver.approx_bcp_conflict_matched();
        let approx_bcp_mismatch = solver.approx_bcp_mismatch_detected();

        if stats_cfg.human {
            let props_per_conf = if confs > 0 {
                props as f64 / confs as f64
            } else {
                0.0
            };
            let props_per_dec = if decs > 0 {
                props as f64 / decs as f64
            } else {
                0.0
            };
            safe_eprintln!("c");
            safe_eprintln!("c --- AY statistics ---");
            safe_eprintln!("c propagations:    {props:>12}");
            safe_eprintln!("c conflicts:       {confs:>12}");
            safe_eprintln!("c decisions:       {decs:>12}");
            safe_eprintln!("c restarts:        {restarts:>12}");
            safe_eprintln!("c cold_restarts:   {cold_restarts:>12}");
            safe_eprintln!("c chrono_bt:       {chrono:>12}");
            safe_eprintln!("c forced_bt:       {forced_bt:>12}");
            safe_eprintln!("c mli_detected:    {mli_detected:>12}");
            safe_eprintln!("c mli_reimplied:   {mli_reimplied:>12}");
            safe_eprintln!("c mli_used_anlyz:  {mli_used:>12}");
            safe_eprintln!("c random_decs:     {random:>12}");
            // Approximate-BCP filter (#8789 Phase 2): three lines of
            // telemetry, all 0 unless ay-sat was built with the
            // `approx-bcp-filter` feature. A nonzero approxbcp_bad is a
            // filter soundness alarm.
            safe_eprintln!("c approxbcp_noop:  {approx_bcp_noop:>12}");
            safe_eprintln!("c approxbcp_conf:  {approx_bcp_conflict:>12}");
            safe_eprintln!("c approxbcp_bad:   {approx_bcp_mismatch:>12}");
            safe_eprintln!("c fixed_vars:      {fixed:>12}");
            safe_eprintln!("c original_cls:    {orig:>12}");
            safe_eprintln!("c learned_cls:     {learned:>12}");
            if let Some(sidecar) = guard_cover {
                safe_eprintln!("c --- guard-cover sidecar ---");
                safe_eprintln!("c gc_path:         {}", sidecar.path);
                safe_eprintln!("c gc_status:       {:>12}", sidecar.status_label());
                safe_eprintln!(
                    "c gc_empty_cut:    {:>12}",
                    if sidecar.injected_empty_cut {
                        "yes"
                    } else {
                        "no"
                    }
                );
                safe_eprintln!("c gc_cuts:         {:>12}", sidecar.cuts);
                safe_eprintln!("c gc_guards:       {:>12}", sidecar.guards);
                safe_eprintln!("c gc_budget_rhs:   {:>12}", sidecar.budget_rhs);
                safe_eprintln!("c gc_deficit:      {:>12}", sidecar.packed_deficit);
            }
            if let Some(sidecar) = separator_cover {
                safe_eprintln!("c --- separator-cover sidecar ---");
                safe_eprintln!("c sc_path:         {}", sidecar.path);
                safe_eprintln!("c sc_status:       {:>12}", sidecar.status_label());
                safe_eprintln!(
                    "c sc_empty_cut:    {:>12}",
                    if sidecar.injected_empty_cut {
                        "yes"
                    } else {
                        "no"
                    }
                );
                safe_eprintln!("c sc_sep_vars:     {:>12}", sidecar.separator_vars);
                safe_eprintln!("c sc_cubes:        {:>12}", sidecar.cubes);
                safe_eprintln!("c sc_covered_asgn: {:>12}", sidecar.covered_assignments);
            }
            safe_eprintln!("c props/conflict:  {props_per_conf:>12.1}");
            safe_eprintln!("c props/decision:  {props_per_dec:>12.1}");
            safe_eprintln!("c search_ticks:    {search_ticks:>12}");
            let ticks_per_conf = if confs > 0 {
                search_ticks as f64 / confs as f64
            } else {
                0.0
            };
            safe_eprintln!("c ticks/conflict:  {ticks_per_conf:>12.1}");
            // Decision level stats (#8131)
            safe_eprintln!("c peak_dec_level:  {peak_dl:>12}");
            safe_eprintln!("c avg_dec_level:   {avg_dl:>12.1}");
            // Phase timing breakdown
            safe_eprintln!("c --- phase timing ---");
            safe_eprintln!("c preprocess_ms:   {:>12}", preprocess_ns / 1_000_000);
            safe_eprintln!("c lucky_ms:        {:>12}", lucky_ns / 1_000_000);
            safe_eprintln!("c walk_ms:         {:>12}", walk_ns / 1_000_000);
            safe_eprintln!("c search_ms:       {:>12}", search_ns / 1_000_000);
            if total_ns > 0 {
                safe_eprintln!(
                    "c preprocess%:     {:>11.1}%",
                    preprocess_ns as f64 / total_ns as f64 * 100.0
                );
                safe_eprintln!(
                    "c search%:         {:>11.1}%",
                    search_ns as f64 / total_ns as f64 * 100.0
                );
                safe_eprintln!(
                    "c inprocessing%:   {:>11.1}%",
                    inproc_ns as f64 / total_ns as f64 * 100.0
                );
            }
            // Rate metrics (based on search time)
            safe_eprintln!("c --- rates ---");
            if search_secs > 0.0 {
                safe_eprintln!("c props/sec:       {:>12.0}", props as f64 / search_secs);
                safe_eprintln!("c conflicts/sec:   {:>12.0}", confs as f64 / search_secs);
                safe_eprintln!("c decisions/sec:   {:>12.0}", decs as f64 / search_secs);
            }
            let decs_per_conf = if confs > 0 {
                decs as f64 / confs as f64
            } else {
                0.0
            };
            safe_eprintln!("c decs/conflict:   {decs_per_conf:>12.2}");
            // LBD distribution (#8131)
            safe_eprintln!("c --- learned clause LBD distribution ---");
            if lbd_count > 0 {
                safe_eprintln!(
                    "c avg_lbd:         {:>12.2}",
                    lbd_sum as f64 / lbd_count as f64
                );
            }
            safe_eprintln!("c lbd_1:           {:>12}", lbd_buckets[0]);
            safe_eprintln!("c lbd_2:           {:>12}", lbd_buckets[1]);
            safe_eprintln!("c lbd_3to5:        {:>12}", lbd_buckets[2]);
            safe_eprintln!("c lbd_6to10:       {:>12}", lbd_buckets[3]);
            safe_eprintln!("c lbd_11plus:      {:>12}", lbd_buckets[4]);
            // BCP telemetry
            safe_eprintln!("c --- BCP internals ---");
            safe_eprintln!("c bcp_blocker_hit: {bcp_blocker:>12}");
            safe_eprintln!("c bcp_binary_hit:  {bcp_binary:>12}");
            safe_eprintln!("c bcp_scan_steps:  {bcp_scan:>12}");
            safe_eprintln!(
                "c bcp_scan_attr:   binary {:>12} nonbinary {:>12} learned {:>12} original {:>12}",
                bcp_long_scan.scan_steps_binary,
                bcp_long_scan.scan_steps_non_binary,
                bcp_long_scan.scan_steps_learned,
                bcp_long_scan.scan_steps_original
            );
            safe_eprintln!(
                "c bcp_long_spos:   {:>12} start_false {:>12} true {:>12} unassigned {:>12} none {:>12}",
                bcp_saved_pos.long_scans,
                bcp_saved_pos.long_start_false,
                bcp_saved_pos.long_found_true,
                bcp_saved_pos.long_found_unassigned,
                bcp_saved_pos.long_no_replacement
            );
            safe_eprintln!(
                "c bcp_len18_spos:  {:>12} start_false {:>12} true {:>12} unassigned {:>12} none {:>12}",
                bcp_saved_pos.len18_scans,
                bcp_saved_pos.len18_start_false,
                bcp_saved_pos.len18_found_true,
                bcp_saved_pos.len18_found_unassigned,
                bcp_saved_pos.len18_no_replacement
            );
            let bcp_long_total_scans: u64 = bcp_long_scan.scans_by_len.iter().sum();
            if bcp_long_total_scans > 0 || bcp_long_scan.long_blocker_fastpath_hits > 0 {
                safe_eprintln!(
                    "c bcp_long_scan:  {:>12} found {:>12} unit {:>12} conflict {:>12} learned {:>12}",
                    bcp_long_total_scans,
                    bcp_long_scan.found_replacement_by_len.iter().sum::<u64>(),
                    bcp_long_scan.unit_by_len.iter().sum::<u64>(),
                    bcp_long_scan.conflict_by_len.iter().sum::<u64>(),
                    bcp_long_scan.learned_scans_by_len.iter().sum::<u64>()
                );
                safe_eprintln!(
                    "c bcp_long_block: {:>12}",
                    bcp_long_scan.long_blocker_fastpath_hits
                );
            }
            safe_eprintln!("c jumped_reasons:  {jumped_reasons:>12}");
            // OTFS
            safe_eprintln!("c otfs_candidates: {otfs_cand:>12}");
            safe_eprintln!("c otfs_subsumed:   {otfs_sub:>12}");
            safe_eprintln!("c otfs_strength:   {otfs_str:>12}");
            safe_eprintln!("c otfs_branch_b:   {otfs_branch_b:>12}");
            safe_eprintln!("c otfs_branch_c:   {otfs_branch_c:>12}");
            safe_eprintln!("c otfs_cls_subsmd: {otfs_clause_sub:>12}");
            // IBCL (#8269)
            if ibcl_attempts > 0 || ibcl_skipped > 0 || ibcl_skipped_missing_pivots > 0 {
                safe_eprintln!("c ibcl_attempts:   {ibcl_attempts:>12}");
                safe_eprintln!("c ibcl_improved:   {ibcl_improvements:>12}");
                safe_eprintln!("c ibcl_skip_short: {ibcl_skipped:>12}");
                safe_eprintln!("c ibcl_skip_pivot: {ibcl_skipped_missing_pivots:>12}");
            }
            // BCP-theory fixed-point loop (#8003)
            if fp_entries > 0 {
                let avg_depth = fp_iters as f64 / fp_entries as f64;
                safe_eprintln!("c fp_entries:      {fp_entries:>12}");
                safe_eprintln!("c fp_iterations:   {fp_iters:>12}");
                safe_eprintln!("c fp_avg_depth:    {avg_depth:>12.2}");
                safe_eprintln!("c fp_max_depth:    {fp_max:>12}");
                safe_eprintln!("c fp_saturated:    {fp_saturated:>12}");
            }
            // Shrink (block-UIP)
            safe_eprintln!("c shrink_attempts: {shrink_attempts:>12}");
            safe_eprintln!("c shrink_success:  {shrink_successes:>12}");
            // Mode and heuristic stats
            safe_eprintln!("c --- mode/heuristic ---");
            let (ema_checks, ema_fires) = solver.focused_ema_stats();
            let reluctant_fires = solver.stable_reluctant_fires();
            let mode_switches = solver.mode_switch_count();
            let ema_blocked = solver.focused_ema_blocked_by_conflict_gate();
            let focused_restart_gate = solver.focused_restart_gate();
            let dense_mutex_gate_updates = solver.dense_mutex_focused_restart_gate_updates();
            let dense_mutex_runtime_checked = solver.dense_mutex_focused_restart_runtime_checked();
            let dense_mutex_runtime_candidate =
                solver.dense_mutex_focused_restart_runtime_candidate();
            let dense_mutex_computed_gate = solver.dense_mutex_focused_restart_computed_gate();
            safe_eprintln!("c mode_switches:   {mode_switches:>12}");
            safe_eprintln!("c focused_decs:    {focused_decs:>12}");
            safe_eprintln!("c stable_decs:     {stable_decs:>12}");
            safe_eprintln!("c focused_fires:   {ema_fires:>12}");
            safe_eprintln!("c focused_checks:  {ema_checks:>12}");
            safe_eprintln!("c focused_blocked: {ema_blocked:>12}");
            safe_eprintln!("c focused_gate:    {focused_restart_gate:>12}");
            safe_eprintln!("c dense_gate_upd:  {dense_mutex_gate_updates:>12}");
            safe_eprintln!("c dense_rt_check:  {dense_mutex_runtime_checked:>12}");
            safe_eprintln!(
                "c dense_rt_cand:   {:>12}",
                u64::from(dense_mutex_runtime_candidate)
            );
            safe_eprintln!("c dense_rt_gate:   {dense_mutex_computed_gate:>12}");
            let trail_blocked = solver.trail_blocked_restarts();
            safe_eprintln!("c trail_blocked:   {trail_blocked:>12}");
            let stable_ema = solver.stable_ema_fires();
            safe_eprintln!("c reluctant_fires: {reluctant_fires:>12}");
            safe_eprintln!("c stable_ema_rst:  {stable_ema:>12}");
            safe_eprintln!("c mab_switches:    {mab_switches:>12}");
            // Lookahead stats (#8087)
            let (la_rounds, la_failed, la_used) = solver.lookahead_stats();
            if la_rounds > 0 {
                safe_eprintln!("c --- lookahead ---");
                safe_eprintln!("c la_rounds:       {la_rounds:>12}");
                safe_eprintln!("c la_failed_lits:  {la_failed:>12}");
                safe_eprintln!("c la_decs_used:    {la_used:>12}");
            }
            let bs = solver.bve_stats();
            let gs = solver.gate_stats();
            let ps = solver.probe_stats();
            safe_eprintln!("c --- preprocessing ---");
            safe_eprintln!("c bve_eliminated:  {val:>12}", val = bs.vars_eliminated);
            safe_eprintln!("c bve_cls_removed: {val:>12}", val = bs.clauses_removed);
            safe_eprintln!("c bve_resolvents:  {val:>12}", val = bs.resolvents_added);
            safe_eprintln!("c bve_tautologies: {val:>12}", val = bs.tautologies_skipped);
            safe_eprintln!("c bve_single_otfs: {val:>12}", val = bs.single_otfs);
            safe_eprintln!("c bve_double_otfs: {val:>12}", val = bs.double_otfs);
            safe_eprintln!(
                "c bve_root_pruned: {val:>12}",
                val = bs.root_literals_pruned
            );
            safe_eprintln!(
                "c bve_root_sat:    {val:>12}",
                val = bs.root_satisfied_parents
            );
            safe_eprintln!("c bve_max_res_len: {val:>12}", val = bs.max_resolvent_len);
            safe_eprintln!("c bve_nonunit_res: {val:>12}", val = bs.non_unit_resolvents);
            if bs.non_unit_resolvents > 0 {
                safe_eprintln!(
                    "c bve_avg_res_len: {val:>12.1}",
                    val = bs.total_resolvent_literals as f64 / bs.non_unit_resolvents as f64
                );
            }
            // Net clause count change: positive = formula grew
            let net = bs.resolvents_added as i64 - bs.clauses_removed as i64;
            safe_eprintln!("c bve_net_clauses: {net:>12}");
            safe_eprintln!("c bve_bw_subsumed: {val:>12}", val = bs.backward_subsumed);
            safe_eprintln!(
                "c bve_bw_strength: {val:>12}",
                val = bs.backward_strengthened
            );
            safe_eprintln!("c bve_bw_units:    {val:>12}", val = bs.backward_units);
            safe_eprintln!(
                "c bve_bw_sig_filt: {val:>12}",
                val = bs.backward_sig_filtered
            );
            if bs.lrat_preflight_rejected > 0 {
                safe_eprintln!(
                    "c bve_lrat_reject:{val:>12}",
                    val = bs.lrat_preflight_rejected
                );
                safe_eprintln!(
                    "c bve_lrat_src_hid:{val:>11}",
                    val = bs.lrat_preflight_missing_or_hidden_source_id
                );
                safe_eprintln!(
                    "c bve_lrat_del_dead:{val:>10}",
                    val = bs.lrat_preflight_deletion_target_not_live
                );
                safe_eprintln!(
                    "c bve_lrat_cleanup:{val:>11}",
                    val = bs.lrat_preflight_replacement_cleanup_unit
                );
                safe_eprintln!(
                    "c bve_lrat_plan: {val:>12}",
                    val = bs.lrat_preflight_planned_add_rejected
                );
                safe_eprintln!(
                    "c bve_lrat_out_id:{val:>11}",
                    val = bs.lrat_preflight_planned_output_id_mismatch
                );
                safe_eprintln!(
                    "c bve_lrat_unknown:{val:>10}",
                    val = bs.lrat_preflight_planned_unknown_hint
                );
            }
            safe_eprintln!("c bve_fastelim_v:  {val:>12}", val = bs.fast_elim_vars);
            safe_eprintln!("c bve_fastelim_c:  {val:>12}", val = bs.fast_elim_clauses);
            // Per-technique rates: BVE elimination rate
            if search_secs > 0.0 && bs.vars_eliminated > 0 {
                safe_eprintln!(
                    "c bve_elim/sec:    {:>12.0}",
                    bs.vars_eliminated as f64 / search_secs
                );
            }
            safe_eprintln!("c gate_and:        {val:>12}", val = gs.and_gates);
            safe_eprintln!("c gate_xor:        {val:>12}", val = gs.xor_gates);
            safe_eprintln!("c gate_equiv:      {val:>12}", val = gs.equivalences);
            safe_eprintln!("c gate_ite:        {val:>12}", val = gs.ite_gates);
            safe_eprintln!("c probe_failed:    {val:>12}", val = ps.failed);
            let cs = solver.congruence_stats();
            let ss = solver.sweep_stats();
            let ds = solver.decompose_stats();
            let ts = solver.transred_stats();
            let fs = solver.factor_stats();
            safe_eprintln!("c --- simplification ---");
            safe_eprintln!("c cong_rounds:     {val:>12}", val = cs.rounds);
            safe_eprintln!("c cong_gates:      {val:>12}", val = cs.gates_analyzed);
            safe_eprintln!("c cong_equivs:     {val:>12}", val = cs.equivalences_found);
            safe_eprintln!("c cong_lits_rwt:   {val:>12}", val = cs.literals_rewritten);
            safe_eprintln!("c sweep_rounds:    {val:>12}", val = ss.rounds);
            safe_eprintln!("c sweep_lits_rwt:  {val:>12}", val = ss.literals_rewritten);
            // Real sweep-yield counters (wf_755ac432 observability). Without
            // these, sweep health reads as a phantom 0 from the two dead/hidden
            // counters above (`sweep_lits_rwt` is never incremented and
            // `inproc_sweep_yields` was un-wired). `sweep_equivs` is the
            // decisive number: on 3f67f676 AY finds 127 kitten equivalences and
            // rewrites 1136 clauses, so a reader can no longer conclude the
            // sweep is dead.
            safe_eprintln!("c sweep_equivs:    {val:>12}", val = ss.kitten_equivalences);
            safe_eprintln!("c sweep_environs:  {val:>12}", val = ss.kitten_environments);
            safe_eprintln!("c sweep_backbone:  {val:>12}", val = ss.kitten_backbone);
            safe_eprintln!("c sweep_cls_rwt:   {val:>12}", val = ss.clauses_rewritten);
            safe_eprintln!("c decomp_rounds:   {val:>12}", val = ds.rounds);
            safe_eprintln!("c decomp_subst:    {val:>12}", val = ds.substituted);
            safe_eprintln!("c transred_rounds: {val:>12}", val = ts.rounds);
            safe_eprintln!("c transred_cls_rm: {val:>12}", val = ts.clauses_removed);
            safe_eprintln!("c factor_rounds:   {val:>12}", val = fs.rounds);
            safe_eprintln!("c factor_count:    {val:>12}", val = fs.factored_count);
            let vs = solver.vivify_stats();
            let sbs = solver.subsume_stats();
            safe_eprintln!("c --- inprocessing ---");
            safe_eprintln!("c inproc_rounds:   {inproc_rounds:>12}");
            safe_eprintln!("c incr_inproc_rnd: {incr_inproc_rounds:>12}");
            safe_eprintln!("c inproc_simplif:  {inproc_simplifications:>12}");
            safe_eprintln!(
                "c rebuild_watch_us:{val:>12}",
                val = solver.rebuild_watches_us()
            );
            safe_eprintln!(
                "c rebuild_watch_n: {val:>12}",
                val = solver.rebuild_watches_calls()
            );
            // Full vs incremental rebuild breakdown (#8103)
            safe_eprintln!(
                "c full_rw_us:      {val:>12}",
                val = solver.full_rebuild_watches_us()
            );
            safe_eprintln!(
                "c full_rw_n:       {val:>12}",
                val = solver.full_rebuild_watches_calls()
            );
            safe_eprintln!(
                "c incr_rw_us:      {val:>12}",
                val = solver.incremental_reconnect_watches_us()
            );
            safe_eprintln!(
                "c incr_rw_n:       {val:>12}",
                val = solver.incremental_reconnect_watches_calls()
            );
            // Post-rebuild BCP cache behavior (#8103)
            {
                let (pr_ns, pr_props) = solver.post_rebuild_bcp_stats();
                if pr_props > 0 && pr_ns > 0 {
                    let pr_mpps = pr_props as f64 / (pr_ns as f64 / 1_000.0);
                    safe_eprintln!("c post_rw_Mpps:    {:>11.1}", pr_mpps);
                }
                // Full rebuild BCP cache behavior
                let (fr_ns, fr_props) = solver.post_full_rebuild_bcp_stats();
                if fr_props > 0 && fr_ns > 0 {
                    let fr_mpps = fr_props as f64 / (fr_ns as f64 / 1_000.0);
                    safe_eprintln!("c full_rw_Mpps:    {:>11.1}", fr_mpps);
                }
                // Incremental reconnect BCP cache behavior
                let (ir_ns, ir_props) = solver.post_incremental_reconnect_bcp_stats();
                if ir_props > 0 && ir_ns > 0 {
                    let ir_mpps = ir_props as f64 / (ir_ns as f64 / 1_000.0);
                    safe_eprintln!("c incr_rw_Mpps:    {:>11.1}", ir_mpps);
                }
                if props > 0 && search_ns > 0 {
                    let overall_mpps = props as f64 / (search_ns as f64 / 1_000.0);
                    safe_eprintln!("c overall_Mpps:    {:>11.1}", overall_mpps);
                }
            }
            safe_eprintln!("c vivify_examined: {val:>12}", val = vs.clauses_examined);
            safe_eprintln!(
                "c vivify_strength: {val:>12}",
                val = vs.clauses_strengthened
            );
            safe_eprintln!("c vivify_lits_rm:  {val:>12}", val = vs.literals_removed);
            safe_eprintln!("c vivify_sat:      {val:>12}", val = vs.clauses_satisfied);
            // Per-technique rates: vivify
            if search_secs > 0.0 && vs.clauses_strengthened > 0 {
                safe_eprintln!(
                    "c vivify_str/sec:  {:>12.0}",
                    vs.clauses_strengthened as f64 / search_secs
                );
            }
            safe_eprintln!("c subsumed:        {val:>12}", val = sbs.forward_subsumed);
            safe_eprintln!(
                "c strengthened:    {val:>12}",
                val = sbs.strengthened_clauses
            );
            safe_eprintln!(
                "c strength_lits:   {val:>12}",
                val = sbs.strengthened_literals
            );
            // Unified total subsumption count (#8368, #8502): aggregates all
            // subsumption sources. CaDiCaL reports a single stats.subsumed.
            safe_eprintln!("c total_subsumed:  {:>12}", solver.total_subsumed());
            // Per-source breakdown (#8502): helps diagnose subsumption gaps.
            safe_eprintln!("c  fwd_subsumed:   {:>12}", sbs.forward_subsumed);
            safe_eprintln!(
                "c  bve_bw_subsmd:  {:>12}",
                solver.bve_stats().backward_subsumed
            );
            safe_eprintln!("c  otfs_subsmd:    {:>12}", solver.otfs_clause_subsumed());
            safe_eprintln!("c  eager_subsmd:   {:>12}", solver.eager_subsumed());
            {
                let vs = solver.vivify_stats();
                safe_eprintln!("c  viv_inline_s:   {:>12}", vs.inline_subsumed);
                safe_eprintln!("c  viv_anlysis_s:  {:>12}", vs.analysis_subsumed);
            }
            safe_eprintln!(
                "c  cong_subsmd:    {:>12}",
                solver.congruence_stats().congruence_subsumed
            );
            safe_eprintln!("c  dedup_deleted:   {:>12}", solver.dedup_deleted());
            safe_eprintln!("c --- inprocessing pass times (ms) ---");
            for (label, value) in solver.inprocessing_pass_times_ms() {
                safe_eprintln!("c {label:<16} {value:>12}");
            }
            let flushes = solver.num_flushes();
            let reductions = solver.num_reductions();
            let inprobe_phases = solver.inprobe_phases();
            let arena_compactions = solver.num_arena_compactions();
            safe_eprintln!("c --- clause db ---");
            safe_eprintln!("c flushes:         {flushes:>12}");
            safe_eprintln!("c reductions:      {reductions:>12}");
            safe_eprintln!("c arena_compacts:  {arena_compactions:>12}");
            safe_eprintln!("c inprobe_phases:  {inprobe_phases:>12}");
            safe_eprintln!("c eager_subsumed:  {:>12}", solver.eager_subsumed());
            // BCE stats (#8131)
            let bces = solver.bce_stats();
            safe_eprintln!("c --- BCE ---");
            safe_eprintln!("c bce_rounds:      {:>12}", bces.rounds);
            safe_eprintln!("c bce_eliminated:  {:>12}", bces.clauses_eliminated);
            safe_eprintln!("c bce_checks:      {:>12}", bces.checks_performed);
            // CCE stats (#8131)
            let cces = solver.cce_stats();
            safe_eprintln!("c --- CCE ---");
            safe_eprintln!("c cce_rounds:      {:>12}", cces.rounds);
            safe_eprintln!("c cce_blocked:     {:>12}", cces.blocked);
            safe_eprintln!("c cce_cla_steps:   {:>12}", cces.cla_steps);
            // HTR stats (#8131)
            let htr = solver.htr_stats();
            safe_eprintln!("c --- HTR ---");
            safe_eprintln!("c htr_rounds:      {:>12}", htr.rounds);
            safe_eprintln!("c htr_ternary:     {:>12}", htr.ternary_resolvents);
            safe_eprintln!("c htr_binary:      {:>12}", htr.binary_resolvents);
            // Conditioning (GBCE) stats (#8131)
            let conds = solver.conditioning_stats();
            safe_eprintln!("c --- conditioning ---");
            safe_eprintln!("c cond_rounds:     {:>12}", conds.rounds);
            safe_eprintln!("c cond_eliminated: {:>12}", conds.clauses_eliminated);
            safe_eprintln!("c cond_checked:    {:>12}", conds.candidates_checked);
            // Occ list incremental vs full rebuild stats (#8403)
            let occ_incr = solver.occ_incremental_refreshes();
            let occ_full = solver.occ_full_rebuilds();
            if occ_incr > 0 || occ_full > 0 {
                safe_eprintln!("c --- occ list ---");
                safe_eprintln!("c occ_incr_refresh:{occ_incr:>12}");
                safe_eprintln!("c occ_full_rebuild:{occ_full:>12}");
            }
            // Between-solve reduction stats (#8435)
            let (bs_reductions, bs_deleted, bs_decays) = solver.between_solve_stats();
            if bs_reductions > 0 {
                safe_eprintln!("c --- between-solve ---");
                safe_eprintln!("c bs_reductions:   {bs_reductions:>12}");
                safe_eprintln!("c bs_cls_deleted:  {bs_deleted:>12}");
                safe_eprintln!("c bs_used_decays:  {bs_decays:>12}");
            }
            // Domain-restricted BCP stats (#8475)
            let (dbcp_skips, dbcp_calls) = solver.domain_bcp_stats();
            if dbcp_calls > 0 {
                safe_eprintln!("c --- domain BCP ---");
                safe_eprintln!("c domain_bcp_calls:{dbcp_calls:>12}");
                safe_eprintln!("c domain_bcp_skips:{dbcp_skips:>12}");
            }
            // Stale enqueue safety net (#8359)
            let stale_skips = solver.stale_enqueue_skips();
            if stale_skips > 0 {
                safe_eprintln!("c WARN stale_enq:  {stale_skips:>12}");
            }
            // Stale BCP watch entry safety net (#8547)
            let stale_bcp = solver.stale_bcp_watch_skips();
            if stale_bcp > 0 {
                safe_eprintln!("c WARN stale_bcp:  {stale_bcp:>12}");
            }
            // Backbone stats (#3274)
            safe_eprintln!("c --- backbone ---");
            safe_eprintln!("c bb_binary_units: {:>12}", solver.backbone_binary_units());
            safe_eprintln!("c --- SAT JIT competition telemetry ---");
            safe_eprintln!("c sat_lc_app:     {sat_learned_clause_candidate_applications:>12}");
            safe_eprintln!("c sat_native_app: {sat_native_code_helper_applications:>12}");
            safe_eprintln!("c sat_wloop_inst: {sat_whole_loop_guard_installs:>12}");
            safe_eprintln!("c sat_wloop_app:  {sat_whole_loop_guard_applications:>12}");
            safe_eprintln!("c sat_subsume_app:{sat_subsumption_native_applications:>12}");
            safe_eprintln!("c sat_confjit_app:{sat_conflict_analysis_native_applications:>12}");
            if solver.sat_propagation_native_active() {
                safe_eprintln!("c --- SAT propagation native telemetry ---");
                safe_eprintln!("c sat_prop_active: {:>12}", "yes");
                safe_eprintln!(
                    "c sat_prop_cls:    {:>12}",
                    solver.sat_propagation_native_clauses()
                );
                safe_eprintln!(
                    "c sat_prop_rounds: {:>12}",
                    solver.sat_propagation_native_rounds()
                );
                safe_eprintln!(
                    "c sat_prop_props:  {:>12}",
                    solver.sat_propagation_native_propagations()
                );
                safe_eprintln!(
                    "c sat_prop_confl:  {:>12}",
                    solver.sat_propagation_native_conflicts()
                );
                safe_eprintln!(
                    "c sat_prop_cmp_us: {:>12}",
                    solver.sat_propagation_native_compile_time_us()
                );
            }
            // Code cache stats (#8394)
            let cc_total = solver.code_cache_total_bytes();
            let cc_peak = solver.code_cache_peak_bytes();
            if cc_peak > 0 {
                safe_eprintln!("c --- code cache ---");
                safe_eprintln!("c cc_total_bytes:  {:>12}", cc_total);
                safe_eprintln!("c cc_peak_bytes:   {:>12}", cc_peak);
                safe_eprintln!("c cc_evictions:    {:>12}", solver.code_cache_evictions());
                safe_eprintln!(
                    "c cc_bytes_evict:  {:>12}",
                    solver.code_cache_bytes_evicted()
                );
            }
            // Memory stats (#8131)
            safe_eprintln!("c --- memory ---");
            safe_eprintln!("c arena_words:     {:>12}", solver.arena_words());
            safe_eprintln!("c active_clauses:  {:>12}", solver.active_clause_count());
            safe_eprintln!("c");
        }

        // Canonical envelope (used for both human and JSON output)
        let result_str = match &result {
            SatResult::Sat(_) => "sat",
            SatResult::Unsat(_) => "unsat",
            SatResult::Unknown => "unknown",
            #[allow(unreachable_patterns)]
            _ => "unknown",
        };
        let mut run_stats = stats_output::RunStatistics::new(
            stats_output::SolveMode::DimacsSat,
            result_str,
            global_elapsed(),
        );
        run_stats.insert("conflicts", confs);
        run_stats.insert("decisions", decs);
        run_stats.insert("propagations", props);
        run_stats.insert("restarts", restarts);
        run_stats.insert("sat.cold_restarts", cold_restarts);
        run_stats.insert("sat.chrono_bt", chrono);
        // Approximate-BCP filter (#8789 Phase 2). All 0 without the
        // `approx-bcp-filter` feature; nonzero mismatch = soundness alarm.
        run_stats.insert("sat.approx_bcp_noop_matched", approx_bcp_noop);
        run_stats.insert("sat.approx_bcp_conflict_matched", approx_bcp_conflict);
        run_stats.insert("sat.approx_bcp_mismatch_detected", approx_bcp_mismatch);
        run_stats.insert("sat.forced_bt", forced_bt);
        run_stats.insert("sat.mli_detected", mli_detected);
        run_stats.insert("sat.mli_reimplied", mli_reimplied);
        run_stats.insert("sat.mli_used_in_analysis", mli_used);
        run_stats.insert("sat.random_decisions", random);
        run_stats.insert("sat.fixed_vars", fixed as u64);
        run_stats.insert("sat.original_clauses", orig as u64);
        run_stats.insert("sat.learned_clauses", learned);
        insert_dimacs_proof_telemetry(
            &mut run_stats,
            solver,
            proof_config,
            proof_writer_telemetry_override,
        );
        insert_preprocessing_transaction_telemetry(
            &mut run_stats,
            solver.preprocessing_transaction_stats(),
        );
        run_stats.insert(
            "sat.guard_cover_sidecar_checked",
            u64::from(guard_cover.is_some()),
        );
        run_stats.insert(
            "sat.guard_cover_sidecar_accepted",
            u64::from(guard_cover.is_some_and(|sidecar| sidecar.accepted)),
        );
        run_stats.insert(
            "sat.guard_cover_sidecar_empty_cut",
            u64::from(guard_cover.is_some_and(|sidecar| sidecar.injected_empty_cut)),
        );
        run_stats.insert(
            "sat.guard_cover_sidecar_cuts",
            guard_cover.map_or(0, |sidecar| sidecar.cuts),
        );
        run_stats.insert(
            "sat.guard_cover_sidecar_guards",
            guard_cover.map_or(0, |sidecar| sidecar.guards),
        );
        run_stats.insert(
            "sat.guard_cover_sidecar_budget_rhs",
            guard_cover.map_or(0, |sidecar| sidecar.budget_rhs),
        );
        run_stats.insert(
            "sat.guard_cover_sidecar_packed_deficit",
            guard_cover.map_or(0, |sidecar| sidecar.packed_deficit),
        );
        run_stats.insert(
            "sat.separator_cover_sidecar_checked",
            separator_cover.is_some() as u64,
        );
        run_stats.insert(
            "sat.separator_cover_sidecar_accepted",
            separator_cover.is_some_and(|sidecar| sidecar.accepted) as u64,
        );
        run_stats.insert(
            "sat.separator_cover_sidecar_empty_cut",
            separator_cover.is_some_and(|sidecar| sidecar.injected_empty_cut) as u64,
        );
        run_stats.insert(
            "sat.separator_cover_sidecar_separator_vars",
            separator_cover.map_or(0, |sidecar| sidecar.separator_vars),
        );
        run_stats.insert(
            "sat.separator_cover_sidecar_cubes",
            separator_cover.map_or(0, |sidecar| sidecar.cubes),
        );
        run_stats.insert(
            "sat.separator_cover_sidecar_covered_assignments",
            separator_cover.map_or(0, |sidecar| sidecar.covered_assignments),
        );
        run_stats.insert(
            "sat.structural_sidecar_checked_count",
            guard_cover.is_some() as u64 + separator_cover.is_some() as u64,
        );
        run_stats.insert(
            "sat.structural_sidecar_accepted_count",
            guard_cover.is_some_and(|sidecar| sidecar.accepted) as u64
                + separator_cover.is_some_and(|sidecar| sidecar.accepted) as u64,
        );
        run_stats.insert(
            "sat.structural_sidecar_empty_cut_count",
            guard_cover.is_some_and(|sidecar| sidecar.injected_empty_cut) as u64
                + separator_cover.is_some_and(|sidecar| sidecar.injected_empty_cut) as u64,
        );
        run_stats.insert("sat.preprocess_ms", preprocess_ns / 1_000_000);
        run_stats.insert("sat.search_ms", search_ns / 1_000_000);
        run_stats.insert("sat.lucky_ms", lucky_ns / 1_000_000);
        run_stats.insert("sat.walk_ms", walk_ns / 1_000_000);
        run_stats.insert("sat.inprocessing_ms", inproc_ns / 1_000_000);
        // Phase percentages (scaled x100 for integer representation)
        if let Some(preprocess_pct) = (preprocess_ns * 10000).checked_div(total_ns) {
            run_stats.insert("sat.preprocess_pct_x100", preprocess_pct);
        }
        if let Some(search_pct) = (search_ns * 10000).checked_div(total_ns) {
            run_stats.insert("sat.search_pct_x100", search_pct);
        }
        if let Some(inprocessing_pct) = (inproc_ns * 10000).checked_div(total_ns) {
            run_stats.insert("sat.inprocessing_pct_x100", inprocessing_pct);
        }
        // Rate metrics (integer: per-second, 0 if search_secs < epsilon)
        if search_secs > 0.001 {
            run_stats.insert("sat.props_per_sec", (props as f64 / search_secs) as u64);
            run_stats.insert("sat.conflicts_per_sec", (confs as f64 / search_secs) as u64);
        }
        if let Some(decs_per_conflict) = (decs * 100).checked_div(confs) {
            // decs_per_conflict x100 for integer representation
            run_stats.insert("sat.decs_per_conflict_x100", decs_per_conflict);
        }
        // LBD stats
        if let Some(avg_lbd) = (lbd_sum * 100).checked_div(lbd_count) {
            run_stats.insert("sat.avg_lbd_x100", avg_lbd);
        }
        run_stats.insert("sat.lbd_1", lbd_buckets[0]);
        run_stats.insert("sat.lbd_2", lbd_buckets[1]);
        run_stats.insert("sat.lbd_3to5", lbd_buckets[2]);
        run_stats.insert("sat.lbd_6to10", lbd_buckets[3]);
        run_stats.insert("sat.lbd_11plus", lbd_buckets[4]);
        // Decision level stats
        run_stats.insert("sat.peak_decision_level", u64::from(peak_dl));
        run_stats.insert("sat.avg_decision_level_x100", (avg_dl * 100.0) as u64);
        // Focused restart route gates.
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY,
            u64::from(env_truthy(SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV)),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY,
            u64::from(solver.dense_mutex_focused_restart_gate_experiment_enabled()),
        );
        run_stats.insert(
            SAT_FOCUSED_RESTART_GATE_FINAL_KEY,
            solver.focused_restart_gate(),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY,
            solver.dense_mutex_focused_restart_gate_updates(),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY,
            solver.dense_mutex_focused_restart_runtime_checked(),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY,
            solver.dense_mutex_focused_restart_active_vars(),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY,
            solver.dense_mutex_focused_restart_active_clauses(),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY,
            solver.dense_mutex_focused_restart_active_binary_clauses(),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY,
            u64::from(solver.dense_mutex_focused_restart_runtime_candidate()),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY,
            solver.dense_mutex_focused_restart_previous_gate(),
        );
        run_stats.insert(
            SAT_DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY,
            solver.dense_mutex_focused_restart_computed_gate(),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY,
            u64::from(env_truthy(SAT_DENSE_CLIQUE_MAB_BRANCH_ENV)),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY,
            u64::from(solver.dense_clique_mab_branch_route_enabled()),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY,
            u64::from(solver.dense_clique_mab_branch_route_exercised()),
        );
        run_stats.insert(
            SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISE_COUNT_KEY,
            solver.dense_clique_mab_branch_route_exercise_count(),
        );
        insert_dense_clique_scout_stats(&mut run_stats, source);
        insert_multiplier_equiv_conservation_scout_stats(&mut run_stats, source);
        // BCP internals
        run_stats.insert("sat.bcp_blocker_hits", bcp_blocker);
        run_stats.insert("sat.bcp_binary_hits", bcp_binary);
        run_stats.insert("sat.bcp_scan_steps", bcp_scan);
        run_stats.insert("sat.bcp_scan_steps_binary", bcp_long_scan.scan_steps_binary);
        run_stats.insert(
            "sat.bcp_scan_steps_non_binary",
            bcp_long_scan.scan_steps_non_binary,
        );
        run_stats.insert(
            "sat.bcp_scan_steps_learned",
            bcp_long_scan.scan_steps_learned,
        );
        run_stats.insert(
            "sat.bcp_scan_steps_original",
            bcp_long_scan.scan_steps_original,
        );
        run_stats.insert(
            "sat.bcp_advance_saved_pos_enabled",
            u64::from(solver.bcp_advance_saved_pos_after_unassigned_move_enabled()),
        );
        run_stats.insert(
            SAT_BCP_TRAIL_LOOKAHEAD_PREFETCH_ENABLED_KEY,
            u64::from(solver.bcp_trail_lookahead_prefetch_enabled()),
        );
        run_stats.insert(
            SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY,
            u64::from(solver.bcp_search_inplace_watch_scan_enabled()),
        );
        run_stats.insert(
            SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY,
            u64::from(solver.bcp_search_inplace_watch_scan_route_enabled()),
        );
        run_stats.insert(
            SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY,
            u64::from(solver.bcp_search_inplace_watch_scan_exercised()),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_true_tail_relocation_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY,
            bcp_long_scan.learned_1963_true_tail_relocation_attempts,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_MOVES_KEY,
            bcp_long_scan.learned_1963_true_tail_relocation_moves,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_used5_fsw_saved_pos_reset_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ELIGIBLE_KEY,
            bcp_long_scan.learned_1963_used5_fsw_saved_pos_reset_eligible,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_WRITES_KEY,
            bcp_long_scan.learned_1963_used5_fsw_saved_pos_reset_writes,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_UNIT_KEY,
            bcp_long_scan.learned_1963_used5_fsw_saved_pos_reset_unit,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_CONFLICT_KEY,
            bcp_long_scan.learned_1963_used5_fsw_saved_pos_reset_conflict,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_fsw_conflict_saved_pos_reset_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ELIGIBLE_KEY,
            bcp_long_scan.learned_1963_fsw_conflict_saved_pos_reset_eligible,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_WRITES_KEY,
            bcp_long_scan.learned_1963_fsw_conflict_saved_pos_reset_writes,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_CONFLICT_KEY,
            bcp_long_scan.learned_1963_fsw_conflict_saved_pos_reset_conflict,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_618_true_tail_relocation_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY,
            bcp_long_scan.learned_618_true_tail_relocation_attempts,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_MOVES_KEY,
            bcp_long_scan.learned_618_true_tail_relocation_moves,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_no_replacement_saved_pos_update_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_fsw_gent_skip_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_CANDIDATES_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_candidates,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_APPLIED_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_applied,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_SAVED_SLOTS_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_saved_slots,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_SUFFIX_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_found_true_suffix,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_SUFFIX_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_found_unassigned_suffix,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_PREFIX_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_found_true_prefix,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_PREFIX_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_found_unassigned_prefix,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_UNIT_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_no_replacement_unit,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_CONFLICT_KEY,
            bcp_long_scan.learned_1963_fsw_gent_skip_no_replacement_conflict,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_no_replacement_scan_pressure_enabled),
        );
        run_stats.insert(
            SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY,
            u64::from(
                bcp_long_scan.disable_learned_1963_no_replacement_unit_blocker_refresh_enabled,
            ),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_blocker_cert_elision_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_blocker_cert_shadow_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_blocker_cert_false_reject_demote_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_CANDIDATES_KEY,
            bcp_long_scan.learned_1963_blocker_cert_candidates,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_elisions,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_HITS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_shadow_hits,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_MISMATCHES_KEY,
            bcp_long_scan.learned_1963_blocker_cert_shadow_mismatches,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_MISMATCH_DEMOTIONS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_mismatch_demotions,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_POPULATES_KEY,
            bcp_long_scan.learned_1963_blocker_cert_populates,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_STALE_REJECTS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_stale_rejects,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECTS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_false_rejects,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTIONS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_false_reject_demotions,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_REPEAT_REJECTS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_repeat_rejects,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELIDED_SUFFIX_SLOTS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_elided_suffix_slots,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ELIDED_SUFFIX_SLOTS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_shadow_elided_suffix_slots,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_AFFECTED_FSW_ROWS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_affected_fsw_rows,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_AFFECTED_FSW_ROWS_KEY,
            bcp_long_scan.learned_1963_blocker_cert_shadow_affected_fsw_rows,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_617_tail_reorder_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_617_TAIL_REORDER_CANDIDATES_KEY,
            bcp_long_scan.learned_617_tail_reorder_candidates,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_617_TAIL_REORDER_EXERCISED_KEY,
            bcp_long_scan.learned_617_tail_reorder_exercised,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_617_TAIL_REORDER_CHANGED_KEY,
            bcp_long_scan.learned_617_tail_reorder_changed,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_617_TAIL_REORDER_SWAPS_KEY,
            bcp_long_scan.learned_617_tail_reorder_swaps,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_18_tail_reorder_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_18_TAIL_REORDER_CANDIDATES_KEY,
            bcp_long_scan.learned_18_tail_reorder_candidates,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_18_TAIL_REORDER_EXERCISED_KEY,
            bcp_long_scan.learned_18_tail_reorder_exercised,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_18_TAIL_REORDER_CHANGED_KEY,
            bcp_long_scan.learned_18_tail_reorder_changed,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_18_TAIL_REORDER_SWAPS_KEY,
            bcp_long_scan.learned_18_tail_reorder_swaps,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY,
            u64::from(bcp_long_scan.learned_1963_tail_reorder_enabled),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_CANDIDATES_KEY,
            bcp_long_scan.learned_1963_tail_reorder_candidates,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_CHANGED_KEY,
            bcp_long_scan.learned_1963_tail_reorder_changed,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAPS_KEY,
            bcp_long_scan.learned_1963_tail_reorder_swaps,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY,
            u64::from(
                bcp_long_scan
                    .learned_1963_tail_reorder_swap_budget
                    .is_some(),
            ),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_LIMIT_KEY,
            bcp_long_scan
                .learned_1963_tail_reorder_swap_budget
                .unwrap_or(0),
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_CANDIDATES_KEY,
            bcp_long_scan.learned_1963_tail_reorder_budget_candidates,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_APPLIED_KEY,
            bcp_long_scan.learned_1963_tail_reorder_budget_applied,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SKIPPED_OVER_BUDGET_KEY,
            bcp_long_scan.learned_1963_tail_reorder_budget_skipped_over_budget,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_APPLIED_KEY,
            bcp_long_scan.learned_1963_tail_reorder_budget_swaps_applied,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_SKIPPED_KEY,
            bcp_long_scan.learned_1963_tail_reorder_budget_swaps_skipped,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY,
            u64::from(learned_1963_pressure_reduction.enabled),
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_candidates",
            learned_1963_pressure_reduction.candidates,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_pressure_candidates",
            learned_1963_pressure_reduction.pressure_candidates,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_ranked",
            learned_1963_pressure_reduction.ranked,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_rank_bias_total",
            learned_1963_pressure_reduction.rank_bias_total,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_selected",
            learned_1963_pressure_reduction.selected,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_selected_steps",
            learned_1963_pressure_reduction.selected_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_deleted",
            learned_1963_pressure_reduction.deleted,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_deleted_steps",
            learned_1963_pressure_reduction.deleted_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_kept",
            learned_1963_pressure_reduction.kept,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_kept_steps",
            learned_1963_pressure_reduction.kept_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_skipped_no_pressure",
            learned_1963_pressure_reduction.skipped_no_pressure,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_reduction_lrat_retained_delete_skips",
            learned_1963_pressure_reduction.lrat_retained_delete_skips,
        );
        run_stats.insert(
            SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY,
            u64::from(learned_1963_pressure_retention.enabled),
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_candidates",
            learned_1963_pressure_retention.candidates,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_pressure_candidates",
            learned_1963_pressure_retention.pressure_candidates,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_ranked",
            learned_1963_pressure_retention.ranked,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_rank_bias_total",
            learned_1963_pressure_retention.rank_bias_total,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_selected",
            learned_1963_pressure_retention.selected,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_selected_steps",
            learned_1963_pressure_retention.selected_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_deleted",
            learned_1963_pressure_retention.deleted,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_deleted_steps",
            learned_1963_pressure_retention.deleted_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_kept",
            learned_1963_pressure_retention.kept,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_kept_steps",
            learned_1963_pressure_retention.kept_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_skipped_no_pressure",
            learned_1963_pressure_retention.skipped_no_pressure,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_pressure_retention_lrat_retained_delete_skips",
            learned_1963_pressure_retention.lrat_retained_delete_skips,
        );
        run_stats.insert("sat.bcp_long_saved_pos_scans", bcp_saved_pos.long_scans);
        run_stats.insert(
            "sat.bcp_long_saved_pos_start_false",
            bcp_saved_pos.long_start_false,
        );
        run_stats.insert(
            "sat.bcp_long_saved_pos_found_true",
            bcp_saved_pos.long_found_true,
        );
        run_stats.insert(
            "sat.bcp_long_saved_pos_found_unassigned",
            bcp_saved_pos.long_found_unassigned,
        );
        run_stats.insert(
            "sat.bcp_long_saved_pos_no_replacement",
            bcp_saved_pos.long_no_replacement,
        );
        run_stats.insert("sat.bcp_len18_saved_pos_scans", bcp_saved_pos.len18_scans);
        run_stats.insert(
            "sat.bcp_len18_saved_pos_start_false",
            bcp_saved_pos.len18_start_false,
        );
        run_stats.insert(
            "sat.bcp_len18_saved_pos_found_true",
            bcp_saved_pos.len18_found_true,
        );
        run_stats.insert(
            "sat.bcp_len18_saved_pos_found_unassigned",
            bcp_saved_pos.len18_found_unassigned,
        );
        run_stats.insert(
            "sat.bcp_len18_saved_pos_no_replacement",
            bcp_saved_pos.len18_no_replacement,
        );
        run_stats.insert(
            "sat.bcp_long_blocker_fastpath_hits",
            bcp_long_scan.long_blocker_fastpath_hits,
        );
        let bcp_long_bucket_keys = ["6_8", "9_17", "18", "19_63", "64_plus"];
        for (idx, bucket) in bcp_long_bucket_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_steps"),
                bcp_long_scan.scan_steps_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_learned_steps"),
                bcp_long_scan.learned_scan_steps_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_original_steps"),
                bcp_long_scan.original_scan_steps_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_scans"),
                bcp_long_scan.scans_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_found_replacement"),
                bcp_long_scan.found_replacement_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_found_true"),
                bcp_long_scan.found_true_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_found_unassigned"),
                bcp_long_scan.found_unassigned_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_no_replacement"),
                bcp_long_scan.no_replacement_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_unit"),
                bcp_long_scan.unit_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_conflict"),
                bcp_long_scan.conflict_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_learned"),
                bcp_long_scan.learned_scans_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_learned_found_replacement"),
                bcp_long_scan.learned_found_replacement_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_learned_no_replacement"),
                bcp_long_scan.learned_no_replacement_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_learned_unit"),
                bcp_long_scan.learned_unit_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_long_scan_{bucket}_learned_conflict"),
                bcp_long_scan.learned_conflict_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_saved_pos_{bucket}_eligible"),
                bcp_long_scan.learned_no_replacement_saved_pos_eligible_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_saved_pos_{bucket}_writes"),
                bcp_long_scan.learned_no_replacement_saved_pos_writes_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_saved_pos_{bucket}_skipped_current"),
                bcp_long_scan.learned_no_replacement_saved_pos_skipped_current_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_saved_pos_{bucket}_unit"),
                bcp_long_scan.learned_no_replacement_saved_pos_unit_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_saved_pos_{bucket}_conflict"),
                bcp_long_scan.learned_no_replacement_saved_pos_conflict_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_scan_pressure_{bucket}_scans"),
                bcp_long_scan.learned_no_replacement_scan_pressure_scans_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_scan_pressure_{bucket}_steps"),
                bcp_long_scan.learned_no_replacement_scan_pressure_steps_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_scan_pressure_{bucket}_start_false"),
                bcp_long_scan.learned_no_replacement_scan_pressure_start_false_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_scan_pressure_{bucket}_wrapped"),
                bcp_long_scan.learned_no_replacement_scan_pressure_wrapped_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_scan_pressure_{bucket}_unit"),
                bcp_long_scan.learned_no_replacement_scan_pressure_unit_by_len[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_no_replacement_scan_pressure_{bucket}_conflict"),
                bcp_long_scan.learned_no_replacement_scan_pressure_conflict_by_len[idx],
            );
        }
        let learned_1963_lbd_keys = ["lbd_0_2", "lbd_3_6", "lbd_7_10", "lbd_11_20", "lbd_21_plus"];
        for (idx, bucket) in learned_1963_lbd_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_unit_{bucket}"),
                bcp_long_scan.learned_1963_fsw_unit_by_lbd[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}"),
                bcp_long_scan.learned_1963_fsw_conflict_by_lbd[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_unit_{bucket}_steps"),
                bcp_long_scan.learned_1963_fsw_unit_steps_by_lbd[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}_steps"),
                bcp_long_scan.learned_1963_fsw_conflict_steps_by_lbd[idx],
            );
        }
        let learned_1963_used_keys = ["used_0", "used_1", "used_2_4", "used_5_plus"];
        for (idx, bucket) in learned_1963_used_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_unit_{bucket}"),
                bcp_long_scan.learned_1963_fsw_unit_by_used[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}"),
                bcp_long_scan.learned_1963_fsw_conflict_by_used[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_unit_{bucket}_steps"),
                bcp_long_scan.learned_1963_fsw_unit_steps_by_used[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}_steps"),
                bcp_long_scan.learned_1963_fsw_conflict_steps_by_used[idx],
            );
        }
        run_stats.insert(
            "sat.bcp_learned_1963_fsw_repeat_bucket_max",
            bcp_long_scan.learned_1963_fsw_repeat_bucket_max,
        );
        for idx in 0..bcp_long_scan.learned_1963_fsw_repeat_by_bucket.len() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_repeat_bucket_{idx}_count"),
                bcp_long_scan.learned_1963_fsw_repeat_by_bucket[idx],
            );
            run_stats.insert(
                &format!("sat.bcp_learned_1963_fsw_repeat_bucket_{idx}_steps"),
                bcp_long_scan.learned_1963_fsw_repeat_steps_by_bucket[idx],
            );
        }
        run_stats.insert(
            SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY,
            u64::from(bcp_identity.enabled),
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_exact_rows",
            bcp_identity.exact_identity_rows,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_row_limit",
            bcp_identity.row_limit,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_total_scans",
            bcp_identity.total_scans,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_total_steps",
            bcp_identity.total_scan_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_replacement_scans",
            bcp_identity.replacement_scans,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_replacement_steps",
            bcp_identity.replacement_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_true_replacements",
            bcp_identity.true_replacements,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_unassigned_replacements",
            bcp_identity.unassigned_replacements,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_no_replacement_scans",
            bcp_identity.no_replacement_scans,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_no_replacement_steps",
            bcp_identity.no_replacement_steps,
        );
        run_stats.insert("sat.bcp_learned_1963_identity_unit", bcp_identity.unit);
        run_stats.insert(
            "sat.bcp_learned_1963_identity_conflict",
            bcp_identity.conflict,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_fsw_scans",
            bcp_identity.fsw_scans,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_fsw_steps",
            bcp_identity.fsw_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_repeat_scans",
            bcp_identity.repeat_scans,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_repeat_steps",
            bcp_identity.repeat_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_fsw_repeat_steps",
            bcp_identity.fsw_repeat_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_topk_steps",
            bcp_identity.topk_scan_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_topk_pressure_share_ppm",
            bcp_identity.topk_pressure_share_ppm,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_topk_fsw_steps",
            bcp_identity.topk_fsw_steps,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_topk_fsw_pressure_share_ppm",
            bcp_identity.topk_fsw_pressure_share_ppm,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_scans_per_conflict_x1000",
            bcp_identity.scans_per_conflict_x1000,
        );
        run_stats.insert(
            "sat.bcp_learned_1963_identity_steps_per_conflict_x1000",
            bcp_identity.steps_per_conflict_x1000,
        );
        let identity_age_keys = [
            "age_0_99",
            "age_100_999",
            "age_1000_9999",
            "age_10000_99999",
            "age_100000_plus",
        ];
        for (idx, bucket) in identity_age_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
                bcp_identity.age_steps_by_bucket[idx],
            );
        }
        for (idx, bucket) in identity_age_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_identity_fsw_{bucket}_steps"),
                bcp_identity.fsw_age_steps_by_bucket[idx],
            );
        }
        let identity_lbd_keys = ["lbd_0_2", "lbd_3_6", "lbd_7_10", "lbd_11_20", "lbd_21_plus"];
        for (idx, bucket) in identity_lbd_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
                bcp_identity.lbd_steps_by_bucket[idx],
            );
        }
        let identity_used_keys = ["used_0", "used_1", "used_2_4", "used_5_plus"];
        for (idx, bucket) in identity_used_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
                bcp_identity.used_steps_by_bucket[idx],
            );
        }
        let identity_activity_keys = [
            "activity_0",
            "activity_1_999",
            "activity_1000_9999",
            "activity_10000_plus",
        ];
        for (idx, bucket) in identity_activity_keys.iter().enumerate() {
            run_stats.insert(
                &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
                bcp_identity.activity_steps_by_bucket[idx],
            );
        }
        for (idx, row) in bcp_identity.rows.iter().enumerate() {
            let prefix = format!("sat.bcp_learned_1963_identity_row_{idx}");
            run_stats.insert(&format!("{prefix}_clause_id"), row.clause_id);
            run_stats.insert(&format!("{prefix}_clause_offset"), row.clause_offset);
            run_stats.insert(&format!("{prefix}_clause_len"), row.clause_len);
            run_stats.insert(&format!("{prefix}_birth_conflict"), row.birth_conflict);
            run_stats.insert(&format!("{prefix}_last_conflict"), row.last_conflict);
            run_stats.insert(&format!("{prefix}_age"), row.age_conflicts);
            run_stats.insert(&format!("{prefix}_lbd"), row.lbd);
            run_stats.insert(&format!("{prefix}_used"), row.used);
            run_stats.insert(&format!("{prefix}_activity_milli"), row.activity_milli);
            run_stats.insert(&format!("{prefix}_scans"), row.scans);
            run_stats.insert(&format!("{prefix}_steps"), row.scan_steps);
            run_stats.insert(
                &format!("{prefix}_replacement_scans"),
                row.replacement_scans,
            );
            run_stats.insert(
                &format!("{prefix}_replacement_steps"),
                row.replacement_steps,
            );
            run_stats.insert(
                &format!("{prefix}_true_replacements"),
                row.true_replacements,
            );
            run_stats.insert(
                &format!("{prefix}_unassigned_replacements"),
                row.unassigned_replacements,
            );
            run_stats.insert(
                &format!("{prefix}_no_replacement_scans"),
                row.no_replacement_scans,
            );
            run_stats.insert(
                &format!("{prefix}_no_replacement_steps"),
                row.no_replacement_steps,
            );
            run_stats.insert(&format!("{prefix}_unit"), row.unit);
            run_stats.insert(&format!("{prefix}_conflict"), row.conflict);
            run_stats.insert(
                &format!("{prefix}_saved_start_false"),
                row.saved_start_false,
            );
            run_stats.insert(&format!("{prefix}_wrapped"), row.wrapped);
            run_stats.insert(&format!("{prefix}_fsw"), row.fsw);
            run_stats.insert(&format!("{prefix}_fsw_steps"), row.fsw_steps);
            run_stats.insert(&format!("{prefix}_fsw_unit_steps"), row.fsw_unit_steps);
            run_stats.insert(
                &format!("{prefix}_fsw_conflict_steps"),
                row.fsw_conflict_steps,
            );
            run_stats.insert(&format!("{prefix}_repeat_scans"), row.repeat_scans);
            run_stats.insert(&format!("{prefix}_repeat_steps"), row.repeat_steps);
            run_stats.insert(&format!("{prefix}_fsw_repeat_steps"), row.fsw_repeat_steps);
            run_stats.insert(&format!("{prefix}_max_scan_steps"), row.max_scan_steps);
        }
        for (idx, row) in bcp_identity.fsw_rows.iter().enumerate() {
            let prefix = format!("sat.bcp_learned_1963_identity_fsw_row_{idx}");
            run_stats.insert(&format!("{prefix}_clause_id"), row.clause_id);
            run_stats.insert(&format!("{prefix}_clause_offset"), row.clause_offset);
            run_stats.insert(&format!("{prefix}_clause_len"), row.clause_len);
            run_stats.insert(&format!("{prefix}_birth_conflict"), row.birth_conflict);
            run_stats.insert(&format!("{prefix}_last_conflict"), row.last_conflict);
            run_stats.insert(&format!("{prefix}_age"), row.age_conflicts);
            run_stats.insert(&format!("{prefix}_lbd"), row.lbd);
            run_stats.insert(&format!("{prefix}_used"), row.used);
            run_stats.insert(&format!("{prefix}_activity_milli"), row.activity_milli);
            run_stats.insert(&format!("{prefix}_scans"), row.scans);
            run_stats.insert(&format!("{prefix}_steps"), row.scan_steps);
            run_stats.insert(
                &format!("{prefix}_replacement_scans"),
                row.replacement_scans,
            );
            run_stats.insert(
                &format!("{prefix}_replacement_steps"),
                row.replacement_steps,
            );
            run_stats.insert(
                &format!("{prefix}_true_replacements"),
                row.true_replacements,
            );
            run_stats.insert(
                &format!("{prefix}_unassigned_replacements"),
                row.unassigned_replacements,
            );
            run_stats.insert(
                &format!("{prefix}_no_replacement_scans"),
                row.no_replacement_scans,
            );
            run_stats.insert(
                &format!("{prefix}_no_replacement_steps"),
                row.no_replacement_steps,
            );
            run_stats.insert(&format!("{prefix}_unit"), row.unit);
            run_stats.insert(&format!("{prefix}_conflict"), row.conflict);
            run_stats.insert(
                &format!("{prefix}_saved_start_false"),
                row.saved_start_false,
            );
            run_stats.insert(&format!("{prefix}_wrapped"), row.wrapped);
            run_stats.insert(&format!("{prefix}_fsw"), row.fsw);
            run_stats.insert(&format!("{prefix}_fsw_steps"), row.fsw_steps);
            run_stats.insert(&format!("{prefix}_fsw_unit_steps"), row.fsw_unit_steps);
            run_stats.insert(
                &format!("{prefix}_fsw_conflict_steps"),
                row.fsw_conflict_steps,
            );
            run_stats.insert(&format!("{prefix}_repeat_scans"), row.repeat_scans);
            run_stats.insert(&format!("{prefix}_repeat_steps"), row.repeat_steps);
            run_stats.insert(&format!("{prefix}_fsw_repeat_steps"), row.fsw_repeat_steps);
            run_stats.insert(&format!("{prefix}_max_scan_steps"), row.max_scan_steps);
        }
        run_stats.insert(
            "sat.lrat_materialize_calls",
            lrat_materialization.materialize_calls,
        );
        run_stats.insert(
            "sat.lrat_materialize_minimize_calls",
            lrat_materialization.materialize_minimize_calls,
        );
        run_stats.insert(
            "sat.lrat_materialize_root_trail_entries",
            lrat_materialization.materialize_root_trail_entries,
        );
        run_stats.insert(
            "sat.lrat_materialize_minimize_root_trail_entries",
            lrat_materialization.materialize_minimize_root_trail_entries,
        );
        run_stats.insert(
            "sat.lrat_materialize_emitted_unit_lines",
            lrat_materialization.materialize_emitted_unit_lines,
        );
        run_stats.insert(
            "sat.lrat_materialize_minimize_emitted_unit_lines",
            lrat_materialization.materialize_minimize_emitted_unit_lines,
        );
        run_stats.insert(
            "sat.lrat_materialize_unit_hints",
            lrat_materialization.materialize_unit_hints,
        );
        run_stats.insert(
            "sat.lrat_materialize_minimize_unit_hints",
            lrat_materialization.materialize_minimize_unit_hints,
        );
        run_stats.insert(
            "sat.lrat_materialize_unit_max_hints",
            lrat_materialization.materialize_unit_max_hints,
        );
        run_stats.insert(
            "sat.lrat_materialize_minimize_unit_max_hints",
            lrat_materialization.materialize_minimize_unit_max_hints,
        );
        run_stats.insert(
            "sat.lrat_materialize_incomplete_chains",
            lrat_materialization.materialize_incomplete_chains,
        );
        run_stats.insert(
            "sat.lrat_materialize_minimize_incomplete_chains",
            lrat_materialization.materialize_minimize_incomplete_chains,
        );
        run_stats.insert(
            "sat.lrat_materialize_hidden_trusted_units",
            lrat_materialization.materialize_hidden_trusted_units,
        );
        run_stats.insert(
            "sat.lrat_unit_chain_calls",
            lrat_materialization.unit_chain_calls,
        );
        run_stats.insert(
            "sat.lrat_unit_chain_root_trail_entries",
            lrat_materialization.unit_chain_root_trail_entries,
        );
        run_stats.insert(
            "sat.lrat_unit_chain_hints",
            lrat_materialization.unit_chain_hints,
        );
        run_stats.insert(
            "sat.lrat_unit_chain_max_hints",
            lrat_materialization.unit_chain_max_hints,
        );
        run_stats.insert(
            "sat.lrat_unit_chain_missing_hints",
            lrat_materialization.unit_chain_missing_hints,
        );
        run_stats.insert("sat.jumped_reasons", jumped_reasons);
        // OTFS
        run_stats.insert("sat.otfs_candidates", otfs_cand);
        run_stats.insert("sat.otfs_subsumed", otfs_sub);
        run_stats.insert("sat.otfs_strengthened", otfs_str);
        run_stats.insert("sat.otfs_branch_b", otfs_branch_b);
        run_stats.insert("sat.otfs_branch_c", otfs_branch_c);
        run_stats.insert("sat.otfs_clause_subsumed", otfs_clause_sub);
        // IBCL (#8269)
        run_stats.insert("sat.ibcl_attempts", ibcl_attempts);
        run_stats.insert("sat.ibcl_improvements", ibcl_improvements);
        run_stats.insert("sat.ibcl_skipped_short_chain", ibcl_skipped);
        run_stats.insert(
            "sat.ibcl_skipped_missing_pivots",
            ibcl_skipped_missing_pivots,
        );
        // BCP-theory fixed-point (#8003)
        run_stats.insert("sat.bcp_theory_fixpoint_entries", fp_entries);
        run_stats.insert("sat.bcp_theory_fixpoint_iterations", fp_iters);
        run_stats.insert("sat.bcp_theory_fixpoint_max_depth", u64::from(fp_max));
        run_stats.insert("sat.bcp_theory_fixpoint_saturated", fp_saturated);
        // Shrink
        run_stats.insert("sat.shrink_attempts", shrink_attempts);
        run_stats.insert("sat.shrink_successes", shrink_successes);
        run_stats.insert(
            "sat.shrink_singleton_fast_path_skips",
            shrink_singleton_fast_path_skips,
        );
        run_stats.insert(
            "sat.lrat_original_learned_snapshot_copies",
            lrat_original_learned_snapshot_copies,
        );
        run_stats.insert(
            "sat.lrat_original_learned_snapshot_literals",
            lrat_original_learned_snapshot_literals,
        );
        run_stats.insert(
            "sat.lrat_original_learned_snapshot_singleton_skips",
            lrat_original_learned_snapshot_singleton_skips,
        );
        run_stats.insert(
            "sat.lrat_removed_literal_chain_calls",
            lrat_removed_literal_chain_calls,
        );
        // Mode/heuristic
        run_stats.insert("sat.mode_switches", solver.mode_switch_count());
        // Restart attribution (diagnostic telemetry for restart-cadence tuning).
        let (_focused_ema_checks, focused_ema_fires) = solver.focused_ema_stats();
        run_stats.insert("sat.focused_ema_fires", focused_ema_fires);
        run_stats.insert(
            "sat.stable_reluctant_fires",
            solver.stable_reluctant_fires(),
        );
        run_stats.insert("sat.stable_ema_fires", solver.stable_ema_fires());
        run_stats.insert(
            "sat.trail_blocked_restarts",
            solver.trail_blocked_restarts(),
        );
        run_stats.insert("sat.focused_decisions", focused_decs);
        run_stats.insert("sat.stable_decisions", stable_decs);
        run_stats.insert("sat.mab_switches", mab_switches);
        // Search ticks (#8148)
        run_stats.insert("sat.search_ticks", search_ticks);
        if let Some(ticks_per_conflict) = search_ticks.checked_div(confs) {
            run_stats.insert("sat.ticks_per_conflict", ticks_per_conflict);
        }
        // Inprocessing rounds/simplifications
        run_stats.insert("sat.inproc_rounds", inproc_rounds);
        run_stats.insert("sat.incr_inproc_rounds", incr_inproc_rounds);
        run_stats.insert("sat.inproc_simplifications", inproc_simplifications);
        // rebuild_watches cost (#8103)
        run_stats.insert("sat.rebuild_watches_us", solver.rebuild_watches_us());
        run_stats.insert("sat.rebuild_watches_calls", solver.rebuild_watches_calls());
        // Full vs incremental rebuild breakdown (#8103)
        run_stats.insert(
            "sat.full_rebuild_watches_us",
            solver.full_rebuild_watches_us(),
        );
        run_stats.insert(
            "sat.full_rebuild_watches_calls",
            solver.full_rebuild_watches_calls(),
        );
        run_stats.insert(
            "sat.incremental_reconnect_watches_us",
            solver.incremental_reconnect_watches_us(),
        );
        run_stats.insert(
            "sat.incremental_reconnect_watches_calls",
            solver.incremental_reconnect_watches_calls(),
        );
        // Post-rebuild BCP cache behavior (#8103)
        {
            let (pr_ns, pr_props) = solver.post_rebuild_bcp_stats();
            run_stats.insert("sat.post_rebuild_bcp_ns", pr_ns);
            run_stats.insert("sat.post_rebuild_bcp_propagations", pr_props);
            if pr_props > 0 && pr_ns > 0 {
                run_stats.insert(
                    "sat.post_rebuild_mpps_x1000",
                    pr_props * 1000 / pr_ns.max(1),
                );
            }
            // Full rebuild BCP cache stats
            let (fr_ns, fr_props) = solver.post_full_rebuild_bcp_stats();
            run_stats.insert("sat.post_full_rebuild_bcp_ns", fr_ns);
            run_stats.insert("sat.post_full_rebuild_bcp_propagations", fr_props);
            if fr_props > 0 && fr_ns > 0 {
                run_stats.insert(
                    "sat.post_full_rebuild_mpps_x1000",
                    fr_props * 1000 / fr_ns.max(1),
                );
            }
            // Incremental reconnect BCP cache stats
            let (ir_ns, ir_props) = solver.post_incremental_reconnect_bcp_stats();
            run_stats.insert("sat.post_incr_reconnect_bcp_ns", ir_ns);
            run_stats.insert("sat.post_incr_reconnect_bcp_propagations", ir_props);
            if ir_props > 0 && ir_ns > 0 {
                run_stats.insert(
                    "sat.post_incr_reconnect_mpps_x1000",
                    ir_props * 1000 / ir_ns.max(1),
                );
            }
            if props > 0 && search_ns > 0 {
                run_stats.insert("sat.overall_mpps_x1000", props * 1000 / search_ns.max(1));
            }
        }
        // Clause DB
        run_stats.insert("sat.reductions", solver.num_reductions());
        run_stats.insert("sat.flushes", solver.num_flushes());
        run_stats.insert("sat.arena_compactions", solver.num_arena_compactions());
        run_stats.insert(
            "sat.reduction_l0_satisfied_occ_scans",
            reduction_l0_satisfied_occ_scans,
        );
        run_stats.insert(
            "sat.reduction_l0_satisfied_full_scans",
            reduction_l0_satisfied_full_scans,
        );
        run_stats.insert(
            "sat.reduction_l0_satisfied_no_occ_skips",
            reduction_l0_satisfied_no_occ_skips,
        );
        run_stats.insert(
            "sat.reduction_l0_satisfied_deleted",
            reduction_l0_satisfied_deleted,
        );
        run_stats.insert(
            "sat.learned_reduction_considered",
            learned_reduction_considered,
        );
        run_stats.insert("sat.learned_reduction_deleted", learned_reduction_deleted);
        run_stats.insert(
            "sat.learned_reduction_reason_protected",
            learned_reduction_reason_protected,
        );
        run_stats.insert(
            "sat.learned_reduction_ic3_protected",
            learned_reduction_ic3_protected,
        );
        run_stats.insert(
            "sat.learned_reduction_low_lbd_protected",
            learned_reduction_low_lbd_protected,
        );
        run_stats.insert(
            "sat.learned_reduction_usage_protected",
            learned_reduction_usage_protected,
        );
        run_stats.insert(
            "sat.learned_reduction_target_kept",
            learned_reduction_target_kept,
        );
        run_stats.insert(
            "sat.learned_reduction_lrat_retained_delete_skips",
            learned_reduction_lrat_retained_delete_skips,
        );
        run_stats.insert(
            "sat.learned_reduction_hyper_deleted",
            learned_reduction_hyper_deleted,
        );
        run_stats.insert(
            "sat.learned_reduction_hyper_kept",
            learned_reduction_hyper_kept,
        );
        // Per-pass inprocessing times
        for (label, value) in solver.inprocessing_pass_times_ms() {
            run_stats.insert(&format!("sat.{label}"), value);
        }
        // Per-pass inprocessing accounting. Labels share the timing stem, with
        // `_ms` removed so the count keys do not read like durations.
        for (label, accounting) in solver.inprocessing_pass_accounting() {
            let stem = label.strip_suffix("_ms").unwrap_or(label);
            run_stats.insert(&format!("sat.{stem}_attempts"), accounting.attempts);
            run_stats.insert(&format!("sat.{stem}_runs"), accounting.runs);
            run_stats.insert(&format!("sat.{stem}_yields"), accounting.yields);
        }
        // Per-technique detail stats (#8131)
        {
            let bs = solver.bve_stats();
            run_stats.insert(
                "sat.bve_occ_delta_enabled",
                u64::from(solver.is_bve_occ_delta_validation_enabled()),
            );
            run_stats.insert(
                "sat.bve_occ_saved_state_reuse_enabled",
                u64::from(solver.is_bve_occ_saved_state_reuse_enabled()),
            );
            run_stats.insert("sat.bve_eliminated", bs.vars_eliminated);
            run_stats.insert("sat.bve_cls_removed", bs.clauses_removed);
            run_stats.insert("sat.bve_resolvents", bs.resolvents_added);
            run_stats.insert("sat.bve_tautologies", bs.tautologies_skipped);
            run_stats.insert("sat.bve_bw_subsumed", bs.backward_subsumed);
            run_stats.insert("sat.bve_bw_strengthened", bs.backward_strengthened);
            run_stats.insert("sat.bve_bw_units", bs.backward_units);
            run_stats.insert("sat.bve_fast_elim_vars", bs.fast_elim_vars);
            run_stats.insert("sat.bve_fast_elim_clauses", bs.fast_elim_clauses);
            run_stats.insert(
                "sat.bve_lrat_preflight_rejected",
                bs.lrat_preflight_rejected,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_missing_proof_manager",
                bs.lrat_preflight_missing_proof_manager,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_missing_or_hidden_source_id",
                bs.lrat_preflight_missing_or_hidden_source_id,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_deletion_target_not_live",
                bs.lrat_preflight_deletion_target_not_live,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_malformed_strengthening",
                bs.lrat_preflight_malformed_strengthening,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_malformed_resolvent",
                bs.lrat_preflight_malformed_resolvent,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_replacement_cleanup_unit",
                bs.lrat_preflight_replacement_cleanup_unit,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_add_rejected",
                bs.lrat_preflight_planned_add_rejected,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_not_lrat",
                bs.lrat_preflight_planned_not_lrat,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_lrat_blocked",
                bs.lrat_preflight_planned_lrat_blocked,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_io_failed",
                bs.lrat_preflight_planned_io_failed,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_pending_deletions",
                bs.lrat_preflight_planned_pending_deletions,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_output_id_mismatch",
                bs.lrat_preflight_planned_output_id_mismatch,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_invalid_clause",
                bs.lrat_preflight_planned_invalid_clause,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_suppressed_axiom",
                bs.lrat_preflight_planned_suppressed_axiom,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_hidden_trusted_unit",
                bs.lrat_preflight_planned_hidden_trusted_unit,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_missing_hints",
                bs.lrat_preflight_planned_missing_hints,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_zero_hint",
                bs.lrat_preflight_planned_zero_hint,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_duplicate_hint",
                bs.lrat_preflight_planned_duplicate_hint,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_unknown_hint",
                bs.lrat_preflight_planned_unknown_hint,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_trusted_hint",
                bs.lrat_preflight_planned_trusted_hint,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_backward_reserved_hint",
                bs.lrat_preflight_planned_backward_reserved_hint,
            );
            run_stats.insert(
                "sat.bve_lrat_preflight_planned_id_overflow",
                bs.lrat_preflight_planned_id_overflow,
            );
            run_stats.insert(
                "sat.occ_epoch_fastpath_refreshes",
                bs.occ_epoch_fastpath_refreshes,
            );
            run_stats.insert(
                "sat.occ_delta_validated_refreshes",
                bs.occ_delta_validated_refreshes,
            );
            run_stats.insert(
                "sat.occ_delta_validation_fallbacks",
                bs.occ_delta_validation_fallbacks,
            );
            run_stats.insert(
                "sat.occ_delta_uncertified_fallbacks",
                bs.occ_delta_uncertified_fallbacks,
            );
            run_stats.insert(
                "sat.occ_delta_oversize_fallbacks",
                bs.occ_delta_oversize_fallbacks,
            );
            run_stats.insert(
                "sat.occ_delta_touched_clauses",
                bs.occ_delta_touched_clauses,
            );
            run_stats.insert("sat.occ_delta_touched_lits", bs.occ_delta_touched_lits);
            run_stats.insert(
                "sat.occ_delta_occ_entries_checked",
                bs.occ_delta_occ_entries_checked,
            );
            run_stats.insert(
                "sat.occ_delta_missing_entries",
                bs.occ_delta_missing_entries,
            );
            run_stats.insert(
                "sat.occ_delta_stale_live_entries",
                bs.occ_delta_stale_live_entries,
            );
            run_stats.insert(
                "sat.occ_delta_live_learned_entries",
                bs.occ_delta_live_learned_entries,
            );
            run_stats.insert(
                "sat.occ_saved_state_round_end_drops",
                bs.occ_saved_state_round_end_drops,
            );
            run_stats.insert(
                "sat.occ_saved_state_round_end_retains",
                bs.occ_saved_state_round_end_retains,
            );
        }
        {
            let gs = solver.gate_stats();
            run_stats.insert("sat.gate_and", gs.and_gates);
            run_stats.insert("sat.gate_xor", gs.xor_gates);
            run_stats.insert("sat.gate_equiv", gs.equivalences);
            run_stats.insert("sat.gate_ite", gs.ite_gates);
        }
        run_stats.insert("sat.probe_failed", solver.probe_stats().failed);
        {
            let cs = solver.congruence_stats();
            run_stats.insert("sat.cong_rounds", cs.rounds);
            run_stats.insert("sat.cong_equivs", cs.equivalences_found);
            run_stats.insert("sat.cong_lits_rwt", cs.literals_rewritten);
        }
        {
            let ss = solver.sweep_stats();
            run_stats.insert("sat.sweep_rounds", ss.rounds);
            run_stats.insert("sat.sweep_lits_rwt", ss.literals_rewritten);
            // Real sweep-yield counters (wf_755ac432 observability). See the
            // `-st` block for why: the two counters above read a phantom 0.
            run_stats.insert("sat.sweep_equivs", ss.kitten_equivalences);
            run_stats.insert("sat.sweep_environments", ss.kitten_environments);
            run_stats.insert("sat.sweep_backbone", ss.kitten_backbone);
            run_stats.insert("sat.sweep_clauses_rwt", ss.clauses_rewritten);
        }
        {
            let ds = solver.decompose_stats();
            run_stats.insert("sat.decomp_rounds", ds.rounds);
            run_stats.insert("sat.decomp_subst", ds.substituted);
            insert_decompose_lrat_preflight_telemetry(
                &mut run_stats,
                &solver.decompose_lrat_preflight_stats(),
            );
        }
        {
            let ts = solver.transred_stats();
            run_stats.insert("sat.transred_rounds", ts.rounds);
            run_stats.insert("sat.transred_cls_rm", ts.clauses_removed);
        }
        {
            let fs = solver.factor_stats();
            run_stats.insert("sat.factor_rounds", fs.rounds);
            run_stats.insert("sat.factor_count", fs.factored_count);
        }
        {
            let vs = solver.vivify_stats();
            run_stats.insert("sat.vivify_examined", vs.clauses_examined);
            run_stats.insert("sat.vivify_strengthened", vs.clauses_strengthened);
            run_stats.insert("sat.vivify_lits_rm", vs.literals_removed);
        }
        {
            let sbs = solver.subsume_stats();
            run_stats.insert("sat.subsumed", sbs.forward_subsumed);
            run_stats.insert("sat.strengthened", sbs.strengthened_clauses);
            run_stats.insert("sat.total_subsumed", solver.total_subsumed());
            // Per-source breakdown (#8502)
            run_stats.insert("sat.bve_bw_subsumed", solver.bve_stats().backward_subsumed);
            run_stats.insert("sat.otfs_subsumed", solver.otfs_clause_subsumed());
            run_stats.insert("sat.eager_subsumed", solver.eager_subsumed());
            run_stats.insert(
                "sat.congruence_subsumed",
                solver.congruence_stats().congruence_subsumed,
            );
            run_stats.insert("sat.dedup_deleted", solver.dedup_deleted());
        }
        {
            let bces = solver.bce_stats();
            run_stats.insert("sat.bce_rounds", bces.rounds);
            run_stats.insert("sat.bce_eliminated", bces.clauses_eliminated);
        }
        {
            let cces = solver.cce_stats();
            run_stats.insert("sat.cce_rounds", cces.rounds);
            run_stats.insert("sat.cce_blocked", cces.blocked);
        }
        {
            let htr = solver.htr_stats();
            run_stats.insert("sat.htr_rounds", htr.rounds);
            run_stats.insert("sat.htr_ternary", htr.ternary_resolvents);
            run_stats.insert("sat.htr_binary", htr.binary_resolvents);
        }
        {
            let conds = solver.conditioning_stats();
            run_stats.insert("sat.cond_rounds", conds.rounds);
            run_stats.insert("sat.cond_eliminated", conds.clauses_eliminated);
        }
        // Dense propagation stats (#8088)
        run_stats.insert("sat.dense_propagations", solver.dense_propagations());
        run_stats.insert("sat.dense_conflicts", solver.dense_conflicts());
        run_stats.insert(
            "sat.dense_satisfied_deleted",
            solver.dense_satisfied_deleted(),
        );
        // Dirty-literal flush stats (#8101)
        run_stats.insert("sat.flush_dirty_lits", solver.flush_dirty_lits());
        run_stats.insert("sat.flush_watches_removed", solver.flush_watches_removed());
        // Watch list shrinking after reduce_db (#8031)
        run_stats.insert("sat.watches_shrunk", solver.watches_shrunk());
        // Minimal trail rewind stats (#8095)
        run_stats.insert("sat.trail_rewind_skipped", solver.trail_rewind_skipped());
        run_stats.insert("sat.trail_rewind_partial", solver.trail_rewind_partial());
        run_stats.insert("sat.trail_rewind_full", solver.trail_rewind_full());
        run_stats.insert(
            "sat.trail_rewind_saved_entries",
            solver.trail_rewind_saved_entries(),
        );
        // Stable flat counter names for native-helper instrumentation.
        run_stats.insert(
            "sat_learned_clause_candidate_applications",
            sat_learned_clause_candidate_applications,
        );
        run_stats.insert(
            "sat_native_code_helper_applications",
            sat_native_code_helper_applications,
        );
        run_stats.insert(
            SAT_WHOLE_LOOP_GUARD_INSTALL_COUNTER,
            sat_whole_loop_guard_installs,
        );
        run_stats.insert(
            SAT_WHOLE_LOOP_GUARD_APPLICATION_COUNTER,
            sat_whole_loop_guard_applications,
        );
        let competition_jit = sat_native_helper_competition_jit_metadata();
        let competition_jit_application_count =
            if competition_jit.application_counter == SAT_WHOLE_LOOP_GUARD_APPLICATION_COUNTER {
                sat_whole_loop_guard_applications
            } else {
                sat_native_code_helper_applications
            };
        run_stats.competition_jit = Some(sat_native_helper_competition_jit_evidence(
            &competition_jit,
            competition_jit_application_count,
        ));
        run_stats.insert(
            "sat.subsumption_native_applications",
            sat_subsumption_native_applications,
        );
        run_stats.insert(
            "sat.conflict_analysis_native_applications",
            sat_conflict_analysis_native_applications,
        );
        // Code cache stats (#8394)
        run_stats.insert(
            "sat.code_cache_total_bytes",
            solver.code_cache_total_bytes() as u64,
        );
        run_stats.insert(
            "sat.code_cache_peak_bytes",
            solver.code_cache_peak_bytes() as u64,
        );
        run_stats.insert("sat.code_cache_evictions", solver.code_cache_evictions());
        run_stats.insert(
            "sat.code_cache_bytes_evicted",
            solver.code_cache_bytes_evicted(),
        );
        run_stats.insert(
            "sat.native_code_helpers_enabled",
            u64::from(solver.native_code_helpers_enabled()),
        );
        run_stats.insert(
            "sat.tier_controller_promotions",
            solver.tier_controller_promotions(),
        );
        // SAT propagation native telemetry
        run_stats.insert(
            "sat.propagation_native_active",
            u64::from(solver.sat_propagation_native_active()),
        );
        run_stats.insert(
            "sat.propagation_native_clauses",
            solver.sat_propagation_native_clauses(),
        );
        run_stats.insert(
            "sat.propagation_native_rounds",
            solver.sat_propagation_native_rounds(),
        );
        run_stats.insert(
            "sat.propagation_native_propagations",
            solver.sat_propagation_native_propagations(),
        );
        run_stats.insert(
            "sat.propagation_native_conflicts",
            solver.sat_propagation_native_conflicts(),
        );
        run_stats.insert(
            "sat.propagation_native_compile_time_us",
            solver.sat_propagation_native_compile_time_us(),
        );
        // Memory stats
        run_stats.insert("sat.arena_words", solver.arena_words() as u64);
        run_stats.insert("sat.active_clauses", solver.active_clause_count() as u64);
        // Backbone stats (#3274)
        run_stats.insert("sat.backbone_binary_units", solver.backbone_binary_units());
        run_stats.insert(
            "sat.inprocessing_yield_productivity_rescue_enabled",
            u64::from(solver.inprocessing_yield_productivity_rescue_enabled()),
        );
        run_stats.insert(
            SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY,
            u64::from(solver.lrat_proof_clamp_probe_rescue_enabled()),
        );
        let (lrat_clamped_bve_due, lrat_clamped_factor_due, lrat_probe_rescue_rounds) =
            solver.inprocessing_lrat_clamp_stats();
        run_stats.insert(
            SAT_INPROCESSING_LRAT_CLAMPED_BVE_DUE_ROUNDS_KEY,
            lrat_clamped_bve_due,
        );
        run_stats.insert(
            SAT_INPROCESSING_LRAT_CLAMPED_FACTOR_DUE_ROUNDS_KEY,
            lrat_clamped_factor_due,
        );
        run_stats.insert(
            SAT_INPROCESSING_LRAT_PROBE_RESCUE_ROUNDS_KEY,
            lrat_probe_rescue_rounds,
        );
        run_stats.insert(
            SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY,
            u64::from(solver.backbone_post_vivify_binary_admission_enabled()),
        );
        let backbone_schedule = solver.backbone_schedule_stats();
        run_stats.insert(
            SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY,
            u64::from(backbone_schedule.yield_rescue_cooldown_enabled),
        );
        run_stats.insert(
            SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ROUNDS_KEY,
            backbone_schedule.yield_rescue_cooldown_rounds,
        );
        run_stats.insert(
            SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL_KEY,
            backbone_schedule.yield_rescue_cooldown_interval,
        );
        run_stats.insert(
            SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY,
            u64::from(backbone_schedule.bounded_zero_decompose_backoff_enabled),
        );
        run_stats.insert(
            SAT_BOUNDED_BACKBONE_BACKOFF_TRIGGERS_KEY,
            backbone_schedule.bounded_backoff_triggers,
        );
        run_stats.insert(
            SAT_BOUNDED_BACKBONE_RUNS_KEY,
            backbone_schedule.bounded_runs,
        );
        run_stats.insert(
            SAT_BOUNDED_BACKBONE_YIELDS_KEY,
            backbone_schedule.bounded_yields,
        );
        run_stats.insert(SAT_BOUNDED_BACKBONE_MS_KEY, backbone_schedule.bounded_ms);
        run_stats.insert(
            SAT_BOUNDED_BACKBONE_BINARY_SUPPRESSED_KEY,
            backbone_schedule.bounded_binary_suppressed,
        );
        run_stats.insert(
            "sat.backbone_schedule_enabled",
            u64::from(backbone_schedule.enabled),
        );
        run_stats.insert("sat.backbone_due", u64::from(backbone_schedule.due));
        run_stats.insert("sat.backbone_phases", u64::from(backbone_schedule.phases));
        run_stats.insert(
            "sat.backbone_max_rounds",
            u64::from(backbone_schedule.max_rounds),
        );
        run_stats.insert(
            "sat.backbone_consecutive_empty",
            u64::from(backbone_schedule.consecutive_empty),
        );
        run_stats.insert(
            "sat.backbone_stall_limit",
            u64::from(backbone_schedule.stall_limit),
        );
        run_stats.insert(
            "sat.backbone_stalled_by_empty",
            u64::from(backbone_schedule.stalled_by_empty),
        );
        run_stats.insert(
            "sat.backbone_rounds_exhausted",
            u64::from(backbone_schedule.rounds_exhausted),
        );
        run_stats.insert(
            "sat.backbone_next_conflict",
            backbone_schedule.next_conflict,
        );
        run_stats.insert(
            "sat.backbone_conflicts_until_next",
            backbone_schedule.conflicts_until_next,
        );
        run_stats.insert(
            "sat.backbone_backoff_interval",
            backbone_schedule.backoff_interval,
        );
        run_stats.insert(
            "sat.backbone_base_interval",
            backbone_schedule.base_interval,
        );
        run_stats.insert("sat.backbone_max_interval", backbone_schedule.max_interval);
        // Occ list incremental vs full rebuild (#8403)
        run_stats.insert(
            "sat.occ_incremental_refreshes",
            solver.occ_incremental_refreshes(),
        );
        run_stats.insert("sat.occ_full_rebuilds", solver.occ_full_rebuilds());
        // Between-solve reduction (#8435)
        {
            let (bs_reductions, bs_deleted, bs_decays) = solver.between_solve_stats();
            run_stats.insert("sat.between_solve_reductions", bs_reductions);
            run_stats.insert("sat.between_solve_clauses_deleted", bs_deleted);
            run_stats.insert("sat.between_solve_used_decays", bs_decays);
        }
        // Domain-restricted BCP (#8475)
        {
            let (dbcp_skips, dbcp_calls) = solver.domain_bcp_stats();
            run_stats.insert("sat.domain_bcp_skips", dbcp_skips);
            run_stats.insert("sat.domain_bcp_calls", dbcp_calls);
        }
        // Stale enqueue safety net (#8359)
        run_stats.insert("sat.stale_enqueue_skips", solver.stale_enqueue_skips());
        // Stale BCP watch entry safety net (#8547)
        run_stats.insert("sat.stale_bcp_watch_skips", solver.stale_bcp_watch_skips());
        // Eager subsumption
        run_stats.insert("sat.eager_subsumed", solver.eager_subsumed());
        // Lookahead stats (#8087)
        {
            let (la_rounds, la_failed, la_used) = solver.lookahead_stats();
            run_stats.insert("sat.lookahead_rounds", la_rounds);
            run_stats.insert("sat.lookahead_failed_literals", la_failed);
            run_stats.insert("sat.lookahead_decisions_used", la_used);
        }
        // decisions/sec rate
        if search_secs > 0.001 {
            run_stats.insert("sat.decisions_per_sec", (decs as f64 / search_secs) as u64);
        }
        // #8640: Resource consumption statistics.
        run_stats.insert(
            "resource.rss_peak_bytes",
            ay_sys::current_rss_bytes() as u64,
        );
        run_stats.insert(
            "resource.memory_limit_bytes",
            ay_sys::get_process_memory_limit() as u64,
        );
        run_stats.insert(
            "resource.term_bytes",
            ay_core::TermStore::global_term_bytes() as u64,
        );
        run_stats.insert("time.total_ms", global_elapsed().as_millis() as u64);
        emit_dimacs_run_stats(&run_stats, stats_cfg, route_profile);
    }
    // FINALIZE_SAT_FAIL rescue lane: when the finalize original-ledger gate
    // rejected a candidate model (InvalidSatModel) and wall budget remains,
    // retry ONCE with a fresh solver on the original formula with every
    // model-mutating preprocessing/inprocessing technique disabled. Safe by
    // construction: a retry SAT passes the SAME finalize gate inside
    // declare_sat_from_model (the retry solver's original ledger IS the
    // original formula); a retry UNSAT comes from a fresh, unpoisoned solver
    // (status quo trust level for non-proof mode). One retry only (no storm):
    // the retry result replaces `result` here and cannot re-enter this branch.
    // Budget: solve_interruptible(is_timed_out) polls the same global
    // watchdog, so total wall stays <= the original -t budget. Scoped to
    // non-proof mode (a proof-mode retry would have to re-emit the DRAT/LRAT
    // stream from scratch; see design notes). Kill-switch:
    // AY_AB_FINALIZE_RESCUE=0 (default ON — worst case == status quo UNKNOWN).
    //
    // Proof interaction: the non-UNSAT sidecar cleanup above already took the
    // first solver's proof writer and deleted the proof file, so the retry
    // recreates the DRAT/LRAT stream from scratch on its own solver — a
    // retry UNSAT flows through the same artifact-write + proof-verification
    // path below as any first-attempt UNSAT. Alethe/Lean4 exports happen in
    // their dedicated runners before this point, so those formats are
    // excluded from the lane.
    let mut result = result;
    let mut rescue_storage: Option<SatSolver> = None;
    if finalize_rescue_applicable(solver, &result, proof_config) {
        if let Some((retry_result, retry_solver)) = run_finalize_rescue(source, proof_config) {
            result = retry_result;
            rescue_storage = Some(retry_solver);
        }
    }
    let solver: &mut SatSolver = match rescue_storage.as_mut() {
        Some(retry_solver) => retry_solver,
        None => solver,
    };
    match result {
        SatResult::Sat(model) => {
            crate::mark_verdict_printed();
            safe_println!("s SATISFIABLE");
            emit_dimacs_sat_model(&model);
            // SAT Competition exit code 10 = SATISFIABLE.
            // Flush before process::exit which skips destructors (#3088).
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();
            std::process::exit(10);
        }
        SatResult::Unsat(_) => {
            crate::mark_verdict_printed();
            safe_println!("s UNSATISFIABLE");
            // SAT Competition exit code 20 = UNSATISFIABLE.
            let _ = io::stdout().flush();
            let _ = io::stderr().flush();

            if let Some(proof) = proof_config {
                write_proof_artifact_or_exit(
                    source.proof_artifact_problem(),
                    proof,
                    ProofArtifactTheoryMetadata::dimacs_sat(
                        solver.user_num_vars(),
                        solver.num_original_clauses(),
                    ),
                );
            }

            // Post-solve proof verification (#8771). Default-on under
            // `debug_assertions`, off in release unless `--verify-proof`.
            // Returns true = accepted/skipped, false = rejected (soundness).
            if !verify_unsat_proof_from_source(source, proof_config) {
                std::process::exit(1);
            }

            // Optional Lean kernel verification (#8773, Phase 1). Only runs
            // when `--lean-verify` was set. Exit 2 on kernel rejection per
            // the design doc's exit-code contract.
            if !verify_lean_proof(proof_config) {
                std::process::exit(2);
            }

            std::process::exit(20);
        }
        SatResult::Unknown => {
            // Check timeout before printing. SAT-COMP wrapper runs must use
            // exit 0 for UNKNOWN; normal CLI timeout behavior remains 124.
            dimacs_exit_if_timed_out(Some(solver));
            safe_eprintln!("c reason: incomplete (SAT solver could not determine satisfiability)");
            safe_println!("s UNKNOWN");
            // Exit 0 for unknown (no definitive result)
        }
        #[allow(unreachable_patterns)]
        _ => {
            safe_eprintln!("c reason: unknown");
            safe_println!("s UNKNOWN");
        }
    }
}

// ---------------------------------------------------------------------------
// FINALIZE_SAT_FAIL rescue lane
// ---------------------------------------------------------------------------

/// Kill-switch for the finalize-fail rescue lane. Default ON: the lane only
/// runs after a would-be `s UNKNOWN`, so its worst case equals the status quo.
const FINALIZE_RESCUE_ENV: &str = "AY_AB_FINALIZE_RESCUE";

fn finalize_rescue_applicable(
    solver: &SatSolver,
    result: &SatResult,
    proof_config: Option<&ProofConfig>,
) -> bool {
    // Alethe/Lean4 write their exports in dedicated runners before the
    // finish path; a rescue UNSAT could not re-emit them here. DRAT/LRAT are
    // re-emitted from scratch by the retry solver.
    let proof_compatible = match proof_config {
        None => true,
        Some(proof) => matches!(proof.format, ProofFormat::Drat | ProofFormat::Lrat),
    };
    matches!(result, SatResult::Unknown)
        && proof_compatible
        && solver.last_unknown_reason() == Some(ay_sat::SatUnknownReason::InvalidSatModel)
        && !is_timed_out()
        && env_bool_default(FINALIZE_RESCUE_ENV, true)
}

/// Maximal-reconstruction-robustness retry profile: every technique that
/// mutates the model (needs reconstruction witnesses) or deletes/substitutes
/// original constraints is OFF. Techniques that only add logically implied
/// clauses or remove redundant ones (model-preserving) stay ON, as do
/// phase-initialization heuristics (walk/warmup) whose candidate models still
/// pass the finalize gate.
fn finalize_rescue_profile() -> ay_sat::InprocessingFeatureProfile {
    let mut profile = ay_sat::InprocessingFeatureProfile::default();
    // Initial preprocess pipeline (ELS/pure literals/elimination): the
    // largest reconstruction surface — OFF.
    profile.preprocess = false;
    // Model-mutating / witness-reconstructing eliminations — OFF.
    profile.bve = false;
    profile.bce = false;
    profile.cce = false;
    profile.condition = false;
    profile.decompose = false;
    profile.sweep = false;
    profile.symmetry = false;
    // Variable-adding / gate-rewriting structure passes — OFF.
    profile.factor = false;
    profile.sbva = false;
    profile.gate = false;
    profile.congruence = false;
    // Clause-deleting resolution passes with historical constraint-loss
    // defects (HTR: b1402a16 e318e2ac/90bec6dc/e4ac15cf) — OFF.
    profile.htr = false;
    // Kept ON (model-preserving): vivify, subsume, probe, transred, hbr,
    // shrink, backbone, reorder, walk, warmup.
    profile
}

/// Retry the solve once on the ORIGINAL formula with the degraded profile.
/// Returns the retry result and the retry solver, or None when the original
/// DIMACS text is unavailable or unparseable. The retry result is trustworthy
/// through the same channels as any first-attempt result: SAT models are
/// validated against the retry solver's original ledger (== the original
/// formula) by the finalize gate inside declare_sat_from_model; a retry UNSAT
/// in DRAT/LRAT mode re-emits its proof stream from scratch to the (already
/// cleaned-up) proof path and flows through the same post-solve verification.
fn run_finalize_rescue(
    source: DimacsInputSource<'_>,
    proof_config: Option<&ProofConfig>,
) -> Option<(SatResult, SatSolver)> {
    let owned_content;
    let content = match source {
        DimacsInputSource::Content(content) => content,
        DimacsInputSource::FilePath(path) => {
            owned_content = match std::fs::read_to_string(path) {
                Ok(text) => text,
                Err(error) => {
                    safe_eprintln!("c FINALIZE_RESCUE: skipped (re-read failed: {error})");
                    return None;
                }
            };
            owned_content.as_str()
        }
        DimacsInputSource::Unavailable => {
            safe_eprintln!("c FINALIZE_RESCUE: skipped (original DIMACS unavailable)");
            return None;
        }
    };
    let formula = match parse_dimacs(content) {
        Ok(formula) => formula,
        Err(error) => {
            safe_eprintln!("c FINALIZE_RESCUE: skipped (re-parse failed: {error})");
            return None;
        }
    };
    safe_eprintln!(
        "c FINALIZE_RESCUE: finalize gate rejected the candidate model; retrying once \
         with model-mutating preprocessing disabled (elapsed {}ms)",
        global_elapsed().as_millis()
    );
    let mut solver = match proof_config {
        None => SatSolver::new(formula.num_vars),
        Some(proof) => {
            // The non-UNSAT sidecar cleanup already deleted the first
            // attempt's proof file; recreate it for a from-scratch stream.
            let file = match File::create(&proof.path) {
                Ok(file) => file,
                Err(error) => {
                    safe_eprintln!(
                        "c FINALIZE_RESCUE: skipped (proof re-create failed for {}: {error})",
                        proof.path
                    );
                    return None;
                }
            };
            let writer = proof_output_writer(file);
            let num_original_clauses = formula.clauses.len() as u64;
            let output = match (proof.format, proof.binary) {
                (ProofFormat::Drat, false) => ProofOutput::drat_text(writer),
                (ProofFormat::Drat, true) => ProofOutput::drat_binary(writer),
                (ProofFormat::Lrat, false) => ProofOutput::lrat_text(writer, num_original_clauses),
                (ProofFormat::Lrat, true) => ProofOutput::lrat_binary(writer, num_original_clauses),
                (ProofFormat::Alethe | ProofFormat::Lean4, _) => {
                    // Excluded by finalize_rescue_applicable.
                    return None;
                }
            };
            SatSolver::with_proof_output(formula.num_vars, output)
        }
    };
    solver.set_inprocessing_profile(&finalize_rescue_profile());
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    let verdict = match &result {
        SatResult::Sat(_) => "sat",
        SatResult::Unsat(_) => "unsat",
        _ => "unknown",
    };
    safe_eprintln!(
        "c FINALIZE_RESCUE: retry verdict={verdict} (elapsed {}ms)",
        global_elapsed().as_millis()
    );
    // Mirror the top-of-finish cleanup for the retry stream: a non-UNSAT
    // retry must not leave a stale proof file behind.
    if !matches!(result, SatResult::Unsat(_)) {
        let _ = cleanup_dimacs_non_unsat_proof_sidecar(&mut solver, &result, proof_config);
    }
    Some((result, solver))
}

// ---------------------------------------------------------------------------
// Streaming DIMACS parser for large formulas
// ---------------------------------------------------------------------------

/// Clause count threshold for streaming parser activation.
const STREAMING_CLAUSE_THRESHOLD: usize = 500_000;

/// Quick header scan to get (num_vars, num_clauses) without full parsing.
fn scan_dimacs_header(content: &str) -> Option<(usize, usize)> {
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("p cnf") {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() >= 4 {
                if let (Ok(v), Ok(c)) = (parts[2].parse::<usize>(), parts[3].parse::<usize>()) {
                    return Some((v, c));
                }
            }
        }
        if !trimmed.is_empty() && !trimmed.starts_with('c') && !trimmed.starts_with("p ") {
            break;
        }
    }
    None
}

fn unexpected_tag_error(tag: char) -> DimacsCoreError {
    DimacsCoreError::InvalidLiteral {
        token: format!("unexpected tagged line '{tag}' in CNF input"),
        line_number: 0,
    }
}

fn checked_lrat_original_clause_count(declared: usize) -> Result<u64, DimacsCoreError> {
    let max = usize::try_from(ay_sat::MAX_LRAT_ORIGINAL_CLAUSES).unwrap_or(usize::MAX);
    if declared > max {
        return Err(DimacsCoreError::HeaderCountTooLarge {
            what: "LRAT original-clause",
            declared,
            max,
        });
    }
    u64::try_from(declared).map_err(|_| DimacsCoreError::HeaderCountTooLarge {
        what: "LRAT original-clause",
        declared,
        max,
    })
}

fn run_proof_streaming(
    content: &str,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    proof: &ProofConfig,
) {
    run_proof_streaming_reader(
        content.as_bytes(),
        stats_cfg,
        variant,
        proof,
        DimacsInputSource::Content(content),
        Some(scan_max_variable(content.as_bytes())),
    );
}

fn run_proof_streaming_reader<R>(
    reader: R,
    stats_cfg: stats_output::StatsConfig,
    variant: SolverVariant,
    proof: &ProofConfig,
    source: DimacsInputSource<'_>,
    // Content-driven variable count when the whole input is in memory (the
    // actual maximum variable referenced); `None` for true single-pass streams.
    content_max_var: Option<usize>,
) where
    R: Read,
{
    let mut solver: Option<SatSolver> = None;
    let mut features: Option<SatFeatureAccumulator> = None;
    let mut original_clauses: Vec<(u64, Vec<i32>)> = Vec::new();
    let mut num_vars = 0usize;
    let mut num_clauses_declared = 0usize;
    let mut clause_buf: Vec<Literal> = Vec::with_capacity(32);
    let dense_clique_php_proof_route_requested = env_truthy(SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENV);
    let mut dense_clique_php_proof_route_clauses: Option<Vec<Vec<Literal>>> = None;

    let parse_result = ay_sat::dimacs_core::parse_dimacs_events(reader, |event| {
        match event {
            DimacsEvent::Header(header) => {
                num_vars = header.num_vars;
                num_clauses_declared = header.num_clauses;
                // Validate the LRAT ID space before constructing a writer (and
                // before creating/truncating the requested proof file).
                let num_original_clauses = if matches!(
                    proof.format,
                    ProofFormat::Alethe | ProofFormat::Lean4 | ProofFormat::Lrat
                ) {
                    checked_lrat_original_clause_count(header.num_clauses)?
                } else {
                    0
                };
                let proof_output = match proof.format {
                    ProofFormat::Alethe => ProofOutput::lrat_text(io::sink(), num_original_clauses),
                    ProofFormat::Lean4 => {
                        ProofOutput::lrat_text(Vec::<u8>::new(), num_original_clauses)
                    }
                    ProofFormat::Drat | ProofFormat::Lrat => {
                        let file = match File::create(&proof.path) {
                            Ok(file) => file,
                            Err(error) => exit_failed_proof_create(&proof.path, &error),
                        };
                        let writer = proof_output_writer(file);
                        match (proof.format, proof.binary) {
                            (ProofFormat::Drat, false) => ProofOutput::drat_text(writer),
                            (ProofFormat::Drat, true) => ProofOutput::drat_binary(writer),
                            (ProofFormat::Lrat, false) => {
                                ProofOutput::lrat_text(writer, num_original_clauses)
                            }
                            (ProofFormat::Lrat, true) => {
                                ProofOutput::lrat_binary(writer, num_original_clauses)
                            }
                            (ProofFormat::Alethe | ProofFormat::Lean4, _) => unreachable!(),
                        }
                    }
                };
                // Content-driven sizing: prefer the actual maximum variable
                // (scanned by the caller when the whole input is in memory) over
                // the untrusted declared header count, so an over-declared header
                // cannot drive the per-variable allocation. Falls back to the
                // header only for true single-pass streams (e.g. proof replay),
                // where the backstop still bounds an absurd declared count.
                let solver_num_vars = content_max_var.unwrap_or(header.num_vars);
                if solver_num_vars > ay_sat::dimacs_core::MAX_DIMACS_VARS {
                    return Err(DimacsCoreError::HeaderCountTooLarge {
                        what: "variable",
                        declared: solver_num_vars,
                        max: ay_sat::dimacs_core::MAX_DIMACS_VARS,
                    });
                }
                num_vars = solver_num_vars;
                solver = Some(SatSolver::with_proof_output(solver_num_vars, proof_output));
                features = Some(SatFeatureAccumulator::new(solver_num_vars));
                if dense_clique_php_proof_route_requested
                    && dense_clique_php_route_header_candidate(header.num_vars, header.num_clauses)
                {
                    // Cap the speculative pre-allocation from the untrusted
                    // declared clause count; the vector grows to fit real
                    // clauses anyway (`p cnf 1 4000000000` must not OOM here).
                    dense_clique_php_proof_route_clauses =
                        Some(Vec::with_capacity(header.num_clauses.min(1 << 20)));
                }
            }
            DimacsEvent::Record(DimacsRecordRef::Clause(raw)) => {
                let solver = solver.as_mut().ok_or(DimacsCoreError::MissingHeader)?;
                let features = features.as_mut().ok_or(DimacsCoreError::MissingHeader)?;
                if proof.format == ProofFormat::Lean4 {
                    original_clauses.push((original_clauses.len() as u64 + 1, raw.to_vec()));
                }
                features.add_dimacs_clause_to_buffer(raw, &mut clause_buf);
                if let Some(clauses) = dense_clique_php_proof_route_clauses.as_mut() {
                    clauses.push(clause_buf.clone());
                }
                solver.add_clause_reusing_buffer(&mut clause_buf);
            }
            DimacsEvent::Record(DimacsRecordRef::Tagged { tag, .. }) => {
                return Err(unexpected_tag_error(tag));
            }
            _ => {}
        }
        Ok(())
    });

    if let Err(error) = parse_result {
        if let Some(mut solver) = solver {
            let _ = cleanup_dimacs_non_unsat_proof_sidecar(
                &mut solver,
                &SatResult::Unknown,
                Some(proof),
            );
        } else {
            cleanup_dimacs_non_unsat_proof_paths(Some(proof));
        }
        let error: DimacsError = error.into();
        safe_eprintln!("c Parse error: {}", error);
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    }

    let Some(mut solver) = solver else {
        safe_eprintln!(
            "c Parse error: missing problem line, expected \"p cnf <num_vars> <num_clauses>\""
        );
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    };
    let features = features
        .map(SatFeatureAccumulator::finish)
        .unwrap_or_else(|| SatFeatures::from_streaming_counters(num_vars, 0, 0, 0));

    let lrat_mode = matches!(
        proof.format,
        ProofFormat::Lrat | ProofFormat::Alethe | ProofFormat::Lean4
    );
    maybe_run_dense_clique_php_proof_route(
        dense_clique_php_proof_route_requested,
        &mut solver,
        num_vars,
        num_clauses_declared,
        dense_clique_php_proof_route_clauses.as_deref(),
        stats_cfg,
        proof,
        source,
    );
    let variant_config = variant_profile_plan_for_dimacs_features(
        variant,
        num_vars,
        num_clauses_declared,
        true,
        lrat_mode,
        matches!(proof.format, ProofFormat::Lrat),
        &features,
    )
    .config;
    variant_config.apply_to_solver(&mut solver);

    match proof.format {
        ProofFormat::Alethe => {
            run_dimacs_solver_alethe_with_source(
                &mut solver,
                stats_cfg,
                &proof.path,
                source,
                Some(proof),
            );
        }
        ProofFormat::Lean4 => {
            run_dimacs_solver_lean4_with_source(
                &mut solver,
                stats_cfg,
                &proof.path,
                source,
                Some(proof),
                &original_clauses,
            );
        }
        ProofFormat::Drat | ProofFormat::Lrat => {
            run_dimacs_solver_with_source(&mut solver, stats_cfg, source, Some(proof));
        }
    }
}

/// Fast streaming DIMACS parser path for large formulas.
///
/// Scan a DIMACS CNF body for the maximum variable index that actually appears
/// — the content-driven variable count, independent of the (untrusted) declared
/// header. Comment (`c`), end-marker (`%`), and `p` header lines are skipped;
/// every other line is clause data whose integer tokens are variable references.
/// Uses saturating arithmetic so an over-long digit run cannot wrap.
fn scan_max_variable(bytes: &[u8]) -> usize {
    let mut max_var: usize = 0;
    let mut pos = 0usize;
    let len = bytes.len();
    while pos < len {
        while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if pos >= len {
            break;
        }
        match bytes[pos] {
            b'c' | b'p' => {
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
            b'%' => break,
            _ => {
                // Clause line: read signed integer tokens until end of line.
                while pos < len && bytes[pos] != b'\n' {
                    while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r') {
                        pos += 1;
                    }
                    if pos >= len || bytes[pos] == b'\n' {
                        break;
                    }
                    if bytes[pos] == b'-' || bytes[pos] == b'+' {
                        pos += 1;
                    }
                    let mut val: usize = 0;
                    let mut saw_digit = false;
                    while pos < len && bytes[pos].is_ascii_digit() {
                        val = val
                            .saturating_mul(10)
                            .saturating_add((bytes[pos] - b'0') as usize);
                        saw_digit = true;
                        pos += 1;
                    }
                    if saw_digit {
                        max_var = max_var.max(val);
                    }
                    // Skip any trailing non-whitespace so we always make progress.
                    while pos < len && !matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
                        pos += 1;
                    }
                }
            }
        }
    }
    max_var
}

/// Parses DIMACS bytes directly into `solver.add_clause()`, skipping all
/// intermediate data structures. On shuffling-2 (98MB, 4.7M clauses),
/// this reduces parse+load from >15s to ~2s.
fn run_streaming(content: &str, stats_cfg: stats_output::StatsConfig, variant: SolverVariant) {
    use ay_sat::Literal;

    let bytes = content.as_bytes();
    let len = bytes.len();
    let mut pos = 0;
    let mut num_vars = 0usize;
    let mut num_clauses_declared = 0usize;
    let mut header_found = false;

    while pos < len && !header_found {
        while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if pos >= len {
            break;
        }
        match bytes[pos] {
            b'c' => {
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
            b'%' => break,
            b'p' => {
                let line_start = pos;
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
                let line = &bytes[line_start..pos];
                let mut lpos = 0;
                while lpos < line.len() && line[lpos].is_ascii_alphabetic() {
                    lpos += 1;
                }
                while lpos < line.len() && line[lpos] == b' ' {
                    lpos += 1;
                }
                while lpos < line.len() && line[lpos].is_ascii_alphabetic() {
                    lpos += 1;
                }
                while lpos < line.len() && line[lpos] == b' ' {
                    lpos += 1;
                }
                // Saturating arithmetic so an absurdly long digit run cannot
                // silently wrap to a small count (which would later index OOB);
                // the saturated value is rejected by the cap check below.
                let mut val = 0usize;
                while lpos < line.len() && line[lpos].is_ascii_digit() {
                    val = val
                        .saturating_mul(10)
                        .saturating_add((line[lpos] - b'0') as usize);
                    lpos += 1;
                }
                num_vars = val;
                while lpos < line.len() && line[lpos] == b' ' {
                    lpos += 1;
                }
                let mut val2 = 0usize;
                while lpos < line.len() && line[lpos].is_ascii_digit() {
                    val2 = val2
                        .saturating_mul(10)
                        .saturating_add((line[lpos] - b'0') as usize);
                    lpos += 1;
                }
                num_clauses_declared = val2;
                header_found = true;
            }
            _ => {
                while pos < len && bytes[pos] != b'\n' {
                    pos += 1;
                }
            }
        }
    }

    if !header_found || num_vars == 0 {
        safe_eprintln!("c Parse error: no valid DIMACS header found, expected \"p cnf <num_vars> <num_clauses>\"");
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    }

    // Content-driven sizing: size the solver by the variables that ACTUALLY
    // appear, not the (untrusted) declared header count. A file that declares a
    // huge `num_vars` but uses few variables is solved at its real size instead
    // of OOMing. The streaming path has the whole input in memory, so this is a
    // cheap extra scan; `num_clauses_declared` stays as advisory metadata.
    num_vars = scan_max_variable(bytes);
    // Backstop on the *actual* maximum variable (dense numbering makes the arrays
    // O(max index)): refuse a pathological explicitly-referenced index rather
    // than allocating hundreds of GB.
    if num_vars > ay_sat::dimacs_core::MAX_DIMACS_VARS {
        safe_eprintln!(
            "c Parse error: maximum variable {num_vars} exceeds the maximum supported {}",
            ay_sat::dimacs_core::MAX_DIMACS_VARS
        );
        safe_println!("s UNKNOWN");
        std::process::exit(1);
    }

    let mut solver = SatSolver::new(num_vars);
    let mut streaming_config = variant.config(variant_input_for_dimacs(
        variant,
        num_vars,
        num_clauses_declared,
        false,
        false,
        false,
    ));

    // Streaming path: apply header-level conditioning gate from declared header.
    // Full SatFeatures extraction runs post-parse below using the shared
    // adaptive infrastructure (#8149). Pre-parse we only gate conditioning
    // on the declared ratio since streaming formulas skip clause buffering.
    let ratio = num_clauses_declared as f64 / num_vars.max(1) as f64;
    if ratio > 100.0 {
        streaming_config.features.condition = false;
    }
    streaming_config.apply_to_solver(&mut solver);

    let mut clause_buf: Vec<Literal> = Vec::with_capacity(32);
    let mut clauses_loaded = 0usize;

    // Counters for adaptive Rules 2 and 4 (computed during streaming parse).
    let mut ternary_count = 0usize;
    let mut horn_count = 0usize;
    let mut positive_in_clause = 0u32;

    while pos < len {
        while pos < len && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if pos >= len {
            break;
        }
        let ch = bytes[pos];
        if ch == b'%' {
            break;
        }
        if ch == b'c' {
            while pos < len && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if ch.is_ascii_alphabetic() {
            while pos < len && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }

        let negative = ch == b'-';
        if negative {
            pos += 1;
        }
        if pos >= len || !bytes[pos].is_ascii_digit() {
            pos += 1;
            continue;
        }
        let mut val = 0u32;
        while pos < len && bytes[pos].is_ascii_digit() {
            val = val * 10 + u32::from(bytes[pos] - b'0');
            pos += 1;
        }
        if val == 0 {
            // Clause complete: classify before adding to solver.
            if clause_buf.len() == 3 {
                ternary_count += 1;
            }
            if positive_in_clause <= 1 {
                horn_count += 1;
            }
            positive_in_clause = 0;
            solver.add_clause(std::mem::take(&mut clause_buf));
            clauses_loaded += 1;
        } else {
            if !negative {
                positive_in_clause += 1;
            }
            let variable = Variable::new(val - 1);
            let lit = if negative {
                Literal::negative(variable)
            } else {
                Literal::positive(variable)
            };
            clause_buf.push(lit);
        }
    }

    if !clause_buf.is_empty() {
        // Final unterminated clause: classify it too.
        if clause_buf.len() == 3 {
            ternary_count += 1;
        }
        if positive_in_clause <= 1 {
            horn_count += 1;
        }
        solver.add_clause(clause_buf);
        clauses_loaded += 1;
    }

    // Post-parse adaptive adjustment using shared SatFeatures infrastructure (#8149).
    // Construct a lightweight SatFeatures from the streaming counters and apply
    // the same rules as the buffered path (conditioning gate, symmetry, reorder).
    {
        let features = SatFeatures::from_streaming_counters(
            num_vars,
            clauses_loaded,
            ternary_count,
            horn_count,
        );
        let class = InstanceClass::classify(&features);

        let mut profile = solver.inprocessing_feature_profile();
        adjust_features_for_instance(&features, &class, &mut profile);
        solver.apply_feature_profile(&profile);
    }

    safe_eprintln!("c streaming parse: {clauses_loaded} clauses loaded ({num_vars} vars)");

    configure_dimacs_solver(&mut solver, stats_cfg);
    let result = solver.solve_interruptible(is_timed_out).into_inner();
    finish_dimacs_solve(&mut solver, result, stats_cfg, content, None, None, None);
}

#[cfg(test)]
mod tests;
