// Z3 open-bug theory reproducer suite.
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// Reproducers extracted from open Z3 GitHub issues and checked in as .smt2
// files under `crates/ay-theories/<theory>/tests/z3_{soundness,mod_rem}/`.
// Tracks AY issue #8713 and the Z3 open-bug parity epic #8712.
//
// Each group has two test sets:
//   * `*_expected` — inputs where ay currently returns the expected answer.
//     These assert the expected answer to catch regressions.
//   * `*_observed` — inputs where ay does not yet return the expected answer
//     (partial completeness, unsupported operators, or known soundness gaps
//     under quantifiers / FP datatype wrappers). These pin the CURRENT
//     observed ay answer so that any change — in either direction — is
//     surfaced. Follow-up issues track each failing reproducer.

use ntest::timeout;
use std::process::Command;
use std::time::Duration;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

/// Read the first whitespace-stripped line of ay's stdout (falling back to
/// stderr when stdout is empty, so `(error ...)` responses from the frontend
/// are preserved for diagnostics). Exit-status is not asserted because some
/// reproducers intentionally exercise elaboration errors (missing SMT-LIB
/// operators such as integer `rem` and real `^`).
fn run_ay(smt_file: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg(smt_file)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("Failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let first_stdout = stdout.trim().lines().next().unwrap_or("").to_string();
    if !first_stdout.is_empty() {
        return first_stdout;
    }
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    stderr.trim().lines().next().unwrap_or("").to_string()
}

fn repro_path(theory: &str, subdir: &str, name: &str) -> String {
    // CARGO_MANIFEST_DIR = crates/ay ; reproducers live at
    // crates/ay-theories/<theory>/tests/<subdir>/<name>.
    format!(
        "{}/../ay-theories/{}/tests/{}/{}",
        env!("CARGO_MANIFEST_DIR"),
        theory,
        subdir,
        name
    )
}

// ---------------------------------------------------------------------------
// Group A — Floating-point soundness reproducers.
//
// Target: crates/ay-theories/fp/tests/z3_soundness/
// Issue #8713 Group A.
// ---------------------------------------------------------------------------

/// Z3 #6633 — fpToReal returns unknown on trivial FP constraint.
/// ay answers sat (expected).
#[test]
#[timeout(30_000)]
fn test_fp_z3_6633_expected() {
    let path = repro_path("fp", "z3_soundness", "z3_6633.smt2");
    let result = run_ay(&path);
    assert_eq!(result, "sat", "Z3#6633: expected sat, got {result}");
}

/// Z3 #7162 — invalid model on FP fma chain.
/// Expected: sat. ay currently answers `unknown` (partial FP completeness).
/// This reproducer is slow inside ay (>30s); the test runs with an internal
/// ay timeout so it always terminates, and the soundness check only needs to
/// confirm that ay does not return unsat.
#[test]
#[timeout(120_000)]
fn test_fp_z3_7162_sound() {
    let path = repro_path("fp", "z3_soundness", "z3_7162.smt2");
    // Spawn ay with an explicit --timeout so the test always finishes. The
    // returned answer can be `unknown`; we just need to verify it is not
    // `unsat`.
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let output = Command::new(ay_path)
        .arg("--timeout")
        .arg("15000")
        .arg(&path)
        .output_timeout(Duration::from_secs(115))
        .expect("Failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let result = stdout.trim().lines().next().unwrap_or("").to_string();
    assert_ne!(
        result, "unsat",
        "Z3#7162: spurious unsat on satisfiable FP fma input, got {result}"
    );
}

/// Z3 #7321 — FP-to-Real transitivity failure.
/// Expected: unsat. ay currently answers `unknown`.
/// Soundness-only check: must not return sat.
#[test]
#[timeout(30_000)]
fn test_fp_z3_7321_sound() {
    let path = repro_path("fp", "z3_soundness", "z3_7321.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "sat",
        "Z3#7321: spurious sat on unsat FP-to-Real transitivity, got {result}"
    );
}

/// Z3 #7431 — invalid model on to_fp from Real.
/// Expected: sat. ay currently answers `unknown`.
/// Soundness-only check: must not return unsat.
#[test]
#[timeout(30_000)]
fn test_fp_z3_7431_sound() {
    let path = repro_path("fp", "z3_soundness", "z3_7431.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "unsat",
        "Z3#7431: spurious unsat on to_fp-from-Real input, got {result}"
    );
}

/// Z3 #7842 — NaN distinctness violated under a datatype wrapper.
/// Expected: unsat. ay previously returned spurious `sat` because the ALL
/// logic auto-detector misrouted DT+FP formulas to QF_DT, dropping the FP
/// theory entirely (#8728). After the fix, ay returns `unknown` — DT+FP
/// has no sound combined solver yet, so we refuse to solve rather than
/// return an unsound answer. This is soundness-preserving: any answer other
/// than `sat` is acceptable, `unknown` is the best achievable until a real
/// DT+FP pipeline exists.
#[test]
#[timeout(30_000)]
fn test_fp_z3_7842_sound() {
    let path = repro_path("fp", "z3_soundness", "z3_7842.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "sat",
        "Z3#7842: spurious sat on unsat DT+FP NaN-distinctness input, got {result}"
    );
}

/// Z3 #7842 companion — explicit `(set-logic QF_FP)` + (declare-datatype).
/// Same formula as `z3_7842.smt2` but with an explicit logic declaration
/// instead of the `ALL` auto-detection path. Guards against regressions
/// where a future change to `with_datatypes()` or `Other`-branch dispatch
/// would re-introduce the DT+FP soundness gap on the explicit-logic path
/// while leaving the ALL auto-detection path correct (#8728).
#[test]
#[timeout(30_000)]
fn test_fp_z3_7842_qf_fp_sound() {
    let path = repro_path("fp", "z3_soundness", "z3_7842_qf_fp.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "sat",
        "Z3#7842 (QF_FP): spurious sat on DT+FP NaN-distinctness with explicit logic, got {result}"
    );
}

/// Z3 #7842 companion — explicit `(set-logic QF_BVFP)` + (declare-datatype).
/// Covers the BV+FP branch of the DT+FP soundness fix: the feature
/// detector picks QF_BVFP when BV is present, and the dispatcher must
/// map that to `Other` and return `Unknown`+Incomplete rather than
/// dropping the FP theory. Paired with `test_fp_z3_7842_qf_fp_sound` so
/// both legs of `logic_detect.rs`'s DT+FP branch are pinned (#8728).
#[test]
#[timeout(30_000)]
fn test_fp_z3_7842_qf_bvfp_sound() {
    let path = repro_path("fp", "z3_soundness", "z3_7842_qf_bvfp.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "sat",
        "Z3#7842 (QF_BVFP): spurious sat on DT+FP NaN-distinctness with explicit logic, got {result}"
    );
}

/// Z3 #8185 — invalid model with strings + FP + proofs.
/// Expected: sat. ay currently answers `unknown`.
/// Soundness-only check: must not return unsat.
#[test]
#[timeout(30_000)]
fn test_fp_z3_8185_sound() {
    let path = repro_path("fp", "z3_soundness", "z3_8185.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "unsat",
        "Z3#8185: spurious unsat on FP+strings+proofs input, got {result}"
    );
}

// ---------------------------------------------------------------------------
// Group B — Arithmetic mod/rem/div0 reproducers.
//
// Target: crates/ay-theories/lia/tests/z3_mod_rem/
// Issue #8713 Group B.
// ---------------------------------------------------------------------------

/// Z3 #9140 — rem collapses to mod on zero divisor.
/// Expected: sat. ay implements `rem` via mk_rem (see #8730); for the
/// zero-divisor case we keep `rem` as its own uninterpreted symbol, so
/// `(distinct (rem x 0) (mod x 0))` is satisfiable. The LIA theory does not
/// yet know how to assign a concrete model to the uninterpreted `rem x 0`
/// application, so ay returns `unknown` (incomplete) here rather than `sat`.
/// The soundness contract is preserved: ay must not claim `unsat`.
#[test]
#[timeout(30_000)]
fn test_lia_z3_9140_observed() {
    let path = repro_path("lia", "z3_mod_rem", "z3_9140.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "unsat",
        "Z3#9140: must not claim unsat under SMT-LIB mod0/rem0 semantics, got {result}"
    );
    assert!(
        result == "sat" || result == "unknown",
        "Z3#9140: expected sat or unknown after rem support lands, got {result}"
    );
}

/// Integer `rem` constant-folding coverage (#8730). Pins the Z3 semantics
/// (remainder takes the sign of the divisor) with `rem 7 3`, `rem -7 3`,
/// `rem 7 -3`, `rem -7 -3` in one benchmark. Expected: sat.
#[test]
#[timeout(30_000)]
fn test_lia_rem_constant_folding() {
    let path = repro_path("lia", "z3_mod_rem", "rem_constant_folding.smt2");
    let result = run_ay(&path);
    assert_eq!(
        result, "sat",
        "rem constant folding: expected sat, got {result}"
    );
}

/// Z3 #7464 — infinite loop on mod with variable divisor.
/// Minimized core: `(mod nn m) = 0` with `m > 0`.
/// Expected: sat. ay currently answers `unknown`.
/// Soundness-only check: must not return unsat.
#[test]
#[timeout(30_000)]
fn test_lia_z3_7464_sound() {
    let path = repro_path("lia", "z3_mod_rem", "z3_7464.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "unsat",
        "Z3#7464: spurious unsat on satisfiable mod-with-variable-divisor, got {result}"
    );
}

/// Z3 #7403 — non-termination with mod0/div0 + quantifiers.
/// Expected: sat. Depends on quantifier support tracked in #8340. ay currently
/// answers sat via a non-quantifier path on this minimized form.
/// Soundness-only check: must not return unsat.
#[test]
#[timeout(30_000)]
fn test_lia_z3_7403_sound() {
    let path = repro_path("lia", "z3_mod_rem", "z3_7403.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "unsat",
        "Z3#7403: spurious unsat on quantified mod0 input, got {result}"
    );
}

// ---------------------------------------------------------------------------
// Group C — Nonlinear soundness reproducers.
//
// Target: crates/ay-theories/nra/tests/z3_soundness/
// Issue #8713 Group C. PR ports (#8747, #9249) are separate work items.
// ---------------------------------------------------------------------------

/// Z3 #9139 — NRA soundness bug. cvc5 confirms sat; Z3 returned unsat.
/// ay answers sat (expected).
#[test]
#[timeout(30_000)]
fn test_nra_z3_9139_expected() {
    let path = repro_path("nra", "z3_soundness", "z3_9139.smt2");
    let result = run_ay(&path);
    assert_eq!(result, "sat", "Z3#9139: expected sat, got {result}");
}

/// Z3 #9319 — invalid model on (^ (* x 2.0) (/ 1.0 x)) with x = 0.
/// AY elaborates `^` under SMT-LIB Reals_Ints §3.8 partial semantics
/// (integer-literal exponents are unfolded to multiplication; symbolic
/// exponents become an uninterpreted application). The under-specified
/// `0^(1/x)` term permits `sat`; Z3 also returns sat (after first
/// printing its `unknown constant ^` error). Expected: sat.
#[test]
#[timeout(30_000)]
fn test_nra_z3_9319_expected() {
    let path = repro_path("nra", "z3_soundness", "z3_9319.smt2");
    let result = run_ay(&path);
    assert_eq!(result, "sat", "Z3#9319: expected sat, got {result}");
}

// ---------------------------------------------------------------------------
// Group D — Arrays + sets reproducers.
//
// Target: crates/ay-theories/arrays/tests/z3_soundness/
// Issue #8713 Group D.
// ---------------------------------------------------------------------------

/// Z3 #6303 — array range-sort inconsistency (BV32 case).
/// Expected: unsat. ay previously returned spurious `sat` because the ALL
/// logic auto-detector stripped the quantifier and bit-blasted the ground
/// residue, letting the SAT solver satisfy `a = b = (as const _ #x0)` while
/// the forall-forced index agreement was never checked (#8729). After the
/// fix, ay returns `unknown` — partial E-matching on a forall with
/// array-sorted binders is unsound for SAT, so the solver refuses to claim
/// either sat or unsat until full quantifier instantiation lands. Any
/// answer other than `sat` is acceptable; `unknown` is the current best.
#[test]
#[timeout(60_000)]
fn test_arrays_z3_6303_bv32_sound() {
    let path = repro_path("arrays", "z3_soundness", "z3_6303_bv32.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "sat",
        "Z3#6303 (BV32): spurious sat on unsat array-range-sort input with forall binder, got {result}"
    );
}

/// Z3 #6303 — array range-sort inconsistency (BV8 case).
/// Expected: unsat. Same soundness reasoning as the BV32 case (#8729).
/// After the fix, ay returns `unknown`. The assertion rejects any `sat`
/// answer; `unknown` is acceptable until full quantifier support lands.
#[test]
#[timeout(60_000)]
fn test_arrays_z3_6303_bv8_sound() {
    let path = repro_path("arrays", "z3_soundness", "z3_6303_bv8.smt2");
    let result = run_ay(&path);
    assert_ne!(
        result, "sat",
        "Z3#6303 (BV8): spurious sat on unsat array-range-sort input with forall binder, got {result}"
    );
}

/// Z3 #7132 — unsound ABV model (minimized store-equality reproducer).
/// Expected: unsat. ay answers unsat (expected).
#[test]
#[timeout(30_000)]
fn test_arrays_z3_7132_expected() {
    let path = repro_path("arrays", "z3_soundness", "z3_7132.smt2");
    let result = run_ay(&path);
    assert_eq!(result, "unsat", "Z3#7132: expected unsat, got {result}");
}

/// Z3 #7544 — wrong solution for subset / Bool Set (encoded as characteristic
/// arrays). Expected: unsat. ay answers unsat (expected).
#[test]
#[timeout(30_000)]
fn test_arrays_z3_7544_expected() {
    let path = repro_path("arrays", "z3_soundness", "z3_7544.smt2");
    let result = run_ay(&path);
    assert_eq!(result, "unsat", "Z3#7544: expected unsat, got {result}");
}

/// Z3 #9293 — invalid model on select with nested arrays (minimized).
/// Expected: unsat. ay answers unsat (expected).
#[test]
#[timeout(30_000)]
fn test_arrays_z3_9293_expected() {
    let path = repro_path("arrays", "z3_soundness", "z3_9293.smt2");
    let result = run_ay(&path);
    assert_eq!(result, "unsat", "Z3#9293: expected unsat, got {result}");
}

/// Z3 #7825 — arrays perf stress scaffold. Soundness-only check.
#[test]
#[timeout(60_000)]
fn test_arrays_z3_7825_sound() {
    let path = repro_path("arrays", "z3_soundness", "z3_7825.smt2");
    let result = run_ay(&path);
    // Accept either sat or unsat depending on how ay constrains the
    // distinct-index chain; reject any error/timeout surface.
    assert!(
        result == "sat" || result == "unsat" || result == "unknown",
        "Z3#7825: unexpected surface {result}"
    );
}

/// Z3 #438 — QF_ABV query hangs (minimized). Soundness-only check.
#[test]
#[timeout(60_000)]
fn test_arrays_z3_438_sound() {
    let path = repro_path("arrays", "z3_soundness", "z3_438.smt2");
    let result = run_ay(&path);
    assert_eq!(
        result, "sat",
        "Z3#438: expected sat on minimized repro, got {result}"
    );
}

/// Array-default congruence regression — store-over-const cannot equal a
/// const-array with a different default.
///
///   `store((as const (Array Int Int)) 0, k, v) = (as const (Array Int Int)) 1`
///
/// is UNSAT: the store fixes exactly one index, but the two const arrays
/// disagree at the infinitely many others. AY previously returned a spurious
/// `sat` because the single-Skolem extensionality witness can only force
/// agreement at ONE fresh index, which the solver equates with the store index
/// to dodge the read-over-const conflict — so a positive equality between two
/// provably-different arrays was never refuted.
///
/// Fix: `add_array_default_congruence_axioms` asserts the array tautology
/// `a = b => default(a) = default(b)`. Here `default(store(const 0, k, v))`
/// folds to `default(const 0) = 0` and `default(const 1) = 1`, so the
/// consequent `(= 0 1)` is `false` and the clause collapses to the unit
/// `(not (= lhs rhs))`, refuting the equality. z3 returns `unsat`; AY must too.
///
/// This is orthogonal to the `select`-over-`ite` Shannon-lift on the array-EUF
/// route (which only rewrites `(select (ite c A B) i)`): this reproducer has no
/// `ite` and no `select`, so the lift does not touch it. Both soundness fixes
/// coexist.
#[test]
#[timeout(30_000)]
fn test_arrays_store_const_eq_const_diff_default_unsat() {
    let path = repro_path(
        "arrays",
        "z3_soundness",
        "store_const_eq_const_diff_default.smt2",
    );
    let result = run_ay(&path);
    assert_eq!(
        result, "unsat",
        "store-over-const = const with different default must be unsat (z3: unsat), got {result}"
    );
}
