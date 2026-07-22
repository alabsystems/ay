// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real-optimization epsilon battery (#opt-epsilon).
//!
//! Pins the delta-rational objective simplex end to end: strict inequalities
//! (`<`/`>`) now DECIDE instead of failing closed, unattained optima print
//! z3's exact `(get-objectives)` epsilon grammar, and every documented
//! deviation from z3 is pinned as such — never silently.
//!
//! Comparison baseline updated to z3 5.0.0 on 2026-07-20 (was z3 4.15.4).
//! z3 5.0.0 FIXED three optimization defects 4.15.4 got wrong — box-mode
//! strict bounds (`m5`/`m8`), lex successor abandonment (`g5`/`adv7`), and a
//! square-objective case — so AY now AGREES with z3 5.0.0 where it previously
//! "deviated as more-correct" from 4.15.4. Two defects REMAIN in 5.0.0
//! (attained-optimum-as-`epsilon` `adv3`; and `seq.last_indexof` elsewhere);
//! AY stays correct/divergent on those.
//!
//! Every fixture in `opt_epsilon/` has a captured z3 5.0.0 reference output
//! beside it (`<name>.z3.expected`, regenerated 2026-07-20 with z3 5.0.0).
//! Comparison classes used below:
//!
//! * **PARITY** — AY's stdout is byte-identical to the z3 capture (modulo
//!   AY's trailing blank line; comparison is over non-empty lines).
//! * **COSMETIC** — identical semantics, pre-existing formatting divergence,
//!   explicitly out of scope for #opt-epsilon and pinned as-is:
//!   - integral Real optima print `2.0` where z3 prints `2`;
//!   - objective TERM strings normalize differently (`(* x 2.0)` vs
//!     `(* 2.0 x)`, `(+ x (- y))` vs `(- x y)`).
//! * **PARITY (z3 5.0.0 defect-fix)** — box mode + any strict bound: 4.15.4
//!   reported interior points / bogus `oo` (`m5`/`m8`: `(x 1)` for `0<x<3`
//!   maximize); z3 5.0.0 now prints the correct `3 - ε` sup and `(y 5)`, so AY
//!   AGREES with z3 5.0.0 here (cosmetic `5.0` vs `5` aside). Non-strict box
//!   `m7` was always fine.
//! * **AY SOUND-BUT-INCOMPLETE** — lex with an unattained/unbounded NON-final
//!   objective: 4.15.4 emitted a FALSE successor scalar (`g5`: `(y (- 1))`
//!   where max y is 5); z3 5.0.0 now decides the suffix correctly (`(y 5)` /
//!   `(y oo)`). AY conservatively marks the suffix unavailable (fail-closed,
//!   sound — never a wrong scalar), so z3 5.0.0 is now MORE complete here.
//! * **DEVIATION (z3 defect, still live in 5.0.0)** — a strict Real bound
//!   weakly coupled through an Int term: z3 5.0.0 still reports `epsilon`
//!   where the true optimum 2 is attained (`adv3`); AY prints the truth.
//! * **DEVIATION (honest)** — AY refuses to answer where z3 fabricates:
//!   `(get-objectives)` after `unsat` errors (z3 prints an oo-interval,
//!   `adv8`); `x < i (Int)` upper-coupling returns `unknown` (Int guard
//!   conservatism, `m15b`) but NEVER a wrong attained scalar.
//!
//! Model semantics (verified against z3, `m1`/`m2`): after an unattained
//! optimum the model is an ORDINARY feasible point, not near-sup — so model
//! VALUES are not pinned here (they are not a stable contract); feasibility
//! is checked against the fixture's own constraints via z3 when available.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::OnceLock;

use ntest::timeout;

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_cli/opt_epsilon")
        .join(name)
}

/// Run the `ay` binary in z3-compat stdin mode over a fixture and return the
/// non-empty stdout lines (stdin mode avoids the `.alethe` side files a file
/// argument would drop next to the fixtures).
fn run_fixture(name: &str) -> Vec<String> {
    let script = std::fs::read_to_string(fixture_path(name))
        .unwrap_or_else(|e| panic!("read fixture {name}: {e}"));
    run_script(&script)
}

fn run_script(script: &str) -> Vec<String> {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let mut child = Command::new(ay_path)
        .arg("--z3-mode")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(script.as_bytes())
        .expect("write stdin");
    let output = child.wait_with_output().expect("wait ay");
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(str::to_owned)
        .collect()
}

fn assert_lines(name: &str, expected: &[&str]) {
    let got = run_fixture(name);
    assert_eq!(
        got, expected,
        "fixture {name}: AY output diverged from the pinned expectation"
    );
}

/// True when a `z3` binary is on PATH (differential/model checks skip
/// gracefully without it — the AY-side pins above always run).
fn z3_available() -> bool {
    static AVAILABLE: OnceLock<bool> = OnceLock::new();
    *AVAILABLE.get_or_init(|| {
        Command::new("z3")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    })
}

fn z3_check_script(script: &str) -> Option<String> {
    if !z3_available() {
        return None;
    }
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn z3");
    child
        .stdin
        .as_mut()
        .expect("stdin")
        .write_all(script.as_bytes())
        .expect("write z3 stdin");
    let output = child.wait_with_output().expect("wait z3");
    Some(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

/// Extract `(define-fun <var> () Real <value>)` bindings from AY's z3-mode
/// model output.
fn model_bindings(lines: &[String]) -> Vec<(String, String)> {
    lines
        .iter()
        .filter_map(|line| {
            let line = line.trim();
            let rest = line.strip_prefix("(define-fun ")?;
            let (var, rest) = rest.split_once(' ')?;
            let value = rest.strip_prefix("() Real ")?.strip_suffix(')')?;
            Some((var.to_owned(), value.to_owned()))
        })
        .collect()
}

/// Conjoin the fixture's own constraints with AY's printed model values on z3:
/// must be `sat` (handoff §4 gate 2 — the model is real, not fabricated).
fn assert_model_feasible_on_z3(fixture: &str, decls_and_asserts: &str, lines: &[String]) {
    let bindings = model_bindings(lines);
    assert!(
        !bindings.is_empty(),
        "{fixture}: expected a model in the output: {lines:?}"
    );
    let mut script = String::from(decls_and_asserts);
    for (var, value) in &bindings {
        script.push_str(&format!("(assert (= {var} {value}))\n"));
    }
    script.push_str("(check-sat)\n");
    if let Some(verdict) = z3_check_script(&script) {
        assert_eq!(
            verdict, "sat",
            "{fixture}: AY's model values are infeasible per z3:\n{script}"
        );
    }
}

// --- Battery item 1: unattained supremum (PARITY) ---

#[test]
#[timeout(60_000)]
fn g1_strict_upper_maximize_prints_epsilon_form() {
    // Byte-parity with g1.z3.expected.
    assert_lines(
        "g1.smt2",
        &[
            "sat",
            "(objectives",
            " (x (+ 3.0 (* (- 1.0) epsilon)))",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn m1_unattained_model_is_ordinary_feasible_point() {
    let lines = run_fixture("m1_max_model.smt2");
    assert_eq!(lines[0], "sat");
    assert_eq!(lines[2], " (x (+ 3.0 (* (- 1.0) epsilon)))");
    // Model: ANY feasible point (z3 parity m1: x = 0.0, NOT near-sup).
    assert_model_feasible_on_z3("m1", "(declare-const x Real)\n(assert (< x 3.0))\n", &lines);
    // (get-value (x)) after the model must answer (no error).
    let last = lines.last().expect("get-value line");
    assert!(
        last.starts_with("((x ") && !last.contains("error"),
        "get-value after unattained optimum must answer: {last}"
    );
}

// --- Battery item 2: attained via strict-elsewhere + conjunction flattening ---

#[test]
#[timeout(60_000)]
fn g2_conjunction_with_dominated_strict_attains() {
    // COSMETIC: z3 prints `(x 2)`.
    assert_lines("g2.smt2", &["sat", "(objectives", " (x 2.0)", ")"]);
}

#[test]
#[timeout(60_000)]
fn g2b_weak_bound_with_strict_elsewhere_attains() {
    // COSMETIC: z3 prints `(x 10)`.
    assert_lines("g2b.smt2", &["sat", "(objectives", " (x 10.0)", ")"]);
}

#[test]
#[timeout(60_000)]
fn m14_all_weak_conjunction_decides() {
    // The adjacent conjunction-flattening bug: no strict bound at all, but the
    // top-level `and` previously hid the bounds from the standalone simplex.
    // COSMETIC: z3 prints `(x 3)`.
    assert_lines(
        "m14_and_weak.smt2",
        &["sat", "(objectives", " (x 3.0)", ")"],
    );
}

// --- Battery item 3: strict lower minimize (PARITY) ---

#[test]
#[timeout(60_000)]
fn g3_strict_lower_minimize_prints_epsilon() {
    assert_lines(
        "g3_min_strict.smt2",
        &["sat", "(objectives", " (x (+ (/ 3.0 2.0) epsilon))", ")"],
    );
}

#[test]
#[timeout(60_000)]
fn m3_zero_infimum_prints_bare_epsilon() {
    let lines = run_fixture("m3_min_eps_zero.smt2");
    assert_eq!(&lines[..4], &["sat", "(objectives", " (x epsilon)", ")"]);
    assert_model_feasible_on_z3("m3", "(declare-const x Real)\n(assert (> x 0.0))\n", &lines);
}

// --- Battery item 4: coefficient / chain scaling (values PARITY) ---

#[test]
#[timeout(60_000)]
fn m4_epsilon_scales_through_bound_chains() {
    let lines = run_fixture("m4_two_strict.smt2");
    assert_eq!(
        &lines[..4],
        &[
            "sat",
            "(objectives",
            " (y (+ 3.0 (* (- 2.0) epsilon)))",
            ")"
        ]
    );
    assert_model_feasible_on_z3(
        "m4",
        "(declare-const x Real)\n(declare-const y Real)\n(assert (< x 3.0))\n(assert (< y x))\n",
        &lines,
    );
}

#[test]
#[timeout(60_000)]
fn m12_epsilon_scales_through_objective_coefficients() {
    // Value part PARITY; the TERM prints `(* x 2.0)` where z3 prints
    // `(* 2.0 x)` (COSMETIC, pre-existing term normalization).
    assert_lines(
        "m12_obj_expr.smt2",
        &[
            "sat",
            "(objectives",
            " ((* x 2.0) (+ 6.0 (* (- 2.0) epsilon)))",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn m16_scaled_zero_infimum() {
    assert_lines(
        "m16_zero_2eps.smt2",
        &["sat", "(objectives", " ((* x 2.0) (* 2.0 epsilon))", ")"],
    );
}

#[test]
#[timeout(60_000)]
fn m9_zero_supremum_keeps_explicit_negative_coefficient() {
    assert_lines(
        "m9_max_neg.smt2",
        &["sat", "(objectives", " (x (* (- 1.0) epsilon))", ")"],
    );
}

#[test]
#[timeout(60_000)]
fn m10_min_coefficient_two() {
    assert_lines(
        "m10_min_2eps.smt2",
        &[
            "sat",
            "(objectives",
            " (x (+ (/ 3.0 2.0) (* 2.0 epsilon)))",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn m11_negative_supremum() {
    assert_lines(
        "m11_neg_sup.smt2",
        &[
            "sat",
            "(objectives",
            " (x (+ (- (/ 5.0 2.0)) (* (- 1.0) epsilon)))",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn adv5_fractional_epsilon_coefficient() {
    // Value part PARITY (fractional k); term COSMETIC (z3: `(* (/ 1.0 2.0) x)`).
    assert_lines(
        "adv5_frac_k.smt2",
        &[
            "sat",
            "(objectives",
            " ((* x (/ 1 2)) (+ (/ 3.0 2.0) (* (- (/ 1.0 2.0)) epsilon)))",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn adv6_negative_infimum_elides_unit_coefficient() {
    assert_lines(
        "adv6_negv_min.smt2",
        &[
            "sat",
            "(objectives",
            " (x (+ (- (/ 5.0 2.0)) epsilon))",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn adv1_epsilon_accumulates_never_cancels() {
    // maximize (x - y) with x < 3, y > 1: both strict bounds contribute the
    // SAME ε-sign through the objective (sup 2 as 2 - 2ε) — no cancellation.
    // Term COSMETIC (z3: `(- x y)`).
    assert_lines(
        "adv1_cancel.smt2",
        &[
            "sat",
            "(objectives",
            " ((+ x (- y)) (+ 2.0 (* (- 2.0) epsilon)))",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn adv4_equality_chain_doubles_epsilon() {
    // Full byte PARITY including the term string.
    assert_lines(
        "adv4_eq_strict.smt2",
        &[
            "sat",
            "(objectives",
            " ((+ x y) (+ 6.0 (* (- 2.0) epsilon)))",
            ")",
        ],
    );
}

// --- Battery item 5: lexicographic mixes ---

#[test]
#[timeout(60_000)]
fn m6_lex_attained_then_unattained_final() {
    let lines = run_fixture("m6_lex_strict_second.smt2");
    assert_eq!(
        &lines[..5],
        &[
            "sat",
            "(objectives",
            " (x 2.0)",
            " (y (+ 5.0 (* (- 1.0) epsilon)))",
            ")",
        ]
    );
    // The final model must ATTAIN the committed lex prefix (x = 2.0).
    let bindings = model_bindings(&lines);
    assert!(
        bindings.iter().any(|(v, val)| v == "x" && val == "2.0"),
        "lex prefix optimum must be attained by the final model: {bindings:?}"
    );
    assert_model_feasible_on_z3(
        "m6",
        "(declare-const x Real)\n(declare-const y Real)\n(assert (<= x 2.0))\n(assert (< y 5.0))\n",
        &lines,
    );
}

#[test]
#[timeout(60_000)]
fn g5_lex_unattained_prefix_marks_suffix_unavailable() {
    // AY SOUND-BUT-INCOMPLETE: 4.15.4 printed the demonstrably FALSE
    // `(y (- 1))` (max y under y <= 5 is 5); z3 5.0.0 now decides the suffix
    // correctly as `(y 5)` (still an interval for the non-final x). AY
    // conservatively refuses to fabricate a suffix scalar and fail-closes it
    // (sound — never a wrong scalar); `check-sat` stays sat and the model is
    // an ordinary feasible witness. z3 5.0.0 is now more complete here.
    let lines = run_fixture("g5_lex_unattained_first.smt2");
    assert_eq!(lines[0], "sat");
    assert_eq!(
        lines[1],
        "(error \"objective 1 is unavailable after a lexicographic predecessor with no attainable optimum\")"
    );
    assert_model_feasible_on_z3(
        "g5",
        "(declare-const x Real)\n(declare-const y Real)\n(assert (< x 3.0))\n(assert (<= y 5.0))\n",
        &lines,
    );
}

#[test]
#[timeout(60_000)]
fn adv7_lex_unattained_prefix_before_unbounded() {
    // Same class as g5: 4.15.4 printed `(y 0)` for an UNBOUNDED y; z3 5.0.0
    // now decides it correctly as `(y oo)`. AY fail-closes the suffix (sound).
    assert_lines(
        "adv7_lex_unatt_then_unbounded.smt2",
        &[
            "sat",
            "(error \"objective 1 is unavailable after a lexicographic predecessor with no attainable optimum\")",
        ],
    );
}

// --- Battery item 6: box mode ---

#[test]
#[timeout(60_000)]
fn m8_box_with_strict_reports_correct_independent_optima() {
    // PARITY (z3 5.0.0 defect-fix): z3 4.15.4 reported `(x 1)` (an interior
    // point of 0 < x < 3!) and `(y oo)` for `y <= 5`; z3 5.0.0 FIXED the
    // box-mode strict-bound defect and now prints the CORRECT independent
    // optima `(x 3 - ε)` + `(y 5)` — so AY now AGREES with z3 5.0.0 (cosmetic
    // `5.0` vs `5` aside). Captured evidence: m5/m7/m8 .z3.expected.
    assert_lines(
        "m8_box_bounded.smt2",
        &[
            "sat",
            "(objectives",
            " (x (+ 3.0 (* (- 1.0) epsilon)))",
            " (y 5.0)",
            ")",
        ],
    );
}

#[test]
#[timeout(60_000)]
fn m5_box_mixed_strict_weak() {
    // Same class: z3 4.15.4 printed `(x 0)` + `(y oo)`; z3 5.0.0 now prints
    // the correct `(x 3 - ε)` + `(y 5)`, so AY AGREES with z3 5.0.0.
    let lines = run_fixture("m5_box.smt2");
    assert_eq!(
        &lines[..5],
        &[
            "sat",
            "(objectives",
            " (x (+ 3.0 (* (- 1.0) epsilon)))",
            " (y 5.0)",
            ")",
        ]
    );
}

#[test]
#[timeout(60_000)]
fn m7_box_nonstrict_regression_pin() {
    // No strict bound: plain box path, unchanged (COSMETIC vs z3's `3`/`5`).
    assert_lines(
        "m7_box_nonstrict.smt2",
        &["sat", "(objectives", " (x 3.0)", " (y 5.0)", ")"],
    );
}

// --- Battery item 7: wrong-fact / classification twins (fail direction) ---

#[test]
#[timeout(60_000)]
fn w1_strict_and_weak_contradiction_stays_unsat() {
    assert_lines("w1_wrongfact_sup.smt2", &["unsat"]);
}

#[test]
#[timeout(60_000)]
fn w2_incremental_reassert_of_sup_flips_to_unsat() {
    // sat (with recorded 3 - ε), then `(assert (>= x 3.0))` → unsat: state
    // from the first optimization must not leak into the second check.
    assert_lines("w2_ge_sup_unsat.smt2", &["sat", "unsat"]);
}

#[test]
#[timeout(60_000)]
fn w3_epsilon_optimum_is_not_attained_maximize() {
    // Classification twin: conjoining `x = sup` with the strict bound is
    // UNSAT — the ε-form really is unattained (z3 agrees).
    assert_lines("w3_eq_sup_unsat.smt2", &["unsat"]);
}

#[test]
#[timeout(60_000)]
fn w4_epsilon_optimum_is_not_attained_minimize() {
    assert_lines("w4_eq_inf_unsat.smt2", &["unsat"]);
}

#[test]
#[timeout(60_000)]
fn m15_int_guard_kill_shot() {
    // `x <= i (Int), i < 3, maximize x`: the LP delta-relaxation reads 3 - ε,
    // but the Int tightening makes 2 ATTAINED. The Int guard must force the
    // exact fallback: `(x 2.0)`, and NEVER an epsilon form.
    let lines = run_fixture("m15_int_strict_real_obj.smt2");
    assert_eq!(&lines[..4], &["sat", "(objectives", " (x 2.0)", ")"]);
    assert!(
        lines.iter().all(|l| !l.contains("epsilon")),
        "Int-coupled strict bound must never print an epsilon form: {lines:?}"
    );
}

#[test]
#[timeout(60_000)]
fn m15b_int_strict_upper_fails_closed() {
    // DEVIATION (honest, documented residual conservatism): `x < i (Int),
    // i <= 5, maximize x` has true sup 5 unattained (z3 5.0.0 correctly prints
    // 5 - ε); AY's Int guard returns unknown rather than trust the LP
    // relaxation near Int terms. MUST never print an attained `(x 5.0)`.
    assert_lines(
        "m15b_int_strict_upper.smt2",
        &["unknown", "(error \"objectives are not available\")"],
    );
}

#[test]
#[timeout(60_000)]
fn adv3_int_weak_coupling_is_attained_not_epsilon() {
    // DEVIATION (z3 defect, still live in 5.0.0): `x <= i (Int), i <= 2.5,
    // maximize x` — Int tightening gives i <= 2, so 2 is ATTAINED (x = i =
    // 2). z3 5.0.0 STILL prints `(x epsilon)` (one of the two defects 5.0.0
    // did not fix), which is wrong twice over (the optimum is neither 0-based
    // nor unattained). AY prints the truth `(x 2.0)`.
    let lines = run_fixture("adv3_int_weak.smt2");
    assert_eq!(&lines[..4], &["sat", "(objectives", " (x 2.0)", ")"]);
    // z3 cross-check of AY's claim: x = 2 must be feasible, x > 2 infeasible.
    if let Some(v) = z3_check_script(
        "(declare-const x Real)(declare-const i Int)(assert (<= x i))(assert (<= i 2.5))(assert (= x 2.0))(check-sat)",
    ) {
        assert_eq!(v, "sat", "adv3: 2 must be attainable");
    }
    if let Some(v) = z3_check_script(
        "(declare-const x Real)(declare-const i Int)(assert (<= x i))(assert (<= i 2.5))(assert (> x 2.0))(check-sat)",
    ) {
        assert_eq!(v, "unsat", "adv3: nothing above 2 may be feasible");
    }
}

// --- Battery item 8: Int regression pins (byte PARITY) ---

#[test]
#[timeout(60_000)]
fn int_pins_unchanged() {
    assert_lines(
        "g4_int_min.smt2",
        &["sat", "(objectives", " (x 0)", ")", "((x 0))"],
    );
    assert_lines(
        "g4b_int_strict.smt2",
        &["sat", "(objectives", " (x 2)", ")"],
    );
    assert_lines(
        "m17_int_obj_strict_real.smt2",
        &["sat", "(objectives", " (x 10)", ")"],
    );
    assert_lines(
        "q1e_lia_strict.smt2",
        &["sat", "(objectives", " (x 3)", ")"],
    );
}

// --- Battery item 9: previously-deciding pins (no regression) ---

#[test]
#[timeout(60_000)]
fn previously_deciding_pins_unchanged() {
    assert_lines(
        "v2_unrelated_strict_bounded.smt2",
        &["sat", "(objectives", " (x 10.0)", ")"],
    );
    assert_lines(
        "v3_strict_dominated_min.smt2",
        &["sat", "(objectives", " (x 2.0)", ")"],
    );
    assert_lines(
        "g5c.smt2",
        &["sat", "(objectives", " (x 2.0)", " (y 5.0)", ")"],
    );
    assert_lines(
        "adv2_strict_nonbinding.smt2",
        &["sat", "(objectives", " (x 2.0)", ")"],
    );
    // Negative attained value formatting (COSMETIC: z3 prints `(- 2)`).
    assert_lines(
        "neg_attained.smt2",
        &["sat", "(objectives", " (x (- 2.0))", ")"],
    );
}

// --- Battery item 10: unbounded (`oo`) interplay ---

#[test]
#[timeout(60_000)]
fn g6_unbounded_with_strict_elsewhere_reports_oo() {
    // A strict bound elsewhere must not break the audited Unbounded path
    // (byte PARITY with z3's `oo` / `(* (- 1) oo)` shapes).
    assert_lines(
        "g6_unbounded_max_strict_elsewhere.smt2",
        &["sat", "(objectives", " (x oo)", ")"],
    );
    assert_lines(
        "g6b_unbounded_min_strict_elsewhere.smt2",
        &["sat", "(objectives", " (x (* (- 1) oo))", ")"],
    );
}

#[test]
#[timeout(60_000)]
fn adv8_infeasible_objectives_error_is_honest_deviation() {
    // DEVIATION (honest): after `unsat` z3 5.0.0 still prints
    // `(x (interval (* (- 1) oo) oo))` — an objectives "value" for an
    // infeasible problem. AY's pre-existing error is the honest answer and is
    // pinned here as a DOCUMENTED DEVIATION, not parity.
    assert_lines(
        "adv8_infeasible.smt2",
        &["unsat", "(error \"objectives are not available\")"],
    );
}

// --- get-value after an unattained optimum (m13) ---

#[test]
#[timeout(60_000)]
fn m13_getvalue_answers_with_feasible_value() {
    let lines = run_fixture("m13_getvalue_after.smt2");
    assert_eq!(lines[0], "sat");
    let value_line = &lines[1];
    assert!(
        value_line.starts_with("((x ") && !value_line.contains("error"),
        "get-value must answer after an unattained optimum: {value_line}"
    );
}
