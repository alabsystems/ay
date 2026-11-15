// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wrong-verdict regressions from the 2026-09-23 strings/FP hunt (D7, D8 and
//! the strings panic), corpus-free, in both the default and the proof-free
//! (`--z3-mode`) postures.
//!
//! Every positive file here is satisfiable (z3 5.1.0 `sat`) and main
//! f399eca07a answered `unsat` for it in both postures:
//!
//! * **D8** — the SMT-LIB 2.6 string alphabet is every code point
//!   `0..=0x2FFFF`, the 2,048 surrogates `U+D800..=U+DFFF` INCLUDED. A Rust
//!   `char` cannot hold a surrogate, so `str.from_code` folded one to `""`, a
//!   range spanning the block lost 2,048 members, and a surrogate escape in a
//!   literal was a parse error. AY now stores a surrogate in a carrier `char`
//!   (`ay_core::smtlib_char`) and reads every code point back through
//!   `ay_core::smtlib_code_point`, so `str.<` and `re.range` keep code-point
//!   order although the carrier `char` sorts above `U+2FFFF`. The negative
//!   controls pin that order: a wrong direction must still be refuted.
//! * **D7** — `((_ fp.to_ubv m) rm x)` is unspecified off its domain but is a
//!   FUNCTION of `(rm, x)`; the bit-blaster keyed the unspecified value on `x`
//!   alone and forced `(RNE, x)` and `(RTZ, x)` equal. The same-mode control
//!   pins that congruence still holds.
//! * the strings panic — a `str` sliced at a byte offset inside a multi-byte
//!   character (`core/nf_equality.rs`), which degraded a satisfiable file to
//!   `unknown`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// The last verdict line of `script`, run in the default posture or, with
/// `proof_free`, in the proof-free (`--z3-mode`) posture.
fn verdict(script: &str, proof_free: bool) -> String {
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}\n{script}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(proof_free);
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{script}"));
    outputs
        .iter()
        .rev()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_default()
}

fn assert_both_postures(script: &str, expected: &str, why: &str) {
    for proof_free in [false, true] {
        let got = verdict(script, proof_free);
        assert_eq!(
            got, expected,
            "{why} (proof_free={proof_free}; main f399eca07a answered the opposite)\n{script}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn d8_str_from_code_of_a_surrogate_is_one_character() {
    assert_both_postures(
        "(set-logic ALL) (assert (= (str.len (str.from_code 55296)) 1)) (check-sat)",
        "sat",
        "U+D800 is an SMT-LIB character",
    );
    assert_both_postures(
        "(set-logic QF_SLIA) \
         (assert (= (str.to_code (str.from_code 55296)) 55296)) (check-sat)",
        "sat",
        "str.to_code inverts str.from_code on a surrogate",
    );
    assert_both_postures(
        "(set-logic QF_SLIA) \
         (assert (not (= (str.from_code 56000) (str.from_code 56001)))) (check-sat)",
        "sat",
        "two surrogates are two characters",
    );
}

#[test]
#[timeout(120_000)]
fn d8_str_lt_orders_surrogates_by_code_point() {
    assert_both_postures(
        "(set-logic QF_SLIA) \
         (assert (str.< (str.from_code 56000) (str.from_code 56001))) \
         (assert (str.< \"\\u{d7ff}\" (str.from_code 56000))) \
         (assert (str.< (str.from_code 56001) \"\\u{e000}\")) \
         (check-sat)",
        "sat",
        "U+D7FF < U+DAC0 < U+DAC1 < U+E000",
    );
    // Control: the carrier `char` of U+D800 sorts ABOVE U+E000; the code point
    // does not. A `char`-order comparison would answer `sat` here.
    assert_both_postures(
        "(set-logic QF_SLIA) \
         (assert (str.< \"\\u{e000}\" (str.from_code 55296))) (check-sat)",
        "unsat",
        "U+E000 is not below U+D800",
    );
}

#[test]
#[timeout(120_000)]
fn d8_re_range_spans_the_surrogate_block() {
    assert_both_postures(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (str.in_re x (re.diff (re.range \"\\u{d7ff}\" \"\\u{e000}\") \
             (re.union (str.to_re \"\\u{d7ff}\") (str.to_re \"\\u{e000}\"))))) \
         (check-sat)",
        "sat",
        "the range U+D7FF..U+E000 has 2,050 members",
    );
    // Control: a range INSIDE the block, bounded by carriers, excludes U+E000.
    assert_both_postures(
        "(set-logic QF_SLIA) \
         (assert (str.in_re \"\\u{e000}\" (re.range \"\\u{d800}\" \"\\u{dfff}\"))) \
         (check-sat)",
        "unsat",
        "U+E000 is outside U+D800..U+DFFF",
    );
}

#[test]
#[timeout(120_000)]
fn d8_surrogate_escape_is_one_character() {
    assert_both_postures(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (= x \"\\u{d800}\")) (assert (= (str.len x) 1)) \
         (assert (= (str.to_code x) 55296)) \
         (assert (= (str.to_code \"\\udfff\") 57343)) \
         (check-sat)",
        "sat",
        "a surrogate escape reads as one character with that code point",
    );
}

/// The satisfying models of these files give the two conversions DIFFERENT
/// unspecified values. The model now carries the value the solve chose for
/// each application, and both the model evaluator and the independent gate
/// read it back (the gate congruence-keyed on mode, width and argument), so
/// these are `sat` — as is the plainly satisfiable
/// `(= ((_ fp.to_ubv 3) RNE ((_ to_fp 3 4) RNE 12.0)) #b101)`, `unknown` on main.
#[test]
#[timeout(120_000)]
fn d7_to_ubv_unspecified_value_depends_on_the_rounding_mode() {
    // w10: 12.0 is out of range for 3 bits under every mode.
    assert_both_postures(
        "(set-logic ALL) \
         (assert (not (= ((_ fp.to_ubv 3) RNE ((_ to_fp 3 4) RNE 12.0)) \
                         ((_ fp.to_ubv 3) RTZ ((_ to_fp 3 4) RNE 12.0))))) \
         (check-sat)",
        "sat",
        "(RNE, 12.0) and (RTZ, 12.0) are different arguments",
    );
    // w11: NaN.
    assert_both_postures(
        "(set-logic ALL) (declare-const x (_ FloatingPoint 3 4)) \
         (assert (fp.isNaN x)) \
         (assert (not (= ((_ fp.to_ubv 3) RNE x) ((_ fp.to_ubv 3) RTZ x)))) \
         (check-sat)",
        "sat",
        "(RNE, NaN) and (RTZ, NaN) are different arguments",
    );
    // w12: signed.
    assert_both_postures(
        "(set-logic ALL) (declare-const x (_ FloatingPoint 3 4)) \
         (assert (= x ((_ to_fp 3 4) RNE 12.0))) \
         (assert (not (= ((_ fp.to_sbv 3) RNE x) ((_ fp.to_sbv 3) RTZ x)))) \
         (check-sat)",
        "sat",
        "fp.to_sbv is a function of (rm, x) too",
    );
    // g9_00071: through the RoundingMode expansion lane.
    assert_both_postures(
        "(set-logic ALL) \
         (declare-const x (_ FloatingPoint 4 4)) (declare-const y (_ FloatingPoint 4 4)) \
         (declare-const r1 RoundingMode) \
         (assert (= x (_ +oo 4 4))) (assert (= y (_ +oo 4 4))) \
         (assert (not (= ((_ fp.to_sbv 2) RTN x) ((_ fp.to_sbv 2) r1 y)))) \
         (check-sat)",
        "sat",
        "r1 = RNE gives a different argument pair",
    );
    // One unspecified conversion pinned to a value: main answered `unknown`.
    assert_both_postures(
        "(set-logic ALL) \
         (assert (= ((_ fp.to_ubv 3) RNE ((_ to_fp 3 4) RNE 12.0)) #b101)) \
         (assert (= ((_ fp.to_ubv 3) RTZ ((_ to_fp 3 4) RNE 12.0)) #b110)) \
         (check-sat)",
        "sat",
        "two different unspecified values at two different modes",
    );
}

#[test]
#[timeout(120_000)]
fn d7_to_ubv_stays_a_function_under_one_rounding_mode() {
    // Control: equal arguments, equal mode — congruence must still refute.
    assert_both_postures(
        "(set-logic ALL) \
         (declare-const x (_ FloatingPoint 3 4)) (declare-const y (_ FloatingPoint 3 4)) \
         (assert (= x ((_ to_fp 3 4) RNE 12.0))) (assert (= y x)) \
         (assert (not (= ((_ fp.to_ubv 3) RTZ x) ((_ fp.to_ubv 3) RTZ y)))) \
         (check-sat)",
        "unsat",
        "one function applied to equal arguments",
    );
    assert_both_postures(
        "(set-logic ALL) \
         (declare-const x (_ FloatingPoint 4 4)) (declare-const y (_ FloatingPoint 4 4)) \
         (declare-const r1 RoundingMode) \
         (assert (= x (_ +oo 4 4))) (assert (= y (_ +oo 4 4))) (assert (= r1 RTN)) \
         (assert (not (= ((_ fp.to_sbv 2) RTN x) ((_ fp.to_sbv 2) r1 y)))) \
         (check-sat)",
        "unsat",
        "r1 = RTN makes the two applications identical",
    );
    // Two NaN arguments are ONE argument (a sort has one NaN): the chosen
    // unspecified value is shared, so pinning it twice differently refutes.
    assert_both_postures(
        "(set-logic ALL) \
         (declare-const x (_ FloatingPoint 3 4)) (declare-const y (_ FloatingPoint 3 4)) \
         (assert (fp.isNaN x)) (assert (fp.isNaN y)) \
         (assert (= ((_ fp.to_ubv 3) RNE x) #b101)) \
         (assert (= ((_ fp.to_ubv 3) RNE y) #b110)) \
         (check-sat)",
        "unsat",
        "one function at one argument",
    );
}

#[test]
#[timeout(120_000)]
fn strings_nf_against_multibyte_constant_answers_instead_of_panicking() {
    // p01: `core/nf_equality.rs` sliced "00"-against-"...U+0663..." at a byte
    // offset inside U+0663; the caught panic degraded the file to `unknown`.
    let script = "(set-logic QF_SLIA) (declare-const x0 String) (declare-const x2 String) \
         (assert (= (str.len x0) 2)) (assert (= (str.len x2) 4)) \
         (assert (not (= (str.replace x0 \"\\u{663}\" x2) \"00\"))) (check-sat)";
    assert_both_postures(script, "sat", "x0 = \"ab\" satisfies it");
}

// ── Verifier witnesses for sites no test above reaches (2026-09-24 fix-up) ──
//
// The 2026-09-23 fp-strings verifier reverted each fix hunk one at a time; the
// sites below survived their revert with every test above green, and each
// revert gave a wrong `unsat` (or a panic) on the witness pinned here. The
// ay-strings, ay-fp and ay-dpll lib suites pin the same sites directly.

fn assert_never_refuted(script: &str, why: &str) {
    for proof_free in [false, true] {
        let got = verdict(script, proof_free);
        assert_ne!(
            got, "unsat",
            "{why} (proof_free={proof_free}; z3 5.1.0 answers sat)\n{script}"
        );
    }
}

#[test]
#[timeout(240_000)]
fn d8_code_point_order_witnesses_are_never_refuted() {
    // M24 (`WeRegex::range` compared its endpoints in `char` order, so a
    // range whose low endpoint is a surrogate read as EMPTY): vd8_25.
    assert_never_refuted(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (str.in_re x (re.inter (re.range \"\\u{d000}\" \"\\u{dbff}\") \
                                        (re.range \"\\u{d900}\" \"\\u{f000}\")))) \
         (assert (not (= x (str.from_code 55552)))) (check-sat)",
        "x = U+D901",
    );
    // M26 (no U+0000 outside representative when the greatest critical is
    // U+2FFFF, so the complement read as empty): m26_a.
    assert_never_refuted(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (str.in_re x (re.inter re.allchar (re.comp (re.range \"a\" \"\\u{2ffff}\"))))) \
         (check-sat)",
        "x = U+0000",
    );
    // M27 (criticals walked in `char` order put the U+DFFE carrier after
    // U+E000, and every representative fell inside the range): fd8_0258.
    assert_never_refuted(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (str.< x \"\\u{10000}\")) \
         (assert (str.in_re x (re.inter re.allchar (re.comp (re.range \"\\u{dffe}\" \"\\u{e000}\"))))) \
         (check-sat)",
        "x = \"a\"",
    );
    // M28 (the length set of a `re.range` straddling the block read as
    // empty under `char` order): wd8_16 and fd8_0012.
    assert_never_refuted(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (str.in_re x (re.range \"\\u{d800}\" \"\\u{10000}\"))) \
         (assert (> (str.to_code x) 60000)) (assert (< (str.to_code x) 60002)) (check-sat)",
        "x = U+EA61",
    );
    assert_never_refuted(
        "(set-logic QF_SLIA) (declare-const x String) (declare-const y String) \
         (assert (= (str.to_code y) 1)) (assert (str.prefixof \"\\u{1f600}\" x)) \
         (assert (str.in_re x (re.range \"\\u{d801}\" \"\\u{2ffff}\"))) (check-sat)",
        "x = U+1F600",
    );
}

#[test]
#[timeout(120_000)]
fn d7_mixed_formats_of_one_total_width_are_two_conversion_functions() {
    // M02: `(3,5)` and `(4,4)` are both 8 bits wide. Congruence keyed on the
    // total width compared the pair field by field and panicked on the
    // shorter exponent (caught: `unknown`); z3 5.1.0 answers sat (vd7_18).
    assert_both_postures(
        "(set-logic ALL) \
         (declare-const x (_ FloatingPoint 3 5)) (declare-const y (_ FloatingPoint 4 4)) \
         (assert (fp.isNaN x)) (assert (fp.isNaN y)) \
         (assert (distinct ((_ fp.to_ubv 3) RNE x) ((_ fp.to_ubv 3) RNE y))) \
         (check-sat)",
        "sat",
        "two sorts, two conversion functions",
    );
}

/// Every output line of `script` in the default posture.
fn outputs(script: &str) -> Vec<String> {
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}\n{script}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.set_memory_limit(Some(8 << 30));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{script}"))
}

#[test]
#[timeout(120_000)]
fn d8_get_value_orders_a_surrogate_by_code_point() {
    // M15: the model evaluator compared strings as UTF-8, under which the
    // U+D800 carrier sorts above U+E000 and U+FFFF — a wrong `get-value`.
    let out = outputs(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (= x (str.from_code 55296))) (check-sat) \
         (get-value ((str.< x \"\\u{e000}\") (str.<= \"\\u{e000}\" x) (str.< \"\\u{ffff}\" x)))",
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}");
    let values = out.get(1).cloned().unwrap_or_default();
    assert!(
        values.contains("((str.< x \"\\u{e000}\") true)")
            && values.contains("((str.<= \"\\u{e000}\" x) false)")
            && values.contains("((str.< \"\\u{ffff}\" x) false)"),
        "U+D800 < U+E000 <= U+FFFF by code point: {values}"
    );
}

#[test]
#[timeout(120_000)]
fn d8_to_code_of_a_surrogate_pins_the_character() {
    // A2 (`strings_lia.rs`): `str.to_code(x) = K` pins `x` to the one-character
    // string of K — a surrogate K too (M20 skipped it, a sound fall-through).
    assert_both_postures(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (= (str.to_code x) 55296)) (assert (not (= x \"\\u{d800}\"))) (check-sat)",
        "unsat",
        "to_code is injective on one-character strings",
    );
}

#[test]
fn d8_api_model_value_prints_a_surrogate_by_code_point() {
    // M32: the API `Display` of a string value printed each character's
    // `char` scalar, so the U+D800 carrier printed `\u{10d800}`.
    let carrier = |code: u32| ay_core::smtlib_char(code).expect("in the SMT-LIB alphabet");
    let value: String = [carrier(0xD800), '\u{e000}'].into_iter().collect();
    assert_eq!(
        ay_dpll::ModelValue::String(value).to_string(),
        r#""\u{d800}\u{e000}""#
    );
}

#[test]
#[timeout(120_000)]
fn e1_closed_sentence_over_a_trust_resolve_is_admitted_on_discharged_trust() {
    // The fix-up's audit of the verifier's E1: corpus AUFBVDTLIA
    // `BitsTricks.scala-7.smt2-3` in miniature. The one nested refutation the
    // closed-sentence theorem seals was accepted because its proof failed the
    // strict check only at a `trust` step; main published it as
    // `checked-exact-closed-sentence` ("an independently checked semantic
    // certificate").
    let script = "(set-logic ALL) \
         (declare-fun f ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32)) \
         (assert (forall ((x (_ BitVec 32)) (n (_ BitVec 32))) \
                  (= (f x n) (bvand x (bvshl (_ bv1 32) n))))) \
         (assert (not (forall ((n (_ BitVec 32)) (x (_ BitVec 32))) \
                  (or (not (bvslt n (_ bv32 32))) \
                      (not (= (f (bvor x (bvshl (_ bv1 32) n)) n) (_ bv0 32))) \
                      (bvslt n (_ bv0 32)))))) \
         (check-sat)";
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(20)));
    let out = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    assert_eq!(out, vec!["unsat"]);
    assert_ne!(
        exec.last_command_unsat_admission_tag(),
        Some("checked-exact-closed-sentence"),
        "a checked admission may not seal a refutation that rests on a trust step"
    );
    if let Some(census) = exec.last_semantic_token_census() {
        if census.kind == "closed-sentence" {
            assert_eq!(census.nested_trust_refuted, 1, "{census:?}");
            assert_eq!(
                exec.last_command_unsat_admission_tag(),
                Some("discharged-trust")
            );
        }
    }
}

#[test]
#[timeout(240_000)]
fn d8_regex_length_alphabet_spans_the_surrogate_block() {
    // A `re.range` spanning the surrogate block under a length window, end to
    // end. The site that reads such a range for the regex×length pre-pass,
    // `strings_regex_len.rs::regex_accepted_alphabet`, is pinned by its own lib
    // test (`accepted_alphabet_of_a_range_is_by_code_point`): these files are
    // decided before that pre-pass runs, so they do not reach it.
    assert_never_refuted(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (str.in_re x (re.range \"\\u{dffe}\" \"\\u{e001}\"))) \
         (assert (= (str.len x) 1)) \
         (assert (not (= x \"\\u{e000}\"))) (assert (not (= x \"\\u{e001}\"))) (check-sat)",
        "x = U+DFFE",
    );
    assert_never_refuted(
        "(set-logic QF_SLIA) (declare-const x String) \
         (assert (str.in_re x (re.range \"\\u{d800}\" \"\\u{e000}\"))) \
         (assert (= (str.len x) 1)) (assert (not (= x \"\\u{e000}\"))) (check-sat)",
        "x = U+D800",
    );
}

/// D13 (found by the fix-up's re-measurement): the FP circuits kept z3's
/// `eb + 2`-bit exponents in formats that need more, and main answered these
/// satisfiable files `unsat` in both postures (the exact reference, the hunt's
/// `fpref.py`, agrees with z3 5.1.0 on `sat`). `ay-fp`'s `tests_small_formats`
/// pins each circuit site.
#[test]
#[timeout(240_000)]
fn d13_small_format_witnesses_are_never_refuted() {
    // Fresh `g6_00041`: `fp.fma` in `(2,3)`; the alignment cap read as -7 and
    // the addend was never aligned. x0 = -2.0: -2 * 0.75 + 3 = 1.5 exactly.
    assert_both_postures(
        "(set-logic ALL) (declare-const x0 (_ FloatingPoint 2 3)) \
         (assert (= (fp.fma RTN x0 (fp #b0 #b00 #b11) (fp #b0 #b10 #b10)) (fp #b0 #b01 #b10))) \
         (check-sat)",
        "sat",
        "fp.fma aligns the addend in a two-bit exponent format",
    );
    // `fbvA`: a 24-bit integer's exponent `bv_sz - 2 = 22` wrapped in 4 bits,
    // and the conversion of 1 read as +0.
    assert_both_postures(
        "(set-logic QF_BVFP) (declare-const b (_ BitVec 24)) \
         (declare-const y (_ FloatingPoint 2 3)) (assert (= b #x000001)) \
         (assert (= y ((_ to_fp_unsigned 2 3) RNE b))) (assert (not (fp.isZero y))) \
         (check-sat)",
        "sat",
        "the integer conversion holds the integer's width",
    );
    // `sqrt38b`: `fp.sqrt` of the smallest `(3,8)` subnormal. Its `eb + 1`-bit
    // exponent wrapped there (main: a wrong `unsat`); `fp.sqrt` now holds it
    // in a width that fits (`sqrt_exponent_widths`).
    assert_both_postures(
        "(set-logic QF_FP) (declare-const x (_ FloatingPoint 3 8)) \
         (declare-const y (_ FloatingPoint 3 8)) (assert (= x (fp #b0 #b000 #b0000001))) \
         (assert (= y (fp.sqrt RTZ x))) (assert (= y (fp #b0 #b000 #b0010110))) (check-sat)",
        "sat",
        "y = sqrt(2^-9) toward zero = 22 * 2^-9",
    );
}
