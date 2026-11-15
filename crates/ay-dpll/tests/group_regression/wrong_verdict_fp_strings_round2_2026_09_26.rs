// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regressions from the fp-strings repair's round 2 (2026-09-26), corpus-free,
//! in both the default and the proof-free (`--z3-mode`) postures: the legal FP
//! formats the first D13 repair declined, and the regex x length pre-pass's
//! surrogate range end to end. The 2026-09-23 module
//! (`wrong_verdict_strings_fp_2026_09_23.rs`) holds the rest of D7, D8 and
//! D13.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// The conflict budget (`:rlimit`, [`Executor::set_resource_limit`]) every
/// file here must decide within: the bound the verdicts are held to, a count
/// host load cannot shorten. The need under it is not load-free: ay-sat
/// schedules its preprocessing and inprocessing by the wall clock by default,
/// so load changes the SAT trajectory. Measured 2026-09-30 at c57bd8481 and
/// 3332a4057 (the default posture's certificate re-solves the file twice more
/// under the same budget): unloaded, the `(4,12)` `fp.rem` file needs 275
/// conflicts and the `(3,8)` `fp.rem` file 293, in both postures, and every
/// file decides at 300; on loaded slow cores the `(4,12)` file needed 275,
/// 307 or 421 (a budget of 300 stops the last) and the `(3,8)` file 66 or
/// 293. 10,000 is 23x the heaviest need seen. A bit-blast solve gets no
/// default conflict budget: only an explicit `:rlimit` bounds it (#8749).
const CONFLICT_BUDGET: u64 = 10_000;

/// A wall-clock hang guard, never the bound a verdict is held to. The 20 s
/// wall it replaces was that bound: the `(4,12)` `fp.rem` file takes ~14 s
/// in the default posture unloaded (two thirds of it minting the UNSAT
/// certificate, most of that its two reconfirmation re-solves), 21 to 29 s
/// on two slow cores shared with two or three other solver processes and
/// 59 s on one, and under the 20 s wall it turned `unknown` (`Timeout`).
/// 200 s is three times the slowest of those runs.
const HANG_GUARD: Duration = Duration::from_secs(200);

/// The last verdict line of `script` under [`CONFLICT_BUDGET`], run in the
/// default posture or, with `proof_free`, in the proof-free (`--z3-mode`)
/// posture.
fn verdict(script: &str, proof_free: bool) -> String {
    verdict_within(script, proof_free, CONFLICT_BUDGET)
}

/// The last verdict line of `script` under a budget of `conflicts` and
/// [`HANG_GUARD`]. An `unknown` carries its reason, so a budget stop
/// (`ResourceLimit`), a hang (`Timeout`) and the first repair's encoding-gap
/// decline (`Incomplete`) read apart in a failed assertion.
fn verdict_within(script: &str, proof_free: bool, conflicts: u64) -> String {
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}\n{script}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(proof_free);
    exec.set_resource_limit(Some(conflicts));
    exec.set_timeout(Some(HANG_GUARD));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{script}"));
    let verdict = outputs
        .iter()
        .rev()
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_default();
    if verdict == "unknown" {
        return format!("unknown ({:?})", exec.unknown_reason());
    }
    verdict
}

/// D13, round 2: formats such as `(2,5)`, `(2,6)`, `(3,8)`, `(3,9)`,
/// `(4,12)` and `(4,17)` are legal SMT-LIB. The first repair declined them
/// (an encoding gap: `unknown`) wherever z3's narrow widths were not shown
/// exact, and lost 27 verdicts main gets right (the round-2 verifier's
/// generated files; each expected verdict below is exact: the symbolic
/// operand enumerated over every value of its format with the hunt's
/// `fpref.py`). The circuits now size themselves for every format
/// (`ay-fp`'s `exponent_widths.rs`), so each file decides, in both postures.
#[test]
#[timeout(480_000)]
fn d13_legal_formats_beyond_the_narrow_envelope_decide() {
    let cases = [
        // fp.sqrt: (3,8), (4,17), (3,10), and (3,8) under a symbolic mode.
        (
            "(declare-const x (_ FloatingPoint 3 8)) \
             (assert (= (fp.sqrt RNE x) (fp #b0 #b110 #b0111101)))",
            "unsat",
        ),
        (
            "(declare-const x (_ FloatingPoint 4 17)) \
             (assert (= (fp.sqrt RNE x) (fp #b1 #b0011 #b1000101101110101)))",
            "unsat",
        ),
        (
            "(declare-const x (_ FloatingPoint 3 10)) \
             (assert (= (fp.sqrt RTP x) (fp #b0 #b001 #b100001010)))",
            "sat",
        ),
        (
            "(declare-const x (_ FloatingPoint 3 8)) (declare-const r RoundingMode) \
             (assert (= (fp.sqrt r x) (fp #b0 #b100 #b1011000)))",
            "sat",
        ),
        // fp.rem: (3,8), (4,12), (2,5).
        (
            "(declare-const x (_ FloatingPoint 3 8)) \
             (assert (= (fp.rem (fp #b0 #b000 #b0011100) x) (fp #b1 #b110 #b0010000)))",
            "unsat",
        ),
        (
            "(declare-const x (_ FloatingPoint 4 12)) \
             (assert (= (fp.rem (fp #b1 #b0000 #b00000100100) x) (fp #b1 #b1010 #b01011000100)))",
            "unsat",
        ),
        (
            "(declare-const x (_ FloatingPoint 2 5)) \
             (assert (= (fp.rem (fp #b1 #b01 #b0010) x) (fp #b0 #b00 #b0001)))",
            "sat",
        ),
        // fp.div and fp.fma: (2,6), (2,5), (4,17).
        (
            "(declare-const x (_ FloatingPoint 2 6)) \
             (assert (= (fp.div RNE x (fp #b0 #b00 #b01100)) (fp #b0 #b01 #b11011)))",
            "sat",
        ),
        (
            "(declare-const x (_ FloatingPoint 2 5)) \
             (assert (= (fp.div RNA (fp #b1 #b10 #b1111) x) (fp #b0 #b00 #b1100)))",
            "unsat",
        ),
        (
            "(declare-const x (_ FloatingPoint 2 6)) \
             (assert (= (fp.fma RTN (fp #b1 #b10 #b11000) (fp #b1 #b10 #b00110) x) \
             (fp #b0 #b00 #b00111)))",
            "unsat",
        ),
        (
            "(declare-const x (_ FloatingPoint 4 17)) \
             (assert (= (fp.fma RTZ (fp #b1 #b0000 #b1011000000000110) x \
             (fp #b0 #b1000 #b1110111010011000)) (fp #b1 #b1011 #b0011010011100000)))",
            "unsat",
        ),
        // FP to FP from (3,8).
        (
            "(declare-const x (_ FloatingPoint 3 8)) \
             (assert (= ((_ to_fp 5 5) RTP x) (fp #b0 #b01110 #b1011)))",
            "sat",
        ),
        // fp.to_ubv of a (2,6) value: a function of (rm, x) (D7) in a format
        // whose subnormals the unpack's 2-bit count wrapped.
        (
            "(declare-const a (_ FloatingPoint 2 6)) (declare-const c (_ FloatingPoint 2 6)) \
             (assert (= a (fp #b0 #b10 #b11111))) (assert (= c a)) \
             (assert (distinct ((_ fp.to_ubv 3) RTZ a) ((_ fp.to_ubv 3) RTZ c)))",
            "unsat",
        ),
        (
            "(declare-const a (_ FloatingPoint 2 6)) (assert (= a (fp #b0 #b10 #b11111))) \
             (assert (distinct ((_ fp.to_ubv 3) RNE a) ((_ fp.to_ubv 3) RTZ a)))",
            "sat",
        ),
    ];
    for (body, expected) in cases {
        let script = format!("(set-logic ALL) {body} (check-sat)");
        for proof_free in [false, true] {
            assert_eq!(
                verdict(&script, proof_free),
                expected,
                "a legal FP format beyond z3's narrow widths decides (proof_free={proof_free}; \
                 main decides it, the first repair declined it)\n{script}"
            );
        }
    }
}

/// The twin of the test above: [`CONFLICT_BUDGET`] is the bound its verdicts
/// are held to, not the wall. Under 5 conflicts per FP solve, 55 times under
/// the least it was seen to need (275 unloaded, 275 to 421 loaded), the
/// `(4,12)` `fp.rem` file (the one the 20 s wall turned `unknown` under load)
/// stops on the budget in both postures, and a stop is `unknown`, never a
/// verdict. Should the FP solve stop honouring `:rlimit`, the verdicts above
/// would rest on the hang guard alone and this fails.
#[test]
#[timeout(240_000)]
fn d13_the_conflict_budget_binds_the_4_12_fp_rem_file() {
    let script = "(set-logic ALL) (declare-const x (_ FloatingPoint 4 12)) \
         (assert (= (fp.rem (fp #b1 #b0000 #b00000100100) x) (fp #b1 #b1010 #b01011000100))) \
         (check-sat)";
    for proof_free in [false, true] {
        assert_eq!(
            verdict_within(script, proof_free, 5),
            "unknown (Some(ResourceLimit))",
            "5 conflicts cannot refute this file (proof_free={proof_free}; it needs 275 to 421)"
        );
    }
}

/// D13, round 2's verifier: two widths no test held. Put back to its narrow
/// width, `fp.sqrt`'s rounded exponent (`W6b`) refuted the square root of a
/// `(2,17)` subnormal, and the FP-to-FP work width (`W10a`) refuted a
/// conversion of a tiny `(2,20)` or `(2,10)` value to a zero of a small
/// target: wrong `unsat`s in both postures on these satisfiable files (the
/// verifier's witnesses; each expectation exact: `sqrt(2^-9)` is 2896 units
/// of `2^-16` under RNE, `-2^-17` rounds to `-0` under RTP in `(2,5)` and
/// `2^-9` to `+0` under RNA in `(2,3)`).
#[test]
#[timeout(240_000)]
fn d13_round2_verifier_width_witnesses_are_sat() {
    let scripts = [
        "(declare-const x (_ FloatingPoint 2 17)) (assert (fp.isSubnormal x)) \
         (assert (= (fp.sqrt RNE x) (fp #b0 #b00 #b0000101101010000)))",
        "(declare-const x_m (_ BitVec 10)) \
         (define-fun x () (_ FloatingPoint 2 20) (fp #b1 #b00 (concat #b000000000 x_m))) \
         (assert (= ((_ to_fp 2 5) RTP x) (_ -zero 2 5))) (assert (= x_m #b0000000100))",
        "(declare-const x_m (_ BitVec 9)) \
         (define-fun x () (_ FloatingPoint 2 10) (fp #b0 #b00 x_m)) \
         (assert (= ((_ to_fp 2 3) RNA x) (_ +zero 2 3))) (assert (= x_m #b000000001))",
    ];
    for body in scripts {
        let script = format!("(set-logic ALL) {body} (check-sat)");
        for proof_free in [false, true] {
            assert_eq!(
                verdict(&script, proof_free),
                "sat",
                "a wrapped circuit width refutes a satisfiable file (proof_free={proof_free})\n\
                 {script}"
            );
        }
    }
}

/// D8's regex×length pre-pass end to end (the round-2 verifier's missing twin
/// for M12/M12b): a `re.range` whose low endpoint is a surrogate, under a
/// length window, with a word equation that sends the file to the QF_SLIA
/// pre-pass cascade. `regex_accepted_alphabet` must read the range by code
/// point: in `char` order the surrogate's carrier sorts above U+E001, the
/// range read as reversed, and its empty alphabet refuted the file.
#[test]
#[timeout(240_000)]
fn d8_regex_length_prepass_reads_a_surrogate_range_by_code_point() {
    let script = "(set-logic QF_SLIA) (declare-const x String) (declare-const y String) \
         (assert (str.in_re x (re.range \"\\u{dffe}\" \"\\u{e001}\"))) \
         (assert (= (str.len x) 1)) (assert (= y (str.++ x \"a\"))) \
         (assert (not (= x \"\\u{e000}\"))) (check-sat)";
    for proof_free in [false, true] {
        assert_eq!(
            verdict(script, proof_free),
            "sat",
            "x = U+DFFE, U+DFFF or U+E001 (proof_free={proof_free}; z3 5.1.0 sat; the \
             alphabet read in `char` order refutes it)\n{script}"
        );
    }
}
