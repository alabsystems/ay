// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The negative-literal shorthand inside a printed congruence.
//!
//! REGRESSION (measured 2026-10-02 with `--proof`, before and after
//! b02bbed887 alike): `(assert (= x -2))` beside `(assert (> y x))` and
//! `(assert (< y -3))` exits 1 with no verdict. Equality substitution prints
//! the congruence premise as the authored `-2` and the conclusion as the
//! canonical `(- 2)`, the surface congruence bridge had no step relating the
//! two spellings (`left="-2"; right="(- 2)"`), and the required UNSAT
//! publication failed (#8821). The authored order `(= -2 x)` failed the same
//! way one step later (`left="x"; right="(- 2)"`): its printed premise pairs
//! with the internal `(= x (- 2))` crosswise. A `forall` with `-1`/`-3` failed
//! on the shorthand and then on the instance's authored `(> x x)` beside the
//! canonical `(< x x)`.
//!
//! Each problem below now answers `unsat` with a document pinned Carcara
//! checks `valid`.
//!
//! SCOPE (z3 5.1.0 / 4.16, cvc5 1.4.1 and pinned Carcara agree, MEASURED
//! 2026-10-02): an UNQUOTED `-1` is the number even where `|-1|` is declared,
//! defined or bound; only the quoted `|-1|` is the symbol. AY used to read
//! the bare spelling as whatever symbol the scope held, which flipped
//! verdicts against z3 (p3/p7 `sat`, a01/a13/a15 `unsat`, a24 "requires
//! arguments"). Every problem here carries z3's verdict.

use super::{exact_carcara_verdict, parse, require_carcara_or_skip, CarcaraSurface, Executor};
use ntest::timeout;

/// The measured problems, each `unsat`.
const UNSAT_PROBLEMS: [(&str, &str); 9] = [
    (
        "equality",
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= x -2))
(assert (> y x))
(assert (< y -3))
(check-sat)
",
    ),
    (
        "reversed equality",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= -2 x))
(assert (> x 0))
(check-sat)
",
    ),
    (
        "reversed equality, shorthand bound",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= -2 x))
(assert (< x -5))
(check-sat)
",
    ),
    (
        "decimal equality",
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (= x -2.5))
(assert (> x 0.0))
(check-sat)
",
    ),
    (
        "decimal bounds",
        "(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (>= x -1.5))
(assert (<= (+ x y) -2.25))
(assert (>= y 0.5))
(check-sat)
",
    ),
    (
        "negative zero",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (> x -0))
(assert (< x 1))
(check-sat)
",
    ),
    (
        "quantified",
        "(set-logic LIA)
(declare-const x Int)
(assert (forall ((y Int)) (or (< y -3) (> y x))))
(assert (= x -1))
(check-sat)
",
    ),
    (
        "declared signed name beside the shorthand",
        "(set-logic QF_LIA)
(declare-const |-1| Int)
(declare-const x Int)
(assert (= |-1| -2))
(assert (> x |-1|))
(assert (< x -3))
(check-sat)
",
    ),
    (
        "declared signed name",
        "(set-logic QF_LIA)
(declare-const |-1| Int)
(declare-const x Int)
(assert (= |-1| 5))
(assert (= x (+ |-1| 1)))
(assert (< x 3))
(check-sat)
",
    ),
];

/// Probes whose unsat document must be hole-free and pinned-Carcara `valid`,
/// beyond the congruence family above: z3's scoping of the bare number, a
/// shorthand in a Real position, negative `evaluate` results, and the
/// arithmetic, comparison and equality respellings a congruence position
/// meets (`checker_identity`).
const SCOPED_UNSAT_PROBLEMS: [(&str, &str); 16] = [
    // Two assertions elaborate to one root with two spellings: either is a
    // premise, so the first is the `assume` (the surface used to be
    // withheld, and `--proof FILE` lost the verdict).
    (
        "g06: one root spelled (= x (- 2.5)) and (= x -2.5)",
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (= x (- 2.5)))
(assert (= x -2.5))
(assert (distinct x (- 2.5)))
(check-sat)
",
    ),
    (
        "p7: forall-bound |-3| beside the bare number",
        "(set-logic LIA)
(declare-const x Int)
(assert (forall ((|-3| Int)) (> (+ |-3| x) -3)))
(check-sat)
",
    ),
    (
        "a02: |-2| declared after the bare number is used",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x -2))
(declare-const |-2| Int)
(assert (= |-2| 5))
(assert (> x 0))
(check-sat)
",
    ),
    (
        "a03: |-2| defined after the bare number is used",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x -2))
(define-fun |-2| () Int 7)
(assert (> x 0))
(check-sat)
",
    ),
    (
        "a06: a binder named |-1| compared with the number",
        "(set-logic LIA)
(assert (forall ((|-1| Int)) (> |-1| -1)))
(check-sat)
",
    ),
    (
        "p5: a macro |-5| with parameters beside the number",
        "(set-logic QF_LIA)
(define-fun |-5| ((a Int)) Int a)
(declare-const x Int)
(assert (= x -5))
(assert (> x 0))
(check-sat)
",
    ),
    (
        "a10: the shorthand in a Real position",
        "(set-logic QF_LRA)
(declare-const x Real)
(assert (= x -2))
(assert (> x 0.0))
(check-sat)
",
    ),
    (
        "f07: forall instances whose evaluate results are negative",
        "(set-logic LIA)
(declare-const x Int)
(assert (forall ((y Int) (z Int)) (or (< y -3) (< z -4) (> (+ y z) x))))
(assert (= x -2))
(check-sat)
",
    ),
    (
        "f08: the same with explicit (- N)",
        "(set-logic LIA)
(declare-const x Int)
(assert (forall ((y Int) (z Int)) (or (< y (- 3)) (< z (- 4)) (> (+ y z) x))))
(assert (= x (- 2)))
(check-sat)
",
    ),
    (
        "a20: (* -1 y) beside the canonical (- y)",
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x -3) (* -1 y)))
(assert (= y -1))
(assert (< x 0))
(check-sat)
",
    ),
    (
        "b01: (* (- 1) y) beside the canonical (- y)",
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x (- 3)) (* (- 1) y)))
(assert (= y (- 1)))
(assert (< x 0))
(check-sat)
",
    ),
    (
        "g10: (- -2 -3) beside its constant",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (- -2 -3)))
(assert (< x 0))
(check-sat)
",
    ),
    (
        "d16: (abs -3) beside its constant",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (= x (abs -3)))
(assert (< x 3))
(check-sat)
",
    ),
    (
        "d02: (> -2 y) under forall beside the canonical (< y (- 2))",
        "(set-logic LIA)
(declare-const x Int)
(assert (forall ((y Int)) (or (> -2 y) (> y x))))
(assert (= x -1))
(check-sat)
",
    ),
    (
        "f01: (not (>= x -3)) beside the canonical (not (<= (- 3) x))",
        "(set-logic LIA)
(declare-const x Int)
(assert (forall ((y Int)) (or (< y -3) (not (>= x y)))))
(assert (= x -1))
(check-sat)
",
    ),
    (
        "d20: (= -2 x) inside an equality, beside (= x (- 2))",
        "(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (= -2 x) (= y -3)))
(assert (= x -2))
(assert (= y 0))
(check-sat)
",
    ),
];

/// z3 5.1.0 answers `sat`: the bare number is not the declared or bound
/// symbol of the same spelling.
const SAT_PROBLEMS: [(&str, &str); 3] = [
    (
        "a01: a declared |-2| and the bare number",
        "(set-logic QF_LIA)
(declare-const |-2| Int)
(declare-const x Int)
(assert (= |-2| 5))
(assert (= x -2))
(assert (< x 0))
(check-sat)
",
    ),
    (
        "a13: (- -2) beside a declared |-2|",
        "(set-logic QF_LIA)
(declare-const |-2| Int)
(declare-const x Int)
(assert (= |-2| 3))
(assert (= x (- -2)))
(assert (> x 0))
(check-sat)
",
    ),
    (
        "a15: a parameter named |-1| beside the bare number",
        "(set-logic QF_LIA)
(define-fun f ((|-1| Int)) Int (+ |-1| -1))
(assert (not (= (f 3) 6)))
(check-sat)
",
    ),
];

/// The verdict lines of one proof-producing session over `problem`.
fn run(label: &str, problem: &str) -> (Executor, Vec<String>) {
    let script = format!("(set-option :produce-proofs true)\n{problem}");
    let commands = parse(&script).unwrap_or_else(|e| panic!("{label}: {e}"));
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    (exec, outputs)
}

#[test]
#[timeout(120_000)]
fn the_negative_literal_shorthand_bridges_its_canonical_spelling_in_every_congruence() {
    let carcara = require_carcara_or_skip();
    for (label, problem) in UNSAT_PROBLEMS {
        let (exec, outputs) = run(label, problem);
        assert_eq!(outputs.last().map(String::as_str), Some("unsat"), "{label}");
        let (document, surface) = exec
            .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
            .unwrap_or_else(|| panic!("{label}: no retained proof"))
            .unwrap_or_else(|e| panic!("{label}: {e}"));
        assert!(
            !document.contains(":rule hole") && !document.contains(":rule trust"),
            "{label}: {document}"
        );
        assert_eq!(surface, CarcaraSurface::Supported, "{label}");
        if label.starts_with("declared") {
            assert!(document.contains("|-1|"), "{label}: {document}");
        }
        if let Some(carcara) = carcara.as_deref() {
            let (valid, why) = exact_carcara_verdict(carcara, problem, &document);
            assert!(valid, "{label}: {why}\n{document}");
        }
    }
}

/// One proof-producing session's `unsat` document: hole-free, Supported,
/// and `valid` to pinned Carcara when `CARCARA_PATH` names it.
fn assert_valid_unsat(carcara: Option<&std::path::Path>, label: &str, problem: &str) {
    let (exec, outputs) = run(label, problem);
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"), "{label}");
    let (document, surface) = exec
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .unwrap_or_else(|| panic!("{label}: no retained proof"))
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{label}: {document}"
    );
    assert_eq!(surface, CarcaraSurface::Supported, "{label}");
    if let Some(carcara) = carcara {
        let (valid, why) = exact_carcara_verdict(carcara, problem, &document);
        assert!(valid, "{label}: {why}\n{document}");
    }
}

#[test]
#[timeout(240_000)]
fn the_bare_number_is_never_a_symbol_and_every_respelling_is_checked() {
    let carcara = require_carcara_or_skip();
    for (label, problem) in SCOPED_UNSAT_PROBLEMS {
        assert_valid_unsat(carcara.as_deref(), label, problem);
    }
}

#[test]
#[timeout(60_000)]
fn a_symbol_named_like_the_number_does_not_capture_it() {
    for (label, problem) in SAT_PROBLEMS {
        let (_, outputs) = run(label, problem);
        assert_eq!(outputs.last().map(String::as_str), Some("sat"), "{label}");
    }
}

/// p3: z3 answers `unsat` (the bare `-1` is the number, not the let-bound
/// `|-1|`). AY decides it without proofs; with proofs its `let` assertion
/// has no authored `assume` spelling yet, so the proof session withholds the
/// verdict as `unknown` rather than publish a foreign `assume`.
#[test]
#[timeout(60_000)]
fn a_let_binder_named_like_the_number_does_not_capture_it() {
    let problem = "(set-logic QF_LIA)
(declare-const x Int)
(assert (let ((|-1| (+ x 1))) (and (> |-1| 4) (< x -1))))
(check-sat)
";
    let commands = parse(problem).expect("p3 parses");
    let outputs = Executor::new().execute_all(&commands).expect("p3 executes");
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
    let (_, outputs) = run("p3 with proofs", problem);
    assert!(
        matches!(
            outputs.last().map(String::as_str),
            Some("unsat" | "unknown")
        ),
        "{outputs:?}"
    );
}

/// a24: z3 answers `unsat`; AY used to refuse the bare `-1` as the function
/// `|-1|` applied to no arguments ("requires arguments").
#[test]
#[timeout(60_000)]
fn a_function_named_like_the_number_leaves_the_bare_number_a_number() {
    let (_, outputs) = run(
        "a24",
        "(set-logic QF_UFLIA)
(declare-fun |-1| (Int) Int)
(declare-const x Int)
(assert (= (|-1| x) -1))
(assert (= x -1))
(assert (= (|-1| -1) 2))
(check-sat)
",
    );
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
}

/// REGRESSION (measured 2026-10-09, pinned Carcara 1.1.0 git 9a352ee): a
/// numeral at a DECLARED function's `Real` parameter echoed as the `Int`
/// literal, `(assume t0 (> (f -2) 1.0))`, a hole-free document Carcara refuses
/// ("sort error: expected 'Real', got 'Int'"); the positive `(f 2)` the same
/// on main. Each `unsat` (z3 5.1.0) now prints `(f -2.0)` / `(f 2.0)`.
#[test]
#[timeout(120_000)]
fn a_numeral_at_a_real_parameter_is_spelled_real() {
    let carcara = require_carcara_or_skip();
    for (label, problem) in [
        (
            "x11: (f -2) at a Real parameter",
            "(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(assert (> (f -2) 1.0))
(assert (< (f -2) 0.0))
(check-sat)
",
        ),
        (
            "x10: (f 2) at a Real parameter",
            "(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(assert (> (f 2) 1.0))
(assert (< (f 2) 0.0))
(check-sat)
",
        ),
    ] {
        assert_valid_unsat(carcara.as_deref(), label, problem);
    }
}
