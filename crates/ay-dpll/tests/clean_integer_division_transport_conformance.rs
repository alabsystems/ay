// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clean's guarded integer expressions must retain checked parsed refutations.

use ay_dpll::Executor;
use ay_frontend::parse;

fn integer(value: i128) -> String {
    if value < 0 {
        format!("(- {})", -value)
    } else {
        value.to_string()
    }
}

// Preserve the guards emitted by Clean. Reducing them in the fixture would
// hide the missing division support in exact-source proof authentication.
fn operation(head: &str, divisor: i128) -> String {
    let rhs = integer(divisor);
    let magnitude = format!("(div (ite (< x 0) (- x) x) (ite (< {rhs} 0) (- {rhs}) {rhs}))");
    let quotient = format!(
        "(ite (= {rhs} 0) 0 \
          (ite (< x 0) \
            (ite (< {rhs} 0) {magnitude} (- {magnitude})) \
            (ite (< {rhs} 0) (- {magnitude}) {magnitude})))"
    );
    match head {
        "Int.div" => quotient,
        "Int.mod" => format!("(- x (* {rhs} {quotient}))"),
        "Int.ediv" => format!("(ite (= {rhs} 0) 0 (div x {rhs}))"),
        "Int.emod" => format!("(ite (= {rhs} 0) x (mod x {rhs}))"),
        _ => panic!("unknown fixture head {head}"),
    }
}

fn check(dividend: i128, claim: &str, expected: &str) {
    let dividend = integer(dividend);
    let source = format!(
        "(set-logic QF_LIA)\n\
         (set-option :timeout 5000)\n\
         (declare-const x Int)\n\
         (assert (= x {dividend}))\n\
         (assert {claim})\n\
         (check-sat)\n"
    );
    check_source(&source, expected);
}

fn check_source(source: &str, expected: &str) {
    let mut executor = Executor::new();
    // Exactly the proof-producing Executor configuration Clean uses.
    executor.set_produce_proofs(true);
    let commands = parse(source).expect("Clean's SMT expression parses");
    let mut output = Vec::new();
    for command in &commands {
        if let Some(line) = executor.execute(command).expect("command executes") {
            output.push(line);
        }
    }
    assert_eq!(
        output,
        [expected],
        "reason={:?}; detail={:?}; source={source}",
        executor.unknown_reason(),
        executor.unknown_detail(),
    );
    if expected == "unsat" {
        let proof = executor
            .last_proof()
            .expect("requested refutation retained");
        let quality = ay_proof::check_proof_strict(proof, executor.terms())
            .expect("the refutation passes strict checking");
        assert!(quality.is_complete(), "{quality}");
        assert_eq!(quality.trust_count, 0);
        assert_eq!(quality.hole_count, 0);
    }
}

#[test]
fn parsed_clean_integer_division_has_checked_refutations_and_sat_controls() {
    let min = i128::from(i64::MIN);
    for (head, dividend, divisor, expected) in [
        ("Int.div", -7, 2, -3),
        ("Int.ediv", -7, 2, -4),
        ("Int.div", -7, -2, 3),
        ("Int.ediv", -7, -2, 4),
        ("Int.div", 7, -2, -3),
        ("Int.ediv", 7, -2, -3),
        ("Int.mod", -7, 2, -1),
        ("Int.emod", -7, 2, 1),
        ("Int.mod", -7, -2, -1),
        ("Int.emod", -7, -2, 1),
        ("Int.div", -7, 0, 0),
        ("Int.ediv", -7, 0, 0),
        ("Int.mod", -7, 0, -7),
        ("Int.emod", -7, 0, -7),
        ("Int.div", min, -1, -min),
        ("Int.ediv", min, -1, -min),
        ("Int.mod", min, 0, min),
        ("Int.emod", min, 0, min),
    ] {
        let operation = operation(head, divisor);
        for (claimed, negate, verdict) in [
            (expected, false, "sat"),
            (expected, true, "unsat"),
            (expected + 1, false, "unsat"),
        ] {
            let equality = format!("(= {operation} {})", integer(claimed));
            let claim = if negate {
                format!("(not {equality})")
            } else {
                equality
            };
            check(dividend, &claim, verdict);
        }
    }
}

#[test]
fn parsed_integer_and_real_negative_zero_preserve_authored_proof_roots() {
    for (logic, zero) in [("QF_LIA", "0"), ("QF_LRA", "0.0")] {
        for (negate, expected) in [(false, "sat"), (true, "unsat")] {
            let equality = format!("(= (- {zero}) {zero})");
            let claim = if negate {
                format!("(not {equality})")
            } else {
                equality
            };
            let source = format!("(set-logic {logic})\n(assert {claim})\n(check-sat)\n");
            check_source(&source, expected);
        }
    }
}
