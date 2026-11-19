// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{QbfResult, QbfSolver};

fn verdict(input: &str) -> QbfResult {
    QbfSolver::new(parse_qcir(input).expect("valid QCIR")).solve_until(None)
}

#[test]
fn qcir_small_examples() {
    // ∀x ∃y. x xor y: true.
    let text = "#QCIR-G14\nforall(x)\nexists(y)\noutput(g)\ng = xor(x, y)\n";
    assert!(matches!(verdict(text), QbfResult::Sat(_)));
    // ∃y ∀x. x xor y: false.
    let text = "#QCIR-G14 2\nexists(y)\nforall(x)\noutput(g)\ng = xor(x, y)\n";
    assert!(matches!(verdict(text), QbfResult::Unsat(_)));
    // Negated output, comments, blank lines, numeric names.
    let text = "#QCIR-G14\n# comment\nforall(1)\n\noutput(-5)\n5 = and(1, -1)\n";
    assert!(matches!(verdict(text), QbfResult::Sat(_)));
    // Empty and/or are the constants true/false.
    let text = "#QCIR-G14\nexists(a)\noutput(t)\nt = and()\n";
    assert!(matches!(verdict(text), QbfResult::Sat(_)));
    let text = "#QCIR-G14\nexists(a)\noutput(f)\nf = or()\n";
    assert!(matches!(verdict(text), QbfResult::Unsat(_)));
    // Output is an input literal; the free block is outermost existential.
    let text = "#QCIR-G14\nfree(a)\nforall(b)\noutput(a)\n";
    assert!(matches!(verdict(text), QbfResult::Sat(_)));
    let text = "#QCIR-G14\nfree(c)\nforall(b)\noutput(g)\ng = ite(c, b, -b)\n";
    assert!(matches!(verdict(text), QbfResult::Unsat(_)));
}

#[test]
fn qcir_rejects_malformed_and_non_prenex_input() {
    assert_eq!(
        parse_qcir("p cnf 1 1\n1 0\n").unwrap_err(),
        QcirError::MissingHeader
    );
    assert!(matches!(
        parse_qcir("#QCIR-G14\nexists(x)\noutput(g)\ng = forall(y; x)\n").unwrap_err(),
        QcirError::Unsupported(4, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nexists(x)\noutput(g)\ng = xor(x)\n").unwrap_err(),
        QcirError::Syntax(4, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nexists(x)\noutput(g)\ng = and(x)\ng = or(x)\n").unwrap_err(),
        QcirError::Syntax(5, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nexists(x, x)\noutput(x)\n").unwrap_err(),
        QcirError::Syntax(2, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nexists(x)\n").unwrap_err(),
        QcirError::Syntax(0, _)
    ));
    // `free` is the outermost block and there is one: after a quantifier
    // block, or a second time, it is invalid, not an existential block there.
    assert!(matches!(
        parse_qcir("#QCIR-G14\nforall(x)\nfree(y)\noutput(g)\ng = xor(x, y)\n").unwrap_err(),
        QcirError::Syntax(3, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nfree(y)\nfree(z)\nforall(x)\noutput(g)\ng = and(x, y, z)\n")
            .unwrap_err(),
        QcirError::Syntax(3, _)
    ));
    // In its place it is the outermost existential block: exists y forall x
    // (x xor y) is false, where forall x exists y (x xor y) is true.
    let text = "#QCIR-G14\nfree(y)\nforall(x)\noutput(g)\ng = xor(x, y)\n";
    assert!(matches!(verdict(text), QbfResult::Unsat(_)));
    // A gate that names itself is not a circuit.
    assert!(matches!(
        parse_qcir("#QCIR-G14\nforall(x)\noutput(g)\ng = and(g, x)\n").unwrap_err(),
        QcirError::Syntax(4, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nforall(x)\noutput(g)\ng = or(x, - g)\n").unwrap_err(),
        QcirError::Syntax(4, _)
    ));
    // Names neither declared nor defined earlier: a misspelled input, a
    // forward reference to a later gate, and an undefined output.
    assert!(matches!(
        parse_qcir("#QCIR-G14\nforall(x)\noutput(g)\ng = and(x, y)\n").unwrap_err(),
        QcirError::Syntax(4, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nexists(x)\noutput(g)\ng = and(x, h)\nh = or(x)\n").unwrap_err(),
        QcirError::Syntax(4, _)
    ));
    assert!(matches!(
        parse_qcir("#QCIR-G14\nexists(x)\noutput(h)\ng = and(x)\n").unwrap_err(),
        QcirError::Syntax(3, _)
    ));
    assert!(is_qcir("  #QCIR-G14\n"));
    assert!(!is_qcir("c x\np cnf 1 1\n"));
}

#[test]
fn qcir_only_encodes_the_output_cone() {
    let text = "#QCIR-G14\nexists(a, b)\noutput(g1)\ng1 = and(a, b)\ng2 = or(a, b)\n\
                g3 = xor(g2, a)\n";
    let formula = parse_qcir(text).unwrap();
    // a, b and g1 only.
    assert_eq!(formula.num_vars(), 3);
}

struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % n
    }
}

#[derive(Clone)]
enum TestGate {
    And(Vec<i64>),
    Or(Vec<i64>),
    Xor(i64, i64),
    Ite(i64, i64, i64),
}

/// Value of a signed node reference (inputs are nodes `1..=n`, gates follow).
fn value(reference: i64, inputs: &[bool], gates: &[TestGate]) -> bool {
    let index = reference.unsigned_abs() as usize - 1;
    let v = if index < inputs.len() {
        inputs[index]
    } else {
        match &gates[index - inputs.len()] {
            TestGate::And(ops) => ops.iter().all(|&o| value(o, inputs, gates)),
            TestGate::Or(ops) => ops.iter().any(|&o| value(o, inputs, gates)),
            TestGate::Xor(a, b) => value(*a, inputs, gates) != value(*b, inputs, gates),
            TestGate::Ite(c, t, e) => {
                if value(*c, inputs, gates) {
                    value(*t, inputs, gates)
                } else {
                    value(*e, inputs, gates)
                }
            }
        }
    };
    if reference > 0 {
        v
    } else {
        !v
    }
}

/// Brute-force QBF value; inputs are quantified in index order.
fn game(
    var: usize,
    exists: &[bool],
    inputs: &mut Vec<bool>,
    output: i64,
    gates: &[TestGate],
) -> bool {
    if var == exists.len() {
        return value(output, inputs, gates);
    }
    let mut results = [false; 2];
    for (slot, bit) in [false, true].into_iter().enumerate() {
        inputs[var] = bit;
        results[slot] = game(var + 1, exists, inputs, output, gates);
    }
    if exists[var] {
        results[0] || results[1]
    } else {
        results[0] && results[1]
    }
}

#[test]
fn qcir_matches_brute_force_on_random_circuits() {
    let mut rng = Lcg(0x0c1c_2026_1118);
    let mut seen = [0usize; 2];
    for round in 0..3000 {
        let n = 1 + rng.below(6) as usize;
        let exists: Vec<bool> = (0..n).map(|_| rng.below(2) == 0).collect();
        let num_gates = 1 + rng.below(8) as usize;
        let mut gates = Vec::new();
        for g in 0..num_gates {
            let pool = (n + g) as u64;
            let operand = |rng: &mut Lcg| {
                let r = 1 + rng.below(pool) as i64;
                if rng.below(2) == 0 {
                    r
                } else {
                    -r
                }
            };
            let gate = match rng.below(4) {
                0 => TestGate::And((0..rng.below(4)).map(|_| operand(&mut rng)).collect()),
                1 => TestGate::Or((0..rng.below(4)).map(|_| operand(&mut rng)).collect()),
                2 => TestGate::Xor(operand(&mut rng), operand(&mut rng)),
                _ => TestGate::Ite(operand(&mut rng), operand(&mut rng), operand(&mut rng)),
            };
            gates.push(gate);
        }
        let last = (n + num_gates) as i64;
        let output = if rng.below(2) == 0 { last } else { -last };

        // Render as QCIR with one quantifier line per input (a first
        // existential input is sometimes declared in a `free` block).
        let name = |r: i64| {
            let index = r.unsigned_abs() as usize - 1;
            let base = if index < n {
                format!("v{index}")
            } else {
                format!("g{}", index - n)
            };
            if r > 0 {
                base
            } else {
                format!("-{base}")
            }
        };
        let join = |ops: &[i64]| ops.iter().map(|&o| name(o)).collect::<Vec<_>>().join(", ");
        let mut text = String::from("#QCIR-G14\n");
        let leave_free = exists[0] && round % 2 == 0;
        for (i, &e) in exists.iter().enumerate() {
            let head = if i == 0 && leave_free {
                "free"
            } else if e {
                "exists"
            } else {
                "forall"
            };
            text.push_str(&format!("{head}(v{i})\n"));
        }
        text.push_str(&format!("output({})\n", name(output)));
        for (g, gate) in gates.iter().enumerate() {
            let body = match gate {
                TestGate::And(ops) => format!("and({})", join(ops)),
                TestGate::Or(ops) => format!("or({})", join(ops)),
                TestGate::Xor(a, b) => format!("xor({}, {})", name(*a), name(*b)),
                TestGate::Ite(c, t, e) => {
                    format!("ite({}, {}, {})", name(*c), name(*t), name(*e))
                }
            };
            text.push_str(&format!("g{g} = {body}\n"));
        }
        // A free first input must actually occur to be quantified at all;
        // if it does not, its quantifier is irrelevant to the value.
        let expected = game(0, &exists, &mut vec![false; n], output, &gates);
        let formula = parse_qcir(&text).unwrap_or_else(|e| panic!("{e}\n{text}"));
        let fast = QbfSolver::new(formula.clone()).solve_until(None);
        let exact = QbfSolver::new(formula).solve();
        for result in [&fast, &exact] {
            assert!(
                matches!(
                    (expected, result),
                    (true, QbfResult::Sat(_)) | (false, QbfResult::Unsat(_))
                ),
                "round {round}: expected {expected}, got {result:?}\n{text}"
            );
        }
        seen[usize::from(!expected)] += 1;
    }
    assert!(
        seen[0] >= 500 && seen[1] >= 500,
        "polarity coverage: {seen:?}"
    );
}
