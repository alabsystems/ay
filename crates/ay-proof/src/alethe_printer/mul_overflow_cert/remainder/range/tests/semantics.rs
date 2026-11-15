// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Independent finite evaluator of the emitted invariant/circuit DAG.
/// It does not use the proof generator's local SAT or bit-vector evaluator.
fn evaluate(terms: &Terms, root: T, bindings: &[(T, u128)]) -> u128 {
    let mut values = Vec::new();
    for node in 0..=root {
        let args: Vec<_> = terms
            .args(node)
            .iter()
            .map(|&id| values[id as usize])
            .collect();
        let value = match terms.op(node) {
            Op::Var(_) => bindings.iter().find(|(id, _)| *id == node).unwrap().1,
            Op::True => 1,
            Op::False => 0,
            Op::Not => u128::from(args[0] == 0),
            Op::And => u128::from(args.iter().all(|&v| v != 0)),
            Op::Or => u128::from(args.iter().any(|&v| v != 0)),
            Op::Xor => args[0] ^ args[1],
            Op::Eq => u128::from(args[0] == args[1]),
            Op::Ite => {
                if args[0] != 0 {
                    args[1]
                } else {
                    args[2]
                }
            }
            Op::BbTerm => args
                .iter()
                .enumerate()
                .fold(0, |word, (i, bit)| word | (bit << i)),
            Op::Ult => u128::from(args[0] < args[1]),
            other => panic!("unexpected range circuit operation: {other:?}"),
        };
        values.push(value);
    }
    values[root as usize]
}

fn assign(bits: &[T], word: u128, bindings: &mut Vec<(T, u128)>) {
    bindings.extend(
        bits.iter()
            .enumerate()
            .map(|(i, &bit)| (bit, (word >> i) & 1)),
    );
}

#[test]
fn actual_range_invariant_holds_for_every_small_incoming_state() {
    let mut admitted = 0;
    let mut rejected = 0;
    for n in 1..=4 {
        // Construct the actual invariant and shared stage, without requiring a
        // proof to decide its truth table or relying on a hand-written theorem.
        let mut p = proof();
        let (r, x, y) = (
            free_bits(&mut p, "r", n),
            free_bits(&mut p, "x", n),
            free_bits(&mut p, "y", n),
        );
        let q = vec![p.t.ff; n as usize];
        let stage = clean::udiv_stage(&mut p.t, &x, &y, &q, &r);
        let shifted = super::super::shifted_x(&p, &x);
        let before = super::super::invariant(&mut p, &r, &shifted, &y);
        let after = super::super::invariant(&mut p, &stage.rem, &x, &y);
        for rv in 0..1u128 << n {
            for xv in 0..1u128 << n {
                for yv in 0..1u128 << n {
                    let mut bindings = Vec::new();
                    assign(&r, rv, &mut bindings);
                    assign(&x, xv, &mut bindings);
                    assign(&y, yv, &mut bindings);
                    let accepted = evaluate(&p.t, before, &bindings) != 0;
                    assert_eq!(accepted, rv < yv && rv <= xv >> 1);
                    if accepted {
                        admitted += 1;
                        assert_eq!(evaluate(&p.t, after, &bindings), 1);
                    } else {
                        rejected += 1;
                    }
                }
            }
        }
    }
    assert!(admitted > 100 && rejected > 100);
}

#[test]
fn projected_actual_divider_matches_total_smt_remainder_exhaustively() {
    for n in 1..=4 {
        let mut p = proof();
        let (x, y) = (free_bits(&mut p, "x", n), free_bits(&mut p, "y", n));
        let stages = super::super::specification::remainder_stages(&mut p, &x, &y).unwrap();
        let is_zero = {
            let equalities: Vec<_> = y.iter().map(|&bit| p.t.eq(bit, p.t.ff)).collect();
            p.t.and(&equalities)
        };
        let rem: Vec<_> = x
            .iter()
            .zip(&stages[0])
            .map(|(&input, &bit)| p.t.ite(is_zero, input, bit))
            .collect();
        let word = p.t.bb(&rem);
        for xv in 0..1u128 << n {
            for yv in 0..1u128 << n {
                let mut bindings = Vec::new();
                assign(&x, xv, &mut bindings);
                assign(&y, yv, &mut bindings);
                let expected = if yv == 0 { xv } else { xv % yv };
                assert_eq!(evaluate(&p.t, word, &bindings), expected, "{n}: {xv}%{yv}");
            }
        }
    }
}
