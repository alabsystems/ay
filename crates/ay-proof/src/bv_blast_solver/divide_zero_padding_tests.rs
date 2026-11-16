// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Mathematical values, emitted CNF, literal sharing and original controls.

use super::super::*;

fn mask(width: u32) -> u128 {
    u128::MAX >> (128 - width)
}

fn evaluate(
    vars: &VarTable,
    gates: &[BitLemma],
    clauses: &[Clause],
    a: u128,
    b: u128,
) -> Vec<bool> {
    let mut values = vars
        .roles
        .iter()
        .map(|role| match role {
            VarRole::InputLeaf { leaf: 0, bit } => a & (1u128 << bit) != 0,
            VarRole::InputLeaf { leaf: 1, bit } => b & (1u128 << bit) != 0,
            VarRole::InputLeaf { .. } => panic!("unexpected input leaf"),
            _ => false,
        })
        .collect::<Vec<_>>();
    for gate in gates {
        let args = gate
            .ins
            .iter()
            .map(|&bit| values[bit as usize])
            .collect::<Vec<_>>();
        values[gate.out as usize] = match gate.kind {
            BitLemmaKind::ConstFalse => false,
            BitLemmaKind::ConstTrue => true,
            BitLemmaKind::Not => !args[0],
            BitLemmaKind::And2 => args[0] && args[1],
            BitLemmaKind::Or2 => args[0] || args[1],
            BitLemmaKind::Xor3 => args[0] ^ args[1] ^ args[2],
            BitLemmaKind::FullAdderCarry => args.iter().filter(|&&arg| arg).count() >= 2,
            _ => panic!("unexpected divider gate"),
        };
    }
    for clause in clauses {
        assert!(
            clause
                .lits
                .iter()
                .any(|literal| values[literal.var as usize] != literal.neg),
            "emitted clause {} disagrees with gate evaluation",
            clause.id
        );
    }
    values
}

fn word(bits: &[u32], values: &[bool]) -> u128 {
    bits.iter().enumerate().fold(0, |value, (index, &bit)| {
        value | (u128::from(values[bit as usize]) << index)
    })
}

#[test]
fn mixed_zero_padded_division_and_remainder_match_math_including_original_width_zero() {
    for outer in [4, 8, 32, 64, 128] {
        for left_width in 1..=4 {
            for right_width in 1..=4 {
                for masked in [false, true] {
                    let input = |name, width| {
                        if masked {
                            BvExpr::and(
                                BvExpr::leaf(name, outer),
                                BvExpr::const_val(mask(width), outer),
                            )
                        } else {
                            BvExpr::zero_ext(BvExpr::leaf(name, width), outer - width)
                        }
                    };
                    let left = input("a", left_width);
                    let right = input("b", right_width);
                    let mut vars = VarTable::default();
                    let mut gates = Vec::new();
                    let mut clauses = Vec::new();
                    let mut poll = || true;
                    let mut blaster = ExprBlaster::new(None, &mut poll);
                    let (quotient, remainder) = blaster
                        .blast_division(&left, &right, &mut vars, &mut gates, &mut clauses)
                        .unwrap();
                    assert_eq!(
                        (quotient.len(), remainder.len()),
                        (outer as usize, outer as usize)
                    );
                    assert!(gates.len() <= topology_bound::divide(outer as usize) + 2);
                    for a in 0..=mask(left_width) {
                        for b in 0..=mask(right_width) {
                            let input_a = if masked {
                                a | ((mask(outer) ^ mask(left_width))
                                    & 0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaau128)
                            } else {
                                a
                            };
                            let input_b = if masked {
                                b | ((mask(outer) ^ mask(right_width))
                                    & 0x5555_5555_5555_5555_5555_5555_5555_5555u128)
                            } else {
                                b
                            };
                            let values = evaluate(&vars, &gates, &clauses, input_a, input_b);
                            let expected = (
                                a.checked_div(b).unwrap_or_else(|| mask(outer)),
                                a.checked_rem(b).unwrap_or(a),
                            );
                            assert_eq!((word(&quotient, &values), word(&remainder, &values)), expected,
                                "outer{outer}, payload{left_width}/{right_width}, masked{masked}, {a}/{b}");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn the_low_quotient_is_the_same_literal_vector_in_both_construction_orders() {
    for wide_first in [false, true] {
        let a = BvExpr::leaf("a", 8);
        let b = BvExpr::leaf("b", 8);
        let narrow = BvExpr::udiv(a.clone(), b.clone());
        let wide = BvExpr::udiv(BvExpr::zero_ext(a, 24), BvExpr::zero_ext(b, 24));
        let mut vars = VarTable::default();
        let mut gates = Vec::new();
        let mut clauses = Vec::new();
        let mut poll = || true;
        let mut blaster = ExprBlaster::new(None, &mut poll);
        let mut blast = |expression| {
            blaster
                .blast(expression, &mut vars, &mut gates, &mut clauses)
                .unwrap()
        };
        let (q8, q32) = if wide_first {
            let q32 = blast(&wide);
            (blast(&narrow), q32)
        } else {
            let q8 = blast(&narrow);
            (q8, blast(&wide))
        };
        assert_eq!(&q32[..8], q8.as_slice());
        assert!(q32[8..].iter().all(|bit| *bit == q32[8]));
        for (a, b) in [(0, 0), (1, 0), (255, 0), (255, 3), (17, 7)] {
            let values = evaluate(&vars, &gates, &clauses, a, b);
            assert_eq!(word(&q8, &values), a.checked_div(b).unwrap_or(255));
            assert_eq!(
                word(&q32, &values),
                a.checked_div(b).unwrap_or_else(|| u128::from(u32::MAX))
            );
        }
    }
}

#[test]
fn trimmed_construction_keeps_original_cancellation_and_malformed_operand_refusals() {
    let expression = BvExpr::udiv(
        BvExpr::zero_ext(BvExpr::leaf("a", 3), 29),
        BvExpr::zero_ext(BvExpr::leaf("b", 3), 29),
    );
    let construct = |poll: &mut dyn FnMut() -> bool| {
        ExprBlaster::new(None, poll).blast(
            &expression,
            &mut VarTable::default(),
            &mut Vec::new(),
            &mut Vec::new(),
        )
    };
    let mut polls = 0;
    construct(&mut || {
        polls += 1;
        true
    })
    .unwrap();
    for stop in 1..=polls {
        let mut calls = 0;
        assert_eq!(
            construct(&mut || {
                calls += 1;
                calls != stop
            }),
            Err(BvExprExportError::Cancelled)
        );
        assert_eq!(calls, stop);
    }
    for malformed in [
        BvExpr::udiv(BvExpr::leaf("a", 8), BvExpr::leaf("b", 9)),
        BvExpr::urem(BvExpr::const_val(256, 8), BvExpr::const_val(0, 8)),
    ] {
        assert!(ExprBlaster::new(None, &mut || true)
            .blast(
                &malformed,
                &mut VarTable::default(),
                &mut Vec::new(),
                &mut Vec::new()
            )
            .is_err());
    }
}

#[test]
fn guarded_width_identity_has_a_replayed_proof_and_unguarded_or_wrong_values_do_not() {
    let a = BvExpr::leaf("a", 8);
    let b = BvExpr::leaf("b", 8);
    let narrow = BvExpr::zero_ext(BvExpr::udiv(a.clone(), b.clone()), 24);
    let wide = BvExpr::udiv(BvExpr::zero_ext(a, 24), BvExpr::zero_ext(b.clone(), 24));
    let guard = BvExpr::eq(b, BvExpr::const_val(0, 8));
    let claim = BvExpr::or(guard.clone(), BvExpr::eq(narrow.clone(), wide.clone()));
    let limits =
        BvExprProofLimits::conservative_external(Instant::now() + Duration::from_secs(10), 1_000);
    let proof = export_bv_blast_proof_expr_with_limits(&claim, &BvExpr::const_val(1, 1), &limits)
        .expect("strict solver-derived proof of the guarded width relation");
    proof
        .validate()
        .expect("independent gate and resolution replay");
    for false_claim in [
        BvExpr::eq(narrow.clone(), wide.clone()),
        BvExpr::or(
            guard,
            BvExpr::eq(BvExpr::add(narrow, BvExpr::const_val(1, 32)), wide),
        ),
    ] {
        let limits = BvExprProofLimits::conservative_external(
            Instant::now() + Duration::from_secs(10),
            1_000,
        );
        assert!(matches!(
            export_bv_blast_proof_expr_with_limits(&false_claim, &BvExpr::const_val(1, 1), &limits),
            Err(BvExprExportError::NoRefutation)
        ));
    }
}
