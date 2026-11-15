// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn widening_both_product_operands_preserves_exact_low_bit_wires() {
    for width in 1..=64 {
        for signed in [false, true] {
            let a = BvExpr::leaf("a", width);
            let b = BvExpr::leaf("b", width);
            let small = BvExpr::mul(a.clone(), b.clone());
            let extend = |v| {
                if signed {
                    BvExpr::sign_ext(v, width)
                } else {
                    BvExpr::zero_ext(v, width)
                }
            };
            let wide = BvExpr::mul(extend(a), extend(b));
            let mut vars = VarTable::default();
            let mut gates = Vec::new();
            let mut clauses = Vec::new();
            let mut poll = || true;
            let mut blaster = ExprBlaster::new(None, &mut poll);
            let low = blaster
                .blast(&small, &mut vars, &mut gates, &mut clauses)
                .unwrap();
            let whole = blaster
                .blast(&wide, &mut vars, &mut gates, &mut clauses)
                .unwrap();
            assert_eq!(
                low.as_slice(),
                &whole[..width as usize],
                "width {width}, signed {signed}"
            );
        }
    }
}

#[test]
fn truncated_product_matches_integer_multiplication_through_128_bits() {
    for width in [1, 2, 3, 4, 8, 16, 32, 64, 128] {
        let mask = u128::MAX >> (128 - width);
        let values: Vec<u128> = if width <= 4 {
            (0..=mask).collect()
        } else {
            vec![
                0,
                1,
                mask,
                1 << (width - 1),
                0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa & mask,
            ]
        };
        let expression = BvExpr::mul(BvExpr::leaf("a", width), BvExpr::leaf("b", width));
        let mut vars = VarTable::default();
        let mut gates = Vec::new();
        let output = ExprBlaster::new(None, &mut || true)
            .blast(&expression, &mut vars, &mut gates, &mut Vec::new())
            .unwrap();
        for &a in &values {
            for &b in &values {
                let mut valuation: Vec<bool> = vars
                    .roles
                    .iter()
                    .map(|role| match role {
                        VarRole::InputLeaf { leaf: 0, bit } => a & (1 << bit) != 0,
                        VarRole::InputLeaf { leaf: 1, bit } => b & (1 << bit) != 0,
                        _ => false,
                    })
                    .collect();
                for gate in &gates {
                    let input = |i: usize| valuation[gate.ins[i] as usize];
                    let value = match gate.kind {
                        BitLemmaKind::ConstFalse => false,
                        BitLemmaKind::ConstTrue => true,
                        BitLemmaKind::And2 => input(0) && input(1),
                        BitLemmaKind::Xor3 => input(0) ^ input(1) ^ input(2),
                        BitLemmaKind::FullAdderCarry => {
                            (input(0) && input(1)) || (input(2) && (input(0) ^ input(1)))
                        }
                        _ => panic!("unexpected product gate"),
                    };
                    valuation[gate.out as usize] = value;
                }
                let actual = output.iter().enumerate().fold(0, |v, (i, &bit)| {
                    v | (u128::from(valuation[bit as usize]) << i)
                });
                assert_eq!(
                    actual,
                    a.wrapping_mul(b) & mask,
                    "width {width}, a {a}, b {b}"
                );
            }
        }
    }
}
