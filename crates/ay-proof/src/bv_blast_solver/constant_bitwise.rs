// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Select exact wires only from the blaster's already defined constant bits.

use super::*;

impl ExprBlaster<'_> {
    pub(super) fn constant_bitwise(&self, kind: BitLemmaKind, a: u32, b: u32) -> Option<u32> {
        for (bit, value) in [(self.zero_bit, false), (self.one_bit, true)] {
            let Some(bit) = bit else { continue };
            let other = if a == bit {
                b
            } else if b == bit {
                a
            } else {
                continue;
            };
            match (kind, value) {
                (BitLemmaKind::And2, false) | (BitLemmaKind::Or2, true) => return Some(bit),
                (BitLemmaKind::And2, true)
                | (BitLemmaKind::Or2, false)
                | (BitLemmaKind::Xor2, false) => return Some(other),
                _ => {}
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constant_bitwise_wires_match_integer_oracles_at_every_width() {
        for width in 1..=128 {
            let all = u128::MAX >> (128 - width);
            let values = [
                0,
                1,
                all,
                1 << (width - 1),
                0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa & all,
            ];
            for mask in values {
                for op in 0..6 {
                    let value = BvExpr::leaf("value", width);
                    let constant = BvExpr::const_val(mask, width);
                    let (a, b) = if op < 3 {
                        (value, constant)
                    } else {
                        (constant, value)
                    };
                    let expression = match op % 3 {
                        0 => BvExpr::and(a, b),
                        1 => BvExpr::or(a, b),
                        _ => BvExpr::xor(a, b),
                    };
                    let mut vars = VarTable::default();
                    let mut gates = Vec::new();
                    let bits = ExprBlaster::new(None, &mut || true)
                        .blast(&expression, &mut vars, &mut gates, &mut Vec::new())
                        .unwrap();
                    for input in values {
                        let mut valuation: Vec<bool> = vars
                            .roles
                            .iter()
                            .map(|role| match role {
                                VarRole::InputLeaf { leaf: 0, bit } => input & (1 << bit) != 0,
                                _ => false,
                            })
                            .collect();
                        for gate in &gates {
                            let args: Vec<_> =
                                gate.ins.iter().map(|&v| valuation[v as usize]).collect();
                            valuation[gate.out as usize] = match gate.kind {
                                BitLemmaKind::ConstFalse => false,
                                BitLemmaKind::ConstTrue => true,
                                BitLemmaKind::And2 => args[0] && args[1],
                                BitLemmaKind::Or2 => args[0] || args[1],
                                BitLemmaKind::Xor2 => args[0] ^ args[1],
                                _ => panic!("unexpected gate"),
                            };
                        }
                        let actual = bits.iter().enumerate().fold(0, |v, (i, &bit)| {
                            v | (u128::from(valuation[bit as usize]) << i)
                        });
                        let expected = match op % 3 {
                            0 => input & mask,
                            1 => input | mask,
                            _ => input ^ mask,
                        };
                        assert_eq!(
                            actual, expected,
                            "width {width}, op {op}, input {input}, mask {mask}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn constant_wiring_never_hides_malformed_operands_or_cancellation() {
        for malformed in [
            BvExpr::and(BvExpr::leaf("a", 8), BvExpr::const_val(0, 9)),
            BvExpr::and(BvExpr::const_val(256, 8), BvExpr::const_val(0, 8)),
            BvExpr::or(BvExpr::const_val(255, 8), BvExpr::leaf("a", 9)),
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
        let expression = BvExpr::and(BvExpr::leaf("a", 8), BvExpr::const_val(0, 8));
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
    }
}
