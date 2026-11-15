// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn mask(width: u32) -> u128 {
    // The low `width` bits: 0 at width 0, all ones from width 128 up.
    u128::MAX
        .checked_shr(128_u32.saturating_sub(width))
        .unwrap_or(0)
}

fn reference(op: BvOp, value: u128, width: u32, amount: u128) -> u128 {
    match op {
        BvOp::Shl => {
            if amount >= u128::from(width) {
                0
            } else {
                (value << amount) & mask(width)
            }
        }
        BvOp::Lshr => {
            if amount >= u128::from(width) {
                0
            } else {
                value >> amount
            }
        }
        BvOp::Ashr => {
            let signed = ((value << (128 - width)) as i128) >> (128 - width);
            let shifted = if amount >= u128::from(width) {
                if signed < 0 {
                    -1
                } else {
                    0
                }
            } else {
                signed >> amount
            };
            shifted as u128 & mask(width)
        }
        _ => unreachable!(),
    }
}

fn expression(op: BvOp, width: u32, amount: u128) -> BvExpr {
    let input = BvExpr::leaf("value", width);
    let amount = BvExpr::const_val(amount, width);
    match op {
        BvOp::Shl => BvExpr::shl(input, amount),
        BvOp::Lshr => BvExpr::lshr(input, amount),
        BvOp::Ashr => BvExpr::ashr(input, amount),
        _ => unreachable!(),
    }
}

#[test]
fn literal_shift_wiring_matches_integer_oracle_at_every_internal_width() {
    for width in 1..=128 {
        for amount in [
            0,
            1,
            u128::from(width - 1),
            u128::from(width),
            u128::from(width + 1),
            mask(width),
        ] {
            if amount > mask(width) {
                continue;
            }
            for op in [BvOp::Shl, BvOp::Lshr, BvOp::Ashr] {
                let expr = expression(op, width, amount);
                let mut limits = BvExprProofLimits::conservative_external(
                    Instant::now() + Duration::from_secs(60),
                    1000,
                );
                // The leaf's inputs, the literal's two shared constants and
                // the shift's one shared zero (`topology_bound`).
                let estimate = width as usize + (width as usize).min(2) + 1;
                limits.max_estimated_gate_work = estimate;
                let mut census = BvExprPreflight::default();
                assert_eq!(
                    preflight_bv_expr_with_cancellation(
                        &expr,
                        &limits,
                        &mut census,
                        1,
                        &mut || true
                    ),
                    Ok(width)
                );
                assert_eq!(census.estimated_gate_work, estimate);
                let mut vars = VarTable::default();
                let mut gates = Vec::new();
                let mut clauses = Vec::new();
                let mut poll = || true;
                let bits = ExprBlaster::new(None, &mut poll)
                    .blast(&expr, &mut vars, &mut gates, &mut clauses)
                    .unwrap();
                assert!(
                    gates.len() <= 2,
                    "literal shifts require only constant gates"
                );
                for value in [
                    0,
                    1,
                    mask(width),
                    1_u128 << (width - 1),
                    0xaaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa_aaaa & mask(width),
                ] {
                    let mut valuation: Vec<bool> = vars
                        .roles
                        .iter()
                        .map(|role| match role {
                            VarRole::InputLeaf { leaf: 0, bit } => ((value >> bit) & 1) != 0,
                            _ => false,
                        })
                        .collect();
                    for gate in &gates {
                        valuation[gate.out as usize] = match gate.kind {
                            BitLemmaKind::ConstTrue => true,
                            BitLemmaKind::ConstFalse => false,
                            _ => panic!("unexpected nonconstant gate"),
                        };
                    }
                    let result = bits.iter().enumerate().fold(0_u128, |result, (bit, var)| {
                        result | (u128::from(valuation[*var as usize]) << bit)
                    });
                    assert_eq!(
                        result,
                        reference(op, value, width, amount),
                        "{op:?}, width={width}, value={value}, amount={amount}"
                    );
                }
            }
        }
    }
}

#[test]
fn literal_shift_keeps_malformed_operand_and_cancellation_refusals() {
    let expr = expression(BvOp::Shl, 3, 2);
    let mut polls = 0;
    let construct = |poll: &mut dyn FnMut() -> bool| {
        ExprBlaster::new(None, poll).blast(
            &expr,
            &mut VarTable::default(),
            &mut Vec::new(),
            &mut Vec::new(),
        )
    };
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
        expression(BvOp::Shl, 3, 8),
        BvExpr::lshr(BvExpr::const_val(8, 3), BvExpr::const_val(0, 3)),
    ] {
        assert!(matches!(
            ExprBlaster::new(None, &mut || true).blast(
                &malformed,
                &mut VarTable::default(),
                &mut Vec::new(),
                &mut Vec::new()
            ),
            Err(BvExprExportError::Malformed(_))
        ));
    }
}
