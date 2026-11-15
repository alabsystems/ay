// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Minimum-format `(2,2)` circuit results against the independent
//! Fraction-based `fpref.py` oracle: a few named cases, then every input of
//! every arithmetic circuit (the source hash is in the text fixture).

use super::{expect, run, Bits, RoundingMode};

const MODES: [RoundingMode; 5] = [
    RoundingMode::RNE,
    RoundingMode::RNA,
    RoundingMode::RTP,
    RoundingMode::RTN,
    RoundingMode::RTZ,
];

fn bits(raw: u8) -> Bits {
    ((raw >> 3) as u64, ((raw >> 1) & 3) as u64, (raw & 1) as u64)
}

fn check_case(expected: &mut impl Iterator<Item = u8>, op: &str, mode: RoundingMode, input: &[u8]) {
    let marker = expected.next().expect("the FP(2,2) table has every case");
    let operands: Vec<Bits> = input.iter().copied().map(bits).collect();
    let got = run((2, 2), op, mode, &operands)
        .unwrap_or_else(|| panic!("encoding gap: {op} {mode:?} raw operands {input:?}"));
    if marker == b'N' {
        assert_eq!(
            (got.1, got.2),
            (3, 1),
            "expected NaN: {op} {mode:?} raw operands {input:?}; got {got:?}"
        );
    } else {
        let raw = (marker as char)
            .to_digit(16)
            .expect("oracle marker is a hex nibble") as u8;
        let want = bits(raw);
        assert_eq!(
            got,
            (want.0 == 1, want.1, want.2),
            "{op} {mode:?} raw operands {input:?}"
        );
    }
}

#[test]
fn all_fp22_arithmetic_circuit_truth_tables_match_fraction_oracle() {
    let fixture = include_str!("fp22_truth_tables.txt");
    let values: Vec<u8> = fixture
        .lines()
        .filter(|line| !line.starts_with('#'))
        .flat_map(str::bytes)
        .collect();
    assert_eq!(values.len(), 24_736, "fixture must cover every combination");
    let mut expected = values.into_iter();

    for op in ["add", "mul", "div"] {
        for mode in MODES {
            for a in 0..16 {
                for b in 0..16 {
                    check_case(&mut expected, op, mode, &[a, b]);
                }
            }
        }
    }
    for mode in MODES {
        for a in 0..16 {
            for b in 0..16 {
                for c in 0..16 {
                    check_case(&mut expected, "fma", mode, &[a, b, c]);
                }
            }
        }
    }
    for op in ["sqrt", "rti"] {
        for mode in MODES {
            for a in 0..16 {
                check_case(&mut expected, op, mode, &[a]);
            }
        }
    }
    for a in 0..16 {
        for b in 0..16 {
            check_case(&mut expected, "rem", RoundingMode::RNE, &[a, b]);
        }
    }
    assert_eq!(expected.next(), None, "no untested oracle results");
}

#[test]
fn minimum_legal_format_keeps_rounding_and_subnormal_bits() {
    use RoundingMode::{RNA, RNE, RTP};
    // Format (2,2) has positive finite values 0, 1/2, 1, 3/2, 2, 3.
    // Expected bits were also checked with the independent Fraction-based
    // scripts/differential/gen/strings-dt-fp/fpref.py evaluator.
    let cases: &[(&str, RoundingMode, &[Bits], Bits)] = &[
        ("mul", RNE, &[(0, 1, 1), (0, 1, 1)], (0, 2, 0)),
        ("mul", RTP, &[(0, 1, 1), (0, 1, 1)], (0, 2, 1)),
        ("fma", RNE, &[(0, 1, 1), (0, 1, 1), (1, 2, 0)], (0, 0, 0)),
        ("fma", RNA, &[(0, 1, 1), (0, 1, 1), (1, 2, 0)], (0, 0, 1)),
        ("sqrt", RNE, &[(0, 1, 1)], (0, 1, 0)),
        ("sqrt", RTP, &[(0, 1, 1)], (0, 1, 1)),
        ("div", RNE, &[(0, 0, 1), (0, 2, 1)], (0, 0, 0)),
        ("div", RTP, &[(0, 0, 1), (0, 2, 1)], (0, 0, 1)),
        ("rem", RNE, &[(0, 2, 1), (0, 2, 0)], (1, 1, 0)),
    ];
    for &(op, mode, operands, expected) in cases {
        assert_eq!(
            run((2, 2), op, mode, operands),
            expect(expected),
            "{op} {mode:?} {operands:?}",
        );
    }
}
