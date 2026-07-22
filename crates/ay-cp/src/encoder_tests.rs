// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_create_ge_literal() {
    let mut sat = SatSolver::new(0);
    let mut enc = IntegerEncoder::new();
    let x = enc.register_var(1, 10);

    let lit5 = enc.get_or_create_ge(&mut sat, x, 5);
    let lit5_again = enc.get_or_create_ge(&mut sat, x, 5);
    assert_eq!(lit5, lit5_again, "same literal returned for same bound");
}

#[test]
fn test_le_is_negated_ge() {
    let mut sat = SatSolver::new(0);
    let mut enc = IntegerEncoder::new();
    let x = enc.register_var(1, 10);

    let le5 = enc.get_or_create_le(&mut sat, x, 5);
    let ge6 = enc.get_or_create_ge(&mut sat, x, 6);
    assert_eq!(le5, ge6.negated(), "[x <= 5] = ¬[x >= 6]");
}

#[test]
fn test_decode_roundtrip() {
    let mut sat = SatSolver::new(0);
    let mut enc = IntegerEncoder::new();
    let x = enc.register_var(0, 100);

    let lit = enc.get_or_create_ge(&mut sat, x, 50);
    let decoded = enc.decode(lit.variable()).unwrap();
    assert_eq!(decoded.var, x);
    assert_eq!(decoded.value, 50);
    assert!(decoded.is_ge);
}

#[test]
fn test_lazy_creation() {
    let mut sat = SatSolver::new(0);
    let mut enc = IntegerEncoder::new();
    let _x = enc.register_var(0, 1_000_000);

    // No literals created yet
    assert_eq!(enc.num_literals(), 0);

    // Create just one
    enc.get_or_create_ge(&mut sat, IntVarId(0), 500_000);
    assert_eq!(enc.num_literals(), 1);
}
