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

#[test]
fn preallocation_plan_is_checked_across_variables() {
    let mut enc = IntegerEncoder::new();
    enc.register_var(0, 600_000);
    enc.register_var(0, 600_000);
    assert!(matches!(
        enc.preallocation_plan(),
        Err(OrderEncodingCapacityError::LiteralLimitExceeded { .. })
    ));
}

#[test]
fn i64_max_domain_omits_the_unrepresentable_upper_sentinel() {
    let mut enc = IntegerEncoder::new();
    enc.register_var(i64::MAX - 2, i64::MAX);
    assert_eq!(enc.preallocation_plan().unwrap(), 3);

    let mut sat = SatSolver::new(0);
    enc.try_pre_allocate_all(&mut sat).unwrap();
    assert!(enc.lookup_ge(IntVarId(0), i64::MAX).is_some());
    assert!(enc.lookup_le(IntVarId(0), i64::MAX).is_some());
}
