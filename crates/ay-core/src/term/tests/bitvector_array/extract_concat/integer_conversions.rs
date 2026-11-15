// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bit-vector and integer conversion regressions.

use super::*;

#[test]
fn test_bv2nat_constant_folding() {
    let mut store = TermStore::new();

    let x0f = store.mk_bitvec(BigInt::from(0x0F), 8);
    let result = store.mk_bv2nat(x0f);

    assert_eq!(store.get_int(result).cloned(), Some(BigInt::from(15)));
}

#[test]
fn test_bv2nat_masked_int2bv_residue_semantics() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    for width in 1..=6 {
        let bv = store.mk_int2bv(width, x);
        for bits in 0..=width {
            let mask_value = (1_i64 << bits) - 1;
            let mask = store.mk_bitvec(BigInt::from(mask_value), width);
            for operands in [vec![bv, mask], vec![mask, bv]] {
                let masked = store.mk_bvand(operands);
                let nat = store.mk_bv2nat(masked);
                if bits == width {
                    assert_eq!(nat, store.mk_bv2nat(bv));
                    continue;
                }
                if bits > 0 && bits < width {
                    assert!(
                        matches!(store.get(nat), TermData::App(Symbol::Named(name), _) if name == "mod")
                    );
                }
                for value in -(1_i64 << width)..=(1_i64 << width) {
                    let literal = store.mk_int(BigInt::from(value));
                    let actual = store.substitute(nat, &[x], &[literal]);
                    assert_eq!(
                        store.get_int(actual),
                        Some(&BigInt::from(value & mask_value)),
                        "width={width}, mask={mask_value}, value={value}"
                    );
                }
            }
        }
    }
}

#[test]
fn test_bv2nat_masked_int2bv_rejects_masks_with_holes() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let bv = store.mk_int2bv(6, x);
    for mask_value in 1_i64..64 {
        if mask_value & (mask_value + 1) == 0 {
            continue;
        }
        let mask = store.mk_bitvec(BigInt::from(mask_value), 6);
        let masked = store.mk_bvand(vec![bv, mask]);
        let nat = store.mk_bv2nat(masked);
        assert!(
            matches!(store.get(nat), TermData::App(Symbol::Named(name), _) if name == "bv2nat")
        );
    }
}

#[test]
fn test_bv2nat_masked_int2bv_wide_negative_residue() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let bv = store.mk_int2bv(129, x);
    let mask_value: BigInt = (BigInt::from(1) << 100_u32) - 1;
    let mask = store.mk_bitvec(mask_value.clone(), 129);
    let masked = store.mk_bvand(vec![bv, mask]);
    let nat = store.mk_bv2nat(masked);
    let negative = store.mk_int(BigInt::from(-1));
    let actual = store.substitute(nat, &[x], &[negative]);
    assert_eq!(store.get_int(actual), Some(&mask_value));
}

#[test]
fn test_bv2nat_masked_int2bv_normalized_mask_and_other_sources() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let bv = store.mk_int2bv(8, x);
    let expected_modulus = store.mk_int(BigInt::from(4));
    let expected = store.mk_mod(x, expected_modulus);
    for mask_value in [-253, 3, 259] {
        let mask = store.mk_bitvec(BigInt::from(mask_value), 8);
        let masked = store.mk_bvand(vec![bv, mask]);
        assert_eq!(store.mk_bv2nat(masked), expected);
    }
    let leaf = store.mk_var("b", Sort::bitvec(64));
    let extended = store.mk_bvsign_extend(56, bv);
    let mask = store.mk_bitvec(BigInt::from(3), 64);
    for source in [leaf, extended] {
        let masked = store.mk_bvand(vec![source, mask]);
        let nat = store.mk_bv2nat(masked);
        assert!(
            matches!(store.get(nat), TermData::App(Symbol::Named(name), _) if name == "bv2nat")
        );
    }
}

fn assert_raw_bv2nat_preserved(store: &mut TermStore, masked: TermId) {
    let actual = store.mk_bv2nat(masked);
    let expected = store.mk_app(Symbol::named("bv2nat"), [masked], Sort::Int);
    assert_eq!(actual, expected);
    assert_eq!(store.sort(actual), &Sort::Int);
}

#[test]
fn test_bv2nat_masked_int2bv_raw_noninteger_sources() {
    let mut store = TermStore::new();
    for (name, sort) in [
        ("boolean", Sort::Bool),
        ("real", Sort::Real),
        ("bitvector", Sort::bitvec(8)),
    ] {
        let source = store.mk_var(name, sort);
        let bv = store.mk_app(
            Symbol::indexed("int2bv", vec![8]),
            [source],
            Sort::bitvec(8),
        );
        for mask_value in [0, 3, 255] {
            let mask = store.mk_bitvec(BigInt::from(mask_value), 8);
            for operands in [[bv, mask], [mask, bv]] {
                let masked = store.mk_app(Symbol::named("bvand"), operands, Sort::bitvec(8));
                // In particular, the zero mask must not erase an ill-typed source.
                assert_raw_bv2nat_preserved(&mut store, masked);
            }
        }
    }
}

#[test]
fn test_bv2nat_masked_int2bv_raw_width_mismatches() {
    let mut store = TermStore::new();
    let source = store.mk_var("x", Sort::Int);
    for (index, value_width, mask_width, result_width) in [
        (8, 8, 8, 16),
        (8, 16, 8, 8),
        (8, 8, 16, 8),
        (16, 8, 8, 8),
        (8, 8, 8, 0),
        (8, 0, 8, 8),
        (0, 8, 8, 8),
    ] {
        let bv = store.mk_app(
            Symbol::indexed("int2bv", vec![index]),
            [source],
            Sort::bitvec(value_width),
        );
        let mask = store.mk_bitvec(BigInt::from(3), mask_width);
        for operands in [[bv, mask], [mask, bv]] {
            let masked = store.mk_app(Symbol::named("bvand"), operands, Sort::bitvec(result_width));
            assert_raw_bv2nat_preserved(&mut store, masked);
        }
    }
}

#[test]
fn test_bv2nat_masked_int2bv_raw_operator_shapes() {
    let mut store = TermStore::new();
    let source = store.mk_var("x", Sort::Int);
    let mask = store.mk_bitvec(BigInt::from(3), 8);
    for (symbol, args) in [
        (Symbol::named("int2bv"), vec![source]),
        (Symbol::indexed("int2bv", vec![]), vec![source]),
        (Symbol::indexed("int2bv", vec![8, 8]), vec![source]),
        (Symbol::indexed("int2bv", vec![8]), vec![]),
        (Symbol::indexed("int2bv", vec![8]), vec![source, source]),
    ] {
        let bv = store.mk_app(symbol, args, Sort::bitvec(8));
        for operands in [[bv, mask], [mask, bv]] {
            let masked = store.mk_app(Symbol::named("bvand"), operands, Sort::bitvec(8));
            assert_raw_bv2nat_preserved(&mut store, masked);
        }
    }
    let bv = store.mk_int2bv(8, source);
    for args in [vec![], vec![bv], vec![bv, mask, mask]] {
        let masked = store.mk_app(Symbol::named("bvand"), args, Sort::bitvec(8));
        assert_raw_bv2nat_preserved(&mut store, masked);
    }
    let indexed = store.mk_app(
        Symbol::indexed("bvand", vec![8]),
        [bv, mask],
        Sort::bitvec(8),
    );
    assert_raw_bv2nat_preserved(&mut store, indexed);
}

#[test]
fn test_bv2nat_masked_int2bv_raw_mask_payloads() {
    let mut store = TermStore::new();
    let source = store.mk_var("x", Sort::Int);
    let bv = store.mk_int2bv(8, source);
    for (value, width, sort) in [
        (511, 8, Sort::bitvec(8)),
        (-1, 8, Sort::bitvec(8)),
        (3, 8, Sort::Int),
        (3, 8, Sort::bitvec(16)),
        (3, 16, Sort::bitvec(8)),
        (0, 8, Sort::Bool),
        (0, 0, Sort::bitvec(8)),
    ] {
        // The existing internal interner permits raw payload fixtures without
        // inventing IDs or minting terms in a checker-only reconstructed store.
        let mask = store.intern(
            TermData::Const(Constant::BitVec {
                value: BigInt::from(value),
                width,
            }),
            sort,
        );
        for operands in [[bv, mask], [mask, bv]] {
            let masked = store.mk_app(Symbol::named("bvand"), operands, Sort::bitvec(8));
            assert_raw_bv2nat_preserved(&mut store, masked);
        }
    }
}

#[test]
fn test_bv2nat_masked_int2bv_well_typed_raw_controls() {
    let mut store = TermStore::new();
    let source = store.mk_var("x", Sort::Int);
    for width in [1, 8, 129] {
        let bv = store.mk_app(
            Symbol::indexed("int2bv", vec![width]),
            [source],
            Sort::bitvec(width),
        );
        for bits in [0, width / 2, width] {
            let modulus_value: BigInt = BigInt::from(1) << bits;
            let mask = store.mk_bitvec(&modulus_value - 1, width);
            let modulus = store.mk_int(modulus_value);
            let expected = store.mk_mod(source, modulus);
            for operands in [[bv, mask], [mask, bv]] {
                // Raw bvand preserves zero/full masks until this conversion.
                let masked = store.mk_app(Symbol::named("bvand"), operands, Sort::bitvec(width));
                assert_eq!(store.mk_bv2nat(masked), expected);
            }
        }
    }
}

#[test]
fn test_bv2int_signed_constant_folding() {
    let mut store = TermStore::new();

    // Unsigned cases (is_signed = false) should match bv2nat
    let x0f = store.mk_bitvec(BigInt::from(0x0F), 8);
    let unsigned = store.mk_bv2int(x0f, false);
    assert_eq!(store.get_int(unsigned).cloned(), Some(BigInt::from(15)));

    // Signed positive: 0x7F (127) is positive, so bv2int_signed = 127
    let x7f = store.mk_bitvec(BigInt::from(0x7F), 8);
    let signed_pos = store.mk_bv2int(x7f, true);
    assert_eq!(store.get_int(signed_pos).cloned(), Some(BigInt::from(127)));

    // Signed negative: 0xFF is -1 in two's complement (8-bit)
    let xff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let signed_neg = store.mk_bv2int(xff, true);
    assert_eq!(store.get_int(signed_neg).cloned(), Some(BigInt::from(-1)));

    // Signed negative: 0x80 is -128 in two's complement (8-bit)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let signed_min = store.mk_bv2int(x80, true);
    assert_eq!(store.get_int(signed_min).cloned(), Some(BigInt::from(-128)));

    // Width=1 bitvectors: signed range is [-1, 0]
    // 0b0 (value 0) -> 0
    // 0b1 (value 1) -> -1
    let bit0 = store.mk_bitvec(BigInt::from(0), 1);
    let signed_0 = store.mk_bv2int(bit0, true);
    assert_eq!(store.get_int(signed_0).cloned(), Some(BigInt::from(0)));

    let bit1 = store.mk_bitvec(BigInt::from(1), 1);
    let signed_1 = store.mk_bv2int(bit1, true);
    assert_eq!(store.get_int(signed_1).cloned(), Some(BigInt::from(-1)));
}

#[test]
fn test_bv2int_symbolic() {
    let mut store = TermStore::new();

    // For symbolic bitvectors, mk_bv2int should produce an ITE expression
    let x = store.mk_var("x", Sort::bitvec(8));

    // Unsigned case: should produce bv2nat(x)
    let unsigned = store.mk_bv2int(x, false);
    assert_eq!(store.sort(unsigned), &Sort::Int);
    // Check it's a bv2nat application
    if let TermData::App(Symbol::Named(name), args) = store.get(unsigned) {
        assert_eq!(name, "bv2nat");
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], x);
    } else {
        panic!("Expected bv2nat application");
    }

    // Signed case: should produce ite(bvslt x 0, bv2nat(x) - 256, bv2nat(x))
    let signed = store.mk_bv2int(x, true);
    assert_eq!(store.sort(signed), &Sort::Int);
    // Check it's an ITE
    if let TermData::Ite(cond, then_branch, else_branch) = store.get(signed) {
        // Condition should be bvslt
        if let TermData::App(Symbol::Named(name), _) = store.get(*cond) {
            assert_eq!(name, "bvslt");
        } else {
            panic!("Expected bvslt condition");
        }
        // Both branches should have Int sort
        assert_eq!(store.sort(*then_branch), &Sort::Int);
        assert_eq!(store.sort(*else_branch), &Sort::Int);
    } else {
        panic!("Expected ITE for signed symbolic conversion");
    }
}

#[test]
fn test_int2bv_constant_folding_and_wraparound() {
    let mut store = TermStore::new();

    let fifteen = store.mk_int(BigInt::from(15));
    let result = store.mk_int2bv(8, fifteen);
    assert_eq!(result, store.mk_bitvec(BigInt::from(0x0F), 8));

    // -1 mod 2^8 = 255
    let minus_one = store.mk_int(BigInt::from(-1));
    let result2 = store.mk_int2bv(8, minus_one);
    assert_eq!(result2, store.mk_bitvec(BigInt::from(0xFF), 8));

    // 256 mod 2^8 = 0
    let two_fifty_six = store.mk_int(BigInt::from(256));
    let result3 = store.mk_int2bv(8, two_fifty_six);
    assert_eq!(result3, store.mk_bitvec(BigInt::from(0), 8));
}

#[test]
fn test_int2bv_bv2nat_roundtrip_simplification() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::bitvec(8));
    let nat = store.mk_bv2nat(x);
    let back = store.mk_int2bv(8, nat);
    assert_eq!(back, x);
}

#[test]
fn test_int2bv_bv2int_signed_roundtrip() {
    // Test that int2bv(bv2int(x, signed)) = x for constant bitvectors
    let mut store = TermStore::new();

    // Positive value: 0x7F (127 signed)
    let x7f = store.mk_bitvec(BigInt::from(0x7F), 8);
    let signed = store.mk_bv2int(x7f, true);
    assert_eq!(store.get_int(signed).cloned(), Some(BigInt::from(127)));
    let back = store.mk_int2bv(8, signed);
    assert_eq!(back, x7f);

    // Negative value: 0xFF (-1 signed)
    let xff = store.mk_bitvec(BigInt::from(0xFF), 8);
    let signed_neg = store.mk_bv2int(xff, true);
    assert_eq!(store.get_int(signed_neg).cloned(), Some(BigInt::from(-1)));
    let back_neg = store.mk_int2bv(8, signed_neg);
    assert_eq!(back_neg, xff);

    // Min value: 0x80 (-128 signed)
    let x80 = store.mk_bitvec(BigInt::from(0x80), 8);
    let signed_min = store.mk_bv2int(x80, true);
    assert_eq!(store.get_int(signed_min).cloned(), Some(BigInt::from(-128)));
    let back_min = store.mk_int2bv(8, signed_min);
    assert_eq!(back_min, x80);
}

#[test]
fn test_bv2int_32bit_width() {
    // Test 32-bit width to verify BigInt arithmetic works for common sizes
    let mut store = TermStore::new();

    // Max positive 32-bit signed: 0x7FFFFFFF = 2147483647
    let max_pos = store.mk_bitvec(BigInt::from(0x7FFFFFFFu32), 32);
    let signed_max = store.mk_bv2int(max_pos, true);
    assert_eq!(
        store.get_int(signed_max).cloned(),
        Some(BigInt::from(2147483647i64))
    );

    // -1 in 32-bit: 0xFFFFFFFF
    let minus_one = store.mk_bitvec(BigInt::from(0xFFFFFFFFu32), 32);
    let signed_neg1 = store.mk_bv2int(minus_one, true);
    assert_eq!(
        store.get_int(signed_neg1).cloned(),
        Some(BigInt::from(-1i64))
    );

    // Min 32-bit signed: 0x80000000 = -2147483648
    let min_neg = store.mk_bitvec(BigInt::from(0x80000000u32), 32);
    let signed_min = store.mk_bv2int(min_neg, true);
    assert_eq!(
        store.get_int(signed_min).cloned(),
        Some(BigInt::from(-2147483648i64))
    );

    // Verify roundtrip works
    let back = store.mk_int2bv(32, signed_min);
    assert_eq!(back, min_neg);
}
