// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn complete_scalar_operator_table_preserves_exact_widths_and_arity() {
    use CountedBuiltin::*;
    let original = ample();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let left = builder.variable("left", &Sort::bitvec(256)).unwrap();
    let right = builder.variable("right", &Sort::bitvec(256)).unwrap();
    for op in [
        BvAdd, BvSub, BvMul, BvUDiv, BvURem, BvSDiv, BvSRem, BvSMod, BvAnd, BvOr, BvXor, BvNand,
        BvNor, BvXnor, BvShl, BvLShr, BvAShr,
    ] {
        let result = builder.apply(op, &[left, right]).unwrap();
        assert_eq!(builder.store.sort(result), &Sort::bitvec(256));
        assert_eq!(
            builder.apply(op, &[left]),
            Err(CountedTermError::InvalidInput)
        );
    }
    for op in [BvULt, BvULe, BvUGt, BvUGe, BvSLt, BvSLe, BvSGt, BvSGe] {
        let result = builder.apply(op, &[left, right]).unwrap();
        assert_eq!(builder.store.sort(result), &Sort::Bool);
    }
    for (op, width) in [
        (BvNot, 256),
        (BvNeg, 256),
        (BvExtract(255, 8), 248),
        (BvZeroExtend(7), 263),
        (BvSignExtend(9), 265),
        (BvRepeat(3), 768),
        (BvRotateLeft(400), 256),
        (BvRotateRight(401), 256),
    ] {
        let result = builder.apply(op, &[left]).unwrap();
        assert_eq!(builder.store.sort(result), &Sort::bitvec(width));
    }
    let comp = builder.apply(BvComp, &[left, right]).unwrap();
    assert_eq!(builder.store.sort(comp), &Sort::bitvec(1));
    let concat = builder.apply(BvConcat, &[left, right]).unwrap();
    assert_eq!(builder.store.sort(concat), &Sort::bitvec(512));
    let small = builder.variable("small", &Sort::bitvec(7)).unwrap();
    let concat = builder.apply(BvConcat, &[left, small]).unwrap();
    assert_eq!(builder.store.sort(concat), &Sort::bitvec(263));
}

#[test]
fn bad_signatures_and_constants_never_become_dead_arm_shortcuts() {
    use CountedBuiltin::*;
    let original = ample();
    let mut store = TermStore::new();
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    let yes = builder.boolean(true).unwrap();
    let a = builder.variable("a", &Sort::bitvec(8)).unwrap();
    let b = builder.variable("b", &Sort::bitvec(16)).unwrap();
    for (op, args) in [
        (BvAdd, vec![a, b]),
        (Not, vec![a]),
        (And, vec![yes, a]),
        (Ite, vec![yes, a, b]),
        (Eq, vec![a, b]),
        (Iff, vec![a, a]),
        (BvRepeat(0), vec![a]),
        (BvExtract(8, 0), vec![a]),
        (BvZeroExtend(u32::MAX), vec![a]),
        (Select, vec![a, a]),
        (Not, vec![TermId(u32::MAX)]),
    ] {
        let before = builder.store.terms.len();
        assert_eq!(
            builder.apply(op, &args),
            Err(CountedTermError::InvalidInput)
        );
        assert_eq!(builder.store.terms.len(), before);
    }
    assert_eq!(
        builder.bitvector(&BigInt::from(-1), 8),
        Err(CountedTermError::InvalidInput)
    );
    assert_eq!(
        builder.bitvector(&BigInt::from(256), 8),
        Err(CountedTermError::InvalidInput)
    );
    assert_eq!(
        builder.variable("bad", &Sort::bitvec(0)),
        Err(CountedTermError::InvalidInput)
    );
    assert_eq!(
        builder.variable("int", &Sort::Int),
        Err(CountedTermError::Unsupported)
    );
    let array = builder.constant_array(&Sort::bitvec(8), b).unwrap();
    assert_eq!(
        builder.apply(Store, &[array, b, b]),
        Err(CountedTermError::InvalidInput)
    );
    assert_eq!(
        builder.apply(Store, &[array, a, yes]),
        Err(CountedTermError::InvalidInput)
    );
}

#[test]
fn native_sort_copy_depth_and_readonly_snapshot_are_explicit_refusals() {
    let original = ample();
    let mut store = TermStore::new();
    let mut deep = Sort::Bool;
    for _ in 0..257 {
        deep = Sort::array(Sort::Bool, deep);
    }
    let mut builder = CountedTermBuilder::new(&mut store, &original).unwrap();
    assert_eq!(
        builder.variable("deep", &deep),
        Err(CountedTermError::Unsupported)
    );
    builder.finish().unwrap();
    let entries = store.entries_snapshot();
    let (yes, no) = store.boolean_constant_ids();
    let mut snapshot = TermStore::from_entries(entries, yes, no, store.var_counter());
    assert!(matches!(
        CountedTermBuilder::new(&mut snapshot, &original),
        Err(CountedTermError::ReadOnlySnapshot)
    ));
}
