// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The old setup really normalizes; this is not whole-pin information loss.

use super::*;

const OLD_UNIFORM: &str = "
 (declare-const a (Array (_ BitVec 64) (_ BitVec 128)))
 (assert (= a (store (store
   ((as const (Array (_ BitVec 64) (_ BitVec 128))) #xffffffffffffffffffffffffffffffff)
   (_ bv18446744073709551615 64) (_ bv7 128))
   (_ bv18446744073709551615 64) #xffffffffffffffffffffffffffffffff)))
 (assert (forall ((i (_ BitVec 64)))
   (= (select a i) #xffffffffffffffffffffffffffffffff)))";

const OLD_MAX_BOUND: &str = "
 (declare-const b (Array (_ BitVec 64) (_ BitVec 8)))
 (declare-const w (Array (_ BitVec 64) (_ BitVec 8)))
 (assert (= b (store (store
   ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
   (_ bv18446744073709551615 64) #x0b) (_ bv0 64) #x09)))
 (assert (= w (lambda ((i (_ BitVec 64)))
   (ite (and (bvule (_ bv1 64) i)
             (bvult i (_ bv18446744073709551615 64)))
        (select b (bvadd (bvsub i (_ bv1 64))
                        (_ bv18446744073709551615 64)))
        (select b i)))))
 (assert (forall ((i (_ BitVec 64))) (bvule (select w i) #xff)))";

#[test]
fn old_uniform_and_unsigned_max_sources_normalize_before_whole_pinning() {
    let end = Instant::now() + Duration::from_secs(20);
    let scope = enter_check_stop(Arc::new(move || Instant::now() >= end));
    let mut exec = loaded(OLD_UNIFORM, end);
    let leaf = variable(&exec, "a");
    let original_value = {
        let definition = args(&exec, exec.ctx.assertions[0], "=");
        assert_eq!(definition[0], leaf);
        definition[1]
    };
    let base = args(&exec, original_value, "const-array");
    let maximum = (num_bigint::BigInt::from(1u8) << 128u32) - 1u8;
    assert!(matches!(exec.ctx.terms.get(base[0]),
        TermData::Const(Constant::BitVec { value, width: 128 }) if value == &maximum));
    let root = matrix(&exec);
    let result = pins(&mut exec, root, &HashSet::new());
    assert!(result.total);
    assert_eq!(result.equalities.len(), 1);
    let value = rhs(&exec, &result, leaf);
    assert_eq!(
        value, original_value,
        "the normalized complete constant function"
    );
    args(&exec, value, "const-array");
    whole(&exec, leaf, value);
    drop(result);
    drop(exec);

    let mut exec = loaded(OLD_MAX_BOUND, end);
    let root = matrix(&exec);
    let TermData::Forall(_, body, _) = exec.ctx.terms.get(root) else {
        panic!("the original quantified matrix is retained");
    };
    assert_eq!(
        *body,
        exec.ctx.terms.true_term(),
        "BV8 unsigned maximum is valid"
    );
    let result = pins(&mut exec, root, &HashSet::new());
    assert!(result.total);
    assert!(
        result.equalities.is_empty(),
        "true has no free array leaf to pin"
    );
    assert!(
        exec.last_result.is_none(),
        "normalization and pins are DATA"
    );
    drop(result);
    drop(exec);
    drop(scope);
    assert!(
        Instant::now() < end,
        "one original end includes both cleanups"
    );
}
