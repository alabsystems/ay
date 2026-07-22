// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sound int2bv/bv2nat round-trip (range-injectivity) bridge.
//!
//! Closes the Int<->BV boundary-conversion gap behind the deductive-checks heap-loop
//! per-element invariant: from the ground fact `bv2nat(i) = n` (with `n` an
//! integer source) the solver must be able to PIN the BV index
//! `i = int2bv_w(n)`. This is the forward range-injectivity direction, which is
//! a theorem of the SMT-LIB `int2bv`/`bv2nat` semantics (it is vacuous when
//! `n >= 2^w`, since then `bv2nat(i) = n` is itself unsatisfiable). Adding it as
//! an additive valid lemma can only enable new UNSATs, never a false one.

use crate::api::{Logic, Solver, Sort};

/// VALID boundary-pin goal (was Unknown before the bridge):
///
/// ```text
///   bv2nat(i) = n   AND   0 <= n   AND   n < 2^w   AND   i != int2bv_w(n)
/// ```
///
/// is UNSAT, because `bv2nat(i) = n` pins `i = int2bv_w(n)`. This is exactly the
/// boundary-index step the heap-loop FQ invariant needs to read the just-pushed
/// element `select (store db (int2bv_w n) v) i = v`.
#[test]
fn test_int2bv_bv2nat_forward_injectivity_pins_boundary_index() {
    let mut solver = Solver::new(Logic::All);
    let w = 8u32;
    let i = solver.declare_const("i", Sort::bitvec(w));
    let n = solver.declare_const("n", Sort::Int);

    // bv2nat(i) = n
    let nat_i = solver.bv2int(i);
    let nat_eq_n = solver.eq(nat_i, n);
    solver.assert_term(nat_eq_n);

    // 0 <= n < 2^w  (the index bound; in the real scenario, n = old_len < 2^64)
    let zero = solver.int_const(0);
    let two_pow_w = solver.int_const(1i64 << w);
    let n_nonneg = solver.le(zero, n);
    let n_below = solver.lt(n, two_pow_w);
    solver.assert_term(n_nonneg);
    solver.assert_term(n_below);

    // i != int2bv_w(n)   (negation of the boundary pin we want to derive)
    let int2bv_n = solver.int2bv(n, w);
    let i_eq_int2bv = solver.eq(i, int2bv_n);
    let i_ne_int2bv = solver.not(i_eq_int2bv);
    solver.assert_term(i_ne_int2bv);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "forward injectivity bv2nat(i)=n & n<2^w => i=int2bv_w(n) should make this UNSAT, got {result:?}"
    );
}

/// The SAME pin used inside a `select (store ...)` boundary read, mirroring the
/// deductive-checks heap-loop shape: after `db.push(v)` at index `int2bv_w(old_len)`,
/// reading the element whose nat index is `old_len` must return `v`.
///
/// ```text
///   bv2nat(i) = n  AND  0 <= n < 2^w
///   AND  select (store db (int2bv_w n) v) i != v
/// ```
///
/// is UNSAT, since the pin `i = int2bv_w(n)` fires the select-store axiom.
#[test]
fn test_int2bv_pin_drives_select_store_boundary_read() {
    let mut solver = Solver::new(Logic::All);
    let w = 8u32;
    let idx_sort = Sort::bitvec(w);
    let elem_sort = Sort::bitvec(16);
    let arr_sort = Sort::array(idx_sort.clone(), elem_sort.clone());

    let db = solver.declare_const("db", arr_sort);
    let i = solver.declare_const("i", idx_sort);
    let v = solver.declare_const("v", elem_sort);
    let n = solver.declare_const("n", Sort::Int);

    // bv2nat(i) = n  &  0 <= n < 2^w
    let nat_i = solver.bv2int(i);
    let nat_eq_n = solver.eq(nat_i, n);
    solver.assert_term(nat_eq_n);
    let zero = solver.int_const(0);
    let two_pow_w = solver.int_const(1i64 << w);
    let n_nonneg = solver.le(zero, n);
    let n_below = solver.lt(n, two_pow_w);
    solver.assert_term(n_nonneg);
    solver.assert_term(n_below);

    // db' = store(db, int2bv_w(n), v)   (the just-pushed element)
    let store_idx = solver.int2bv(n, w);
    let db2 = solver.store(db, store_idx, v);
    // select db' i != v   (negation: the boundary read must equal v)
    let read = solver.select(db2, i);
    let read_eq_v = solver.eq(read, v);
    let read_ne_v = solver.not(read_eq_v);
    solver.assert_term(read_ne_v);

    let result = solver.check_sat();
    assert!(
        result.is_unsat(),
        "boundary pin should make select(store db int2bv_w(n) v) i = v, so UNSAT, got {result:?}"
    );
}

/// FALSE-CONTROL (overflow): the BACKWARD round-trip `i = int2bv_w(n) =>
/// bv2nat(i) = n` is NOT valid without `n < 2^w` (it would need
/// `bv2nat(int2bv_w(n)) = n`, true only mod `2^w`). With `n` unconstrained it can
/// overflow, so the following MUST stay satisfiable (witness `n = 2^w`, `i = 0`,
/// `bv2nat(i) = 0 != 2^w`):
///
/// ```text
///   i = int2bv_w(n)   AND   bv2nat(i) != n         (n free, may be >= 2^w)
/// ```
///
/// A bogus unguarded round-trip would wrongly refute this. It must NOT be UNSAT.
#[test]
fn test_int2bv_overflow_false_control_not_refuted() {
    let mut solver = Solver::new(Logic::All);
    let w = 8u32;
    let i = solver.declare_const("i", Sort::bitvec(w));
    let n = solver.declare_const("n", Sort::Int);

    // i = int2bv_w(n)
    let int2bv_n = solver.int2bv(n, w);
    let i_eq = solver.eq(i, int2bv_n);
    solver.assert_term(i_eq);

    // bv2nat(i) != n   (with no n < 2^w bound, n can overflow)
    let nat_i = solver.bv2int(i);
    let nat_eq_n = solver.eq(nat_i, n);
    let nat_ne_n = solver.not(nat_eq_n);
    solver.assert_term(nat_ne_n);

    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "overflow false-control must NOT be refuted (bogus backward round-trip), got {result:?}"
    );
}
