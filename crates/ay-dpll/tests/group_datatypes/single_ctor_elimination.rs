// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Eager single-constructor datatype elimination (product types).
//!
//! A single-constructor datatype `D = C(f_0: T_0, ..., f_{n-1}: T_{n-1})` is
//! isomorphic to the tuple of its fields. A freshly declared constant of such a
//! sort is bound at elaboration to `C(v!f_0, ..., v!f_{n-1})` over fresh field
//! constants, so:
//!   * `sel_i(v)` reduces to `v!f_i` (selector-over-constructor fold), and
//!   * `v = w` decomposes into field equalities (constructor injectivity),
//! discharging with only the underlying scalar/UF theories — no datatype
//! decision procedure required.
//!
//! These cases are exactly the closure-environment shapes a bounded model
//! checker emits for `proof_for_contract` harnesses (a closure's captured
//! environment is a single-constructor struct over scalar fields, havoc'd and
//! then projected with selectors). Before this fix the combined DT+BV solver
//! returned `unknown (incomplete)` on the SAT cases below — most importantly a
//! constructor=constructor equality between two havoc'd variables combined with
//! a selector pinned to a concrete value — which a verifier reports as
//! "no checks". They must now be decided precisely (sat/unsat), not `unknown`.

use ntest::timeout;

/// SAT: direct construct-then-select, `(c (mk x)) = 5`.
#[test]
#[timeout(60_000)]
fn test_single_ctor_direct_construct_select() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((mk (c (_ BitVec 64)))))
        (declare-const x (_ BitVec 64))
        (assert (= (c (mk x)) #x0000000000000005))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// UNSAT: selector of a constructor is the field — `(c (mk x)) = x` always.
#[test]
#[timeout(60_000)]
fn test_single_ctor_select_is_field() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((mk (c (_ BitVec 64)))))
        (declare-const x (_ BitVec 64))
        (assert (not (= (c (mk x)) x)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// SAT: selector on a free (havoc'd) single-constructor variable, pinned.
#[test]
#[timeout(60_000)]
fn test_single_ctor_free_var_selector_pinned() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((mk (c (_ BitVec 64)))))
        (declare-const p Cl)
        (assert (= (c p) #x0000000000000005))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// SAT: the key regression — constructor=constructor equality between two
/// havoc'd variables (`p = q`) plus a selector pinned to a concrete value.
/// This is the exact shape that returned `unknown (incomplete)` before the fix.
#[test]
#[timeout(60_000)]
fn test_single_ctor_var_equality_plus_pinned_selector() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((mk (c (_ BitVec 64)))))
        (declare-const p Cl)
        (declare-const q Cl)
        (assert (= p q))
        (assert (= (c p) #x0000000000000005))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve(smt).trim(),
        "sat",
        "p = q plus a pinned selector must be SAT, not unknown"
    );
}

/// UNSAT: injectivity through the variable equality — `p = q` forces
/// `c(p) = c(q)`.
#[test]
#[timeout(60_000)]
fn test_single_ctor_var_equality_injectivity() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((mk (c (_ BitVec 64)))))
        (declare-const p Cl)
        (declare-const q Cl)
        (assert (= p q))
        (assert (not (= (c p) (c q))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// UNSAT: a selector cannot hold two distinct concrete values.
#[test]
#[timeout(60_000)]
fn test_single_ctor_free_var_selector_conflict() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((mk (c (_ BitVec 64)))))
        (declare-const p Cl)
        (assert (= (c p) #x0000000000000005))
        (assert (= (c p) #x0000000000000006))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// SAT: the full closure-environment shape a BMC `proof_for_contract` harness
/// emits — a havoc'd closure env aliased to another (`l22 = l14`), its captured
/// field projected (`l78 = cap_0(l22)`), then pinned (`l78 = 5`).
#[test]
#[timeout(60_000)]
fn test_single_ctor_closure_env_proof_shape() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Closure_401 ((Closure_401_mk (cap_0 (_ BitVec 64)))))
        (declare-const l22 Closure_401)
        (declare-const l14 Closure_401)
        (declare-const l78 (_ BitVec 64))
        (assert (= l22 l14))
        (assert (= l78 (cap_0 l22)))
        (assert (= l78 #x0000000000000005))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve(smt).trim(),
        "sat",
        "closure-environment proof_for_contract shape must be decided SAT"
    );
}

/// SAT: a multi-field single-constructor struct over a single theory (two
/// bitvector fields — the shape a closure capturing multiple scalars produces),
/// with both selectors projected, plus a constructor=constructor variable
/// equality. Exercises positional field elimination across fields.
///
/// (Fields are kept in ONE theory deliberately: ay does not yet decide combined
/// bitvector+integer goals, so a BV+Int struct would hit that orthogonal
/// mixed-theory gap, not the datatype machinery under test here.)
#[test]
#[timeout(60_000)]
fn test_single_ctor_multifield_struct() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype S ((mkS (f0 (_ BitVec 32)) (f1 (_ BitVec 8)))))
        (declare-const s S)
        (declare-const t S)
        (assert (= s t))
        (assert (= (f0 s) #x00000007))
        (assert (= (f1 t) #x2a))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// UNSAT companion to the multi-field case: aliased structs cannot disagree on a
/// field (injectivity over the second field).
#[test]
#[timeout(60_000)]
fn test_single_ctor_multifield_struct_injectivity() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype S ((mkS (f0 (_ BitVec 32)) (f1 (_ BitVec 8)))))
        (declare-const s S)
        (declare-const t S)
        (assert (= s t))
        (assert (= (f1 s) #x01))
        (assert (= (f1 t) #x02))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// Multi-constructor datatypes must be UNAFFECTED by the single-constructor
/// elimination: a genuinely free Option-typed variable still case-splits.
/// SAT here (x could be None, making the Some-selector constraint vacuous via
/// exhaustiveness), but it must be decided, not regressed to unknown.
#[test]
#[timeout(60_000)]
fn test_multi_ctor_not_eliminated() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Option ((None) (Some (value Int))))
        (declare-const o Option)
        (assert (= o (Some 5)))
        (assert (not (= (value o) 5)))
        (check-sat)
    "#;
    // o = Some 5 forces value(o) = 5, contradicting the disequality.
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// SAT: a qualified nullary constructor `(as Ctor Sort)` must elaborate to the
/// same term as the bare constructor. Emitting a 0-ary `App` here (instead of
/// the constructor's `Var` term) left construct/equality goals `unknown`. This
/// is the Rust unit-variant pattern a bounded model checker emits.
#[test]
#[timeout(60_000)]
fn test_qualified_nullary_constructor_single() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Unit ((Unit_mk)))
        (declare-const u Unit)
        (assert (= u (as Unit_mk Unit)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// UNSAT: there is only one inhabitant of a zero-field single-constructor
/// datatype, so `u` cannot differ from `(as Unit_mk Unit)`.
#[test]
#[timeout(60_000)]
fn test_qualified_nullary_constructor_unique() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Unit ((Unit_mk)))
        (declare-const u Unit)
        (assert (not (= u (as Unit_mk Unit))))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "unsat");
}

/// SAT: qualified nullary constructor of a MULTI-constructor enum `(as A E)`.
#[test]
#[timeout(60_000)]
fn test_qualified_nullary_constructor_multi() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype E ((A) (B (x (_ BitVec 8)))))
        (declare-const e E)
        (assert (= e (as A E)))
        (check-sat)
    "#;
    assert_eq!(crate::common::solve(smt).trim(), "sat");
}

/// SAT: a USED zero-field datatype (`Unit`) alongside an eliminated multi-field
/// datatype with a constructor-in-`ite` and a pinned selector. The zero-field
/// datatype is eliminated to its sole inhabitant rather than left a free
/// variable, so it no longer drags the combined solver to `unknown` here. This
/// is the closure-environment shape a `proof_for_contract` CHECK harness emits
/// for a `&mut self` method (`Unit` return + multi-capture closure).
#[test]
#[timeout(60_000)]
fn test_zero_field_with_multifield_closure() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Unit ((Unit_mk)))
        (declare-datatype C2 ((C2_mk (cap_0 (_ BitVec 64)) (cap_1 (_ BitVec 64)))))
        (declare-const u Unit)
        (assert (= u (as Unit_mk Unit)))
        (declare-const x C2)
        (declare-const cond Bool)
        (declare-const a (_ BitVec 64))
        (declare-const b (_ BitVec 64))
        (declare-const xssa C2)
        (assert (= x (ite cond (C2_mk a b) xssa)))
        (declare-const r (_ BitVec 64))
        (assert (= r (cap_1 x)))
        (assert (= r #x0000000000000007))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve(smt).trim(),
        "sat",
        "zero-field DT used alongside a two-field eliminated DT must be decided SAT"
    );
}

/// SAT: a datatype SELECTOR applied to an `ite` whose BOTH branches are
/// constructor applications — `(cap_0 (ite c (Cl_mk a a) (Cl_mk b b)))`. The
/// selector distributes through the `ite` to its constructor leaves
/// (`sel(ite c X Y) -> ite c (sel X) (sel Y)`), folding to `(ite c a b)`, so the
/// captured field is a constrained BV rather than an opaque selector left as a
/// free Tseitin variable. This is exactly the closure-environment SSA-select
/// shape a `proof_for_contract` emits
/// (`(cap_i (ite c (Closure_mk ..) (Closure_mk ..)))`). (#selector-over-ite)
#[test]
#[timeout(60_000)]
fn test_selector_over_ite_both_constructors() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((Cl_mk (cap_0 (_ BitVec 64)) (cap_1 (_ BitVec 64)))))
        (declare-const a (_ BitVec 64))
        (declare-const b (_ BitVec 64))
        (declare-const cond Bool)
        (declare-const r (_ BitVec 64))
        (assert (= r (cap_0 (ite cond (Cl_mk a a) (Cl_mk b b)))))
        (assert (= r #x0000000000000005))
        (assert (not cond))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve(smt).trim(),
        "sat",
        "selector over an ite of two constructors must distribute and decide SAT"
    );
}

/// UNSAT companion: with `cond` false the distributed selector picks the second
/// branch's field `b`, so `r = cap_0(..) = b` and `r = 5` force `b = 5`; adding
/// `b != 5` is then a contradiction. Without the distribution the selector stays
/// opaque and `b` is unconstrained, which would wrongly admit SAT — so this
/// pins down that the field is genuinely CONSTRAINED. (#selector-over-ite)
#[test]
#[timeout(60_000)]
fn test_selector_over_ite_constrains_field() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Cl ((Cl_mk (cap_0 (_ BitVec 64)) (cap_1 (_ BitVec 64)))))
        (declare-const a (_ BitVec 64))
        (declare-const b (_ BitVec 64))
        (declare-const cond Bool)
        (declare-const r (_ BitVec 64))
        (assert (= r (cap_0 (ite cond (Cl_mk a a) (Cl_mk b b)))))
        (assert (= r #x0000000000000005))
        (assert (not cond))
        (assert (not (= b #x0000000000000005)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve(smt).trim(),
        "unsat",
        "the distributed selector field must be constrained (b = r = 5), so b != 5 is unsat"
    );
}

/// SAT: a Parser-shaped nested datatype with an `Array`-valued field, where a
/// field equality is reflexively true via selector-over-constructor:
/// `(= (AV_mk b l) (pr p))` with `p`'s `pr` field being `(AV_mk b l)`. The
/// `Array` field has no canonical ground string, so the model-validation
/// `resolve_ground` path cannot confirm the datatype equality; the
/// reflexive-after-selector-reduction decision keeps it from being fail-closed
/// to `unknown`. This is the `process_byte_inner_preserves_invariant` contract
/// shape (a `Parser` datatype whose `ArrayVec`/`Vec` fields back `(Array ..)`).
/// (#selector-over-ctor-ground)
#[test]
#[timeout(60_000)]
fn test_datatype_array_field_reflexive_equality() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype AV
            ((AV_mk (buf (Array (_ BitVec 64) (_ BitVec 16))) (len (_ BitVec 64)))))
        (declare-datatype P ((P_mk (st (_ BitVec 8)) (pr AV))))
        (declare-const p P)
        (declare-const b (Array (_ BitVec 64) (_ BitVec 16)))
        (declare-const l (_ BitVec 64))
        (assert (= (AV_mk b l) (pr p)))
        (check-sat)
    "#;
    assert_eq!(
        crate::common::solve(smt).trim(),
        "sat",
        "a datatype equality with an Array-valued field must not fail-close to unknown"
    );
}
