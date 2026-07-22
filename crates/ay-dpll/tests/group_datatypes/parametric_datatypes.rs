// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Integration tests for parametric (polymorphic) algebraic datatypes,
//! implemented via lazy monomorphization in the frontend elaborator.
//!
//! A `(declare-datatypes ((Name n)) ((par (T..) (ctors))))` with arity `n > 0`
//! is stored as a template and each ground use `(Name A1 .. An)` is
//! monomorphized into a fresh instance sort whose constructors/selectors/testers
//! are resolved by argument/result sort via the overload machinery. Each result
//! below was cross-checked against z3 (logic ALL).

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

/// Resolve the single sat/unsat/unknown answer, asserting it equals `expected`.
fn assert_result(smt: &str, expected: &str) {
    let output = crate::common::solve(smt);
    let got = crate::common::sat_result(&output)
        .unwrap_or_else(|| panic!("no sat/unsat/unknown line in output:\n{output}\nSMT2:\n{smt}"));
    assert_eq!(got, expected, "unexpected result\nSMT2:\n{smt}");
}

/// SAT: `(Opt Int)` with `is-some` and a constrained `val` field.
#[test]
#[timeout(60_000)]
fn test_parametric_option_some_val_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (declare-const x (Opt Int))
        (assert ((_ is some) x))
        (assert (= (val x) 5))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// SAT: recursive parametric list `(Lst Int)` with `is-cons` and `hd`.
#[test]
#[timeout(60_000)]
fn test_parametric_list_cons_hd_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
        (declare-const l (Lst Int))
        (assert ((_ is cons) l))
        (assert (= (hd l) 1))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// UNSAT: constructor injectivity — `(cons 1 nil) = (cons 2 nil)` forces `1 = 2`.
#[test]
#[timeout(60_000)]
fn test_parametric_list_injectivity_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
        (declare-const l (Lst Int))
        (assert (= (cons 1 (as nil (Lst Int))) (cons 2 (as nil (Lst Int)))))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT: datatype acyclicity — `l = (cons 1 l)` is a structural cycle.
#[test]
#[timeout(60_000)]
fn test_parametric_list_acyclicity_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
        (declare-const l (Lst Int))
        (assert (= l (cons 1 l)))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// SAT: two instantiations of the same parametric datatype coexist, with the
/// selector resolving to the right field sort for each (`Int` vs `Bool`).
#[test]
#[timeout(60_000)]
fn test_parametric_two_instances_coexist_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (declare-const a (Opt Int))
        (declare-const b (Opt Bool))
        (assert ((_ is some) a))
        (assert ((_ is some) b))
        (assert (= (val a) 7))
        (assert (val b))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// UNSAT: distinct constructors of one instance clash — `(some 1) = none`.
#[test]
#[timeout(60_000)]
fn test_parametric_option_constructor_clash_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (declare-const a (Opt Int))
        (assert (= a (some 1)))
        (assert (= a (as none (Opt Int))))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT: two coexisting instances must keep distinct field constraints — the
/// `Int`-instance `val` is pinned to two different values through a constructor
/// equality (selector-through-indirection), while a `Bool` instance also exists.
#[test]
#[timeout(60_000)]
fn test_parametric_two_instances_field_conflict_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (declare-const a (Opt Int))
        (declare-const b (Opt Bool))
        (assert (= a (some 7)))
        (assert (= (val a) 8))
        (assert ((_ is some) b))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// SAT: a datatype with TWO type parameters `(Pair Int Bool)`; selectors project
/// the correct heterogeneous field sorts.
#[test]
#[timeout(60_000)]
fn test_parametric_pair_two_params_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 2)) ((par (A B) ((mk (fst A) (snd B))))))
        (declare-const p (Pair Int Bool))
        (assert (= (fst p) 4))
        (assert (snd p))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// UNSAT: injectivity for a two-parameter datatype — `(mk 1 true) = (mk 2 true)`.
#[test]
#[timeout(60_000)]
fn test_parametric_pair_injectivity_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 2)) ((par (A B) ((mk (fst A) (snd B))))))
        (declare-const p (Pair Int Bool))
        (declare-const q (Pair Int Bool))
        (assert (= p (mk 1 true)))
        (assert (= q (mk 2 true)))
        (assert (= p q))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// SAT: nested instantiation `(Lst (Lst Int))` monomorphizes both the inner and
/// outer instances and reasons about the nested head.
#[test]
#[timeout(60_000)]
fn test_parametric_nested_instance_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 1)) ((par (T) ((nil) (cons (hd T) (tl (Lst T)))))))
        (declare-const ll (Lst (Lst Int)))
        (assert ((_ is cons) ll))
        (assert ((_ is cons) (hd ll)))
        (assert (= (hd (hd ll)) 9))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

// ===================== BARE-constructor instance inference =====================
// A bare parametric-constructor application (no `(as ...)`) names no instance
// sort, so lazy monomorphization must infer the instance from the constructor's
// ARGUMENT sorts — otherwise the application gets no injectivity/distinctness
// axioms and `(= (some true) (some false))` is wrongly SAT. Each answer below
// was cross-checked against z3 (logic ALL).

/// UNSAT: bare `(some true) = (some false)` — injectivity over a Bool field.
/// Regression for the wrong-SAT soundness bug (instance inferred from `T = Bool`).
#[test]
#[timeout(60_000)]
fn test_parametric_bare_some_injectivity_bool_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (assert (= (some true) (some false)))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT: bare `(some 1) = (some 2)` — injectivity over an Int field, no `as`.
#[test]
#[timeout(60_000)]
fn test_parametric_bare_some_injectivity_int_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (assert (= (some 1) (some 2)))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT: bare `(mk 1 true) = (mk 2 true)` — injectivity for a 2-param datatype
/// whose instance `(Pair Int Bool)` is inferred from `A = Int, B = Bool`.
#[test]
#[timeout(60_000)]
fn test_parametric_bare_mk_injectivity_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 2)) ((par (A B) ((mk (fst A) (snd B))))))
        (assert (= (mk 1 true) (mk 2 true)))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT: `(distinct (some 1) (some 1))` — a value cannot differ from itself.
#[test]
#[timeout(60_000)]
fn test_parametric_bare_some_distinct_same_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (assert (distinct (some 1) (some 1)))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// SAT: `(= (some 1) (some 1))` — identical constructor applications are equal.
#[test]
#[timeout(60_000)]
fn test_parametric_bare_some_eq_same_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (assert (= (some 1) (some 1)))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// UNSAT: a bare constructor bound to a variable still drives selector
/// reasoning — `x = (some 5)` forces `(val x) = 5`, contradicting `(val x) = 6`.
#[test]
#[timeout(60_000)]
fn test_parametric_bare_some_var_field_conflict_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (declare-const x (Opt Int))
        (assert (= x (some 5)))
        (assert (= (val x) 6))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// A bare nullary constructor whose instance cannot be inferred from any
/// argument (phantom parameter) and is genuinely ambiguous across two
/// registered instances must NOT be reported SAT — a clean elaboration error
/// (or unknown) is required, never a guess.
#[test]
#[timeout(60_000)]
fn test_parametric_bare_none_ambiguous_not_wrong_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))
        (declare-const x (Opt Int))
        (declare-const y (Opt Bool))
        (assert (= x (some 1)))
        (assert (= y (some true)))
        (assert (= x (none)))
        (check-sat)
    "#;
    let result = run_executor_smt_with_timeout(smt, 60);
    // A clean error (Err) or any non-SAT outcome is acceptable; a SAT answer
    // would be an unsound guess at the ambiguous instance.
    assert_ne!(
        result.ok(),
        Some(SolverOutcome::Sat),
        "ambiguous bare nullary constructor must not be reported SAT"
    );
}

// ============ Multi-instance single-constructor elimination soundness ============
// A single-constructor parametric datatype (a product/struct) is eagerly
// eliminated to a constructor term over fresh field constants. The field SORTS
// must come from THIS instance, not the last-registered one — otherwise nested
// selectors mis-type (wrong-UNSAT) and two instances of the same datatype get
// confused (wrong-SAT). Each answer was cross-checked against z3 (logic ALL).

/// SAT (Group A): nested selector `(snd (fst p))` must keep the INNER instance's
/// field sort. `(fst p):(Pair Int Int)` so `(snd (fst p)):Int`, satisfiable for 2.
#[test]
#[timeout(60_000)]
fn test_parametric_nested_selector_inner_snd_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 2)) ((par (A B) ((mk (fst A) (snd B))))))
        (declare-const p (Pair (Pair Int Int) Bool))
        (assert (= (snd (fst p)) 2))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// SAT (Group A, other slot): `(fst (snd p))` where `(snd p):(Pair Int Int)`.
#[test]
#[timeout(60_000)]
fn test_parametric_nested_selector_inner_fst_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Pair 2)) ((par (A B) ((mk (fst A) (snd B))))))
        (declare-const p (Pair Bool (Pair Int Int)))
        (assert (= (fst (snd p)) 2))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// SAT (Group A, 3-param Triple): nested selector `(e1 (e3 t))` through a
/// `(Triple Int Int Int)` field must resolve to `Int`.
#[test]
#[timeout(60_000)]
fn test_parametric_nested_selector_triple_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Triple 3)) ((par (A B C) ((t3 (e1 A) (e2 B) (e3 C))))))
        (declare-const t (Triple Bool Bool (Triple Int Int Int)))
        (assert (= (e1 (e3 t)) 5))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// UNSAT (Group B): two consts of the SAME instance `(P Int Bool)` declared with
/// a `(P Bool Int)` instance interleaved between them must keep the SAME internal
/// sort, so `(distinct x4 x6) ∧ (= x4 x6)` is a direct contradiction.
#[test]
#[timeout(60_000)]
fn test_parametric_multi_instance_distinct_eq_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((P 2)) ((par (A B) ((mk (s0 A) (s1 B))))))
        (declare-const x4 (P Int Bool))
        (declare-const x5 (P Bool Int))
        (declare-const x6 (P Int Bool))
        (assert (distinct x4 x6))
        (assert (= x4 x6))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT (Group B, injectivity): with a swapped-arg instance interleaved, two
/// distinct constructor values of `(P Int Bool)` cannot be equal.
#[test]
#[timeout(60_000)]
fn test_parametric_multi_instance_injectivity_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((P 2)) ((par (A B) ((mk (s0 A) (s1 B))))))
        (declare-const x4 (P Int Bool))
        (declare-const x5 (P Bool Int))
        (declare-const x6 (P Int Bool))
        (assert (= x4 ((as mk (P Int Bool)) 1 true)))
        (assert (= x6 ((as mk (P Int Bool)) 2 true)))
        (assert (= x4 x6))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT (Group C): acyclicity must fire for a monomorphized parametric instance
/// — `x = D0c1(x)` is a structural cycle.
#[test]
#[timeout(60_000)]
fn test_parametric_instance_acyclicity_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((D0 2))
          ((par (T0 T1) ((D0c0) (D0c1 (D0c1s0 (D0 T0 T1)))))))
        (declare-const x5 (D0 Bool Int))
        (assert (= x5 (D0c1 x5)))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

/// UNSAT (Group C, tester-forced): `(is-D0c1 x) ∧ (D0c1s0 x) = x` ⇒ `x = D0c1(x)`.
#[test]
#[timeout(60_000)]
fn test_parametric_instance_acyclicity_tester_unsat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((D0 2))
          ((par (T0 T1) ((D0c0) (D0c1 (D0c1s0 (D0 T0 T1)))))))
        (declare-const x5 (D0 Bool Int))
        (assert ((_ is D0c1) x5))
        (assert (= (D0c1s0 x5) x5))
        (check-sat)
    "#;
    assert_result(smt, "unsat");
}

// ===================== Finite-cardinality / pigeonhole over instances ============
// A SELF-NESTED parametric instance over a FINITE element type has finite
// cardinality (`(Opt (Opt Bool))` has 4 inhabitants), so a `distinct` clique
// larger than the cardinality is UNSAT (pigeonhole). The instance-mangled
// constructor names keep each monomorphized instance a name-disjoint datatype,
// so the DT theory computes the EXACT cardinality (a shared-name collision would
// mis-classify the field-bearing instance as recursive/infinite -> wrong SAT).
// Each answer was cross-checked against z3 (logic ALL).

const OPT_DECL: &str = "(declare-datatypes ((Opt 1)) ((par (T) ((onone) (osome (oval T))))))";

/// UNSAT: `(Opt (Opt Bool))` has exactly 4 inhabitants; 5 distinct is impossible.
#[test]
#[timeout(60_000)]
fn test_parametric_finite_cardinality_5_distinct_unsat() {
    let smt = format!(
        "(set-logic ALL)\n{OPT_DECL}\n\
         (declare-const a (Opt (Opt Bool)))(declare-const b (Opt (Opt Bool)))\
         (declare-const c (Opt (Opt Bool)))(declare-const d (Opt (Opt Bool)))\
         (declare-const e (Opt (Opt Bool)))\n\
         (assert (distinct a b c d e))\n(check-sat)\n"
    );
    assert_result(&smt, "unsat");
}

/// SAT: 4 distinct values of `(Opt (Opt Bool))` exhaust its 4 inhabitants.
#[test]
#[timeout(60_000)]
fn test_parametric_finite_cardinality_4_distinct_sat() {
    let smt = format!(
        "(set-logic ALL)\n{OPT_DECL}\n\
         (declare-const a (Opt (Opt Bool)))(declare-const b (Opt (Opt Bool)))\
         (declare-const c (Opt (Opt Bool)))(declare-const d (Opt (Opt Bool)))\n\
         (assert (distinct a b c d))\n(check-sat)\n"
    );
    assert_result(&smt, "sat");
}

/// UNSAT: `(Opt (Opt (Opt Bool)))` has 5 inhabitants; 6 distinct is impossible.
#[test]
#[timeout(60_000)]
fn test_parametric_finite_cardinality_deeper_6_distinct_unsat() {
    let smt = format!(
        "(set-logic ALL)\n{OPT_DECL}\n\
         (declare-const a (Opt (Opt (Opt Bool))))(declare-const b (Opt (Opt (Opt Bool))))\
         (declare-const c (Opt (Opt (Opt Bool))))(declare-const d (Opt (Opt (Opt Bool))))\
         (declare-const e (Opt (Opt (Opt Bool))))(declare-const f (Opt (Opt (Opt Bool))))\n\
         (assert (distinct a b c d e f))\n(check-sat)\n"
    );
    assert_result(&smt, "unsat");
}

/// UNSAT: `(Opt (Opt (_ BitVec 1)))` has 4 inhabitants; 5 distinct is impossible.
#[test]
#[timeout(60_000)]
fn test_parametric_finite_cardinality_bitvec_nested_unsat() {
    let smt = format!(
        "(set-logic ALL)\n{OPT_DECL}\n\
         (declare-const a (Opt (Opt (_ BitVec 1))))(declare-const b (Opt (Opt (_ BitVec 1))))\
         (declare-const c (Opt (Opt (_ BitVec 1))))(declare-const d (Opt (Opt (_ BitVec 1))))\
         (declare-const e (Opt (Opt (_ BitVec 1))))\n\
         (assert (distinct a b c d e))\n(check-sat)\n"
    );
    assert_result(&smt, "unsat");
}

/// SAT: a genuinely RECURSIVE instance `(Lst Bool)` is infinite, so any finite
/// `distinct` clique is satisfiable (must NOT be mis-classified as finite).
#[test]
#[timeout(60_000)]
fn test_parametric_recursive_instance_distinct_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 1)) ((par (T) ((lnil) (lcons (lhd T) (ltl (Lst T)))))))
        (declare-const a (Lst Bool))(declare-const b (Lst Bool))(declare-const c (Lst Bool))
        (declare-const d (Lst Bool))(declare-const e (Lst Bool))
        (assert (distinct a b c d e))
        (check-sat)
    "#;
    assert_result(smt, "sat");
}

/// `(get-value ...)` and `(get-model)` must print USER-FACING constructor/
/// selector names (`osome`, `oval`), never the instance-mangled internals.
#[test]
#[timeout(60_000)]
fn test_parametric_model_prints_surface_names() {
    let smt = format!(
        "(set-logic ALL)\n{OPT_DECL}\n\
         (declare-const x (Opt Int))\n(assert (= x (osome 5)))\n(check-sat)\n\
         (get-value (x (oval x)))\n(get-model)\n"
    );
    let output = crate::common::solve(&smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        !output.contains('@'),
        "model/get-value leaked an instance-mangled name:\n{output}"
    );
    assert!(
        output.contains("osome"),
        "expected surface constructor name `osome` in output:\n{output}"
    );
}

/// `(get-value ...)` echoes the ORIGINAL requested term as the key (SMT-LIB
/// spec), not an internally-rewritten form. A single-constructor (struct)
/// datatype constant `w` is eagerly eliminated to `(wrap <field>)`; the key must
/// still read `w` / `(item w)`, never the eliminated `(wrap w!item...)` /
/// fresh-field-var form (and never an instance-mangled `@`).
#[test]
#[timeout(60_000)]
fn test_parametric_single_ctor_get_value_echoes_original_term() {
    let smt = "(set-logic ALL)\n\
        (declare-datatypes ((Wrap 1)) ((par (T) ((wrap (item T))))))\n\
        (declare-const w (Wrap Int))\n(assert (= (item w) 42))\n(check-sat)\n\
        (get-value (w (item w)))\n";
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    // Original-term keys, correct values, no eliminated/mangled leak.
    assert!(
        output.contains("(w (wrap 42))"),
        "key `w` not echoed verbatim:\n{output}"
    );
    assert!(
        output.contains("((item w) 42)"),
        "key `(item w)` not echoed verbatim:\n{output}"
    );
    assert!(
        !output.contains("w!item") && !output.contains('@'),
        "get-value leaked an internal/eliminated name:\n{output}"
    );
}
