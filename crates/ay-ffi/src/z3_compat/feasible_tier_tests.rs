// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the "feasible-tier" Z3 C-API closings: char theory, special-relation
//! orders, quantifier `:qid`/`:skolemid` + de-Bruijn index, and
//! `Z3_solver_get_levels`.
//!
//! SOUNDNESS-CRITICAL cases (a Z3-UNSAT that MUST stay UNSAT in AY) are marked;
//! every order/char verdict here was cross-checked against libz3 4.16.0.

use super::super::*;
use std::ffi::CStr;

unsafe fn ctx() -> Z3_context {
    unsafe {
        let cfg = Z3_mk_config();
        let c = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        c
    }
}

unsafe fn sym(c: Z3_context, name: &CStr) -> Z3_symbol {
    unsafe { Z3_mk_string_symbol(c, name.as_ptr()) }
}

// ============================================================================
// Char theory
// ============================================================================

#[test]
fn char_free_const_carries_range_invariant() {
    // SOUNDNESS: a free Char `c` obeys `0 <= c <= 196607`, so `196607 < c` is
    // UNSAT and `c < 0` is UNSAT — a fresh Char is NEVER an unbounded Int.
    unsafe {
        let c = ctx();
        let char_sort = Z3_mk_char_sort(c);
        let int = Z3_mk_int_sort(c);
        let cc = Z3_mk_const(c, sym(c, c"cc"), char_sort);

        // 196607 < cc  → UNSAT
        let hi = Z3_mk_int(c, 196607, int);
        let s1 = Z3_mk_solver(c);
        Z3_solver_assert(c, s1, Z3_mk_lt(c, hi, cc));
        assert_eq!(
            Z3_solver_check(c, s1),
            Z3_L_FALSE,
            "196607 < char must be UNSAT"
        );

        // cc < 0  → UNSAT
        let zero = Z3_mk_int(c, 0, int);
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_lt(c, cc, zero));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE, "char < 0 must be UNSAT");

        // An in-range value is SAT: 0 <= cc <= 196607 has models (e.g. cc = 65).
        let s3 = Z3_mk_solver(c);
        Z3_solver_assert(c, s3, Z3_mk_eq(c, cc, Z3_mk_int(c, 65, int)));
        assert_eq!(Z3_solver_check(c, s3), Z3_L_TRUE, "char = 65 must be SAT");

        Z3_del_context(c);
    }
}

#[test]
fn char_le_is_antisymmetric_and_total() {
    unsafe {
        let c = ctx();
        let char_sort = Z3_mk_char_sort(c);
        let a = Z3_mk_const(c, sym(c, c"a"), char_sort);
        let b = Z3_mk_const(c, sym(c, c"b"), char_sort);

        // SOUNDNESS: char.<= antisymmetry: (a<=b) & (b<=a) & a!=b → UNSAT.
        let ab = Z3_mk_char_le(c, a, b);
        let ba = Z3_mk_char_le(c, b, a);
        let ne = Z3_mk_not(c, Z3_mk_eq(c, a, b));
        let conj = [ab, ba, ne];
        let s1 = Z3_mk_solver(c);
        Z3_solver_assert(c, s1, Z3_mk_and(c, 3, conj.as_ptr()));
        assert_eq!(Z3_solver_check(c, s1), Z3_L_FALSE, "char_le antisymmetry");

        // char.<= totality: not(a<=b) & not(b<=a) → UNSAT (Int order is total).
        let n_ab = Z3_mk_not(c, Z3_mk_char_le(c, a, b));
        let n_ba = Z3_mk_not(c, Z3_mk_char_le(c, b, a));
        let conj2 = [n_ab, n_ba];
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_and(c, 2, conj2.as_ptr()));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE, "char_le totality");

        // A strict order IS satisfiable: (a<=b) & a!=b → SAT.
        let s3 = Z3_mk_solver(c);
        Z3_solver_assert(c, s3, Z3_mk_char_le(c, a, b));
        Z3_solver_assert(c, s3, Z3_mk_not(c, Z3_mk_eq(c, a, b)));
        assert_eq!(Z3_solver_check(c, s3), Z3_L_TRUE, "a<=b & a!=b SAT");

        Z3_del_context(c);
    }
}

#[test]
fn char_is_digit_boundary() {
    // Boundary code points 47/48/57/58: is_digit iff in 48..=57.
    unsafe {
        let c = ctx();
        for (cp, is_digit) in [(47u32, false), (48, true), (57, true), (58, false)] {
            let lit = Z3_mk_char(c, cp);
            let d = Z3_mk_char_is_digit(c, lit);
            // Assert is_digit(lit): SAT iff the digit predicate holds.
            let s = Z3_mk_solver(c);
            Z3_solver_assert(c, s, d);
            let got = Z3_solver_check(c, s) == Z3_L_TRUE;
            assert_eq!(got, is_digit, "is_digit({cp}) expected {is_digit}");
        }
        Z3_del_context(c);
    }
}

#[test]
fn char_to_int_is_identity_codepoint() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let c65 = Z3_mk_char(c, 65);
        let ci = Z3_mk_char_to_int(c, c65);
        // Result reports Int sort.
        assert_eq!(Z3_get_sort_kind(c, Z3_get_sort(c, ci)), Z3_INT_SORT);
        // char.to_int(char(65)) = 65  → asserting the negation is UNSAT.
        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, Z3_mk_not(c, Z3_mk_eq(c, ci, Z3_mk_int(c, 65, int))));
        assert_eq!(
            Z3_solver_check(c, s),
            Z3_L_FALSE,
            "char.to_int(65) must equal 65"
        );
        Z3_del_context(c);
    }
}

#[test]
fn mk_char_rejects_out_of_range() {
    unsafe {
        let c = ctx();
        assert_eq!(Z3_mk_char(c, 196608), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

// ============================================================================
// Special-relation orders
// ============================================================================

/// Build an uninterpreted sort S with three distinct consts a,b,c.
unsafe fn order_scaffold(c: Z3_context) -> (Z3_sort, Z3_ast, Z3_ast, Z3_ast) {
    unsafe {
        let s = Z3_mk_uninterpreted_sort(c, sym(c, c"S"));
        let a = Z3_mk_const(c, sym(c, c"a"), s);
        let b = Z3_mk_const(c, sym(c, c"b"), s);
        let cc = Z3_mk_const(c, sym(c, c"cc"), s);
        (s, a, b, cc)
    }
}

unsafe fn app2(c: Z3_context, f: Z3_func_decl, x: Z3_ast, y: Z3_ast) -> Z3_ast {
    unsafe {
        let args = [x, y];
        Z3_mk_app(c, f, 2, args.as_ptr())
    }
}

#[test]
fn linear_order_soundness() {
    unsafe {
        let c = ctx();
        let (s, a, b, cc) = order_scaffold(c);
        let r = Z3_mk_linear_order(c, s, 0);
        assert!(!r.is_null(), "linear_order must be a REAL func_decl");

        // SOUNDNESS: antisymmetry — R(a,b) & R(b,a) & a!=b → UNSAT.
        let s1 = Z3_mk_solver(c);
        let conj = [
            app2(c, r, a, b),
            app2(c, r, b, a),
            Z3_mk_not(c, Z3_mk_eq(c, a, b)),
        ];
        Z3_solver_assert(c, s1, Z3_mk_and(c, 3, conj.as_ptr()));
        assert_eq!(Z3_solver_check(c, s1), Z3_L_FALSE, "LO antisymmetry");

        // SOUNDNESS: a strict 3-cycle a<b<c<a → UNSAT (antisym + trans).
        let s2 = Z3_mk_solver(c);
        let distinct = [a, b, cc];
        let cyc = [
            app2(c, r, a, b),
            app2(c, r, b, cc),
            app2(c, r, cc, a),
            Z3_mk_distinct(c, 3, distinct.as_ptr()),
        ];
        Z3_solver_assert(c, s2, Z3_mk_and(c, 4, cyc.as_ptr()));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE, "LO 3-cycle");

        // totality: incomparable a,b (not R(a,b) & not R(b,a) & a!=b) → UNSAT.
        let s3 = Z3_mk_solver(c);
        let incomp = [
            Z3_mk_not(c, app2(c, r, a, b)),
            Z3_mk_not(c, app2(c, r, b, a)),
            Z3_mk_not(c, Z3_mk_eq(c, a, b)),
        ];
        Z3_solver_assert(c, s3, Z3_mk_and(c, 3, incomp.as_ptr()));
        assert_eq!(Z3_solver_check(c, s3), Z3_L_FALSE, "LO totality");

        // A consistent chain a<b<c IS satisfiable.
        let s4 = Z3_mk_solver(c);
        let chain = [
            app2(c, r, a, b),
            app2(c, r, b, cc),
            app2(c, r, a, cc),
            Z3_mk_distinct(c, 3, distinct.as_ptr()),
        ];
        Z3_solver_assert(c, s4, Z3_mk_and(c, 4, chain.as_ptr()));
        assert_eq!(Z3_solver_check(c, s4), Z3_L_TRUE, "LO chain SAT");

        Z3_del_context(c);
    }
}

#[test]
fn partial_order_soundness() {
    unsafe {
        let c = ctx();
        let (s, a, b, _cc) = order_scaffold(c);
        let r = Z3_mk_partial_order(c, s, 0);
        assert!(!r.is_null());

        // SOUNDNESS: antisymmetry holds for a partial order too → UNSAT.
        let s1 = Z3_mk_solver(c);
        let conj = [
            app2(c, r, a, b),
            app2(c, r, b, a),
            Z3_mk_not(c, Z3_mk_eq(c, a, b)),
        ];
        Z3_solver_assert(c, s1, Z3_mk_and(c, 3, conj.as_ptr()));
        assert_eq!(Z3_solver_check(c, s1), Z3_L_FALSE, "PO antisymmetry");

        // A partial order need NOT be total: incomparable a,b is SAT.
        let s2 = Z3_mk_solver(c);
        let incomp = [
            Z3_mk_not(c, app2(c, r, a, b)),
            Z3_mk_not(c, app2(c, r, b, a)),
            Z3_mk_not(c, Z3_mk_eq(c, a, b)),
        ];
        Z3_solver_assert(c, s2, Z3_mk_and(c, 3, incomp.as_ptr()));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_TRUE, "PO incomparable SAT");

        Z3_del_context(c);
    }
}

#[test]
fn tree_and_piecewise_order_soundness() {
    unsafe {
        let c = ctx();

        // tree order: the DOWN-set of a node is linearly ordered → two elements
        // both below `a`, mutually incomparable, is UNSAT; but the UP-set need
        // not be linear → two elements both above `a`, incomparable, is SAT.
        {
            let (s, a, b, cc) = order_scaffold(c);
            let r = Z3_mk_tree_order(c, s, 0);
            assert!(!r.is_null());

            let s1 = Z3_mk_solver(c);
            let downset = [
                app2(c, r, b, a),
                app2(c, r, cc, a),
                Z3_mk_not(c, app2(c, r, b, cc)),
                Z3_mk_not(c, app2(c, r, cc, b)),
                Z3_mk_distinct(c, 3, [a, b, cc].as_ptr()),
            ];
            Z3_solver_assert(c, s1, Z3_mk_and(c, 5, downset.as_ptr()));
            assert_eq!(Z3_solver_check(c, s1), Z3_L_FALSE, "tree down-set linear");

            let s2 = Z3_mk_solver(c);
            let upset = [
                app2(c, r, a, b),
                app2(c, r, a, cc),
                Z3_mk_not(c, app2(c, r, b, cc)),
                Z3_mk_not(c, app2(c, r, cc, b)),
                Z3_mk_distinct(c, 3, [a, b, cc].as_ptr()),
            ];
            Z3_solver_assert(c, s2, Z3_mk_and(c, 5, upset.as_ptr()));
            assert_eq!(
                Z3_solver_check(c, s2),
                Z3_L_TRUE,
                "tree up-set need not be linear"
            );
        }

        // piecewise-linear order: BOTH down-set and up-set are linear → the
        // up-set-not-linear case that was SAT for a tree is now UNSAT.
        {
            let (s, a, b, cc) = order_scaffold(c);
            let r = Z3_mk_piecewise_linear_order(c, s, 1);
            assert!(!r.is_null());

            let s3 = Z3_mk_solver(c);
            let upset = [
                app2(c, r, a, b),
                app2(c, r, a, cc),
                Z3_mk_not(c, app2(c, r, b, cc)),
                Z3_mk_not(c, app2(c, r, cc, b)),
                Z3_mk_distinct(c, 3, [a, b, cc].as_ptr()),
            ];
            Z3_solver_assert(c, s3, Z3_mk_and(c, 5, upset.as_ptr()));
            assert_eq!(
                Z3_solver_check(c, s3),
                Z3_L_FALSE,
                "piecewise up-set linear"
            );
        }

        Z3_del_context(c);
    }
}

#[test]
fn special_order_cache_and_tc_decl() {
    unsafe {
        let c = ctx();
        let s = Z3_mk_uninterpreted_sort(c, sym(c, c"S"));
        // Same (kind, sort, id) → identical cached func_decl.
        let r1 = Z3_mk_linear_order(c, s, 7);
        let r2 = Z3_mk_linear_order(c, s, 7);
        assert_eq!(r1, r2, "same (kind,sort,id) must return the same decl");
        // A different id → a different relation.
        let r3 = Z3_mk_linear_order(c, s, 8);
        assert_ne!(r1, r3);

        // transitive_closure: REAL decl; same relation → identical decl
        // (libz3 parity, probed 2026-07-09).
        let f = Z3_mk_func_decl(c, sym(c, c"f"), 2, [s, s].as_ptr(), Z3_mk_bool_sort(c));
        let tc1 = Z3_mk_transitive_closure(c, f);
        assert!(
            !tc1.is_null(),
            "transitive closure must be a REAL func_decl"
        );
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let tc2 = Z3_mk_transitive_closure(c, f);
        assert_eq!(tc1, tc2, "same relation must return the same TC decl");

        // Validation mirrors libz3's classes (both raise errors there):
        // unary decl → mismatched/missing domain pair.
        let f1 = Z3_mk_func_decl(c, sym(c, c"f1"), 1, [s].as_ptr(), Z3_mk_bool_sort(c));
        assert!(Z3_mk_transitive_closure(c, f1).is_null());
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        // non-Bool range → "tc relation should be Boolean".
        let f3 = Z3_mk_func_decl(c, sym(c, c"f3"), 2, [s, s].as_ptr(), s);
        assert!(Z3_mk_transitive_closure(c, f3).is_null());
        assert_ne!(Z3_get_error_code(c), Z3_OK);
        Z3_del_context(c);
    }
}

#[test]
fn transitive_closure_unsat_cases_match_z3() {
    // SOUNDNESS (all three verdicts cross-checked against libz3 4.16.0,
    // 2026-07-09): Z3's TC is the REFLEXIVE-transitive closure.
    unsafe {
        let c = ctx();
        let (s, a, b, _cc) = order_scaffold(c);
        let f = Z3_mk_func_decl(c, sym(c, c"R"), 2, [s, s].as_ptr(), Z3_mk_bool_sort(c));
        let tc = Z3_mk_transitive_closure(c, f);
        assert!(!tc.is_null());

        // ¬TC(a,a) → UNSAT (reflexivity; z3: unsat even with no R facts).
        let s0 = Z3_mk_solver(c);
        Z3_solver_assert(c, s0, Z3_mk_not(c, app2(c, tc, a, a)));
        assert_eq!(Z3_solver_check(c, s0), Z3_L_FALSE, "TC reflexivity");

        // R(a,b) ∧ ¬TC(a,b) → UNSAT (inclusion).
        let s1 = Z3_mk_solver(c);
        Z3_solver_assert(c, s1, app2(c, f, a, b));
        Z3_solver_assert(c, s1, Z3_mk_not(c, app2(c, tc, a, b)));
        assert_eq!(Z3_solver_check(c, s1), Z3_L_FALSE, "R ⊆ TC");

        // Cycle a→b→a with ¬TC(a,a) is UNSAT already by reflexivity; the
        // sharper transitivity case: R(a,b) ∧ R(b,a) ∧ ¬TC(b,b) → UNSAT.
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, app2(c, f, a, b));
        Z3_solver_assert(c, s2, app2(c, f, b, a));
        Z3_solver_assert(c, s2, Z3_mk_not(c, app2(c, tc, b, b)));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE, "cycle closure");

        Z3_del_context(c);
    }
}

#[test]
fn transitive_closure_sat_is_model_check_gated() {
    unsafe {
        let c = ctx();
        let (s, a, b, _cc) = order_scaffold(c);
        let f = Z3_mk_func_decl(c, sym(c, c"R"), 2, [s, s].as_ptr(), Z3_mk_bool_sort(c));
        let tc = Z3_mk_transitive_closure(c, f);
        assert!(!tc.is_null());

        // VERIFIABLE SAT (z3: sat): R(a,b) ∧ TC(a,b) ∧ ¬TC(b,a) ∧ a≠b.
        // The gate releases SAT only after Warshall over the model universe
        // confirms the TC table IS the reflexive-transitive closure of R.
        let s1 = Z3_mk_solver(c);
        Z3_solver_assert(c, s1, app2(c, f, a, b));
        Z3_solver_assert(c, s1, app2(c, tc, a, b));
        Z3_solver_assert(c, s1, Z3_mk_not(c, app2(c, tc, b, a)));
        Z3_solver_assert(c, s1, Z3_mk_distinct(c, 2, [a, b].as_ptr()));
        let v1 = Z3_solver_check(c, s1);
        assert_ne!(v1, Z3_L_FALSE, "z3-SAT case must never flip to UNSAT");
        assert_eq!(v1, Z3_L_TRUE, "verifiable TC model must pass the SAT gate");

        // MINIMALITY (z3: UNSAT — LFP): ∀xy. R(x,y) ⇔ (x=a ∧ y=b), TC(b,a),
        // a≠b. The partial axioms admit an over-approximated TC ⊇ {(b,a)}, so
        // an ungated engine would answer SAT — the WRONG verdict. The gate
        // must catch the closure mismatch: anything but Z3_L_TRUE is sound
        // (unknown = honest incompleteness; z3 itself proves unsat).
        let s2 = Z3_mk_solver(c);
        let x = Z3_mk_const(c, sym(c, c"x"), s);
        let y = Z3_mk_const(c, sym(c, c"y"), s);
        let rxy = app2(c, f, x, y);
        let defn = Z3_mk_eq(
            c,
            rxy,
            Z3_mk_and(c, 2, [Z3_mk_eq(c, x, a), Z3_mk_eq(c, y, b)].as_ptr()),
        );
        let bound = [x, y];
        let q = Z3_mk_forall_const(c, 0, 2, bound.as_ptr(), 0, ptr::null(), defn);
        Z3_solver_assert(c, s2, q);
        Z3_solver_assert(c, s2, app2(c, tc, b, a));
        Z3_solver_assert(c, s2, Z3_mk_distinct(c, 2, [a, b].as_ptr()));
        let v2 = Z3_solver_check(c, s2);
        assert_ne!(
            v2, Z3_L_TRUE,
            "TC(b,a) outside the closure of R = {{(a,b)}} must NEVER be SAT \
             (z3 proves it unsat; unknown is the honest floor)"
        );
        assert!(
            Z3_solver_get_model(c, s2).is_null(),
            "a TC-rejected candidate is not an admitted public model"
        );

        Z3_del_context(c);
    }
}

// ============================================================================
// Char ↔ BV bridge (width 18, pinned against libz3 4.16.0 — 2026-07-09)
// ============================================================================

#[test]
fn char_to_bv_is_bv18_and_exact() {
    unsafe {
        let c = ctx();
        let char_sort = Z3_mk_char_sort(c);
        let bv18 = Z3_mk_bv_sort(c, 18);

        // Literal char: folds to the exact BV18 literal (z3 agrees on both
        // verdicts and the width).
        let lit = Z3_mk_char_to_bv(c, Z3_mk_char(c, 65));
        assert_ne!(lit, 0, "char_to_bv must be a REAL term");
        assert_eq!(Z3_get_error_code(c), Z3_OK);
        let lit_sort = Z3_get_sort(c, lit);
        assert_eq!(Z3_get_sort_kind(c, lit_sort), Z3_BV_SORT);
        assert_eq!(
            Z3_get_bv_sort_size(c, lit_sort),
            18,
            "char BV width must be 18"
        );
        let s0 = Z3_mk_solver(c);
        Z3_solver_assert(c, s0, Z3_mk_eq(c, lit, Z3_mk_unsigned_int64(c, 65, bv18)));
        assert_eq!(
            Z3_solver_check(c, s0),
            Z3_L_TRUE,
            "to_bv(char 65) = 65 is SAT"
        );
        let s0b = Z3_mk_solver(c);
        Z3_solver_assert(
            c,
            s0b,
            Z3_mk_not(c, Z3_mk_eq(c, lit, Z3_mk_unsigned_int64(c, 65, bv18))),
        );
        assert_eq!(
            Z3_solver_check(c, s0b),
            Z3_L_FALSE,
            "to_bv(char 65) ≠ 65 is UNSAT"
        );

        // Symbolic char: witness encoding; the sort is still BV18.
        let cc = Z3_mk_const(c, sym(c, c"cc"), char_sort);
        let bv = Z3_mk_char_to_bv(c, cc);
        assert_ne!(bv, 0);
        assert_eq!(Z3_get_bv_sort_size(c, Z3_get_sort(c, bv)), 18);
        // Same char term → identical witness term (hash-consing parity).
        assert_eq!(bv, Z3_mk_char_to_bv(c, cc));

        // SOUNDNESS (z3: unsat): to_bv(cc) = 196608 — no char maps above
        // max_char even though 196608 < 2^18 (the BV-side image bound).
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(
            c,
            s2,
            Z3_mk_eq(c, bv, Z3_mk_unsigned_int64(c, 196608, bv18)),
        );
        assert_eq!(
            Z3_solver_check(c, s2),
            Z3_L_FALSE,
            "to_bv(c) = 196608 is UNSAT"
        );

        // z3-SAT case `to_bv(cc) = 65`: pinning a SYMBOLIC char through the
        // bridge sits in the engine's mixed BV+LIA lane, which is honestly
        // incomplete — the verdict must simply never be WRONG (z3: sat).
        let s1 = Z3_mk_solver(c);
        Z3_solver_assert(c, s1, Z3_mk_eq(c, bv, Z3_mk_unsigned_int64(c, 65, bv18)));
        assert_ne!(
            Z3_solver_check(c, s1),
            Z3_L_FALSE,
            "to_bv(c) = 65 must never flip to UNSAT (z3: sat; unknown is the honest floor)"
        );

        // Round trip (z3: unsat): from_bv(to_bv(cc)) ≠ cc.
        let rt = Z3_mk_char_from_bv(c, bv);
        assert_ne!(rt, 0);
        let s3 = Z3_mk_solver(c);
        Z3_solver_assert(c, s3, Z3_mk_not(c, Z3_mk_eq(c, rt, cc)));
        assert_eq!(
            Z3_solver_check(c, s3),
            Z3_L_FALSE,
            "from_bv∘to_bv is the identity"
        );

        Z3_del_context(c);
    }
}

#[test]
fn char_from_bv_width_check_and_range() {
    unsafe {
        let c = ctx();
        // Wrong width → Z3_SORT_ERROR + 0 (libz3: "expected bit-vector sort
        // argument with 18" for widths 8/17/19/32).
        let bv8 = Z3_mk_bv_sort(c, 8);
        let v8 = Z3_mk_unsigned_int64(c, 65, bv8);
        assert_eq!(Z3_mk_char_from_bv(c, v8), 0, "width 8 must be rejected");
        assert_ne!(Z3_get_error_code(c), Z3_OK);

        let bv18 = Z3_mk_bv_sort(c, 18);
        let b = Z3_mk_const(c, sym(c, c"b"), bv18);
        let ch = Z3_mk_char_from_bv(c, b);
        assert_ne!(ch, 0, "width-18 from_bv must be a REAL term");

        // In-range identity (z3: unsat): b ≤ 196607 ∧ to_int(from_bv(b)) ≠
        // bv2int(b).
        let int = Z3_mk_int_sort(c);
        let s1 = Z3_mk_solver(c);
        let le = Z3_mk_bvule(c, b, Z3_mk_unsigned_int64(c, 196607, bv18));
        Z3_solver_assert(c, s1, le);
        let toi = Z3_mk_char_to_int(c, ch);
        let b2i = Z3_mk_bv2int(c, b, false);
        Z3_solver_assert(c, s1, Z3_mk_not(c, Z3_mk_eq(c, toi, b2i)));
        assert_eq!(
            Z3_solver_check(c, s1),
            Z3_L_FALSE,
            "in-range from_bv is bv2int"
        );

        // Out-of-range is INFEASIBLE (z3's char theory wherever it engages —
        // to_int/to_bv/le/eq probes all UNSAT, 2026-07-09):
        // to_int(from_bv(b)) > 196607 → UNSAT.
        let s2 = Z3_mk_solver(c);
        Z3_solver_assert(c, s2, Z3_mk_gt(c, toi, Z3_mk_int(c, 196607, int)));
        assert_eq!(Z3_solver_check(c, s2), Z3_L_FALSE, "no char above max_char");

        // And a concrete SAT witness: from_bv(65) = char 65 (z3: simplifies to
        // (_ Char 65)).
        let s3 = Z3_mk_solver(c);
        let ch65 = Z3_mk_char_from_bv(c, Z3_mk_unsigned_int64(c, 65, bv18));
        Z3_solver_assert(c, s3, Z3_mk_eq(c, ch65, Z3_mk_char(c, 65)));
        assert_eq!(
            Z3_solver_check(c, s3),
            Z3_L_TRUE,
            "from_bv(65) = char(65) is SAT"
        );

        Z3_del_context(c);
    }
}

// ============================================================================
// Quantifier :qid / :skolemid + de-Bruijn index
// ============================================================================

#[test]
fn quantifier_id_and_skolem_id_roundtrip() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        let x = Z3_mk_const(c, sym(c, c"x"), int);
        // body: x >= 0
        let body = Z3_mk_ge(c, x, Z3_mk_int(c, 0, int));
        let bound = [x];
        let qid = sym(c, c"myqid");
        let skid = sym(c, c"myskid");
        let q = Z3_mk_quantifier_const_ex(
            c,
            true,
            0,
            qid,
            skid,
            1,
            bound.as_ptr(),
            0,
            ptr::null(),
            0,
            ptr::null(),
            body,
        );
        assert_ne!(q, 0);

        let got_qid = Z3_get_quantifier_id(c, q);
        assert!(!got_qid.is_null(), "explicit :qid must round-trip");
        let qname = CStr::from_ptr(Z3_get_symbol_string(c, got_qid))
            .to_str()
            .unwrap();
        assert_eq!(qname, "myqid");

        let got_skid = Z3_get_quantifier_skolem_id(c, q);
        assert!(!got_skid.is_null(), "explicit :skolemid must round-trip");
        let sname = CStr::from_ptr(Z3_get_symbol_string(c, got_skid))
            .to_str()
            .unwrap();
        assert_eq!(sname, "myskid");

        // A STRUCTURALLY-DISTINCT quantifier with NO explicit qid → honest null
        // (never fabricated). (It must differ structurally from `q`; a quantifier
        // identical except for its qid hash-conses to the same term — the
        // documented benign metadata caveat.)
        let body2 = Z3_mk_gt(c, x, Z3_mk_int(c, 5, int));
        let q2 = Z3_mk_forall_const(c, 0, 1, bound.as_ptr(), 0, ptr::null(), body2);
        assert!(Z3_get_quantifier_id(c, q2).is_null());

        Z3_del_context(c);
    }
}

#[test]
fn get_index_value_recovers_de_bruijn() {
    unsafe {
        let c = ctx();
        let int = Z3_mk_int_sort(c);
        // Z3_mk_bound encodes the index into the var name (`__db3`).
        let b3 = Z3_mk_bound(c, 3, int);
        assert_eq!(Z3_get_index_value(c, b3), 3);
        let b0 = Z3_mk_bound(c, 0, int);
        assert_eq!(Z3_get_index_value(c, b0), 0);

        // A user-named const is not a de-Bruijn node → honest INVALID_ARG.
        let x = Z3_mk_const(c, sym(c, c"x"), int);
        assert_eq!(Z3_get_index_value(c, x), 0);
        assert_eq!(Z3_get_error_code(c), Z3_INVALID_ARG);
        Z3_del_context(c);
    }
}

// ============================================================================
// Z3_solver_get_levels
// ============================================================================

#[test]
fn solver_get_levels_reports_level_zero_units() {
    unsafe {
        let c = ctx();
        let bools = Z3_mk_bool_sort(c);
        let p = Z3_mk_const(c, sym(c, c"p"), bools);
        let q = Z3_mk_const(c, sym(c, c"q"), bools);
        let r = Z3_mk_const(c, sym(c, c"r"), bools);

        let s = Z3_mk_solver(c);
        Z3_solver_assert(c, s, p); // a level-0 input unit
        let or_pq = Z3_mk_or(c, 2, [p, q].as_ptr());
        Z3_solver_assert(c, s, or_pq); // a compound (not a unit)

        // Query [p, (or p q), r]: p is a level-0 unit → 0; the others → UINT_MAX.
        let vec = Z3_mk_ast_vector(c);
        Z3_ast_vector_push(c, vec, p);
        Z3_ast_vector_push(c, vec, or_pq);
        Z3_ast_vector_push(c, vec, r);
        let mut levels = [12345u32; 3];
        Z3_solver_get_levels(c, s, vec, 3, levels.as_mut_ptr());
        assert_eq!(levels[0], 0, "p is a level-0 input unit");
        assert_eq!(levels[1], u32::MAX, "compound has unknown level");
        assert_eq!(levels[2], u32::MAX, "unasserted literal has unknown level");

        Z3_del_context(c);
    }
}
