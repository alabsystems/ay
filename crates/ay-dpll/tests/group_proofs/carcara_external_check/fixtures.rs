// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use folded_atom_assumptions::published_assumption_scope;

static TEMP_FILE_SEQ: AtomicU64 = AtomicU64::new(0);

const QF_BOOL_UNSAT: &str = r#"
(set-logic QF_BOOL)
(declare-const a Bool)
(assert a)
(assert (not a))
(check-sat)
"#;

const QF_LRA_UNSAT: &str = r#"
(set-logic QF_LRA)
(declare-const x Real)
(assert (<= x 5.0))
(assert (>= x 10.0))
(check-sat)
"#;

const QF_UF_UNSAT: &str = r#"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
(check-sat)
"#;

const UF_AUTHORED_WITNESS_FORALL_CONFLICT_UNSAT: &str = r#"
(set-logic UF)
(declare-sort U 0)
(declare-const authored_w U)
(declare-fun p (U) Bool)
(declare-fun q (U) Bool)
(assert (q authored_w))
(assert (forall ((x U)) (p x)))
(assert (forall ((x U)) (not (p x))))
(check-sat)
"#;

const QF_DT_FINITE_ENUM_PIGEONHOLE_UNSAT: &str = r#"
(set-logic QF_DT)
(declare-datatype Unit ((u0) (u1) (u2)))
(declare-const p0 Unit)
(declare-const p1 Unit)
(declare-const p2 Unit)
(declare-const p3 Unit)
(assert (not (= p0 p1)))
(assert (not (= p0 p2)))
(assert (not (= p0 p3)))
(assert (not (= p1 p2)))
(assert (not (= p1 p3)))
(assert (not (= p2 p3)))
(check-sat)
"#;

// Carcara 1.1.0 has no datatype parser or exhaustiveness rule. Give its proof
// checker the exact six authored assumptions over an uninterpreted carrier so
// it can validate every `assume` and resolution around the explicit `hole`.
// AY still solves and natively checks the real datatype problem above; this
// erased checker scope cannot turn the missing exhaustiveness inference into a
// valid external proof, and the required verdict remains `holey`.
const QF_DT_FINITE_ENUM_PIGEONHOLE_CARCARA_SCOPE: &str = r#"
(set-logic QF_UF)
(declare-sort Unit 0)
(declare-const p0 Unit)
(declare-const p1 Unit)
(declare-const p2 Unit)
(declare-const p3 Unit)
(assert (not (= p0 p1)))
(assert (not (= p0 p2)))
(assert (not (= p0 p3)))
(assert (not (= p1 p2)))
(assert (not (= p1 p3)))
(assert (not (= p2 p3)))
(check-sat)
"#;

const QF_UF_COMPOSED_AUTHORED_ROOT_UNSAT: &str = r#"
(set-logic QF_UF)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (not (=> (and (= x y) (= y z)) (= x z))))
(check-sat)
"#;

const QF_LIA_COMPOSED_AUTHORED_ROOT_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (not (=> (and (= x 2) (= y 3)) (= (+ x y) 5))))
(check-sat)
"#;

const QF_AUFLIA_COMPOSED_ROW2_ROOT_UNSAT: &str = r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const j Int)
(declare-const v Int)
(assert
  (not
    (=> (not (= i j))
        (= (select (store a i v) j) (select a j)))))
(check-sat)
"#;

// Carcara 1.1.0 has no `store_permutation` rule (probed: `unknown rule`), so
// AY's n-ary store-commutativity lemma used to export as an unchecked `hole`.
// It is now DERIVED from the rules carcara does implement: `arrays_ext`
// supplies the extensionality witness, the four cases on that witness reduce
// through `arrays_row` / `arrays_idx` / `cong` / `trans`, and the carried index
// disequality kills the case where the witness is both indices at once.
const QF_AUFLIA_STORE_PERMUTATION_UNSAT: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(declare-fun w () Int)
(assert (not (= i j)))
(assert (not (= (store (store a i v) j w) (store (store a j w) i v))))
(check-sat)
"#;

// The same schema at chain length three: the permutation is factored into
// ADJACENT transpositions, so this one additionally exercises lifting a
// transposition back out through an untouched outer store with `cong` and
// composing three of them with `trans`.
const QF_AUFLIA_STORE_PERMUTATION_CHAIN3_UNSAT: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun v3 () Int)
(assert (not (= i1 i2)))
(assert (not (= i1 i3)))
(assert (not (= i2 i3)))
(assert
  (not (= (store (store (store a i1 v1) i2 v2) i3 v3)
          (store (store (store a i3 v3) i2 v2) i1 v1))))
(check-sat)
"#;

// A store chain that mentions a user symbol literally named `x`. The
// transposition derivation inlines the printed chains into the scope of the
// `arrays_ext` witness's `choice` binder — also literally `x` — so lowering
// this chain would CAPTURE the user symbol and publish a document that claims
// a different term than the checker constructs (carcara-`invalid`). The
// lowering must decline and keep the honest `hole` instead.
const QF_AUFLIA_STORE_PERMUTATION_BINDER_COLLISION_UNSAT: &str = r#"
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun x () Int)
(declare-fun w () Int)
(assert (not (= i j)))
(assert (not (= (store (store a i x) j w) (store (store a j w) i x))))
(check-sat)
"#;

const QF_LIA_LINEAR_AND_FOLD_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (and (<= (+ (* 1 x0) (* (- 1) x0)) (- 1))
             (<= (+ (* 1 x1) (* 0 x0)) 0)))
(check-sat)
"#;

const QF_LIA_LITERAL_FALSE_UNSAT: &str = r#"
(set-logic QF_LIA)
(assert false)
(check-sat)
"#;

const QF_LIA_MOD_ASSUMING_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= (mod x 2) 0))
(check-sat-assuming ((= (mod x 2) 1)))
"#;

// Carcara 1.1.0 does not expose `check-sat-assuming` literals as original
// premises to its Alethe checker.  Replay the same active query scope as
// assertions so the independent checker can authenticate every `assume`
// command emitted for the query.  AY still produces the proof from the
// `check-sat-assuming` problem above, so this does not weaken its per-query
// authority boundary.
const QF_LIA_MOD_ASSUMING_CARCARA_SCOPE: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (= (mod x 2) 0))
(assert (= (mod x 2) 1))
(check-sat)
"#;

const QF_AUFLIA_LINEAR_ASSUMING_UNSAT: &str = r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const x Int)
(assert (= (select a 0) x))
(check-sat-assuming ((> x 0) (<= (select a 0) 0)))
"#;

const QF_AUFLIA_LINEAR_ASSUMING_CARCARA_SCOPE: &str = r#"
(set-logic QF_AUFLIA)
(declare-const a (Array Int Int))
(declare-const x Int)
(assert (= (select a 0) x))
(assert (< 0 x))
(assert (<= (select a 0) 0))
(check-sat)
"#;

const QF_LRA_GUARDED_SPLIT_UNSAT: &str = r#"
(set-logic QF_LRA)
(declare-const gate Bool)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= x 1.0))
(assert (= y 0.0))
(assert (= z 1.0))
(assert (not gate))
(assert (or gate (not (= (+ x y) z))))
(check-sat)
"#;

const QF_LIA_LET_LINEAR_AND_FOLD_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (let ((?v_0 (* 1 x0)) (?v_1 (* (- 1) x0)))
  (and (<= (+ ?v_0 ?v_1) (- 1))
       (<= (+ (* 1 x1) (* 0 x0)) 0))))
(check-sat)
"#;

const QF_LIA_UNSAT: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
"#;

fn arithmetic_ite_nonnegative_problem(
    extra_setup: &str,
    definition: &str,
    contradiction: &str,
) -> String {
    format!(
        r#"
(set-logic QF_LIA)
(declare-const A Int)
(declare-const B Int)
(declare-const C Int)
(declare-const D Int)
(declare-const E Int)
(declare-const F Int)
(declare-const G Int)
(declare-const H Int)
(declare-const I Int)
(declare-const J Int)
{extra_setup}
{definition}
(assert (= H (+ C F)))
(assert (= G (+ B 1)))
(assert (= F (+ A 1)))
(assert (= E (+ D G)))
(assert (>= D 0))
(assert (>= A 0))
(assert (>= B 0))
(assert (>= C 0))
{contradiction}
(check-sat)
"#
    )
}

const QF_UFLIA_UNSAT: &str = r#"
(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (>= x 5))
(assert (<= x 5))
(assert (= y 5))
(assert (= (f x) 10))
(assert (= (f y) 20))
(check-sat)
"#;

const AUFLIA_EMATCHING_FORALL_EQUALITY_UNSAT: &str = r#"
(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)))))
(assert (= (f 7) (- 1)))
(check-sat)
"#;

const QF_ABV_PINNED_CONCAT_UNSAT: &str = r#"
(set-logic QF_ABV)
(declare-const tbl (Array (_ BitVec 24) (_ BitVec 32)))
(declare-const op (_ BitVec 8))
(declare-const lhs (_ BitVec 8))
(declare-const rhs (_ BitVec 8))
(declare-const out (_ BitVec 32))
(assert (= out (select tbl (concat op (concat lhs rhs)))))
(assert (= op #x01))
(assert (= (select tbl (concat #x01 (concat #x3f #x40))) #x40400000))
(assert (= lhs #x3f))
(assert (= rhs #x40))
(assert (distinct out #x40400000))
(check-sat)
"#;
