// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mandatory certification of refutations whose array axioms the term store
//! folded.
//!
//! The array axiom sites build equality conclusions such as
//! `(or (not (= c S)) (= v (select c x)))`; when `v` is the constant `true` the
//! term store folds the equality to the atom `(select c x)` (and to
//! `(not (select c x))` for `false`). The checker's read-over-write schemas
//! only matched an equality conclusion, so
//! `recognize_array_theory_lemma` answered `None`, the axiom was recorded as
//! `Generic`, and an explicit proof request answered `unknown` with `step t0
//! uses unsupported theory lemma kind Generic in strict mode` although each of
//! these queries is unsat (z3 5.1.0 agrees).

use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;

/// `store_value_cong` under `c = (store (const false) #x42 true)`.
const BV_STORE_VALUE_READ: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 32) Bool))
    (declare-const c (Array (_ BitVec 32) Bool))
    (assert (select a #x00000042))
    (assert (or (not (select a #x00000042))
                (= c (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000042 true))))
    (assert (not (select c #x00000042)))
"#;

/// `array_cong_select` under `c = (const true)`: the store of `true` into the
/// `true` constant array folds away, and so does the constant read.
const BV_CONST_ARRAY_READ: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 32) Bool))
    (declare-const b Bool)
    (declare-const c (Array (_ BitVec 32) Bool))
    (assert (select a #x00000042))
    (assert (or (and (not (select a #x00000042)) (not b))
                (= c (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000042 true))))
    (assert (not (select c #x00000007)))
"#;

/// A `true` element over an `Int` carrier: the lowering reaches the pinned
/// checker's `arrays_idx` and closes the fold with `equiv_simplify`.
const INT_TRUE_READ: &str = r#"
    (set-logic QF_AUFLIA)
    (declare-const a (Array Int Bool))
    (declare-const c (Array Int Bool))
    (declare-const d (Array Int Bool))
    (assert (select a 66))
    (assert (or (not (select a 66)) (= c (store d 66 true))))
    (assert (not (select c 66)))
"#;

/// A `false` element: the folded literal is the NEGATED atom.
const INT_FALSE_READ: &str = r#"
    (set-logic QF_AUFLIA)
    (declare-const c (Array Int Bool))
    (declare-const d (Array Int Bool))
    (declare-const p Bool)
    (assert (or p (= c (store d 3 false))))
    (assert (not p))
    (assert (select c 3))
"#;

/// `row1_clause` with `true` stored: `(or (not (= i k)) (select (store a i
/// true) k))`.
const ROW1_TRUE_STORE: &str = r#"
    (set-logic QF_AUFLIA)
    (declare-const a (Array Int Bool))
    (declare-const i Int)
    (declare-const k Int)
    (assert (<= i k))
    (assert (<= k i))
    (assert (not (select (store a i true) k)))
"#;

/// `row2_clause` over a `true` constant base: the base read folds to `true`.
const ROW2_CONST_TRUE_BASE: &str = r#"
    (set-logic QF_AUFLIA)
    (declare-const i Int)
    (declare-const k Int)
    (declare-const v Bool)
    (assert (< i k))
    (assert (not (select (store ((as const (Array Int Bool)) true) i v) k)))
"#;

/// `row2_clause` over a `false` constant base: the folded literal is negated.
const ROW2_CONST_FALSE_BASE: &str = r#"
    (set-logic QF_AUFLIA)
    (declare-const i Int)
    (declare-const k Int)
    (declare-const v Bool)
    (assert (< i k))
    (assert (select (store ((as const (Array Int Bool)) false) i v) k))
"#;

/// `store_value_cong` over a store/store equality, folded sub-schema (I):
/// `(or p (not (= (store X i p) (store Y i true))))`.
const SAME_INDEX_STORE_VALUE: &str = r#"
    (set-logic QF_AUFLIA)
    (declare-const X (Array Int Bool))
    (declare-const Y (Array Int Bool))
    (declare-const i Int)
    (declare-const p Bool)
    (declare-const q Bool)
    (assert (or q (= (store X i p) (store Y i true))))
    (assert (not q))
    (assert (not p))
"#;

/// Solve under an explicit proof request, check the retained refutation
/// strictly, and return the published `(get-proof)` document.
fn certified_document(script: &str) -> String {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor
        .execute_all(&parse(&format!("{script}(check-sat)\n(get-proof)\n")).unwrap())
        .unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "the query is unsat (z3 5.1.0) and the refutation must survive mandatory \
         certification: {outputs:?}"
    );
    let proof = executor
        .last_proof()
        .expect("a certified UNSAT keeps its proof");
    let has_kind = |wanted: TheoryLemmaKind| {
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if *kind == wanted))
    };
    assert!(
        has_kind(TheoryLemmaKind::ArrayRowChain),
        "the folded axiom must carry the checker's ArrayRowChain kind"
    );
    assert!(
        !has_kind(TheoryLemmaKind::Generic),
        "no Generic lemma may remain in the certified refutation"
    );
    ay_proof::check_proof_strict(proof, executor.terms())
        .expect("the plain strict checker must accept the refutation");
    let document = outputs.get(1).expect("published proof").clone();
    assert!(!document.contains(":rule trust"), "{document}");
    document
}

/// Before the fix: `unknown`, `step t0 uses unsupported theory lemma kind
/// Generic in strict mode`. The BV index keeps an honest printer `hole`.
#[test]
fn bv_store_value_read_is_strictly_certified() {
    certified_document(BV_STORE_VALUE_READ);
}

/// The constant-array read has no pinned-checker primitive, so its document
/// stays honestly holey; the internal certification is what changed.
#[test]
fn bv_const_array_read_is_strictly_certified() {
    certified_document(BV_CONST_ARRAY_READ);
}

#[test]
fn int_true_read_publishes_a_hole_free_document() {
    let document = certified_document(INT_TRUE_READ);
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(document.contains(":rule equiv_simplify"), "{document}");
}

#[test]
fn int_false_read_publishes_a_hole_free_document() {
    let document = certified_document(INT_FALSE_READ);
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(document.contains(":rule equiv_simplify"), "{document}");
}

/// Folded ROW1 and folded (A) have no lowering, so their lemma keeps an honest
/// `hole` in the document; the internal certification is what changed.
#[test]
fn folded_row1_and_row2_over_a_constant_base_are_strictly_certified() {
    for script in [ROW1_TRUE_STORE, ROW2_CONST_TRUE_BASE, ROW2_CONST_FALSE_BASE] {
        certified_document(script);
    }
}

#[test]
fn folded_same_index_store_value_publishes_a_hole_free_document() {
    let document = certified_document(SAME_INDEX_STORE_VALUE);
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(document.contains(":rule equiv_simplify"), "{document}");
}
