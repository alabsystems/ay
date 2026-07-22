// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1 family-classifier unit tests, pinning the verification-consumer demand-campaign
//! vocabularies against their expected family class. Each test builds an
//! `Executor` from an inline smt2 fragment WITHOUT a `(check-sat)` (so the
//! classified `forall` term ids are the raw parsed ones), then drives the shadow
//! classifier directly.

use super::super::model_completion::is_quantifier_consumer_seq_model_completion_quantifier;
use super::FamilyClass;
use crate::Executor;
use ay_frontend::parse;

/// Elaborate `src` (declarations + asserts, NO check-sat) into an `Executor` whose
/// `ctx.assertions` hold the raw parsed foralls.
fn build(src: &str) -> Executor {
    let commands = parse(src).expect("parse classifier fixture");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("execute classifier fixture");
    exec
}

/// (self_chaining, bridge_cycle, other) population counts over the fixture's
/// classifiable foralls.
fn class_counts(src: &str) -> (usize, usize, usize) {
    let exec = build(src);
    let foralls = exec.collect_classifiable_foralls();
    let classes = exec.classify_quantifier_families(&foralls);
    let mut counts = (0usize, 0usize, 0usize);
    for class in classes.values() {
        match class {
            FamilyClass::SelfChainingDefinitional => counts.0 += 1,
            FamilyClass::BridgeCycle => counts.1 += 1,
            FamilyClass::Other => counts.2 += 1,
        }
    }
    counts
}

// ---------------------------------------------------------------------------
// SelfChainingDefinitional — the tsum / logic_sum recursive defining forall.
// ---------------------------------------------------------------------------

/// The recursive `sum` defining forall (List) classifies SelfChainingDefinitional;
/// its nonneg lemma sibling — same `sum` trigger, but no recursive descent and only
/// a mono-vocabulary coupling — classifies Other (NOT a bridge cycle).
#[test]
fn sum_list_defining_forall_is_self_chaining() {
    let src = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
        (declare-fun sum (Lst) Int)
        (assert (forall ((l Lst)) (! (= (sum l) (ite ((_ is Cons) l) (+ (hd l) (sum (tl l))) 0))
           :pattern ((sum l)))))
        (assert (forall ((l Lst)) (! (>= (sum l) 0) :pattern ((sum l)))))
    "#;
    assert_eq!(
        class_counts(src),
        (1, 0, 1),
        "sum-def must be SelfChaining, sum-nonneg must be Other (mono-vocab coupling \
         is not a bridge cycle)"
    );

    // The self-chaining forall is exactly the recursive `sum` definition.
    let exec = build(src);
    let foralls = exec.collect_classifiable_foralls();
    let self_chaining: Vec<String> = foralls
        .iter()
        .filter_map(|&q| exec.quantifier_is_self_chaining_definition(q))
        .collect();
    assert_eq!(
        self_chaining,
        vec!["sum".to_string()],
        "exactly the `sum` defining forall recurses on a selector chain"
    );
}

/// The `tsum` defining forall over a TWO-recursive-field datatype (`Node left val
/// right`) classifies SelfChainingDefinitional (it re-applies `tsum` to both the
/// `left` and `right` selectors); its nonneg lemma classifies Other.
#[test]
fn tsum_tree_defining_forall_is_self_chaining() {
    let src = r#"
        (set-logic ALL)
        (declare-datatypes ((Tree 0)) (((Leaf) (Node (left Tree) (val Int) (right Tree)))))
        (declare-fun tsum (Tree) Int)
        (assert (forall ((t Tree)) (! (= (tsum t) (ite ((_ is Node) t) (+ (val t) (+ (tsum (left t)) (tsum (right t)))) 0)) :pattern ((tsum t)))))
        (assert (forall ((t Tree)) (! (>= (tsum t) 0) :pattern ((tsum t)))))
    "#;
    assert_eq!(class_counts(src), (1, 0, 1));
}

/// A GUARDED recursive definition `forall l. Cons?(l) => (= (f l) (g (f (tl l))))`
/// still classifies SelfChainingDefinitional: the `=>` guard is peeled and the
/// recursive `f (tl l)` descent is recognized.
#[test]
fn guarded_recursive_definition_is_self_chaining() {
    let src = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
        (declare-fun f (Lst) Int)
        (assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (f l) (+ (hd l) (f (tl l))))) :pattern ((f l)))))
    "#;
    assert_eq!(class_counts(src), (1, 0, 0));
}

// ---------------------------------------------------------------------------
// BridgeCycle — the list_cons_1 <-> enum_payload_get dual-vocabulary cycle.
// ---------------------------------------------------------------------------

/// The dual-vocabulary bridge cycle from the `freevar_takesome_repro` prophecy-pair
/// vocabulary. The simplified repro's own foralls do NOT close a two-input-forall
/// cycle (its bridge runs through synthesized DT selector axioms, not input
/// foralls), so this fixture pins the genuine `list_cons_1` <-> `payload_get`
/// dual-vocabulary shape the blueprint names: `payload_get` is defined via
/// `list_cons_1` and `list_cons_1` is defined via `payload_get` on a deeper term.
/// Instantiating either mints a term that triggers the other — a 2-forall SCC whose
/// internal edges carry two DISTINCT bridging symbols. Both classify BridgeCycle.
#[test]
fn list_cons_payload_pair_is_bridge_cycle() {
    let src = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
        (declare-fun payload_get (Lst) Lst)
        (declare-fun list_cons_1 (Lst) Lst)
        (assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (payload_get l) (list_cons_1 l))) :pattern ((payload_get l)))))
        (assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (list_cons_1 l) (payload_get (tl l)))) :pattern ((list_cons_1 l)))))
    "#;
    assert_eq!(
        class_counts(src),
        (0, 2, 0),
        "both foralls of the dual-vocabulary cycle classify BridgeCycle"
    );
}

/// A mono-vocabulary 2-forall coupling (two foralls both triggered on `g` and both
/// minting `g`, e.g. a defined symbol plus a lemma about it) is NOT a bridge cycle:
/// its cycle carries only ONE distinct bridging symbol. Guards the cross-vocabulary
/// requirement so a plain lemma pair never spuriously flags BridgeCycle.
#[test]
fn mono_vocabulary_coupling_is_not_bridge_cycle() {
    let src = r#"
        (set-logic ALL)
        (declare-fun g (Int) Int)
        (assert (forall ((x Int)) (! (= (g x) (g (+ x 1))) :pattern ((g x)))))
        (assert (forall ((x Int)) (! (>= (g x) 0) :pattern ((g x)))))
    "#;
    // Neither is a recursive selector-chain definition (Int has no selectors), and
    // the only cycle is mono-vocabulary -> both Other.
    assert_eq!(class_counts(src), (0, 0, 2));
}

// ---------------------------------------------------------------------------
// Other — every certificate-path shape MUST classify Other.
// ---------------------------------------------------------------------------

/// A quantifier_consumer `(Seq Int)` model-completion axiom (`0 <= seq_len s`) is a certificate
/// shape: it is recognized by [`is_quantifier_consumer_seq_model_completion_quantifier`] AND
/// classifies Other (never SelfChaining / BridgeCycle).
#[test]
fn quantifier_consumer_seq_prelude_axiom_is_other() {
    let src = r#"
        (set-logic ALL)
        (declare-fun seq_len ((Seq Int)) Int)
        (assert (forall ((s (Seq Int))) (! (<= 0 (seq_len s)) :pattern ((seq_len s)))))
    "#;
    assert_eq!(class_counts(src), (0, 0, 1));

    // Cross-check: it genuinely IS a quantifier_consumer model-completion certificate shape, so
    // the "certificate shapes classify Other" pin is over a real certificate.
    let exec = build(src);
    let foralls = exec.collect_classifiable_foralls();
    assert_eq!(foralls.len(), 1);
    assert!(
        is_quantifier_consumer_seq_model_completion_quantifier(&exec.ctx.terms, foralls[0]),
        "fixture must be a recognized quantifier_consumer seq model-completion axiom"
    );
}

/// A uf-completion pointwise/constant definition (`forall x. f(x) = 0`) is a
/// certificate shape: `quantifier_supported_by_uf_completion` accepts it AND it
/// classifies Other (it is a NON-recursive definition — no self-application).
#[test]
fn uf_completion_definition_is_other() {
    let src = r#"
        (set-logic ALL)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (= (f x) 0) :pattern ((f x)))))
    "#;
    assert_eq!(class_counts(src), (0, 0, 1));

    let exec = build(src);
    let foralls = exec.collect_classifiable_foralls();
    assert_eq!(foralls.len(), 1);
    assert!(
        exec.quantifier_supported_by_uf_completion(foralls[0]),
        "fixture must be a recognized uf-completion definition"
    );
    assert!(
        exec.quantifier_is_self_chaining_definition(foralls[0])
            .is_none(),
        "a non-recursive uf definition must NOT be self-chaining"
    );
}

/// A plain bounded finite-table forall (single Int binder, guarded predicate)
/// classifies Other.
#[test]
fn plain_bounded_forall_is_other() {
    let src = r#"
        (set-logic ALL)
        (declare-fun P (Int) Bool)
        (assert (forall ((i Int)) (! (=> (and (<= 0 i) (< i 5)) (P i)) :pattern ((P i)))))
    "#;
    assert_eq!(class_counts(src), (0, 0, 1));
}

/// The full `freevar_takesome_repro` probe (four foralls): the recursive `sum`
/// definition is SelfChaining; the two payload bridge foralls and the `sum` nonneg
/// lemma are Other. This documents that the simplified repro contains NO
/// two-input-forall bridge cycle (its bridge is via synthesized DT selector axioms),
/// which is exactly why the dedicated dual-vocabulary fixture above exercises the
/// BridgeCycle class.
#[test]
fn freevar_takesome_repro_classification() {
    let src = r#"
        (set-logic ALL)
        (declare-datatypes ((Lst 0)) (((Nil) (Cons (hd Int) (tl Lst)))))
        (declare-fun sum (Lst) Int)
        (declare-fun payload_hd (Lst) Int)
        (declare-fun payload_get (Lst) Lst)
        (assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (payload_get l) (tl l))) :pattern ((payload_get l)))))
        (assert (forall ((l Lst)) (! (=> ((_ is Cons) l) (= (payload_hd l) (hd l))) :pattern ((payload_hd l)))))
        (assert (forall ((l Lst)) (! (= (sum l) (ite ((_ is Cons) l) (+ (hd l) (sum (tl l))) 0)) :pattern ((sum l)))))
        (assert (forall ((l Lst)) (! (>= (sum l) 0) :pattern ((sum l)))))
    "#;
    assert_eq!(
        class_counts(src),
        (1, 0, 3),
        "sum-def SelfChaining; payload_get/payload_hd bridges + sum-nonneg are Other"
    );
}

/// REAL verification-consumer `rusthorn/inc_some_list` shape (extracted verbatim from the
/// driver's pre-solve VC): the recursive `logic_sum` definition is emitted as a
/// GROUND `ite` assertion — NOT a `forall` — because verification-consumer skips the global
/// quantified defining axiom for datatype-recursive logic fns and grounds it per
/// occurrence (`skip_global_quantified_logic_axioms`). Consequently the classifier
/// finds ZERO SelfChainingDefinitional families on the real obligation, even though
/// the hand-written `freevar_takesome_repro` above (which the M2/M3 flip was tuned
/// on) presents that same recursion AS a self-chaining `forall`.
///
/// This pins the repro-vs-real DELTA the demand-driven-instantiation campaign
/// diagnosis surfaced: the demand lane's self-chaining minter-control (what flips
/// the repros) is structurally INERT on the real VCs because that minter is a
/// GROUND term set there, not a quantified family. What the classifier DOES find on
/// the real VC is the dual-vocabulary bridge (`list_cons_1` <-> the datatype tail
/// selector) plus the triggerless `sum`-nonneg lemma (Other). The real residual
/// timeout is downstream of the quantifier lane — the ground DT/EUF/LIA combiner —
/// so extending the SelfChaining recognizer here cannot move it. Keep this test
/// green as the guard against re-chasing a self-chaining `forall` that the real
/// encoding never emits.
#[test]
fn real_inc_some_list_ground_recursion_has_no_self_chaining() {
    let src = r#"
        (set-logic ALL)
        (declare-datatypes ((List 0))
          (((Cons (enum_payload_get_0_1 Int) (enum_payload_get_1_1 List)) (Nil))))
        (declare-fun logic_sum (List) Int)
        (declare-fun list_cons_1 (List) List)
        (declare-fun list_cons_0__ret (List) Int)
        (declare-const self List)
        ; GROUND recursive definition of logic_sum — verification-consumer emits this per
        ; occurrence, NOT as `(forall (l) (= (logic_sum l) (ite ...)))`.
        (assert (ite (is-Cons self)
                     (= (logic_sum self) (+ (list_cons_0__ret self) (logic_sum (list_cons_1 self))))
                     (= 0 (logic_sum self))))
        ; the only logic_sum forall present: the triggerless nonneg lemma (Other).
        (assert (forall ((l List)) (<= 0 (logic_sum l))))
        ; dual-vocabulary bridge foralls (list_cons_* <-> datatype tail/head selectors).
        (assert (forall ((x List)) (or (= (list_cons_1 x) (enum_payload_get_1_1 x)) (not (is-Cons x)))))
        (assert (forall ((x List)) (or (= (list_cons_0__ret x) (enum_payload_get_0_1 x)) (not (is-Cons x)))))
    "#;
    let (self_chaining, bridge_cycle, _other) = class_counts(src);
    assert_eq!(
        self_chaining, 0,
        "the real inc_some_list recursion is GROUND (ite), so no SelfChaining family \
         exists — unlike the hand-written freevar_takesome_repro"
    );
    assert!(
        bridge_cycle >= 1,
        "the dual-vocabulary list_cons_* <-> datatype-selector bridge is the family \
         the demand lane actually arms on for the real VC"
    );
}

/// No foralls -> empty classification, all class populations zero.
#[test]
fn ground_problem_has_no_families() {
    let src = r#"
        (set-logic ALL)
        (declare-const a Int)
        (assert (> a 0))
    "#;
    assert_eq!(class_counts(src), (0, 0, 0));
}
