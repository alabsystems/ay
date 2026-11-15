// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! REACHABILITY and EXACT WIRE TEXT for the fold-identity promoter
//! (`authored_fold_identity`).
//!
//! A preprocessor fold-to-`false` whose argument is a NORMALIZATION IDENTITY:
//! the authored conjunct `(distinct (ite c a (+ v v)) (ite c a (* 2 v)))`
//! under a `let` — the QF_UFLIA `mathsat/Hash/hash_uns_*` family, 54 corpus
//! files. Elaboration normalizes `(+ v v)` to `(* 2 v)`, the two `ite`s become
//! one term, `(distinct t t)` folds to `false`, the root folds with it, and
//! the document used to be `(step t0 (cl) :rule hole)`. Measured on
//! `hash_uns_03_08` at build 9659: `unsat`, `unproved_steps=1
//! ay_self_checkable=no`, decline `preprocessor-fold-to-false`, carcara
//! `holey`.

use ay_dpll::Executor;
use ay_frontend::parse;

fn run_with_proofs(body: &str) -> (Vec<String>, Option<String>) {
    let script = format!("(set-option :produce-proofs true)\n{body}");
    let commands = parse(&script).expect("fixture script must parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture script must run");
    let proof = if outputs.last().map(String::as_str) == Some("unsat") {
        let get_proof = parse("(get-proof)").expect("(get-proof) must parse");
        exec.execute_all(&get_proof)
            .ok()
            .and_then(|out| out.last().cloned())
    } else {
        None
    };
    (outputs, proof)
}

/// The exact shape of the corpus family, reduced to one hash function and
/// two elements. The `let` chain, the parallel binding of `?v_24` over the
/// first level's names, and the trailing conjunct are the family's.
const FOLD: &str = "\
(set-logic QF_UFLIA)\n\
(declare-fun f (Int) Int)\n\
(declare-fun x () Int)\n\
(declare-fun y () Int)\n\
(assert (let ((?v_0 (f x)) (?v_3 (f y))) (let ((?v_24 (= ?v_0 ?v_3))) (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0)))))))\n\
(check-sat)\n";

/// The published document, byte for byte. Pinned as BYTES for the reason the
/// sibling fold test records: AY's strict checker accepting a candidate says
/// nothing about what the PRINTER then writes. Load-bearing and invisible to
/// any looser assertion:
///
/// * the `assume` is the authored `(let ...)` text, and the elimination is
///   the printer's own certified `refl`/`let` bridge — carcara matches a
///   let-rooted premise only through `let`, so an eliminated `assume` is one
///   it refuses at the first line;
/// * the two `la_generic` units carry Farkas coefficient `1`, and the
///   `la_disequality` triangle lists the equality FIRST — the fixed positions
///   carcara's rule checks;
/// * `cong` cites one premise per `ite` argument, `refl` for the two that
///   are already identical.
///
/// Pinned carcara 1.1.0 answers `valid` on exactly this document against the
/// fixture above (measured 2026-09-12).
const PUBLISHED: &str = "\
(assume t0.a (let ((?v_0 (f x)) (?v_3 (f y))) (let ((?v_24 (= ?v_0 ?v_3))) (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0)))))))\n\
(anchor :step t0.l :args ((:= ?v_0 (f x)) (:= ?v_3 (f y))))\n\
(anchor :step t0.l.t1 :args ((:= ?v_24 (= ?v_0 ?v_3))))\n\
(step t0.l.t1.t1 (cl (= (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0)))) (and (distinct x y) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))))) :rule refl)\n\
(step t0.l.t1 (cl (= (let ((?v_24 (= ?v_0 ?v_3))) (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0))))) (and (distinct x y) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))))) :rule let)\n\
(step t0.l (cl (= (let ((?v_0 (f x)) (?v_3 (f y))) (let ((?v_24 (= ?v_0 ?v_3))) (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0)))))) (and (distinct x y) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))))) :rule let)\n\
(step t0.e (cl (not (= (let ((?v_0 (f x)) (?v_3 (f y))) (let ((?v_24 (= ?v_0 ?v_3))) (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0)))))) (and (distinct x y) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))))) (not (let ((?v_0 (f x)) (?v_3 (f y))) (let ((?v_24 (= ?v_0 ?v_3))) (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 2 ?v_0))))))) (and (distinct x y) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))))) :rule equiv_pos2)\n\
(step t0 (cl (and (distinct x y) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))))) :rule resolution :premises (t0.e t0.l t0.a))\n\
(step t1 (cl (not (and (distinct x y) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))))) (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))) :rule and_pos :args (1))\n\
(step t2 (cl (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))) :rule resolution :premises (t1 t0))\n\
(step t3 (cl (= (= (f x) (f y)) (= (f x) (f y)))) :rule refl)\n\
(step t4 (cl (= (f y) (f y))) :rule refl)\n\
(step t5 (cl (<= (+ (f x) (f x)) (* 2 (f x)))) :rule la_generic :args (1))\n\
(step t6 (cl (<= (* 2 (f x)) (+ (f x) (f x)))) :rule la_generic :args (1))\n\
(step t7 (cl (or (= (+ (f x) (f x)) (* 2 (f x))) (not (<= (+ (f x) (f x)) (* 2 (f x)))) (not (<= (* 2 (f x)) (+ (f x) (f x)))))) :rule la_disequality)\n\
(step t8 (cl (= (+ (f x) (f x)) (* 2 (f x))) (not (<= (+ (f x) (f x)) (* 2 (f x)))) (not (<= (* 2 (f x)) (+ (f x) (f x))))) :rule or :premises (t7))\n\
(step t9 (cl (= (+ (f x) (f x)) (* 2 (f x))) (not (<= (* 2 (f x)) (+ (f x) (f x))))) :rule resolution :premises (t8 t5))\n\
(step t10 (cl (= (+ (f x) (f x)) (* 2 (f x)))) :rule resolution :premises (t9 t6))\n\
(step t11 (cl (= (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))) :rule cong :premises (t3 t4 t10))\n\
(step t12 (cl (= (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))) (not (= (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))))) :rule distinct_elim)\n\
(step t13 (cl (not (= (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))) (not (= (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))))) (not (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))) (not (= (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))))) :rule equiv_pos2)\n\
(step t14 (cl (not (distinct (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x))))) (not (= (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))))) :rule resolution :premises (t13 t12))\n\
(step t15 (cl (not (= (ite (= (f x) (f y)) (f y) (+ (f x) (f x))) (ite (= (f x) (f y)) (f y) (* 2 (f x)))))) :rule resolution :premises (t14 t2))\n\
(step t16 (cl) :rule resolution :premises (t15 t11))";

/// The SAME script with the identity broken by one digit: `(* 3 ?v_0)`. The
/// two `ite`s are no longer one term, nothing folds, and the query is
/// SATISFIABLE (`f x = 1`, `f y = 0`, `x != y`).
const MUTANT: &str = "\
(set-logic QF_UFLIA)\n\
(declare-fun f (Int) Int)\n\
(declare-fun x () Int)\n\
(declare-fun y () Int)\n\
(assert (let ((?v_0 (f x)) (?v_3 (f y))) (let ((?v_24 (= ?v_0 ?v_3))) (and (distinct x y) (distinct (ite ?v_24 ?v_3 (+ ?v_0 ?v_0)) (ite ?v_24 ?v_3 (* 3 ?v_0)))))))\n\
(check-sat)\n";

#[test]
fn a_normalization_identity_fold_publishes_the_exact_derivation() {
    let (outputs, proof) = run_with_proofs(FOLD);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "the fold must publish its verdict under an explicit proof demand"
    );
    let proof = proof.expect("an unsat verdict under :produce-proofs must carry a proof");
    assert_eq!(
        proof.trim(),
        PUBLISHED,
        "the published document must be the fold's own argument, byte for byte"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "the published document must carry no hole and no trust step"
    );
}

/// FALSIFY-ONCE at the PRODUCT boundary. The promoter's whole soundness
/// argument is that the two disequality operands ARE one term after
/// normalization, and that the derivation discharges that identity with
/// checker-verified steps. Break it by one digit and there is no fold, no
/// refutation, and a model: if this ever reports `unsat`, the pass is
/// inventing a refutation the problem does not have.
#[test]
fn a_disequality_whose_operands_differ_by_one_digit_is_not_refuted() {
    let (outputs, proof) = run_with_proofs(MUTANT);
    assert_ne!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "with the identity broken the query is satisfiable and must never refute"
    );
    assert!(
        proof.is_none(),
        "a satisfiable query cannot carry a refutation"
    );
}

/// The kill switch restores the baseline byte for byte: under an explicit
/// proof demand the bare-hole document cannot be published, so the verdict is
/// the base's `unknown`.
#[test]
fn the_kill_switch_restores_the_bare_hole_decline() {
    let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_authored_fold_identity: true,
        ..Default::default()
    });
    let (outputs, proof) = run_with_proofs(FOLD);
    drop(guard);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "with the pass disabled the explicit-proof posture withholds the fold, as on the base"
    );
    assert!(proof.is_none(), "a withheld verdict carries no proof");
}

/// The COMPLEMENT shape under one `(not (not ..))` pair: the QF_BVFP
/// `klee query.2121` root (`(not (not (and (not $x50) $x50)))`) with a
/// checkable sort in place of the FloatingPoint one, and the QF_LRA
/// `polypaver-bench-exp-3d-chunk-0145` root's `(and (not ?v_0) (and ?v_0 ..))`.
/// `mk_and`'s complement scan folds it to `false` at construction.
const COMPLEMENT: &str = "\
(set-logic QF_LRA)\n\
(declare-fun x () Real)\n\
(declare-fun y () Real)\n\
(assert (let ((?v_0 (<= 0 x))) (not (not (and (not ?v_0) (and ?v_0 (<= y 1)))))))\n\
(check-sat)\n";

/// Byte for byte. The shelled assume is projected by resolving it against
/// `and_pos` on the pivot `(not (and ..))` — `t2` and `t6` cite `t0` FIRST,
/// the premise carrying the pivot's negation — so no `not_not` step is
/// needed. Pinned carcara 1.1.0 answers `valid` on exactly this document
/// (measured 2026-09-12).
const COMPLEMENT_PUBLISHED: &str = "\
(assume t0.a (let ((?v_0 (<= 0 x))) (not (not (and (not ?v_0) (and ?v_0 (<= y 1)))))))\n\
(anchor :step t0.l :args ((:= ?v_0 (<= 0 x))))\n\
(step t0.l.t1 (cl (= (not (not (and (not ?v_0) (and ?v_0 (<= y 1))))) (not (not (and (not (<= 0 x)) (and (<= 0 x) (<= y 1))))))) :rule refl)\n\
(step t0.l (cl (= (let ((?v_0 (<= 0 x))) (not (not (and (not ?v_0) (and ?v_0 (<= y 1)))))) (not (not (and (not (<= 0 x)) (and (<= 0 x) (<= y 1))))))) :rule let)\n\
(step t0.e (cl (not (= (let ((?v_0 (<= 0 x))) (not (not (and (not ?v_0) (and ?v_0 (<= y 1)))))) (not (not (and (not (<= 0 x)) (and (<= 0 x) (<= y 1))))))) (not (let ((?v_0 (<= 0 x))) (not (not (and (not ?v_0) (and ?v_0 (<= y 1))))))) (not (not (and (not (<= 0 x)) (and (<= 0 x) (<= y 1)))))) :rule equiv_pos2)\n\
(step t0 (cl (not (not (and (not (<= 0 x)) (and (<= 0 x) (<= y 1)))))) :rule resolution :premises (t0.e t0.l t0.a))\n\
(step t1 (cl (not (and (not (<= 0 x)) (and (<= 0 x) (<= y 1)))) (and (<= 0 x) (<= y 1))) :rule and_pos :args (1))\n\
(step t2 (cl (and (<= 0 x) (<= y 1))) :rule resolution :premises (t0 t1))\n\
(step t3 (cl (not (and (<= 0 x) (<= y 1))) (<= 0 x)) :rule and_pos :args (0))\n\
(step t4 (cl (<= 0 x)) :rule resolution :premises (t3 t2))\n\
(step t5 (cl (not (and (not (<= 0 x)) (and (<= 0 x) (<= y 1)))) (not (<= 0 x))) :rule and_pos :args (0))\n\
(step t6 (cl (not (<= 0 x))) :rule resolution :premises (t0 t5))\n\
(step t7 (cl) :rule resolution :premises (t6 t4))";

#[test]
fn a_shelled_complement_fold_publishes_the_exact_projection() {
    let (outputs, proof) = run_with_proofs(COMPLEMENT);
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "the complement fold must publish its verdict under an explicit proof demand"
    );
    let proof = proof.expect("an unsat verdict under :produce-proofs must carry a proof");
    assert_eq!(
        proof.trim(),
        COMPLEMENT_PUBLISHED,
        "the published document must be the fold's own argument, byte for byte"
    );
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "the published document must carry no hole and no trust step"
    );
}
