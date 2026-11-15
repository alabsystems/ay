// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nested-array-quarantine-datatype-fields: the quarantine sees nested arrays
//! through declared record carriers. It withholds the record-boxed twin of the
//! quantified pin, releases the MODEL_CHECKER_CONSUMER nested Vec frame refutation only on
//! its strict proof, never lets a record-boxed wrong UNSAT out, still publishes
//! flat-record and proof-backed verdicts, and admits a boxed UNSAT on the
//! exact finite-expansion theorem,
//! whose release of a directly nested UNSAT is pinned here with its negative
//! twins.

use ay_frontend::parse;
use ntest::timeout;

use crate::Executor;

fn solve(input: &str) -> (Executor, String) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    let verdict = outputs.first().cloned().unwrap_or_default();
    (exec, verdict)
}

fn assert_quarantined(exec: &Executor, verdict: &str, what: &str) {
    assert_eq!(
        (verdict, exec.statistics().get_string("unknown.phase")),
        ("unknown", Some("array-combination-quarantine")),
        "{what}: the nested-array quarantine must be the gate that withholds it"
    );
    assert_eq!(exec.last_command_unsat_admission_tag(), None, "{what}");
}

/// The record-boxed twin of
/// `test_nested_array_quantified_instance_unsat_without_authority_is_quarantined`.
/// Before declared carriers were resolved it published `unsat` on
/// `discharged-trust` behind a bare `hole`; z3 answers `unsat`, so the verdict
/// was right and its only backing was the distrusted combination re-run.
#[test]
#[timeout(120_000)]
fn a_record_boxed_nested_array_unsat_without_authority_is_quarantined() {
    let (exec, verdict) = solve(include_str!(
        "../../../../../../repros/abv-record-boxed-nested-array-quantified-unsat-quarantine.smt2"
    ));
    assert_quarantined(
        &exec,
        &verdict,
        "wrapping the inner array in a one-field record must not bypass the quarantine",
    );
}

/// The depth-0 counterexample query of ay-chc's nested Vec store transition
/// (`quantified::solve::nested_cell_tests::stores`), rebuilt by hand: the fact
/// frames every valid cell of `d0` as `fill1`, the query asks for a valid cell
/// of the equal `d2` that differs from the equal `fill3`. z3: `unsat`. It
/// published `unsat` on `discharged-trust` alone while the carriers read as
/// opaque sorts, which is what certified that transition `Safe`.
///
/// It now publishes on a strict proof, and only on one. Since the diagonal
/// pass skips foralls over interpreted sorts whose body applies a function to
/// a binder (`diagonal_scope`), no `r = c` instance of the frame axiom is
/// added, and the refutation is the one e-matching instance at `(r4, c5)`
/// plus congruence through `d0 = d2`, `len0 = len2` and `fill1 = fill3`: 46
/// steps, no trust step, strictly checked. With the diagonal instances the
/// proof carried 4 trust steps and the quarantine withheld it. Whatever else
/// changes, this refutation must never leave on `discharged-trust`.
#[test]
#[timeout(120_000)]
fn the_model_checker_consumer_nested_vec_frame_refutation_publishes_only_on_a_strict_proof() {
    let (exec, verdict) = solve(
        "(set-logic ALL)
         (declare-datatype Inner ((mkInner
           (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
           (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((mkOuter
           (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
           (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) Inner)))))
         (declare-const p0 (_ BitVec 64)) (declare-const len0 (_ BitVec 64))
         (declare-const cap0 (_ BitVec 64)) (declare-const d0 (Array (_ BitVec 64) Inner))
         (declare-const p2 (_ BitVec 64)) (declare-const len2 (_ BitVec 64))
         (declare-const cap2 (_ BitVec 64)) (declare-const d2 (Array (_ BitVec 64) Inner))
         (declare-const fill1 (_ BitVec 8)) (declare-const fill3 (_ BitVec 8))
         (declare-const r4 (_ BitVec 64)) (declare-const c5 (_ BitVec 64))
         (assert (forall ((r (_ BitVec 64)) (c (_ BitVec 64)))
           (or (= fill1 (select (fld_data (select d0 r)) c))
               (not (bvult r len0))
               (not (bvult c (fld_len (select d0 r)))))))
         (assert (and (bvule #x0000000000000020 r4) (bvule #x0000000000000020 c5)
           (bvult r4 len2) (bvult c5 (fld_len (select d2 r4)))
           (not (= fill3 (select (fld_data (select d2 r4)) c5)))))
         (assert (and (= p0 p2) (= len0 len2) (= cap0 cap2) (= d0 d2)))
         (assert (= fill1 fill3))
         (check-sat)",
    );
    assert_eq!(
        (verdict.as_str(), exec.last_command_unsat_admission_tag()),
        ("unsat", Some("strict-proof")),
        "the nested Vec frame refutation publishes on its strict proof, never on trust"
    );
}

/// NEVER-UNSAT CANARY. Record-boxed forms (BV and Int) of the binder-capture
/// defect `3fac3f55e` fixed: the declared constant `i_2` spells like a
/// renamed binder `i`. z3: `sat` on both (`i_2` outside `{0, 1}`). At
/// ad60a0707 both printed a WRONG `unsat` on `discharged-trust` -- the fresh
/// executor re-ran the same fold -- while their directly nested twin was
/// withheld here; with the carriers resolved the quarantine withholds them
/// even without `3fac3f55e`. Whatever else changes, neither may say `unsat`.
#[test]
#[timeout(120_000)]
fn record_boxed_binder_capture_twins_never_publish_unsat() {
    for (label, script) in [
        (
            "bv",
            "(set-logic ALL)
             (declare-datatype Row ((mk_row (cells (Array (_ BitVec 8) (_ BitVec 8))))))
             (declare-const lens (Array (_ BitVec 8) (_ BitVec 8)))
             (declare-const w (Array (_ BitVec 8) Row))
             (assert (forall ((i (_ BitVec 8))) (=> (bvult i (select lens #x00))
               (distinct i (select (cells (select w #x00)) #x00)))))
             (declare-const |i_2| (_ BitVec 8))
             (assert (= lens (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x00 #x02)))
             (assert (= w (store ((as const (Array (_ BitVec 8) Row))
               (mk_row ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00)))
               #x00 (mk_row (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x00 |i_2|)))))
             (check-sat)",
        ),
        (
            "int",
            "(set-logic ALL)
             (declare-datatype Row ((mk_row (cells (Array Int Int)))))
             (declare-const lens (Array Int Int))
             (declare-const w (Array Int Row))
             (assert (forall ((i Int)) (=> (and (<= 0 i) (< i (select lens 0)))
               (distinct i (select (cells (select w 0)) 0)))))
             (declare-const |i_2| Int)
             (assert (= lens (store ((as const (Array Int Int)) 0) 0 2)))
             (assert (= w (store ((as const (Array Int Row)) (mk_row ((as const (Array Int Int)) 0)))
               0 (mk_row (store ((as const (Array Int Int)) 0) 0 |i_2|)))))
             (check-sat)",
        ),
    ] {
        let (_, verdict) = solve(script);
        assert_ne!(verdict, "unsat", "{label}: z3 answers sat");
    }
}

/// Negative twin: a record whose only array is flat, beside an outer array of
/// scalar records, is not nested state, so its UNSAT still publishes.
#[test]
#[timeout(60_000)]
fn a_flat_record_carrier_unsat_is_not_quarantined() {
    let (_, verdict) = solve(
        "(set-logic ALL)
         (declare-datatype Vec ((mk_vec (len (_ BitVec 8))
           (data (Array (_ BitVec 8) (_ BitVec 8))))))
         (declare-datatype Pair ((mk_pair (fst (_ BitVec 8)) (snd (_ BitVec 8)))))
         (declare-const v Vec)
         (declare-const t (Array (_ BitVec 8) Pair))
         (assert (= (select (data v) #x00) (fst (select t #x01))))
         (assert (= (fst (select t #x01)) #x05))
         (assert (not (= (select (data v) #x00) #x05)))
         (check-sat)",
    );
    assert_eq!(verdict, "unsat");
}

/// A record-boxed nested UNSAT that carries a checked authority still leaves
/// the quarantine: this one's strict proof is current.
#[test]
#[timeout(60_000)]
fn a_record_boxed_nested_unsat_with_a_strict_proof_publishes() {
    let (exec, verdict) = solve(
        "(set-logic ALL)
         (declare-datatype Row ((mk_row (cells (Array (_ BitVec 8) (_ BitVec 8))))))
         (declare-const t (Array (_ BitVec 8) Row))
         (assert (= (select (cells (select t #x01)) #x00) #x05))
         (assert (not (= (select (cells (select t #x01)) #x00) #x05)))
         (check-sat)",
    );
    assert_eq!(verdict, "unsat");
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("strict-proof")
    );
}

/// The finite-expansion rung. MODEL_CHECKER_CONSUMER's `nested_premise_false_unsat` keeps
/// `Outer{fld_data: (Array _ Inner)}` with `Inner{fld_data: (Array _ _)}`, so
/// it is nested, and its only authority is the exact finite-expansion theorem
/// b79271632 minted for it (an elementary ground contradiction over the
/// expanded public roots, no theory solver). It must keep publishing on it.
#[test]
#[timeout(120_000)]
fn a_finite_expansion_theorem_releases_a_record_boxed_nested_unsat() {
    let (exec, verdict) = solve(include_str!(
        "../../../../../../benchmarks/smt/model_checker_consumer_quantified_counterexample/nested_premise_false_unsat.smt2"
    ));
    assert_eq!(
        (verdict.as_str(), exec.last_command_unsat_admission_tag()),
        ("unsat", Some("checked-exact-finite-expansion")),
        "the verdict must leave the quarantine on the checked theorem, not on trust"
    );
}

/// DISCLOSED NARROWING. The same rung admits a DIRECTLY nested UNSAT that
/// carries the theorem: this `(Array _ (Array _ _))` twin of the row above was
/// `unknown` (`array-combination-quarantine`) before the rung existed and
/// z3 answers `unsat`. The covered twin stays withheld when a proof is
/// requested, because semantic evidence never satisfies a proof request, and
/// the quantified pin's directly nested UNSAT, which no finite-expansion
/// theorem covers, stays quarantined.
#[test]
#[timeout(120_000)]
fn the_finite_expansion_rung_admits_a_directly_nested_unsat_only_on_the_theorem() {
    let covered = "(set-logic ALL)
        (declare-const olen (_ BitVec 64))
        (declare-const lens (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-const data (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
        (assert (= olen (_ bv34 64)))
        (assert (= lens (store ((as const (Array (_ BitVec 64) (_ BitVec 64))) (_ bv0 64))
          (_ bv33 64) (_ bv65 64))))
        (assert (= data (let ((cells ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv7 8))))
          (store ((as const (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8)))) cells)
            (_ bv33 64) (store cells (_ bv64 64) (_ bv9 8))))))
        (assert (forall ((r (_ BitVec 64)) (c (_ BitVec 64)))
          (=> (and (bvult r olen) (bvult c (select lens r)))
              (= (select (select data r) c) (_ bv7 8)))))
        (assert (distinct (select (select data (_ bv33 64)) (_ bv64 64)) (_ bv8 8)))
        (check-sat)";
    let (exec, verdict) = solve(covered);
    assert_eq!(
        (verdict.as_str(), exec.last_command_unsat_admission_tag()),
        ("unsat", Some("checked-exact-finite-expansion"))
    );

    let (exec, verdict) = solve(&format!("(set-option :produce-proofs true)\n{covered}"));
    assert_eq!(
        (verdict.as_str(), exec.last_command_unsat_admission_tag()),
        ("unknown", None),
        "a proof request is never met by semantic evidence"
    );

    let (exec, verdict) = solve(include_str!(
        "../../../../../../repros/abv-nested-array-quantified-unsat-quarantine.smt2"
    ));
    assert_quarantined(&exec, &verdict, "no finite-expansion theorem covers it");
}
