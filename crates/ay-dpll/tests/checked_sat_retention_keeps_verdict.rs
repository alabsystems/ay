// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The checked-SAT retention may only ADD an artifact, never cost a verdict.
//!
//! `build_unsat_proof` may swap the assembled Alethe document for the checked
//! SAT-refutation sidecar's materialized reconstruction when the assembled one
//! still trips the wire-gap screen. That screen asks about Alethe/Carcara
//! EXPORTABILITY, not about validity, so the document it flags can be exactly
//! the one that certifies the result.
//!
//! Under `:produce-proofs true` — and under every other promised-artifact mode
//! — `independent_sidecar_blocked_by_presentation` bars the independent
//! sidecar lanes, so `check_strict_unsat_presentation` over the retained
//! document is `mint_unsat_certificate`'s ONLY remaining certification route.
//! An unconditional swap therefore turns a correct `unsat` into
//! `(incomplete self-check-rejected)` whenever the replacement is less
//! certifiable than what it displaced, which is what regressed this fixture:
//! the substitute's first step printed as a non-deferred Alethe `hole`, which
//! `ay_proof`'s checker refuses.
//!
//! This is a pin on MONOTONICITY, not on a route. Any assembly that publishes
//! this refutation keeps the test green; only losing the verdict fails it.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `g(x) /\ ~g(x)` over an FP-sorted uninterpreted atom: unsatisfiable on any
/// reading of `g`, refuted at the SAT level, and assembled into a native proof
/// that the wire-gap screen still flags. `:produce-proofs true` is load-bearing
/// — it is what blocks every certification lane except the strict proof.
const FP_UF_CONTRADICTION: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_UFFP)
    (declare-const x Float64)
    (declare-fun g (Float64) Bool)
    (assert (and (g x) (not (g x))))
    (check-sat)
"#;

#[test]
#[timeout(600_000)]
fn produce_proofs_keeps_the_fp_uf_contradiction_decided() {
    let commands = parse(FP_UF_CONTRADICTION).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "`(and (g x) (not (g x)))` is unsatisfiable on any reading of `g`; the \
         checked-SAT retention must not withhold it. Got {outputs:?}"
    );
}

/// One authored `(and ...)` refuted by the lazy QF_DT lane over its
/// `FlattenAnd` image. The checked-SAT sidecar's reconstruction `assume`s each
/// bare conjunct, which the strict checker admits through its `and` expansion
/// but which no `(assert ...)` row spells, so running the authored cascade over
/// it suppressed the query's whole reconstruction, and mandatory certification
/// withheld this `unsat` as "the provisional UNSAT verdict has no proof". The
/// assembled proof it displaced assumes the authored root, projects each
/// conjunct with `and_pos`, and certifies.
const DT_FLATTENED_CONJUNCTION: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_DT)
    (declare-datatypes ((L 0)) (((c (h Int) (t L)) (n))))
    (declare-const x L)
    (assert (and (not ((_ is c) x)) (not (= n x))))
    (check-sat)
"#;

#[test]
#[timeout(600_000)]
fn produce_proofs_keeps_a_flattened_datatype_conjunction_decided() {
    let commands = parse(DT_FLATTENED_CONJUNCTION).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "every value of a two-constructor datatype is headed by one of them; \
         the checked-SAT retention must not withhold it. Got {outputs:?}"
    );
    assert!(
        exec.last_proof().is_some(),
        "the published `unsat` must carry the proof that certified it"
    );
}

/// A model-checker-consumer quantified safety obligation (the corpus file
/// `model_checker_consumer_quantified_safety/uf_record_unsat.smt2` under `:produce-proofs`).
/// Consequence replay re-solves it on a same-context probe whose assembled
/// proof is trust-bearing and whose own source restoration already suppressed
/// reconstruction; the checked-SAT candidate is what gives that probe a
/// strict-complete refutation to stitch. Every retention on this query sees a
/// strict-rejected assembled proof, and declining their candidates for want of
/// an authored-source presentation answered `unknown` (`step t13 uses
/// unverified trust rule`). Pins that the retention's presentability decline
/// fires only for a live, strictly accepted assembled proof.
const UF_RECORD_SAFETY_OBLIGATION: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-datatype Vec ((mkVec (ptr (_ BitVec 64)) (len (_ BitVec 64))
        (cap (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8))))))
    (declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
    (declare-fun g (Bool (_ BitVec 8)) (_ BitVec 8))
    (declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
    (declare-const x (_ BitVec 8))
    (declare-const fill (_ BitVec 8))
    (declare-const k (_ BitVec 64))
    (assert (= fill (f true x)))
    (assert (bvuge k (_ bv32 64)))
    (declare-const v Vec)
    (assert (= (len v) (_ bv65 64)))
    (assert (bvult k (len v)))
    (assert (forall ((i (_ BitVec 64)))
      (=> (bvult i (len v)) (= (select (data v) i) (f true x)))))
    (assert (distinct (select (data v) k) fill))
    (check-sat)
"#;

#[test]
#[timeout(600_000)]
fn produce_proofs_keeps_the_uf_record_safety_obligation_decided() {
    let commands = parse(UF_RECORD_SAFETY_OBLIGATION).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "one shared uninterpreted `f` supplies `fill` and every cell, so cell `k` \
         cannot differ from `fill`; the checked-SAT retention must not withhold \
         it. Got {outputs:?}"
    );
}

/// The retention's OTHER measured way of costing a verdict, and the one that
/// is not the strict checker's leg: a DECLINED trial that condemned the proof
/// it kept.
///
/// `retain_checked_sat_proof_for_wire_gap` used to run the whole authored
/// cascade over the candidate before deciding whether to adopt it, and that
/// cascade ends in `restore_reachable_authored_assume_surface_overrides`. The
/// retained checked-SAT refutation assumes the CLAUSIFIED components of the
/// authored root rather than the root, so on the composed ROW2 root below it
/// carries `(assume (not (= i j)))` — no assertion of the problem.
/// `resolve_reachable_authored_sources` refuses the document
/// (`authored-source-authority-invalid`), the pass calls
/// `suppress_unsat_proof_reconstruction()`, and that suppression is EXECUTOR
/// state: it outlived the trial and condemned the proof that was kept, so a
/// publishable `unsat` became `unknown (self-check-rejected)` with
/// `MissingProof: last_proof=None … reconstruction_suppressed=true
/// proof_decline=Some(AuthoredSourceAuthorityInvalid)`.
///
/// `checked_sat_candidate_would_cost_the_assembled_proof` now declines such a
/// candidate BEFORE its cascade runs. This pins the OUTCOME that guard exists
/// for, from the presentation side rather than the verdict side: not merely
/// that `unsat` is published, but that the document published with it is the
/// assembled one — which assumes the authored root itself and DERIVES both
/// components, hole-free and trust-free.
///
/// Like its siblings above this pins MONOTONICITY, not a route: any assembly
/// that publishes this refutation with a complete document keeps it green.
const AUFLIA_COMPOSED_ROW2_ROOT: &str = r#"
    (set-option :produce-proofs true)
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
    (get-proof)
"#;

#[test]
#[timeout(600_000)]
fn a_declined_retention_leaves_the_authored_surface_of_the_kept_proof_intact() {
    let commands = parse(AUFLIA_COMPOSED_ROW2_ROOT).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "ROW2 at distinct indices is a theorem, so its negation is \
         unsatisfiable; a retention trial that was DECLINED must not suppress \
         the kept proof's reconstruction. Got {outputs:?}; unknown_reason={:?}",
        exec.unknown_reason()
    );
    let proof = outputs.last().cloned().expect("proof output");
    assert!(
        proof.contains("(assume ") && proof.contains("(step "),
        "the published document must carry Alethe commands:\n{proof}"
    );
    assert!(
        !proof.contains(":rule trust") && !proof.contains(":rule hole"),
        "the kept document is complete; no unchecked step may appear:\n{proof}"
    );
    // The authored root is the ONE top-level assume, and its components are
    // DERIVED — that is the property the declined trial used to destroy. The
    // step id is deliberately not pinned; the assumed TERM is the claim.
    assert!(
        proof.contains(
            " (not (=> (not (= i j)) (= (select (store a i v) j) (select a j)))))\n(step "
        ),
        "the document must assume the authored root:\n{proof}"
    );
    // A subproof's own hypothesis (`(assume t5.h ..)`) is discharged by its
    // `:discharge`, so only the dotted-free ids are document-level premises.
    let top_level_assumes = proof
        .lines()
        .filter_map(|line| line.strip_prefix("(assume "))
        .filter(|rest| !rest.split(' ').next().unwrap_or_default().contains('.'))
        .count();
    assert_eq!(
        top_level_assumes, 1,
        "the clausified components must not be assumed alongside it:\n{proof}"
    );
    assert!(
        proof.contains(":rule implies_neg1") && proof.contains(":rule implies_neg2"),
        "both components must be DERIVED from that root:\n{proof}"
    );
}

/// The same contract over a SELECTOR-headed conjunct, the fixture the
/// `dt-unknown` investigation measured: the sidecar's reconstruction assumes
/// `(not (is-cons (tl x)))` and `(not (= null (tl x)))`, neither of which owns
/// an `(assert ...)` source row, while the assembled document assumes the
/// authored `(and ...)` and projects both conjuncts with `and_pos`.
///
/// `(not (is-cons (tl x))) /\ (tl x) != null` is unsatisfiable by datatype
/// exhaustiveness alone: `list` has exactly the two constructors `cons` and
/// `null`, and `null` is nullary, so `is-null t` and `t = null` are the same
/// claim. Its sibling above covers the bare-variable shape; this one covers a
/// conjunct that is a selector application, where the flattened leaves are not
/// even sub-terms of an assertion the problem spells directly.
const QF_DT_EXHAUSTIVENESS_UNDER_AUTHORED_CONJUNCTION: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_DT)
    (declare-datatypes ((list 0)) (((cons (hd Int) (tl list)) (null))))
    (declare-fun x () list)
    (assert (and (not ((_ is cons) (tl x))) (not (= null (tl x)))))
    (check-sat)
"#;

#[test]
#[timeout(600_000)]
fn produce_proofs_keeps_the_conjunct_assumed_dt_exhaustiveness_decided() {
    let commands =
        parse(QF_DT_EXHAUSTIVENESS_UNDER_AUTHORED_CONJUNCTION).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "a value of `list` that is neither `cons` nor `null` does not exist; the \
         checked-SAT retention must not withhold the refutation because the \
         sidecar's document assumes the CONJUNCTS of the authored `(and ...)`. \
         Got {outputs:?}"
    );
    assert!(
        exec.last_proof().is_some(),
        "the published `unsat` must carry the proof that certified it"
    );
}
