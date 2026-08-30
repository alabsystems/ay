// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

// A refutation whose empty-clause cone rests on a CEGQI counterexample lemma
// must never mint a certificate (see
// `reject_counterexample_contaminated_cone` in `builder.rs`).
//
// CEGQI asserts the NEGATED body of a `forall` at a fresh
// `__ay_ce_<binder>!<n>` and pushes that lemma into the MAIN assertion set, so
// its conjuncts reach the SAT solver as ordinary ORIGINAL clauses. They assert
// a fragment of `!F(e)` while the authored problem asserts `F`, so a cone using
// them refutes `problem AND !F(e)`, not the problem.
//
// The funnel already declined these cones before the guard, but only as an
// ACCIDENT of which recognizers exist: nothing currently authenticates
// `(<= 0 e)` for a fresh `e`. A future recognizer that did -- a
// plausible-looking arithmetic-bounds rule, say -- would silently certify a
// non-entailed premise. These tests make the invariant CHECKED.

/// The verification-consumer ext_eq push/pop refutation (#7956), whose measured 21-original
/// cone contains `(<= 0 __ay_ce_ext_eq_i_12!15)` and
/// `(< __ay_ce_ext_eq_i_12!15 (seq_len vec))`.
///
/// Genuinely UNSAT: `ext_eq_0` forces `len(vec) >= 1`, so the pointwise axiom at
/// index 0 is in range and chains to `v = 42`, contradicting `(not (= v 42))`.
const EXT_EQ_CE_CONE: &str = r#"
(set-logic AUFLIA)
(declare-sort Seq 0)
(declare-fun seq_len (Seq) Int)
(declare-fun seq_offset (Seq) Int)
(declare-fun seq_array (Seq) (Array Int Int))
(declare-fun seq_index_logic (Seq Int) Int)
(declare-fun seq_concat (Seq Seq) Seq)
(declare-fun seq_singleton (Int) Seq)
(declare-const vec Seq)
(declare-const next Seq)
(declare-const v Int)
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i) (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))
(assert (= (seq_array (seq_singleton v)) (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))
(declare-const ext_eq_0 Bool)
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))
(assert (=> ext_eq_0
  (forall ((ext_eq_i Int))
    (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
        (= (seq_index_logic vec ext_eq_i)
           (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i))))))
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))
(assert (= (seq_index_logic vec 0) (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (not (= v 42)))
(check-sat)
"#;

#[cfg(test)]
fn solve_script(script: &str) -> (String, Executor) {
    let commands = ay_frontend::parse(script).expect("probe script must parse");
    let mut executor = Executor::new();
    executor.set_deadline(Some(
        ay_core::time::Instant::now() + std::time::Duration::from_secs(60),
    ));
    executor.set_memory_limit(Some(8 << 30));
    let outputs = executor.execute_all(&commands).expect("execution succeeds");
    let verdict = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| "<none>".to_string());
    (verdict, executor)
}

/// The guard withholds a CERTIFICATE, never an answer. AY still refutes this
/// through `disambiguate_cegqi_unsat`, which by design refuses to publish a
/// CE-dependent conflict and re-derives the refutation without one.
#[test]
fn contaminated_cone_still_answers_unsat() {
    let (verdict, _executor) = solve_script(EXT_EQ_CE_CONE);
    assert_eq!(
        verdict, "unsat",
        "the guard must withhold the certificate, not the correct verdict"
    );
}

/// THE INVARIANT. Asserted as "no certificate" rather than "declined with
/// reason X", so it keeps holding if the funnel later declines earlier or for
/// an additional reason. What it must never do is start succeeding.
#[test]
fn contaminated_cone_mints_no_certificate() {
    let (verdict, mut executor) = solve_script(EXT_EQ_CE_CONE);
    assert_eq!(verdict, "unsat", "fixture drifted: expected a refutation");
    assert!(
        executor.take_unsat_certificate().is_none(),
        "a cone containing a CEGQI counterexample premise must NOT certify: those \
         clauses assert a fragment of the NEGATED quantifier body at a fresh variable \
         and are not entailed by the authored problem"
    );
}

/// CONTROL, and the reason the guard is scoped to the CONE rather than to the
// assertion set. Without it the guard could "pass" by suppressing every
// certificate in sight, gutting the funnel instead of protecting it.
//
// A plain Boolean contradiction has no quantifier, so CEGQI never runs and no
// `__ay_ce_*` symbol exists; its cone is uncontaminated and must still certify.
//
// (An earlier draft of this control used `(assert (= 0 1))` beside an E-matched
// quantifier. That was a BAD fixture and it failed for a reason unrelated to the
// guard: measured, the guard never fires on it, and it publishes through
// deferred-trust discharge rather than minting at all -- so it could not have
// witnessed what this control is for.)
#[test]
fn uncontaminated_refutation_still_mints_its_certificate() {
    let (mut executor, _, _) = contradictory_unit_executor();
    let published = executor.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(
        published.is_unsat(),
        "an uncontaminated Boolean contradiction must still publish unsat"
    );
    assert!(
        executor.take_unsat_certificate().is_some(),
        "the guard is scoped to counterexample-contaminated cones; a refutation whose \
         cone holds no CEGQI counterexample premise must still mint its certificate"
    );
}

// Chained from here rather than from `checked_sat_refutation.rs` so the parent
// file, which sits exactly on its `.code_quality_file_size_baseline.toml`
// ceiling, does not grow. Same `tests` module, same `super::*` scope.
include!("level0_theory_conflict_tests.rs");
