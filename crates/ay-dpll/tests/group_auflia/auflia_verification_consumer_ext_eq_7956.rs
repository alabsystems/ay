// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #7956: false UNSAT on AUFLIA formula with
//! Array+Quantifier+UF involving ext_eq(vec, concat(singleton(v), next)).
//!
//! Mail issue from verification-consumer reporting that ay returns `unsat` on a satisfiable
//! AUFLIA formula. The formula models sequence extensional equality via a
//! Tseitin Bool variable with forward/backward axioms, combined with
//! concat/singleton/bridge quantified axioms and array select/store.
//!
//! Root cause (fixed in #6920/#6930): EUF proof-forest collect_path_reasons
//! cleared reasons on broken path, causing empty reasons leading to false UNSAT
//! on array+quantifier+UF formulas.
//!
//! This test file covers the exact verification-consumer encoding pattern (Tseitin ext_eq
//! variable, triggerless pointwise quantifier) plus several variants to
//! prevent future regressions.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// QuantifierConsumer's direct SeqValue ext_eq path for
/// vec.ext_eq(seq_singleton(v).concat(next)): the singleton prefix and concat
/// are represented by concrete array stores, and ext_eq emits a ground index-0
/// select equality. The SAT check guards the downstream vacuity precheck; the
/// UNSAT variant guards the actual `v == first(vec)` proof obligation.
const QUANTIFIER_CONSUMER_SINGLETON_PREFIX_ARRAY_EXT_EQ: &str = r#"
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
(declare-const ext_eq_0 Bool)

; QuantifierConsumer library sequence axioms present in the verification context.
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; seq![v]
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; seq![v].concat(next), using QuantifierConsumer's singleton-prefix SeqValue shape.
(assert (= (seq_array (seq_concat (seq_singleton v) next))
           (store (seq_array next)
                  (+ (- (seq_offset next) 1) 0)
                  (select (seq_array (seq_singleton v))
                          (+ (seq_offset (seq_singleton v)) 0)))))
(assert (= (seq_len (seq_concat (seq_singleton v) next))
           (+ (seq_len (seq_singleton v)) (seq_len next))))
(assert (= (seq_offset (seq_concat (seq_singleton v) next))
           (- (seq_offset next) 1)))

; ext_eq direct path: length plus the ground index-0 pointwise fact.
(assert (=> ext_eq_0
            (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))
(assert (=> ext_eq_0
            (=> (< 0 (seq_len vec))
                (= (select (seq_array vec) (+ (seq_offset vec) 0))
                   (select (seq_array (seq_concat (seq_singleton v) next))
                           (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))))

(assert ext_eq_0)
(assert (= (seq_len vec) 3))
(assert (= (select (seq_array vec) (+ (seq_offset vec) 0)) 42))
"#;

#[test]
fn test_quantifier_consumer_singleton_prefix_array_ext_eq_preconditions_fail_closed() {
    let smt = format!("{QUANTIFIER_CONSUMER_SINGLETON_PREFIX_ARRAY_EXT_EQ}\n(check-sat)\n");
    let result = run_executor_smt_with_timeout(&smt, 20).expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Unknown,
        "singleton-prefix array ext_eq preconditions lack a total quantified model certificate"
    );
}

#[test]
fn test_quantifier_consumer_singleton_prefix_array_ext_eq_proves_first_element() {
    let smt =
        format!("{QUANTIFIER_CONSUMER_SINGLETON_PREFIX_ARRAY_EXT_EQ}\n(assert (not (= v 42)))\n(check-sat)\n");
    // The former private 2s acceptance deadline produced, in six release runs
    // of this exact query, `unknown unknown unknown unsat unsat unsat` depending
    // only on machine load. Keep one debug run for suite cost, but replay the
    // measured six-run release profile so a hidden wall-clock publication gate
    // cannot return unnoticed.
    let runs = if cfg!(debug_assertions) { 1 } else { 6 };
    for run in 1..=runs {
        let commands = ay_frontend::parse(&smt).expect("proof-mode #7956 input must parse");
        let mut executor = ay_dpll::Executor::new();
        executor.set_produce_proofs(true);
        executor.set_deadline(Some(
            std::time::Instant::now() + std::time::Duration::from_secs(20),
        ));
        executor.set_memory_limit(Some(8 << 30));
        let output = executor
            .execute_all(&commands)
            .expect("proof-mode #7956 execution should succeed");
        let result = output
            .iter()
            .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
            .map(|line| SolverOutcome::from_output_line(line))
            .unwrap_or(SolverOutcome::Unknown);
        assert_eq!(
            result,
            SolverOutcome::Unsat,
            "singleton-prefix array ext_eq should prove v equals vec[0] \
             deterministically (run {run}/{runs})"
        );
        let alethe = executor
            .try_export_last_proof_alethe_for_problem_scope()
            .expect("proof-mode #7956 UNSAT must retain a proof")
            .expect("proof-mode #7956 Alethe export must succeed");
        assert!(
            !alethe.contains(":rule trust") && !alethe.contains(":rule hole"),
            "#7956 proof must contain no unchecked rule (run {run}/{runs}): {alethe}"
        );
        assert!(
            alethe.contains(":rule arrays_idx")
                && alethe.contains(":rule la_generic")
                && alethe.contains(":rule cong")
                && alethe.contains(":rule implies_pos"),
            "#7956 proof must externally certify ROW1, its surface-index bridge, \
             and the authored implication \
             (run {run}/{runs}): {alethe}"
        );
    }
}

/// Exact verification-consumer ext_eq encoding: Tseitin Bool variable with three axioms,
/// pointwise quantifier has NO triggers (matches verification-consumer's `self.solver.forall`).
///
/// SAT witness: v=42, vec has len >= 1 with index 0 = 42, next = anything.
const QUANTIFIER_CONSUMER_EXT_EQ_TSEITIN: &str = r#"
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

; Background axioms with triggers (from verification-consumer's Seq axiom set)
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton axioms (concrete array shape)
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; === QuantifierConsumer ext_eq Tseitin encoding ===
; ext_eq_0 is a fresh Bool constant (Tseitin variable)
(declare-const ext_eq_0 Bool)

; Axiom 1: ext_eq_0 => len(vec) == len(concat(singleton(v), next))
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))

; Axiom 2: ext_eq_0 => forall i. bounds => pointwise equality
; NOTE: NO TRIGGERS (matches verification-consumer's self.solver.forall without triggers)
(assert (=> ext_eq_0
  (forall ((ext_eq_i Int))
    (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
        (= (seq_index_logic vec ext_eq_i)
           (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i))))))

; Axiom 3: (len_eq AND pointwise) => ext_eq_0
(assert (=> (and (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))
                 (forall ((ext_eq_i Int))
                   (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
                       (= (seq_index_logic vec ext_eq_i)
                          (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i)))))
            ext_eq_0))

; === VC body ===
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))

; Ground bridge seeds (verification-consumer adds these)
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))

(check-sat)
"#;

/// #7956: the core verification-consumer ext_eq encoding has a known SAT witness
/// (`v = 42`, `len(vec) = 1`), but its triggerless quantified ext-equality
/// currently has no total materialized and rechecked model. The generic
/// UF-completion shape shortcut is not SAT authority, so AY must fail closed.
#[test]
fn test_quantifier_consumer_ext_eq_tseitin_fails_closed_without_total_model_7956() {
    let result = run_executor_smt_with_timeout(QUANTIFIER_CONSUMER_EXT_EQ_TSEITIN, 60)
        .expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Unknown,
        "#7956: the SAT instance must remain fail-closed without a total-model certificate"
    );
}

/// Variant with push/pop refutation proof (verification-consumer's primary usage pattern).
/// First check: negate v==42 (should be UNSAT because it IS provable).
/// Second check: the semantically SAT formula may fail closed to UNKNOWN.
const QUANTIFIER_CONSUMER_EXT_EQ_PUSH_POP: &str = r#"
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

; Background axioms
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; ext_eq Tseitin
(declare-const ext_eq_0 Bool)
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))
(assert (=> ext_eq_0
  (forall ((ext_eq_i Int))
    (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
        (= (seq_index_logic vec ext_eq_i)
           (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i))))))
(assert (=> (and (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))
                 (forall ((ext_eq_i Int))
                   (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
                       (= (seq_index_logic vec ext_eq_i)
                          (seq_index_logic (seq_concat (seq_singleton v) next) ext_eq_i)))))
            ext_eq_0))

; Refutation check: preconditions + negated postcondition
(push 1)
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))
; Negate: v == 42 (this IS provable, so UNSAT is correct)
(assert (not (= v 42)))
(check-sat)
(pop 1)

; SAT check: preconditions alone (should be SAT)
(push 1)
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))
(check-sat)
(pop 1)
"#;

/// #7956: Push/pop refutation proof pattern must work correctly.
/// First check-sat should be UNSAT (v==42 is provable, so not(v==42) is UNSAT).
/// Second check-sat is satisfiable but may be UNKNOWN without a total model.
///
/// Note: `run_executor_smt_with_timeout` returns the FIRST check-sat result,
/// so we verify only the refutation proof (UNSAT) here. The fail-closed
/// satisfiable check is covered by
/// `test_quantifier_consumer_ext_eq_tseitin_fails_closed_without_total_model_7956`.
///
/// That claim about the helper was FALSE until the helper was fixed: it
/// returned `Timeout` without reading any output line whenever the interrupt
/// had fired, so this script's divergent SECOND `check-sat` made the FIRST
/// one's verdict unobservable. Any assertion here was therefore reading a
/// timeout, not a refutation. The helper now prefers a verdict the run already
/// produced, so the comment above describes what actually happens.
#[test]
fn test_quantifier_consumer_ext_eq_push_pop_refutation_7956() {
    let result = run_executor_smt_with_timeout(QUANTIFIER_CONSUMER_EXT_EQ_PUSH_POP, 60)
        .expect("execution should succeed");
    // The first check-sat negates v==42. Since v==42 is provable from the
    // axioms (ext_eq + concat-left + bridge), this should be genuinely UNSAT.
    assert_eq!(
        result,
        SolverOutcome::Unsat,
        "#7956: push/pop refutation: negated v==42 should be UNSAT (provable)"
    );
}

/// Variant with empty seq and ext_eq(vec, concat(singleton(v), empty)).
/// This is a common verification-consumer pattern for single-element sequences.
const QUANTIFIER_CONSUMER_EXT_EQ_EMPTY_NEXT: &str = r#"
(set-logic AUFLIA)

(declare-sort Seq 0)
(declare-fun seq_len (Seq) Int)
(declare-fun seq_offset (Seq) Int)
(declare-fun seq_array (Seq) (Array Int Int))
(declare-fun seq_index_logic (Seq Int) Int)
(declare-fun seq_concat (Seq Seq) Seq)
(declare-fun seq_singleton (Int) Seq)
(declare-fun seq_empty () Seq)

(declare-const vec Seq)
(declare-const v Int)

; Background axioms
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; Empty seq
(assert (= (seq_array seq_empty) ((as const (Array Int Int)) 0)))
(assert (= (seq_len seq_empty) 0))
(assert (= (seq_offset seq_empty) 0))

; ext_eq Tseitin (with empty next)
(declare-const ext_eq_0 Bool)
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) seq_empty)))))
(assert (=> ext_eq_0
  (forall ((ext_eq_i Int))
    (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
        (= (seq_index_logic vec ext_eq_i)
           (seq_index_logic (seq_concat (seq_singleton v) seq_empty) ext_eq_i))))))
(assert (=> (and (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) seq_empty)))
                 (forall ((ext_eq_i Int))
                   (=> (and (>= ext_eq_i 0) (< ext_eq_i (seq_len vec)))
                       (= (seq_index_logic vec ext_eq_i)
                          (seq_index_logic (seq_concat (seq_singleton v) seq_empty) ext_eq_i)))))
            ext_eq_0))

; VC body
(assert ext_eq_0)
(assert (= (seq_index_logic vec 0) 42))

(check-sat)
"#;

/// #7956 variant: ext_eq with an empty `next` sequence is satisfiable, but AY
/// must fail closed until it constructs and rechecks a total quantified model.
///
/// The guard entails the finite range `{0}`, so bounded instantiation can cover
/// the pointwise obligation. That still does not construct a total shared model
/// for every surrounding sequence helper axiom, so the final SAT side is kept
/// fail-closed rather than relying on per-axiom syntax.
#[test]
fn test_quantifier_consumer_ext_eq_empty_next_fails_closed_7956() {
    let result = run_executor_smt_with_timeout(QUANTIFIER_CONSUMER_EXT_EQ_EMPTY_NEXT, 60)
        .expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Unknown,
        "#7956 variant: ext_eq with empty next lacks a total quantified model certificate"
    );
}

/// Variant matching the original #6920 reproducer but using the verification-consumer
/// Tseitin encoding style instead of direct ext_eq Bool constant.
/// This bridges the two test patterns.
const QUANTIFIER_CONSUMER_EXT_EQ_WITH_TRIGGERS: &str = r#"
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
(declare-const ext_eq_0 Bool)

; Background axioms with triggers
(assert (forall ((s Seq)) (! (>= (seq_len s) 0) :pattern ((seq_len s)))))
(assert (forall ((s Seq) (i Int))
  (! (= (seq_index_logic s i)
        (select (seq_array s) (+ (seq_offset s) i)))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s1 Seq) (s2 Seq))
  (! (= (seq_len (seq_concat s1 s2)) (+ (seq_len s1) (seq_len s2)))
     :pattern ((seq_concat s1 s2)))))
(assert (forall ((s1 Seq) (s2 Seq) (i Int))
  (! (=> (and (>= i 0) (< i (seq_len s1)))
         (= (seq_index_logic (seq_concat s1 s2) i) (seq_index_logic s1 i)))
     :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Singleton
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; ext_eq Tseitin WITH triggers on pointwise quantifier
(assert (=> ext_eq_0 (= (seq_len vec) (seq_len (seq_concat (seq_singleton v) next)))))
(assert (=> ext_eq_0
  (forall ((i Int))
    (! (=> (and (>= i 0) (< i (seq_len vec)))
           (= (seq_index_logic vec i)
              (seq_index_logic (seq_concat (seq_singleton v) next) i)))
       :pattern ((seq_index_logic vec i))
       :pattern ((seq_index_logic (seq_concat (seq_singleton v) next) i))))))

; VC body
(assert ext_eq_0)
(assert (= (select (seq_array vec) (+ (seq_offset vec) 0)) 42))
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))

(check-sat)
"#;

/// #7956 variant with explicit triggers remains satisfiable, but trigger
/// coverage alone is not a total-model certificate.
#[test]
fn test_quantifier_consumer_ext_eq_with_triggers_fails_closed_7956() {
    let result = run_executor_smt_with_timeout(QUANTIFIER_CONSUMER_EXT_EQ_WITH_TRIGGERS, 60)
        .expect("execution should succeed");
    assert_eq!(
        result,
        SolverOutcome::Unknown,
        "#7956 variant: ext_eq triggers do not establish a total model"
    );
}
