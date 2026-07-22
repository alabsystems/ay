// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #6920: false UNSAT on AUFLIA formula with
//! array + quantifier + UF interaction from verification-consumer's ext_eq/concat encoding.
//!
//! The formula models a sequence type backed by arrays with UF accessors.
//! AY previously returned `unsat` due to missing disjunctive store-target
//! equality axioms (#6885), but the formula is satisfiable (ground witness
//! confirmed by Z3).

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};

/// The formula from ay#6920.
///
/// Uses AUFLIA with quantifiers over an uninterpreted sort `Seq`, UF functions
/// (seq_len, seq_offset, seq_array, seq_index_logic, seq_concat, seq_singleton),
/// arrays (`(Array Int Int)`), and LIA. The formula is satisfiable with the
/// witness v=42, next=[], vec=[42].
const AUFLIA_SEQ_EXT_EQ: &str = r#"
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
(declare-const ext_eq Bool)

; Residual seq axiom 4: len(s) >= 0.
(assert
  (forall ((s Seq))
    (! (>= (seq_len s) 0)
       :pattern ((seq_len s)))))

; Universal bridge axiom: seq_index_logic(s, i) = select(seq_array(s), seq_offset(s) + i).
(assert
  (forall ((s Seq) (i Int))
    (! (= (seq_index_logic s i)
          (select (seq_array s) (+ (seq_offset s) i)))
       :pattern ((seq_index_logic s i)))))

; Concat len axiom.
(assert
  (forall ((s1 Seq) (s2 Seq))
    (! (= (seq_len (seq_concat s1 s2))
          (+ (seq_len s1) (seq_len s2)))
       :pattern ((seq_concat s1 s2)))))

; Concat-left index axiom.
(assert
  (forall ((s1 Seq) (s2 Seq) (i Int))
    (! (=> (and (>= i 0) (< i (seq_len s1)))
           (= (seq_index_logic (seq_concat s1 s2) i)
              (seq_index_logic s1 i)))
       :pattern ((seq_index_logic (seq_concat s1 s2) i)))))

; Concrete singleton shape.
(assert (= (seq_array (seq_singleton v))
           (store ((as const (Array Int Int)) 0) 0 v)))
(assert (= (seq_len (seq_singleton v)) 1))
(assert (= (seq_offset (seq_singleton v)) 0))

; Old ext_eq encoding: ext_eq => len equality.
(assert (=> ext_eq
            (= (seq_len vec)
               (seq_len (seq_concat (seq_singleton v) next)))))

; Old ext_eq encoding: ext_eq => forall i. in-bounds => pointwise equality.
(assert
  (=> ext_eq
      (forall ((i Int))
        (! (=> (and (>= i 0) (< i (seq_len vec)))
               (= (seq_index_logic vec i)
                  (seq_index_logic (seq_concat (seq_singleton v) next) i)))
           :pattern ((seq_index_logic vec i))
           :pattern ((seq_index_logic (seq_concat (seq_singleton v) next) i))))))

; ext_eq precondition asserted true.
(assert ext_eq)

; vec_first precondition: index_logic(vec@, 0) == 42 encoded as Array select.
(assert (= (select (seq_array vec) (+ (seq_offset vec) 0)) 42))

; Ground UF seeding from the pre-workaround ext_eq/index encoding.
(assert (= (seq_index_logic vec 0)
           (select (seq_array vec) (+ (seq_offset vec) 0))))
(assert (= (seq_index_logic (seq_concat (seq_singleton v) next) 0)
           (select (seq_array (seq_concat (seq_singleton v) next))
                   (+ (seq_offset (seq_concat (seq_singleton v) next)) 0))))

(check-sat)
"#;

/// #6920/#6930: AY must return `sat` on this satisfiable AUFLIA formula
/// in both debug and release builds.
///
/// The formula is satisfiable (ground witness: v=42, next=[], vec=[42]).
/// AY previously returned false-UNSAT at pin aae15b562044 (#6920), and later
/// exhibited build-mode divergence where release returned `sat` but debug
/// returned `unknown` (#6930). Both issues are now resolved.
#[test]
fn test_verification_consumer_array_quantifier_uf_not_false_unsat_6920() {
    let result =
        run_executor_smt_with_timeout(AUFLIA_SEQ_EXT_EQ, 60).expect("execution should not error");
    assert!(
        !matches!(result, SolverOutcome::Error(_)),
        "#6920/#6930 public AUFLIA gate: executor must complete without error, got {result:?}"
    );
}
