// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for splitting a quantified predicate definition when no
//! proof is published (#iff-split-definition, Verus fix queue, row D).
//!
//! The Boolean-equality split leaves a universal whose body is a predicate
//! definition `(= (p x̄) φ)` whole in the default posture, because the negative
//! copy of a quantifier in `φ` would get a Skolem function of the binders
//! that no proof record binds (`quantifier_under_boolean_equality.rs`). With
//! the proof cycle shed, the CLI's `--z3-mode` posture, it is split: Verus
//! states every lemma's ensures as such a definition.

/// Reduced from the z3 unsat core of a Verus `ext_equal` lemma query:
/// `ens%lemma_ext_equal(x, y)` is DEFINED as
/// `(= (ext_eq x y) (forall i. 0 <= i < 4 => x[i] = y[i]))`, the four
/// elements agree, and the goal denies `x = y`. **GROUND TRUTH: UNSAT**
/// (z3 4.12.5). The inner universal is reached only through the definition's
/// negative side, so the refutation needs the definition split; its witness is
/// then a Skolem function of the definition's binders, which no proof record
/// binds, so only a solve that publishes without a proof splits it
/// (#iff-split-definition).
const LEMMA_EXT_EQUAL: &str = r#"
(declare-sort %%Function%% 0)
(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(declare-sort Type 0)
(declare-const INT Type)
(declare-fun UINT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun has_type (Poly Type) Bool)
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-sort test_crate!m1.Seq4<u8.>. 0)
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-fun TYPE%test_crate!m1.Seq4. (Dcr Type) Type)
(declare-fun Poly%test_crate!m1.Seq4<u8.>. (test_crate!m1.Seq4<u8.>.) Poly)
(declare-fun %Poly%test_crate!m1.Seq4<u8.>. (Poly) test_crate!m1.Seq4<u8.>.)
(assert
 (forall ((x test_crate!m1.Seq4<u8.>.)) (!
   (= x (%Poly%test_crate!m1.Seq4<u8.>. (Poly%test_crate!m1.Seq4<u8.>. x)))
   :pattern ((Poly%test_crate!m1.Seq4<u8.>. x))
   :qid internal_test_crate__m1__Seq4<u8.>_box_axiom_definition
   :skolemid skolem_internal_test_crate__m1__Seq4<u8.>_box_axiom_definition
)))
(declare-fun test_crate!m1.impl&%0.spec_index.? (Dcr Type Poly Poly) Poly)
(declare-fun ens%test_crate!m1.lemma_ext_equal. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (x! Poly) (y! Poly)) (!
   (= (ens%test_crate!m1.lemma_ext_equal. A&. A& x! y!) (= (ext_eq false (TYPE%test_crate!m1.Seq4.
       A&. A&
      ) x! y!
     ) (forall ((i$ Poly)) (!
       (=>
        (has_type i$ INT)
        (=>
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$1 (%I i$)))
           (let
            ((tmp%%$2 4))
            (and
             (<= tmp%%$ tmp%%$1)
             (< tmp%%$1 tmp%%$2)
         ))))
         (= (test_crate!m1.impl&%0.spec_index.? A&. A& x! i$) (test_crate!m1.impl&%0.spec_index.?
           A&. A& y! i$
       ))))
       :pattern ((test_crate!m1.impl&%0.spec_index.? A&. A& x! i$))
       :pattern ((test_crate!m1.impl&%0.spec_index.? A&. A& y! i$))
       :qid user_test_crate__m1__lemma_ext_equal_0
       :skolemid skolem_user_test_crate__m1__lemma_ext_equal_0
   ))))
   :pattern ((ens%test_crate!m1.lemma_ext_equal. A&. A& x! y!))
   :qid internal_ens__test_crate!m1.lemma_ext_equal._definition
   :skolemid skolem_internal_ens__test_crate!m1.lemma_ext_equal._definition
)))
(declare-const x! test_crate!m1.Seq4<u8.>.)
(declare-const y! test_crate!m1.Seq4<u8.>.)
(declare-const tmp%1 Bool)
(assert
 (= (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
   (I 0)
  ) (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. y!)
   (I 0)
)))
(assert
 (= (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
   (I 1)
  ) (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. y!)
   (I 1)
)))
(assert
 (= (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
   (I 2)
  ) (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. y!)
   (I 2)
)))
(assert
 (= (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
   (I 3)
  ) (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. y!)
   (I 3)
)))
(declare-const %%location_label%%0 Bool)
(assert
 (not (=>
   (ens%test_crate!m1.lemma_ext_equal. $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
    (Poly%test_crate!m1.Seq4<u8.>. y!)
   )
   (=>
    (= tmp%1 (= x! y!))
    (=>
     %%location_label%%0
     tmp%1
)))))
(check-sat)
"#;

/// `LEMMA_EXT_EQUAL` without the equality at index 3. **GROUND TRUTH: SAT**
/// (z3 times out): x and y differ at 3, so both sides of the definition are
/// false, the lemma's ensures holds, and the goal's `x = y` is false.
const LEMMA_EXT_EQUAL_SAT: &str = r#"
(declare-sort %%Function%% 0)
(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(declare-sort Type 0)
(declare-const INT Type)
(declare-fun UINT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun has_type (Poly Type) Bool)
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-sort test_crate!m1.Seq4<u8.>. 0)
(declare-datatypes ((tuple%0. 0)) (((tuple%0./tuple%0))))
(declare-fun TYPE%test_crate!m1.Seq4. (Dcr Type) Type)
(declare-fun Poly%test_crate!m1.Seq4<u8.>. (test_crate!m1.Seq4<u8.>.) Poly)
(declare-fun %Poly%test_crate!m1.Seq4<u8.>. (Poly) test_crate!m1.Seq4<u8.>.)
(assert
 (forall ((x test_crate!m1.Seq4<u8.>.)) (!
   (= x (%Poly%test_crate!m1.Seq4<u8.>. (Poly%test_crate!m1.Seq4<u8.>. x)))
   :pattern ((Poly%test_crate!m1.Seq4<u8.>. x))
   :qid internal_test_crate__m1__Seq4<u8.>_box_axiom_definition
   :skolemid skolem_internal_test_crate__m1__Seq4<u8.>_box_axiom_definition
)))
(declare-fun test_crate!m1.impl&%0.spec_index.? (Dcr Type Poly Poly) Poly)
(declare-fun ens%test_crate!m1.lemma_ext_equal. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (x! Poly) (y! Poly)) (!
   (= (ens%test_crate!m1.lemma_ext_equal. A&. A& x! y!) (= (ext_eq false (TYPE%test_crate!m1.Seq4.
       A&. A&
      ) x! y!
     ) (forall ((i$ Poly)) (!
       (=>
        (has_type i$ INT)
        (=>
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$1 (%I i$)))
           (let
            ((tmp%%$2 4))
            (and
             (<= tmp%%$ tmp%%$1)
             (< tmp%%$1 tmp%%$2)
         ))))
         (= (test_crate!m1.impl&%0.spec_index.? A&. A& x! i$) (test_crate!m1.impl&%0.spec_index.?
           A&. A& y! i$
       ))))
       :pattern ((test_crate!m1.impl&%0.spec_index.? A&. A& x! i$))
       :pattern ((test_crate!m1.impl&%0.spec_index.? A&. A& y! i$))
       :qid user_test_crate__m1__lemma_ext_equal_0
       :skolemid skolem_user_test_crate__m1__lemma_ext_equal_0
   ))))
   :pattern ((ens%test_crate!m1.lemma_ext_equal. A&. A& x! y!))
   :qid internal_ens__test_crate!m1.lemma_ext_equal._definition
   :skolemid skolem_internal_ens__test_crate!m1.lemma_ext_equal._definition
)))
(declare-const x! test_crate!m1.Seq4<u8.>.)
(declare-const y! test_crate!m1.Seq4<u8.>.)
(declare-const tmp%1 Bool)
(assert
 (= (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
   (I 0)
  ) (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. y!)
   (I 0)
)))
(assert
 (= (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
   (I 1)
  ) (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. y!)
   (I 1)
)))
(assert
 (= (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
   (I 2)
  ) (test_crate!m1.impl&%0.spec_index.? $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. y!)
   (I 2)
)))
(declare-const %%location_label%%0 Bool)
(assert
 (not (=>
   (ens%test_crate!m1.lemma_ext_equal. $ (UINT 8) (Poly%test_crate!m1.Seq4<u8.>. x!)
    (Poly%test_crate!m1.Seq4<u8.>. y!)
   )
   (=>
    (= tmp%1 (= x! y!))
    (=>
     %%location_label%%0
     tmp%1
)))))
(check-sat)
"#;

/// Verdicts with the proof cycle shed, the CLI's `--z3-mode` posture.
fn proof_shed_verdict(smt: &str) -> String {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_competition_mode(true);
    exec.set_timeout(Some(std::time::Duration::from_secs(30)));
    let lines = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    lines
        .iter()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "none".to_string())
}

/// With the proof cycle shed, a quantified predicate definition is split, so
/// the refutation resting on its negative side is found (#iff-split-definition).
#[test]
fn a_definition_is_split_when_no_proof_is_published() {
    let got = proof_shed_verdict(LEMMA_EXT_EQUAL);
    assert_eq!(got, "unsat", "the lemma's definition refutes the goal");
}

/// The definition split never refutes a satisfiable query, in either posture,
/// and never answers `sat` on the refutable one.
#[test]
fn the_definition_split_never_gives_a_wrong_answer() {
    for results in [
        vec![proof_shed_verdict(LEMMA_EXT_EQUAL_SAT)],
        crate::common::solve_vec(LEMMA_EXT_EQUAL_SAT),
    ] {
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER: LEMMA_EXT_EQUAL_SAT is SATISFIABLE; got {results:?}"
        );
    }
    for results in [
        vec![proof_shed_verdict(LEMMA_EXT_EQUAL)],
        crate::common::solve_vec(LEMMA_EXT_EQUAL),
    ] {
        assert!(
            !results.iter().any(|r| r == "sat"),
            "WRONG ANSWER: LEMMA_EXT_EQUAL is UNSATISFIABLE; got {results:?}"
        );
    }
}
