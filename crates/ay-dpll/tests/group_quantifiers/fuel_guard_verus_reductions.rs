// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verus queries, reduced by delta debugging, whose fuel guard ay can only
//! derive through other facts (#unit-bool-eq, #conjunctive-closure,
//! #unit-bcp; Verus fix queue row D1). The small hand-written cases live in
//! `fuel_guarded_definitions.rs`.
//!
//! Ground truth for every fixture is in its doc comment and was checked with
//! z3 4.12.5 (the solver Verus ships).

/// Reduced from Verus `modules::test_mod_adt_1`. The guard
/// `(fuel_bool is_four_doors)` follows only from `(fuel_bool_default
/// is_four_doors)` through the instance of the `fuel_defaults` axiom, and the
/// refutation needs the accessor instance at a term that only the
/// definition's own instance contains. **GROUND TRUTH: UNSAT** (z3 4.12.5).
/// Before #unit-bool-eq and #conjunctive-closure: `unknown`. With the car built
/// from `false` instead of `true` the goal holds: **SAT** (z3 4.12.5).
const GUARD_DERIVED_THROUGH_AN_INSTANCE: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
))))
(declare-sort Poly 0)
(declare-fun B (Bool) Poly)
(declare-fun %B (Poly) Bool)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-fun has_type (Poly Type) Bool)
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
)))
(declare-const fuel%test_crate!M1.is_four_doors. FuelId)
(declare-datatypes ((test_crate!M1.Car. 0) (tuple%0. 0)) (((test_crate!M1.Car./Car (test_crate!M1.Car./Car/?four_doors
     Bool
   ))
  ) ((tuple%0./tuple%0))
))
(declare-fun test_crate!M1.Car./Car/four_doors (test_crate!M1.Car.) Bool)
(declare-fun Poly%test_crate!M1.Car. (test_crate!M1.Car.) Poly)
(declare-fun %Poly%test_crate!M1.Car. (Poly) test_crate!M1.Car.)
(assert
 (forall ((x test_crate!M1.Car.)) (!
   (= x (%Poly%test_crate!M1.Car. (Poly%test_crate!M1.Car. x)))
   :pattern ((Poly%test_crate!M1.Car. x))
)))
(assert
 (forall ((x test_crate!M1.Car.)) (!
   (= (test_crate!M1.Car./Car/four_doors x) (test_crate!M1.Car./Car/?four_doors x))
   :pattern ((test_crate!M1.Car./Car/four_doors x))
)))
(declare-fun test_crate!M1.is_four_doors.? (Poly) Bool)
(assert
 (fuel_bool_default fuel%test_crate!M1.is_four_doors.)
)
(assert
 (=>
  (fuel_bool fuel%test_crate!M1.is_four_doors.)
  (forall ((c! Poly)) (!
    (= (test_crate!M1.is_four_doors.? c!) (test_crate!M1.Car./Car/four_doors (%Poly%test_crate!M1.Car.
       c!
    )))
    :pattern ((test_crate!M1.is_four_doors.? c!))
))))
(declare-const tmp%1 Bool)
(declare-const c@ test_crate!M1.Car.)
(assert
 fuel_defaults
)
(declare-const %%location_label%%0 Bool)
(assert
 (not (=>
   (= c@ (test_crate!M1.Car./Car (%B (B true))))
   (=>
    (= tmp%1 (test_crate!M1.is_four_doors.? (Poly%test_crate!M1.Car. c@)))
    (=>
     %%location_label%%0
     tmp%1
)))))
(check-sat)
"#;

/// Reduced from Verus `regression::test_189a`. The set lemmas' guards follow
/// from `(fuel_bool_default group_vstd_default)` through two asserted
/// implications of vstd's broadcast groups and then the `fuel_defaults`
/// axiom. **GROUND TRUTH: UNSAT** (z3 4.12.5). Before #unit-bcp: `unknown`.
const GUARD_DERIVED_THROUGH_BROADCAST_GROUPS: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
))))
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-sort Type 0)
(declare-fun SINT (Int) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-fun has_type (Poly Type) Bool)
(declare-fun sized (Dcr) Bool)
(assert
 (sized $)
)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iHi 32) 2147483648)
)
(declare-fun iInv (Int Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
)))
(declare-const fuel%vstd!set.axiom_set_empty. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_same. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_different. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal_deep. FuelId)
(declare-const fuel%vstd!array.group_array_axioms. FuelId)
(declare-const fuel%vstd!function.group_function_axioms. FuelId)
(declare-const fuel%vstd!laws_cmp.group_laws_cmp. FuelId)
(declare-const fuel%vstd!laws_eq.group_laws_eq. FuelId)
(declare-const fuel%vstd!layout.group_layout_axioms. FuelId)
(declare-const fuel%vstd!map.group_map_axioms. FuelId)
(declare-const fuel%vstd!multiset.group_multiset_axioms. FuelId)
(declare-const fuel%vstd!raw_ptr.group_raw_ptr_axioms. FuelId)
(declare-const fuel%vstd!seq.group_seq_axioms. FuelId)
(declare-const fuel%vstd!seq_lib.group_seq_lib_default. FuelId)
(declare-const fuel%vstd!set.group_set_axioms. FuelId)
(declare-const fuel%vstd!set_lib.group_set_lib_default. FuelId)
(declare-const fuel%vstd!slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!string.group_string_axioms. FuelId)
(declare-const fuel%vstd!std_specs.bits.group_bits_axioms. FuelId)
(declare-const fuel%vstd!std_specs.control_flow.group_control_flow_axioms. FuelId)
(declare-const fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms. FuelId)
(declare-const fuel%vstd!std_specs.btree.group_btree_axioms. FuelId)
(declare-const fuel%vstd!std_specs.hash.group_hash_axioms. FuelId)
(declare-const fuel%vstd!std_specs.range.group_range_axioms. FuelId)
(declare-const fuel%vstd!std_specs.slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vec.group_vec_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms. FuelId)
(declare-const fuel%vstd!group_vstd_default. FuelId)
(assert
 (=>
  (fuel_bool_default fuel%vstd!set.group_set_axioms.)
  (and
   (fuel_bool_default fuel%vstd!set.axiom_set_empty.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_same.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_different.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal_deep.)
)))
(assert
 (fuel_bool_default fuel%vstd!group_vstd_default.)
)
(assert
 (=>
  (fuel_bool_default fuel%vstd!group_vstd_default.)
  (and
   (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
   (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
   (fuel_bool_default fuel%vstd!map.group_map_axioms.)
   (fuel_bool_default fuel%vstd!set.group_set_axioms.)
   (fuel_bool_default fuel%vstd!set_lib.group_set_lib_default.)
   (fuel_bool_default fuel%vstd!multiset.group_multiset_axioms.)
   (fuel_bool_default fuel%vstd!function.group_function_axioms.)
   (fuel_bool_default fuel%vstd!laws_eq.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_cmp.group_laws_cmp.)
   (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!array.group_array_axioms.)
   (fuel_bool_default fuel%vstd!string.group_string_axioms.)
   (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
   (fuel_bool_default fuel%vstd!layout.group_layout_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.range.group_range_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.bits.group_bits_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.control_flow.group_control_flow_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vec.group_vec_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.hash.group_hash_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.btree.group_btree_axioms.)
)))
(declare-sort vstd!set.Set<i32.>. 0)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-fun Poly%vstd!set.Set<i32.>. (vstd!set.Set<i32.>.) Poly)
(declare-fun %Poly%vstd!set.Set<i32.>. (Poly) vstd!set.Set<i32.>.)
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. $ (SINT 32)))
    (= x (Poly%vstd!set.Set<i32.>. (%Poly%vstd!set.Set<i32.>. x)))
   )
   :pattern ((has_type x (TYPE%vstd!set.Set. $ (SINT 32))))
)))
(declare-fun vstd!set.Set.contains.? (Dcr Type Poly Poly) Bool)
(declare-fun vstd!set.Set.empty.? (Dcr Type) Poly)
(declare-fun vstd!set.Set.insert.? (Dcr Type Poly Poly) Poly)
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (has_type (vstd!set.Set.empty.? A&. A&) (TYPE%vstd!set.Set. A&. A&))
   :pattern ((vstd!set.Set.empty.? A&. A&))
)))
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_empty.)
  (forall ((A&. Dcr) (A& Type) (a! Poly)) (!
    (=>
     (has_type a! A&)
     (=>
      (sized A&.)
      (not (vstd!set.Set.contains.? A&. A& (vstd!set.Set.empty.? A&. A&) a!))
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.empty.? A&. A&) a!))
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!set.Set.insert.? A&. A& self! a!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.Set.insert.? A&. A& self! a!))
)))
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!) a!)
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!) a!))
))))
(declare-const tmp%1 Bool)
(declare-const tmp%2 Bool)
(declare-const s1@ vstd!set.Set<i32.>.)
(declare-const s2@ vstd!set.Set<i32.>.)
(assert
 fuel_defaults
)
(declare-const %%location_label%%0 Bool)
(declare-const %%location_label%%1 Bool)
(assert
 (not (=>
   (= s1@ (%Poly%vstd!set.Set<i32.>. (vstd!set.Set.insert.? $ (SINT 32) (vstd!set.Set.empty.?
       $ (SINT 32)
      ) (I 1)
   )))
   (=>
    (= s2@ (%Poly%vstd!set.Set<i32.>. (vstd!set.Set.empty.? $ (SINT 32))))
    (=>
     (= tmp%1 (not (vstd!set.Set.contains.? $ (SINT 32) (Poly%vstd!set.Set<i32.>. s2@) (I
         1
     ))))
     (and
      (=>
       %%location_label%%0
       tmp%1
      )
      (=>
       tmp%1
       (=>
        (= tmp%2 (not (= s1@ s2@)))
        (=>
         %%location_label%%1
         tmp%2
)))))))))
(check-sat)
"#;

fn verdicts(smt: &str) -> Vec<String> {
    crate::common::solve_vec(smt)
}

/// CAPABILITY: before #unit-bool-eq and #conjunctive-closure this answered
/// `unknown`.
#[test]
fn a_definition_guarded_through_an_instance_refutes() {
    let results = verdicts(GUARD_DERIVED_THROUGH_AN_INSTANCE);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "fuel_bool(f) = fuel_bool_default(f) = true, so the definition and \
         the accessor refute the goal; got {results:?}"
    );
}

/// SOUNDNESS FLOOR: the same query with the goal made true.
#[test]
fn a_definition_guarded_through_an_instance_never_refutes_a_true_goal() {
    let smt = GUARD_DERIVED_THROUGH_AN_INSTANCE.replace("(B true)", "(B false)");
    assert_ne!(smt, GUARD_DERIVED_THROUGH_AN_INSTANCE);
    for results in [verdicts(&smt), crate::common::solve_selfcheck_vec(&smt)] {
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG ANSWER: this query is SATISFIABLE; got {results:?}"
        );
    }
}

/// CAPABILITY: before #unit-bcp this answered `unknown`.
#[test]
fn a_lemma_enabled_through_broadcast_groups_refutes() {
    let results = verdicts(GUARD_DERIVED_THROUGH_BROADCAST_GROUPS);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the vstd default group enables the set lemmas, which refute the \
         goal; got {results:?}"
    );
}

/// The recovered refutations never become `sat` in any posture.
#[test]
fn the_reduced_queries_are_never_sat() {
    for smt in [
        GUARD_DERIVED_THROUGH_AN_INSTANCE,
        GUARD_DERIVED_THROUGH_BROADCAST_GROUPS,
    ] {
        for results in [verdicts(smt), crate::common::solve_selfcheck_vec(smt)] {
            assert!(
                !results.iter().any(|r| r == "sat"),
                "WRONG ANSWER: the query is UNSATISFIABLE; got {results:?}"
            );
        }
    }
}
