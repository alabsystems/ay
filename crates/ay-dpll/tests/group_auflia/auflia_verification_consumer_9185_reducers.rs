// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY-side reducers from ay#9185 native replay artifacts.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

fn expect_sat(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert_eq!(result, SolverOutcome::Sat, "{label}: expected SAT");
}

fn expect_unknown(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert_eq!(result, SolverOutcome::Unknown, "{label}: expected UNKNOWN");
}

fn expect_not_sat(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert_ne!(result, SolverOutcome::Sat, "{label}: must not return SAT");
}

/// The counterpart of [`expect_not_sat`], and the one whose absence hid a wrong
/// answer: a ONE-SIDED assertion cannot catch a wrong verdict on the side it
/// permits. `expect_not_sat` accepts `unsat`, so a WRONG UNSAT passed as green.
/// Use this whenever the formula is satisfiable but AY is not yet expected to
/// prove it — it forbids the unsound direction while tolerating incompleteness.
fn expect_not_unsat(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert_ne!(
        result,
        SolverOutcome::Unsat,
        "{label}: must not return UNSAT (the formula is satisfiable)"
    );
}

fn expect_unsat(input: &str, label: &str) {
    let result = run_executor_smt_with_timeout(input, 30).expect("execution should succeed");
    assert_eq!(result, SolverOutcome::Unsat, "{label}: expected UNSAT");
}

#[test]
#[timeout(30_000)]
fn symbolic_address_frame_independence_frontend_reducer_is_sat() {
    expect_sat(
        include_str!(
            "../fixtures/verification_consumer_9185/symbolic_address_frame_independence_sat.smt2"
        ),
        "ay#9185 symbolic-address store/select reducer",
    );
}

#[test]
#[timeout(30_000)]
fn symbolic_address_frame_independence_native_reducer_is_sat() {
    expect_sat(
        include_str!(
            "../fixtures/verification_consumer_9185/symbolic_address_frame_independence_native_sat.smt2"
        ),
        "ay#9185 native symbolic-address frame reducer",
    );
}

#[test]
#[timeout(30_000)]
fn slice_index_has_value_usize_fails_closed_without_total_model() {
    expect_unknown(
        include_str!("../fixtures/verification_consumer_9185/slice_index_has_value_usize_sat.smt2"),
        "ay#9185 slice_index has_value_usize reducer",
    );
}

#[test]
#[timeout(30_000)]
fn slice_index_in_bounds_usize_fails_closed_without_total_model() {
    expect_unknown(
        include_str!("../fixtures/verification_consumer_9185/slice_index_in_bounds_usize_sat.smt2"),
        "ay#9185 slice_index in_bounds_usize reducer",
    );
}

#[test]
#[timeout(30_000)]
fn slice_index_in_bounds_range_inclusive_fails_closed_without_total_model() {
    expect_unknown(
        include_str!(
            "../fixtures/verification_consumer_9185/slice_index_in_bounds_range_inclusive_sat.smt2"
        ),
        "ay#9185 slice_index in_bounds_range_inclusive reducer",
    );
}

#[test]
#[timeout(30_000)]
fn option_constructor_membership_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun logic_Some (Int) Int)
(declare-fun __quantifier_consumer_is_option (Int) Bool)
(assert (forall ((opt_ax_v_86 Int))
    (! (__quantifier_consumer_is_option (logic_Some opt_ax_v_86))
       :pattern ((logic_Some opt_ax_v_86)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list option constructor-membership axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn option_constructor_membership_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun logic_Some (Int) Int)
(declare-fun __quantifier_consumer_is_option (Int) Bool)
(assert (not (__quantifier_consumer_is_option (logic_Some 0))))
(assert (forall ((opt_ax_v Int))
    (! (__quantifier_consumer_is_option (logic_Some opt_ax_v))
       :pattern ((logic_Some opt_ax_v)))))
(check-sat)
"#,
        "ay#8971/verification-consumer option constructor-membership contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn option_none_some_disjointness_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun logic_None () Int)
(declare-fun logic_Some (Int) Int)
(assert (forall ((opt_ax_some_none_v Int))
    (! (not (= logic_None (logic_Some opt_ax_some_none_v)))
       :pattern ((logic_Some opt_ax_some_none_v)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list option None/Some disjointness axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn option_constructor_name_disjointness_reducer_is_sat() {
    expect_sat(
        r#"
(set-logic AUFLIA)
(declare-sort OptionInt 0)
(declare-fun None () OptionInt)
(declare-fun Some (Int) OptionInt)
(declare-fun v () Int)
(assert (not (= None (Some v))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list OptionInt None/Some constructor-name disjointness",
    );
}

#[test]
#[timeout(30_000)]
fn option_none_some_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun logic_None () Int)
(declare-fun logic_Some (Int) Int)
(assert (= logic_None (logic_Some 0)))
(assert (forall ((opt_ax_some_none_v Int))
    (! (not (= logic_None (logic_Some opt_ax_some_none_v)))
       :pattern ((logic_Some opt_ax_some_none_v)))))
(check-sat)
"#,
        "ay#8971/verification-consumer option None/Some direct contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_symbolic_mod_bucket_index_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-fun self () MyHashMap)
(declare-fun key () Int)
(declare-fun seq_len_proxy () Int)
(declare-fun method_deep_model_1_i (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_K_P__P_hash__log__placeholder_i__ret_i (Int) Int)
(assert (= (logic_bucket__ix self (method_deep_model_1_i key))
           (mod (logic_K_P__P_hash__log__placeholder_i__ret_i
                    (method_deep_model_1_i key))
                seq_len_proxy)))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list symbolic modulo bucket index reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_symbolic_mod_bucket_index_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-fun self () MyHashMap)
(declare-fun key () Int)
(declare-fun seq_len_proxy () Int)
(declare-fun method_deep_model_1_i (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_K_P__P_hash__log__placeholder_i__ret_i (Int) Int)
(assert (= (method_deep_model_1_i key) 0))
(assert (= (logic_K_P__P_hash__log__placeholder_i__ret_i 0) 5))
(assert (= seq_len_proxy 2))
(assert (= (logic_bucket__ix self 0) 3))
(assert (= (logic_bucket__ix self (method_deep_model_1_i key))
           (mod (logic_K_P__P_hash__log__placeholder_i__ret_i
                    (method_deep_model_1_i key))
                seq_len_proxy)))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list symbolic modulo contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn datatype_seq_field_len_proxy_validation_gap_is_sat_9227() {
    expect_sat(
        r#"
(set-logic ALL)
(declare-datatypes ((MyHashMap 0))
  (((mk-map (buckets (Seq Int))))))
(declare-fun old_self () MyHashMap)
(declare-fun seq_len_proxy () Int)
(declare-fun seq_len ((Seq Int)) Int)
(assert (= (seq_len (buckets old_self)) seq_len_proxy))
(assert (= seq_len_proxy 1))
(check-sat)
"#,
        "ay#9227/verification-consumer datatype receiver seq_len proxy validation gap",
    );
}

#[test]
#[timeout(30_000)]
fn datatype_seq_uf_projection_validation_gap_is_sat_9227() {
    expect_sat(
        r#"
(set-logic ALL)
(declare-datatypes ((MyHashMap 0))
  (((mk-map (buckets (Seq Int))))))
(declare-fun old_self () MyHashMap)
(declare-fun seq_len_proxy () Int)
(declare-fun logic_field_buckets (MyHashMap) (Seq Int))
(declare-fun seq_len ((Seq Int)) Int)
(assert (= (buckets old_self) (logic_field_buckets old_self)))
(assert (= (seq_len (logic_field_buckets old_self)) seq_len_proxy))
(assert (= seq_len_proxy 1))
(check-sat)
"#,
        "ay#9227/verification-consumer datatype receiver UF seq projection validation gap",
    );
}

#[test]
#[timeout(30_000)]
fn symbolic_mod_range_disjunction_reducer_is_sat() {
    expect_sat(
        r#"
(set-logic AUFLIA)
(declare-fun dividend () Int)
(declare-fun divisor () Int)
(declare-fun len_a () Int)
(declare-fun len_b () Int)
(declare-fun len_c () Int)
(assert (or (= 0 len_a)
            (= 0 divisor)
            (not (<= 0 (mod dividend divisor)))
            (not (< (mod dividend divisor) len_b))
            (= 0 len_c)))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list symbolic modulo range disjunction reducer",
    );
}

#[test]
#[timeout(30_000)]
fn symbolic_mod_zero_divisor_branch_with_restore_equality_is_soundly_unknown() {
    // STALE PIN REFRESHED. The premise below is obsolete:
    //
    //   "Built-in non-string sequences do not yet have a complete model witness.
    //    Keep this satisfiable reducer behind the deliberate fail-closed gate:
    //    UNKNOWN is sound, whereas bypassing validation to recover SAT is not."
    //
    // Non-string sequences DO have a complete model witness now. The test's own
    // wording concedes the reducer is SATISFIABLE, and AY answers `sat` with a
    // complete model; z3 4.15.4 answers `sat` directly; and AY's published model
    // REPLAYS through z3 as `sat` against the original assertions. So this is
    // AY having closed a capability gap, not a gate being bypassed.
    //
    // Note this pin was `expect_unknown`, which — like the `expect_not_sat` on
    // its sibling above — is ONE-SIDED. That one hid a wrong `unsat` for as long
    // as it stood. This one only hid an improvement, but the shape is the same:
    // prefer an assertion that names the correct verdict.
    expect_sat(
        r#"
(set-logic ALL)
(declare-datatype List ((nil) (cons (hd Int) (tl List))))
(declare-fun list_current () List)
(declare-fun arg0_view () (Seq Int))
(declare-fun dividend () Int)
(declare-fun divisor () Int)
(declare-fun seq_len_proxy_48 () Int)
(declare-fun seq_len_proxy_60 () Int)
(declare-fun seq_len_proxy_68 () Int)
(declare-fun __seq_index_restore_List ((Seq Int) Int) List)
(assert (= list_current
           (__seq_index_restore_List arg0_view (mod dividend divisor))))
(assert (or (= 0 seq_len_proxy_48)
            (= 0 divisor)
            (not (<= 0 (mod dividend divisor)))
            (not (< (mod dividend divisor) seq_len_proxy_60))
            (= 0 seq_len_proxy_68)))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list symbolic mod zero-divisor restore branch",
    );
}

#[test]
#[timeout(30_000)]
fn symbolic_mod_zero_divisor_branch_with_restore_contradiction_is_not_sat() {
    // KNOWN-RED, PINNING A WRONG ANSWER. AY returns `unsat`; the formula is
    // SATISFIABLE and z3 4.15.4 produces an explicit witness:
    //
    //   dividend = -1, divisor = 0, mod0(-1, 0) = 0, arg0_view = (seq.unit 2),
    //   list_current = nil,
    //   __seq_index_restore_List = \v i. ite(v = (seq.unit 2) and i = -1,
    //                                        cons 5 nil, nil)
    //
    // Checked by hand against all three assertions:
    //   1. nil != (cons 5 nil)                       -> true
    //   2. nil  = restore(view, mod(-1,0)) = nil     -> true
    //   3. first disjunct `(= 0 seq_len_proxy_48)`   -> true
    //
    // SMT-LIB leaves `(mod a 0)` UNCONSTRAINED, so `mod dividend divisor` may
    // take the value 0 here. AY refutes a branch the problem explicitly allows.
    //
    // This assertion USED to be `expect_not_sat`, which accepts `unsat` — so a
    // WRONG UNSAT passed as green and the defect was invisible. That is the
    // failure mode recorded as "`disagree: 0` is not zero wrong answers": a
    // one-sided assertion cannot see a wrong answer on the side it permits.
    //
    // Isolated by controlled variant: dropping assertion 3 yields a sound
    // `unknown`, and adding a disjunction cannot make a formula unsat — so
    // assertion 3 is triggering a different code path (its extra `mod` atoms
    // bring in `mod_div_elim`), not narrowing the model space. Root cause is in
    // `executor/mod_div_elim/`; `mk_mod` itself is correct and already guards
    // div-by-zero (#div0-soundness).
    //
    // FIXED in `theories/combined/mod.rs`: `zero_mod_dividend` asserted the
    // identity `(mod a 0) == a`, which SMT-LIB does not grant, and
    // `assertions_have_quantifier_consumer_restore_zero_divisor_contradiction` turned that
    // into an outright `SolveResult::unsat()`. AY now answers `unknown` here —
    // sound but incomplete; `sat` remains the completeness goal.
    //
    // Asserted as NOT-UNSAT, deliberately. That is the SOUNDNESS property, and
    // it is the assertion that would have caught this from the start: the old
    // `expect_not_sat` permitted exactly the wrong answer AY was giving.
    expect_not_unsat(
        r#"
(set-logic ALL)
(declare-datatype List ((nil) (cons (hd Int) (tl List))))
(declare-fun list_current () List)
(declare-fun arg0_view () (Seq Int))
(declare-fun dividend () Int)
(declare-fun divisor () Int)
(declare-fun seq_len_proxy_48 () Int)
(declare-fun seq_len_proxy_60 () Int)
(declare-fun seq_len_proxy_68 () Int)
(declare-fun __seq_index_restore_List ((Seq Int) Int) List)
(assert (not (= list_current
                (__seq_index_restore_List arg0_view dividend))))
(assert (= list_current
           (__seq_index_restore_List arg0_view (mod dividend divisor))))
(assert (or (= 0 seq_len_proxy_48)
            (= 0 divisor)
            (not (<= 0 (mod dividend divisor)))
            (not (< (mod dividend divisor) seq_len_proxy_60))
            (= 0 seq_len_proxy_68)))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list symbolic mod zero-divisor restore contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_elem_list_injectivity_axiom_reducer_is_sat() {
    expect_sat(
        r#"
(set-logic AUFLIA)
(declare-sort List 0)
(declare-fun __seq_elem_List (List) Int)
(assert (forall ((x List) (y List))
    (! (or (= x y) (not (= (__seq_elem_List x) (__seq_elem_List y))))
       :pattern ((__seq_elem_List x) (__seq_elem_List y)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq elem injectivity axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_elem_list_injectivity_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-sort List 0)
(declare-fun a () List)
(declare-fun b () List)
(declare-fun __seq_elem_List (List) Int)
(assert (not (= a b)))
(assert (= (__seq_elem_List a) (__seq_elem_List b)))
(assert (forall ((x List) (y List))
    (! (or (= x y) (not (= (__seq_elem_List x) (__seq_elem_List y))))
       :pattern ((__seq_elem_List x) (__seq_elem_List y)))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq elem injectivity contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_invariant_bounded_good_bucket_axiom_is_soundly_unknown_without_model_certificate() {
    // This is satisfiable (for example, seq_len_proxy = 0 makes every guard
    // vacuous), but AY has not constructed and rechecked a total interpretation.
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-fun self () MyHashMap)
(declare-fun buckets (MyHashMap) (Seq Int))
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun seq_offset ((Seq Int)) Int)
(declare-fun seq_len_proxy () Int)
(declare-fun method_good_bucket_3_u4d79486173684d6170_i_i (MyHashMap Int Int) Bool)
(declare-fun method_no_double_binding_1_i (Int) Bool)
(assert (forall ((i Int))
  (! (or (and (method_good_bucket_3_u4d79486173684d6170_i_i
                self
                (select (seq_array (buckets self))
                        (+ (seq_offset (buckets self)) i))
                i)
              (method_no_double_binding_1_i
                (select (seq_array (buckets self))
                        (+ (seq_offset (buckets self)) i))))
         (not (<= 0 i))
         (not (< i seq_len_proxy)))
     :pattern ((select (seq_array (buckets self))
                       (+ (seq_offset (buckets self)) i))))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap invariant bounded good_bucket axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_bucket_ix_symbolic_mod_definition_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-fun logic_K_P__P_hash__log__placeholder_i__ret_i (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun seq_len_proxy () Int)
(assert (forall ((self MyHashMap) (k Int))
    (! (= (logic_bucket__ix self k)
          (mod (logic_K_P__P_hash__log__placeholder_i__ret_i k)
               seq_len_proxy))
       :pattern ((logic_bucket__ix self k)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap bucket index symbolic modulo definition axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_bucket_ix_zero_divisor_seq_definition_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic ALL)
(declare-sort MyHashMap 0)
(declare-fun seq_holder () (Seq Int))
(declare-fun seq_marker ((Seq Int)) Bool)
(declare-fun logic_K_P__P_hash__log__placeholder_i__ret_i (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun seq_len_proxy () Int)
(assert (seq_marker seq_holder))
(assert (= 0 seq_len_proxy))
(assert (forall ((self MyHashMap) (k Int))
    (! (= (logic_bucket__ix self k)
          (mod (logic_K_P__P_hash__log__placeholder_i__ret_i k)
               seq_len_proxy))
       :pattern ((logic_bucket__ix self k)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap bucket index zero-divisor Seq definition axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_bucket_ix_definition_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-fun self () MyHashMap)
(declare-fun logic_K_P__P_hash__log__placeholder_i__ret_i (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun seq_len_proxy () Int)
(assert (= seq_len_proxy 2))
(assert (= (logic_K_P__P_hash__log__placeholder_i__ret_i 0) 5))
(assert (not (= (logic_bucket__ix self 0) 1)))
(assert (forall ((m MyHashMap) (k Int))
    (! (= (logic_bucket__ix m k)
          (mod (logic_K_P__P_hash__log__placeholder_i__ret_i k)
               seq_len_proxy))
       :pattern ((logic_bucket__ix m k)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap bucket index definition contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_concat_len_definition_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun seq_concat ((Seq Int) (Seq Int)) (Seq Int))
(declare-fun seq_len ((Seq Int)) Int)
(assert (forall ((lhs (Seq Int)) (rhs (Seq Int)))
    (! (= (seq_len (seq_concat lhs rhs))
          (+ (seq_len lhs) (seq_len rhs)))
       :pattern ((seq_len (seq_concat lhs rhs))))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq concat length definition axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_concat_len_definition_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun a () (Seq Int))
(declare-fun b () (Seq Int))
(declare-fun seq_concat ((Seq Int) (Seq Int)) (Seq Int))
(declare-fun seq_len ((Seq Int)) Int)
(assert (= (seq_len (seq_concat a b)) 0))
(assert (= (seq_len a) 1))
(assert (= (seq_len b) 1))
(assert (forall ((lhs (Seq Int)) (rhs (Seq Int)))
    (! (= (seq_len (seq_concat lhs rhs))
          (+ (seq_len lhs) (seq_len rhs)))
       :pattern ((seq_len (seq_concat lhs rhs))))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq concat length definition contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_concat_len_and_bucket_ix_definitions_are_soundly_unknown_without_joint_model() {
    // Each axiom family is satisfiable, but the mixed bundle has no jointly
    // materialized and rechecked model. Per-axiom syntax is not SAT authority.
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-fun seq_concat ((Seq Int) (Seq Int)) (Seq Int))
(declare-fun seq_len ((Seq Int)) Int)
(declare-fun logic_K_P__P_hash__log__placeholder_i__ret_i (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun seq_len_proxy () Int)
(assert (forall ((lhs (Seq Int)) (rhs (Seq Int)))
    (! (= (seq_len (seq_concat lhs rhs))
          (+ (seq_len lhs) (seq_len rhs)))
       :pattern ((seq_len (seq_concat lhs rhs))))))
(assert (forall ((self MyHashMap) (k Int))
    (! (= (logic_bucket__ix self k)
          (mod (logic_K_P__P_hash__log__placeholder_i__ret_i k)
               seq_len_proxy))
       :pattern ((logic_bucket__ix self k)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq concat plus bucket index definitions",
    );
}

#[test]
#[timeout(30_000)]
fn seq_contains_push_back_definition_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun seq_push_back ((Seq Int) Int) (Seq Int))
(declare-fun seq_contains ((Seq Int) Int) Bool)
(assert (forall ((s (Seq Int)) (pushed Int) (x Int))
    (! (= (seq_contains (seq_push_back s pushed) x)
          (or (= pushed x) (seq_contains s x)))
       :pattern ((seq_contains (seq_push_back s pushed) x)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq push_back contains definition axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_contains_push_back_definition_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun s () (Seq Int))
(declare-fun seq_push_back ((Seq Int) Int) (Seq Int))
(declare-fun seq_contains ((Seq Int) Int) Bool)
(assert (not (seq_contains (seq_push_back s 5) 5)))
(assert (forall ((seq (Seq Int)) (pushed Int) (x Int))
    (! (= (seq_contains (seq_push_back seq pushed) x)
          (or (= pushed x) (seq_contains seq x)))
       :pattern ((seq_contains (seq_push_back seq pushed) x)))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq push_back contains definition contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_empty_contains_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun seq_empty () (Seq Int))
(declare-fun seq_contains ((Seq Int) Int) Bool)
(assert (forall ((v Int))
    (! (not (seq_contains seq_empty v))
       :pattern ((seq_contains seq_empty v)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq_empty contains axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_empty_contains_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun seq_empty () (Seq Int))
(declare-fun seq_contains ((Seq Int) Int) Bool)
(assert (seq_contains seq_empty 7))
(assert (forall ((v Int))
    (! (not (seq_contains seq_empty v))
       :pattern ((seq_contains seq_empty v)))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq_empty contains contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn unrelated_quantifier_consumer_trigger_never_certifies_seq_empty_contains_sat() {
    expect_not_sat(
        r#"
(set-logic ALL)
(declare-fun seq_contains ((Seq Int) Int) Bool)
(declare-const seq_empty (Seq Int))
(declare-const other (Seq Int))
(assert (distinct seq_empty other))
(assert (forall ((x Int))
    (! (not (seq_contains seq_empty x))
       :pattern ((seq_contains other x)))))
(assert (not (seq_contains other 0)))
(assert (seq_contains seq_empty 1))
(check-sat)
"#,
        "unrelated seq_contains trigger must not certify a contradictory universal",
    );
}

#[test]
#[timeout(30_000)]
fn seq_len_nonnegative_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun seq_len ((Seq Int)) Int)
(assert (forall ((s (Seq Int)))
    (! (<= 0 (seq_len s))
       :pattern ((seq_len s)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq_len nonnegative axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_len_nonnegative_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun s () (Seq Int))
(declare-fun seq_len ((Seq Int)) Int)
(assert (= (seq_len s) (- 1)))
(assert (forall ((seq (Seq Int)))
    (! (<= 0 (seq_len seq))
       :pattern ((seq_len seq)))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq_len nonnegative contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_select_bridge_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun seq_offset ((Seq Int)) Int)
(declare-fun seq_index_logic ((Seq Int) Int) Int)
(assert (forall ((s (Seq Int)) (i Int))
    (! (= (select (seq_array s) (+ (seq_offset s) i))
          (seq_index_logic s i))
       :pattern ((seq_index_logic s i)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq select bridge axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_select_bridge_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun s () (Seq Int))
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun seq_offset ((Seq Int)) Int)
(declare-fun seq_index_logic ((Seq Int) Int) Int)
(assert (= (select (seq_array s) (+ (seq_offset s) 0)) 1))
(assert (= (seq_index_logic s 0) 2))
(assert (forall ((seq (Seq Int)) (i Int))
    (! (= (select (seq_array seq) (+ (seq_offset seq) i))
          (seq_index_logic seq i))
       :pattern ((seq_index_logic seq i)))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq select bridge contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_get_in_bounds_axiom_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-fun seq_get ((Seq Int) Int) Int)
(declare-fun seq_index_logic ((Seq Int) Int) Int)
(declare-fun seq_len ((Seq Int)) Int)
(declare-fun logic_Some (Int) Int)
(assert (forall ((s (Seq Int)) (i Int))
    (! (or (= (seq_get s i) (logic_Some (seq_index_logic s i)))
           (not (<= 0 i))
           (not (< i (seq_len s))))
       :pattern ((seq_get s i)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq_get in-bounds axiom reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_get_in_bounds_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-fun s () (Seq Int))
(declare-fun seq_get ((Seq Int) Int) Int)
(declare-fun seq_index_logic ((Seq Int) Int) Int)
(declare-fun seq_len ((Seq Int)) Int)
(declare-fun logic_Some (Int) Int)
(assert (= (seq_len s) 1))
(assert (not (= (seq_get s 0) (logic_Some (seq_index_logic s 0)))))
(assert (forall ((seq (Seq Int)) (i Int))
    (! (or (= (seq_get seq i) (logic_Some (seq_index_logic seq i)))
           (not (<= 0 i))
           (not (< i (seq_len seq))))
       :pattern ((seq_get seq i)))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq_get in-bounds contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_index_restore_ground_bridge_reducer_is_soundly_unknown() {
    // Built-in non-string sequences do not yet have a complete model witness.
    // Keep this satisfiable reducer behind the deliberate fail-closed gate:
    // UNKNOWN is sound, whereas bypassing validation to recover SAT is not.
    expect_unknown(
        r#"
(set-logic ALL)
(declare-datatype List ((nil) (cons (hd Int) (tl List))))
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun seq_offset ((Seq Int)) Int)
(declare-fun __seq_index_restore_List ((Seq Int) Int) List)
(declare-fun __seq_elem_List (List) Int)
(declare-fun s () (Seq Int))
(declare-fun dividend () Int)
(declare-fun divisor () Int)
(assert (= (select (seq_array s) (+ (seq_offset s) (mod dividend divisor)))
           (__seq_elem_List (__seq_index_restore_List s (mod dividend divisor)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list seq index restore ground bridge reducer",
    );
}

#[test]
#[timeout(30_000)]
fn seq_index_restore_ground_bridge_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic ALL)
(declare-datatype List ((nil) (cons (hd Int) (tl List))))
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun seq_offset ((Seq Int)) Int)
(declare-fun __seq_index_restore_List ((Seq Int) Int) List)
(declare-fun __seq_elem_List (List) Int)
(declare-fun s () (Seq Int))
(declare-fun dividend () Int)
(declare-fun divisor () Int)
(assert (= (select (seq_array s) (+ (seq_offset s) (mod dividend divisor))) 1))
(assert (= (__seq_elem_List (__seq_index_restore_List s (mod dividend divisor))) 2))
(assert (= (select (seq_array s) (+ (seq_offset s) (mod dividend divisor)))
           (__seq_elem_List (__seq_index_restore_List s (mod dividend divisor)))))
(check-sat)
"#,
        "ay#8971/verification-consumer seq index restore ground bridge contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn seq_index_restore_with_verification_consumer_quantifiers_and_symbolic_mod_fails_closed() {
    expect_unknown(
        r#"
(set-logic ALL)
(declare-datatype List ((nil) (cons (hd Int) (tl List))))
(declare-fun arg0 () (Seq Int))
(declare-fun arg0_view () (Seq Int))
(declare-fun seq_empty () (Seq Int))
(declare-fun dividend_view () Int)
(declare-fun dividend () Int)
(declare-fun divisor () Int)
(declare-fun seq_len_proxy_49 () Int)
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun seq_offset ((Seq Int)) Int)
(declare-fun seq_index_logic ((Seq Int) Int) Int)
(declare-fun seq_get ((Seq Int) Int) Int)
(declare-fun seq_len ((Seq Int)) Int)
(declare-fun logic_Some (Int) Int)
(declare-fun __seq_index_restore_List ((Seq Int) Int) List)
(declare-fun __seq_elem_List (List) Int)
(assert (= (seq_array seq_empty) ((as const (Array Int Int)) 0)))
(assert (forall ((s (Seq Int)) (i Int))
  (! (= (select (seq_array s) (+ (seq_offset s) i))
        (seq_index_logic s i))
     :pattern ((seq_index_logic s i)))))
(assert (forall ((s (Seq Int)) (i Int))
  (! (or (= (seq_get s i) (logic_Some (seq_index_logic s i)))
         (not (<= 0 i))
         (not (< i (seq_len s))))
     :pattern ((seq_get s i)))))
(assert (= arg0 arg0_view))
(assert (= dividend_view dividend))
(assert (<= 0 seq_len_proxy_49))
(assert (= (select (seq_array arg0_view)
                   (+ (seq_offset arg0_view) (mod dividend divisor)))
           (__seq_elem_List
             (__seq_index_restore_List arg0_view (mod dividend divisor)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap_list quantified seq restore symbolic modulo reducer",
    );
}

#[test]
#[timeout(30_000)]
fn verification_consumer_bucket_mod_ground_completion_with_seq_sort_proxy_is_soundly_unknown_9227()
{
    // Even an otherwise-unused `(Seq Int)` leaf enters the non-string sequence
    // witness lane.  Until that model is complete, the public result must stay
    // fail-closed UNKNOWN rather than expose an unvalidated SAT certificate.
    expect_unknown(
        r#"
(set-logic ALL)
(declare-sort MyHashMap 0)
(declare-fun old_self () MyHashMap)
(declare-fun seq_empty () (Seq Int))
(declare-fun sk_k () Int)
(declare-fun seq_len_proxy_34 () Int)
(declare-fun seq_array ((Seq Int)) (Array Int Int))
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_hash_log (Int) Int)
(assert (= (seq_array seq_empty) ((as const (Array Int Int)) 0)))
(assert (= (logic_bucket__ix old_self sk_k)
           (mod (logic_hash_log sk_k) seq_len_proxy_34)))
(check-sat)
"#,
        "ay#9227/verification-consumer resize ground AUFLIA mod completion reducer",
    );
}

#[test]
#[timeout(30_000)]
fn verification_consumer_bucket_mod_ground_completion_rejects_concrete_contradiction_9227() {
    expect_not_sat(
        r#"
(set-logic ALL)
(declare-sort MyHashMap 0)
(declare-fun old_self () MyHashMap)
(declare-fun sk_k () Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(assert (= (logic_bucket__ix old_self sk_k) 1))
(assert (= (logic_bucket__ix old_self sk_k) (mod 5 3)))
(check-sat)
"#,
        "ay#9227/verification-consumer mod completion must reject concrete contradictions",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_invariant_nested_definition_is_soundly_unknown_without_model_certificate() {
    // This is satisfiable (choose seq_len_proxy = 0 and the invariant false),
    // but the nested quantified RHS has no constructive total-model certificate.
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-fun self () MyHashMap)
(declare-fun good_arg () List)
(declare-fun seq_len_proxy () Int)
(declare-fun method___quantifier_consumer_invariant_creusot__test_P__P_MyHashMap_1_d4d79486173684d6170 (MyHashMap) Bool)
(declare-fun myhashmap_buckets (MyHashMap) (Seq Int))
(declare-fun method_index_logic_2_s_i ((Seq Int) Int) Int)
(declare-fun logic_good__bucket (MyHashMap List Int) Bool)
(declare-fun method_no_double_binding_1_i (Int) Bool)
(assert (= (method___quantifier_consumer_invariant_creusot__test_P__P_MyHashMap_1_d4d79486173684d6170 self)
           (and (< 0 seq_len_proxy)
                (forall ((i Int))
                  (! (or (and (logic_good__bucket self good_arg i)
                              (method_no_double_binding_1_i
                                (method_index_logic_2_s_i (myhashmap_buckets self) i)))
                         (not (<= 0 i))
                         (not (< i seq_len_proxy)))
                     :pattern ((logic_good__bucket self good_arg i))
                     :pattern ((method_no_double_binding_1_i
                                  (method_index_logic_2_s_i (myhashmap_buckets self) i)))
                     :pattern ((method_index_logic_2_s_i (myhashmap_buckets self) i)))))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap invariant nested definition reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_invariant_nested_definition_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-fun self () MyHashMap)
(declare-fun good_arg () List)
(declare-fun seq_len_proxy () Int)
(declare-fun method___quantifier_consumer_invariant_creusot__test_P__P_MyHashMap_1_d4d79486173684d6170 (MyHashMap) Bool)
(declare-fun myhashmap_buckets (MyHashMap) (Seq Int))
(declare-fun method_index_logic_2_s_i ((Seq Int) Int) Int)
(declare-fun logic_good__bucket (MyHashMap List Int) Bool)
(declare-fun method_no_double_binding_1_i (Int) Bool)
(assert (= seq_len_proxy 1))
(assert (method___quantifier_consumer_invariant_creusot__test_P__P_MyHashMap_1_d4d79486173684d6170 self))
(assert (not (logic_good__bucket self good_arg 0)))
(assert (= (method___quantifier_consumer_invariant_creusot__test_P__P_MyHashMap_1_d4d79486173684d6170 self)
           (and (< 0 seq_len_proxy)
                (forall ((i Int))
                  (! (or (and (logic_good__bucket self good_arg i)
                              (method_no_double_binding_1_i
                                (method_index_logic_2_s_i (myhashmap_buckets self) i)))
                         (not (<= 0 i))
                         (not (< i seq_len_proxy)))
                     :pattern ((logic_good__bucket self good_arg i))
                     :pattern ((method_no_double_binding_1_i
                                  (method_index_logic_2_s_i (myhashmap_buckets self) i)))
                     :pattern ((method_index_logic_2_s_i (myhashmap_buckets self) i)))))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap invariant nested definition contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn ematching_exists_does_not_mask_ground_unsat() {
    expect_unsat(
        r#"
(set-logic AUFLIA)
(declare-fun flag () Bool)
(declare-fun P (Int) Bool)
(assert (= 0 1))
(assert (= flag
           (not (forall ((x Int))
                  (! (P x) :pattern ((P x)))))))
(assert (P 0))
(check-sat)
"#,
        "ay#8971/verification-consumer ground UNSAT should survive incomplete existential E-matching",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_bucket_guarded_frame_clause_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-sort OptionInt 0)
(declare-fun old_self () MyHashMap)
(declare-fun old_list () List)
(declare-fun new_list () List)
(declare-fun i () Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_get (List Int) OptionInt)
(assert (forall ((k Int))
    (! (or (= (logic_get new_list k) (logic_get old_list k))
           (not (< (logic_bucket__ix old_self k) i)))
       :pattern ((logic_get new_list k))
       :pattern ((logic_get old_list k))
       :pattern ((logic_bucket__ix old_self k)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap bucket-guarded frame clause reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_bucket_guarded_frame_clause_direct_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-sort OptionInt 0)
(declare-fun old_self () MyHashMap)
(declare-fun old_list () List)
(declare-fun new_list () List)
(declare-fun a () OptionInt)
(declare-fun b () OptionInt)
(declare-fun i () Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_get (List Int) OptionInt)
(assert (= i 1))
(assert (= (logic_bucket__ix old_self 0) 0))
(assert (= (logic_get new_list 0) a))
(assert (= (logic_get old_list 0) b))
(assert (not (= a b)))
(assert (forall ((k Int))
    (! (or (= (logic_get new_list k) (logic_get old_list k))
           (not (< (logic_bucket__ix old_self k) i)))
       :pattern ((logic_get new_list k))
       :pattern ((logic_get old_list k))
       :pattern ((logic_bucket__ix old_self k)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap bucket-guarded frame clause contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_bucket_range_guarded_frame_clause_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-sort OptionInt 0)
(declare-fun old_self () MyHashMap)
(declare-fun new_list () List)
(declare-fun nil () List)
(declare-fun i () Int)
(declare-fun len () Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_get (List Int) OptionInt)
(assert (forall ((k Int))
    (! (or (= nil new_list)
           (= (logic_get new_list k) (logic_get nil k))
           (not (<= i (logic_bucket__ix old_self k)))
           (not (<= (logic_bucket__ix old_self k) len)))
       :pattern ((logic_get new_list k))
       :pattern ((logic_bucket__ix old_self k)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap bucket-range guarded frame clause reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_resize_shifted_bucket_guard_contradiction_is_unsat() {
    expect_unsat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort OptionInt 0)
(declare-fun old_self () MyHashMap)
(declare-fun new_map () MyHashMap)
(declare-fun sk_k () Int)
(declare-fun i () Int)
(declare-fun i_prime () Int)
(declare-fun len () Int)
(declare-fun None () OptionInt)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_get (MyHashMap Int) OptionInt)
(declare-fun hash_log (Int) Int)
(assert (forall ((k Int))
    (! (or (= (logic_get new_map k) None)
           (not (<= i (logic_bucket__ix old_self k)))
           (not (<= (logic_bucket__ix old_self k) len)))
       :pattern ((logic_get new_map k))
       :pattern ((logic_bucket__ix old_self k)))))
(assert (= i_prime (+ i 1)))
(assert (<= i_prime (logic_bucket__ix old_self sk_k)))
(assert (<= (logic_bucket__ix old_self sk_k) len))
(assert (not (= (logic_get new_map sk_k) None)))
(assert (= (logic_bucket__ix old_self sk_k) (mod (hash_log sk_k) len)))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap resize shifted bucket guard contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_resize_shifted_bucket_with_placeholder_good_bucket_is_unsat() {
    expect_unsat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-sort OptionInt 0)
(declare-fun old_self () MyHashMap)
(declare-fun new_map () MyHashMap)
(declare-fun l () List)
(declare-fun sk_k () Int)
(declare-fun i () Int)
(declare-fun i_prime () Int)
(declare-fun len () Int)
(declare-fun None () OptionInt)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_get (MyHashMap Int) OptionInt)
(declare-fun hash_log (Int) Int)
(declare-fun logic_good__bucket__placeholder_u4d79486173684d6170_i_i__ret_b (MyHashMap List Int) Bool)
(assert (logic_good__bucket__placeholder_u4d79486173684d6170_i_i__ret_b old_self l i))
(assert (forall ((k Int))
    (! (or (= (logic_get new_map k) None)
           (not (<= i (logic_bucket__ix old_self k)))
           (not (<= (logic_bucket__ix old_self k) len)))
       :pattern ((logic_get new_map k))
       :pattern ((logic_bucket__ix old_self k)))))
(assert (= i_prime (+ i 1)))
(assert (<= i_prime (logic_bucket__ix old_self sk_k)))
(assert (<= (logic_bucket__ix old_self sk_k) len))
(assert (not (= (logic_get new_map sk_k) None)))
(assert (= (logic_bucket__ix old_self sk_k) (mod (hash_log sk_k) len)))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap resize placeholder good_bucket completion reducer",
    );
}

#[test]
#[timeout(30_000)]
fn unsupported_symbolic_mod_cannot_mask_mod_free_resize_contradiction() {
    expect_unsat(
        r#"
(set-logic AUFLIA)
(declare-sort A 0)
(declare-fun i () Int)
(declare-fun i_prime () Int)
(declare-fun len () Int)
(declare-fun old_len () Int)
(declare-fun hash_value () Int)
(declare-fun a () A)
(declare-fun b () A)
(declare-fun c () A)
(declare-fun flag () Bool)
(assert (<= 0 i))
(assert (< i len))
(assert (= i_prime (+ i 1)))
(assert (= len old_len))
(assert (or (= 0 old_len) (not (<= i_prime len))))
(assert (or (ite flag (= a b) (= a c))
            (not (= i (mod hash_value old_len)))))
(check-sat)
"#,
        "ay#9227/verification-consumer resize unsupported mod must not mask mod-free UNSAT",
    );
}

#[test]
#[timeout(30_000)]
fn positive_symbolic_mod_bounds_discharge_resize_frame_split() {
    expect_unsat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort OptionInt 0)
(declare-fun old_self () MyHashMap)
(declare-fun old_view () MyHashMap)
(declare-fun new_map () MyHashMap)
(declare-fun new_view () MyHashMap)
(declare-fun sk_k () Int)
(declare-fun i () Int)
(declare-fun i_prime () Int)
(declare-fun len () Int)
(declare-fun hash_log (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_get (MyHashMap Int) OptionInt)
(assert (< 0 len))
(assert (= new_map new_view))
(assert (= i_prime (+ i 1)))
(assert (= (logic_bucket__ix old_self sk_k) (mod (hash_log sk_k) len)))
(assert (or (= (logic_get old_view sk_k) (logic_get new_map sk_k))
            (not (< (logic_bucket__ix old_self sk_k) i))))
(assert (or (= (logic_get old_view sk_k) (logic_get new_view sk_k))
            (not (= i (mod (hash_log sk_k) len)))))
(assert (or (= 0 len)
            (and (< (logic_bucket__ix old_self sk_k) i_prime)
                 (not (= (logic_get old_view sk_k) (logic_get new_map sk_k))))))
(check-sat)
"#,
        "ay#9227/verification-consumer resize symbolic mod range must prove split-frame UNSAT",
    );
}

#[test]
#[timeout(30_000)]
fn positive_symbolic_mod_bounds_discharge_resize_frame_split_with_list_carriers() {
    expect_unsat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-sort OptionInt 0)
(declare-fun old_self () MyHashMap)
(declare-fun old_self_view () List)
(declare-fun new () List)
(declare-fun new_view () List)
(declare-fun sk_k () Int)
(declare-fun i () Int)
(declare-fun i_view () Int)
(declare-fun i_prime () Int)
(declare-fun len () Int)
(declare-fun None () OptionInt)
(declare-fun hash_log (Int) Int)
(declare-fun logic_bucket__ix (MyHashMap Int) Int)
(declare-fun logic_get (List Int) OptionInt)
(assert (= new new_view))
(assert (= i i_view))
(assert (= i_prime (+ i 1)))
(assert (< 0 len))
(assert (= (logic_bucket__ix old_self sk_k) (mod (hash_log sk_k) len)))
(assert (or (= (logic_get old_self_view sk_k) (logic_get new sk_k))
            (not (< (logic_bucket__ix old_self sk_k) i))))
(assert (or (= (logic_get old_self_view sk_k) (logic_get new_view sk_k))
            (not (= i_view (mod (hash_log sk_k) len)))))
(assert (or (= None (logic_get new sk_k))
            (not (<= i (logic_bucket__ix old_self sk_k)))
            (not (<= (logic_bucket__ix old_self sk_k) len))))
(assert (or (= 0 len)
            (and (< (logic_bucket__ix old_self sk_k) i_prime)
                 (not (= (logic_get old_self_view sk_k) (logic_get new sk_k))))))
(check-sat)
"#,
        "ay#9227/verification-consumer resize symbolic mod range with List carriers",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_logic_no_double_binding_invariant_fails_closed_without_total_model() {
    expect_unknown(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-fun self () MyHashMap)
(declare-fun bucket () List)
(declare-fun seq_len_proxy () Int)
(declare-fun logic_good__bucket (MyHashMap List Int) Bool)
(declare-fun logic_no__double__binding (List) Bool)
(assert (forall ((i Int))
    (! (or (and (logic_good__bucket self bucket i)
                (logic_no__double__binding bucket))
           (not (<= 0 i))
           (not (< i seq_len_proxy)))
       :pattern ((logic_good__bucket self bucket i))
       :pattern ((logic_no__double__binding bucket)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap logic_no__double__binding invariant reducer",
    );
}

#[test]
#[timeout(30_000)]
fn hashmap_logic_no_double_binding_invariant_contradiction_is_not_sat() {
    expect_not_sat(
        r#"
(set-logic AUFLIA)
(declare-sort MyHashMap 0)
(declare-sort List 0)
(declare-fun self () MyHashMap)
(declare-fun bucket () List)
(declare-fun seq_len_proxy () Int)
(declare-fun logic_good__bucket (MyHashMap List Int) Bool)
(declare-fun logic_no__double__binding (List) Bool)
(assert (= seq_len_proxy 1))
(assert (not (logic_good__bucket self bucket 0)))
(assert (forall ((i Int))
    (! (or (and (logic_good__bucket self bucket i)
                (logic_no__double__binding bucket))
           (not (<= 0 i))
           (not (< i seq_len_proxy)))
       :pattern ((logic_good__bucket self bucket i))
       :pattern ((logic_no__double__binding bucket)))))
(check-sat)
"#,
        "ay#8971/verification-consumer hashmap logic_no__double__binding invariant contradiction",
    );
}

#[test]
#[timeout(30_000)]
fn verification_consumer_datatype_tester_branch_reducer_is_sat() {
    expect_sat(
        r#"
(set-logic AUFLIA)
(declare-sort List 0)
(declare-fun l_current () List)
(declare-fun __uf_int_aux_1 () Int)
(declare-fun is-Nil (List) Bool)
(assert (or (= 0 __uf_int_aux_1)
            (not (is-Nil l_current))))
(check-sat)
"#,
        "ay#8971/verification-consumer is-* datatype tester branch reducer",
    );
}

#[test]
#[timeout(30_000)]
fn arbitrary_seq_quantifier_is_sat_by_constant_interpretation() {
    // HISTORY: this was `arbitrary_seq_quantifier_still_fails_closed`, pinning
    // `unknown` for an opaque `(p s)` body. The pin recorded a LIMITATION, not
    // a soundness boundary — and the comment it carried already set the
    // precedent that a sound improvement here "is a sound improvement, not a
    // guard bypass".
    //
    // The CONSTANT-INTERPRETATION certificate now decides it. The answer is
    // `sat`, and the certificate's own witness is `p := λs. true`:
    // substituting that interpretation turns the body into `true`, so the
    // negated body is refuted outright.
    //
    // Cross-checked against z3 4.15.4 (the `(Seq Int)` sort needs `ALL`;
    // `QF_AUFLIA` makes z3 reject the sort and answer `sat` for an empty
    // problem, so the check below was run under `(set-logic ALL)`):
    //     $ z3 canary.smt2
    //     sat
    //     ( (define-fun p ((x!0 (Seq Int))) Bool true) )
    // z3 reports exactly the interpretation AY's certificate constructs.
    expect_sat(
        r#"
(set-logic QF_AUFLIA)
(declare-fun p ((Seq Int)) Bool)
(assert (forall ((s (Seq Int))) (! (p s) :pattern ((p s)))))
(check-sat)
"#,
        "non-verification-consumer opaque Seq quantifier",
    );
}
