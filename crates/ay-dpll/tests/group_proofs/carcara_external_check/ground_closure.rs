// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground refutations rebuilt over the RAW authored roots by congruence
//! closure with read-over-write, closed bit-vector evaluation, and instances
//! of authored universals (`executor/proof/authored_ground_closure.rs`).
//!
//! Each fixture is the smallest shape of a MODEL_CHECKER_CONSUMER corpus row that shipped a
//! whole-problem `hole` (or no proof at all) because elaboration folded the
//! authored index spelling or the missed write away:
//! `model_checker_consumer_store_miss_residual_inner_miss_conflict_unsat`,
//! `model_checker_consumer_store_miss_residual_newest_store_hit_unsat` and
//! `model_checker_consumer_quantified_counterexample_wide_key136_premise_false_unsat`, or
//! because a record constant's field reads have no raw re-intern
//! (`model_checker_consumer_quantified_counterexample_branching_vec_query_false_unsat`).
//! Measured without the lane on 938ec0327: `unknown` for every fixture and
//! every row. Each document must now be Carcara `valid` with no allowance.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, run_carcara_trust_free,
    solve_or_fail_closed_and_maybe_get_proof, solve_unsat_and_get_proof, CarcaraVerdict,
};
use ntest::timeout;

/// A write the read misses, under an array alias through two datatype fields.
const INNER_MISS: &str = r#"
(set-logic ALL)
(declare-datatype Vec ((mk_vec (vec_len (_ BitVec 8)) (vec_data (Array (_ BitVec 8) (_ BitVec 8))))))
(declare-datatype Term ((mk_term (term_lits Vec))))
(declare-const a (Array (_ BitVec 8) Term))
(declare-const b (Array (_ BitVec 8) Term))
(assert (= a b))
(assert (= (select (store (vec_data (term_lits (select a #x09))) #x40 #x07) #x41) #x08))
(assert (= (select (vec_data (term_lits (select b #x09))) #x41) #x09))
(check-sat)
"#;

/// The newest write hits the read through a closed index spelling.
const NEWEST_HIT: &str = r#"
(set-logic ALL)
(declare-datatype Cell ((mk_cell (cell_data (Array (_ BitVec 8) (_ BitVec 8))))))
(declare-const a (Array (_ BitVec 8) Cell))
(assert (= (select (store (store (cell_data (select a #x09)) #x40 #x01) (bvadd #x3f #x01) #x02) #x40) #x01))
(check-sat)
"#;

/// A universal fill pin contradicted at the written index.
const GUARD_INSTANCE: &str = r#"
(set-logic ALL)
(declare-const data (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= data (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) #x40 #x08)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i #x41) (= (select data i) #x07))))
(check-sat)
"#;

/// A universal whose instance guard is a closed `bvsub` equality. Pinned
/// Carcara's `evaluate` computes `bvsub` wrongly (`(bvsub #xff #x01)` reads as
/// `#x00`), so the guard must be proved by checked `bitblast_*` steps, never
/// by `evaluate`; the committed state exported it as a `hole` until the
/// complete bit-blast series between e12eadbc7 and 938ec0327.
const CLOSED_SUB_GUARD: &str = r#"
(set-logic ALL)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(assert (forall ((i (_ BitVec 8))) (=> (= (bvsub i #x01) #xfe) (= (g i) #x01))))
(assert (= (g #xff) #x00))
(check-sat)
"#;

/// Two record constants aliased to two pinned vectors, queried through field
/// reads in an authored conjunction spelled with `(_ bvN W)` literals.
const RECORD_ALIAS: &str = r#"
(set-logic ALL)
(declare-datatype Vec ((mk_vec (vec_len (_ BitVec 8)) (vec_data (Array (_ BitVec 8) (_ BitVec 8))))))
(declare-const v0 Vec)
(declare-const f0 (_ BitVec 8))
(declare-const v1 Vec)
(declare-const f1 (_ BitVec 8))
(declare-const a Vec)
(declare-const b Vec)
(assert (= v0 (mk_vec #x41 ((as const (Array (_ BitVec 8) (_ BitVec 8))) f0))))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (vec_len v0)) (= (select (vec_data v0) i) f0))))
(assert (= v1 (mk_vec #x41 ((as const (Array (_ BitVec 8) (_ BitVec 8))) f1))))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i (vec_len v1)) (= (select (vec_data v1) i) f1))))
(assert (= a v0))
(assert (= #x07 f0))
(assert (= b v1))
(assert (= #x09 f1))
(assert (and (bvult (_ bv64 8) (vec_len a)) (bvult (_ bv64 8) (vec_len b))
  (= (select (vec_data a) (_ bv64 8)) (select (vec_data b) (_ bv64 8)))))
(check-sat)
"#;

pub(super) fn trust_free_document(problem: &str, label: &str, rules: &[&str]) -> String {
    let proof = solve_unsat_and_get_proof(problem, label);
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "{label}: the document must be hole- and trust-free:\n{proof}"
    );
    for rule in rules {
        assert!(
            proof.contains(&format!(":rule {rule}")),
            "{label}: expected a `{rule}` step:\n{proof}"
        );
    }
    // Pinned Carcara misevaluates `bvsub`, the signed family and `extract`
    // (`checker/ground_evaluate/unsigned_order.rs`), so no `evaluate` step
    // may read one, even where Carcara is not installed.
    let misevaluated = [
        "(bvsub ",
        "(bvsdiv ",
        "(bvsrem ",
        "(bvsmod ",
        "(bvashr ",
        "(bvslt ",
        "(bvsle ",
        "(bvsgt ",
        "(bvsge ",
        "(_ extract ",
    ];
    assert!(
        !proof.lines().any(|line| line.contains(":rule evaluate")
            && misevaluated.iter().any(|operator| line.contains(operator))),
        "{label}: an `evaluate` step reads an operator Carcara misevaluates:\n{proof}"
    );
    // The raw roots print their bit-vector literals in binary (`#b00001001`
    // for the authored `#x09`); Carcara parses both as one constant and
    // matches every `assume` against the problem itself, so the premise check
    // is Carcara's, below.
    proof
}

#[test]
#[timeout(120_000)]
fn raw_ground_closure_refutations_are_carcara_valid() {
    let cases = [
        (
            INNER_MISS,
            "ground_closure_inner_miss",
            &["arrays_row", "eq_congruent", "eq_transitive"][..],
        ),
        (
            NEWEST_HIT,
            "ground_closure_newest_hit",
            &["arrays_idx", "eq_transitive"][..],
        ),
        (
            GUARD_INSTANCE,
            "ground_closure_guard_instance",
            &["forall_inst", "arrays_idx"][..],
        ),
        (
            CLOSED_SUB_GUARD,
            "ground_closure_closed_sub_guard",
            &["forall_inst", "bitblast_add", "bitblast_neg"][..],
        ),
        (
            RECORD_ALIAS,
            "ground_closure_record_alias",
            &[
                "forall_inst",
                "cong",
                "and_neg",
                "and_pos",
                "eq_congruent_pred",
            ][..],
        ),
    ];
    let documents: Vec<(&str, &str, String)> = cases
        .iter()
        .map(|&(problem, label, rules)| {
            (problem, label, trust_free_document(problem, label, rules))
        })
        .collect();
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    for (problem, label, proof) in &documents {
        assert!(
            run_carcara_trust_free(&carcara, label, problem, proof),
            "{label}: carcara must answer a literal `valid`"
        );
    }
}

/// NEGATIVE TWIN at the checker boundary: the instance and the missed read
/// are re-derived by Carcara, not allowed. The universal instantiated at a
/// value its conclusion does not state, or a miss read off the OTHER array,
/// is refused.
#[test]
#[timeout(120_000)]
fn tampered_instance_or_missed_read_is_refused_by_carcara() {
    let guard = trust_free_document(
        GUARD_INSTANCE,
        "ground_closure_tamper_guard",
        &["forall_inst"],
    );
    let miss = trust_free_document(INNER_MISS, "ground_closure_tamper_miss", &["arrays_row"]);
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let instance = ":rule forall_inst :args (#b01000000)";
    assert_eq!(guard.matches(instance).count(), 1, "{guard}");
    let forged_guard = guard.replacen(instance, ":rule forall_inst :args (#b01000001)", 1);
    let read =
        "(select (vec_data (term_lits (select a #b00001001))) #b01000001))) :rule arrays_row";
    assert_eq!(miss.matches(read).count(), 1, "{miss}");
    let forged_miss = miss.replacen(
        read,
        "(select (vec_data (term_lits (select b #b00001001))) #b01000001))) :rule arrays_row",
        1,
    );
    for (label, problem, forged) in [
        ("ground_closure_tamper_guard", GUARD_INSTANCE, forged_guard),
        ("ground_closure_tamper_miss", INNER_MISS, forged_miss),
    ] {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &forged),
            CarcaraVerdict::Invalid,
            "{label}"
        );
    }
}

/// NEGATIVE TWIN of the literal-spelling projection the record row rides on
/// (the parsed-equal `and_pos` conjunct, b4933f3b3): the authored conjunction
/// keeps `(_ bv64 8)` and the projected conjunct prints `#b01000000`, which
/// Carcara reads as one constant. The same projection naming ANOTHER value is
/// refused, so the projection grants nothing Carcara does not re-derive.
#[test]
#[timeout(120_000)]
fn a_projection_forged_to_another_literal_is_refused_by_carcara() {
    let proof = trust_free_document(RECORD_ALIAS, "ground_closure_tamper_literal", &["and_pos"]);
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let projection = "(bvult #b01000000 (vec_len a))) :rule and_pos :args (0))";
    assert_eq!(proof.matches(projection).count(), 1, "{proof}");
    let forged = proof.replacen(
        projection,
        "(bvult #b01000001 (vec_len a))) :rule and_pos :args (0))",
        1,
    );
    assert_eq!(
        carcara_verdict_without_allowances(
            &carcara,
            "ground_closure_tamper_literal",
            RECORD_ALIAS,
            &forged
        ),
        CarcaraVerdict::Invalid
    );
}

/// The guard `(bvsge i #x30)` elaborates to `(bvsle #x30 i)`, so the instance
/// the lane clausifies is not the one the authored universal publishes.
const NORMALIZED_GUARD: &str = r#"
(set-logic ALL)
(declare-const data (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= data (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) #x30 #x08)))
(assert (forall ((i (_ BitVec 8))) (=> (bvsge i #x30) (= (select data i) #x07))))
(check-sat)
"#;

/// NEGATIVE TWIN of the publication screen: each problem is unsat and the
/// lane refutes it strictly, but the post-cascade presentation passes re-spell
/// what it assumes -- the universal's instance from its authored `bvsge` body,
/// the record query from its authored nested `and` or `(not (distinct ..))`
/// conjunct, which the elaborated twin flattened -- and the committed
/// derivation no longer prints under them. The lane must judge the published
/// bytes: each answer is the fail-closed `unknown` it was without the lane, or
/// a Carcara `valid` document, never a `hole` or a refused export. Measured
/// with the screen exporting the committed state only (dt-array-rows review,
/// 09b0371c6): a `holey` `unsat` for the guard and `unsat` with the export
/// refused (`and_pos indexed conjunct is absent from its effective source`)
/// for both record queries.
#[test]
#[timeout(120_000)]
fn presentation_respelled_candidates_never_publish_a_gap() {
    let nested_and = RECORD_ALIAS.replace(
        "(assert (and (bvult (_ bv64 8) (vec_len a)) (bvult (_ bv64 8) (vec_len b))\n  \
         (= (select (vec_data a) (_ bv64 8)) (select (vec_data b) (_ bv64 8)))))",
        "(assert (and (bvult #x40 (vec_len a)) (and (bvult (_ bv64 8) (vec_len b)) \
         (= (select (vec_data a) #x40) (select (vec_data b) #x40)))))",
    );
    let not_distinct = RECORD_ALIAS.replace(
        "(= (select (vec_data a) (_ bv64 8)) (select (vec_data b) (_ bv64 8)))",
        "(not (distinct (select (vec_data a) (_ bv64 8)) (select (vec_data b) (_ bv64 8))))",
    );
    assert_ne!(nested_and, RECORD_ALIAS);
    assert_ne!(not_distinct, RECORD_ALIAS);
    let cases = [
        ("ground_closure_normalized_guard", NORMALIZED_GUARD),
        ("ground_closure_nested_and_query", nested_and.as_str()),
        ("ground_closure_not_distinct_query", not_distinct.as_str()),
    ];
    let carcara = require_carcara_or_skip();
    for (label, problem) in cases {
        let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(problem, label) else {
            continue;
        };
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}: a published document must be hole- and trust-free:\n{proof}"
        );
        if let Some(carcara) = carcara.as_ref() {
            assert!(
                run_carcara_trust_free(carcara, label, problem, &proof),
                "{label}: carcara must answer a literal `valid`"
            );
        }
    }
}

/// [`NEWEST_HIT`] at `width` bits, the hitting write's index spelled `index`
/// (a closed term equal to 64).
fn newest_hit_through(index: &str, width: u32) -> String {
    let sort = format!("(_ BitVec {width})");
    let lit = |value: u32| format!("(_ bv{value} {width})");
    format!(
        "(set-logic ALL)\n\
         (declare-datatype Cell ((mk_cell (cell_data (Array {sort} {sort})))))\n\
         (declare-const a (Array {sort} Cell))\n\
         (assert (= (select (store (store (cell_data (select a {nine})) {t} {one}) \
         {index} {two}) {t}) {one}))\n(check-sat)\n",
        nine = lit(9),
        t = lit(64),
        one = lit(1),
        two = lit(2),
    )
}

/// NEGATIVE TWIN of the evaluation path at the checker boundary: each problem
/// is unsat by the newest-write hit, through a closed index the printer can
/// only spell in a form pinned Carcara refuses -- a `bitblast_udiv` or
/// `bitblast_urem` step (clean `5390f432b8`'s fixed divider, e9b297e37), or
/// `refl` between a `zero_extend` and its `concat`. None of those is a `hole`,
/// so the wire screen passes them; the lane must not propose the evaluation.
/// Each answer is the fail-closed `unknown` or a Carcara `valid` document.
/// Measured on 938ec0327 with `bvudiv`, `bvurem` and `zero_extend` in the
/// lane's `EVALUATED_OPERATORS`: every one published `unsat` with a
/// Carcara-`invalid` document ("expected terms to be equal" at the divider,
/// "reflexivity failed" at the extension).
#[test]
#[timeout(120_000)]
fn closed_evaluations_carcara_refuses_are_never_published() {
    let carcara = require_carcara_or_skip();
    for (index, width) in [
        ("(bvudiv (_ bv128 8) (_ bv2 8))", 8),
        ("(bvurem (_ bv64 8) (_ bv0 8))", 8),
        ("(bvurem (_ bv192 64) (_ bv128 64))", 64),
        ("((_ zero_extend 1) (_ bv64 15))", 16),
        ("((_ zero_extend 32) (_ bv64 32))", 64),
    ] {
        let problem = newest_hit_through(index, width);
        let label = format!("ground_closure_refused_evaluation_{width}");
        let Some(proof) = solve_or_fail_closed_and_maybe_get_proof(&problem, &label) else {
            continue;
        };
        for rule in ["bitblast_udiv", "bitblast_urem"] {
            assert!(
                !proof.contains(&format!(":rule {rule}")),
                "{index}: a `{rule}` step pinned Carcara refuses:\n{proof}"
            );
        }
        assert!(
            !proof
                .lines()
                .any(|line| line.contains(":rule refl") && line.contains("zero_extend")),
            "{index}: a `zero_extend` reflexivity pinned Carcara refuses:\n{proof}"
        );
        if let Some(carcara) = carcara.as_ref() {
            assert!(
                run_carcara_trust_free(carcara, &label, &problem, &proof),
                "{index}: carcara must answer a literal `valid`"
            );
        }
    }
}

// The propagation replay's constant-array read leg
// (`executor/proof_propagated_rewrite/equality/array_folds.rs`) closes a read
// of an array preprocessing replaced by a constant array with the
// `ArrayRowChain` (E) lemma. Pinned Carcara has no rule for that lemma, so it
// prints as `hole`: the leg may fill a gap, never displace a refutation
// Carcara checks.
//
// Each fixture pairs the fold the leg exists for (`(select z #x9)` of
// `z = K` folded to `(g x)`, refuting the read assertion) with a second
// reason the problem is unsat, which a leg-free lane certifies Carcara
// `valid` (a628c3b2a, unproved_steps=0). Measured with the leg asked first,
// every fixture published a `holey` document instead (unproved_steps=1, the
// (E) step): for the bit-vector pair, both folds reach `false` and the
// replay's conjunct scan met the folded read first; for the guard pair, the
// leg made the incumbent native-strict, and the wire-gap retries never tried
// the raw-root ground closure that instantiates the guard universal.

/// The read assertion is refuted by the fold, and `(bvult x #x3)` by `x = 7`.
const FOLDED_READ_BESIDE_BV_CORE: &str = r#"
(set-logic QF_AUFBV)
(declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
(declare-const x (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 3))
(assert (and (bvult x #x3) (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x)))))
(assert (not (= (select z #x9) (g x))))
(assert (= x #x7))
(check-sat)
"#;

/// [`FOLDED_READ_BESIDE_BV_CORE`] with the pin inside the defining conjunction.
const FOLDED_READ_BESIDE_BV_CORE_ONE_ROOT: &str = r#"
(set-logic QF_AUFBV)
(declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
(declare-const x (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 3))
(assert (and (bvult x #x3) (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x))) (= x #x7)))
(assert (not (= (select z #x9) (g x))))
(check-sat)
"#;

/// The fold beside the ground closure's guard instance: the universal at
/// `#x40` reads `#x07` where the store wrote `#x08`.
const FOLDED_READ_BESIDE_GUARD: &str = r#"
(set-logic ALL)
(declare-const data (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
(declare-const x (_ BitVec 4))
(declare-fun g ((_ BitVec 4)) (_ BitVec 3))
(assert (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x))))
(assert (not (= (select z #x9) (g x))))
(assert (= data (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) #x40 #x08)))
(assert (forall ((i (_ BitVec 8))) (=> (bvult i #x41) (= (select data i) #x07))))
(check-sat)
"#;

#[test]
#[timeout(120_000)]
fn a_constant_array_read_never_displaces_a_checked_refutation() {
    let carcara = require_carcara_or_skip();
    for (label, problem) in [
        (
            "const_array_read_leg_bit_vector_core",
            FOLDED_READ_BESIDE_BV_CORE,
        ),
        (
            "const_array_read_leg_bit_vector_core_one_root",
            FOLDED_READ_BESIDE_BV_CORE_ONE_ROOT,
        ),
        (
            "const_array_read_leg_guard_instance",
            FOLDED_READ_BESIDE_GUARD,
        ),
    ] {
        let proof = solve_unsat_and_get_proof(problem, label);
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{label}: the leg-free refutation must be kept:\n{proof}"
        );
        if let Some(carcara) = carcara.as_ref() {
            assert!(
                run_carcara_trust_free(carcara, label, problem, &proof),
                "{label}: carcara must answer a literal `valid`"
            );
        }
    }
}
