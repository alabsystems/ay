// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence shapes whose `sat` witness AY builds in model completion.
//!
//! The QF_SEQLIA model fixes an equality class and a length for every sequence
//! term, and the decomposition axioms of `seq.replace`, `seq.contains`,
//! `seq.extract` and `seq.nth` commit word equations over skolems, but the
//! sequence theory only values a variable equal to a ground term. The free
//! leaves (`u`, `src`, `r` below) used to be completed one at a time, as their
//! pinned length of default elements, which ignores concatenation: `u = [0,0]`,
//! `src = [0]`, `r = [0,0,0]` falsifies `r = (seq.replace u src dst)`. Their
//! old `sat` came from the Phase-0 completion sub-solve leaking its own model
//! through the shared evaluation memo (fixed in ae8cb6ed5), so it depended on
//! the CPU. Positional witness construction
//! (`executor/model/completion/seq_witness.rs`) now builds these witnesses
//! from the outer model alone, and the gates check them against the original
//! assertions. It replaces the per-carrier witness only when the gates refute
//! that one, so a shape the all-default witness already satisfies keeps it.
//!
//! Every positive shape here is `sat` for z3 4.8.12, and the model AY
//! publishes for each was confirmed by z3. The UNSAT twins (z3: `unsat`)
//! guard the new acceptance path: a construction that satisfies the length
//! system but not the word equations must never turn into `sat`.

const REPLACE_SHAPE: &str = "(set-logic QF_SEQLIA)
     (declare-const u (Seq Int))
     (declare-const src (Seq Int))
     (declare-const dst (Seq Int))
     (declare-const r (Seq Int))
     (assert (= r (seq.replace u src dst)))
     (assert (seq.contains u src))
     (assert (not (= src (as seq.empty (Seq Int)))))
     (assert (not (= u (as seq.empty (Seq Int)))))
     (assert (not (= src dst)))
     (assert (not (= r u)))";

const TAIL_SHAPE: &str = "(set-logic QF_SEQLIA)
     (declare-const s (Seq Int))
     (declare-const tail (Seq Int))
     (declare-const b Bool)
     (assert (= s (seq.++ (seq.unit 1) tail)))
     (assert (=> (< 0 (seq.len s)) (= (+ (seq.len s) (- 1)) (seq.len tail))))
     (assert (or b (> (seq.len s) 3)))";

const EXTRACT_SHAPE: &str = "(set-logic QF_SEQLIA)
     (declare-const s (Seq Int))
     (declare-const t (Seq Int))
     (assert (= t (seq.extract s 1 (- (seq.len s) 1))))
     (assert (= (seq.nth s 0) 7))";

fn solve_with(shape: &str, pins: &str) -> String {
    crate::common::solve(&format!("{shape}\n{pins}\n(check-sat)"))
}

#[test]
fn replace_decomposition_with_pinned_witness_is_sat() {
    let result = solve_with(
        REPLACE_SHAPE,
        "(assert (= u (seq.unit 1)))
         (assert (= src (seq.unit 1)))
         (assert (= dst (seq.unit 2)))",
    );
    assert_eq!(result, "sat");
}

#[test]
fn replace_decomposition_with_symbolic_dst_is_sat() {
    // replace([1], [1], dst) = dst, so `r != u` and `src != dst` both reduce
    // to `dst != [1]`; `dst` itself stays symbolic.
    let result = solve_with(
        REPLACE_SHAPE,
        "(assert (= u (seq.unit 1)))
         (assert (= src (seq.unit 1)))",
    );
    assert_eq!(result, "sat");
}

/// The free-leaf replace variants that were `sat` only through the Phase-0
/// leak, and `unknown` on every core after ae8cb6ed5.
#[test]
fn replace_decomposition_with_free_leaves_is_sat() {
    let variants = [
        ("bare", ""),
        ("v1 len src = 1", "(assert (= (seq.len src) 1))"),
        ("v2 len u = 2", "(assert (= (seq.len u) 2))"),
        ("v4 dst = [5]", "(assert (= dst (seq.unit 5)))"),
        (
            "v7 len dst = len src + 1",
            "(assert (= (seq.len dst) (+ (seq.len src) 1)))",
        ),
        (
            "w6 lengths 4/2/1",
            "(assert (= (seq.len u) 4)) (assert (= (seq.len src) 2))
             (assert (= (seq.len dst) 1))",
        ),
    ];
    let failed: Vec<(&str, String)> = variants
        .into_iter()
        .map(|(name, pins)| (name, solve_with(REPLACE_SHAPE, pins)))
        .filter(|(_, result)| result != "sat")
        .collect();
    assert!(failed.is_empty(), "not sat: {failed:?}");
}

#[test]
fn extract_tail_with_pinned_head_is_sat() {
    // `s = [7, x]`, `t = [x]`: the extract window and the `seq.nth` read
    // identify and bind cells of one class.
    assert_eq!(solve_with(EXTRACT_SHAPE, ""), "sat", "w1");
    assert_eq!(
        solve_with(EXTRACT_SHAPE, "(assert (> (seq.len s) 0))"),
        "sat",
        "w1b"
    );
}

#[test]
fn tail_length_axiom_through_a_non_arithmetic_disjunct_is_sat() {
    // The #8373 tail-length shape Phase 0 was written for (from the verification-consumer
    // take_first_mut fixture): `s` is derived from `[1] ++ tail`.
    assert_eq!(solve_with(TAIL_SHAPE, ""), "sat");
}

/// Shapes the per-carrier (all-default) witness satisfies but the positional
/// one does not: fresh distinct elements break a disequality, keep `v` out of
/// `y` so `seq.replace` is the identity, or disagree with element terms a
/// later phase values. Each is `sat` without the positional witness (at
/// 1ffa9c17a and 938ec0327) and went `unknown` when that witness was
/// committed before Phase 3; the positional candidate must never displace
/// an accepted per-carrier model. The texts are exact: the unused `i` shifts
/// term numbering, and without it the search itself ends elsewhere
/// (`unknown` with or without this change).
#[test]
fn a_positional_candidate_never_displaces_an_accepted_per_carrier_model() {
    let declare = |elem: &str| {
        format!(
            "(set-logic QF_SEQLIA)
             (declare-const u (Seq {elem}))
             (declare-const v (Seq {elem}))
             (declare-const w (Seq {elem}))
             (declare-const x (Seq {elem}))
             (declare-const y (Seq {elem}))
             (declare-const i Int)"
        )
    };
    let cases = [
        (
            "disequality over an extract window",
            "Real",
            "(assert (not (= (seq.++ w u) y)))
             (assert (= (seq.extract y 0 1) (seq.++ v w)))",
        ),
        (
            "negative suffix over a replace",
            "Real",
            "(assert (or (seq.contains (seq.unit 1.0) v) (= x u)))
             (assert (not (seq.suffixof (seq.++ y u) (seq.replace y v x))))
             (assert (not (= (seq.++ v u) (as seq.empty (Seq Real)))))",
        ),
        (
            "unit elements valued after Phase 3",
            "(_ BitVec 2)",
            "(assert (= w u))
             (assert (seq.contains (seq.replace y v x) x))
             (assert (not (= (seq.nth (seq.++ u x) i) #b10)))
             (assert (seq.prefixof v (seq.++ y w)))
             (assert (= (seq.len u) 3))",
        ),
    ];
    let failed: Vec<(&str, String)> = cases
        .into_iter()
        .map(|(name, elem, body)| {
            let smt = format!("{}\n{body}\n(check-sat)", declare(elem));
            (name, crate::common::solve(&smt))
        })
        .filter(|(_, result)| result != "sat")
        .collect();
    assert!(failed.is_empty(), "not sat: {failed:?}");
}

/// The per-carrier model is refuted (`v4 = [0]` gives `(seq.nth v4 0) = 0`,
/// not 3), and at the end of completion the positional one (`v4 = [3]`) is not
/// yet CONFIRMABLE: the preprocessed window dropped `v6 = []`, and a later pass
/// pins that `(Seq Bool)` constant. Adoption therefore goes by refutation, not
/// confirmation; judged by confirmation this corpus file
/// (`rank1_qf_slia_CRASH_seq_sort_interning.smt2`) stays `unknown`.
#[test]
fn adoption_waits_for_leaves_a_later_pass_pins() {
    let result = crate::common::solve(
        "(set-logic QF_SLIA)
         (declare-fun v4 () (Seq Int))
         (declare-fun v6 () (Seq Bool))
         (declare-fun v9 () Int)
         (assert (= v6 (as seq.empty (Seq Bool))))
         (assert (= (seq.len (seq.++ (seq.unit 4) (seq.++ (seq.unit (- 0 1)) (seq.unit 0))))
                    (seq.nth (seq.++ (as seq.empty (Seq Int)) v4) (+ v9 v9))))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

/// UNSAT twins (z3 4.8.12: `unsat`). Where AY cannot refute one, it must stay
/// `unknown`; the positional witness may never make it `sat`.
#[test]
fn unsat_twins_of_the_witness_shapes_are_never_sat() {
    let twins = [
        (
            REPLACE_SHAPE,
            "(assert (= (seq.len src) 1)) (assert (= (seq.len dst) 1))
             (assert (not (= (seq.len r) (seq.len u))))",
        ),
        (REPLACE_SHAPE, "(assert (= u src)) (assert (not (= r dst)))"),
        (
            REPLACE_SHAPE,
            "(assert (= (seq.len u) 4)) (assert (= (seq.len src) 2))
             (assert (= (seq.len dst) 1)) (assert (= (seq.len r) 4))",
        ),
        (
            REPLACE_SHAPE,
            "(assert (= (seq.len u) 1)) (assert (= (seq.len src) 2))",
        ),
        (
            EXTRACT_SHAPE,
            "(assert (> (seq.len s) 0))
             (assert (not (= s (seq.++ (seq.unit 7) t))))",
        ),
        (
            EXTRACT_SHAPE,
            "(assert (= (seq.len s) 3)) (assert (= (seq.len t) 1))",
        ),
        (TAIL_SHAPE, "(assert (= (seq.len s) (seq.len tail)))"),
    ];
    for (i, (shape, pins)) in twins.into_iter().enumerate() {
        let result = solve_with(shape, pins);
        assert_ne!(result, "sat", "UNSAT twin {i} answered sat: {pins}");
    }
}
