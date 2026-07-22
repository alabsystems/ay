// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sequence theory soundness and regression tests (#5841, #5998, #6024, #6026, #6029, #6040).
//!
//! Split from seq_theory_5841.rs — these test axiom reduction soundness,
//! ground evaluation edge cases, and regression fixes.

// ========== Soundness tests for new axiom reductions (#5841) ==========
// These tests verify the axioms produce UNSAT for contradictory formulas,
// not just SAT for everything.

#[test]
fn test_seq_contains_length_unsat_5841() {
    // contains(s, t) implies len(s) >= len(t).
    // If s = empty and t = unit(42), contains must be false.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= s (as seq.empty (Seq Int))))
         (assert (= t (seq.unit 42)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_prefixof_length_unsat_5841() {
    // prefixof(s, t) implies len(s) <= len(t).
    // If s has 2 elements and t has 1, prefix is impossible.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (assert (seq.prefixof (seq.++ (seq.unit 1) (seq.unit 2)) t))
         (assert (= t (seq.unit 99)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_suffixof_length_unsat_5841() {
    // suffixof(s, t) implies len(s) <= len(t).
    // If s has 2 elements and t has 1, suffix is impossible.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (assert (seq.suffixof (seq.++ (seq.unit 1) (seq.unit 2)) t))
         (assert (= t (seq.unit 99)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_extract_oob_empty_5841() {
    // extract(s, 5, 1) from a 1-element sequence is out-of-bounds => empty.
    // Asserting len(extract) = 1 contradicts the OOB axiom.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 10)))
         (assert (= (seq.len (seq.extract s 5 1)) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_not_found_5841() {
    // indexof(s, t, 0) = -1 when !contains(s, t).
    // Asserting indexof >= 0 AND !contains should be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (seq.contains s t)))
         (assert (>= (seq.indexof s t 0) 0))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_empty_source_unsat_5998() {
    // Regression for #5998: indexof synthesized contains(s, t) lacked axioms.
    // With len(s)=0 and len(t)=1, contains(s,t) requires len(s) >= len(t),
    // so indexof(s,t,0) >= 0 is impossible.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (>= (seq.indexof s t 0) 0))
         (assert (= (seq.len s) 0))
         (assert (= (seq.len t) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_implies_contains_5998() {
    // Regression for #5998: indexof > 0 must imply contains(s, t).
    // Asserting indexof = 1 AND !contains should be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.indexof s t 0) 1))
         (assert (= (seq.len t) 1))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_basic_5998() {
    // Non-zero offset: offset < 0 => r = -1. Offset = -2 forces r = -1.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (= (seq.indexof s t (- 2)) (- 1))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_suffix_too_short_5998() {
    // Non-zero offset: indexof(s, t, 1) >= 0 with len(s) = 1, len(t) = 1.
    // offset = len(s) = 1 and t != "" (len(t) = 1), so axiom
    // "offset >= len(s) & t != '' => r = -1" should fire, giving r = -1.
    // This contradicts r >= 0.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (>= (seq.indexof s t 1) 0))
         (assert (= (seq.len s) 1))
         (assert (= (seq.len t) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Regression tests for #5998 Bug 2: tightest prefix ==========

#[test]
fn test_seq_indexof_not_found_returns_neg1_5998() {
    // !contains(s, t) => indexof(s, t, 0) = -1.
    // Asserting !contains AND indexof != -1 should be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (seq.contains s t)))
         (assert (not (= (seq.indexof s t 0) (- 1))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_empty_needle_returns_zero_5998() {
    // indexof(s, "", 0) = 0 for any s.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (not (= (seq.indexof s (as seq.empty (Seq Int)) 0) 0)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Regression tests for #5998 Bug 3: non-zero offset ==========

#[test]
fn test_seq_indexof_negative_offset_returns_neg1_5998() {
    // indexof(s, t, -1) = -1 always.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (= (seq.indexof s t (- 1)) (- 1))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== seq.replace axiom tests (#5841) ==========

#[test]
fn test_seq_replace_empty_src_prepends_5841() {
    // replace(u, "", dst) = dst ++ u (Z3 semantics: empty src prepends dst).
    // Assert the result is not equal to dst ++ u — should be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const dst (Seq Int))
         (declare-const src (Seq Int))
         (assert (= src (as seq.empty (Seq Int))))
         (assert (not (= (seq.replace u src dst) (seq.++ dst u))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_replace_not_found_unchanged_5841() {
    // When u does not contain src, replace returns u unchanged.
    // len(u) = 1, len(src) = 2 => u can't contain src => replace(u, src, dst) = u.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const src (Seq Int))
         (declare-const dst (Seq Int))
         (assert (= (seq.len u) 1))
         (assert (= (seq.len src) 2))
         (assert (not (= (seq.replace u src dst) u)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_replace_decomposition_5841() {
    // When contains(u, src) & src != "" & u != "":
    //   u = x ++ src ++ y  AND  r = x ++ dst ++ y
    // So if we assert seq.contains(u, src) and force constraints, the
    // decomposition should hold. Here: assert replace gives different result
    // than u when contains is true and dst != src. Should be SAT (the result
    // differs from u when src != dst and u contains src).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const src (Seq Int))
         (declare-const dst (Seq Int))
         (declare-const r (Seq Int))
         (assert (= r (seq.replace u src dst)))
         (assert (seq.contains u src))
         (assert (not (= src (as seq.empty (Seq Int)))))
         (assert (not (= u (as seq.empty (Seq Int)))))
         (assert (not (= src dst)))
         (assert (not (= r u)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_replace_sat_basic_5841() {
    // Basic SAT: replace(u, src, dst) = some_value is satisfiable.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const u (Seq Int))
         (declare-const src (Seq Int))
         (declare-const dst (Seq Int))
         (declare-const r (Seq Int))
         (assert (= r (seq.replace u src dst)))
         (assert (>= (seq.len u) 0))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// ========== Regression tests for #5998 R1 findings: cnt_earlier + idx_sfx ==========

#[test]
fn test_seq_indexof_nonzero_offset_value_bounds_5998() {
    // Regression for #5998 R1 Finding 1: non-zero offset idx_sfx decomposition.
    // When indexof(s, t, offset) >= 0, the result must be >= offset.
    // Without decomposition axioms, idx_sfx is unconstrained and the solver
    // could set r = 0 even with offset = 2.
    // Assert: indexof(s, t, 2) = 0 with contains(s, t), len(s) = 5, len(t) = 1.
    // Result 0 < offset 2 is impossible because r = offset + idx_sfx with idx_sfx >= 0.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 5))
         (assert (= (seq.len t) 1))
         (assert (= (seq.indexof s t 2) 0))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_result_ge_offset_5998() {
    // Regression for #5998 R1 Finding 1: idx_sfx decomposition gives idx_sfx >= 0
    // so r = offset + idx_sfx >= offset when found.
    // Assert: contains(s, t), len(s) = 5, len(t) = 1, offset = 3,
    //         indexof(s, t, 3) = 1 — should be UNSAT because r >= offset = 3.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 5))
         (assert (= (seq.len t) 1))
         (assert (= (seq.indexof s t 3) 1))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_indexof_nonzero_offset_decomposition_sat_5998() {
    // SAT test for non-zero offset with decomposition.
    // Assert: contains(s, t), len(s) = 5, len(t) = 1, offset = 2.
    // indexof(s, t, 2) >= 2 should be SAT.
    // Verifies the decomposition axioms produce a consistent assignment.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 5))
         (assert (= (seq.len t) 1))
         (assert (>= (seq.indexof s t 2) 2))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_indexof_nonzero_offset_upper_bound_5998() {
    // The result of indexof(s, t, offset) must be < len(s) when found.
    // With decomposition: r = offset + len(sk_left2), and
    // sfx = sk_left2 ++ t ++ sk_right2, so len(sk_left2) + len(t) <= len(sfx).
    // len(sfx) = len(s) - offset, so r = offset + len(sk_left2) <= len(s) - len(t).
    // Assert: len(s) = 4, len(t) = 2, offset = 1, indexof(s, t, 1) = 4.
    // r = 4 requires len(sk_left2) = 3 but len(sfx) = 3, and
    // len(sk_left2) + len(t) = 3 + 2 = 5 > 3 = len(sfx), which is impossible.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (assert (= (seq.len s) 4))
         (assert (= (seq.len t) 2))
         (assert (= (seq.indexof s t 1) 4))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Non-zero-offset indexof: ground evaluation + direct bounds ==========
// The non-zero-offset `seq.indexof` reduction reduces to a synthesized
// zero-offset search on `extract(s, offset, ...)`, which model validation cannot
// evaluate for a symbolic `s` — so even an out-of-window result stayed `unknown`.
// Two sound additions close the UNSAT direction without the suffix model:
//   * exact ground evaluation when `s`, `t` resolve to concrete sequences and
//     `offset` is a constant (forces `r = <computed>`); and
//   * the direct LIA fact `r = -1 OR r >= offset` (a found position is never
//     before the search start).
// All are pure refinements (they only refute), so they never introduce a wrong
// verdict — verified by differential fuzzing vs z3 (zero sat-vs-unsat
// disagreements over 4000+ cases).

/// Ground (nth-reconstructed) `s`, constant offset: the exact indexof is forced,
/// so a wrong asserted value is UNSAT. `s = [1,2,3]`, `indexof(s,[3],1) = 2`, so
/// `= 5` is impossible.
#[test]
fn test_seq_indexof_nonzero_offset_ground_exact_unsat_5998() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (= (seq.indexof s (seq.unit 3) 1) 5))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

/// Literal-ground `s` with the only occurrence of `t` AT/AFTER the offset:
/// `indexof([1,2,1], [1], 1) = 2`, so asserting `= -1` is UNSAT. Before the
/// ground-exact path the non-zero-offset reduction left this `unknown`.
#[test]
fn test_seq_indexof_nonzero_offset_ground_found_after_offset_unsat_5998() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (assert (= (seq.indexof
                      (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 1)))
                      (seq.unit 1) 1) (- 1)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

/// Soundness: a SYMBOLIC empty needle (`len(t) = 0` but not the syntactic
/// `seq.empty`) at a non-zero in-range offset is found AT the offset, so
/// `indexof(s, t, 1) <= -1` is UNSAT. Without the `len(t) = 0`-keyed axiom the
/// result was under-constrained and a free `contains = false` wrongly allowed
/// `r = -1` (a false-SAT).
#[test]
fn test_seq_indexof_nonzero_offset_empty_needle_unsat_5998() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 4))
         (assert (= (seq.len t) 0))
         (assert (<= (seq.indexof s t 1) (- 1)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Negative contains soundness tests ==========
// The negative !contains axiom is currently incomplete (MVP): only the
// skolem decomposition is absent when contains=false, but no explicit
// negative axiom forces inconsistency. These tests check whether
// the solver is still sound on basic !contains scenarios.

#[test]
fn test_seq_not_contains_length_sat() {
    // !contains(s, t) when len(t) > len(s) — trivially SAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (not (seq.contains s t)))
         (assert (= (seq.len s) 1))
         (assert (= (seq.len t) 3))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_concrete_unsat() {
    // s = (seq.unit 1 ++ seq.unit 2 ++ seq.unit 3) clearly contains (seq.unit 2).
    // Asserting !contains is UNSAT. Fixed via contains-indexof bridge (#6024):
    // contains(s,t) <=> indexof(s,t,0) >= 0 forces indexof decomposition to
    // derive contradiction on concrete sequences.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= t (seq.unit 2)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// === Ground evaluation edge cases (#6024) ===

#[test]
fn test_seq_contains_empty_in_empty_sat_6024() {
    // Empty sequence contains empty sequence. ground_seq_contains returns true
    // for empty needle.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (as seq.empty (Seq Int))))
         (assert (seq.contains s (as seq.empty (Seq Int))))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_empty_in_nonempty_unsat_6024() {
    // Every sequence contains the empty sequence. Asserting !contains(s, empty)
    // should be UNSAT when s is concrete non-empty.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (not (seq.contains s (as seq.empty (Seq Int)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_not_contains_nonempty_in_empty_sat_6024() {
    // Empty sequence does not contain a non-empty sequence.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (as seq.empty (Seq Int))))
         (assert (not (seq.contains s (seq.unit 1))))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_partial_match_sat_6024() {
    // s = [1, 3, 2], t = [1, 2]. The elements 1 and 2 both appear but NOT
    // contiguously. !contains should be SAT (no contiguous subsequence).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 3) (seq.unit 2)))))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_contains_self_sat_6024() {
    // A concrete sequence always contains itself.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (seq.contains s t))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_contains_self_unsat_6024() {
    // Asserting a sequence does NOT contain itself is UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 5) (seq.unit 6))))
         (assert (not (seq.contains s s)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// === seq.at tests (#6029) ===

#[test]
fn test_seq_at_sat_basic_6029() {
    // seq.at(s, 1) on s = [1, 2, 3] should return (seq.unit 2)
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.at s 1) (seq.unit 2)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_at_consistency_6029() {
    // seq.at(s, i) is lowered to seq.extract(s, i, 1).
    // The result should have length 1 for valid indices.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const r (Seq Int))
         (assert (= s (seq.++ (seq.unit 10) (seq.++ (seq.unit 20) (seq.unit 30)))))
         (assert (= r (seq.at s 0)))
         (assert (= (seq.len r) 1))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_at_no_parse_error_6029() {
    // Verify that seq.at is recognized (no UndefinedSymbol error)
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 5)))
         (assert (= (seq.len (seq.at s 0)) 1))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// === Unsupported seq op allowlist guard (#6026) ===

#[test]
fn test_seq_replace_all_returns_unknown_6026() {
    // seq.replace_all is parsed but has no axiom support.
    // The allowlist guard must return unknown (not false-SAT).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= t (seq.replace_all s (seq.unit 1) (seq.unit 2))))
         (assert (= (seq.len s) 3))
         (check-sat)",
    );
    assert_eq!(result, "unknown");
}

// === Soundness regression: prefixof + extract axiom interaction (#6033) ===

#[test]
fn test_seq_prefixof_extract_interaction_sat_6033() {
    // False-UNSAT regression: prefixof and extract axiom decompositions
    // on a concrete 3-element sequence produce conflicting skolem constraints.
    // Z3 correctly returns sat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (= (seq.extract s 1 1) (seq.unit 2)))
         (check-sat)",
    );
    // Fixed (#6033): removed broken completeness axiom that created
    // overlapping skolem decompositions. Z3 and ay both return sat.
    assert_eq!(result, "sat");
}

// === Soundness: prefixof completeness (#6035) ===

#[test]
fn test_seq_not_prefixof_concrete_prefix_unsat_6035() {
    // [1] IS a prefix of [1,2]. NOT prefixof must be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_not_prefixof_non_prefix_sat_6035() {
    // [5] is NOT a prefix of [1,2]. NOT prefixof must be sat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 5)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_not_prefixof_longer_prefix_sat_6035() {
    // [1,2,3] is NOT a prefix of [1,2] (too long). NOT prefixof must be sat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// ========== #6028: nth-constrained !contains false-SAT ==========

#[test]
fn test_seq_nth_constrained_not_contains_unsat_6028() {
    // Sequence defined element-by-element via seq.nth + seq.len constraints.
    // s = [1, 2, 3], t = [2]. contains(s, t) must be true,
    // so !contains(s, t) is unsatisfiable.
    // Before #6028 fix: ay returned false-SAT because build_ground_seq_map
    // only recognized seq.unit/seq.++/seq.empty patterns, missing nth-defined seqs.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (= t (seq.unit 2)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_constrained_not_contains_sat_6028() {
    // s = [1, 2, 3], t = [5]. Element 5 not in s, so !contains is satisfiable.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (= t (seq.unit 5)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_nth_constrained_empty_contains_unsat_6028() {
    // Empty sequence is always contained. !contains(s, empty) is unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 2))
         (assert (= (seq.nth s 0) 10))
         (assert (= (seq.nth s 1) 20))
         (assert (= t (as seq.empty (Seq Int))))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_incomplete_no_forced_eval_6028() {
    // Incomplete nth constraints (missing index 1 of 3). A valid model exists
    // (e.g. s = [1, 0, 3], which does NOT contain [2]), so the verdict must
    // never be unsat.
    //
    // #nonstring-seq-failclose: AY could not produce a VALID model — the
    // baseline emitted s = [1, 2, 3], whose middle element 2 makes s CONTAIN
    // [2] and thus falsifies the asserted `(not (seq.contains s t))`. That is
    // the self-falsifying wrong-`sat` signature, so the fail-closed gate now
    // returns a sound `unknown`. Accept sat (with a real model) or unknown;
    // reject only unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 2) 3))
         (assert (= t (seq.unit 2)))
         (assert (not (seq.contains s t)))
         (check-sat)",
    );
    assert_ne!(result, "unsat");
}

#[test]
fn test_seq_nth_constrained_not_prefixof_unsat_6036() {
    // s = [1, 2, 3] via nth. [1] IS a prefix of s, so !prefixof is unsat.
    // Requires nth ground equality injection (#6036) so prefixof axioms
    // can reason about the sequence structure.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (not (seq.prefixof (seq.unit 1) s)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== #seq-bool-nth / #seq-partial-pred: search predicates over =========
// nth-defined and PARTIALLY-determined sequences must never be wrong-SAT.
//
// Root cause: a search predicate (prefixof/suffixof/contains/indexof) applied to
// a seq constrained via `(seq.len s)=N` + `(seq.nth s i)=v` (NOT a direct
// `(= s (seq.++ ...))`) was left under-constrained, so AY answered `sat` where the
// reconstructed contents make the predicate FALSE (true answer `unsat`). Two gaps:
//   * Bool elements: `(= (seq.nth s i) true/false)` is simplified to
//     `(seq.nth s i)` / `(not (seq.nth s i))`, so the nth reconstruction never saw
//     it (`try_extract_bool_nth_constraint` recovers it).
//   * Partially-determined seqs: only SOME elements pinned, so full reconstruction
//     does not fire, yet a PINNED element can still make the predicate definitely
//     false (`generate_seq_partial_predicate_axioms` forces the definite outcome).
// The invariant asserted here is the soundness one: the answer is NEVER `sat`.

#[test]
fn test_seq_bool_nth_prefixof_wrong_sat_unsat() {
    // s = [false] via len+nth (Bool). [true] is NOT a prefix => unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Bool))
         (assert (= (seq.len s) 1))
         (assert (= (seq.nth s 0) false))
         (assert (seq.prefixof (seq.unit true) s))
         (check-sat)",
    );
    assert_ne!(
        result, "sat",
        "bool nth-defined prefixof must not be wrong-SAT"
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bool_nth_indexof_wrong_sat_unsat() {
    // s = [true,true,false]. [true,true] occurs at index 0, so indexof != -1.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Bool))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) true))
         (assert (= (seq.nth s 1) true))
         (assert (= (seq.nth s 2) false))
         (assert (= (- 1) (seq.indexof s (seq.++ (seq.unit true) (seq.unit true)) 0)))
         (check-sat)",
    );
    assert_ne!(result, "sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bool_nth_prefixof2_wrong_sat_unsat() {
    // s = [true,false]. [false] is not a prefix (s[0]=true) => unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Bool))
         (assert (= (seq.len s) 2))
         (assert (= (seq.nth s 0) true))
         (assert (= (seq.nth s 1) false))
         (assert (seq.prefixof (seq.unit false) s))
         (check-sat)",
    );
    assert_ne!(result, "sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_partial_prefixof_wrong_sat_unsat() {
    // Partially determined: s[1]=-1, s[2]=2 pinned, s[0] free. prefixof([-1,0],s)
    // needs s[1]=0 but s[1]=-1 => impossible regardless of s[0] => unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 1) (- 1)))
         (assert (= (seq.nth s 2) 2))
         (assert (seq.prefixof (seq.++ (seq.unit (- 1)) (seq.unit 0)) s))
         (check-sat)",
    );
    assert_ne!(
        result, "sat",
        "partially-determined prefixof must not be wrong-SAT"
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_partial_contains_wrong_sat_unsat() {
    // Partially determined: s[1]=0, s[2]=1, s[0] free. [2,1] cannot occur at any
    // window (s[1]=0 blocks both candidate windows) => unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 1) 0))
         (assert (= (seq.nth s 2) 1))
         (assert (seq.contains s (seq.++ (seq.unit 2) (seq.unit 1))))
         (check-sat)",
    );
    assert_ne!(result, "sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_partial_indexof_upper_bound_wrong_sat_unsat() {
    // Partially determined: s[1]=1, s[2]=1, s[0] free. indexof([1],0) is 0 or 1
    // (a pinned match at index 1 bounds it), never 2 => `2 = indexof` is unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 1) 1))
         (assert (= (seq.nth s 2) 1))
         (assert (= 2 (seq.indexof s (seq.unit 1) 0)))
         (check-sat)",
    );
    assert_ne!(result, "sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_partial_suffixof_bv_wrong_sat_unsat() {
    // BitVec elements, partially determined: s[0]=#x7. suffixof([#x1,#x1],s) needs
    // the whole length-2 s to be [#x1,#x1], but s[0]=#x7 => unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 4)))
         (assert (= (seq.len s) 2))
         (assert (= (seq.nth s 0) (_ bv7 4)))
         (assert (seq.suffixof (seq.++ (seq.unit (_ bv1 4)) (seq.unit (_ bv1 4))) s))
         (check-sat)",
    );
    assert_ne!(result, "sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_partial_indexof_offset_wrong_sat_unsat() {
    // Offset reasoning: s[0]=1, s[1..] free. With offset 2 the only candidate is
    // index 2, so indexof in {2,-1}, never 0 => `0 = indexof ... 2` is unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= 0 (seq.indexof s (seq.unit 1) 2)))
         (check-sat)",
    );
    assert_ne!(result, "sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bool_nth_prefixof_genuine_sat_not_unsat() {
    // Soundness guard the OTHER way: s = [true,false], [true] IS a prefix, so the
    // problem is genuinely satisfiable — the new forcing must not over-constrain it
    // to a wrong UNSAT (`unknown` is an acceptable sound answer here).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Bool))
         (assert (= (seq.len s) 2))
         (assert (= (seq.nth s 0) true))
         (assert (= (seq.nth s 1) false))
         (assert (seq.prefixof (seq.unit true) s))
         (check-sat)",
    );
    assert_ne!(result, "unsat", "genuine SAT must not become wrong-UNSAT");
}

// ========== last_indexof rightmost guarantee tests (#6030) ==========
// W4 implemented last_indexof axioms but didn't test the key semantic:
// returning the LAST (rightmost) position, not just any position.

#[test]
fn test_seq_last_indexof_rightmost_value_6030() {
    // t = [1, 2, 1], s = [1]. last_indexof(t, s) should be 2 (last occurrence).
    // Assert i != 2 to verify the rightmost axiom forces the correct value.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (declare-const i Int)
         (assert (= t (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 1)))))
         (assert (= i (seq.last_indexof t (seq.unit 1))))
         (assert (not (= i 2)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "last_indexof([1,2,1], [1]) must be 2 (rightmost), not 0"
    );
}

#[test]
fn test_seq_last_indexof_rightmost_not_first_6030() {
    // t = [1, 2, 1], s = [1]. last_indexof(t, s) should NOT be 0 (first occurrence).
    // This is the dual: asserting i = 0 should be unsat because the axioms
    // enforce the rightmost guarantee via !contains(tail(s) ++ sk_right, s).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (declare-const i Int)
         (assert (= t (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 1)))))
         (assert (= i (seq.last_indexof t (seq.unit 1))))
         (assert (= i 0))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "last_indexof([1,2,1], [1]) cannot be 0 — rightmost guarantee requires i=2"
    );
}

#[test]
fn test_seq_last_indexof_single_occurrence_6030() {
    // t = [1, 2, 3], s = [2]. last_indexof = indexof = 1 (only one occurrence).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (declare-const i Int)
         (assert (= t (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= i (seq.last_indexof t (seq.unit 2))))
         (assert (not (= i 1)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "last_indexof([1,2,3], [2]) must be 1 (only occurrence)"
    );
}

// === Soundness: prefixof+extract interaction with nth-defined sequences ===

#[test]
fn test_seq_nth_prefixof_extract_interaction_sat_6033() {
    // Regression: nth-defined seq with BOTH prefixof and extract.
    // s = [1,2,3] via nth. prefixof([1], s) is true and extract(s,1,1) = [2].
    // Z3 returns sat. AY must NOT return false-UNSAT.
    // This is the #6033 variant with nth-defined (not concat-defined) sequences.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 3))
         (assert (= (seq.nth s 0) 1))
         (assert (= (seq.nth s 1) 2))
         (assert (= (seq.nth s 2) 3))
         (assert (seq.prefixof (seq.unit 1) s))
         (assert (= (seq.extract s 1 1) (seq.unit 2)))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "#6033 variant: nth-defined seq with prefixof+extract must be sat"
    );
}

// === Soundness: seq.extract ground evaluation (#6040) ===

#[test]
fn test_seq_extract_ground_false_sat_6040() {
    // Reproduction from #6040: extract(s, 0, 1) on s = [1,2,3] must equal [1].
    // Asserting it equals [5] must be unsat.
    // Previously returned sat because skolem decomposition couldn't force the result.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.extract s 0 1) (seq.unit 5)))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3], 0, 1) = [1], not [5]");
}

#[test]
fn test_seq_extract_ground_middle_6040() {
    // Extract middle element: extract([1,2,3], 1, 1) = [2].
    // Asserting it equals [9] must be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.extract s 1 1) (seq.unit 9)))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3], 1, 1) = [2], not [9]");
}

#[test]
fn test_seq_extract_ground_multi_elem_6040() {
    // Extract 2 elements: extract([1,2,3], 0, 2) = [1,2].
    // Asserting len = 1 must be unsat (it should be 2).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.len (seq.extract s 0 2)) 1))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "extract([1,2,3], 0, 2) has length 2, not 1"
    );
}

#[test]
fn test_seq_extract_ground_oob_6040() {
    // Extract beyond bounds: extract([1,2], 5, 1) = empty.
    // Asserting len > 0 must be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (> (seq.len (seq.extract s 5 1)) 0))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "extract([1,2], 5, 1) = empty (out of bounds)"
    );
}

#[test]
fn test_seq_extract_ground_clamped_6040() {
    // Extract clamped: extract([1,2,3], 1, 10) = [2,3] (n exceeds remaining).
    // The result should have length 2.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.len (seq.extract s 1 10)) 3))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "extract([1,2,3], 1, 10) has length 2, not 3"
    );
}

#[test]
fn test_seq_extract_ground_correct_sat_6040() {
    // Positive test: extract([1,2,3], 0, 1) = [1] should be sat.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= (seq.extract s 0 1) (seq.unit 1)))
         (check-sat)",
    );
    assert_eq!(result, "sat", "extract([1,2,3], 0, 1) = [1] is correct");
}

// ========== Multi-element extract ground eval (#6040) ==========

/// extract([1,2,3], 0, 2) should be [1,2]; claiming it's [1,99] is UNSAT.
#[test]
fn test_seq_extract_multi_elem_wrong_second_unsat_6040() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 2)))
         (assert (= e (seq.++ (seq.unit 1) (seq.unit 99))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],0,2) != [1,99]");
}

/// extract([1,2,3], 0, 2) should be [1,2]; claiming it's [99,2] is UNSAT.
#[test]
fn test_seq_extract_multi_elem_wrong_first_unsat_6040() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 2)))
         (assert (= e (seq.++ (seq.unit 99) (seq.unit 2))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],0,2) != [99,2]");
}

/// Positive test: extract([1,2,3], 0, 2) = [1,2] should be SAT.
#[test]
fn test_seq_extract_multi_elem_correct_sat_6040() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 2)))
         (assert (= e (seq.++ (seq.unit 1) (seq.unit 2))))
         (check-sat)",
    );
    assert_eq!(result, "sat", "extract([1,2,3],0,2) = [1,2] is correct");
}

/// 3-element extract: extract([1,2,3], 0, 3) != [1,2,99] is UNSAT.
#[test]
fn test_seq_extract_three_elem_wrong_unsat_6040() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 0 3)))
         (assert (= e (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 99)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],0,3) != [1,2,99]");
}

/// Middle extraction: extract([1,2,3], 1, 2) != [2,99] is UNSAT.
#[test]
fn test_seq_extract_middle_multi_elem_unsat_6040() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 1 2)))
         (assert (= e (seq.++ (seq.unit 2) (seq.unit 99))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "extract([1,2,3],1,2) != [2,99]");
}

/// Positive middle extraction: extract([1,2,3], 1, 2) = [2,3] should be SAT.
#[test]
fn test_seq_extract_middle_multi_elem_sat_6040() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const e (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
         (assert (= e (seq.extract s 1 2)))
         (assert (= e (seq.++ (seq.unit 2) (seq.unit 3))))
         (check-sat)",
    );
    assert_eq!(result, "sat", "extract([1,2,3],1,2) = [2,3] is correct");
}

// ========== Basic (Seq _) theorem soundness (#seq-assoc, #seq-pred-taut,
// #seq-len-zero) ==========
// AY previously reported the NEGATION of these basic sequence theorems as SAT.
// They are tautologies, so their negation is UNSAT; the concrete-element
// suffix mismatch is refuted via fail-closed model validation (unsat-or-unknown,
// never wrong SAT). z3 is the oracle for all of these.

/// seq.++ associativity: (a ++ b) ++ c = a ++ (b ++ c). The negation is UNSAT.
/// Previously wrong-SAT because EUF treated seq.++ as uninterpreted (#seq-assoc).
#[test]
fn test_seq_concat_associativity_negation_unsat_seqassoc() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (declare-const c (Seq Int))
         (assert (not (= (seq.++ (seq.++ a b) c) (seq.++ a (seq.++ b c)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "concat associativity is a theorem");
}

/// seq.++ commutativity is NOT a theorem: a ++ b != b ++ a is satisfiable. The
/// associativity normalization must NOT equate different leaf orders, so this
/// must never become a (wrong) unsat.
#[test]
fn test_seq_concat_non_commutativity_not_unsat_seqassoc() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (assert (not (= (seq.++ a b) (seq.++ b a))))
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "concat is NOT commutative; a++b != b++a is satisfiable"
    );
}

/// Empty is a subsequence of everything: contains(s, empty) is a tautology, so
/// its negation is UNSAT (#seq-pred-taut).
#[test]
fn test_seq_contains_empty_negation_unsat_seqpredtaut() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const s (Seq Int))
         (assert (not (seq.contains s (as seq.empty (Seq Int)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "empty is a subsequence of everything");
}

/// Reflexive containment: contains(s, s) is a tautology, negation UNSAT.
#[test]
fn test_seq_contains_self_negation_unsat_seqpredtaut() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const s (Seq Int))
         (assert (not (seq.contains s s)))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "containment is reflexive");
}

/// Empty is a prefix of everything: prefixof(empty, s) tautology, negation UNSAT.
#[test]
fn test_seq_prefixof_empty_negation_unsat_seqpredtaut() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const s (Seq Int))
         (assert (not (seq.prefixof (as seq.empty (Seq Int)) s)))
         (check-sat)",
    );
    assert_eq!(result, "unsat", "empty is a prefix of everything");
}

/// Concrete-element suffix mismatch: [0]++s can never be a suffix of [1] (the
/// length axioms force s empty, then [0] != [1]). Refuted via fail-closed model
/// validation — must be unsat OR unknown, NEVER (wrong) sat (#seq-len-zero).
#[test]
fn test_seq_suffixof_concrete_mismatch_not_sat_seqlenzero() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const s (Seq Int))
         (assert (seq.suffixof (seq.++ (seq.unit 0) s) (seq.unit 1)))
         (check-sat)",
    );
    assert_ne!(
        result, "sat",
        "[0]++s cannot be a suffix of [1]; must not be wrong-SAT"
    );
}

/// Genuine SAT must be preserved: s = [1,2] is satisfiable.
#[test]
fn test_seq_concrete_equality_still_sat_nonregression() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
         (check-sat)",
    );
    assert_eq!(result, "sat", "s = [1,2] is satisfiable");
}

/// contains(s, [5]) is satisfiable (s can be [5]), so the verdict must never be
/// `unsat`.
///
/// #nonstring-seq-failclose: AY's symbolic non-string sequence theory could not
/// produce a VALID model here — the baseline emitted `s = [0]`, which does NOT
/// contain `[5]` and therefore falsifies its own assertion (a self-falsifying
/// wrong-`sat`). The fail-closed gate soundly returns `unknown` instead. Accept
/// `sat` (with a real model) or `unknown`; reject only `unsat`.
#[test]
fn test_seq_contains_unit_not_unsat_nonregression() {
    let result = crate::common::solve(
        "(set-logic ALL)
         (declare-const s (Seq Int))
         (assert (seq.contains s (seq.unit 5)))
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "contains(s,[5]) is satisfiable; must not be unsat"
    );
}

/// (#seq-ite-eq) Equality of a concrete one-element sequence with an `ite`
/// whose BOTH branches differ from it is UNSAT regardless of the (model-
/// undetermined) condition. Here `(seq.at v1 0) = [false]` matches NEITHER the
/// then-branch `(seq.unit true) = [true]` NOR the else-branch (an empty
/// concat = `[]`), so the equality is false for every value of the condition.
/// The condition `(seq.nth (seq.unit v5) (- 3))` is an out-of-bounds read that
/// the evaluator cannot resolve, so the Tseitin encoding leaves two
/// opposite-polarity unit clauses over the SAME atom — caught by the
/// cross-conjunct unit-clause contradiction gate. Must be unsat OR unknown,
/// NEVER (wrong) sat. Regression for soundness_fuzz_round2.
#[test]
fn test_seq_ite_eq_both_branches_mismatch_not_sat_seqiteeq() {
    let result = crate::common::solve(
        "(set-logic QF_S)
         (declare-fun v1 () (Seq Bool))
         (declare-fun v3 () (Seq Bool))
         (declare-fun v5 () Bool)
         (assert (= v1 (seq.++ (seq.unit false) (seq.unit false))))
         (assert (= v3 (as seq.empty (Seq Bool))))
         (assert (= (seq.at v1 0)
                    (ite (seq.nth (seq.unit v5) (- 3))
                         (seq.unit true)
                         (seq.++ v3 (as seq.empty (Seq Bool)) (as seq.empty (Seq Bool))))))
         (check-sat)",
    );
    assert_ne!(
        result, "sat",
        "[false] equals neither ite branch ([true] / []); must not be wrong-SAT"
    );
}

/// Genuine SAT companion: when the LHS DOES match one ite branch, the equality
/// is satisfiable and must NOT be degraded by the unit-clause gate. Here
/// `(seq.at v1 0) = [true]` equals the then-branch, so a model exists.
#[test]
fn test_seq_ite_eq_branch_match_still_sat_nonregression() {
    let result = crate::common::solve(
        "(set-logic QF_S)
         (declare-fun v1 () (Seq Bool))
         (declare-fun v5 () Bool)
         (assert (= v1 (seq.++ (seq.unit true) (seq.unit false))))
         (assert (= (seq.at v1 0)
                    (ite (seq.nth (seq.unit v5) (- 3))
                         (seq.unit true)
                         (as seq.empty (Seq Bool)))))
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "[true] matches the ite then-branch; a model exists, must not be wrong-UNSAT"
    );
}

// ========== `seq.*` over a String operand (wrong-SAT regression) ==========
// SMT-LIB defines `String` as `(Seq Char)`, so every sequence operator is also a
// string operator and z3 decides both spellings. AY models `Sort::String`
// separately from `Sort::Seq`, so a `seq.*` app over a String elaborated into a
// named app that NEITHER theory interpreted: it survived as an uninterpreted
// function and AY answered `sat` to plainly unsatisfiable ground formulas, with
// exit 0 and no diagnostic. `seq.len "abab"` IS 4, so each negation below is
// UNSAT — z3 says unsat on every one. Six operators were affected.
//
// The elaborator now routes these to their `str.*` twin (same operator, same
// values), and fails closed where AY has no twin rather than answering from a
// stub. Each assertion here answered `sat` before the fix.

#[test]
fn test_seq_ops_over_string_are_not_uninterpreted_wrong_sat() {
    for (op, formula) in [
        ("seq.len", r#"(not (= (seq.len "abab") 4))"#),
        ("seq.contains", r#"(not (seq.contains "abab" "ab"))"#),
        ("seq.at", r#"(not (= (seq.at "abab" 1) "b"))"#),
        ("seq.indexof", r#"(not (= (seq.indexof "abab" "ab" 0) 0))"#),
        ("seq.++", r#"(not (= (seq.++ "ab" "ab") "abab"))"#),
        ("seq.extract", r#"(not (= (seq.extract "abab" 0 2) "ab"))"#),
    ] {
        let result =
            crate::common::solve(&format!("(set-logic ALL)\n(assert {formula})\n(check-sat)"));
        assert_eq!(
            result, "unsat",
            "{op} over a String must be decided as the str.* twin, never left \
             uninterpreted (a `sat` here is a wrong answer; z3 says unsat)"
        );
    }
}

#[test]
fn test_seq_ops_over_string_true_facts_still_sat() {
    // The routing must not over-reject: the true facts stay satisfiable.
    for (op, formula) in [
        ("seq.len", r#"(= (seq.len "abab") 4)"#),
        ("seq.contains", r#"(seq.contains "abab" "ab")"#),
        ("seq.++", r#"(= (seq.++ "ab" "ab") "abab")"#),
    ] {
        let result =
            crate::common::solve(&format!("(set-logic ALL)\n(assert {formula})\n(check-sat)"));
        assert_eq!(
            result, "sat",
            "{op} over a String must still decide true facts"
        );
    }
}

#[test]
fn test_seq_ops_over_string_without_str_twin_fail_closed() {
    // `seq.last_indexof` and `seq.nth` have no `str.*` twin in AY. They must fail
    // closed — never a definite verdict from an uninterpreted stub.
    // `last_indexof("abab","ab")` is 2, so this is UNSAT; before the fix AY
    // answered `sat`. Rejecting at elaboration (which `solve` surfaces as a
    // panic) and returning `unknown` are both acceptable; answering `sat` is not.
    for formula in [
        r#"(not (= (seq.last_indexof "abab" "ab") 2))"#,
        r#"(not (= (seq.nth "abab" 0) "a"))"#,
    ] {
        let smt = format!("(set-logic ALL)\n(assert {formula})\n(check-sat)");
        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(|| crate::common::solve(&smt));
        std::panic::set_hook(hook);
        if let Ok(result) = outcome {
            assert_ne!(
                result, "sat",
                "no str.* twin exists, so this must fail closed rather than answer \
                 `sat` from an uninterpreted stub: {formula}"
            );
        }
    }
}

// ========== Symbolic (Seq Int) wrong-verdict regressions ==========
// Four cross-surface soundness bugs where AY returned `sat` for formulas z3
// proves `unsat` (a negated seq theorem the incomplete axiomatization failed to
// refute), and could not even exhibit a model value for its own answer. Each
// must now be NON-SAT (decided `unsat`, or a sound `unknown` — never `sat`).
// Fixed by adding the missing sound axioms: extract-whole identity with a
// symbolic length, `seq.at` = `seq.unit(seq.nth …)` for an in-bounds index, and
// subsequence-containment transitivity. See axioms_search.rs.

#[test]
fn test_seq_extract_whole_symbolic_len_not_sat() {
    // `(seq.extract a 0 (seq.len a))` copies all of `a`, so its disequality from
    // `a` is UNSAT. Was wrongly `sat` because the full-extract identity only
    // fired for a LITERAL length, not the `(seq.len a)` term.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (assert (not (= (seq.extract a 0 (seq.len a)) a)))
         (check-sat)",
    );
    assert_ne!(result, "sat", "extract-whole != itself must not be sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_at_is_unit_nth_in_bounds_not_sat() {
    // For an in-bounds index, `(seq.at a 0)` is `(seq.unit (seq.nth a 0))`, so
    // their disequality under `0 < len a` is UNSAT. Was wrongly `sat` because the
    // length-1 extract node was never linked to the element read.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (assert (< 0 (seq.len a)))
         (assert (not (= (seq.at a 0) (seq.unit (seq.nth a 0)))))
         (check-sat)",
    );
    assert_ne!(result, "sat", "at = unit(nth) in-bounds must not be sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_of_at_in_bounds_not_sat() {
    // `(seq.nth (seq.at a 1) 0)` reads the same element as `(seq.nth a 1)` when
    // index 1 is in bounds, so their disequality is UNSAT. Was wrongly `sat`.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (assert (< 1 (seq.len a)))
         (assert (not (= (seq.nth (seq.at a 1) 0) (seq.nth a 1))))
         (check-sat)",
    );
    assert_ne!(result, "sat", "nth(at(a,1),0) = nth(a,1) must not be sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_contains_transitivity_not_sat() {
    // Subsequence containment is transitive: `a ⊇ b ∧ b ⊇ c ⟹ a ⊇ c`, so with
    // `¬(a ⊇ c)` the conjunction is UNSAT. Was wrongly `sat` — AY even printed a
    // model a=[0,0,0], b=[0,0], c=[0] violating its own third assertion.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (declare-const c (Seq Int))
         (assert (seq.contains a b))
         (assert (seq.contains b c))
         (assert (not (seq.contains a c)))
         (check-sat)",
    );
    assert_ne!(result, "sat", "contains transitivity must not be sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_contains_transitivity_chain_not_sat() {
    // Longer chain `a ⊇ b ⊇ c ⊇ d ∧ ¬(a ⊇ d)`: the bounded transitive-closure
    // fixpoint must still refute it. Guards against a one-hop-only regression.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (declare-const c (Seq Int))
         (declare-const d (Seq Int))
         (assert (seq.contains a b))
         (assert (seq.contains b c))
         (assert (seq.contains c d))
         (assert (not (seq.contains a d)))
         (check-sat)",
    );
    assert_ne!(result, "sat", "contains transitivity chain must not be sat");
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_contains_self_extract_not_sat() {
    // A sequence always contains any `seq.extract` window of itself (including
    // `seq.at`), so `¬(seq.contains a (seq.at a 0))` under `0 < len a` is UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (assert (< 0 (seq.len a)))
         (assert (not (seq.contains a (seq.at a 0))))
         (check-sat)",
    );
    assert_ne!(result, "sat", "contains(a, at(a,0)) must not be sat");
    assert_eq!(result, "unsat");
}

// Companion positive cases: the new axioms must NOT over-constrain genuine SATs
// into `unsat`/`unknown`.

#[test]
fn test_seq_contains_transitivity_positive_still_sat() {
    // `a ⊇ b ∧ b ⊇ c ∧ a ⊇ c` is satisfiable — transitivity must not falsify it.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (declare-const c (Seq Int))
         (assert (seq.contains a b))
         (assert (seq.contains b c))
         (assert (seq.contains a c))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_extract_whole_positive_not_falsely_unsat() {
    // The extract-whole IDENTITY (not its negation) is satisfiable, so the new
    // identity axiom must never REFUTE it. AY currently answers `unknown` here
    // (a pre-existing incompleteness in whole-extract model construction, also
    // present before this fix), which is sound; the load-bearing check is that
    // it is not wrongly `unsat`.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (assert (= (seq.extract a 0 (seq.len a)) a))
         (assert (seq.contains a (seq.unit 1)))
         (check-sat)",
    );
    assert_ne!(
        result, "unsat",
        "extract-whole identity is satisfiable — must not be refuted"
    );
}
