// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Sequence theory (Seq T) integration tests (#5841).
//!
//! Tests end-to-end QF_SEQ solving: parsing, theory dispatch, model
//! validation bypass, and basic sat/unsat results.

#[test]
fn test_seq_declare_const_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_concat_assoc_symbolic_unsat() {
    // (a++b)++c == a++(b++c) holds for all sequences; its negation is unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (declare-const c (Seq Int))
         (assert (not (= (seq.++ (seq.++ a b) c) (seq.++ a (seq.++ b c)))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_concat_not_commutative_symbolic_not_unsat() {
    // a++b == b++a is NOT valid; its negation is satisfiable (soundness control),
    // so the verdict must never be unsat.
    //
    // #nonstring-seq-failclose: AY's symbolic non-string sequence theory could
    // not produce a model here — the baseline returned `sat` but `(get-value
    // (a b))` errored with "no model value available", a modelless wrong-`sat`.
    // The fail-closed gate now returns a sound `unknown`. Accept sat (with a
    // real model) or unknown; reject only unsat (over-refutation).
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (assert (not (= (seq.++ a b) (seq.++ b a))))
         (check-sat)",
    );
    assert_ne!(result, "unsat");
}

#[test]
fn test_seq_reflexive_equality() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (assert (= s s))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_len_zero() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 0))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_unit_assignment() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 5)))
         (check-sat)",
    );
    assert!(
        matches!(result.as_str(), "sat" | "unknown"),
        "consistent Seq<BitVec> alias chain must not be unsat; got {result}"
    );
}

#[test]
fn test_seq_empty_qualified() {
    // (as seq.empty (Seq Int)) — qualified empty sequence
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (assert (= s (as seq.empty (Seq Int))))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_empty_qualified_bool() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Bool))
         (assert (= s (as seq.empty (Seq Bool))))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_concat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) t)))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_pure_int_in_qf_seq() {
    // Pure integer assertions in QF_SEQ logic should still be sat.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const x Int)
         (assert (= x 5))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// ========== UNSAT tests: exercise actual theory conflict detection ==========

#[test]
fn test_seq_unit_equals_empty_unsat() {
    // seq.unit(x) = seq.empty is always false: a length-1 sequence cannot
    // equal a length-0 sequence. This exercises the SeqSolver's only
    // conflict detection path: check_unit_empty_conflict().
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const x Int)
         (assert (= (seq.unit x) (as seq.empty (Seq Int))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_unit_equals_empty_via_variables() {
    // Transitive unit-empty conflict: s = unit(5) and s = empty implies
    // unit(5) = empty, which is UNSAT. Requires EUF for transitivity
    // reasoning + SeqSolver for unit-empty detection. Fixed by #5951:
    // UfSeqSolver combines EUF + SeqSolver via Nelson-Oppen.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 5)))
         (assert (= s (as seq.empty (Seq Int))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_unit_equals_empty_bool_unsat() {
    // Unit-empty conflict with Bool element type.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const b Bool)
         (assert (= (seq.unit b) (as seq.empty (Seq Bool))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Tests for #5958: seq.len length axiom soundness ==========

#[test]
fn test_seq_len_negative_unsat_5958() {
    // seq.len(s) = -1 is UNSAT: length is always non-negative.
    // Previously returned sat (false-SAT) because seq.len was uninterpreted.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) (- 1)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_unit_len_not_one_unsat_5958() {
    // s = seq.unit(x), seq.len(s) != 1 is UNSAT: unit sequences have length 1.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const x Int)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit x)))
         (assert (not (= (seq.len s) 1)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_empty_len_not_zero_unsat_5958() {
    // s = seq.empty, seq.len(s) != 0 is UNSAT: empty has length 0.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (as seq.empty (Seq Int))))
         (assert (not (= (seq.len s) 0)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_concat_len_decomposition_5958() {
    // seq.len(a) = 2, seq.len(b) = 3, seq.len(seq.++(a, b)) != 5 is UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a (Seq Int))
         (declare-const b (Seq Int))
         (assert (= (seq.len a) 2))
         (assert (= (seq.len b) 3))
         (assert (not (= (seq.len (seq.++ a b)) 5)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_len_sat_positive_5958() {
    // seq.len(s) = 5 should be SAT (valid positive length).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len s) 5))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

// ========== Tests for #5951: N-O equality consumption in UfSeqSolver ==========

#[test]
fn test_seq_unit_injectivity_via_euf_5951() {
    // Unit injectivity through EUF: seq.unit(a) = seq.unit(b) implies a = b.
    // Combined with a != b, this should be unsat.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const a Int)
         (declare-const b Int)
         (assert (= (seq.unit a) (seq.unit b)))
         (assert (not (= a b)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_unit_injectivity_via_variable_5951() {
    // Unit injectivity through shared variable:
    // s = unit(a), s = unit(b), a != b → unsat.
    // Requires EUF transitivity (s = unit(a) ∧ s = unit(b) → unit(a) = unit(b))
    // then Seq unit injectivity (→ a = b), contradicting a != b.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (declare-const a Int)
         (declare-const b Int)
         (assert (= s (seq.unit a)))
         (assert (= s (seq.unit b)))
         (assert (not (= a b)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_transitive_empty_chain_5951() {
    // Three-variable chain: s = t, t = unit(5), s = empty → unsat.
    // EUF derives unit(5) = empty via transitivity through s and t.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s t))
         (assert (= t (seq.unit 5)))
         (assert (= s (as seq.empty (Seq Int))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Tests for #5841: seq.nth axiom injection ==========

#[test]
fn test_seq_nth_unit_element_unsat_5841() {
    // seq.nth(seq.unit(42), 0) = 42 is a tautology.
    // Asserting the negation should be UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (assert (not (= (seq.nth (seq.unit 42) 0) 42)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_unit_variable_unsat_5841() {
    // seq.nth(seq.unit(x), 0) = x for any x.
    // Asserting seq.nth(seq.unit(x), 0) != x should be UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const x Int)
         (assert (not (= (seq.nth (seq.unit x) 0) x)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_unit_sat_5841() {
    // seq.nth(seq.unit(x), 0) = 5 and x = 5 should be SAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const x Int)
         (assert (= x 5))
         (assert (= (seq.nth (seq.unit x) 0) 5))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_nth_unit_conflict_5841() {
    // seq.nth(seq.unit(x), 0) = x. If x = 3 and seq.nth(seq.unit(x), 0) = 7,
    // then 3 = 7, which is UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const x Int)
         (assert (= x 3))
         (assert (= (seq.nth (seq.unit x) 0) 7))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Tests for #5841: seq.nth concat decomposition ==========

#[test]
fn test_seq_nth_concat_first_element_5841() {
    // seq.nth(seq.++(seq.unit(10), seq.unit(20)), 0) = 10.
    // Index 0 < len(seq.unit(10)) = 1, so nth picks from the left.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (assert (not (= (seq.nth (seq.++ (seq.unit 10) (seq.unit 20)) 0) 10)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_concat_second_element_5841() {
    // seq.nth(seq.++(seq.unit(10), seq.unit(20)), 1) = 20.
    // Index 1 >= len(seq.unit(10)) = 1, so nth picks from the right at offset 1-1=0.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (assert (not (= (seq.nth (seq.++ (seq.unit 10) (seq.unit 20)) 1) 20)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_nth_concat_variable_index_5841() {
    // If seq.nth(seq.++(seq.unit(a), seq.unit(b)), 0) = 5 and a = 5, should be SAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a Int)
         (declare-const b Int)
         (assert (= a 5))
         (assert (= (seq.nth (seq.++ (seq.unit a) (seq.unit b)) 0) 5))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_nth_concat_conflict_5841() {
    // seq.nth(seq.++(seq.unit(a), seq.unit(b)), 0) should equal a.
    // If a = 3 but nth(..., 0) = 7, that's UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const a Int)
         (declare-const b Int)
         (assert (= a 3))
         (assert (= (seq.nth (seq.++ (seq.unit a) (seq.unit b)) 0) 7))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

// ========== Tests for axiom-supported Seq ops (#5841, #5985) ==========
// These operations now have axiom reductions (contains, extract, prefixof,
// suffixof, indexof) and return sat/unsat instead of unknown.

#[test]
fn test_seq_contains_sat_5841() {
    // seq.contains now has skolem decomposition axioms.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.contains s t))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_prefixof_sat_5841() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.prefixof s t))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_suffixof_sat_5841() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (seq.suffixof s t))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_extract_sat_5841() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= (seq.len (seq.extract s 0 1)) 1))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_indexof_sat_5841() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (>= (seq.indexof s t 0) 0))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_replace_identity_when_not_found_5841() {
    // replace(s, t, r) = s is SAT when s does not contain t.
    // Previously returned unknown (#5985); now has axioms (#5841).
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (declare-const r (Seq Int))
         (assert (= (seq.replace s t r) s))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

#[test]
fn test_seq_replace_all_returns_unknown_5985() {
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (declare-const r (Seq Int))
         (assert (= (seq.replace_all s t r) s))
         (check-sat)",
    );
    assert_eq!(result, "unknown");
}

#[test]
fn test_seq_supported_ops_still_work_5985() {
    // Verify that supported operations (unit, ++, len, nth, empty) are
    // not blocked by the unsupported ops guard.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (= (seq.len s) 2))
         (assert (= (seq.nth s 0) 1))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

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

// ========== Tests for #7587: bvsle transitivity through seq.nth ==========

#[test]
fn test_seq_bv_bvsle_transitivity_direct_7587() {
    // bvsle(a, b) /\ bvsle(b, c) /\ bvslt(c, a) is UNSAT by transitivity.
    // a <= b <= c < a forms a contradictory cycle.
    // Without transitivity axioms, the Seq solver treats bvsle as uninterpreted
    // and returns false SAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const a (_ BitVec 8))
         (declare-const b (_ BitVec 8))
         (declare-const c (_ BitVec 8))
         (assert (bvsle a b))
         (assert (bvsle b c))
         (assert (bvslt c a))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bv_bvsle_transitivity_through_seq_nth_7587() {
    // s is a Seq(BitVec 8) with 3 elements. The elements satisfy:
    //   bvsle(s[0], s[1]) /\ bvsle(s[1], s[2]) /\ bvslt(s[2], s[0])
    // This is UNSAT by bvsle transitivity: s[0] <= s[1] <= s[2] < s[0].
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 8)))
         (assert (= (seq.len s) 3))
         (assert (bvsle (seq.nth s 0) (seq.nth s 1)))
         (assert (bvsle (seq.nth s 1) (seq.nth s 2)))
         (assert (bvslt (seq.nth s 2) (seq.nth s 0)))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bv_bvsle_negated_conclusion_through_seq_nth_7587() {
    // Exact deductive-checks issue shape: adjacent signed <= constraints should imply
    // the final signed <=, making its negation UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 64)))
         (assert (= (seq.len s) 3))
         (assert (bvsle (seq.nth s 0) (seq.nth s 1)))
         (assert (bvsle (seq.nth s 1) (seq.nth s 2)))
         (assert (not (bvsle (seq.nth s 0) (seq.nth s 2))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bv_bvsle_multi_step_transitivity_through_seq_nth_7587() {
    // Multi-step closure: the solver must propagate across derived conclusions,
    // not just a single two-edge transitivity step.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 8)))
         (assert (= (seq.len s) 4))
         (assert (bvsle (seq.nth s 0) (seq.nth s 1)))
         (assert (bvsle (seq.nth s 1) (seq.nth s 2)))
         (assert (bvsle (seq.nth s 2) (seq.nth s 3)))
         (assert (not (bvsle (seq.nth s 0) (seq.nth s 3))))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bv_bvsle_transitivity_via_variable_alias_7587() {
    // BV variables aliased to seq.nth results: a = s[0], b = s[1], c = s[2].
    // bvsle(a, b) /\ bvsle(b, c) /\ bvslt(c, a) should be UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 8)))
         (declare-const a (_ BitVec 8))
         (declare-const b (_ BitVec 8))
         (declare-const c (_ BitVec 8))
         (assert (= (seq.len s) 3))
         (assert (= a (seq.nth s 0)))
         (assert (= b (seq.nth s 1)))
         (assert (= c (seq.nth s 2)))
         (assert (bvsle a b))
         (assert (bvsle b c))
         (assert (bvslt c a))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bv_bvule_transitivity_7587() {
    // Unsigned version: bvule(a, b) /\ bvule(b, c) /\ bvult(c, a) is UNSAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const a (_ BitVec 8))
         (declare-const b (_ BitVec 8))
         (declare-const c (_ BitVec 8))
         (assert (bvule a b))
         (assert (bvule b c))
         (assert (bvult c a))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bv_bvsle_sat_consistent_7587() {
    // Consistent BV ordering: a <= b <= c should be SAT.
    let result = crate::common::solve(
        "(set-logic QF_SEQ)
         (declare-const a (_ BitVec 8))
         (declare-const b (_ BitVec 8))
         (declare-const c (_ BitVec 8))
         (assert (bvsle a b))
         (assert (bvsle b c))
         (check-sat)",
    );
    assert!(
        matches!(result.as_str(), "sat" | "unknown"),
        "consistent BV ordering must not be unsat; got {result}"
    );
}

// ========== Tests for #7579: Seq<BitVec> ground alias chain ==========

#[test]
fn test_seq_bv_ground_alias_chain_unsat_7579() {
    // Ground alias chain: a = s[0], b = s[0] (same element).
    // bvsle(a, #x05) /\ bvslt(#x05, b) is UNSAT because a = b (both alias
    // to s[0]), so bvsle(a, #x05) /\ bvslt(#x05, a) would require a <= 5 < a.
    // The alias chain (a -> s[0] <- b) must be resolved for the solver to
    // detect the contradiction.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 8)))
         (declare-const a (_ BitVec 8))
         (declare-const b (_ BitVec 8))
         (assert (= (seq.len s) 1))
         (assert (= a (seq.nth s 0)))
         (assert (= b (seq.nth s 0)))
         (assert (bvsle a #x05))
         (assert (bvslt #x05 b))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

#[test]
fn test_seq_bv_ground_alias_chain_sat_7579() {
    // Ground alias chain with consistent constraints: SAT.
    // a = s[0], b = s[1], bvsle(a, b) is satisfiable.
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq (_ BitVec 8)))
         (declare-const a (_ BitVec 8))
         (declare-const b (_ BitVec 8))
         (assert (= (seq.len s) 2))
         (assert (= a (seq.nth s 0)))
         (assert (= b (seq.nth s 1)))
         (assert (bvsle a b))
         (check-sat)",
    );
    assert!(
        matches!(result.as_str(), "sat" | "unknown"),
        "consistent Seq<BitVec> alias chain must not be unsat; got {result}"
    );
}
