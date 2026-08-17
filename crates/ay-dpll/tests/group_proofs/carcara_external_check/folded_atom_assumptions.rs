// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{extract_assume_terms, solve_unsat_and_get_proof};
use ntest::timeout;
use std::fmt::Write as _;

/// The problem scope a bit-vector identity refutation is checked against.
///
/// Replaying AY's own printed assumptions as the problem scope isolates the
/// claim under test: whether the DERIVATION is externally re-derivable. It
/// cannot hide a bad derivation because every non-`assume` step still has to
/// check, and the assumptions are taken verbatim from the published proof.
/// The regression below separately requires those assumptions to retain the
/// authored source spelling when an application folds to an atom.
pub(super) fn published_assumption_scope(declarations: &str, proof: &str) -> String {
    let assertions =
        extract_assume_terms(proof)
            .into_iter()
            .fold(String::new(), |mut assertions, term| {
                writeln!(assertions, "(assert {term})").expect("writing to a String cannot fail");
                assertions
            });
    format!("(set-logic QF_BV)\n{declarations}{assertions}(check-sat)\n")
}

/// The exported `assume` steps must print the problem's own assertions —
/// carcara matches every `assume` against the source problem BEFORE any
/// derivation is considered, so a re-spelled premise invalidates the whole
/// document however good the proof after it is.
///
/// Regression for the folded-subterm surface-override defect
/// (`override_would_hijack_atom`): elaboration folds `(bvand x x)` -> `x`
/// (and `(bvmul x #x…0)` -> `#x…0`), and the subterm override collector used
/// to record the authored spelling AGAINST THE FOLD RESULT's TermId. Keyed
/// by the atom, the entry re-spelled every occurrence of that atom at print
/// time, and the exported assume came out as
/// `(not (= (bvand (bvand x x) (bvand x x)) (bvand x x)))` — no longer any
/// assertion of the problem. Runs without carcara: the faithfulness claim is
/// about AY's own printed bytes.
#[test]
#[timeout(120_000)]
fn exported_assume_steps_print_the_problem_assertion_itself() {
    // Fully lowered family (bvand idempotency, no hole on the wire).
    let proof = solve_unsat_and_get_proof(
        "(set-logic QF_BV)\n\
         (declare-const x (_ BitVec 8))\n\
         (assert (not (= (bvand x x) x)))\n\
         (check-sat)\n",
        "faithful_assume_bvand_idempotent",
    );
    assert_eq!(
        extract_assume_terms(&proof),
        vec!["(not (= (bvand x x) x))".to_string()],
        "the assume must be the problem's own assertion, never a re-spelled \
         fold image:\n{proof}"
    );

    // Honest-hole family (bvmul by zero, width 32): the lemma legitimately
    // stays a `hole`, but the assume must still be faithful — the folded
    // constant's TermId must not carry the `(bvmul x …)` spelling into
    // either side of the printed equality.
    let proof = solve_unsat_and_get_proof(
        "(set-logic QF_BV)\n\
         (declare-const x (_ BitVec 32))\n\
         (assert (not (= (bvmul x #x00000000) #x00000000)))\n\
         (check-sat)\n",
        "faithful_assume_bvmul_zero",
    );
    let assumes = extract_assume_terms(&proof);
    assert_eq!(
        assumes.len(),
        1,
        "one problem assertion, one assume:\n{proof}"
    );
    assert!(
        !assumes[0].contains("(bvmul x (bvmul"),
        "the folded zero constant must not re-spell as the bvmul it was \
         folded from:\n{proof}"
    );
    assert!(
        assumes[0].starts_with("(not (= (bvmul x "),
        "the assume must keep the authored equality shape:\n{proof}"
    );
}
