// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored equality whose operands elaboration SWAPPED and one of which
//! names a nullary array `define-fun`: `benchmarks/smt/QF_AX/swap_two_reads.smt2`.
//!
//! `(assert (not (= (select a2 i) (select a j))))` interns as
//! `(not (= (select a j) (select (store (store a i ..) j ..) i)))`. Pinned
//! carcara 1.1.0 (git 9a352ee), run without `--apply-function-defs`, holds
//! `a1`/`a2` as declared constants with the premises `(= a1 ..)`/`(= a2 ..)`,
//! so the document must `assume` the authored row and reach the expansion
//! through those premises. The authored-assume definition schema had no arm
//! for a swap combined with a macro operand, so the bridge declined, the
//! authored spelling rode the root document-wide, and the export was REFUSED
//! at the closing resolution ("the printed premises do not eliminate the
//! printed resolution pivot, starting at `(= (select a j) ..)`"). The
//! read-over-write at the other index was never the gap: the ROW lemma
//! already prints `arrays_row` citing `(not (= j i))`, derived with
//! `not_symm` from the assumed index disequality.

use super::{
    carcara_verdict_without_allowances, parse, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict, Executor,
};
use ntest::timeout;

const DECLARATIONS: &str = "(set-logic QF_AX)\n(declare-sort Index 0)\n\
    (declare-sort Elem 0)\n(declare-fun a () (Array Index Elem))\n\
    (declare-fun i () Index)\n(declare-fun j () Index)\n(assert (not (= i j)))\n\
    (define-fun a1 () (Array Index Elem) (store a i (select a j)))\n\
    (define-fun a2 () (Array Index Elem) (store a1 j (select a i)))\n";

fn assumed_terms(proof: &str) -> Vec<&str> {
    proof
        .lines()
        .filter_map(|line| line.strip_prefix("(assume "))
        .filter_map(|rest| rest.split_once(' '))
        .filter_map(|(_, term)| term.trim_end().strip_suffix(')'))
        .collect()
}

#[test]
#[timeout(120_000)]
fn swap_two_reads_is_bridged_through_both_definitions_and_checks_valid() {
    let label = "swap_two_reads";
    let authored = "(not (= (select a2 i) (select a j)))";
    let problem = format!("{DECLARATIONS}(assert {authored})\n(check-sat)\n");
    let proof = solve_unsat_and_get_proof(&problem, label);
    for forbidden in [":rule hole", ":rule trust"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    let assumed = assumed_terms(&proof);
    for premise in [
        authored,
        "(not (= i j))",
        "(= a2 (store a1 j (select a i)))",
        "(= a1 (store a i (select a j)))",
    ] {
        assert!(assumed.contains(&premise), "{label}: {premise}:\n{proof}");
    }
    assert!(
        !assumed.iter().any(|term| term.contains("(store (store a")),
        "{label}: the expanded row is no premise of the problem:\n{proof}"
    );
    // The read at the other index is `arrays_row` citing the index
    // disequality in the store-then-read orientation the rule requires.
    let row = proof
        .lines()
        .find(|line| line.contains(":rule arrays_row"))
        .unwrap_or_else(|| panic!("{label}: no arrays_row step:\n{proof}"));
    let cited = row
        .rsplit_once(":premises (")
        .and_then(|(_, rest)| rest.strip_suffix("))"))
        .unwrap_or_else(|| panic!("{label}: arrays_row cites no premise: {row}"));
    assert!(
        proof.contains(&format!("(step {cited} (cl (not (= j i))) :rule not_symm")),
        "{label}: arrays_row must cite (not (= j i)):\n{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, &problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must re-derive every step:\n{proof}"
        );
    }
}

/// SAT twin: the swapped row reads the OTHER original cell, `a2[i] = a[j]`
/// need not equal `a[i]`, so no refutation (and no bridge) may exist.
#[test]
#[timeout(120_000)]
fn the_satisfiable_swap_twin_stays_sat() {
    let problem =
        format!("{DECLARATIONS}(assert (not (= (select a2 i) (select a i))))\n(check-sat)\n");
    let script = format!("(set-option :produce-proofs true)\n{problem}");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(&script).expect("parse"))
        .expect("execute");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "the satisfiable swap twin must stay SAT, got {outputs:?}"
    );
}
