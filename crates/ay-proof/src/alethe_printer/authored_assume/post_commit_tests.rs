// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A printed-equivalence bridge re-planned against the view its commit
//! produces ([`super`]): the re-plan that keeps a bridge, the decline that
//! drops a bridge no schema re-derives, and the antecedent no schema ever
//! relates.

use super::super::spelling_bridge_tests::{assert_valid, overrides};
use super::*;
use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::{AletheRule, Symbol, TermStore};
use num_bigint::BigInt;

/// The error the emitter raised for a bridge planned before the commit
/// changed what it reads, before `post_commit` existed.
const STALE: &str = "planned authored assume equivalence no longer has a checked derivation";

/// `(=> A (<= x 3))`, `G`, `(not (<= x 3))` as the producer hands them over,
/// with `A` the implication's authored antecedent and `G` the guard row's
/// authored spelling: the implication is the canonical
/// `(or (<= x 3) (not (<= 0 y)))` and the guard is the canonical `(<= 0 y)`.
fn implication_refutation(
    antecedent_surface: &str,
    guard_surface: &str,
) -> (TermStore, Proof, HashMap<TermId, String>, Vec<TermId>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let guard = terms.mk_app(Symbol::named("<="), [zero, y], Sort::Bool);
    let bound = terms.mk_app(Symbol::named("<="), [x, three], Sort::Bool);
    let not_guard = terms.mk_not_raw(guard);
    let not_bound = terms.mk_not_raw(bound);
    let implication = terms.mk_app(Symbol::named("or"), [bound, not_guard], Sort::Bool);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(implication, None);
    let guard_holds = proof.add_assume(guard, None);
    let clause = proof.add_rule_step(
        AletheRule::Or,
        vec![bound, not_guard],
        vec![assumed],
        vec![],
    );
    let bounded = proof.add_resolution(vec![bound], guard, guard_holds, clause);
    let refuted = proof.add_assume(not_bound, None);
    proof.add_resolution(vec![], bound, bounded, refuted);
    let table = overrides(&[
        (implication, &format!("(=> {antecedent_surface} (<= x 3))")),
        (guard, guard_surface),
    ]);
    (terms, proof, table, vec![implication, guard, not_bound])
}

fn problem(antecedent_surface: &str, guard_surface: &str) -> String {
    format!(
        "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n\
         (assert (=> {antecedent_surface} (<= x 3)))\n(assert {guard_surface})\n\
         (assert (not (<= x 3)))\n(check-sat)\n"
    )
}

#[test]
fn a_printed_equivalence_is_replanned_against_the_view_its_commit_produces() {
    let (terms, proof, table, assertions) = implication_refutation("(>= y 0)", "(>= y 0)");
    let document = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &assertions,
        Some(&table),
    )
    .expect("the implication bridge survives the commit that confines (<= 0 y)");
    assert!(
        document.starts_with("(assume t0.a (=> (>= y 0) (<= x 3)))\n"),
        "{document}"
    );
    assert!(
        document.contains("(step t0 (cl (or (<= x 3) (not (<= 0 y)))) :rule resolution"),
        "{document}"
    );
    assert!(document.contains(":rule comp_simplify"), "{document}");
    assert_valid(
        "replanned_implication",
        &problem("(>= y 0)", "(>= y 0)"),
        &document,
    );
}

/// NEGATIVE TWIN: an antecedent no schema relates to the canonical guard
/// (`(>= y 1)` is not `(<= 0 y)`; with it the three assertions are
/// satisfiable at `y = 0`) is never bridged, before or after the commit. The
/// printed implication then cannot meet the `or` step over the canonical
/// disjunction, and the export is refused.
#[test]
fn a_replanned_equivalence_never_bridges_an_unrelated_antecedent() {
    let (terms, proof, table, assertions) = implication_refutation("(>= y 1)", "(>= y 0)");
    let exported = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &assertions,
        Some(&table),
    );
    let error = exported
        .expect_err("an unrelated antecedent has no bridge, so the printed premises cannot meet")
        .to_string();
    assert!(error.contains("printed implication literals"), "{error}");
}

/// The DECLINE path. `(>= y (- 0))` is planned onto the pre-commit rendering
/// `(or (<= x 3) (not (>= y (- 0))))`, the guard row then confines `(<= 0 y)`,
/// and no schema relates `(>= y (- 0))` to `(<= 0 y)` (the comparison schema
/// reads the operands verbatim). The stale plan is dropped, the implication
/// keeps its authored spelling, and the `or` step's validator refuses the
/// export, as it would with no bridge. Kept, the plan would have reached the
/// emitter and failed there with [`STALE`].
#[test]
fn a_stale_equivalence_no_schema_rederives_is_declined() {
    let (terms, proof, table, assertions) = implication_refutation("(>= y (- 0))", "(>= y (- 0))");
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &assertions,
        Some(&table),
    )
    .expect_err("an implication no schema bridges after the commit stays unbridged")
    .to_string();
    assert!(!error.contains(STALE), "{error}");
    assert!(error.contains("printed implication literals"), "{error}");
}

/// A bridge the commit leaves derivable is kept as planned: when the guard row
/// keeps its authored spelling document-wide (no bridge confines
/// `(or (>= y 0) false)` or `(not (< y 0))`), the implication's bridge onto
/// the rendering `(or (<= x 3) (not G))` still holds after the commit, the
/// re-check finds nothing stale, and the document checks.
#[test]
fn a_bridge_the_commit_leaves_derivable_is_kept_as_planned() {
    for antecedent in ["(or (>= y 0) false)", "(not (< y 0))"] {
        let (terms, proof, table, assertions) = implication_refutation(antecedent, antecedent);
        let document = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &assertions,
            Some(&table),
        )
        .unwrap_or_else(|error| panic!("{antecedent}: {error}"));
        assert!(
            document.contains(&format!(
                "(step t0 (cl (or (<= x 3) (not {antecedent}))) :rule resolution"
            )),
            "{document}"
        );
        assert!(
            document.contains(&format!("(assume t1 {antecedent})")),
            "{document}"
        );
        assert_valid("kept_bridge", &problem(antecedent, antecedent), &document);
    }
}
