// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #probe-qx: contract tests for the QUICKXPLAIN shared-equality minimizer
//! (`quickxplain_shared_equalities`).
//!
//! The minimizer replaces the O(|candidates|) linear forward scan in
//! `probe_needed_shared_equalities`, so it inherits that routine's two
//! load-bearing contracts — the returned subset is drawn ONLY from the
//! candidate order, and it is NEVER empty — plus the acceptance rule that
//! makes the emitted clause valid by construction: a subset is returned only
//! after a probe check actually re-derives UNSAT from the conflict literals
//! plus exactly that subset, never by inference from the recursion.
//!
//! These call the minimizer directly rather than through `AY_LIA_PROBE_QX`:
//! the env gate is process-cached (`OnceLock`), so a test that set it would
//! leak into every other test in the binary.

use super::*;
use crate::check::QxOutcome;
use ay_core::{TheoryLit, TheorySolver};

/// `n` fresh `(p_i, q_i)` Int variable pairs — shared-equality operands that
/// constrain nothing in the conflict under test.
fn fresh_pairs(terms: &mut TermStore, n: usize) -> Vec<(TermId, TermId)> {
    (0..n)
        .map(|i| {
            (
                terms.mk_var(format!("p{i}"), Sort::Int),
                terms.mk_var(format!("q{i}"), Sort::Int),
            )
        })
        .collect()
}

/// Contract 1 (subset of the candidate order) and contract 2 (never empty), on
/// the shape the probe can actually refute: conflict literals that are
/// infeasible on their OWN.
///
/// Contract 2 is the load-bearing one here. A clause built from the conflict's
/// own atoms alone need not be falsified by the current model (those atoms can
/// be congruence-derived equalities the SAT solver cannot flip), so at least
/// one SAT-visible reason literal must survive minimization or the split loop
/// makes no progress. The recursion bottoms out at a singleton — never at ∅ —
/// because the root call carries no Δ.
#[test]
fn test_quickxplain_keeps_a_nonempty_subset_of_the_candidate_order() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let le_x0 = terms.mk_le(x, zero);
    let ge_x1 = terms.mk_ge(x, one);
    let reason = terms.mk_eq(x, zero);
    let pairs = fresh_pairs(&mut terms, 4);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(le_x0, true);
    solver.assert_literal(ge_x1, true);
    for (a, b) in pairs {
        solver.assert_shared_equality(a, b, &[TheoryLit::new(reason, true)]);
    }

    let literals = vec![TheoryLit::new(le_x0, true), TheoryLit::new(ge_x1, true)];
    let order: Vec<usize> = (0..solver.shared_equalities.len()).collect();
    let mut checks = 0u64;
    match solver.quickxplain_shared_equalities(&literals, &order, &mut checks) {
        QxOutcome::Proved(subset) => {
            assert!(!subset.is_empty(), "contract 2: the subset is never empty");
            assert!(
                subset.iter().all(|i| order.contains(i)),
                "contract 1: the subset is drawn only from the candidate order"
            );
            assert!(
                checks <= order.len() as u64,
                "the minimizer must not out-spend the scan it replaces: {checks}"
            );
        }
        _ => panic!("literals alone are infeasible, so any subset refutes them"),
    }
}

/// A definite-Sat full candidate set PROVES that no subset can refute the
/// literals (a model of `literals + ALL` models `literals + ANY`): the
/// minimizer must take the exact fast-fail at one check instead of scanning
/// every candidate.
#[test]
fn test_quickxplain_refutes_a_satisfiable_candidate_set_in_one_check() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let le_x0 = terms.mk_le(x, zero);
    let reason = terms.mk_eq(x, zero);
    let pairs = fresh_pairs(&mut terms, 6);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(le_x0, true);
    for (a, b) in pairs {
        solver.assert_shared_equality(a, b, &[TheoryLit::new(reason, true)]);
    }

    let literals = vec![TheoryLit::new(le_x0, true)];
    let order: Vec<usize> = (0..solver.shared_equalities.len()).collect();
    let mut checks = 0u64;
    assert!(
        matches!(
            solver.quickxplain_shared_equalities(&literals, &order, &mut checks),
            QxOutcome::Refuted
        ),
        "a model of literals + ALL candidates models every subset"
    );
    assert_eq!(checks, 1, "the fast-fail costs exactly one check");
}

/// The acceptance rule from the other side: an UNDECIDED full-set verdict is
/// never read as a proof. `x + y = 1` with the shared equality `x = y` is
/// integer-infeasible, but the probe answers `NeedSplit` rather than proving
/// it — so the minimizer must hand back `Undecided` (the caller then runs the
/// forward scan), never a subset it has not seen refuted.
#[test]
fn test_quickxplain_never_proves_from_an_undecided_batch() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let sum = terms.mk_add(vec![x, y]);
    let le = terms.mk_le(sum, one);
    let ge = terms.mk_ge(sum, one);
    let reason = terms.mk_eq(x, y);
    let pairs = fresh_pairs(&mut terms, 7);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(le, true);
    solver.assert_literal(ge, true);
    for (a, b) in pairs {
        solver.assert_shared_equality(a, b, &[TheoryLit::new(reason, true)]);
    }
    solver.assert_shared_equality(x, y, &[TheoryLit::new(reason, true)]);

    let literals = vec![TheoryLit::new(le, true), TheoryLit::new(ge, true)];
    let order: Vec<usize> = (0..solver.shared_equalities.len()).collect();
    let mut checks = 0u64;
    assert!(
        matches!(
            solver.quickxplain_shared_equalities(&literals, &order, &mut checks),
            QxOutcome::Undecided
        ),
        "an undecided batch decides nothing — the scan must get the attempt"
    );
    assert_eq!(checks, 1, "an undecided batch costs exactly one check");
}
