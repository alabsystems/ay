// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict decisions made with no exact divider
//! (`exact_division_sweeps::without_exact_division`): a lemma the abstracted
//! attempt cannot refute is refused without the exact-division attempt, and
//! that refusal is remembered nowhere, so the clause is decided afresh, with
//! its exact divider and its whole sweep, as soon as the probe ends.

#![cfg(test)]

use super::*;
use crate::checker::bv_bitblast::producer_limits::strict_producer_envelope_id;
use crate::exact_division_sweeps::{self, without_exact_division, ExactDivisionSweepMemo};

/// `(bvurem x 1000003)` and its divisor over a fresh `width`-bit `x`.
fn remainder(terms: &mut TermStore, width: u32) -> (TermId, TermId) {
    let x = terms.mk_var("withheld-division-dividend", Sort::bitvec(width));
    let divisor = terms.mk_bitvec(1_000_003.into(), width);
    let remainder = terms.mk_app(Symbol::named("bvurem"), [x, divisor], Sort::bitvec(width));
    (remainder, divisor)
}

/// `(bvult (bvurem x 1000003) 1000003)`: the abstracted attempt cannot refute
/// its negation; the exact divider can (`exact_division_memo.rs`).
fn in_range(width: u32) -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let (remainder, divisor) = remainder(&mut terms, width);
    let atom = terms.mk_app(Symbol::named("bvult"), [remainder, divisor], Sort::Bool);
    (terms, vec![atom])
}

fn refused(terms: &TermStore, clause: &[TermId]) -> bool {
    terms
        .strict_bv_semantics_refusal(strict_producer_envelope_id(), clause)
        .is_some()
}

#[test]
fn only_the_probe_withholds_an_exact_division_attempt_and_its_decision_is_told() {
    let ((), withheld) = exact_division_sweeps::deciding(|| {
        assert!(!exact_division_sweeps::withholds_exact_division());
    });
    assert!(!withheld);
    let ((), withheld) = exact_division_sweeps::deciding(|| {
        without_exact_division(|| {
            without_exact_division(|| ());
            assert!(
                exact_division_sweeps::withholds_exact_division(),
                "a nested probe ends without ending the outer one"
            );
        });
    });
    assert!(withheld);
    let ((), withheld) = exact_division_sweeps::deciding(|| {
        assert!(!exact_division_sweeps::withholds_exact_division());
    });
    assert!(!withheld, "the probe ended with its scope");
}

/// With a stand-in producer that withholds, as `attempt` does under the
/// probe: neither the store nor the build's memo remembers the refusal.
#[test]
fn a_probes_refusal_is_neither_the_stores_nor_the_builds_decline() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("withheld-division-identity", Sort::bitvec(16));
    let clause = vec![terms.mk_app(Symbol::named("="), [x, x], Sort::Bool)];
    let mut entered = 0;
    let mut decide = |outcome: fn() -> Result<(), ProofProducingFailure>| {
        semantic_control::run(&mut |_, _| true, |poll| {
            validate_bv_bitblast_semantics_with_fallback(&terms, ProofId(0), &clause, poll, |_| {
                entered += 1;
                outcome()
            })
        })
    };
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    let probed = without_exact_division(|| {
        decide(|| {
            assert!(exact_division_sweeps::withholds_exact_division());
            Err(ProofProducingFailure::Rejected("abstracted".to_owned()))
        })
    });
    assert!(matches!(
        probed,
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    assert_eq!(decide(|| Ok(())), Ok(()), "decided afresh after the probe");
    assert_eq!(entered, 2);
    assert!(!refused(&terms, &clause));
    assert!(!exact_division_sweeps::declined(
        &terms,
        &clause,
        strict_producer_envelope_id()
    ));
}

/// The real producer on the 32-bit obligation, whose exact-division sweep
/// closes: under the probe it is refused with no exact attempt (no sweep
/// fails, none is withheld on the memo's word), and the same clause is then
/// accepted with the exact divider, so the refusal outlived nothing.
#[test]
fn the_probe_refuses_a_divider_obligation_without_its_exact_attempt_and_forgets_it() {
    let (terms, clause) = in_range(32);
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    let probed = without_exact_division(|| Lane::BitBlast.run(&terms, &clause, &mut |_, _| true));
    assert!(
        matches!(probed, Err(ProofCheckError::InvalidTheoryLemma { .. })),
        "refused without the exact divider: {probed:?}"
    );
    assert_eq!(memo.failed_signatures(), 0, "no exact attempt swept");
    assert_eq!(memo.skipped_sweeps(), 0);
    assert!(!refused(&terms, &clause));
    assert!(!exact_division_sweeps::declined(
        &terms,
        &clause,
        strict_producer_envelope_id()
    ));
    Lane::BitBlast
        .run(&terms, &clause, &mut |_, _| true)
        .expect("decided afresh: the exact-division sweep closes");
    assert!(terms.strict_bv_semantics_validated(&clause));
}

/// The BvUremBound joint over the 40-bit obligation (`guarded/urem_bound.rs`
/// in `ay-dpll`): the theorem `d = 0 or x % d < d` makes the abstracted
/// attempt enough, so the probe accepts it, and no sweep is spent.
#[test]
fn the_probe_accepts_a_remainder_obligation_the_bound_theorem_closes() {
    let mut terms = TermStore::new();
    let (remainder, divisor) = remainder(&mut terms, 40);
    let in_range = terms.mk_app(Symbol::named("bvult"), [remainder, divisor], Sort::Bool);
    let obligation = terms.mk_not_raw(in_range);
    let zero = terms.mk_bitvec(0.into(), 40);
    let is_zero = terms.mk_app(Symbol::named("="), [divisor, zero], Sort::Bool);
    let bound = terms.mk_app(Symbol::named("or"), [is_zero, in_range], Sort::Bool);
    let joint = terms.mk_app(Symbol::named("and"), [obligation, bound], Sort::Bool);
    let clause = vec![terms.mk_not_raw(joint)];
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    without_exact_division(|| Lane::BitBlast.run(&terms, &clause, &mut |_, _| true))
        .expect("the bound closes the joint with the division abstracted");
    assert_eq!(memo.failed_signatures(), 0);
    assert_eq!(memo.skipped_sweeps(), 0);
}
