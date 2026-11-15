// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The exact-division sweep memo's bookkeeping: what a signature is, which
//! attempts a failed sweep reaches, where a decline stands, and how memos
//! are installed and shared.

use super::*;

const ENVELOPE: u64 = 7;

/// `(bvult (bvurem x k) k)` over a fresh `width`-bit `x` in `terms`, after
/// `padding` unrelated constants (which move every `TermId` but name no
/// variable).
fn in_range(terms: &mut TermStore, width: u32, k: u64, padding: u64) -> TermId {
    for value in 0..padding {
        let _unrelated = terms.mk_bitvec(value.into(), 8);
    }
    let x = terms.mk_var("dividend", Sort::bitvec(width));
    let divisor = terms.mk_bitvec(k.into(), width);
    let remainder = terms.mk_app(Symbol::named("bvurem"), [x, divisor], Sort::bitvec(width));
    terms.mk_app(Symbol::named("bvult"), [remainder, divisor], Sort::Bool)
}

/// An exact-division attempt at `clause` whose sweep ran to the end of its
/// envelope without closing.
fn fail_sweep(terms: &TermStore, clause: &[TermId]) {
    exact_division(terms, clause, Some(true), ENVELOPE, || {
        assert!(!skips_sweep(), "a first sweep has its whole envelope");
        assert!(remembers_sweep());
        sweep_failed();
    });
}

/// Whether an exact-division attempt at `clause` read as `hypotheses` would
/// skip its sweep.
fn would_skip(terms: &TermStore, clause: &[TermId], hypotheses: Option<bool>) -> bool {
    exact_division(terms, clause, hypotheses, ENVELOPE, skips_sweep)
}

#[test]
fn nothing_is_remembered_or_withheld_without_an_installed_memo() {
    let mut terms = TermStore::new();
    let clause = vec![in_range(&mut terms, 32, 1_000_003, 0)];
    fail_sweep_without_memo(&terms, &clause);
    assert!(!would_skip(&terms, &clause, Some(true)));
    assert!(!declined(&terms, &clause, ENVELOPE));
    record_decline(&terms, &clause, ENVELOPE);
    assert!(!declined(&terms, &clause, ENVELOPE));
}

fn fail_sweep_without_memo(terms: &TermStore, clause: &[TermId]) {
    exact_division(terms, clause, Some(true), ENVELOPE, || {
        assert!(!remembers_sweep(), "no memo, nothing to remember");
        sweep_failed();
    });
}

#[test]
fn another_spelling_of_a_failed_divider_obligation_skips_only_its_sweep() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let negated = terms.mk_not_raw(atom);
    let respelled = vec![terms.mk_not_raw(negated)];
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    fail_sweep(&terms, &[atom]);
    assert_eq!(memo.failed_signatures(), 1);
    let ((), withheld) = deciding(|| assert!(would_skip(&terms, &respelled, Some(true))));
    assert!(withheld, "the decision is told its sweep was withheld");
    assert_eq!(memo.skipped_sweeps(), 1);
    // Outside an exact-division attempt, and for a case reading or another
    // reading of the clause, nothing is withheld.
    assert!(!skips_sweep());
    assert!(!would_skip(&terms, &respelled, None));
    assert!(!would_skip(&terms, &respelled, Some(false)));
    let ((), withheld) = deciding(|| ());
    assert!(!withheld, "each decision starts with nothing withheld");
}

#[test]
fn another_divider_or_another_envelope_is_another_obligation() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let other_divisor = in_range(&mut terms, 64, 1_000_033, 0);
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    fail_sweep(&terms, &[atom]);
    assert!(!would_skip(&terms, &[other_divisor], Some(true)));
    assert!(!would_skip(&terms, &[atom, other_divisor], Some(true)));
    let other_envelope = exact_division(&terms, &[atom], Some(true), ENVELOPE + 1, skips_sweep);
    assert!(!other_envelope);
    assert_eq!(memo.skipped_sweeps(), 0);
}

#[test]
fn a_signature_names_no_term_id_so_it_holds_in_a_renumbered_or_cloned_store() {
    let mut first = TermStore::new();
    let atom = in_range(&mut first, 64, 1_000_003, 0);
    let mut renumbered = TermStore::new();
    let moved = in_range(&mut renumbered, 64, 1_000_003, 5);
    assert_ne!(atom, moved);
    let cloned = first.clone();
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    fail_sweep(&first, &[atom]);
    assert!(would_skip(&renumbered, &[moved], Some(true)));
    assert!(would_skip(&cloned, &[atom], Some(true)));
}

#[test]
fn a_clause_without_a_division_has_no_signature() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("plain", Sort::bitvec(8));
    let equality = terms.mk_app(Symbol::named("="), [x, x], Sort::Bool);
    assert_eq!(division_signature(&terms, &[equality]), None);
    let atom = in_range(&mut terms, 8, 7, 0);
    assert_eq!(
        division_signature(&terms, &[equality, atom]).map(|divisions| divisions.len()),
        Some(1)
    );
}

#[test]
fn a_decline_stands_only_for_the_exact_clause_in_its_store_while_its_memo_is_installed() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let negated = terms.mk_not_raw(atom);
    let respelled = terms.mk_not_raw(negated);
    let mut memo = ExactDivisionSweepMemo::new();
    {
        let _build = memo.begin_build();
        record_decline(&terms, &[atom], ENVELOPE);
        assert!(declined(&terms, &[atom], ENVELOPE));
        assert!(
            !declined(&terms, &[respelled], ENVELOPE),
            "another spelling still makes its own monolithic attempt"
        );
        assert!(
            !declined(&terms.clone(), &[atom], ENVELOPE),
            "a clone is another store"
        );
        let _more = in_range(&mut terms, 16, 3, 0);
        assert!(
            declined(&terms, &[atom], ENVELOPE),
            "growth keeps every id it names"
        );
    }
    assert!(
        !declined(&terms, &[atom], ENVELOPE),
        "uninstalled with its build"
    );
    let _next = memo.begin_build();
    assert!(
        !declined(&terms, &[atom], ENVELOPE),
        "the next build starts afresh"
    );
}

#[test]
fn a_rollback_retires_a_decline() {
    let mut terms = TermStore::new();
    let checkpoint = terms.rollback_checkpoint();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    record_decline(&terms, &[atom], ENVELOPE);
    terms.rollback_to(checkpoint);
    let again = in_range(&mut terms, 64, 1_000_003, 0);
    assert_eq!(again, atom, "the reclaimed id, minted again");
    assert!(
        !declined(&terms, &[again], ENVELOPE),
        "a rollback retires the stamp"
    );
}

#[test]
fn each_build_starts_its_own_memo_afresh_and_a_derived_executor_carries_on() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let mut memo = ExactDivisionSweepMemo::new();
    {
        let _build = memo.begin_build();
        fail_sweep(&terms, &[atom]);
    }
    let mut derived = memo.share_with_derived();
    {
        let _nested = derived.begin_build();
        assert!(
            would_skip(&terms, &[atom], Some(true)),
            "a derived build carries on"
        );
        let mut deeper = derived.share_with_derived();
        let _deeper = deeper.begin_build();
        assert!(would_skip(&terms, &[atom], Some(true)));
    }
    assert_eq!(
        memo.skipped_sweeps(),
        2,
        "the derived builds share the parent's memo"
    );
    let _next = memo.begin_build();
    assert_eq!(
        memo.failed_signatures(),
        0,
        "the parent's next build starts afresh"
    );
    assert!(!would_skip(&terms, &[atom], Some(true)));
}

#[test]
fn a_build_inside_a_build_of_the_same_memo_does_not_start_it_afresh() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let mut memo = ExactDivisionSweepMemo::new();
    let _outer = memo.begin_build();
    fail_sweep(&terms, &[atom]);
    let _inner = memo.begin_build();
    assert!(would_skip(&terms, &[atom], Some(true)));
}

#[test]
fn a_scope_reinstates_what_it_displaced() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let mut outer = ExactDivisionSweepMemo::new();
    let _outer = outer.begin_build();
    fail_sweep(&terms, &[atom]);
    {
        let mut other = ExactDivisionSweepMemo::new();
        let _other = other.begin_build();
        assert!(
            !would_skip(&terms, &[atom], Some(true)),
            "another executor's build"
        );
    }
    assert!(would_skip(&terms, &[atom], Some(true)));
}

#[test]
fn a_withheld_sweep_reaches_the_enclosing_decision_even_through_an_unwind() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 64, 1_000_003, 0);
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    fail_sweep(&terms, &[atom]);
    let ((), outer) = deciding(|| {
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            deciding(|| {
                assert!(would_skip(&terms, &[atom], Some(true)));
                panic!("an inner decision unwinds");
            })
        }));
        assert!(caught.is_err());
    });
    assert!(
        outer,
        "the inner decision's withheld sweep is the outer one's too"
    );
}

#[test]
fn a_clause_decline_is_owned_by_its_counted_envelope() {
    let mut terms = TermStore::new();
    let atom = in_range(&mut terms, 32, 1_000_003, 0);
    let mut memo = ExactDivisionSweepMemo::new();
    let _build = memo.begin_build();
    record_decline(&terms, &[atom], ENVELOPE);
    assert!(declined(&terms, &[atom], ENVELOPE));
    assert!(!declined(&terms, &[atom], ENVELOPE + 1));
    record_decline(&terms, &[atom], ENVELOPE + 1);
    assert!(declined(&terms, &[atom], ENVELOPE + 1));
    assert!(declined(&terms, &[atom], ENVELOPE));
}
