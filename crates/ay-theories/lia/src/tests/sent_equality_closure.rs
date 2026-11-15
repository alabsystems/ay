// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #tight-bound-star-dedup: Phase 3 (implied difference equalities) must not
//! re-send a pair the already-sent equalities join. The anchor-star
//! tight-bound emission sends `n - 1` edges per same-value group and records
//! only those, so a literal lookup of the sent set re-sent every spoke pair
//! the star had joined (the store-chain witnesses of
//! `array_repair_completeness_2026_09_24` turned `unknown`).

use super::*;
use crate::sent_equality_closure::SentEqualityClosure;

fn pair(a: TermId, b: TermId) -> (TermId, TermId) {
    if a.0 < b.0 {
        (a, b)
    } else {
        (b, a)
    }
}

/// `a <= c <= a` entails `a = c` (Phase 3); `seeds` are pairs recorded as
/// already sent (as a fresh instance's replayed star edges are). Returns the
/// round's propagated pairs.
fn phase3_round(seeds: &[(usize, usize)]) -> (Vec<(TermId, TermId)>, [TermId; 3]) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let vars = [a, b, c];
    let atoms = [terms.mk_le(a, c), terms.mk_le(c, a), terms.mk_le(a, b)];
    let mut solver = LiaSolver::new(&terms);
    for atom in atoms {
        solver.assert_literal(atom, true);
    }
    for &(lhs, rhs) in seeds {
        solver.seed_propagated_equality_pair(vars[lhs], vars[rhs]);
    }
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let result = solver.propagate_equalities();
    assert!(result.conflict.is_none(), "no conflict expected");
    let pairs = result
        .equalities
        .iter()
        .map(|eq| pair(eq.lhs, eq.rhs))
        .collect();
    (pairs, vars)
}

/// The sent pairs `a = b` and `b = c` (an anchor star on `b`) already join
/// `a` and `c`: Phase 3 must not send the implied `a = c` again.
#[test]
fn an_implied_difference_the_sent_pairs_join_is_not_resent() {
    let (pairs, [a, _, c]) = phase3_round(&[(0, 1), (1, 2)]);
    assert!(
        !pairs.contains(&pair(a, c)),
        "`a = c` is joined by the sent star edges: {pairs:?}"
    );
}

/// Negative twin: with nothing sent, the entailed `a = c` is still sent.
#[test]
fn an_implied_difference_nothing_joins_is_sent() {
    let (pairs, [a, _, c]) = phase3_round(&[]);
    assert!(
        pairs.contains(&pair(a, c)),
        "the entailed `a = c` must be sent: {pairs:?}"
    );
}

/// Negative twin: a sent pair touching only one end joins nothing.
#[test]
fn a_sent_pair_on_one_end_does_not_join_the_other() {
    let (pairs, [a, _, c]) = phase3_round(&[(0, 1)]);
    assert!(
        pairs.contains(&pair(a, c)),
        "`a = b` alone does not join `c`: {pairs:?}"
    );
}

#[test]
fn closure_joins_chains_and_nothing_else() {
    let ids: Vec<TermId> = (10..16).map(TermId).collect();
    let sent = [(ids[0], ids[1]), (ids[2], ids[1]), (ids[3], ids[4])];
    let closure = SentEqualityClosure::new(sent.iter());
    assert!(closure.connected(ids[0], ids[2]), "joined through ids[1]");
    assert!(closure.connected(ids[2], ids[0]));
    assert!(closure.connected(ids[4], ids[3]));
    assert!(!closure.connected(ids[0], ids[3]), "separate classes");
    assert!(!closure.connected(ids[5], ids[0]), "never sent");
    assert!(!closure.connected(ids[5], ids[5]), "a term is not a pair");
}
