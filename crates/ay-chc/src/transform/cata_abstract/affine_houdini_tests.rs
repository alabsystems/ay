// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the multi-predicate affine Houdini abstract solver (CATA v2).

use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;

use super::super::{CataKind, ColumnTag};
use super::{candidate_pool, solve_abstract_affine};
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};

fn iv(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(20)
}

/// An empty tags map ⇒ the affine Houdini runs its legacy conjunctive pool.
fn no_tags() -> FxHashMap<PredicateId, Vec<ColumnTag>> {
    FxHashMap::default()
}

/// `append(s0,s1,s2)` as a size relation: base `append(1,x,x)`, step
/// `append(s0,s1,s2) ⇒ append(s0+1,s1,s2+1)`. The safe query
/// `append(s0,s1,s2) ∧ s2 ≥ s0+s1 ⇒ false` needs the triple-sum equality
/// `s2 = s0+s1−1` — the `size(append)` invariant that PDR/Spacer miss.
#[test]
fn affine_houdini_finds_append_sum_invariant() {
    let mut p = ChcProblem::new();
    let append = p.declare_predicate("append", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    // base: append(1, x, x)
    let x = iv("x");
    p.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(
            append,
            vec![ChcExpr::int(1), ChcExpr::var(x.clone()), ChcExpr::var(x)],
        ),
    ));
    // step: append(s0,s1,s2) => append(s0+1, s1, s2+1)
    let (s0, s1, s2) = (iv("s0"), iv("s1"), iv("s2"));
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            append,
            vec![
                ChcExpr::var(s0.clone()),
                ChcExpr::var(s1.clone()),
                ChcExpr::var(s2.clone()),
            ],
        )]),
        ClauseHead::Predicate(
            append,
            vec![
                ChcExpr::add(ChcExpr::var(s0), ChcExpr::int(1)),
                ChcExpr::var(s1.clone()),
                ChcExpr::add(ChcExpr::var(s2), ChcExpr::int(1)),
            ],
        ),
    ));
    // query: append(a,b,c) ∧ c >= a+b => false  (unreachable: c = a+b-1)
    let (a, b, c) = (iv("a"), iv("b"), iv("c"));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                append,
                vec![
                    ChcExpr::var(a.clone()),
                    ChcExpr::var(b.clone()),
                    ChcExpr::var(c.clone()),
                ],
            )],
            Some(ChcExpr::ge(
                ChcExpr::var(c),
                ChcExpr::add(ChcExpr::var(a), ChcExpr::var(b)),
            )),
        ),
        ClauseHead::False,
    ));

    let model = solve_abstract_affine(&p, &no_tags(), deadline())
        .expect("affine Houdini must prove the append-sum problem safe");
    let interp = model.get(&append).expect("append interpreted");
    let smt = crate::InvariantModel::expr_to_smtlib(&interp.formula);
    // The invariant must pin the sum relation (some `a_i + a_j - a_k` equality).
    assert!(
        smt.contains('+') || smt.contains('-'),
        "expected an affine relation, got: {smt}"
    );
}

/// The `ff` error-flag encoding used by clam/leon: a Bool nullary predicate
/// `ff` with `body ⇒ ff` and `ff ⇒ false`. Exercises the universal `false`
/// candidate that lets Houdini keep an unreachable flag pinned to `false`.
#[test]
fn affine_houdini_handles_error_flag_encoding() {
    let mut p = ChcProblem::new();
    let r = p.declare_predicate("R", vec![ChcSort::Int]);
    let ff = p.declare_predicate("ff", vec![]);

    // R(0)
    p.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(r, vec![ChcExpr::int(0)]),
    ));
    // R(x) => R(x+1)
    let x = iv("x");
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(r, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(r, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1))]),
    ));
    // R(y) ∧ y < 0 => ff
    let y = iv("y");
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(ff, vec![]),
    ));
    // ff => false
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(ff, vec![])]),
        ClauseHead::False,
    ));

    let model = solve_abstract_affine(&p, &no_tags(), deadline())
        .expect("affine Houdini must prove the error-flag problem safe");
    // ff must be pinned to false (unreachable).
    let ff_interp = model.get(&ff).expect("ff interpreted");
    let smt = crate::InvariantModel::expr_to_smtlib(&ff_interp.formula);
    assert!(smt.contains("false"), "ff must be false, got: {smt}");
}

/// SOUNDNESS: an UNSAFE abstract problem (the query is genuinely reachable)
/// must NOT be reported safe — Houdini's query check fails ⇒ `None`.
#[test]
fn affine_houdini_returns_none_for_unsafe_abstract_problem() {
    let mut p = ChcProblem::new();
    let r = p.declare_predicate("R", vec![ChcSort::Int]);
    // R(0)
    p.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(r, vec![ChcExpr::int(0)]),
    ));
    // R(x) => R(x+1)
    let x = iv("x");
    p.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(r, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(r, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1))]),
    ));
    // query: R(y) ∧ y >= 5 => false  — REACHABLE (R holds of every y ≥ 0).
    let y = iv("y");
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    assert!(
        solve_abstract_affine(&p, &no_tags(), deadline()).is_none(),
        "an unsafe abstract problem must never be proved safe by Houdini"
    );
}

// ── CATA v2 depth-1 GUARDED families ────────────────────────────────────────

/// Column tags for a 3-column `insert`-shaped abstract predicate:
/// `[scalar F | Min_a | Min_b]`. Kept minimal (one scalar element + two Min
/// columns) so the guarded-min recurrence `B = ite(F ≤ A, F, A)` is emitted.
fn min_recurrence_tags(pid: PredicateId) -> FxHashMap<PredicateId, Vec<ColumnTag>> {
    let mut m = FxHashMap::default();
    m.insert(
        pid,
        vec![
            ColumnTag {
                kind: None,
                group: 0,
                scalar_int: true,
            }, // col0: element F
            ColumnTag {
                kind: Some(CataKind::Min),
                group: 1,
                scalar_int: false,
            }, // col1: Min_a
            ColumnTag {
                kind: Some(CataKind::Min),
                group: 2,
                scalar_int: false,
            }, // col2: Min_b
        ],
    );
    m
}

fn smtlib_pool(pool: &[ChcExpr]) -> Vec<String> {
    pool.iter()
        .map(crate::InvariantModel::expr_to_smtlib)
        .collect()
}

/// `candidate_pool` emits the guarded families when tags are supplied, and is
/// BYTE-IDENTICAL to the legacy conjunctive pool when tags are empty — the
/// guarded atoms are purely additive (the only `ite`/`=>` atoms in the pool).
#[test]
fn candidate_pool_guarded_families_are_additive() {
    let pid = PredicateId::new(0);
    // Compact 4-column layout `[scalar F | Min_a | Min_b | Sorted]`. Small
    // enough that NEITHER pool hits its truncation cap, so `stripped` vs
    // `empty` isolates exactly the guarded atoms (no cap confound).
    let sorts = vec![ChcSort::Int; 4];
    let tags = vec![
        ColumnTag {
            kind: None,
            group: 0,
            scalar_int: true,
        }, // col0 scalar element
        ColumnTag {
            kind: Some(CataKind::Min),
            group: 1,
            scalar_int: false,
        }, // col1 Min
        ColumnTag {
            kind: Some(CataKind::Min),
            group: 2,
            scalar_int: false,
        }, // col2 Min
        ColumnTag {
            kind: Some(CataKind::Sorted),
            group: 3,
            scalar_int: false,
        }, // col3 flag
    ];
    let constants = vec![-2, -1, 0, 1, 2];

    let with_tags = candidate_pool(pid, &sorts, &constants, &tags);
    let empty = candidate_pool(pid, &sorts, &constants, &[]);

    let with_smt = smtlib_pool(&with_tags);
    let empty_smt = smtlib_pool(&empty);

    // Emission: at least one guarded-min `ite` recurrence and one flag-guarded
    // `=>` implication appear only in the tagged pool.
    assert!(
        with_smt.iter().any(|s| s.contains("ite")),
        "tagged pool must contain a guarded-min ite recurrence"
    );
    assert!(
        with_smt.iter().any(|s| s.contains("=>")),
        "tagged pool must contain a flag-guarded implication"
    );

    // Additive: the legacy (empty-tags) pool has NO guarded atoms, and it is
    // strictly smaller than the tagged pool.
    assert!(
        empty_smt
            .iter()
            .all(|s| !s.contains("ite") && !s.contains("=>")),
        "empty-tags pool must be free of guarded atoms"
    );
    assert!(
        with_smt.len() > empty_smt.len(),
        "tagged pool must strictly add atoms"
    );

    // PURELY ADDITIVE: the legacy pool is an ORDER-PRESERVING SUBSEQUENCE of the
    // tagged pool. The guarded families are inserted between the exact
    // equalities and the low-value bounds — no legacy atom is removed, altered,
    // or reordered. (Neither pool is truncated at this column count, so the cap
    // difference is not a confound.)
    let mut tagged_iter = with_smt.iter();
    for legacy in &empty_smt {
        assert!(
            tagged_iter.by_ref().any(|t| t == legacy),
            "legacy atom `{legacy}` is missing or reordered in the tagged pool"
        );
    }
}

/// LOAD-BEARING: a 3-clause abstract problem whose safety proof requires the
/// NON-CONVEX min recurrence `B = ite(F ≤ A, F, A)`. Houdini returns `None`
/// WITHOUT the guarded family (the convex hull of the min relation admits a
/// spurious `B < F ∧ B < A` point that the query hits), and a certified Safe
/// WITH it.
fn min_recurrence_problem() -> (ChcProblem, PredicateId) {
    let mut p = ChcProblem::new();
    let pp = p.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);
    let (f, a, b) = (iv("F"), iv("A"), iv("B"));
    // Fact: B = min(F, A)  ⇒  P(F, A, B).   Reachable(P) = { (F, A, min(F,A)) }.
    p.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::var(b.clone()),
            ChcExpr::ite(
                ChcExpr::le(ChcExpr::var(f.clone()), ChcExpr::var(a.clone())),
                ChcExpr::var(f.clone()),
                ChcExpr::var(a.clone()),
            ),
        )),
        ClauseHead::Predicate(pp, vec![ChcExpr::var(f), ChcExpr::var(a), ChcExpr::var(b)]),
    ));
    // Query: P(F,A,B) ∧ B < F ∧ B < A ⇒ false.  Unreachable (min equals F or A),
    // but NON-CONVEX to exclude: needs `B = F ∨ B = A`.
    let (f2, a2, b2) = (iv("F2"), iv("A2"), iv("B2"));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pp,
                vec![
                    ChcExpr::var(f2.clone()),
                    ChcExpr::var(a2.clone()),
                    ChcExpr::var(b2.clone()),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::lt(ChcExpr::var(b2.clone()), ChcExpr::var(f2)),
                ChcExpr::lt(ChcExpr::var(b2), ChcExpr::var(a2)),
            )),
        ),
        ClauseHead::False,
    ));
    (p, pp)
}

#[test]
fn guarded_min_recurrence_is_load_bearing() {
    let (p, pid) = min_recurrence_problem();

    // WITHOUT guards: the affine lattice cannot exclude the non-convex query.
    assert!(
        solve_abstract_affine(&p, &no_tags(), deadline()).is_none(),
        "affine-only Houdini must NOT prove the min-recurrence problem safe"
    );

    // WITH the guarded-min family: `B = ite(F ≤ A, F, A)` is retained and proves
    // safety.
    let tags = min_recurrence_tags(pid);
    let model = solve_abstract_affine(&p, &tags, deadline())
        .expect("guarded-min Houdini must prove the min-recurrence problem safe");
    let smt = crate::InvariantModel::expr_to_smtlib(&model.get(&pid).expect("P interp").formula);
    assert!(
        smt.contains("ite"),
        "the retained invariant must carry the non-convex min recurrence: {smt}"
    );
}

/// ADVERSARIAL NO-FALSE-SAFE PIN (i): a "perturbed abstraction" whose TRUE
/// relation is `B = max(F, A)` (the classic min↔max swap) with a GENUINELY
/// REACHABLE query. The plausible-but-false guarded-min atom `B = min(F, A)` is
/// in the pool, yet it is dropped by the fail-closed sweep — Houdini returns
/// `None`, NEVER a wrong Safe. 0-wrong is a property of the gate, not the pool.
#[test]
fn guarded_min_never_manufactures_false_safe() {
    let mut p = ChcProblem::new();
    let pp = p.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);
    let (f, a, b) = (iv("F"), iv("A"), iv("B"));
    // Fact (perturbed): B = max(F, A) ⇒ P(F, A, B).
    p.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::var(b.clone()),
            ChcExpr::ite(
                ChcExpr::le(ChcExpr::var(f.clone()), ChcExpr::var(a.clone())),
                ChcExpr::var(a.clone()),
                ChcExpr::var(f.clone()),
            ),
        )),
        ClauseHead::Predicate(pp, vec![ChcExpr::var(f), ChcExpr::var(a), ChcExpr::var(b)]),
    ));
    // Query: P(F,A,B) ∧ B = F ∧ F > A ⇒ false.  REACHABLE (e.g. (10,0,10)),
    // so the problem is UNSAFE — the correct verdict is "no proof" (None).
    let (f2, a2, b2) = (iv("F2"), iv("A2"), iv("B2"));
    p.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pp,
                vec![
                    ChcExpr::var(f2.clone()),
                    ChcExpr::var(a2.clone()),
                    ChcExpr::var(b2.clone()),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(b2), ChcExpr::var(f2.clone())),
                ChcExpr::gt(ChcExpr::var(f2), ChcExpr::var(a2)),
            )),
        ),
        ClauseHead::False,
    ));

    let tags = min_recurrence_tags(pp);
    assert!(
        solve_abstract_affine(&p, &tags, deadline()).is_none(),
        "a false guarded-min atom must be dropped — never a wrong Safe"
    );
}
