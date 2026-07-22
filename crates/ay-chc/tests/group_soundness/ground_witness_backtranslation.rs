// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Anti-fabrication regression tests for ground-witness back-translation.
//!
//! Ground back-translation converts a counterexample found on a heavily
//! TRANSFORMED problem (condense + array-store forwarding + ground-table read
//! concretization + datatype flattening + dead-parameter slicing) into a
//! concrete derivation over the ORIGINAL clauses, which is then decided by pure
//! ground evaluation. The reconstruction itself is a heuristic — it guesses at
//! values the transforms erased — so the guard that matters is that a guess can
//! never become a verdict.
//!
//! These tests exercise the SAFE side of that guard: a problem with the exact
//! archetype shape (a datatype-carrying state, a read-only ground-pinned table
//! array, and a wide acyclic linear predicate DAG) whose error state is
//! genuinely UNREACHABLE must never come back Unsafe, however aggressively the
//! chain engages. The companion UNSAFE instance of the same shape confirms the
//! guard is not passing simply because the machinery is inert.

use ay_chc::{engines, ChcParser, PortfolioConfig, PortfolioResult};
use ntest::timeout;
use std::time::Duration;

/// Build an archetype-shaped problem: datatype state + ground-pinned table
/// array + `depth`-long linear acyclic predicate chain.
///
/// The counter advances by the table value at each step. `bound` is the value
/// the error query compares against: make it unreachable for the SAFE case and
/// reachable for the UNSAFE case.
fn archetype(depth: usize, bound: i64, reachable: bool) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic HORN)\n");
    // Multi-constructor datatype: exercises the per-variant-column flattener
    // (discriminant + per-variant payload columns).
    smt.push_str("(declare-datatypes ((Cell 0)) (((empty) (full (payload Int) (tag Bool)))))\n");
    for level in 0..=depth {
        smt.push_str(&format!(
            "(declare-fun P{level} ((Array Int Int) Int Cell) Bool)\n"
        ));
    }
    // Fact: the table is pinned at three ground indices and nowhere else, which
    // is exactly the read-only-ground-pin shape the concretizer proves away.
    smt.push_str(
        "(assert (forall ((t (Array Int Int)) (c Cell))\n\
         \x20 (=> (and (= (select t 0) 1) (= (select t 1) 2) (= (select t 2) 1) (= c empty))\n\
         \x20     (P0 t 0 c))))\n",
    );
    for level in 0..depth {
        let next = level + 1;
        // Two parallel definitions per step so MultiEdgeMerger has something to
        // merge and the graph collapse has branching to contract.
        smt.push_str(&format!(
            "(assert (forall ((t (Array Int Int)) (n Int) (m Int) (c Cell) (d Cell))\n\
             \x20 (=> (and (P{level} t n c)\n\
             \x20          (= m (+ n (select t 0)))\n\
             \x20          (= d (full m true)))\n\
             \x20     (P{next} t m d))))\n"
        ));
        smt.push_str(&format!(
            "(assert (forall ((t (Array Int Int)) (n Int) (m Int) (c Cell) (d Cell))\n\
             \x20 (=> (and (P{level} t n c)\n\
             \x20          (= m (+ n (select t 2)))\n\
             \x20          (= d (full m false)))\n\
             \x20     (P{next} t m d))))\n"
        ));
    }
    // Error query. Each step adds exactly 1 (both table pins used are 1), so the
    // counter at the last level is exactly `depth`.
    let guard = if reachable {
        format!("(= n {bound})")
    } else {
        format!("(> n {bound})")
    };
    smt.push_str(&format!(
        "(assert (forall ((t (Array Int Int)) (n Int) (c Cell))\n\
         \x20 (=> (and (P{depth} t n c) {guard} (is-full c)) false)))\n"
    ));
    smt.push_str("(check-sat)\n");
    smt
}

fn solve(smt: &str, budget: Duration) -> PortfolioResult {
    let problem = ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let config = PortfolioConfig::test_default().parallel_timeout(Some(budget));
    engines::new_portfolio_solver(problem, config).solve()
}

/// ANTI-FABRICATION GUARD.
///
/// The counter can only ever reach `depth`, and the query needs strictly more
/// than that, so the error is unreachable. Every transform in the chain engages
/// on this shape (datatype flattening, ground-table concretization, condense,
/// graph collapse), which is the point: an over-eager reconstruction that
/// invented values for the erased table entries or the flattened datatype
/// columns would surface here as a fabricated Unsafe.
///
/// Safe or Unknown are both acceptable outcomes. Unsafe is a hard failure.
#[test]
#[timeout(120_000)]
fn safe_archetype_analogue_is_never_reported_unsafe() {
    let smt = archetype(8, 8, false);
    let result = solve(&smt, Duration::from_secs(30));
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "SAFE archetype analogue was reported UNSAFE — a reconstructed derivation was \
         promoted without being validated on the original clauses. Result: {result:?}"
    );
}

/// The companion UNSAFE instance: same shape, reachable error. This is not a
/// completeness assertion (the class is hard and Unknown is a legitimate
/// budget-compliant answer) — it exists so that a future change which makes the
/// SAFE test pass by disabling the whole lane is visible: if this ever reports
/// SAFE, the encoding stopped being a counterexample shape at all.
#[test]
#[timeout(120_000)]
fn unsafe_archetype_analogue_is_never_reported_safe() {
    let smt = archetype(8, 8, true);
    let result = solve(&smt, Duration::from_secs(30));
    assert!(
        !matches!(result, PortfolioResult::Safe(_)),
        "UNSAFE archetype analogue was reported SAFE: {result:?}"
    );
}

/// Build a SAFE archetype variant whose query carries a datatype existential
/// that occurs NOWHERE else — the exact shape ground completion's tester rule
/// is designed to instantiate.
///
/// `contradictory` decides whether the existential is merely tester-constrained
/// (`is-full c`, which the rule CAN satisfy) or self-contradictory
/// (`is-full c ∧ is-empty c`, which it must refuse to satisfy). Either way the
/// arithmetic guard `n > depth` is unreachable, so Unsafe is always wrong.
fn tester_existential_archetype(depth: usize, contradictory: bool) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic HORN)\n");
    smt.push_str("(declare-datatypes ((Cell 0)) (((empty) (full (payload Int) (tag Bool)))))\n");
    for level in 0..=depth {
        smt.push_str(&format!(
            "(declare-fun P{level} ((Array Int Int) Int) Bool)\n"
        ));
    }
    smt.push_str(
        "(assert (forall ((t (Array Int Int)))\n\
         \x20 (=> (and (= (select t 0) 1) (= (select t 1) 2)) (P0 t 0))))\n",
    );
    for level in 0..depth {
        let next = level + 1;
        smt.push_str(&format!(
            "(assert (forall ((t (Array Int Int)) (n Int) (m Int))\n\
             \x20 (=> (and (P{level} t n) (= m (+ n (select t 0)))) (P{next} t m))))\n"
        ));
    }
    // `c` is existential in the query: no equality names it, no premise pins
    // it, and it reaches the constraint only through testers.
    let cell_guard = if contradictory {
        "(and (is-full c) (is-empty c))"
    } else {
        "(is-full c)"
    };
    smt.push_str(&format!(
        "(assert (forall ((t (Array Int Int)) (n Int) (c Cell))\n\
         \x20 (=> (and (P{depth} t n) (> n {depth}) {cell_guard}) false)))\n"
    ));
    smt.push_str("(check-sat)\n");
    smt
}

/// ANTI-FABRICATION GUARD for the tester-driven completion rule.
///
/// Ground completion is allowed to INSTANTIATE a datatype existential to the
/// constructor a tester demands — that is how it recovers witnesses the
/// transforms erased. This test pins the boundary: satisfying the tester does
/// not satisfy the CLAUSE. The counter advances by exactly 1 per step and the
/// query needs strictly more than `depth`, so the error is unreachable no
/// matter what `c` is instantiated to.
///
/// A completion that treated "I made the tester true" as "the step fires" would
/// surface here as a fabricated Unsafe.
#[test]
#[timeout(120_000)]
fn tester_existential_safe_analogue_is_never_reported_unsafe() {
    let smt = tester_existential_archetype(8, false);
    let result = solve(&smt, Duration::from_secs(30));
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "SAFE analogue with a tester-only existential was reported UNSAFE — \
         tester-driven completion manufactured a witness. Result: {result:?}"
    );
}

/// The same shape with a SELF-CONTRADICTORY existential (`is-full c` and
/// `is-empty c` at once). No value of `c` satisfies the query, so the clause
/// can never fire even if the arithmetic guard were reachable. Tester-driven
/// completion must ABSTAIN on conflicting demands rather than pick a tag and
/// let the rest of the environment carry a step that cannot exist.
#[test]
#[timeout(120_000)]
fn contradictory_tester_existential_is_never_reported_unsafe() {
    let smt = tester_existential_archetype(8, true);
    let result = solve(&smt, Duration::from_secs(30));
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "a SELF-CONTRADICTORY tester constraint was satisfied by completion — \
         the rule fabricated a witness for an impossible clause. Result: {result:?}"
    );
}

// ==========================================================================
// MULTI-QUERY (multi-lane) archetype.
//
// `ChcProblem::expand_nullary_fail_queries` — which model-checker-consumer's driver runs and
// the AY CLI does not — replaces a single nullary `(query error)` with ONE
// query per `body => error` clause, so the level-BMC lane sees MANY queries
// whose bodies mention DIFFERENT predicates. The encoding must treat those as
// ALTERNATIVES (a disjunction). Two directions matter, and both are pinned
// here: conflating lanes must never manufacture reachability (the SAFE test),
// and the disjunction must actually find the one reachable lane (the UNSAFE
// test).
// ==========================================================================

/// Archetype shape with several terminal "lanes", each with its OWN query.
///
/// The counter advances by exactly 1 per step, so `P{level}` holds `n =
/// level`. Lane `i` is fed by `P{depth - i}`, hence lane `i` observes `n =
/// depth - i` and nothing else. `reachable_lane` picks which lane's query
/// guard is satisfiable; every other lane is guarded at `depth + 10 + i`,
/// which no state ever reaches.
fn multi_query_archetype(depth: usize, lanes: usize, reachable_lane: Option<usize>) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic HORN)\n");
    smt.push_str("(declare-datatypes ((Cell 0)) (((empty) (full (payload Int) (tag Bool)))))\n");
    for level in 0..=depth {
        smt.push_str(&format!(
            "(declare-fun P{level} ((Array Int Int) Int Cell) Bool)\n"
        ));
    }
    for lane in 0..lanes {
        smt.push_str(&format!(
            "(declare-fun L{lane} ((Array Int Int) Int Cell) Bool)\n"
        ));
    }
    smt.push_str(
        "(assert (forall ((t (Array Int Int)) (c Cell))\n\
         \x20 (=> (and (= (select t 0) 1) (= (select t 1) 2) (= (select t 2) 1) (= c empty))\n\
         \x20     (P0 t 0 c))))\n",
    );
    for level in 0..depth {
        let next = level + 1;
        smt.push_str(&format!(
            "(assert (forall ((t (Array Int Int)) (n Int) (m Int) (c Cell) (d Cell))\n\
             \x20 (=> (and (P{level} t n c)\n\
             \x20          (= m (+ n (select t 0)))\n\
             \x20          (= d (full m true)))\n\
             \x20     (P{next} t m d))))\n"
        ));
        smt.push_str(&format!(
            "(assert (forall ((t (Array Int Int)) (n Int) (m Int) (c Cell) (d Cell))\n\
             \x20 (=> (and (P{level} t n c)\n\
             \x20          (= m (+ n (select t 2)))\n\
             \x20          (= d (full m false)))\n\
             \x20     (P{next} t m d))))\n"
        ));
    }
    // One lane predicate per source level: the lanes reference DIFFERENT
    // predicates, which is the property the expanded-query shape has.
    for lane in 0..lanes {
        let src = depth - lane;
        smt.push_str(&format!(
            "(assert (forall ((t (Array Int Int)) (n Int) (c Cell))\n\
             \x20 (=> (and (P{src} t n c) (is-full c)) (L{lane} t n c))))\n"
        ));
    }
    // One query per lane — the post-`expand_nullary_fail_queries` shape.
    for lane in 0..lanes {
        let bound = if reachable_lane == Some(lane) {
            depth - lane
        } else {
            depth + 10 + lane
        };
        smt.push_str(&format!(
            "(assert (forall ((t (Array Int Int)) (n Int) (c Cell))\n\
             \x20 (=> (and (L{lane} t n c) (= n {bound})) false)))\n"
        ));
    }
    smt.push_str("(check-sat)\n");
    smt
}

/// ANTI-FABRICATION GUARD for the multi-lane query encoding.
///
/// Every lane's query guard is unreachable, so no combination of lanes can
/// derive `false`. The multi-query path must not manufacture reachability by
/// conflating lanes — e.g. by satisfying lane `i`'s guard with lane `j`'s
/// state, or by promoting a level model that satisfies no query at all.
///
/// Safe or Unknown are both acceptable. Unsafe is a hard failure.
#[test]
#[timeout(120_000)]
fn safe_multi_query_analogue_is_never_reported_unsafe() {
    let smt = multi_query_archetype(8, 3, None);
    let result = solve(&smt, Duration::from_secs(30));
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "SAFE multi-query analogue was reported UNSAFE — the multi-lane query \
         encoding manufactured reachability by conflating lanes. Result: {result:?}"
    );
}

/// Scalar multi-lane shape — what the archetype looks like AFTER the
/// scalarizing transform chain (no arrays, no datatypes), which is the problem
/// the level-BMC probe actually encodes.
///
/// `P{level}` holds `n = level`; lane `i` is fed by `P{depth - i}` and so
/// observes only `n = depth - i`. Every lane gets its own query, exactly as
/// `expand_nullary_fail_queries` produces. `reachable_lane` picks the single
/// satisfiable guard; the rest are pinned at `depth + 10 + i`.
fn scalar_multi_query_lanes(depth: usize, lanes: usize, reachable_lane: Option<usize>) -> String {
    let mut smt = String::new();
    smt.push_str("(set-logic HORN)\n");
    for level in 0..=depth {
        smt.push_str(&format!("(declare-fun P{level} (Int Int) Bool)\n"));
    }
    for lane in 0..lanes {
        smt.push_str(&format!("(declare-fun L{lane} (Int Int) Bool)\n"));
    }
    smt.push_str("(assert (forall ((k Int)) (=> (= k 0) (P0 0 k))))\n");
    for level in 0..depth {
        let next = level + 1;
        // Two parallel definitions per step: branching for the graph collapse.
        smt.push_str(&format!(
            "(assert (forall ((n Int) (m Int) (k Int))\n\
             \x20 (=> (and (P{level} n k) (= m (+ n 1)) (= k 0)) (P{next} m k))))\n"
        ));
        smt.push_str(&format!(
            "(assert (forall ((n Int) (m Int) (k Int))\n\
             \x20 (=> (and (P{level} n k) (= m (+ n 1)) (>= k 0)) (P{next} m k))))\n"
        ));
    }
    for lane in 0..lanes {
        let src = depth - lane;
        smt.push_str(&format!(
            "(assert (forall ((n Int) (k Int)) (=> (P{src} n k) (L{lane} n k))))\n"
        ));
    }
    for lane in 0..lanes {
        let bound = if reachable_lane == Some(lane) {
            depth - lane
        } else {
            depth + 10 + lane
        };
        smt.push_str(&format!(
            "(assert (forall ((n Int) (k Int)) (=> (and (L{lane} n k) (= n {bound})) false)))\n"
        ));
    }
    smt.push_str("(check-sat)\n");
    smt
}

/// The converting direction, on the scalarized shape: exactly one reachable
/// lane, expressed as several queries over DIFFERENT predicates, must be found
/// Unsafe.
///
/// Before the multi-lane fix the level loop conjoined the per-query
/// conditions, demanding that all lanes fire at the same level — never
/// satisfiable — so this shape came back Unknown while its single-query
/// equivalent converted. The promoted verdict still comes only from a
/// derivation validated by ground evaluation on the ORIGINAL clauses.
#[test]
#[timeout(180_000)]
fn unsafe_multi_query_analogue_converts() {
    let smt = scalar_multi_query_lanes(8, 3, Some(2));
    let result = solve(&smt, Duration::from_secs(60));
    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "UNSAFE multi-query analogue did not convert: {result:?}"
    );
}

/// The SAFE scalar multi-lane companion: no lane guard is reachable, so a
/// verdict of Unsafe can only come from conflating lanes.
#[test]
#[timeout(180_000)]
fn safe_scalar_multi_query_lanes_never_reported_unsafe() {
    let smt = scalar_multi_query_lanes(8, 3, None);
    let result = solve(&smt, Duration::from_secs(60));
    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "SAFE scalar multi-query analogue was reported UNSAFE: {result:?}"
    );
}

/// Cross-check that the multi-query UNSAFE instance is genuinely the same
/// reachability as its single-query equivalent: lane 2's query alone, without
/// the unreachable sibling queries, must give the same verdict. If these ever
/// disagree, the multi-query encoding changed the problem rather than the
/// search.
#[test]
#[timeout(180_000)]
fn multi_query_and_single_query_analogues_agree() {
    let multi = solve(
        &scalar_multi_query_lanes(8, 3, Some(2)),
        Duration::from_secs(60),
    );
    let single = solve(
        &scalar_multi_query_lanes(6, 1, Some(0)),
        Duration::from_secs(60),
    );
    let unsafe_multi = matches!(multi, PortfolioResult::Unsafe(_));
    let unsafe_single = matches!(single, PortfolioResult::Unsafe(_));
    assert_eq!(
        unsafe_multi, unsafe_single,
        "multi-query ({multi:?}) and single-query ({single:?}) forms of the SAME \
         reachability disagree"
    );
}
