// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential soundness gate for the incremental engine.
//!
//! [`IncrementalDiffGraph`] is an optimization of a decision procedure, and the
//! only thing that matters about an optimized decision procedure is that it
//! decides the same language. So every property here cross-checks it against the
//! deliberately simple, already-trusted [`DiffGraph`] Bellman-Ford engine on
//! randomly generated systems: same edges in, same verdict out.
//!
//! The generator is seeded and deterministic — a failure reproduces exactly.

use ay_diff_logic::graph::{DiffGraph, DiffResult};
use ay_diff_logic::incremental::{AssertOutcome, IncrementalDiffGraph};

/// xorshift64*, so the suite carries no `rand` dependency and every failure is
/// reproducible from its seed alone.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }

    /// A weight in `[-span, span]`.
    fn weight(&mut self, span: i64) -> i64 {
        let m = 2 * span + 1;
        (self.next() % m as u64) as i64 - span
    }
}

/// Reference verdict: is this edge set feasible, per the trusted engine?
fn reference_sat(n: usize, edges: &[(usize, usize, i64)]) -> bool {
    let mut g: DiffGraph<i64> = DiffGraph::new(n);
    for &(from, to, w) in edges {
        // DiffGraph::add_constraint(x, y, c) encodes `x - y <= c` as edge y->x,
        // so pass (to, from, w) to build the edge `from -> to : w`.
        g.add_constraint(to, from, w);
    }
    matches!(g.check(), DiffResult::Sat { .. })
}

/// Incremental verdict: assert every edge in order, reporting the first
/// conflict.
fn incremental_sat(n: usize, edges: &[(usize, usize, i64)]) -> bool {
    let mut g: IncrementalDiffGraph<i64> = IncrementalDiffGraph::new(n);
    for (i, &(from, to, w)) in edges.iter().enumerate() {
        let id = g.register_edge(from, to, w, i as u64);
        if let AssertOutcome::Conflict(tags) = g.assert_edge(id) {
            assert!(!tags.is_empty(), "a conflict must name its edges");
            return false;
        }
    }
    true
}

#[test]
fn incremental_agrees_with_bellman_ford_on_random_systems() {
    let mut rng = Rng(0x5EED_1234_ABCD_0001);
    let mut sat_seen = 0;
    let mut unsat_seen = 0;

    for case in 0..4000 {
        let n = 2 + rng.below(7) as usize;
        let m = rng.below(14) as usize;
        // A narrow weight span makes negative cycles common, so the UNSAT side
        // is exercised as hard as the SAT side.
        let span = 1 + rng.below(3) as i64;
        let edges: Vec<(usize, usize, i64)> = (0..m)
            .map(|_| {
                let a = rng.below(n as u64) as usize;
                let b = rng.below(n as u64) as usize;
                (a, b, rng.weight(span))
            })
            .collect();

        let want = reference_sat(n, &edges);
        let got = incremental_sat(n, &edges);
        assert_eq!(
            want, got,
            "case {case}: incremental disagrees with Bellman-Ford\n  n={n}\n  edges={edges:?}"
        );
        if want {
            sat_seen += 1;
        } else {
            unsat_seen += 1;
        }
    }

    // A differential test that only ever saw one verdict would prove nothing.
    assert!(
        sat_seen > 200 && unsat_seen > 200,
        "generator is degenerate: {sat_seen} sat / {unsat_seen} unsat"
    );
}

#[test]
fn potentials_are_always_a_model_of_the_asserted_edges() {
    let mut rng = Rng(0xC0FF_EE00_1111_2222);

    for _ in 0..1500 {
        let n = 2 + rng.below(6) as usize;
        let m = rng.below(12) as usize;
        let span = 1 + rng.below(3) as i64;

        let mut g: IncrementalDiffGraph<i64> = IncrementalDiffGraph::new(n);
        let mut live: Vec<(usize, usize, i64)> = Vec::new();

        for i in 0..m {
            let from = rng.below(n as u64) as usize;
            let to = rng.below(n as u64) as usize;
            let w = rng.weight(span);
            let id = g.register_edge(from, to, w, i as u64);
            if let AssertOutcome::Consistent = g.assert_edge(id) {
                live.push((from, to, w));
            }
            // The potential must satisfy every edge accepted so far, by direct
            // substitution: this is the model, not an approximation of one.
            let model = g.model();
            for &(f, t, ww) in &live {
                assert!(
                    model[t] - model[f] <= ww,
                    "potential violates {f}->{t}:{ww} (model {:?})",
                    model
                );
            }
        }
    }
}

#[test]
fn pop_restores_the_verdict_of_the_enclosing_level() {
    let mut rng = Rng(0x0BAD_F00D_5555_7777);

    for _ in 0..1200 {
        let n = 2 + rng.below(5) as usize;
        let span = 1 + rng.below(2) as i64;

        let mut g: IncrementalDiffGraph<i64> = IncrementalDiffGraph::new(n);
        let mut base: Vec<(usize, usize, i64)> = Vec::new();

        // A consistent base level.
        let mut tag = 0u64;
        for _ in 0..rng.below(5) {
            let f = rng.below(n as u64) as usize;
            let t = rng.below(n as u64) as usize;
            let w = rng.weight(span);
            let id = g.register_edge(f, t, w, tag);
            tag += 1;
            if let AssertOutcome::Consistent = g.assert_edge(id) {
                base.push((f, t, w));
            }
        }

        // Speculate inside a level, then undo it.
        g.push();
        for _ in 0..rng.below(5) {
            let f = rng.below(n as u64) as usize;
            let t = rng.below(n as u64) as usize;
            let w = rng.weight(span);
            let id = g.register_edge(f, t, w, tag);
            tag += 1;
            let _ = g.assert_edge(id);
        }
        g.pop();

        // After popping, the potential must again be a model of exactly the base
        // constraints, and asserting a base-consistent edge must still succeed.
        let model = g.model().to_vec();
        for &(f, t, w) in &base {
            assert!(
                model[t] - model[f] <= w,
                "after pop, potential violates base edge {f}->{t}:{w}"
            );
        }
        assert!(
            reference_sat(n, &base),
            "base level should be satisfiable by construction"
        );
    }
}

#[test]
fn conflict_explanation_is_a_genuine_negative_cycle() {
    let mut rng = Rng(0xFEED_BEEF_9999_3333);
    let mut conflicts = 0;

    for _ in 0..3000 {
        let n = 2 + rng.below(5) as usize;
        let span = 1 + rng.below(2) as i64;

        let mut g: IncrementalDiffGraph<i64> = IncrementalDiffGraph::new(n);
        let mut by_tag: Vec<(usize, usize, i64)> = Vec::new();

        for i in 0..rng.below(12) {
            let f = rng.below(n as u64) as usize;
            let t = rng.below(n as u64) as usize;
            let w = rng.weight(span);
            let id = g.register_edge(f, t, w, i);
            by_tag.push((f, t, w));
            if let AssertOutcome::Conflict(tags) = g.assert_edge(id) {
                conflicts += 1;
                // The named edges must sum to a negative total weight — that is
                // what makes the conflict a proof of unsatisfiability.
                let total: i64 = tags.iter().map(|&t| by_tag[t as usize].2).sum();
                assert!(
                    total < 0,
                    "explanation sums to {total} >= 0, so it proves nothing: {tags:?}"
                );
                // And the explanation must be a subset of what was asserted.
                for &t in &tags {
                    assert!(
                        (t as usize) < by_tag.len(),
                        "explanation names an unknown edge {t}"
                    );
                }
                break;
            }
        }
    }

    assert!(
        conflicts > 300,
        "expected the generator to produce conflicts, saw {conflicts}"
    );
}

// ---------------------------------------------------------------------------
// RDL: the same differential gate over ℚ[ε].
//
// QF_RDL runs on `RStar`, not `i64`, and the ε component is exactly where a
// strict-inequality bug would hide: `x - y < c` lowers to weight `(c, -1)`, so a
// cycle of rational weight EXACTLY zero is unsatisfiable iff its ε-count is
// negative. An engine that compared only rational parts would call those cycles
// feasible and answer `sat` on an unsat problem. These cases are generated
// deliberately dense in zero-sum cycles so that path is exercised.
// ---------------------------------------------------------------------------

use ay_diff_logic::rstar::RStar;
use num_rational::BigRational;

fn rs(q: i64, eps: i64) -> RStar {
    RStar::new(BigRational::from_integer(q.into()), eps)
}

fn reference_sat_rstar(n: usize, edges: &[(usize, usize, RStar)]) -> bool {
    let mut g: DiffGraph<RStar> = DiffGraph::new(n);
    for (from, to, w) in edges {
        g.add_constraint(*to, *from, w.clone());
    }
    matches!(g.check(), DiffResult::Sat { .. })
}

fn incremental_sat_rstar(n: usize, edges: &[(usize, usize, RStar)]) -> bool {
    let mut g: IncrementalDiffGraph<RStar> = IncrementalDiffGraph::new(n);
    for (i, (from, to, w)) in edges.iter().enumerate() {
        let id = g.register_edge(*from, *to, w.clone(), i as u64);
        if let AssertOutcome::Conflict(_) = g.assert_edge(id) {
            return false;
        }
    }
    true
}

#[test]
fn incremental_agrees_with_bellman_ford_over_q_epsilon() {
    let mut rng = Rng(0xE9E9_1234_5678_9ABC);
    let mut sat_seen = 0;
    let mut unsat_seen = 0;
    let mut strict_zero_cycles = 0;

    for case in 0..3000 {
        let n = 2 + rng.below(6) as usize;
        let m = rng.below(12) as usize;
        let edges: Vec<(usize, usize, RStar)> = (0..m)
            .map(|_| {
                let a = rng.below(n as u64) as usize;
                let b = rng.below(n as u64) as usize;
                // Weights in [-1, 1] with an ε-count in {0, -1}: small rational
                // parts make zero-sum cycles common, and ε = -1 is the strict
                // bound, so the "rational part cancels, ε decides" case is hit
                // constantly rather than by luck.
                let q = rng.weight(1);
                let eps = if rng.below(2) == 0 { 0 } else { -1 };
                if q == 0 && eps == -1 {
                    strict_zero_cycles += 1;
                }
                (a, b, rs(q, eps))
            })
            .collect();

        let want = reference_sat_rstar(n, &edges);
        let got = incremental_sat_rstar(n, &edges);
        assert_eq!(
            want, got,
            "case {case}: ℚ[ε] incremental disagrees with Bellman-Ford\n  n={n}\n  edges={edges:?}"
        );
        if want {
            sat_seen += 1;
        } else {
            unsat_seen += 1;
        }
    }

    assert!(
        sat_seen > 100 && unsat_seen > 100,
        "degenerate ℚ[ε] generator: {sat_seen} sat / {unsat_seen} unsat"
    );
    assert!(
        strict_zero_cycles > 100,
        "the ε-decides-it path was barely exercised ({strict_zero_cycles} strict-zero edges)"
    );
}

#[test]
fn a_zero_weight_cycle_of_strict_bounds_is_unsat() {
    // x < y and y < x: rational parts sum to exactly 0, but two ε's make the
    // cycle negative. This is THE case that separates exact ℚ[ε] handling from
    // a naive rational-only comparison, so it gets its own named test.
    let mut g: IncrementalDiffGraph<RStar> = IncrementalDiffGraph::new(2);
    // x - y <= (0, -1)   i.e.  x - y < 0
    let e0 = g.register_edge(1, 0, rs(0, -1), 0);
    // y - x <= (0, -1)   i.e.  y - x < 0
    let e1 = g.register_edge(0, 1, rs(0, -1), 1);

    assert_eq!(g.assert_edge(e0), AssertOutcome::Consistent);
    match g.assert_edge(e1) {
        AssertOutcome::Conflict(tags) => {
            assert_eq!(tags, vec![0, 1], "both strict edges must be in the cycle");
        }
        AssertOutcome::Consistent => {
            panic!("x < y together with y < x must be UNSAT — ε was ignored");
        }
    }

    // And the non-strict version of the same cycle IS satisfiable (x <= y, y <= x).
    let mut h: IncrementalDiffGraph<RStar> = IncrementalDiffGraph::new(2);
    let f0 = h.register_edge(1, 0, rs(0, 0), 0);
    let f1 = h.register_edge(0, 1, rs(0, 0), 1);
    assert_eq!(h.assert_edge(f0), AssertOutcome::Consistent);
    assert_eq!(
        h.assert_edge(f1),
        AssertOutcome::Consistent,
        "x <= y with y <= x is satisfiable (x = y)"
    );
}

// ---------------------------------------------------------------------------
// Theory propagation soundness.
//
// A propagation that claims a FALSE entailment is worse than no propagation at
// all: DPLL will assert the implied literal and can then return a wrong verdict.
// So each claim is checked two independent ways:
//
//   1. CERTIFICATE. The reported reason is a concrete path v ⇝ a → b ⇝ u. Summing
//      its edge weights must give a value <= the entailed atom's own bound —
//      that IS the proof that δ(v,u) <= d, checkable without trusting the engine.
//   2. REFUTATION. Adding the NEGATION of the entailed atom to the same active
//      set must make the trusted Bellman-Ford engine report UNSAT. If the atom
//      were not entailed, its negation would be consistent.
// ---------------------------------------------------------------------------

use ay_diff_logic::incremental::Entailment;

#[test]
fn every_propagated_entailment_is_certified_and_irrefutable() {
    let mut rng = Rng(0x9A9A_2468_1357_BDBD);
    let mut claims = 0usize;

    for _case in 0..2500 {
        let n = 2 + rng.below(6) as usize;
        let span = 1 + rng.below(3) as i64;

        let mut g: IncrementalDiffGraph<i64> = IncrementalDiffGraph::new(n);
        let mut spec: Vec<(usize, usize, i64)> = Vec::new();

        // Register a pool of edges; assert some, leave the rest as candidate
        // atoms for propagation to reason about.
        let pool = 4 + rng.below(9) as usize;
        let mut ids = Vec::new();
        for i in 0..pool {
            let f = rng.below(n as u64) as usize;
            let t = rng.below(n as u64) as usize;
            let w = rng.weight(span);
            ids.push(g.register_edge(f, t, w, i as u64));
            spec.push((f, t, w));
        }

        let mut active: Vec<(usize, usize, i64)> = Vec::new();
        for (k, &id) in ids.iter().enumerate() {
            if rng.below(2) == 0 {
                continue;
            }
            if let AssertOutcome::Conflict(_) = g.assert_edge(id) {
                break;
            }
            active.push(spec[k]);

            for Entailment { edge_id, reason } in g.entailed_after_assert(id, 64) {
                claims += 1;
                let (v, u, d) = spec[edge_id];

                // (1) THE CONTRACT: AND(reason) |= atom. Verified directly —
                // the reason's own edges, plus the NEGATION of the atom, must be
                // infeasible. This is exactly what DPLL relies on when it turns
                // the propagation into a clause, so it is the property worth
                // testing, and it holds regardless of whether the justifying
                // walk happens to be simple.
                // not(u - v <= d)  ==  v - u <= -d-1  over the integers.
                let mut just: Vec<(usize, usize, i64)> =
                    reason.iter().map(|t| spec[*t as usize]).collect();
                just.push((u, v, -d - 1));
                assert!(
                    !reference_sat(n, &just),
                    "reason {reason:?} does NOT imply atom {v}->{u}:{d} — \
                     the negation is consistent with the stated reason"
                );

                // (2) and the full asserted set must entail it too.
                let mut probe = active.clone();
                probe.push((u, v, -d - 1));
                assert!(
                    !reference_sat(n, &probe),
                    "atom {v}->{u}:{d} was reported entailed, but its negation is \
                     consistent with the asserted set {active:?}"
                );
            }
        }
    }

    assert!(
        claims > 100,
        "propagation never fired ({claims} claims) — the test proves nothing"
    );
}

// ---------------------------------------------------------------------------
// The fast lane must lower atoms IDENTICALLY to the exact lane.
//
// `IStar` exists only to avoid BigRational allocation; if its table drifted from
// `RStar`'s — a flipped edge direction, a missing ε on a strict bound — the
// engine would silently decide a different problem. This pins them together over
// every operator, both atom forms, and both signs of the constant.
// ---------------------------------------------------------------------------

use ay_diff_logic::atom::{lower_istar_atom, lower_rational_atom, DiffAtom, Op};

#[test]
fn fast_lane_lowering_matches_the_exact_lane() {
    const Z: usize = 99;
    let ops = [Op::Le, Op::Lt, Op::Ge, Op::Gt, Op::Eq];
    let consts = [-7i64, -1, 0, 1, 14];
    let mut checked = 0;

    for op in ops {
        for c in consts {
            for rhs in [Some(2usize), None] {
                let q = BigRational::from_integer(c.into());
                let atom = DiffAtom {
                    lhs: 1,
                    rhs,
                    op,
                    c: q,
                };

                let exact = lower_rational_atom(&atom, Z).expect("exact lane lowers every op");
                let fast = lower_istar_atom(&atom, Z).expect("integer constants fit the fast lane");

                assert_eq!(exact.len(), fast.len(), "{op:?} c={c}: edge COUNT differs");
                for (e, f) in exact.iter().zip(fast.iter()) {
                    assert_eq!(
                        (e.from, e.to),
                        (f.from, f.to),
                        "{op:?} c={c}: edge DIRECTION differs"
                    );
                    assert_eq!(
                        e.weight.eps, f.weight.eps,
                        "{op:?} c={c}: ε differs — a strict bound lost its infinitesimal"
                    );
                    assert_eq!(
                        e.weight.q,
                        BigRational::from_integer(f.weight.q.into()),
                        "{op:?} c={c}: constant differs"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert!(
        checked >= 50,
        "coverage too thin: only {checked} edges compared"
    );
}

#[test]
fn fast_lane_declines_what_it_cannot_represent() {
    const Z: usize = 99;
    // A genuine fraction has no i128 image; the caller must use the exact lane.
    let third = DiffAtom {
        lhs: 1,
        rhs: Some(2),
        op: Op::Le,
        c: BigRational::new(1.into(), 3.into()),
    };
    assert!(lower_rational_atom(&third, Z).is_some());
    assert!(
        lower_istar_atom(&third, Z).is_none(),
        "a non-integral constant must be REFUSED, never rounded"
    );
}
