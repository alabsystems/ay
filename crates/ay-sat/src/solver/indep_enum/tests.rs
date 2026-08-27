// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the bit-parallel support enumerator (`indep_enum.rs`).
//!
//! The properties that matter: it FINDS the model of a tiny circuit with a
//! known support; it DECLINES (at zero cost) on a formula with no small
//! support; it finds a model that lives in the LAST block, which is where an
//! off-by-one in the block/column decomposition shows up; exhaustion never
//! turns into a verdict; and — the `4b23cc79df` regression — an enumeration
//! that would run for minutes NEVER spends the solve budget, because search
//! goes first and the slice that follows is metered.

use super::*;
use crate::solver::Solver;

fn lit(v: i32) -> Literal {
    if v > 0 {
        Literal::positive(Variable((v - 1) as u32))
    } else {
        Literal::negative(Variable((-v - 1) as u32))
    }
}

fn solver_from(num_vars: usize, clauses: &[Vec<i32>]) -> Solver {
    let mut s = Solver::new(num_vars);
    for c in clauses {
        s.add_clause(c.iter().map(|&l| lit(l)).collect());
    }
    s
}

/// CNF of `out <-> a XOR b` (the four parity clauses).
fn xor_gate(a: i32, b: i32, out: i32) -> Vec<Vec<i32>> {
    vec![
        vec![-out, a, b],
        vec![-out, -a, -b],
        vec![out, -a, b],
        vec![out, a, -b],
    ]
}

/// CNF of `out <-> a AND b`.
fn and_gate(a: i32, b: i32, out: i32) -> Vec<Vec<i32>> {
    vec![vec![-out, a], vec![-out, b], vec![out, -a, -b]]
}

/// A miniature "PRNG inversion": `n_in` free input bits feed a fixed circuit
/// of XOR and AND gates, and the final layer is pinned by unit clauses to the
/// values the circuit produces on `seed`. Structurally the `xorshift` family
/// in miniature: a tiny independent support, everything else UP-implied, and
/// the outputs nailed down.
///
/// Returns `(num_vars, clauses, seed_bits)`.
fn mini_prng(n_in: usize, rounds: usize, seed: u64) -> (usize, Vec<Vec<i32>>, Vec<bool>) {
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut next = n_in as i32 + 1;
    let mut layer: Vec<i32> = (1..=n_in as i32).collect();
    let seed_bits: Vec<bool> = (0..n_in).map(|i| (seed >> i) & 1 == 1).collect();
    let mut vals = seed_bits.clone();
    for r in 0..rounds {
        let mut next_layer = Vec::with_capacity(n_in);
        let mut next_vals = Vec::with_capacity(n_in);
        for i in 0..n_in {
            let j = (i + 1 + r) % n_in;
            let (a, b) = (layer[i], layer[j]);
            let (av, bv) = (vals[i], vals[j]);
            let out = next;
            next += 1;
            if (i + r) % 3 == 0 {
                clauses.extend(and_gate(a, b, out));
                next_vals.push(av && bv);
            } else {
                clauses.extend(xor_gate(a, b, out));
                next_vals.push(av ^ bv);
            }
            next_layer.push(out);
        }
        layer = next_layer;
        vals = next_vals;
    }
    for (i, &v) in layer.iter().enumerate() {
        clauses.push(vec![if vals[i] { v } else { -v }]);
    }
    ((next - 1) as usize, clauses, seed_bits)
}

fn assert_model(clauses: &[Vec<i32>], model: &[bool]) {
    for c in clauses {
        let ok = c.iter().any(|&l| {
            let v = (l.unsigned_abs() - 1) as usize;
            model[v] == (l > 0)
        });
        assert!(ok, "model violates clause {c:?}");
    }
}

/// Gate 1(a): a tiny circuit with a 4-variable support and a known model —
/// the enumerator must find it.
#[test]
fn finds_model_of_a_four_bit_support_circuit() {
    let (nv, clauses, seed) = mini_prng(4, 3, 0b1011);
    let mut s = solver_from(nv, &clauses);
    let model = s.indep_enum_probe().expect("probe must construct a model");
    assert_model(&clauses, &model);
    assert_eq!(s.stats.indep_enum_admitted, 1, "gate must admit");
    assert_eq!(s.stats.indep_enum_verify_failures, 0);
    assert!(s.stats.indep_enum_support_size <= 4);
    // Whatever seed it returns must reproduce the pinned outputs; the planted
    // one is a model, so at minimum a model exists.
    assert_eq!(seed.len(), 4);
}

/// Gate 1(c): a model that lives in the LAST block. The support is wider than
/// `ENUM_BITS`, so the block/column decomposition is exercised for real, and
/// the planted seed is the very last column of the very last block.
#[test]
fn finds_a_model_that_lives_in_the_last_block() {
    let n_in = (ENUM_BITS + 2) as usize; // 14 support bits => 4 blocks
    let seed = (1u64 << n_in) - 1; // all ones
    let (nv, clauses, _) = mini_prng(n_in, 2, seed);
    let mut s = solver_from(nv, &clauses);
    let model = s.indep_enum_probe().expect("probe must construct a model");
    assert_model(&clauses, &model);
    assert_eq!(s.stats.indep_enum_verify_failures, 0);
    assert!(
        s.stats.indep_enum_blocks >= 1,
        "the enumerator must have run blocks"
    );
}

/// The boundary case with no ambiguity: a conjunction chain over `n_in` free
/// inputs pinned true has EXACTLY ONE model, all-inputs-true, which is the
/// last column of the last block. If the block/column decomposition drops the
/// final block, or mis-maps the high support bits, this test fails.
#[test]
fn the_only_model_being_the_final_column_of_the_final_block_is_found() {
    let n_in = (ENUM_BITS + 2) as usize; // 14 inputs => 2^14 assignments, 4 blocks
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut next = n_in as i32 + 1;
    // Two conjunction chains over the same inputs, in opposite input order, so
    // the internal variables outnumber the support (the support brancher's
    // "|S| <= decidable / 2" policy is upstream of this probe). Pin both.
    for forward in [true, false] {
        let order: Vec<i32> = if forward {
            (1..=n_in as i32).collect()
        } else {
            (1..=n_in as i32).rev().collect()
        };
        let mut acc = next;
        next += 1;
        clauses.extend(and_gate(order[0], order[1], acc));
        for &i in &order[2..] {
            let out = next;
            next += 1;
            clauses.extend(and_gate(acc, i, out));
            acc = out;
        }
        clauses.push(vec![acc]);
    }
    let nv = (next - 1) as usize;
    let mut s = solver_from(nv, &clauses);
    let model = s
        .indep_enum_probe()
        .expect("the unique model must be found");
    assert_model(&clauses, &model);
    assert!(
        (0..n_in).all(|i| model[i]),
        "the unique model sets every input true"
    );
    // The unique model sets EVERY variable true, so whatever support comes
    // out, its assignment index is all-ones: the last column of the last
    // block. Reaching it means the enumerator walked the whole space.
    let size = s.stats.indep_enum_support_size as u32;
    assert!(size > ENUM_BITS, "support {size} must exceed one block");
    assert_eq!(
        s.stats.indep_enum_blocks,
        1u64 << (size - ENUM_BITS),
        "the enumerator must have walked every block to reach the last one"
    );
    assert_eq!(s.stats.indep_enum_verify_failures, 0);
}

/// Two AND chains over `n_in` inputs, in opposite input order, whose outputs
/// are forced true by a RESOLVENT rather than by a unit clause: `(acc | p)`
/// and `(acc | ~p)` imply `acc`, but neither propagates at level 0, so the
/// formula survives root BCP intact and the enumerator faces the whole
/// `2^|S|` space (`|S| = n_in + 2`: the inputs plus the two `p` variables,
/// which no gate defines).
///
/// The unique model sets EVERY variable true, so the surviving column is the
/// last column of the LAST block whatever the support turns out to be —
/// the enumeration has to walk the entire space to reach it. CDCL, by
/// contrast, needs one conflict: decide `acc` false, propagate `p`, hit
/// `(acc | ~p)`, learn `acc`, and the chains propagate every input true.
///
/// That gap — an enumeration that runs for minutes on an instance search
/// answers immediately — is the regression this module's budget exists for.
fn resolvent_forced_and_chains(n_in: usize) -> (usize, Vec<Vec<i32>>) {
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut next = n_in as i32 + 1;
    for forward in [true, false] {
        let order: Vec<i32> = if forward {
            (1..=n_in as i32).collect()
        } else {
            (1..=n_in as i32).rev().collect()
        };
        let mut acc = next;
        next += 1;
        clauses.extend(and_gate(order[0], order[1], acc));
        for &i in &order[2..] {
            let out = next;
            next += 1;
            clauses.extend(and_gate(acc, i, out));
            acc = out;
        }
        let p = next;
        next += 1;
        clauses.push(vec![acc, p]);
        clauses.push(vec![acc, -p]);
    }
    ((next - 1) as usize, clauses)
}

/// THE BUDGET CONTRACT (the `4b23cc79df` regression): an admitted enumeration
/// that would run for minutes must not be able to spend the solve budget.
/// Search goes first, answers, and the enumeration never runs at all.
///
/// Without the budget/ordering fix this instance is enumerated at startup for
/// the WHOLE deadline (the gate authorises billions of visits; the sweep needs
/// minutes) and the solve only returns once the deadline expires — the exact
/// shape that turned six 0.15-186 s SAT solves into 300 s timeouts.
#[test]
fn a_long_enumeration_never_spends_the_solve_budget() {
    let budget = std::time::Duration::from_secs(20);
    let (nv, clauses) = resolvent_forced_and_chains(34);
    let mut s = solver_from(nv, &clauses);
    s.set_solve_deadline(Some(ay_core::time::Instant::now() + budget));
    let t0 = ay_core::time::Instant::now();
    let result = s.solve();
    let elapsed = t0.elapsed();

    assert!(
        result.is_sat(),
        "the formula is SAT and search decides it immediately, got {result:?}"
    );
    assert_eq!(
        s.stats.indep_enum_admitted, 1,
        "the gate must admit this instance — otherwise the test proves nothing"
    );
    assert!(
        s.stats.indep_enum_projected_visits > 1_000_000_000,
        "the admitted work must be huge (projected {} visits)",
        s.stats.indep_enum_projected_visits
    );
    assert_eq!(
        s.stats.indep_enum_blocks, 0,
        "search answered inside its head start, so the parked enumeration must \
         never have run a single block"
    );
    assert!(
        elapsed * 4 < budget,
        "the solve must finish well inside the budget, not at the deadline: \
         {elapsed:?} of {budget:?}"
    );
}

/// The same instance with a deadline the head start cannot cover: the
/// enumeration DOES get its slice, spends it without finding the last block,
/// and hands the budget back to search rather than owning it to the deadline.
#[test]
fn a_spent_enumeration_slice_falls_through_to_search() {
    let budget = std::time::Duration::from_secs(30);
    let (nv, clauses) = resolvent_forced_and_chains(34);
    let mut s = solver_from(nv, &clauses);
    s.set_solve_deadline(Some(ay_core::time::Instant::now() + budget));
    // Park the enumeration exactly as the solve pipeline does, then hand it a
    // slice directly: this is the fall-through path, without waiting out a
    // head start in a unit test.
    s.prepare_indep_enum_at_startup();
    assert_eq!(s.stats.indep_enum_admitted, 1, "the gate must admit");
    if let Some(pending) = s.cold.indep_enum_pending.as_mut() {
        pending.budget = std::time::Duration::from_millis(200);
    }
    let t0 = ay_core::time::Instant::now();
    let outcome = s.run_parked_indep_enum();
    let elapsed = t0.elapsed();
    assert!(
        outcome.is_none(),
        "a slice that cannot reach the last block must produce no verdict"
    );
    assert_eq!(
        s.stats.indep_enum_budget_exhausted, 1,
        "the slice must record that it spent its budget"
    );
    assert!(
        s.stats.indep_enum_blocks > 0,
        "the slice must have enumerated something"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(2),
        "the slice must stop at its own budget, not at the solve deadline: {elapsed:?}"
    );
    // Search still owns the rest of the budget, and still decides the formula.
    assert!(
        s.solve().is_sat(),
        "search must still decide the formula after the probe falls through"
    );
}

/// Gate 1(b): no gate structure means no support means no admission, and the
/// cost is the pre-gate plus a bailed support computation — no enumeration.
#[test]
fn declines_a_formula_with_no_small_support() {
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let n = 60i32;
    let mut x = 12_345u64;
    for _ in 0..200 {
        let mut c: Vec<i32> = Vec::new();
        while c.len() < 3 {
            x = x
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let v = ((x >> 33) % n as u64) as i32 + 1;
            if c.iter().all(|l| l.abs() != v) {
                c.push(if (x >> 20) & 1 == 1 { v } else { -v });
            }
        }
        clauses.push(c);
    }
    let mut s = solver_from(n as usize, &clauses);
    assert!(s.indep_enum_probe().is_none(), "must decline");
    assert_eq!(s.stats.indep_enum_admitted, 0, "must not be admitted");
    assert_eq!(s.stats.indep_enum_blocks, 0, "must not enumerate anything");
}

/// An unreachable output target must exhaust without ever becoming a verdict.
#[test]
fn exhaustion_never_claims_unsat() {
    let (nv, mut clauses, _) = mini_prng(4, 3, 0b0110);
    for c in clauses.iter_mut() {
        if c.len() == 1 {
            c[0] = -c[0];
        }
    }
    let mut s = solver_from(nv, &clauses);
    match s.indep_enum_probe() {
        // Either the flipped target happened to be reachable (then it is a
        // real, verified model) ...
        Some(model) => assert_model(&clauses, &model),
        // ... or the space was exhausted, and the probe still says nothing.
        None => assert!(
            s.stats.indep_enum_exhausted + s.stats.indep_enum_stalled >= 1
                || s.stats.indep_enum_admitted == 0,
            "a declined run must be exhaustion, a stall, or a refused gate"
        ),
    }
    assert_eq!(s.stats.indep_enum_verify_failures, 0);
}

/// The XOR collapse must be exact: a complete parity class becomes one XOR
/// with the polarity that makes "an odd number of literals true" the right
/// constraint.
#[test]
fn xor_collapse_recognises_complete_parity_classes() {
    // Literal encoding: 2v = positive, 2v+1 = negative.
    let p = |v: u32| v * 2;
    let n = |v: u32| v * 2 + 1;
    // Parity-0 class over {0,1,2} (masks 000, 011, 101, 110) => XOR = 1.
    let raw = vec![
        vec![p(0), p(1), p(2)],
        vec![n(0), n(1), p(2)],
        vec![n(0), p(1), n(2)],
        vec![p(0), n(1), n(2)],
        // Parity-1 class over {3,4} (masks 01, 10) => XOR = 0, i.e. x3 = x4.
        vec![n(3), p(4)],
        vec![p(3), n(4)],
    ];
    let (kinds, starts, lits) = collapse_xors(&raw);
    assert_eq!(
        kinds.len(),
        2,
        "both groups must collapse to one constraint"
    );
    assert!(kinds.iter().all(|&k| k == KIND_XOR));
    assert_eq!(starts.last().copied(), Some(5), "3 + 2 literals");
    // XOR = 1 keeps all-positive; XOR = 0 flips exactly one literal.
    assert_eq!(&lits[0..3], &[p(0), p(1), p(2)]);
    assert_eq!(&lits[3..5], &[n(3), p(4)]);
}

/// An incomplete parity class must NOT collapse — those clauses are strictly
/// weaker than the XOR and have to stay as clauses.
#[test]
fn xor_collapse_leaves_incomplete_classes_alone() {
    let p = |v: u32| v * 2;
    let n = |v: u32| v * 2 + 1;
    // The AND-gate shape: three clauses, no complete parity class anywhere.
    let raw = vec![vec![n(2), p(0)], vec![n(2), p(1)], vec![p(2), n(0), n(1)]];
    let (kinds, _, _) = collapse_xors(&raw);
    assert_eq!(kinds.len(), 3);
    assert!(kinds.iter().all(|&k| k == KIND_CLAUSE));
}
