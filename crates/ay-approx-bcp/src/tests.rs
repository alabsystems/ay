// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Crate-level property tests.  The soundness test is the load-bearing
//! one: if the filter ever returns `false` for a clause that is
//! actually unit or falsified, BCP would drop a forced literal or miss
//! a conflict, and the solver would be unsound.

use crate::{
    filter::{may_be_unit_or_falsified, AssignmentMask},
    metrics::FilterMetrics,
    signature::ClauseSignature,
};

/// A small xorshift64* PRNG so the property test is deterministic
/// without pulling in a dev-dependency on `rand`.
#[derive(Debug, Clone, Copy)]
struct Xorshift64 {
    state: u64,
}

impl Xorshift64 {
    const fn new(seed: u64) -> Self {
        // xorshift64 cannot start from zero.
        let state = if seed == 0 {
            0xDEAD_BEEF_CAFE_F00D
        } else {
            seed
        };
        Self { state }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    /// Uniform in `[0, bound)`; `bound` must be positive.  Biased for
    /// large `bound`, but 32-bit truncation is fine for our variable
    /// ranges.
    fn next_range(&mut self, bound: u32) -> u32 {
        assert!(bound > 0);
        (self.next_u64() as u32) % bound
    }

    fn flip(&mut self) -> bool {
        self.next_u64() & 1 == 0
    }
}

/// Truth value of a variable under a sparse partial assignment.  `None`
/// means unassigned.
type Assignment = std::collections::HashMap<u32, bool>;

/// Evaluate a literal under the assignment.  Returns `None` if the
/// variable is unassigned, otherwise `Some(true/false)`.
fn eval_literal(lit: i32, assignment: &Assignment) -> Option<bool> {
    let var = lit.unsigned_abs();
    let truth = assignment.get(&var).copied()?;
    Some(if lit > 0 { truth } else { !truth })
}

/// Classify a clause under a partial assignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseStatus {
    /// Some literal evaluates to true.
    Satisfied,
    /// Exactly one literal is unassigned and all others are false.
    Unit,
    /// All literals are false.
    Falsified,
    /// Two or more literals are unassigned and none are true.
    Open,
}

fn classify(clause: &[i32], assignment: &Assignment) -> ClauseStatus {
    let mut unassigned = 0u32;
    let mut has_true = false;
    for &lit in clause {
        match eval_literal(lit, assignment) {
            Some(true) => has_true = true,
            Some(false) => {}
            None => unassigned += 1,
        }
    }
    if has_true {
        ClauseStatus::Satisfied
    } else if unassigned == 0 {
        ClauseStatus::Falsified
    } else if unassigned == 1 {
        ClauseStatus::Unit
    } else {
        ClauseStatus::Open
    }
}

/// Build the [`AssignmentMask`] that corresponds to `assignment` — the
/// OR of `literal_bit(l)` for every literal currently falsified.
fn build_mask(assignment: &Assignment) -> AssignmentMask {
    let mut mask = AssignmentMask::empty();
    for (&var, &truth) in assignment {
        // A literal is falsified iff its polarity disagrees with the
        // variable's truth value.  If `var = true`, then `-var` is
        // false.  If `var = false`, then `+var` is false.
        let falsified_literal = if truth { -(var as i32) } else { var as i32 };
        mask.insert_falsified_literal(falsified_literal);
    }
    mask
}

/// Generate a random 3-literal clause over `n_vars` variables.  We
/// deliberately allow the same variable to appear twice — realistic
/// 3-SAT benchmarks contain such clauses after preprocessing.
fn random_3sat_clause(rng: &mut Xorshift64, n_vars: u32) -> Vec<i32> {
    let mut clause = Vec::with_capacity(3);
    for _ in 0..3 {
        let var = 1 + rng.next_range(n_vars);
        let lit = if rng.flip() {
            var as i32
        } else {
            -(var as i32)
        };
        clause.push(lit);
    }
    clause
}

/// Generate a random partial assignment over `n_vars` variables.  Each
/// variable is included with probability `density` (0..1).
fn random_assignment(rng: &mut Xorshift64, n_vars: u32, density_256: u32) -> Assignment {
    let mut a = Assignment::new();
    for var in 1..=n_vars {
        if rng.next_range(256) < density_256 {
            a.insert(var, rng.flip());
        }
    }
    a
}

#[test]
fn signature_from_literals_deterministic() {
    // Same input slice → same u64.
    let lits = [7i32, -3, 12, -50, 1];
    let a = ClauseSignature::from_literals(&lits);
    let b = ClauseSignature::from_literals(&lits);
    assert_eq!(a, b);

    // Order-invariant: OR is commutative/associative.
    let mut shuffled = lits.to_vec();
    shuffled.reverse();
    let c = ClauseSignature::from_literals(&shuffled);
    assert_eq!(a, c);
}

#[test]
fn filter_never_false_negative() {
    // Deterministic randomized soundness test.  For 10_000 (clause,
    // assignment) pairs, compute the exact status and verify:
    //
    //     status ∈ { Unit, Falsified }   ⟹   filter returns true.
    //
    // This is the load-bearing property.  A single failure would mean
    // the filter can cause the solver to skip a unit propagation or
    // miss a conflict.
    let mut rng = Xorshift64::new(0xA5A5_A5A5_A5A5_A5A5);
    let n_vars: u32 = 30;
    let iterations = 10_000;

    let mut unit_or_falsified_seen = 0u64;

    for iter in 0..iterations {
        // Vary assignment density to stress both sparse and dense
        // trails.  256 means "always assigned," 0 means "never."
        let density = (iter as u32) % 256;
        let assignment = random_assignment(&mut rng, n_vars, density);
        let clause = random_3sat_clause(&mut rng, n_vars);

        let exact_status = classify(&clause, &assignment);
        let sig = ClauseSignature::from_literals(&clause);
        let mask = build_mask(&assignment);
        let filter_said = may_be_unit_or_falsified(sig, mask);

        match exact_status {
            ClauseStatus::Unit | ClauseStatus::Falsified => {
                unit_or_falsified_seen += 1;
                assert!(
                    filter_said,
                    "SOUNDNESS VIOLATION (iter {iter}): clause {clause:?} is \
                     {exact_status:?} under assignment {assignment:?} but the \
                     filter returned false (would skip)."
                );
            }
            ClauseStatus::Satisfied | ClauseStatus::Open => {
                // No constraint — filter may return true (false positive
                // is allowed) or false (skip, which is correct).
            }
        }
    }

    // Sanity: the random generator actually produced unit/falsified
    // clauses.  If this number is zero, the property above is vacuous.
    assert!(
        unit_or_falsified_seen > 100,
        "property test is vacuous: only {unit_or_falsified_seen} unit/falsified \
         clauses were sampled out of {iterations}.  Tighten the distribution."
    );
}

#[test]
fn filter_skip_rate_nonzero() {
    // On random 3-SAT clauses and reasonably dense random assignments,
    // the filter should skip a non-trivial fraction of clauses.  If it
    // skipped 0% we'd be doing pure overhead; if ≥10% we're buying real
    // BCP time back.
    let mut rng = Xorshift64::new(0x1234_5678_9ABC_DEF0);
    let n_vars: u32 = 100;
    let iterations = 5_000;
    let mut metrics = FilterMetrics::new();

    for _ in 0..iterations {
        // Fixed moderate density: ~25% of variables assigned.  This
        // keeps the clause distribution dominated by open clauses that
        // the filter *should* be able to skip.
        let assignment = random_assignment(&mut rng, n_vars, 64);
        let clause = random_3sat_clause(&mut rng, n_vars);

        let sig = ClauseSignature::from_literals(&clause);
        let mask = build_mask(&assignment);
        let flagged = may_be_unit_or_falsified(sig, mask);
        metrics.record(!flagged);
    }

    let rate = metrics.skip_rate().expect("at least one probe recorded");
    assert!(
        rate >= 0.10,
        "filter skip rate too low to be useful: {rate:.3} \
         (checked {}, skipped {})",
        metrics.checked,
        metrics.skipped
    );
}

#[test]
fn metrics_counts_correctly() {
    let mut m = FilterMetrics::new();
    for _ in 0..7 {
        m.record(true);
    }
    for _ in 0..3 {
        m.record(false);
    }
    assert_eq!(m.checked, 10);
    assert_eq!(m.skipped, 7);
    let rate = m.skip_rate().expect("non-empty");
    assert!((rate - 0.7).abs() < 1e-12);
}
