// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BDD-based PB-to-CNF encoding (Een & Sorensson 2006).
//!
//! Builds a Reduced Ordered BDD for the PB constraint and extracts
//! clauses by assigning an auxiliary variable to each internal BDD node.
//!
//! # References
//! - Een & Sorensson, "Translating Pseudo-Boolean Constraints into SAT", 2006

use std::collections::BTreeMap as HashMap;

/// Poll the stop hook (deadline / memory budget) once per this many freshly
/// created BDD nodes. The BDD/counter encoding of a wide cardinality row is
/// pseudo-polynomial — `O(n * rhs)` distinct `(index, slack)` states — so a
/// dense row (e.g. a 20000-term `sum = 10000` from a stable-marriage SMTI
/// objective) materializes hundreds of millions of nodes/clauses. Without an
/// interruption check the construction runs for tens of seconds and allocates
/// many gigabytes before the caller's per-constraint poll ever regains control,
/// overrunning the timeout and breaching `MEMLIMIT`. Polling on this cadence
/// lets the build bail cleanly the instant the deadline passes or memory crosses
/// the budget. Cheap relative to the node's own clause emission, so it is a
/// strict no-op for rows that finish within budget.
pub(crate) const BDD_STOP_POLL_INTERVAL: u64 = 4096;

/// BDD node identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum BddNode {
    /// Terminal TRUE node.
    True,
    /// Terminal FALSE node.
    False,
    /// Internal node with an assigned auxiliary variable (1-based DIMACS).
    Internal(i32),
}

/// Encodes a normalized `>= rhs` constraint into CNF using BDD construction.
///
/// `coeffs` and `lits` must be the same length, with all coefficients positive.
/// `rhs` must be > 0 (trivial cases should be handled by the caller).
/// Clauses are appended to `clauses`; new variables are allocated via `next_var`.
pub(crate) fn encode_bdd(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) {
    let n = coeffs.len();

    // Sort by coefficient descending for better BDD ordering.
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| coeffs[b].cmp(&coeffs[a]));
    let sorted_coeffs: Vec<i128> = order.iter().map(|&i| coeffs[i]).collect();
    let sorted_lits: Vec<i32> = order.iter().map(|&i| lits[i]).collect();

    // Compute suffix sums for pruning.
    let mut suffix_sum = vec![0i128; n + 1];
    for i in (0..n).rev() {
        suffix_sum[i] = suffix_sum[i + 1].saturating_add(sorted_coeffs[i]);
    }

    // Build BDD and generate clauses.
    let mut memo: HashMap<(usize, i128), BddNode> = HashMap::new();
    let root = build_bdd(
        0,
        rhs,
        &sorted_coeffs,
        &sorted_lits,
        &suffix_sum,
        &mut memo,
        clauses,
        next_var,
    );

    match root {
        BddNode::True => {
            // Constraint is always satisfied -- nothing to add.
        }
        BddNode::False => {
            // Constraint is unsatisfiable.
            clauses.push(Vec::new());
        }
        BddNode::Internal(sel) => {
            // Force the root to be true.
            clauses.push(vec![sel]);
        }
    }
}

/// Interruptible counterpart of [`encode_bdd`].
///
/// Identical clause/variable output to [`encode_bdd`] when it runs to completion,
/// but polls `should_stop` (the deadline + `MEMLIMIT` guard) on a fixed cadence
/// during BDD construction. Returns `true` if the build was interrupted partway —
/// in which case the partially-emitted clauses MUST be discarded by the caller
/// (an incomplete BDD does not soundly encode the constraint). Returns `false`
/// when the constraint was encoded in full (output is bit-identical to
/// [`encode_bdd`]). See [`BDD_STOP_POLL_INTERVAL`] for why this matters.
pub(crate) fn encode_bdd_interruptible<F>(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    should_stop: &mut F,
) -> bool
where
    F: FnMut() -> bool,
{
    let n = coeffs.len();

    // Sort by coefficient descending for better BDD ordering (matches `encode_bdd`).
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| coeffs[b].cmp(&coeffs[a]));
    let sorted_coeffs: Vec<i128> = order.iter().map(|&i| coeffs[i]).collect();
    let sorted_lits: Vec<i32> = order.iter().map(|&i| lits[i]).collect();

    let mut suffix_sum = vec![0i128; n + 1];
    for i in (0..n).rev() {
        suffix_sum[i] = suffix_sum[i + 1].saturating_add(sorted_coeffs[i]);
    }

    let mut memo: HashMap<(usize, i128), BddNode> = HashMap::new();
    let mut poll_counter: u64 = 0;
    let mut interrupted = false;
    let root = build_bdd_interruptible(
        0,
        rhs,
        &sorted_coeffs,
        &sorted_lits,
        &suffix_sum,
        &mut memo,
        clauses,
        next_var,
        should_stop,
        &mut poll_counter,
        &mut interrupted,
    );

    if interrupted {
        return true;
    }

    match root {
        BddNode::True => {}
        BddNode::False => {
            clauses.push(Vec::new());
        }
        BddNode::Internal(sel) => {
            clauses.push(vec![sel]);
        }
    }
    false
}

/// Outcome of a budget-capped BDD encode attempt ([`encode_bdd_budgeted`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BddBudgetOutcome {
    /// Row fully encoded within budget; clauses and variables were appended.
    Encoded {
        /// Fresh-state work charged to the caller's budget pool (poll
        /// granularity: multiples of [`BDD_STOP_POLL_INTERVAL`]).
        fresh_states: u64,
    },
    /// The fresh-state budget was exceeded; ALL partial output (clauses and
    /// allocated variables) has been rolled back. The caller should fall back
    /// to another encoding.
    BudgetExceeded {
        /// Fresh-state work spent before the abort (charge it to the pool).
        fresh_states: u64,
    },
    /// `external_stop` requested interruption; partial output rolled back.
    /// The caller should propagate the interruption.
    Interrupted,
}

/// Budget-capped BDD encode: identical output to [`encode_bdd`] when the row's
/// BDD has at most ~`max_fresh_states` fresh `(index, slack)` states, and a
/// clean rollback (no clauses, no variables) otherwise.
///
/// The budget is enforced via the existing interruption hook, which fires once
/// per [`BDD_STOP_POLL_INTERVAL`] fresh states — so the effective cap is
/// `max_fresh_states` rounded up to the next poll boundary, and the decision is
/// DETERMINISTIC in the row (it depends only on the fresh-state count, never on
/// wall clock). `external_stop` is polled on the same cadence; when it fires
/// the attempt rolls back and reports [`BddBudgetOutcome::Interrupted`] so the
/// caller can abandon the whole encode (deadline / memory pressure).
pub(crate) fn encode_bdd_budgeted<F>(
    coeffs: &[i128],
    lits: &[i32],
    rhs: i128,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    max_fresh_states: u64,
    external_stop: &mut F,
) -> BddBudgetOutcome
where
    F: FnMut() -> bool,
{
    let saved_clauses = clauses.len();
    let saved_next_var = *next_var;
    let mut polls: u64 = 0;
    let mut external = false;
    let mut hook = || {
        if external_stop() {
            external = true;
            return true;
        }
        polls += 1;
        polls.saturating_mul(BDD_STOP_POLL_INTERVAL) > max_fresh_states
    };
    let interrupted = encode_bdd_interruptible(coeffs, lits, rhs, clauses, next_var, &mut hook);
    let fresh_states = polls.saturating_mul(BDD_STOP_POLL_INTERVAL);

    if interrupted {
        // An incomplete BDD does not soundly encode the row: discard every
        // partial clause and free the allocated variable numbers.
        clauses.truncate(saved_clauses);
        *next_var = saved_next_var;
        if external {
            BddBudgetOutcome::Interrupted
        } else {
            BddBudgetOutcome::BudgetExceeded { fresh_states }
        }
    } else {
        BddBudgetOutcome::Encoded { fresh_states }
    }
}

/// Interruptible counterpart of [`build_bdd`]. On a stop request it sets
/// `*interrupted = true` and returns `BddNode::False`; the caller must not use
/// the (partial) result once `interrupted` is set.
///
/// Delegates to [`build_bdd_iter`] with an active poll hook — same iterative,
/// heap-bounded traversal as [`build_bdd`], so the two produce bit-identical
/// output for any row that finishes within budget (see
/// `interruptible_matches_plain_when_not_stopped`).
#[allow(clippy::too_many_arguments)]
fn build_bdd_interruptible<F>(
    i: usize,
    s: i128,
    coeffs: &[i128],
    lits: &[i32],
    suffix_sum: &[i128],
    memo: &mut HashMap<(usize, i128), BddNode>,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    should_stop: &mut F,
    poll_counter: &mut u64,
    interrupted: &mut bool,
) -> BddNode
where
    F: FnMut() -> bool,
{
    if *interrupted {
        return BddNode::False;
    }
    build_bdd_iter(
        i,
        s,
        coeffs,
        lits,
        suffix_sum,
        memo,
        clauses,
        next_var,
        Some((should_stop, poll_counter, interrupted)),
    )
}

/// Resolve a child node's value once it is guaranteed available: terminals are
/// computed inline (they are never stored in `memo`, matching the recursive
/// version), internal nodes are read from `memo`. The iterative post-order
/// traversal in [`build_bdd_iter`] guarantees every non-terminal child has been
/// finalized into `memo` before the parent that needs it is resolved.
fn bdd_child_node(
    i: usize,
    s: i128,
    coeffs: &[i128],
    suffix_sum: &[i128],
    memo: &HashMap<(usize, i128), BddNode>,
) -> BddNode {
    if s <= 0 {
        return BddNode::True;
    }
    if i >= coeffs.len() || suffix_sum[i] < s {
        return BddNode::False;
    }
    memo[&(i, s)]
}

/// One work item for the explicit-stack BDD construction.
enum BddWork {
    /// First visit of state `(i, s)`: run base/memo/poll checks and, for a fresh
    /// internal node, schedule its `Finish` plus the visits of its two children.
    Visit(usize, i128),
    /// Second visit of state `(i, s)`: both children are resolved; reduce, emit
    /// clauses, and record the node in `memo`.
    Finish(usize, i128),
}

/// Iterative (explicit-stack) BDD construction shared by [`build_bdd`] and
/// [`build_bdd_interruptible`].
///
/// This replaces the previous direct recursion, whose depth grew with the term
/// count `n` (the `low = build(i+1, s)` chain descends one index per level).
/// A wide single-literal objective row (e.g. `rail507`'s ~60k-term objective
/// upper-bound query `obj <= k`) drove that recursion ~n deep and overflowed the
/// stack. The traversal here keeps all state on the heap, so depth is bounded by
/// the heap, never the call stack.
///
/// Output is identical to the original recursion: variables are allocated in the
/// same post-order (the high child's whole subtree before the low child's, before
/// the node itself), clauses are emitted in the same per-node order, and `memo`
/// stores exactly the same non-terminal nodes. When `poll` is `Some`, the
/// deadline/memory hook is consulted on the same cadence and at the same
/// "new-state" boundaries as before; on a stop it sets `*interrupted` and returns
/// `BddNode::False` (the caller discards the partial result).
#[allow(clippy::too_many_arguments)]
fn build_bdd_iter<F>(
    root_i: usize,
    root_s: i128,
    coeffs: &[i128],
    lits: &[i32],
    suffix_sum: &[i128],
    memo: &mut HashMap<(usize, i128), BddNode>,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
    mut poll: Option<(&mut F, &mut u64, &mut bool)>,
) -> BddNode
where
    F: FnMut() -> bool,
{
    let mut stack: Vec<BddWork> = vec![BddWork::Visit(root_i, root_s)];

    while let Some(work) = stack.pop() {
        match work {
            BddWork::Visit(i, s) => {
                // Terminals are not pushed and not memoized (matches recursion).
                if s <= 0 {
                    continue;
                }
                if i >= coeffs.len() || suffix_sum[i] < s {
                    continue;
                }
                // Already finalized (DAG sharing): nothing to do. This is the
                // recursive memo-hit case, which neither polls nor re-descends.
                if memo.contains_key(&(i, s)) {
                    continue;
                }

                // Deadline / memory poll on a fixed cadence, counted at the
                // new-state boundary (a fresh memo miss) — exactly the work the
                // recursion charged. `i` strictly increases toward the children,
                // so a node is never its own ancestor and each fresh `(i, s)` is
                // visited (and thus charged) at most once before it is finalized.
                if let Some((should_stop, poll_counter, interrupted)) = poll.as_mut() {
                    **poll_counter += 1;
                    if poll_counter.is_multiple_of(BDD_STOP_POLL_INTERVAL) && should_stop() {
                        **interrupted = true;
                        return BddNode::False;
                    }
                }

                // Schedule this node's finalization, then its children, so the
                // high child resolves before the low child (LIFO: push low then
                // high), and both before this node — preserving the recursion's
                // post-order variable allocation and clause emission order.
                stack.push(BddWork::Finish(i, s));
                stack.push(BddWork::Visit(i + 1, s)); // low
                stack.push(BddWork::Visit(i + 1, s - coeffs[i])); // high
            }
            BddWork::Finish(i, s) => {
                // A node can be scheduled to finish only once: `Visit` schedules
                // `Finish` exactly when it first observes a memo miss, and the
                // subsequent `memo` insert below makes any later `Visit` of the
                // same state a memo hit (so no duplicate `Finish`).
                debug_assert!(!memo.contains_key(&(i, s)));

                let high = bdd_child_node(i + 1, s - coeffs[i], coeffs, suffix_sum, memo);
                let low = bdd_child_node(i + 1, s, coeffs, suffix_sum, memo);

                // Reduce: if both children are the same, skip this node.
                if high == low {
                    memo.insert((i, s), high);
                    continue;
                }

                // Create an auxiliary variable for this node.
                let sel = *next_var as i32;
                *next_var += 1;
                let node = BddNode::Internal(sel);

                let x = lits[i];

                match high {
                    BddNode::True => {}
                    BddNode::False => {
                        clauses.push(vec![-sel, -x]);
                    }
                    BddNode::Internal(h_sel) => {
                        clauses.push(vec![-sel, -x, h_sel]);
                    }
                }

                match low {
                    BddNode::True => {}
                    BddNode::False => {
                        clauses.push(vec![-sel, x]);
                    }
                    BddNode::Internal(l_sel) => {
                        clauses.push(vec![-sel, x, l_sel]);
                    }
                }

                memo.insert((i, s), node);
            }
        }
    }

    bdd_child_node(root_i, root_s, coeffs, suffix_sum, memo)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The interruptible BDD must produce byte-identical clauses and the same
    /// `next_var` as the plain `encode_bdd` when it is allowed to run to
    /// completion (never-stop). This is the no-regression guarantee: routing the
    /// interruptible path through `encode_bdd_interruptible` cannot change the
    /// encoding for any constraint that finishes within budget.
    #[test]
    fn interruptible_matches_plain_when_not_stopped() {
        let cases: &[(&[i128], &[i32], i128)] = &[
            (&[1, 1, 1, 1, 1], &[1, 2, 3, 4, 5], 3),
            (&[3, 2, 2, 1], &[1, -2, 3, 4], 4),
            (&[5, 4, 3, 2, 1], &[1, 2, 3, 4, 5], 7),
            (&[1, 1, 1, 1, 1, 1, 1, 1], &[1, 2, 3, 4, 5, 6, 7, 8], 5),
            (&[7, 5, 3, 2], &[-1, 2, -3, 4], 9),
        ];
        for (coeffs, lits, rhs) in cases {
            let mut plain_clauses: Vec<Vec<i32>> = Vec::new();
            let mut plain_next = 100u32;
            encode_bdd(coeffs, lits, *rhs, &mut plain_clauses, &mut plain_next);

            let mut int_clauses: Vec<Vec<i32>> = Vec::new();
            let mut int_next = 100u32;
            let mut never_stop = || false;
            let interrupted = encode_bdd_interruptible(
                coeffs,
                lits,
                *rhs,
                &mut int_clauses,
                &mut int_next,
                &mut never_stop,
            );

            assert!(
                !interrupted,
                "never-stop must not interrupt: {coeffs:?} >= {rhs}"
            );
            assert_eq!(
                plain_clauses, int_clauses,
                "clause sets diverged for {coeffs:?} >= {rhs}"
            );
            assert_eq!(
                plain_next, int_next,
                "next_var diverged for {coeffs:?} >= {rhs}"
            );
        }
    }

    /// An always-stop hook must make the interruptible build report interruption
    /// on a large enough row (where construction crosses at least one poll
    /// boundary). The build returns `true` so the caller discards the result.
    #[test]
    fn interruptible_bails_when_always_stopped() {
        // Wide cardinality row: O(n*rhs) BDD, far more than one poll interval of
        // fresh states, so the always-stop hook is consulted and trips.
        let n = 4000usize;
        let coeffs: Vec<i128> = vec![1; n];
        let lits: Vec<i32> = (1..=n as i32).collect();
        let rhs = (n / 2) as i128;

        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let mut next = (n as u32) + 1;
        let mut always_stop = || true;
        let interrupted = encode_bdd_interruptible(
            &coeffs,
            &lits,
            rhs,
            &mut clauses,
            &mut next,
            &mut always_stop,
        );
        assert!(interrupted, "always-stop must interrupt a wide BDD build");
    }

    /// A reference *recursive* BDD build, identical to the pre-iterative
    /// implementation. Used only as a test oracle to prove the iterative
    /// [`build_bdd`] emits byte-identical clauses and allocates variables in the
    /// same order on a broad sweep of rows.
    fn encode_bdd_recursive_reference(
        coeffs: &[i128],
        lits: &[i32],
        rhs: i128,
        clauses: &mut Vec<Vec<i32>>,
        next_var: &mut u32,
    ) {
        fn build_rec(
            i: usize,
            s: i128,
            coeffs: &[i128],
            lits: &[i32],
            suffix_sum: &[i128],
            memo: &mut HashMap<(usize, i128), BddNode>,
            clauses: &mut Vec<Vec<i32>>,
            next_var: &mut u32,
        ) -> BddNode {
            if s <= 0 {
                return BddNode::True;
            }
            if i >= coeffs.len() || suffix_sum[i] < s {
                return BddNode::False;
            }
            if let Some(&node) = memo.get(&(i, s)) {
                return node;
            }
            let high = build_rec(
                i + 1,
                s - coeffs[i],
                coeffs,
                lits,
                suffix_sum,
                memo,
                clauses,
                next_var,
            );
            let low = build_rec(i + 1, s, coeffs, lits, suffix_sum, memo, clauses, next_var);
            if high == low {
                memo.insert((i, s), high);
                return high;
            }
            let sel = *next_var as i32;
            *next_var += 1;
            let node = BddNode::Internal(sel);
            let x = lits[i];
            match high {
                BddNode::True => {}
                BddNode::False => clauses.push(vec![-sel, -x]),
                BddNode::Internal(h) => clauses.push(vec![-sel, -x, h]),
            }
            match low {
                BddNode::True => {}
                BddNode::False => clauses.push(vec![-sel, x]),
                BddNode::Internal(l) => clauses.push(vec![-sel, x, l]),
            }
            memo.insert((i, s), node);
            node
        }

        let n = coeffs.len();
        let mut order: Vec<usize> = (0..n).collect();
        order.sort_by(|&a, &b| coeffs[b].cmp(&coeffs[a]));
        let sorted_coeffs: Vec<i128> = order.iter().map(|&i| coeffs[i]).collect();
        let sorted_lits: Vec<i32> = order.iter().map(|&i| lits[i]).collect();
        let mut suffix_sum = vec![0i128; n + 1];
        for i in (0..n).rev() {
            suffix_sum[i] = suffix_sum[i + 1].saturating_add(sorted_coeffs[i]);
        }
        let mut memo: HashMap<(usize, i128), BddNode> = HashMap::new();
        let root = build_rec(
            0,
            rhs,
            &sorted_coeffs,
            &sorted_lits,
            &suffix_sum,
            &mut memo,
            clauses,
            next_var,
        );
        match root {
            BddNode::True => {}
            BddNode::False => clauses.push(Vec::new()),
            BddNode::Internal(sel) => clauses.push(vec![sel]),
        }
    }

    /// The iterative `encode_bdd` must produce byte-identical clauses and the
    /// same `next_var` as the reference recursion across a broad sweep of unit
    /// and weighted rows. This is the behavior-preservation guarantee for the
    /// recursion -> explicit-stack conversion.
    #[test]
    fn iterative_matches_recursive_reference() {
        // Deterministic LCG so the sweep is reproducible.
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut rng = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            state
        };

        for _ in 0..400 {
            let n = 1 + (rng() % 14) as usize;
            let mut coeffs: Vec<i128> = Vec::with_capacity(n);
            let mut lits: Vec<i32> = Vec::with_capacity(n);
            for k in 0..n {
                // Mix unit and small weighted coefficients.
                let c = 1 + (rng() % 5) as i128;
                coeffs.push(c);
                // Distinct variables, randomly polarized.
                let v = (k as i32) + 1;
                lits.push(if rng() & 1 == 0 { v } else { -v });
            }
            let total: i128 = coeffs.iter().sum();
            // rhs spanning trivial-true, interesting, and trivial-false ranges.
            let rhs = (rng() % (total as u64 + 3)) as i128;

            let mut rec_clauses: Vec<Vec<i32>> = Vec::new();
            let mut rec_next = 1000u32;
            encode_bdd_recursive_reference(&coeffs, &lits, rhs, &mut rec_clauses, &mut rec_next);

            let mut iter_clauses: Vec<Vec<i32>> = Vec::new();
            let mut iter_next = 1000u32;
            encode_bdd(&coeffs, &lits, rhs, &mut iter_clauses, &mut iter_next);

            assert_eq!(
                rec_clauses, iter_clauses,
                "clauses diverged for coeffs={coeffs:?} lits={lits:?} rhs={rhs}"
            );
            assert_eq!(
                rec_next, iter_next,
                "next_var diverged for coeffs={coeffs:?} lits={lits:?} rhs={rhs}"
            );
        }
    }

    /// Regression for the `rail507` default-path stack overflow: a wide
    /// single-literal cardinality row (here ~60k terms, like the objective
    /// upper-bound query `obj <= k`) drove the old recursion ~n deep and aborted
    /// the process with a stack overflow. The iterative build must encode it
    /// without crashing and emit a non-empty, satisfiable encoding.
    #[test]
    fn wide_cardinality_row_does_not_overflow_the_stack() {
        let n = 60_000usize;
        let coeffs: Vec<i128> = vec![1; n];
        let lits: Vec<i32> = (1..=n as i32).collect();
        // A "many true required" threshold so the BDD's low-chain is long — the
        // exact shape that overflowed the recursive build.
        let rhs = (n as i128) - 5;

        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let mut next = (n as u32) + 1;
        encode_bdd(&coeffs, &lits, rhs, &mut clauses, &mut next);

        // Constraint is satisfiable (e.g. all-true), so we must NOT have emitted
        // the empty (UNSAT) clause, and we must have produced some encoding.
        assert!(!clauses.is_empty(), "wide row produced no clauses");
        assert!(
            !clauses.iter().any(Vec::is_empty),
            "wide satisfiable row must not emit an empty (UNSAT) clause"
        );
    }
}

/// Builds BDD nodes and emits clauses, returning the node for "from index `i`,
/// we need at least `s` more weight".
///
/// Iterative (heap-bounded) wrapper over [`build_bdd_iter`]; see that function
/// for why the traversal is explicit-stack rather than recursive and for the
/// guarantee that the output matches the original recursion exactly.
fn build_bdd(
    i: usize,
    s: i128,
    coeffs: &[i128],
    lits: &[i32],
    suffix_sum: &[i128],
    memo: &mut HashMap<(usize, i128), BddNode>,
    clauses: &mut Vec<Vec<i32>>,
    next_var: &mut u32,
) -> BddNode {
    // No poll hook: the non-interruptible path never stops early.
    build_bdd_iter::<fn() -> bool>(
        i, s, coeffs, lits, suffix_sum, memo, clauses, next_var, None,
    )
}
