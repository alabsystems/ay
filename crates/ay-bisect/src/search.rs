// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binary-search minimization of feature-disable flag sets.
//!
//! Given a set of `--no-*` flags and a [`TrialRunner`], find a *minimal*
//! subset whose inclusion (i.e. disabling exactly those features) makes the
//! solver produce the expected verdict.
//!
//! ### Algorithm
//!
//! Starting from the full disable set (known to produce the expected verdict;
//! verified by the caller), halve it and run one trial per half:
//!   1. If the left half alone is sufficient, recurse into the left half.
//!   2. Else if the right half alone is sufficient, recurse into the right
//!      half.
//!   3. Else both halves are needed — recurse *within each half* while
//!      keeping the other half fixed.
//!
//! This is a straightforward generalisation of the "divide-and-conquer"
//! variant of delta-debugging; it is simpler than full ddmin but guarantees
//! minimality at the individual-flag level (removing any single flag from the
//! returned set breaks the fix).
//!
//! Parallelism: the two halves in step (1)/(2) are probed concurrently via
//! rayon when the caller configures `jobs > 1`; the caller owns the rayon
//! thread pool.

use std::sync::atomic::{AtomicUsize, Ordering};

use rayon::prelude::*;

use crate::error::Result;
use crate::runner::{Expected, SolveResult, TrialRunner};

/// Outcome classification used internally and exported via [`BisectResult`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TrialVerdict {
    /// Disabling this flag subset produces the expected verdict — good.
    Fixes,
    /// Disabling this flag subset does NOT produce the expected verdict.
    DoesNotFix,
}

/// Run a single trial with `flags` disabled and classify the verdict.
fn trial(
    runner: &dyn TrialRunner,
    flags: &[&str],
    expected: Expected,
    counter: &AtomicUsize,
) -> Result<TrialVerdict> {
    counter.fetch_add(1, Ordering::Relaxed);
    let verdict = runner.run(flags)?;
    Ok(classify(verdict, expected))
}

fn classify(verdict: SolveResult, expected: Expected) -> TrialVerdict {
    if verdict.matches(expected) {
        TrialVerdict::Fixes
    } else {
        TrialVerdict::DoesNotFix
    }
}

/// Binary-search minimization driver.
///
/// Preconditions (enforced by caller):
/// * `disable_all` trial **has already been verified** to `Fixes`.
/// * `flags` is the full flag universe in stable order.
///
/// Returns the minimal subset whose disabling preserves the fix.
pub(crate) fn minimize(
    runner: &dyn TrialRunner,
    flags: &[&'static str],
    expected: Expected,
    trials: &AtomicUsize,
) -> Result<Vec<&'static str>> {
    if flags.is_empty() {
        return Ok(Vec::new());
    }
    // Try to shrink: can we drop a half entirely?
    let current: Vec<&'static str> = flags.to_vec();
    shrink(runner, &current, expected, trials)
}

/// Recursive shrinker. Invariant: `current` (when passed as the flag set)
/// produces the expected verdict. We attempt to discard flags while
/// preserving that invariant, returning a 1-minimal subset.
fn shrink(
    runner: &dyn TrialRunner,
    current: &[&'static str],
    expected: Expected,
    trials: &AtomicUsize,
) -> Result<Vec<&'static str>> {
    if current.len() <= 1 {
        return Ok(current.to_vec());
    }

    let mid = current.len() / 2;
    let (left, right) = current.split_at(mid);

    // Probe both halves in parallel. Collecting into `Result<Vec<_>>` short-
    // circuits on the first error, so callers see the original runner error
    // without having to unwrap indexed elements.
    let left_vec = left.to_vec();
    let right_vec = right.to_vec();
    let probes: Vec<Vec<&'static str>> = vec![left_vec, right_vec];
    let verdicts: Vec<TrialVerdict> = probes
        .par_iter()
        .map(|subset| trial(runner, subset.as_slice(), expected, trials))
        .collect::<Result<Vec<_>>>()?;
    let left_verdict = verdicts[0];
    let right_verdict = verdicts[1];

    match (left_verdict, right_verdict) {
        (TrialVerdict::Fixes, _) => {
            // Left alone suffices — recurse into left.
            shrink(runner, left, expected, trials)
        }
        (_, TrialVerdict::Fixes) => {
            // Right alone suffices — recurse into right.
            shrink(runner, right, expected, trials)
        }
        (TrialVerdict::DoesNotFix, TrialVerdict::DoesNotFix) => {
            // Neither half is enough on its own: we need contributions from
            // both halves. Minimise each half while keeping the other fixed.
            let left_min = shrink_with_context(runner, left, right, expected, trials)?;
            let right_min = shrink_with_context(runner, right, &left_min, expected, trials)?;
            let mut combined = left_min;
            combined.extend(right_min);
            Ok(combined)
        }
    }
}

/// Minimise `focus` while always keeping `context` disabled too. We search
/// the smallest subset of `focus` such that `focus_subset ∪ context` still
/// produces the expected verdict.
fn shrink_with_context(
    runner: &dyn TrialRunner,
    focus: &[&'static str],
    context: &[&'static str],
    expected: Expected,
    trials: &AtomicUsize,
) -> Result<Vec<&'static str>> {
    if focus.len() <= 1 {
        // Single-flag focus: we already know focus+context fixes (by the
        // caller's invariant chain), so the focus element is necessary.
        return Ok(focus.to_vec());
    }

    let mid = focus.len() / 2;
    let (left, right) = focus.split_at(mid);

    let combined_left = combine(left, context);
    let combined_right = combine(right, context);
    let probes: Vec<Vec<&'static str>> = vec![combined_left, combined_right];
    let verdicts: Vec<TrialVerdict> = probes
        .par_iter()
        .map(|subset| trial(runner, subset.as_slice(), expected, trials))
        .collect::<Result<Vec<_>>>()?;
    let left_verdict = verdicts[0];
    let right_verdict = verdicts[1];

    match (left_verdict, right_verdict) {
        (TrialVerdict::Fixes, _) => shrink_with_context(runner, left, context, expected, trials),
        (_, TrialVerdict::Fixes) => shrink_with_context(runner, right, context, expected, trials),
        (TrialVerdict::DoesNotFix, TrialVerdict::DoesNotFix) => {
            // Both halves contribute. Recurse on each, fixing the other +
            // context.
            let left_ctx: Vec<&'static str> = right.iter().chain(context.iter()).copied().collect();
            let left_min = shrink_with_context(runner, left, &left_ctx, expected, trials)?;
            let right_ctx: Vec<&'static str> =
                left_min.iter().chain(context.iter()).copied().collect();
            let right_min = shrink_with_context(runner, right, &right_ctx, expected, trials)?;
            let mut combined = left_min;
            combined.extend(right_min);
            Ok(combined)
        }
    }
}

fn combine(a: &[&'static str], b: &[&'static str]) -> Vec<&'static str> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    out.extend_from_slice(a);
    out.extend_from_slice(b);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    /// Mock runner: the "bug" is fixed iff the enabled set contains all flags
    /// in `required`. All other flags are irrelevant.
    struct MockRunner {
        required: Vec<&'static str>,
        /// Expected verdict to return when the required flags are present.
        pass_verdict: SolveResult,
        /// Verdict to return when required flags are missing.
        fail_verdict: SolveResult,
        history: Mutex<Vec<Vec<String>>>,
    }

    impl MockRunner {
        fn new(required: Vec<&'static str>) -> Self {
            Self {
                required,
                pass_verdict: SolveResult::Sat,
                fail_verdict: SolveResult::Unsat,
                history: Mutex::new(Vec::new()),
            }
        }
    }

    impl TrialRunner for MockRunner {
        fn run(&self, flags: &[&str]) -> Result<SolveResult> {
            self.history
                .lock()
                .expect("mutex poisoned")
                .push(flags.iter().map(|s| (*s).to_string()).collect());
            let all_present = self.required.iter().all(|r| flags.contains(r));
            Ok(if all_present {
                self.pass_verdict
            } else {
                self.fail_verdict
            })
        }
    }

    #[test]
    fn test_shrink_single_flag_required() {
        let runner = MockRunner::new(vec!["--no-bve"]);
        let trials = AtomicUsize::new(0);
        let flags = vec!["--no-bve", "--no-vivify", "--no-probe", "--no-subsume"];
        let min = minimize(&runner, &flags, Expected::Sat, &trials).expect("minimize");
        assert_eq!(min, vec!["--no-bve"]);
    }

    #[test]
    fn test_shrink_pair_required() {
        let runner = MockRunner::new(vec!["--no-bve", "--no-probe"]);
        let trials = AtomicUsize::new(0);
        let flags = vec![
            "--no-preprocess",
            "--no-bve",
            "--no-vivify",
            "--no-probe",
            "--no-subsume",
            "--no-bce",
        ];
        let min = minimize(&runner, &flags, Expected::Sat, &trials).expect("minimize");
        let set: std::collections::HashSet<_> = min.iter().copied().collect();
        assert!(set.contains("--no-bve"), "missing --no-bve in {min:?}");
        assert!(set.contains("--no-probe"), "missing --no-probe in {min:?}");
        assert_eq!(min.len(), 2, "expected minimal pair, got {min:?}");
    }

    #[test]
    fn test_minimize_empty_flags_returns_empty() {
        let runner = MockRunner::new(vec![]);
        let trials = AtomicUsize::new(0);
        let min = minimize(&runner, &[], Expected::Sat, &trials).expect("minimize");
        assert!(min.is_empty());
        assert_eq!(trials.load(Ordering::Relaxed), 0);
    }
}
