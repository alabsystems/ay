// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded integer enumeration for NIA solver.
//!
//! When all variables in nonlinear monomials have finite integer bounds
//! and the total domain size is small (product of ranges < threshold),
//! enumerate all integer points to find a satisfying assignment or prove
//! UNSAT definitively.
//!
//! This handles practical bounded NIA problems like `x^2 = 9, -5 <= x <= 5`
//! and `x*y = 7, 1 <= x <= 2, 1 <= y <= 2` that tangent planes cannot solve.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::BTreeMap;

use ay_core::TheoryResult;

use super::*;

/// Maximum total domain size for bounded enumeration (product of all variable ranges).
const MAX_ENUM_DOMAIN: i64 = 10_000;

/// Points between wall-clock deadline polls inside a point-enumeration loop
/// (#nia-enum-deadline).
///
/// The enumeration loops in this file and in `factor_split.rs` evaluate every
/// asserted atom by EXACT BigInt substitution at every point, so one point is
/// already tens of microseconds on a dense atom set; 256 of them bound the
/// post-deadline overshoot to well under a millisecond while making the clock
/// read itself (a `checked_duration_since` on a cached `Instant`) unmeasurable
/// against the evaluation cost.
const ENUM_DEADLINE_POLL_POINTS: i64 = 256;

#[cfg(test)]
thread_local! {
    /// Test-only count of deadline polls actually performed by
    /// [`NiaSolver::enum_deadline_expired`] on the current thread
    /// (#nia-enum-deadline).
    ///
    /// ANTI-VACUITY INSTRUMENT. The property this module has to hold is that
    /// the clock is read *while* a box is being walked, not merely once on
    /// entry: an entry-only poll is exactly the shape that spun for 7h12m
    /// inside a single `try_capped_model_search` activation. Wall-clock
    /// assertions do not pin that — under `--release` the full 10_000-point
    /// box takes tens of microseconds here, so a 1 ms budget is never reached
    /// and any timing assertion passes vacuously. Counting the polls pins it
    /// exactly and without a clock: an entry-only poll counts 1, a correctly
    /// polling walk counts `ceil(points / ENUM_DEADLINE_POLL_POINTS)`.
    pub(crate) static ENUM_DEADLINE_POLLS: std::cell::Cell<u64> =
        const { std::cell::Cell::new(0) };
}

/// Reset the thread's poll counter and return the previous value (test-only).
#[cfg(test)]
pub(crate) fn reset_enum_deadline_polls() -> u64 {
    ENUM_DEADLINE_POLLS.with(|n| n.replace(0))
}

/// Polls performed on this thread since the last reset (test-only).
#[cfg(test)]
pub(crate) fn enum_deadline_polls() -> u64 {
    ENUM_DEADLINE_POLLS.with(std::cell::Cell::get)
}

impl NiaSolver<'_> {
    /// Wall-clock poll for the point-enumeration loops (#nia-enum-deadline).
    ///
    /// `visited` is the number of points ALREADY examined in the current loop,
    /// so the very first call (`visited == 0`) polls, and an already-expired
    /// deadline aborts before a single point is evaluated.
    ///
    /// ## Why the enumerations must poll at all
    ///
    /// `NiaSolver::deadline` was polled in exactly ONE place
    /// (`check_loop.rs`, at each refinement-iteration boundary), which is only
    /// sound as a budget if every call made from that loop returns quickly.
    /// The enumerations do not: `try_capped_model_search` alone walks up to
    /// [`MAX_ENUM_DOMAIN`] points and is re-entered on every `NeedSplit`, and
    /// an odometer that overflowed past its bound walked ~2^64 of them —
    /// measured 2026-09-11 as 7h12m of silent full-CPU spinning inside
    /// `compiler_consumer`, on a 15 s per-obligation budget, with the deadline sitting
    /// live and unread in `self.deadline` the whole time.
    ///
    /// ## Why aborting is always sound here
    ///
    /// Every caller of this helper returns `None` on expiry. `None` is each
    /// enumeration's EXISTING "no claim" answer — "not applicable" for the
    /// exhaustive decider, "no witness found" for the SAT-only searches — so
    /// an abort can never manufacture `Sat` or `Unsat`; it can only lose
    /// completeness, and the caller reports the `Unknown` it would otherwise
    /// have reported. In particular the exhaustive decider must NOT fall out
    /// of its loop on expiry: falling out means "box exhausted", which is its
    /// `Unsat` claim.
    pub(crate) fn enum_deadline_expired(&self, visited: i64) -> bool {
        if visited % ENUM_DEADLINE_POLL_POINTS != 0 {
            return false;
        }
        #[cfg(test)]
        ENUM_DEADLINE_POLLS.with(|n| n.set(n.get() + 1));
        self.should_timeout()
    }
    /// True if any asserted atom contains a SCALED nonlinear product
    /// (`(* c x y)` with a constant factor, hence not registered as a monomial —
    /// see #nia-const-factor). Such problems have no registered monomials, so the
    /// check loop's `!self.monomials.is_empty()` gates would skip bounded
    /// enumeration; this lets the loop still attempt the exact enumeration
    /// decider for them (sound — `check_assignment` is fail-closed).
    pub(crate) fn has_scaled_product_vars(&self) -> bool {
        let mut vars: Vec<TermId> = Vec::new();
        for &(term, _) in &self.asserted {
            self.collect_scaled_product_vars(term, &mut vars);
            if !vars.is_empty() {
                return true;
            }
        }
        false
    }

    /// Try bounded enumeration over all monomial variables.
    ///
    /// Returns `Some(TheoryResult)` if enumeration succeeds (either SAT or UNSAT),
    /// or `None` if enumeration is not applicable (missing bounds, domain too large).
    pub(crate) fn try_bounded_enumeration(&mut self) -> Option<TheoryResult> {
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();

        // SOUNDNESS (#nia-enum-tentative): bounded enumeration is a standalone
        // decision procedure that reasons over the variables' *genuine* integer
        // bounds (from asserted constraints, read via `get_integer_bounds`). It
        // must therefore NOT see the speculative bounds injected by tentative
        // model patching — `try_integer_rounding`/`try_tentative_patch` add tight
        // Gomory cuts (e.g. `x >= 8 ∧ x <= 8`) that pin factors to a *guessed*
        // model point inside a `push`ed LIA scope. Left active, those cuts collapse
        // the enumeration box to a single guessed point: e.g. for
        // `x+y=10 ∧ x*y=24 ∧ x>=0 ∧ y>=0`, rounding guesses x=8,y=2, and enumerating
        // only [8,8]×[2,2] (where x*y=16≠24) yields a WRONG UNSAT even though
        // x=4,y=6 is a genuine model. Undo all tentative scopes first so the box is
        // derived solely from real constraints; speculative narrowing could only
        // ever excise real models and produce a spurious UNSAT.
        self.undo_tentative_patch();

        // Collect unique variables from all monomials
        let mut vars: Vec<TermId> = Vec::new();
        for mon in self.monomials.values() {
            for &v in &mon.vars {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        // Also collect variable factors from SCALED nonlinear products
        // (`(* c x y)` with a constant factor c != 1). These are deliberately
        // NOT registered as monomials (#nia-const-factor: the monomial invariant
        // requires `aux == product(vars)`, which a constant factor breaks), so
        // the linearization never sees them. Bounded enumeration, however,
        // evaluates the ORIGINAL `*` term via `eval_term` — which multiplies the
        // constant in exactly — so it can decide such constraints SOUNDLY by
        // exhaustive search. Adding these factor vars lets enumeration recover
        // the bounded scaled-monomial cases without re-introducing the unsound
        // linearization. `check_assignment` is fail-closed: any atom it cannot
        // evaluate exactly yields Unknown, so this only ever adds decisions.
        for &(term, _) in &self.asserted {
            self.collect_scaled_product_vars(term, &mut vars);
        }
        // Sort for deterministic enumeration order
        vars.sort_by_key(|t| t.0);

        if vars.is_empty() {
            return None;
        }

        // Phase 1: Get direct integer bounds from LRA — JUSTIFIED bounds only
        // (see `get_integer_bounds`).
        let mut var_bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::default();

        for &var in &vars {
            let (lo, hi) = match self.get_integer_bounds(var) {
                Some((lo, hi)) => (Some(lo), Some(hi)),
                None => {
                    // Try partial bounds
                    let (lo_opt, hi_opt) = self.get_partial_integer_bounds(var);
                    (lo_opt, hi_opt)
                }
            };
            var_bounds.insert(var, (lo, hi));
        }
        self.apply_asserted_integer_bounds(&vars, &mut var_bounds);

        // Phase 2: Infer missing bounds from monomial constraints.
        // If aux = x*y and aux has an upper bound U and x has lower bound L > 0,
        // then y <= floor(U/L). Similarly for other missing directions.
        //
        // Also check for equality constraints (= area (* w h)) where `area`
        // has bounds but the monomial aux variable doesn't directly.
        let mut changed = true;
        let max_inference_rounds = 5;
        for _ in 0..max_inference_rounds {
            if !changed {
                break;
            }
            changed = false;
            for mon in self.monomials.values() {
                // Get bounds on the auxiliary variable (the product term).
                // Also check if an asserted equality links the monomial to
                // another variable that has bounds (e.g., area = w*h).
                let (aux_lo, aux_hi) = self.get_monomial_bounds(mon);

                // For each variable in the monomial, try to derive missing bounds
                for (i, &var) in mon.vars.iter().enumerate() {
                    let (cur_lo, cur_hi) = var_bounds.get(&var).copied().unwrap_or((None, None));

                    // Collect other factors' bounds
                    let other_factors: Vec<_> = mon
                        .vars
                        .iter()
                        .enumerate()
                        .filter(|&(j, _)| j != i)
                        .map(|(_, &v)| var_bounds.get(&v).copied().unwrap_or((None, None)))
                        .collect();

                    // Infer upper bound: if aux <= U and all other factors >= L > 0
                    if cur_hi.is_none() {
                        if let Some(u) = aux_hi {
                            if u > 0 {
                                let all_others_positive: Option<i64> =
                                    other_factors.iter().try_fold(1i64, |acc, (lo, _)| {
                                        lo.and_then(
                                            |l| {
                                                if l > 0 {
                                                    acc.checked_mul(l)
                                                } else {
                                                    None
                                                }
                                            },
                                        )
                                    });
                                if let Some(other_product) = all_others_positive {
                                    if other_product > 0 {
                                        let inferred_hi = u / other_product;
                                        var_bounds.insert(var, (cur_lo, Some(inferred_hi)));
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }

                    // Infer lower bound: if aux >= L > 0 and every OTHER factor is
                    // strictly positive (lo > 0), then var = aux / product_of_others
                    // >= L / product_of_uppers, so var >= ceil(L / product_of_uppers).
                    //
                    // The strict-positivity guard on the other factors' LOWER bounds is
                    // REQUIRED for soundness, exactly as the upper-bound inference above
                    // demands `all_others_positive`. Checking only that the other factors'
                    // UPPER bounds are positive (`h > 0`) is UNSOUND: a factor that can be
                    // negative (e.g. bounds [-10, 3]) leaves the product's sign undetermined,
                    // and dividing the inequality by it does not preserve direction. Concretely
                    // for (x*y >= 6) with y in [-10, 3] and x bounded only above, the old code
                    // clamped x >= ceil(6/3) = 2 and excised the negative-product cone
                    // (x=-4, y=-10 gives x*y = 40 >= 6), enumerated an empty box, and returned a
                    // spurious UNSAT -> a false-PROVE on the no-proof-check subprocess path. When
                    // the sign is not pinned positive we skip the inference, leaving the bound
                    // open so Phase 3 yields Unknown (sound) rather than a wrong UNSAT.
                    if cur_lo.is_none() {
                        if let Some(l) = aux_lo {
                            if l > 0 {
                                let others_all_positive = other_factors
                                    .iter()
                                    .all(|(lo, _)| lo.is_some_and(|l| l > 0));
                                let all_others_upper: Option<i64> =
                                    if others_all_positive {
                                        other_factors.iter().try_fold(1i64, |acc, (_, hi)| {
                                            hi.and_then(|h| {
                                                if h > 0 {
                                                    acc.checked_mul(h)
                                                } else {
                                                    None
                                                }
                                            })
                                        })
                                    } else {
                                        None
                                    };
                                if let Some(other_product) = all_others_upper {
                                    if other_product > 0 {
                                        // var >= ceil(l / other_product).
                                        //
                                        // Both operands are guarded `> 0` above, so the
                                        // quotient lies in `[1, l]` and always fits an
                                        // i64 — but the textbook `(l + d - 1) / d` does
                                        // NOT: its intermediate sum PANICS ("attempt to
                                        // add with overflow") once `l` sits within `d`
                                        // of i64::MAX. A refuter reached exactly that
                                        // with a 3-assertion QF_NIA input (the
                                        // regression test rebuilds the shape: `x*y =
                                        // i64::MAX`, `y ∈ [1, 2]`, `x <= 10`), and NIA
                                        // runs IN-PROCESS inside compiler_consumer, so the panic
                                        // is an ICE that kills the compilation, not a
                                        // verdict. `(l - 1) / d + 1` is the same ceiling
                                        // (`l - 1 >= 0`, quotient `<= l - 1`, `+ 1 <=
                                        // l`) and cannot overflow for `l >= 1`,
                                        // `d >= 1`. Unlike the domain-size check below
                                        // there is nothing uncomputable here — only the
                                        // intermediate was mis-shaped — so the bound is
                                        // computed exactly rather than declined or
                                        // saturated. A saturated `i64::MAX / d` is the
                                        // FLOOR at the rim, one below the ceiling: still
                                        // sound (weaker, never model-excising) but
                                        // incomplete — it widens the box by a point,
                                        // which is enough to push a domain sitting at
                                        // MAX_ENUM_DOMAIN over the cap, turning a
                                        // provable Unsat into a decline (the regression
                                        // test's exactness companion pins that).
                                        let inferred_lo = (l - 1) / other_product + 1;
                                        let new_lo = cur_lo
                                            .map(|old| old.max(inferred_lo))
                                            .unwrap_or(inferred_lo);
                                        let cur_hi_now = var_bounds.get(&var).and_then(|b| b.1);
                                        var_bounds.insert(var, (Some(new_lo), cur_hi_now));
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Phase 2.5: interval contraction over the asserted atoms
        // (#nia-interval-contract, interval_contract.rs). Derives bounds that
        // flow only THROUGH nonlinear atoms — e.g. for `x*x = 2*y*y + 1` with
        // `100 < x < 130`, it derives `y ∈ [-91, 91]` (since `y*y =
        // (x*x-1)/2 <= 8320`), completing the finite box so the exhaustive
        // decider below can run. Sound: pure bounds tightening (every removed
        // value provably violates some asserted atom); never produces a
        // verdict by itself.
        let (derived_reasons, contract_refuted) = self.contract_enum_bounds(&vars, &mut var_bounds);
        // Deadline discipline (#nia-enum-deadline): an expired budget
        // forbids claiming any verdict out of this decider, the
        // contraction refutation included — poll before claiming it.
        if contract_refuted && !self.enum_deadline_expired(0) {
            // #nia-contract-empty-refutes: interval contraction over the
            // justified seed bounds produced an empty interval — the
            // asserted literals are jointly unsatisfiable. This decides
            // searched trails whose refutation is pure bound propagation
            // through nonlinear atoms (VeryMax: a sibling disjunct's
            // negated Farkas atom pushes the shared factor's seed bound
            // against the compound-equality bound), where no complete
            // factor box ever forms. Conflict cites every asserted
            // literal, the same cover exhaustive enumeration uses.
            // Conflict shrinking (#nia-contract-subset-refutes): the
            // full cover (~100 literals on searched trails) blocks
            // exactly one Boolean trail in the CEGAR loop. Try to
            // re-derive emptiness from the relevant literals alone
            // (subset seeds, subset-filtered lookups — sound by
            // construction), then greedy-delete while it still
            // refutes. Any failure falls back to the full cover.
            let conflict = self
                .minimized_contract_conflict(&vars)
                .unwrap_or_else(|| self.full_conflict_lits());
            if self.enum_deadline_expired(0) {
                return None;
            }
            return Some(TheoryResult::Unsat(conflict));
        }
        // #nia-mccormick-contracted-bounds: stash the contracted box for
        // the McCormick envelopes added later in this check. The seeds
        // above are justified bounds only (Phase 1) plus algebraic
        // consequences of asserted atoms (Phase 2 / contraction), and
        // tentative scopes were undone at entry, so every endpoint here
        // is implied by the current asserted literals.
        self.contracted_bounds.clone_from(&var_bounds);
        self.contracted_bound_reasons = derived_reasons;

        // Phase 3: Convert to var_ranges, checking all variables have complete bounds
        let mut var_ranges: Vec<(TermId, i64, i64)> = Vec::new();
        for &var in &vars {
            let (lo_opt, hi_opt) = var_bounds.get(&var).copied().unwrap_or((None, None));
            match (lo_opt, hi_opt) {
                (Some(lo), Some(hi)) if lo <= hi => {
                    var_ranges.push((var, lo, hi));
                }
                _ => {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Bounded enum: incomplete bounds for {:?}: lo={:?}, hi={:?}",
                            var,
                            lo_opt,
                            hi_opt
                        );
                    }
                    return None;
                }
            }
        }

        // Compute total domain size, checking for overflow
        let mut domain_size: i64 = 1;
        for &(_, lo, hi) in &var_ranges {
            // `hi - lo + 1` in `i64` PANICS on a wide bound pair — measured
            // 2026-09-07 as `attempt to subtract with overflow` at this line,
            // 20 times, while compiler_consumer was verifying `ty`'s workspace. The solver
            // runs IN-PROCESS inside the compiler, so an arithmetic panic here
            // is not a solver error the caller can handle: it takes the whole
            // rustc process down with an ICE, and the crate under verification
            // reports nothing at all.
            //
            // The bounds come from the LRA layer and are attacker-shaped in the
            // sense that matters here — they are whatever the input formula
            // implies, including `i64::MIN`/`i64::MAX`. The very next line
            // already uses `checked_mul`, so the intent was overflow-safe; the
            // subtraction and the `+ 1` were simply missed.
            //
            // Declining (`None`) is the right answer, not saturating: this
            // function is an admission test for enumerating a bounded domain,
            // and a range too wide to compute is exactly a domain too wide to
            // enumerate. Saturating would hand the loop below a fabricated size.
            let range = hi.checked_sub(lo).and_then(|d| d.checked_add(1))?;
            if range <= 0 {
                // Empty range — already handled by LRA
                return None;
            }
            domain_size = domain_size.checked_mul(range)?;
            if domain_size > MAX_ENUM_DOMAIN {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Bounded enum: domain size {} exceeds threshold {}",
                        domain_size,
                        MAX_ENUM_DOMAIN
                    );
                }
                return None;
            }
        }

        if self.debug {
            safe_eprintln!(
                "[NIA] Bounded enum: {} vars, domain size {}, ranges: {:?}",
                var_ranges.len(),
                domain_size,
                var_ranges
                    .iter()
                    .map(|(v, lo, hi)| format!("{v:?}:[{lo},{hi}]"))
                    .collect::<Vec<_>>()
            );
        }

        // Enumerate all integer points
        let n = var_ranges.len();
        let mut assignment: Vec<i64> = var_ranges.iter().map(|&(_, lo, _)| lo).collect();
        // Points examined so far: drives the deadline poll and the defensive
        // visit bound below.
        let mut visited: i64 = 0;

        loop {
            // Wall-clock abort (#nia-enum-deadline). MUST be a `return None`,
            // not a `break`: breaking out of this loop is the "box exhausted"
            // exit and claims Unsat. `None` means "enumeration not applicable"
            // and leaves the caller at the sound `unknown`.
            if self.enum_deadline_expired(visited) {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Bounded enum: wall-clock deadline exceeded after {visited} \
                         points — returning None (unknown), no UNSAT claim"
                    );
                }
                return None;
            }
            // Defensive visit bound (#nia-enum-visit-bound). A correct odometer
            // exhausts the admitted box in exactly `domain_size` points and
            // leaves through the `carry` break below, so this is unreachable;
            // it exists so that a future odometer defect costs a declined
            // enumeration rather than an unbounded spin. Declining (not
            // breaking) is the sound choice: fewer than `domain_size` DISTINCT
            // points may have been seen, so no UNSAT claim is available.
            if visited >= domain_size {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Bounded enum: visit bound {domain_size} reached without the \
                         odometer signalling exhaustion — returning None (unknown)"
                    );
                }
                return None;
            }
            visited += 1;

            // Check if this assignment satisfies all active constraints. If
            // any asserted atom is opaque to this evaluator, enumeration is
            // not a sound decision procedure for this formula.
            match self.check_assignment(&vars, &assignment) {
                Some(true) => {
                    self.record_bounded_enum_model(&vars, &assignment);
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Bounded enum: SAT with assignment {:?}",
                            vars.iter()
                                .zip(assignment.iter())
                                .map(|(v, a)| format!("{v:?}={a}"))
                                .collect::<Vec<_>>()
                        );
                    }
                    return Some(TheoryResult::Sat);
                }
                Some(false) => {}
                None => {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Bounded enum: unsupported asserted constraint; returning Unknown"
                        );
                    }
                    return None;
                }
            }

            // Advance to next point (odometer-style increment).
            //
            // Compare BEFORE incrementing. The previous shape — `+= 1`, then
            // `> hi` — overflowed on a digit whose `hi == i64::MAX`: the last
            // step computes `i64::MAX + 1` before it ever looks at the bound,
            // and under `overflow-checks = true` (every profile here) that is
            // a panic inside compiler_consumer, i.e. an ICE. Such a box IS admitted: the
            // domain-size check above only caps `hi - lo + 1`, so `[i64::MAX -
            // 3, i64::MAX]` (width 4) passes. Same points, same order — a
            // digit `a` in `[lo, hi]` advances to `a + 1` exactly when `a <
            // hi` (the old `a + 1 > hi` test negated) and otherwise wraps to
            // `lo` and carries, and the invariant `a ∈ [lo, hi]` holds because
            // the box was checked non-empty (`range > 0`) above.
            let mut carry = true;
            for i in (0..n).rev() {
                if carry {
                    if assignment[i] < var_ranges[i].2 {
                        assignment[i] += 1;
                        carry = false;
                    } else {
                        assignment[i] = var_ranges[i].1;
                        // carry continues
                    }
                }
            }
            if carry {
                // All points exhausted
                break;
            }
        }

        // No satisfying assignment found — return UNSAT
        if self.debug {
            safe_eprintln!(
                "[NIA] Bounded enum: UNSAT after exhaustive search of {} points",
                domain_size
            );
        }

        Some(TheoryResult::Unsat(self.full_conflict_lits()))
    }

    /// Shrink an interval-contraction refutation to a relevant subset
    /// of the asserted literals (#nia-contract-subset-refutes), or
    /// `None` when the subset alone does not refute (caller falls back
    /// to the full cover). Greedy deletion is capped in oracle calls;
    /// every accepted subset is re-verified by
    /// `contract_subset_refutes`, so the result is sound regardless of
    /// where the cap stops.
    fn minimized_contract_conflict(&self, vars: &[TermId]) -> Option<Vec<TheoryLit>> {
        const MAX_SHRINK_CALLS: usize = 96;
        let mut relevant: std::collections::BTreeSet<TermId> = Default::default();
        relevant.extend(vars.iter().copied());
        relevant.extend(self.monomials.values().map(|m| m.aux_var));
        let mut subset: Vec<(TermId, bool)> = self
            .asserted
            .iter()
            .copied()
            .filter(|&(term, _)| self.atom_mentions_any(term, &relevant))
            .collect();
        if subset.len() >= self.asserted.len() || !self.contract_subset_refutes(&subset) {
            return None;
        }
        let mut calls = 1usize;
        let mut i = 0usize;
        while i < subset.len() && calls < MAX_SHRINK_CALLS {
            if self.enum_deadline_expired(calls as i64) {
                break;
            }
            let removed = subset.remove(i);
            calls += 1;
            if self.contract_subset_refutes(&subset) {
                // Still refutes without it: keep the deletion.
            } else {
                subset.insert(i, removed);
                i += 1;
            }
        }
        Some(
            subset
                .into_iter()
                .map(|(term, value)| TheoryLit { term, value })
                .collect(),
        )
    }

    /// Capped finite-domain search for a SATISFYING assignment ONLY
    /// (#nia-capped-search).
    ///
    /// `try_bounded_enumeration` requires a *complete, sound* finite box for
    /// every variable so it can decide both SAT and UNSAT. Many genuinely
    /// satisfiable search-heavy QF_NIA problems have no such box: e.g. the
    /// Pythagorean query `a>0 ∧ b>0 ∧ a*a+b*b = c*c ∧ c<10` is SAT (3,4,5) yet
    /// `c` is unbounded BELOW (`c<10` only caps it above; `c=-100` is also a
    /// model), so `a` and `b` have no upper bound and the exhaustive decider
    /// soundly bails to `unknown`.
    ///
    /// This routine fills that completeness gap WITHOUT ever sacrificing
    /// soundness: it imposes an ARTIFICIAL finite search window on each variable
    /// (using its genuine bounds where present, and a bounded cap otherwise),
    /// enumerates that window, and returns `Some(Sat)` ONLY for a point that
    /// `check_assignment` verifies against EVERY asserted atom by exact integer
    /// substitution (fail-closed — any atom it cannot evaluate yields `None`).
    /// A verified witness is a genuine model regardless of how the window was
    /// chosen, so the SAT verdict is sound.
    ///
    /// Crucially it can NEVER return UNSAT: the window is an arbitrary cap, not
    /// an entailed bound, so exhausting it proves nothing. When no witness is
    /// found it returns `None`, leaving the caller at the sound `unknown` it
    /// would otherwise have produced. This is therefore a pure completeness
    /// improvement (turns some `unknown` into a checked `sat`) with zero
    /// soundness risk — it can only ever turn `unknown` into `sat`, never into
    /// `unsat`, and never produces an `unsat` at all.
    pub(crate) fn try_capped_model_search(&mut self) -> Option<TheoryResult> {
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();

        // Soundness mirror of try_bounded_enumeration: speculative tentative
        // patch scopes must not narrow the (already artificial) window further,
        // since that could hide a real model and there is no UNSAT risk to
        // offset. Undo them so the genuine bounds are visible.
        self.undo_tentative_patch();

        // Collect the same variable set the exhaustive decider would use:
        // monomial factor variables plus scaled-product factor variables.
        let mut vars: Vec<TermId> = Vec::new();
        for mon in self.monomials.values() {
            for &v in &mon.vars {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        for &(term, _) in &self.asserted {
            self.collect_scaled_product_vars(term, &mut vars);
        }
        // Completeness fix (#nia-capped-residual): also enumerate the ordinary
        // Int-variable leaves of every asserted atom, not just monomial/scaled
        // factors. Without them a satisfiable query like `x*x = k*y` (x a
        // monomial factor, y linear) leaves `y` unassigned, so
        // `check_assignment` fail-closes to `None` on every candidate and no
        // witness can ever be verified. Assigning ALL leaves lets the exact
        // evaluator decide each atom. Widening the set is SAT-sound: it can only
        // let more genuine witnesses be verified (every returned point is still
        // exact-checked against every atom), never manufacture a false one, and
        // never removes a previously-found witness (those had all-monomial-var
        // atoms, so their leaf set is unchanged).
        for &(term, _) in &self.asserted {
            self.collect_int_var_leaves(term, &mut vars);
        }
        vars.sort_by_key(|t| t.0);
        if vars.is_empty() {
            return None;
        }

        // Gather whatever genuine integer bounds exist for each variable.
        let mut var_bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::default();
        for &var in &vars {
            let (lo, hi) = match self.get_integer_bounds(var) {
                Some((lo, hi)) => (Some(lo), Some(hi)),
                None => self.get_partial_integer_bounds(var),
            };
            var_bounds.insert(var, (lo, hi));
        }
        self.apply_asserted_integer_bounds(&vars, &mut var_bounds);

        // First compute the product of all *genuinely bounded* ranges. These
        // consume budget that cannot be shrunk (they are real constraints), so
        // they determine how much of MAX_ENUM_DOMAIN remains for the artificial
        // windows. A genuinely empty real range (lo > hi) means no model.
        let mut bounded_product: i64 = 1;
        let mut capped_count: u32 = 0;
        for &var in &vars {
            match var_bounds.get(&var).copied().unwrap_or((None, None)) {
                (Some(lo), Some(hi)) => {
                    if lo > hi {
                        return None;
                    }
                    let range = hi.checked_sub(lo)?.checked_add(1)?;
                    bounded_product = bounded_product.checked_mul(range)?;
                    if bounded_product > MAX_ENUM_DOMAIN {
                        // The real (non-artificial) box alone already exceeds the
                        // budget — exhaustive enumeration would have handled this
                        // had it fit, so just give up (sound: returns None).
                        return None;
                    }
                }
                _ => capped_count += 1,
            }
        }

        // Pick the largest per-window half-width `cap` such that the total
        // search box `bounded_product * (2*cap+1)^capped_count` still fits the
        // budget. A one-sided cap uses the same window length `2*cap+1`. With
        // `cap` chosen this way the search box never exceeds MAX_ENUM_DOMAIN, so
        // the search is always small regardless of how many variables are
        // unbounded; if even `cap == 1` would not fit, we bail (None/unknown).
        let cap = if capped_count == 0 {
            // Every variable has genuine two-sided bounds, so no artificial
            // window is ever built: each `var_ranges` entry below takes the
            // `(Some(lo), Some(hi))` arm and `cap` is never read. Without this
            // short-circuit the probe below still runs — its inner
            // `for _ in 0..capped_count` body never executes, so `fits` stays
            // true and the loop exits only on `c > MAX_ENUM_DOMAIN`: 10_000
            // unpolled iterations computing a value nobody uses, inside the
            // very routine this file is hardening against unpolled loops
            // (#nia-enum-cap-probe).
            0
        } else {
            let mut best: i64 = 0;
            let mut c: i64 = 1;
            loop {
                let window = 2 * c + 1;
                let mut total = bounded_product;
                let mut fits = true;
                for _ in 0..capped_count {
                    match total.checked_mul(window) {
                        Some(t) if t <= MAX_ENUM_DOMAIN => total = t,
                        _ => {
                            fits = false;
                            break;
                        }
                    }
                }
                if fits {
                    best = c;
                    c += 1;
                    // Cap the half-width so unbounded-only problems still search
                    // a sensible window without spinning this probe loop forever.
                    if c > MAX_ENUM_DOMAIN {
                        break;
                    }
                } else {
                    break;
                }
            }
            best
        };
        if capped_count > 0 && cap == 0 {
            // Cannot fit even a single extra point per unbounded variable.
            if self.debug {
                safe_eprintln!(
                    "[NIA] Capped search: cannot fit window (bounded_product={}, capped={})",
                    bounded_product,
                    capped_count
                );
            }
            return None;
        }

        // Build a finite search window per variable. Genuine bounds are kept;
        // a missing direction is replaced by a `cap`-wide window anchored to the
        // present bound (so e.g. `c<=9` searches `[9-cap, 9]`, capturing c=5).
        let mut var_ranges: Vec<(TermId, i64, i64)> = Vec::new();
        for &var in &vars {
            let (lo_opt, hi_opt) = var_bounds.get(&var).copied().unwrap_or((None, None));
            let (lo, hi) = match (lo_opt, hi_opt) {
                (Some(lo), Some(hi)) => (lo, hi),
                (Some(lo), None) => (lo, lo.checked_add(2 * cap)?),
                (None, Some(hi)) => (hi.checked_sub(2 * cap)?, hi),
                (None, None) => (-cap, cap),
            };
            var_ranges.push((var, lo, hi));
        }

        // Verify the total enumerated domain is within budget (defensive; the
        // `cap` computation above already guarantees this).
        let mut domain_size: i64 = 1;
        for &(_, lo, hi) in &var_ranges {
            let range = hi.checked_sub(lo)?.checked_add(1)?;
            if range <= 0 {
                return None;
            }
            domain_size = domain_size.checked_mul(range)?;
            if domain_size > MAX_ENUM_DOMAIN {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Capped search: domain size {} exceeds threshold {}",
                        domain_size,
                        MAX_ENUM_DOMAIN
                    );
                }
                return None;
            }
        }

        if self.debug {
            safe_eprintln!(
                "[NIA] Capped search: {} vars, domain size {}, windows: {:?}",
                var_ranges.len(),
                domain_size,
                var_ranges
                    .iter()
                    .map(|(v, lo, hi)| format!("{v:?}:[{lo},{hi}]"))
                    .collect::<Vec<_>>()
            );
        }

        // Enumerate the capped box; return SAT only on a verified witness.
        let n = var_ranges.len();
        let mut assignment: Vec<i64> = var_ranges.iter().map(|&(_, lo, _)| lo).collect();
        let mut visited: i64 = 0;
        loop {
            // Wall-clock abort (#nia-enum-deadline). THIS is the loop that hung
            // compiler_consumer for 7h12m: it is re-entered on every `NeedSplit` and never
            // read the clock. `None` is this routine's ordinary "no witness"
            // answer, so aborting is verdict-neutral by construction.
            if self.enum_deadline_expired(visited) {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Capped search: wall-clock deadline exceeded after {visited} \
                         points — returning None (unknown)"
                    );
                }
                return None;
            }
            // Defensive visit bound (#nia-enum-visit-bound), as in
            // `try_bounded_enumeration`. Unreachable with a correct odometer.
            if visited >= domain_size {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Capped search: visit bound {domain_size} reached without the \
                         odometer signalling exhaustion — returning None (unknown)"
                    );
                }
                return None;
            }
            visited += 1;

            // Anything other than `Some(true)` (constraint violation, or an
            // atom opaque to the exact evaluator) keeps scanning — it means
            // only that THIS point is not a provable witness, not that the
            // formula is unsatisfiable.
            if self.check_assignment(&vars, &assignment) == Some(true) {
                self.record_bounded_enum_model(&vars, &assignment);
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Capped search: SAT with assignment {:?}",
                        vars.iter()
                            .zip(assignment.iter())
                            .map(|(v, a)| format!("{v:?}={a}"))
                            .collect::<Vec<_>>()
                    );
                }
                return Some(TheoryResult::Sat);
            }

            // Compare before incrementing — same odometer as
            // `try_bounded_enumeration`, for the same reason: a genuine bound
            // `hi == i64::MAX` is admitted here whenever the box is narrow,
            // and `+= 1` before the `> hi` test overflows (ICE inside compiler_consumer)
            // on the last step. `a < hi` is exactly `!(a + 1 > hi)` for `a ∈
            // [lo, hi]`, so the visit order is unchanged.
            let mut carry = true;
            for i in (0..n).rev() {
                if carry {
                    if assignment[i] < var_ranges[i].2 {
                        assignment[i] += 1;
                        carry = false;
                    } else {
                        assignment[i] = var_ranges[i].1;
                    }
                }
            }
            if carry {
                break;
            }
        }

        // No witness inside the cap. SOUND: we make NO UNSAT claim — the window
        // is artificial — so we return None and let the caller report unknown.
        if self.debug {
            safe_eprintln!(
                "[NIA] Capped search: no witness in {} points; returning None (unknown)",
                domain_size
            );
        }
        None
    }

    /// Collect the Int-sorted VARIABLE leaves of `term` into `out` (deduped).
    /// Used to assemble exact integer model points from the LIA model.
    pub(crate) fn collect_int_var_leaves(&self, term: TermId, out: &mut Vec<TermId>) {
        for &v in self.int_var_leaves(term).iter() {
            if !out.contains(&v) {
                out.push(v);
            }
        }
    }

    /// The Int-sorted variable leaves of `term` in first-occurrence
    /// traversal order, memoized per term (`int_leaf_memo`): the list
    /// is a pure function of the immutable term store, so a memo hit
    /// returns exactly what the walk would rebuild. Children resolve
    /// through the same memo, making shared-subterm DAGs linear.
    fn int_var_leaves(&self, term: TermId) -> std::rc::Rc<Vec<TermId>> {
        if let Some(hit) = self.int_leaf_memo.borrow().get(&term) {
            return std::rc::Rc::clone(hit);
        }
        self.pure_walk_nodes.set(self.pure_walk_nodes.get() + 1);
        let mut vars: Vec<TermId> = Vec::new();
        match self.terms.get(term) {
            TermData::Var(_, _) if matches!(self.terms.sort(term), Sort::Int) => {
                vars.push(term);
            }
            TermData::App(_, args) => {
                let args: Vec<TermId> = args.clone();
                for arg in args {
                    for &v in self.int_var_leaves(arg).iter() {
                        if !vars.contains(&v) {
                            vars.push(v);
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                let inner = *inner;
                vars.extend(self.int_var_leaves(inner).iter().copied());
            }
            TermData::Ite(c, t, e) => {
                for part in [*c, *t, *e] {
                    for &v in self.int_var_leaves(part).iter() {
                        if !vars.contains(&v) {
                            vars.push(v);
                        }
                    }
                }
            }
            _ => {}
        }
        let rc = std::rc::Rc::new(vars);
        self.int_leaf_memo
            .borrow_mut()
            .insert(term, std::rc::Rc::clone(&rc));
        rc
    }

    /// Build an exact integer model point for the Int variable leaves of
    /// `terms` from the current LIA model. Returns `None` (fail-closed) when
    /// any leaf has no model value, a fractional value, or a value outside
    /// i64. The map feeds the exact evaluator (`eval_term` /
    /// `eval_constraint_exact`), which computes products for real — never via
    /// the opaque aux relaxation.
    pub(crate) fn integer_model_point_for(&self, terms: &[TermId]) -> Option<HashMap<TermId, i64>> {
        let mut vars: Vec<TermId> = Vec::new();
        for &t in terms {
            self.collect_int_var_leaves(t, &mut vars);
        }
        let mut map: HashMap<TermId, i64> = HashMap::default();
        for var in vars {
            let val = self.var_value(var)?;
            if !val.denom().is_one() {
                return None;
            }
            map.insert(var, val.numer().to_i64()?);
        }
        Some(map)
    }

    /// Exact single-point model verification (#nia-model-point, SAT only).
    ///
    /// When the inner LIA relaxation reports Sat but the nonlinear part is not
    /// trusted (scaled products present, or LIA itself answered Unknown), the
    /// check loop historically jumped straight to bounded enumeration — which
    /// bails on any domain over `MAX_ENUM_DOMAIN` (e.g. calypto's `[0, 2^15]²`
    /// boxes) even though the CURRENT LIA model point is often already a
    /// genuine witness. This routine checks exactly that one point: it reads
    /// the integral model value of every Int variable appearing in the
    /// asserted atoms and re-evaluates EVERY atom by exact integer
    /// substitution (`check_assignment`, fail-closed on any opaque atom).
    ///
    /// SOUND: a point that passes exact verification of all asserted atoms is
    /// a genuine model regardless of why the relaxation was distrusted. It
    /// never returns Unsat — a failed point check proves nothing — so this is
    /// a pure completeness gain (some `unknown` become checked `sat`).
    pub(crate) fn try_model_point_sat(&mut self) -> Option<TheoryResult> {
        let asserted_terms: Vec<TermId> = self.asserted.iter().map(|&(t, _)| t).collect();
        let var_map = self.integer_model_point_for(&asserted_terms)?;
        if var_map.is_empty() {
            return None;
        }
        let mut vars: Vec<TermId> = var_map.keys().copied().collect();
        vars.sort_by_key(|t| t.0);
        let values: Vec<i64> = vars.iter().map(|v| var_map[v]).collect();
        if self.check_assignment(&vars, &values) == Some(true) {
            self.record_bounded_enum_model(&vars, &values);
            if self.debug {
                safe_eprintln!(
                    "[NIA] Model point verification: SAT at LIA model point {:?}",
                    vars.iter()
                        .zip(values.iter())
                        .map(|(v, a)| format!("{v:?}={a}"))
                        .collect::<Vec<_>>()
                );
            }
            return Some(TheoryResult::Sat);
        }
        None
    }

    /// The `Sat` verdict the check loop may return for the CURRENT state, or
    /// `None` when it may not (#nia-sign-cut-soundness, the SAT side of the
    /// stale-point defect).
    ///
    /// The inner LIA's `Sat` can come from its direct-enumeration witness — a
    /// solution of the LINEAR atoms only — while the tableau point the NIA
    /// verifies its monomials against is left fractional or was relaxed by an
    /// unjustified-bound retraction. Returning `Sat` for such a point served
    /// a model the executor's gate rejected (`MODEL-UNCONFIRMED` ->
    /// `unknown`) on satisfiable inputs. So a `Sat` is claimed only for:
    ///
    /// 1. the tableau point when the exact evaluator confirms it against
    ///    every asserted atom;
    /// 2. else the LIA's own model when the exact evaluator confirms THAT
    ///    (the witness with the products computed for real), recorded as the
    ///    model to serve;
    /// 3. else the tableau point when it is integral on every Int leaf and
    ///    the evaluator is merely inconclusive (an opaque atom — the
    ///    historical acceptance, unchanged).
    ///
    /// A provably wrong or fractional point yields `None`: the caller keeps
    /// refining (rounding pins the fractional factors; `fractional_int_split`
    /// hands the rest to branch-and-bound). Pure completeness: every served
    /// model is re-validated downstream.
    pub(crate) fn sat_verdict_for_current_point(&mut self) -> Option<TheoryResult> {
        match self.current_model_point_status() {
            // Record the exact-verified point as the model to serve
            // (#nia-record-verified-point): extraction otherwise reads
            // the tableau at extraction time, which can drift from the
            // point verified here (tentative scopes popped, LIA
            // re-solved during model merging) and serve values the
            // gate rejects — measured on VeryMax a=1, where the served
            // candidate falsified the very disjunct the trail chose.
            // `try_model_point_sat` recomputes the same point and
            // records it; the fallback preserves the verdict if the
            // recomputation somehow cannot reproduce it.
            Some(true) => self.try_model_point_sat().or(Some(TheoryResult::Sat)),
            Some(false) => self.try_lia_model_point_sat(),
            None => {
                if let Some(result) = self.try_lia_model_point_sat() {
                    return Some(result);
                }
                let asserted_terms: Vec<TermId> = self.asserted.iter().map(|&(t, _)| t).collect();
                let mut vars: Vec<TermId> = Vec::new();
                for &t in &asserted_terms {
                    self.collect_int_var_leaves(t, &mut vars);
                }
                let integral = vars
                    .iter()
                    .all(|&v| self.var_value(v).is_none_or(|val| val.denom().is_one()));
                if integral {
                    // #nia-record-verified-point: pin the leaves that
                    // carry i64 tableau values as the model to serve,
                    // so extraction cannot drift from the accepted
                    // point on those leaves.
                    let (mut rec_vars, mut rec_values): (Vec<TermId>, Vec<i64>) =
                        (Vec::new(), Vec::new());
                    for &v in &vars {
                        if let Some(val) = self.var_value(v) {
                            if let Some(iv) = val.numer().to_i64() {
                                rec_vars.push(v);
                                rec_values.push(iv);
                            }
                        }
                    }
                    if !rec_vars.is_empty() {
                        self.record_bounded_enum_model(&rec_vars, &rec_values);
                    }
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Sat on an integral tableau point the exact evaluator cannot                              judge (opaque atom) — historical acceptance"
                        );
                    }
                    Some(TheoryResult::Sat)
                } else {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] LIA Sat on a FRACTIONAL tableau point — not a model; refining"
                        );
                    }
                    None
                }
            }
        }
    }

    /// Exact verification of the LIA's OWN model (its direct-enumeration
    /// witness when one exists, else the tableau) against every asserted atom
    /// with the products computed for real. `Some(Sat)` records that point
    /// as the model to serve; `None` proves nothing.
    pub(crate) fn try_lia_model_point_sat(&mut self) -> Option<TheoryResult> {
        let lia_model = self.lia.extract_model()?;
        let asserted_terms: Vec<TermId> = self.asserted.iter().map(|&(t, _)| t).collect();
        let mut vars: Vec<TermId> = Vec::new();
        for &t in &asserted_terms {
            self.collect_int_var_leaves(t, &mut vars);
        }
        if vars.is_empty() {
            return None;
        }
        vars.sort_by_key(|t| t.0);
        let mut values: Vec<i64> = Vec::with_capacity(vars.len());
        for v in &vars {
            values.push(lia_model.values.get(v)?.to_i64()?);
        }
        if self.check_assignment(&vars, &values) == Some(true) {
            self.record_bounded_enum_model(&vars, &values);
            if self.debug {
                safe_eprintln!(
                    "[NIA] Model point verification: SAT at the LIA's own model point {:?}",
                    vars.iter()
                        .zip(values.iter())
                        .map(|(v, a)| format!("{v:?}={a}"))
                        .collect::<Vec<_>>()
                );
            }
            return Some(TheoryResult::Sat);
        }
        None
    }

    /// The branch-and-bound split for the first Int variable (of the asserted
    /// atoms) whose tableau value is fractional AND inside the variable's
    /// current bounds, if any (#nia-sign-cut-soundness). The inner LIA
    /// answered `Sat` on its direct-enumeration witness and left the tableau
    /// fractional on a variable that is not a monomial factor, so the loop's
    /// rounding never touches it and no refinement can make the point a
    /// model; this is the split LIA itself would have requested for that
    /// variable.
    ///
    /// A value OUTSIDE the variable's bounds is not the LP's answer to them:
    /// the assignment is stale — an exact fallback (the factor split's
    /// branches, a popped tentative scope) left the tableau where its last
    /// pivot stopped. A split there proposes a literal that is already
    /// asserted or already refuted, so the branch instance is the same
    /// problem again and the split loop walks (signfuzz p066: `y = 1/170`
    /// split 1,940 times under an asserted `y <= 0`). Inside the bounds both
    /// branches are new information (`lb <= val < ceil`, `floor < val <= ub`).
    /// Branch split for a factor of a tracked monomial, offered only
    /// at the refinement stall exit (integral model point, monomials
    /// inconsistent, every exact/SAT-only lane declined, no fractional
    /// split): without a branch the loop can only return Unknown.
    ///
    /// A factor with a finite integer box `[lo, hi]`, `lo < hi`, is
    /// bisected at its midpoint (`v <= mid OR v >= mid + 1`), so
    /// successive branches pin boxed factors level by level — the
    /// DPLL-level analogue of the one-level factor split, which on
    /// slayer-3 refutes most of its 54 branches immediately but
    /// leaves the rest inconclusive for want of a second level. A
    /// sign-undetermined unbounded factor gets the sign dichotomy
    /// `v <= -1 OR v >= 0`. Once per `(var, floor)` per instance
    /// (`sign_split_offered`): re-offering the identical split at
    /// every BCP quiescence of a persistent eager-lane instance
    /// churns split-loop rounds until the round cap converts a
    /// deciding solve into `unknown`
    /// (DR-AY-NIA-SIGN-SPLIT-REJECTED-20261116).
    pub(crate) fn monomial_sign_split(&mut self) -> Option<ay_core::SplitRequest> {
        let mut candidates: Vec<TermId> = self
            .monomials
            .values()
            .flat_map(|m| m.vars.iter().copied())
            .collect();
        candidates.sort_by_key(|t| t.0);
        candidates.dedup();
        // (width in integers, term, split floor); unbounded sign splits
        // sort last via a maximal width.
        let mut offers: Vec<(BigInt, TermId, BigInt)> = Vec::new();
        let zero = BigRational::zero();
        for v in candidates {
            // Plain Int variable leaves only: a compound factor has no
            // single bound atom the split could assert.
            if !matches!(self.terms.get(v), TermData::Var(..)) {
                continue;
            }
            if *self.terms.sort(v) != Sort::Int {
                continue;
            }
            let (lb, ub) = match self.lia.lra_solver().get_bounds_ref(v) {
                Some(pair) => pair,
                None => continue,
            };
            // Effective integer box from the direct bounds: lower rounds
            // up (strict `> c` means `>= floor(c) + 1`), upper rounds down.
            let lo = lb.map(|b| {
                let value = b.value_big();
                let floor = value.floor().to_integer();
                if b.strict && value.is_integer() {
                    floor + 1
                } else if value.is_integer() {
                    floor
                } else {
                    floor + 1
                }
            });
            let hi = ub.map(|b| {
                let value = b.value_big();
                let floor = value.floor().to_integer();
                if b.strict && value.is_integer() {
                    floor - 1
                } else {
                    floor
                }
            });
            match (lo, hi) {
                (Some(lo), Some(hi)) if lo < hi => {
                    // Midpoint floor: (lo + hi - 1) / 2 floored, so the
                    // fractional value floor + 1/2 lies inside the box.
                    let mid = (&lo + &hi - BigInt::one()).div_floor(&BigInt::from(2));
                    offers.push((&hi - &lo, v, mid));
                }
                (Some(_), Some(_)) => {}
                _ => {
                    let determined_nonneg = lb.is_some_and(|b| b.value_big() >= zero);
                    let determined_negative = ub.is_some_and(|b| {
                        let value = b.value_big();
                        value < zero || (value.is_zero() && b.strict)
                    });
                    if !determined_nonneg && !determined_negative {
                        offers.push((BigInt::from(i64::MAX), v, BigInt::from(-1)));
                    }
                }
            }
        }
        offers.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1 .0.cmp(&b.1 .0)));
        for (_, v, floor) in offers {
            if self.sign_split_offered.contains(&(v, floor.clone())) {
                continue;
            }
            self.sign_split_offered.insert((v, floor.clone()));
            return Some(ay_core::SplitRequest {
                variable: v,
                value: BigRational::new(&floor * 2 + 1, BigInt::from(2)),
                ceil: &floor + 1,
                floor,
            });
        }
        None
    }

    pub(crate) fn fractional_int_split(&self) -> Option<ay_core::SplitRequest> {
        let asserted_terms: Vec<TermId> = self.asserted.iter().map(|&(t, _)| t).collect();
        let mut vars: Vec<TermId> = Vec::new();
        for &t in &asserted_terms {
            self.collect_int_var_leaves(t, &mut vars);
        }
        vars.sort_by_key(|t| t.0);
        let lra = self.lia.lra_solver();
        for v in vars {
            let Some(val) = self.var_value(v) else {
                continue;
            };
            if val.denom().is_one() {
                continue;
            }
            if let Some((lb, ub)) = lra.get_bounds_ref(v) {
                if lb.is_some_and(|b| b.value_big() > val)
                    || ub.is_some_and(|b| b.value_big() < val)
                {
                    continue;
                }
            }
            let floor = val.floor().to_integer();
            let ceil = val.ceil().to_integer();
            return Some(ay_core::SplitRequest {
                variable: v,
                value: val,
                floor,
                ceil,
            });
        }
        None
    }

    /// Tri-state exact verification of the CURRENT LIA model point against
    /// every asserted atom (#nia-scaled-patch-verify).
    ///
    /// Returns `Some(true)` when the point is a verified genuine model,
    /// `Some(false)` when it PROVABLY violates some asserted atom, and `None`
    /// when inconclusive (no integral model point, or an atom is opaque to
    /// the exact evaluator). Unlike [`Self::try_model_point_sat`] this
    /// distinguishes "provably wrong" from "cannot tell", so the check loop
    /// can suppress a Sat verdict it KNOWS the model checker would reject
    /// (and keep refining) without disturbing any inconclusive case.
    pub(crate) fn current_model_point_status(&self) -> Option<bool> {
        let asserted_terms: Vec<TermId> = self.asserted.iter().map(|&(t, _)| t).collect();
        let var_map = self.integer_model_point_for(&asserted_terms)?;
        if var_map.is_empty() {
            return None;
        }
        let mut vars: Vec<TermId> = var_map.keys().copied().collect();
        vars.sort_by_key(|t| t.0);
        let values: Vec<i64> = vars.iter().map(|v| var_map[v]).collect();
        self.check_assignment(&vars, &values)
    }

    /// Model-anchored bounded REPAIR search (#nia-repair-search, SAT only).
    ///
    /// The capped window search (`try_capped_model_search`) anchors its
    /// windows at genuine bounds and searches EVERY monomial variable, so with
    /// many unbounded variables the shared `MAX_ENUM_DOMAIN` budget cannot fit
    /// even a ±1 window (`cannot fit window (bounded_product=…, capped=12+)`)
    /// and the SAT-side completeness gap stays open — the dominant stall shape
    /// on leipzig / T2 termination instances whose LIA model is ALMOST right.
    ///
    /// This search exploits that: it pins every Int variable at its current
    /// integral LIA model value EXCEPT the "suspect" variables — the factors
    /// of monomials whose model value disagrees with the true product, plus
    /// scaled-product factors — and enumerates a small box of half-width `cap`
    /// centered at each suspect's model value (budgeted so the total box stays
    /// within `MAX_ENUM_DOMAIN`). Every candidate is verified by exact integer
    /// substitution into EVERY asserted atom (`check_assignment`, fail-closed).
    ///
    /// SOUND: returns Sat ONLY for an exactly-verified witness; never Unsat
    /// (the box is an arbitrary neighborhood, exhausting it proves nothing).
    pub(crate) fn try_model_repair_search(&mut self) -> Option<TheoryResult> {
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();
        // Mirror of try_bounded_enumeration: speculative tentative-patch scopes
        // pin variables to guessed points; drop them so the anchor is the real
        // relaxation model. (SAT-only, so this is purely about search quality.)
        self.undo_tentative_patch();

        // Integral model point over ALL Int vars in the asserted atoms.
        let asserted_terms: Vec<TermId> = self.asserted.iter().map(|&(t, _)| t).collect();
        let Some(var_map) = self.integer_model_point_for(&asserted_terms) else {
            if self.debug {
                safe_eprintln!("[NIA] Repair search: no integral model point; skipping");
            }
            return None;
        };
        if var_map.is_empty() {
            return None;
        }

        // Suspects: factor vars of model-inconsistent monomials, plus scaled
        // product factors (never constrained by the linearization at all).
        // Rank by how many inconsistent monomials each participates in so the
        // budget-forced truncation below keeps the most repair-relevant vars.
        let mut suspect_score: BTreeMap<TermId, usize> = BTreeMap::new();
        for mon in self.monomials_sorted() {
            let consistent = (|| {
                let mut prod = BigInt::one();
                for &v in &mon.vars {
                    prod *= BigInt::from(*var_map.get(&v)?);
                }
                Some(BigInt::from(*var_map.get(&mon.aux_var)?) == prod)
            })();
            if consistent != Some(true) {
                for &v in &mon.vars {
                    if var_map.contains_key(&v) {
                        *suspect_score.entry(v).or_insert(0) += 1;
                    }
                }
            }
        }
        for &(term, _) in &self.asserted {
            let mut scaled: Vec<TermId> = Vec::new();
            self.collect_scaled_product_vars(term, &mut scaled);
            for v in scaled {
                if var_map.contains_key(&v) {
                    *suspect_score.entry(v).or_insert(0) += 1;
                }
            }
        }
        if suspect_score.is_empty() {
            if self.debug {
                safe_eprintln!("[NIA] Repair search: no suspects; skipping");
            }
            return None;
        }
        let mut suspects: Vec<TermId> = suspect_score.keys().copied().collect();
        // Highest score first; TermId ascending for determinism (BTreeMap
        // iteration already sorted the keys, and sort_by_key is stable).
        suspects.sort_by_key(|v| std::cmp::Reverse(suspect_score[v]));
        // A ±1 window needs 3^k points, so more than 8 suspects can never fit
        // MAX_ENUM_DOMAIN = 10_000. Keep the top-ranked 8; the rest stay
        // pinned at their model values (the exact verification still covers
        // them, so truncation costs only completeness, never soundness).
        const MAX_REPAIR_SUSPECTS: usize = 8;
        suspects.truncate(MAX_REPAIR_SUSPECTS);
        suspects.sort_by_key(|t| t.0);

        // Largest half-width `cap >= 1` whose box fits the budget.
        let k = suspects.len() as u32;
        let mut cap: i64 = 0;
        let mut c: i64 = 1;
        loop {
            let window = 2 * c + 1;
            match window.checked_pow(k) {
                Some(total) if total <= MAX_ENUM_DOMAIN => {
                    cap = c;
                    c += 1;
                }
                _ => break,
            }
        }
        if cap == 0 {
            return None;
        }

        // Enumerate the box around the model point; pin everything else.
        let mut vars: Vec<TermId> = var_map.keys().copied().collect();
        vars.sort_by_key(|t| t.0);
        let mut values: Vec<i64> = vars.iter().map(|v| var_map[v]).collect();
        let suspect_idx: Vec<usize> = suspects
            .iter()
            .map(|s| {
                vars.iter()
                    .position(|v| v == s)
                    .expect("suspect is a model var")
            })
            .collect();
        let centers: Vec<i64> = suspect_idx.iter().map(|&i| values[i]).collect();
        let mut offsets: Vec<i64> = vec![-cap; suspect_idx.len()];
        // `cap` was chosen above so this power fits `MAX_ENUM_DOMAIN`.
        let box_points = (2 * cap + 1).checked_pow(k)?;
        if self.debug {
            safe_eprintln!(
                "[NIA] Repair search: {} suspects of {} vars, cap={} (box {})",
                suspects.len(),
                vars.len(),
                cap,
                box_points
            );
        }
        let mut visited: i64 = 0;
        loop {
            // Wall-clock abort (#nia-enum-deadline). SAT-only search: `None` is
            // its ordinary "no witness in the neighbourhood" answer.
            if self.enum_deadline_expired(visited) {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Repair search: wall-clock deadline exceeded after {visited} \
                         points — returning None (unknown)"
                    );
                }
                return None;
            }
            // Defensive visit bound (#nia-enum-visit-bound).
            if visited >= box_points {
                return None;
            }
            visited += 1;

            for (j, &i) in suspect_idx.iter().enumerate() {
                values[i] = centers[j].checked_add(offsets[j])?;
            }
            if self.check_assignment(&vars, &values) == Some(true) {
                self.record_bounded_enum_model(&vars, &values);
                if self.debug {
                    safe_eprintln!("[NIA] Repair search: SAT with verified witness");
                }
                return Some(TheoryResult::Sat);
            }
            // Odometer over offsets.
            let mut carry = true;
            for j in (0..offsets.len()).rev() {
                if carry {
                    offsets[j] += 1;
                    if offsets[j] > cap {
                        offsets[j] = -cap;
                    } else {
                        carry = false;
                    }
                }
            }
            if carry {
                break;
            }
        }
        // No witness in the neighborhood: make NO claim (SAT-only search).
        None
    }

    /// Tighten enumeration bounds from active integer var-vs-constant atoms.
    pub(crate) fn apply_asserted_integer_bounds(
        &self,
        vars: &[TermId],
        var_bounds: &mut HashMap<TermId, (Option<i64>, Option<i64>)>,
    ) {
        for &(term, positive) in &self.asserted {
            let Some((var, lo, hi)) = self.asserted_integer_bound(term, positive) else {
                continue;
            };
            if !vars.contains(&var) {
                continue;
            }

            let (old_lo, old_hi) = var_bounds.get(&var).copied().unwrap_or((None, None));
            let new_lo = match (old_lo, lo) {
                (Some(old), Some(bound)) => Some(old.max(bound)),
                (None, Some(bound)) => Some(bound),
                (old, None) => old,
            };
            let new_hi = match (old_hi, hi) {
                (Some(old), Some(bound)) => Some(old.min(bound)),
                (None, Some(bound)) => Some(bound),
                (old, None) => old,
            };
            var_bounds.insert(var, (new_lo, new_hi));
        }
    }

    /// Extract a direct integer bound from an asserted comparison atom.
    pub(crate) fn asserted_integer_bound(
        &self,
        term: TermId,
        positive: bool,
    ) -> Option<(TermId, Option<i64>, Option<i64>)> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        let (var, constant, var_on_left) = if matches!(self.terms.get(args[0]), TermData::Var(_, _))
        {
            (args[0], self.term_i64_constant(args[1])?, true)
        } else if matches!(self.terms.get(args[1]), TermData::Var(_, _)) {
            (args[1], self.term_i64_constant(args[0])?, false)
        } else {
            return None;
        };

        let op = match (name.as_str(), positive) {
            ("=", true) => "=",
            ("distinct", false) => "=",
            ("<", true) => "<",
            ("<", false) => ">=",
            ("<=", true) => "<=",
            ("<=", false) => ">",
            (">", true) => ">",
            (">", false) => "<=",
            (">=", true) => ">=",
            (">=", false) => "<",
            _ => return None,
        };

        let (lo, hi) = match (op, var_on_left) {
            ("=", _) => (Some(constant), Some(constant)),
            (">=", true) | ("<=", false) => (Some(constant), None),
            (">", true) | ("<", false) => (Some(constant.checked_add(1)?), None),
            ("<=", true) | (">=", false) => (None, Some(constant)),
            ("<", true) | (">", false) => (None, Some(constant.checked_sub(1)?)),
            _ => return None,
        };

        Some((var, lo, hi))
    }

    /// Evaluate an integer constant expression to i64.
    fn term_i64_constant(&self, term: TermId) -> Option<i64> {
        self.terms
            .extract_integer_constant(term)
            .or_else(|| self.eval_term(term, &HashMap::default()))
            .and_then(|n| n.to_i64())
    }

    /// Store the exact integer witness used to return SAT from bounded enum.
    fn record_bounded_enum_model(&mut self, vars: &[TermId], values: &[i64]) {
        let var_map: HashMap<TermId, i64> =
            vars.iter().copied().zip(values.iter().copied()).collect();
        let mut model = HashMap::default();

        for (&var, &value) in vars.iter().zip(values) {
            model.insert(var, BigInt::from(value));
        }

        for mon in self.monomials.values() {
            if let Some(value) = self.eval_term(mon.aux_var, &var_map) {
                model.insert(mon.aux_var, value);
            }
        }

        self.bounded_enum_bool_model.clear();
        self.bounded_enum_model = Some(model);
    }

    /// Get bounds for a monomial, including bounds propagated through equalities.
    ///
    /// Checks: (1) direct LRA bounds on the aux variable, (2) equality constraints
    /// in the asserted atoms like `(= area (* w h))` where `area` has bounds.
    fn get_monomial_bounds(&self, mon: &Monomial) -> (Option<i64>, Option<i64>) {
        // First try direct bounds on the monomial's auxiliary variable
        let (mut lo, mut hi) = match self.get_integer_bounds(mon.aux_var) {
            Some((lo, hi)) => (Some(lo), Some(hi)),
            None => self.get_partial_integer_bounds(mon.aux_var),
        };

        // If we still don't have both bounds, check asserted equality constraints.
        // Look for (= other_var monomial_aux) or (= monomial_aux other_var)
        // where other_var has bounds.
        if lo.is_none() || hi.is_none() {
            for &(term, val) in &self.asserted {
                if !val {
                    continue; // Only positive equality assertions
                }
                if let TermData::App(Symbol::Named(name), args) = self.terms.get(term) {
                    if name.as_str() == "=" && args.len() == 2 {
                        let other = if args[0] == mon.aux_var {
                            Some(args[1])
                        } else if args[1] == mon.aux_var {
                            Some(args[0])
                        } else {
                            None
                        };
                        if let Some(other_term) = other {
                            let (other_lo, other_hi) = self
                                .terms
                                .extract_integer_constant(other_term)
                                .and_then(|n| n.to_i64().map(|i| (Some(i), Some(i))))
                                .unwrap_or_else(|| match self.get_integer_bounds(other_term) {
                                    Some((lo, hi)) => (Some(lo), Some(hi)),
                                    None => self.get_partial_integer_bounds(other_term),
                                });
                            if lo.is_none() {
                                lo = other_lo;
                            }
                            if hi.is_none() {
                                hi = other_hi;
                            }
                        }
                    }
                }
            }
        }

        (lo, hi)
    }

    /// Get partial integer bounds for a variable (lower only, upper only, or both).
    ///
    /// Unlike `get_integer_bounds` which requires both bounds, this returns
    /// whatever bounds are available.
    pub(crate) fn get_partial_integer_bounds(&self, var: TermId) -> (Option<i64>, Option<i64>) {
        let bounds = match self.lia.justified_bounds(var) {
            Some(b) => b,
            None => return (None, None),
        };

        let lower = bounds.0.and_then(|bound| {
            let val = bound.value.to_big();
            if bound.strict {
                let ceil = rational_ceil(&val);
                if BigRational::from(ceil.clone()) == val {
                    (&ceil + &BigInt::one()).to_i64()
                } else {
                    ceil.to_i64()
                }
            } else {
                rational_ceil(&val).to_i64()
            }
        });

        let upper = bounds.1.and_then(|bound| {
            let val = bound.value.to_big();
            if bound.strict {
                let floor = rational_floor(&val);
                if BigRational::from(floor.clone()) == val {
                    (&floor - &BigInt::one()).to_i64()
                } else {
                    floor.to_i64()
                }
            } else {
                rational_floor(&val).to_i64()
            }
        });

        (lower, upper)
    }

    /// Get the integer lower and upper bounds for a variable.
    ///
    /// JUSTIFIED bounds only (`LiaSolver::justified_bounds`,
    /// #nia-sign-cut-soundness): the box these helpers build decides an
    /// exhaustive-search `Unsat`, and a verdict may rest only on bounds whose
    /// reasons are asserted atoms or cross-theory reasons (or sentinel
    /// axioms). `undo_tentative_patch` already pops the NIA's own guess
    /// scopes; reading through the accessor makes the box independent of
    /// which scope any model-derived bound lives in. An unjustified side is
    /// absent, so the box can only widen (fewer enumerations, never a wrong
    /// one).
    ///
    /// Returns `Some((lower, upper))` as i64 integers if the variable has
    /// finite bounds. For strict bounds on integers, adjusts to the nearest
    /// valid integer (e.g., x > 0 strict becomes x >= 1).
    pub(crate) fn get_integer_bounds(&self, var: TermId) -> Option<(i64, i64)> {
        let (lb_opt, ub_opt) = self.lia.justified_bounds(var)?;

        let lower = {
            let bound = lb_opt?;
            let val = bound.value.to_big();
            if bound.strict {
                // x > v  =>  x >= ceil(v+epsilon)
                // For integers, x > 2 means x >= 3
                // x > 2.5 means x >= 3
                let ceil = rational_ceil(&val);
                if BigRational::from(ceil.clone()) == val {
                    // x > 2  =>  x >= 3
                    (&ceil + &BigInt::one()).to_i64()?
                } else {
                    // x > 2.5  =>  x >= 3
                    ceil.to_i64()?
                }
            } else {
                // x >= v  =>  x >= ceil(v)
                rational_ceil(&val).to_i64()?
            }
        };

        let upper = {
            let bound = ub_opt?;
            let val = bound.value.to_big();
            if bound.strict {
                // x < v  =>  x <= floor(v-epsilon)
                // For integers, x < 5 means x <= 4
                // x < 4.5 means x <= 4
                let floor = rational_floor(&val);
                if BigRational::from(floor.clone()) == val {
                    // x < 5  =>  x <= 4
                    (&floor - &BigInt::one()).to_i64()?
                } else {
                    // x < 4.5  =>  x <= 4
                    floor.to_i64()?
                }
            } else {
                // x <= v  =>  x <= floor(v)
                rational_floor(&val).to_i64()?
            }
        };

        if lower > upper {
            return None;
        }

        Some((lower, upper))
    }

    /// Recursively collect the variable (non-constant) factors of every
    /// nonlinear `*` subterm of `term` into `vars`. Used only by bounded
    /// enumeration to recover SCALED monomials (`(* c x y)`) that are not
    /// registered as monomials (#nia-const-factor). Only Int `Var` factors are
    /// added — non-variable factors keep `eval_term` fail-closed, so a product
    /// whose factors are not all enumerable Int vars simply yields Unknown.
    fn collect_scaled_product_vars(&self, term: TermId, vars: &mut Vec<TermId>) {
        for &v in self.scaled_product_vars(term).iter() {
            if !vars.contains(&v) {
                vars.push(v);
            }
        }
    }

    /// The scaled-product factor variables of `term` in
    /// first-occurrence traversal order (a product node's own
    /// factors before its children's), memoized per term
    /// (`scaled_vars_memo`); see `int_var_leaves` for the exactness
    /// argument.
    fn scaled_product_vars(&self, term: TermId) -> std::rc::Rc<Vec<TermId>> {
        if let Some(hit) = self.scaled_vars_memo.borrow().get(&term) {
            return std::rc::Rc::clone(hit);
        }
        self.pure_walk_nodes.set(self.pure_walk_nodes.get() + 1);
        let mut vars: Vec<TermId> = Vec::new();
        match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                let is_mul = name == "*";
                let args: Vec<TermId> = args.clone();
                if is_mul {
                    let mut var_factors = 0usize;
                    let mut const_product = BigInt::one();
                    for &arg in &args {
                        if let Some(c) = self.terms.extract_integer_constant(arg) {
                            const_product *= c;
                        } else {
                            var_factors += 1;
                        }
                    }
                    // Only a SCALED nonlinear product contributes enumeration
                    // variables: >= 2 non-constant factors AND a constant factor
                    // != 1. A constant-free product (`const_product == 1`) is
                    // already registered as a monomial (the linearization handles
                    // it), and treating it as "scaled" here would wrongly route an
                    // unbounded pure product like `r = n*m` — which the relaxation
                    // soundly reports Sat — into the enumeration/Unknown path.
                    if var_factors >= 2 && !const_product.is_one() {
                        for &arg in &args {
                            if matches!(self.terms.get(arg), TermData::Var(_, _))
                                && matches!(self.terms.sort(arg), Sort::Int)
                                && !vars.contains(&arg)
                            {
                                vars.push(arg);
                            }
                        }
                    }
                }
                for arg in args {
                    for &v in self.scaled_product_vars(arg).iter() {
                        if !vars.contains(&v) {
                            vars.push(v);
                        }
                    }
                }
            }
            TermData::Not(inner) => {
                let inner = *inner;
                vars.extend(self.scaled_product_vars(inner).iter().copied());
            }
            TermData::Ite(c, t, e) => {
                for part in [*c, *t, *e] {
                    for &v in self.scaled_product_vars(part).iter() {
                        if !vars.contains(&v) {
                            vars.push(v);
                        }
                    }
                }
            }
            _ => {}
        }
        let rc = std::rc::Rc::new(vars);
        self.scaled_vars_memo
            .borrow_mut()
            .insert(term, std::rc::Rc::clone(&rc));
        rc
    }

    /// Check if a variable assignment satisfies all monomial constraints.
    ///
    /// For each assertion, evaluates it under the given assignment and checks
    /// if the constraint holds.
    pub(crate) fn check_assignment(&self, vars: &[TermId], values: &[i64]) -> Option<bool> {
        // Build a lookup map from variable -> value
        let var_map: HashMap<TermId, i64> =
            vars.iter().copied().zip(values.iter().copied()).collect();

        // Check each assertion against the assignment
        for (term, val) in &self.asserted {
            match self.eval_constraint_exact(*term, *val, &var_map) {
                Some(true) => {}
                Some(false) => return Some(false),
                None => return None,
            }
        }
        Some(true)
    }

    /// Evaluate a constraint under the given variable assignment.
    ///
    /// Returns true if the constraint is satisfied, false if violated,
    /// and true (conservative) if the constraint cannot be fully evaluated.
    #[cfg(test)]
    fn eval_constraint(
        &self,
        term: TermId,
        positive: bool,
        var_map: &HashMap<TermId, i64>,
    ) -> bool {
        self.eval_constraint_exact(term, positive, var_map)
            .unwrap_or(true)
    }

    /// Evaluate a constraint exactly under the given variable assignment.
    ///
    /// Returns `None` for unsupported atoms or terms. Bounded enumeration uses
    /// this tri-state result so it does not claim SAT/UNSAT when opaque active
    /// constraints could still affect the answer.
    ///
    /// Shared with the univariate-integer decider (`univariate_int.rs`), which
    /// re-verifies its integer witnesses through this SAME exact evaluator.
    pub(crate) fn eval_constraint_exact(
        &self,
        term: TermId,
        positive: bool,
        var_map: &HashMap<TermId, i64>,
    ) -> Option<bool> {
        self.eval_constraint_exact_with_progress(term, positive, var_map, &mut || true)
    }

    /// The same arithmetic semantics with a cooperative caller-owned check.
    /// A false progress result makes this evaluation inconclusive.
    pub(crate) fn eval_constraint_exact_with_progress(
        &self,
        term: TermId,
        positive: bool,
        var_map: &HashMap<TermId, i64>,
        progress: &mut impl FnMut() -> bool,
    ) -> Option<bool> {
        if !progress() {
            return None;
        }
        let result = match self.terms.get(term) {
            TermData::Not(inner) => {
                self.eval_constraint_exact_with_progress(*inner, !positive, var_map, progress)
            }
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let lhs_val = self.eval_term_with_progress(args[0], var_map, progress);
                let rhs_val = self.eval_term_with_progress(args[1], var_map, progress);

                match (lhs_val, rhs_val) {
                    (Some(l), Some(r)) => {
                        let result = match name.as_str() {
                            "=" => l == r,
                            "distinct" => l != r,
                            "<" => l < r,
                            "<=" => l <= r,
                            ">" => l > r,
                            ">=" => l >= r,
                            _ => return None,
                        };
                        Some(if positive { result } else { !result })
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if progress() {
            result
        } else {
            None
        }
    }

    /// Evaluate a term to an integer value under the given variable assignment.
    ///
    /// Returns `None` if the term cannot be fully evaluated (e.g., unbound variable).
    ///
    /// Shared with the univariate-integer decider (`univariate_int.rs`) to
    /// materialize monomial aux-var values for the witness model.
    pub(crate) fn eval_term(&self, term: TermId, var_map: &HashMap<TermId, i64>) -> Option<BigInt> {
        self.eval_term_with_progress(term, var_map, &mut || true)
    }

    /// Exact BigInt substitution, polling before/after each recursive visit.
    /// It cannot preempt an individual BigInt operation or allocation.
    pub(crate) fn eval_term_with_progress(
        &self,
        term: TermId,
        var_map: &HashMap<TermId, i64>,
        progress: &mut impl FnMut() -> bool,
    ) -> Option<BigInt> {
        if !progress() {
            return None;
        }
        let result = match self.terms.get(term) {
            TermData::Var(_, _) => var_map.get(&term).map(|&v| BigInt::from(v)),
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::Const(Constant::Rational(r)) => {
                // Only return integer rationals
                if r.0.denom().is_one() {
                    Some(r.0.numer().clone())
                } else {
                    None
                }
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut sum = BigInt::zero();
                    for &arg in args {
                        sum += self.eval_term_with_progress(arg, var_map, progress)?;
                    }
                    Some(sum)
                }
                "-" if args.len() == 1 => {
                    let val = self.eval_term_with_progress(args[0], var_map, progress)?;
                    Some(-val)
                }
                "-" if args.len() == 2 => {
                    let l = self.eval_term_with_progress(args[0], var_map, progress)?;
                    let r = self.eval_term_with_progress(args[1], var_map, progress)?;
                    Some(l - r)
                }
                "*" => {
                    let mut prod = BigInt::one();
                    for &arg in args {
                        prod *= self.eval_term_with_progress(arg, var_map, progress)?;
                    }
                    Some(prod)
                }
                _ => None,
            },
            _ => None,
        };
        if progress() {
            result
        } else {
            None
        }
    }
}

/// Compute ceil of a rational number as a BigInt.
fn rational_ceil(r: &BigRational) -> BigInt {
    let (quot, rem) = r.numer().div_rem(r.denom());
    if rem.is_zero() {
        quot
    } else if r.numer() > &BigInt::zero() {
        // Positive with remainder: ceil rounds up
        quot + BigInt::one()
    } else {
        // Negative with remainder: truncation toward zero IS ceiling
        quot
    }
}

/// Compute floor of a rational number as a BigInt.
fn rational_floor(r: &BigRational) -> BigInt {
    let (quot, rem) = r.numer().div_rem(r.denom());
    if rem.is_zero() {
        quot
    } else if r.numer() > &BigInt::zero() {
        // Positive with remainder: truncation toward zero IS floor
        quot
    } else {
        // Negative with remainder: floor rounds down
        quot - BigInt::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rational_ceil_positive_integer() {
        let r = BigRational::new(BigInt::from(5), BigInt::from(1));
        assert_eq!(rational_ceil(&r), BigInt::from(5));
    }

    #[test]
    fn test_rational_ceil_positive_fraction() {
        let r = BigRational::new(BigInt::from(7), BigInt::from(2));
        assert_eq!(rational_ceil(&r), BigInt::from(4)); // ceil(3.5) = 4
    }

    #[test]
    fn test_rational_ceil_negative_fraction() {
        let r = BigRational::new(BigInt::from(-7), BigInt::from(2));
        assert_eq!(rational_ceil(&r), BigInt::from(-3)); // ceil(-3.5) = -3
    }

    #[test]
    fn test_rational_floor_positive_fraction() {
        let r = BigRational::new(BigInt::from(7), BigInt::from(2));
        assert_eq!(rational_floor(&r), BigInt::from(3)); // floor(3.5) = 3
    }

    #[test]
    fn test_rational_floor_negative_fraction() {
        let r = BigRational::new(BigInt::from(-7), BigInt::from(2));
        assert_eq!(rational_floor(&r), BigInt::from(-4)); // floor(-3.5) = -4
    }

    #[test]
    fn test_rational_floor_negative_integer() {
        let r = BigRational::new(BigInt::from(-6), BigInt::from(2));
        assert_eq!(rational_floor(&r), BigInt::from(-3)); // floor(-3.0) = -3
    }

    /// ceil(0) = 0
    #[test]
    fn test_rational_ceil_zero() {
        let r = BigRational::new(BigInt::from(0), BigInt::from(1));
        assert_eq!(rational_ceil(&r), BigInt::from(0));
    }

    /// floor(0) = 0
    #[test]
    fn test_rational_floor_zero() {
        let r = BigRational::new(BigInt::from(0), BigInt::from(1));
        assert_eq!(rational_floor(&r), BigInt::from(0));
    }

    /// ceil(1/3) = 1
    #[test]
    fn test_rational_ceil_small_positive() {
        let r = BigRational::new(BigInt::from(1), BigInt::from(3));
        assert_eq!(rational_ceil(&r), BigInt::from(1));
    }

    /// floor(-1/3) = -1
    #[test]
    fn test_rational_floor_small_negative() {
        let r = BigRational::new(BigInt::from(-1), BigInt::from(3));
        assert_eq!(rational_floor(&r), BigInt::from(-1));
    }

    /// ceil(-1/3) = 0
    #[test]
    fn test_rational_ceil_small_negative() {
        let r = BigRational::new(BigInt::from(-1), BigInt::from(3));
        assert_eq!(rational_ceil(&r), BigInt::from(0));
    }

    /// floor(1/3) = 0
    #[test]
    fn test_rational_floor_small_positive() {
        let r = BigRational::new(BigInt::from(1), BigInt::from(3));
        assert_eq!(rational_floor(&r), BigInt::from(0));
    }

    // Additional edge cases for #8460 coverage improvement

    /// ceil(-1) = -1 (exact integer)
    #[test]
    fn test_rational_ceil_negative_integer() {
        let r = BigRational::new(BigInt::from(-5), BigInt::from(1));
        assert_eq!(rational_ceil(&r), BigInt::from(-5));
    }

    /// floor(1) = 1 (exact positive integer)
    #[test]
    fn test_rational_floor_positive_integer() {
        let r = BigRational::new(BigInt::from(7), BigInt::from(1));
        assert_eq!(rational_floor(&r), BigInt::from(7));
    }

    /// ceil(99/100) = 1 (just below 1)
    #[test]
    fn test_rational_ceil_just_below_one() {
        let r = BigRational::new(BigInt::from(99), BigInt::from(100));
        assert_eq!(rational_ceil(&r), BigInt::from(1));
    }

    /// floor(-99/100) = -1 (just above -1)
    #[test]
    fn test_rational_floor_just_above_neg_one() {
        let r = BigRational::new(BigInt::from(-99), BigInt::from(100));
        assert_eq!(rational_floor(&r), BigInt::from(-1));
    }

    /// ceil(101/100) = 2 (just above 1)
    #[test]
    fn test_rational_ceil_just_above_one() {
        let r = BigRational::new(BigInt::from(101), BigInt::from(100));
        assert_eq!(rational_ceil(&r), BigInt::from(2));
    }

    /// floor(101/100) = 1 (just above 1)
    #[test]
    fn test_rational_floor_just_above_one() {
        let r = BigRational::new(BigInt::from(101), BigInt::from(100));
        assert_eq!(rational_floor(&r), BigInt::from(1));
    }

    /// ceil and floor of large rational: 10000001/3
    #[test]
    fn test_rational_ceil_floor_large() {
        let r = BigRational::new(BigInt::from(10_000_001), BigInt::from(3));
        // 10000001/3 = 3333333.666...
        assert_eq!(rational_ceil(&r), BigInt::from(3_333_334));
        assert_eq!(rational_floor(&r), BigInt::from(3_333_333));
    }

    /// ceil and floor agree on exact rationals: 6/3 = 2
    #[test]
    fn test_rational_ceil_floor_exact_agree() {
        let r = BigRational::new(BigInt::from(6), BigInt::from(3));
        assert_eq!(rational_ceil(&r), BigInt::from(2));
        assert_eq!(rational_floor(&r), BigInt::from(2));
    }

    /// Property: floor(x) <= x <= ceil(x) for various rationals.
    #[test]
    fn test_rational_floor_le_ceil_property() {
        let test_cases = vec![
            BigRational::new(BigInt::from(7), BigInt::from(2)),
            BigRational::new(BigInt::from(-7), BigInt::from(2)),
            BigRational::new(BigInt::from(0), BigInt::from(1)),
            BigRational::new(BigInt::from(1), BigInt::from(1)),
            BigRational::new(BigInt::from(-1), BigInt::from(1)),
            BigRational::new(BigInt::from(100), BigInt::from(7)),
            BigRational::new(BigInt::from(-100), BigInt::from(7)),
        ];
        for r in &test_cases {
            let f = rational_floor(r);
            let c = rational_ceil(r);
            let f_rat = BigRational::from(f.clone());
            let c_rat = BigRational::from(c.clone());
            assert!(f_rat <= *r, "floor({r}) = {f} should be <= {r}");
            assert!(c_rat >= *r, "ceil({r}) = {c} should be >= {r}");
            assert!(f <= c, "floor({r}) = {f} should be <= ceil({r}) = {c}");
        }
    }

    // ====================================================================
    // eval_term / eval_constraint tests for #8460
    // ====================================================================

    /// Helper: create a NiaSolver with a TermStore for eval_term testing.
    fn make_solver_for_eval(terms: &TermStore) -> NiaSolver<'_> {
        NiaSolver::new(terms)
    }

    /// eval_term on a variable present in the map should return its value.
    #[test]
    fn test_eval_term_variable_present() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 42i64);
        assert_eq!(solver.eval_term(x, &var_map), Some(BigInt::from(42)));
    }

    /// eval_term on an unbound variable should return None.
    #[test]
    fn test_eval_term_variable_absent() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let solver = make_solver_for_eval(&terms);
        let var_map = HashMap::default();
        assert_eq!(solver.eval_term(x, &var_map), None);
    }

    /// eval_term on an integer constant should return the constant.
    #[test]
    fn test_eval_term_integer_constant() {
        let mut terms = TermStore::new();
        let c = terms.mk_int(BigInt::from(7));
        let solver = make_solver_for_eval(&terms);
        let var_map = HashMap::default();
        assert_eq!(solver.eval_term(c, &var_map), Some(BigInt::from(7)));
    }

    /// eval_term on a negative integer constant.
    #[test]
    fn test_eval_term_negative_constant() {
        let mut terms = TermStore::new();
        let c = terms.mk_int(BigInt::from(-99));
        let solver = make_solver_for_eval(&terms);
        let var_map = HashMap::default();
        assert_eq!(solver.eval_term(c, &var_map), Some(BigInt::from(-99)));
    }

    /// eval_term on addition: x + 3 = 10 when x = 7.
    #[test]
    fn test_eval_term_addition() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let three = terms.mk_int(BigInt::from(3));
        let sum = terms.mk_add(vec![x, three]);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 7i64);
        assert_eq!(solver.eval_term(sum, &var_map), Some(BigInt::from(10)));
    }

    /// eval_term on subtraction: x - y = 3 when x=5, y=2.
    #[test]
    fn test_eval_term_subtraction() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let diff = terms.mk_sub(vec![x, y]);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 5i64);
        var_map.insert(y, 2i64);
        assert_eq!(solver.eval_term(diff, &var_map), Some(BigInt::from(3)));
    }

    /// eval_term on multiplication: x * y = 12 when x=3, y=4.
    #[test]
    fn test_eval_term_multiplication() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let prod = terms.mk_mul(vec![x, y]);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 3i64);
        var_map.insert(y, 4i64);
        assert_eq!(solver.eval_term(prod, &var_map), Some(BigInt::from(12)));
    }

    /// eval_term on unary negation: -x = -5 when x=5.
    #[test]
    fn test_eval_term_unary_negation() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let neg_x = terms.mk_neg(x);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 5i64);
        assert_eq!(solver.eval_term(neg_x, &var_map), Some(BigInt::from(-5)));
    }

    /// eval_term returns None when a sub-term cannot be evaluated.
    #[test]
    fn test_eval_term_partial_failure() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let sum = terms.mk_add(vec![x, y]);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 5i64);
        // y is not bound
        assert_eq!(solver.eval_term(sum, &var_map), None);
    }

    /// eval_constraint for x >= 0 with x=5 (positive) should return true.
    #[test]
    fn test_eval_constraint_ge_positive() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let ge = terms.mk_ge(x, zero);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 5i64);
        assert!(solver.eval_constraint(ge, true, &var_map));
    }

    /// eval_constraint for x >= 0 with x=-1 (positive polarity) should return false.
    #[test]
    fn test_eval_constraint_ge_negative_value() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let ge = terms.mk_ge(x, zero);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, -1i64);
        assert!(!solver.eval_constraint(ge, true, &var_map));
    }

    /// eval_constraint for NOT(x >= 0) with x=-1 should return true.
    #[test]
    fn test_eval_constraint_negated() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let ge = terms.mk_ge(x, zero);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, -1i64);
        // Negated: NOT(x >= 0) with x=-1 => NOT(false) => true
        assert!(solver.eval_constraint(ge, false, &var_map));
    }

    /// eval_constraint for x = y with x=3, y=3 should return true.
    #[test]
    fn test_eval_constraint_equality_sat() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let eq = terms.mk_eq(x, y);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 3i64);
        var_map.insert(y, 3i64);
        assert!(solver.eval_constraint(eq, true, &var_map));
    }

    /// eval_constraint for x = y with x=3, y=4 should return false.
    #[test]
    fn test_eval_constraint_equality_unsat() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let eq = terms.mk_eq(x, y);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 3i64);
        var_map.insert(y, 4i64);
        assert!(!solver.eval_constraint(eq, true, &var_map));
    }

    /// eval_constraint for x < y with x=2, y=5 should return true.
    #[test]
    fn test_eval_constraint_lt_satisfied() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let lt = terms.mk_lt(x, y);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 2i64);
        var_map.insert(y, 5i64);
        assert!(solver.eval_constraint(lt, true, &var_map));
    }

    /// eval_constraint with unbound variable should be conservative (true).
    #[test]
    fn test_eval_constraint_unbound_conservative() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let ge = terms.mk_ge(x, y);
        let solver = make_solver_for_eval(&terms);
        // Neither x nor y bound
        let var_map = HashMap::default();
        assert!(solver.eval_constraint(ge, true, &var_map));
    }

    /// eval_constraint for x * y = 12 with x=3, y=4 should return true.
    #[test]
    fn test_eval_constraint_nonlinear_eq_sat() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let twelve = terms.mk_int(BigInt::from(12));
        let eq = terms.mk_eq(xy, twelve);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 3i64);
        var_map.insert(y, 4i64);
        assert!(solver.eval_constraint(eq, true, &var_map));
    }

    /// eval_constraint for x * y = 12 with x=3, y=5 should return false.
    #[test]
    fn test_eval_constraint_nonlinear_eq_unsat() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let twelve = terms.mk_int(BigInt::from(12));
        let eq = terms.mk_eq(xy, twelve);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 3i64);
        var_map.insert(y, 5i64);
        assert!(!solver.eval_constraint(eq, true, &var_map));
    }

    /// eval_term on zero constant should return 0.
    #[test]
    fn test_eval_term_zero_constant() {
        let mut terms = TermStore::new();
        let c = terms.mk_int(BigInt::from(0));
        let solver = make_solver_for_eval(&terms);
        let var_map = HashMap::default();
        assert_eq!(solver.eval_term(c, &var_map), Some(BigInt::from(0)));
    }

    /// eval_term on nested expression: (x + y) * z = 15 with x=2, y=3, z=3.
    #[test]
    fn test_eval_term_nested_expression() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let sum = terms.mk_add(vec![x, y]);
        let prod = terms.mk_mul(vec![sum, z]);
        let solver = make_solver_for_eval(&terms);
        let mut var_map = HashMap::default();
        var_map.insert(x, 2i64);
        var_map.insert(y, 3i64);
        var_map.insert(z, 3i64);
        assert_eq!(solver.eval_term(prod, &var_map), Some(BigInt::from(15)));
    }

    /// Property: ceil(x) - floor(x) is 0 for integers and 1 for non-integers.
    #[test]
    fn test_rational_ceil_minus_floor_is_zero_or_one() {
        let cases = vec![
            BigRational::new(BigInt::from(7), BigInt::from(2)), // non-integer
            BigRational::new(BigInt::from(-7), BigInt::from(2)), // non-integer
            BigRational::new(BigInt::from(6), BigInt::from(2)), // integer (3)
            BigRational::new(BigInt::from(1), BigInt::from(3)), // non-integer
            BigRational::new(BigInt::from(-10), BigInt::from(5)), // integer (-2)
        ];
        for r in &cases {
            let c = rational_ceil(r);
            let f = rational_floor(r);
            let diff = &c - &f;
            assert!(
                diff == BigInt::from(0) || diff == BigInt::from(1),
                "ceil({r}) - floor({r}) = {diff}, expected 0 or 1"
            );
        }
    }

    /// Property: for non-integer x, floor(-x) == -ceil(x).
    #[test]
    fn test_rational_floor_neg_equals_neg_ceil() {
        let cases = vec![
            BigRational::new(BigInt::from(7), BigInt::from(2)),
            BigRational::new(BigInt::from(1), BigInt::from(3)),
            BigRational::new(BigInt::from(100), BigInt::from(7)),
        ];
        for r in &cases {
            let neg_r = -r.clone();
            let floor_neg = rational_floor(&neg_r);
            let neg_ceil = -rational_ceil(r);
            assert_eq!(floor_neg, neg_ceil, "floor(-{r}) should == -ceil({r})");
        }
    }

    /// Large rational: ceil(1000000002/7) = 142857143 + 1 = 142857144.
    /// 1000000002 / 7 = 142857143.14... (not exact), so ceil rounds up.
    #[test]
    fn test_rational_ceil_large_ratio() {
        let r = BigRational::new(BigInt::from(1_000_000_002i64), BigInt::from(7));
        assert_eq!(rational_ceil(&r), BigInt::from(142_857_144i64));
    }

    /// Large negative rational: floor(-1000000002/7) = -142857144.
    #[test]
    fn test_rational_floor_large_negative_ratio() {
        let r = BigRational::new(BigInt::from(-1_000_000_002i64), BigInt::from(7));
        assert_eq!(rational_floor(&r), BigInt::from(-142_857_144i64));
    }

    // ====================================================================
    // i64-rim regressions. Every raw i64 arithmetic site in this file that
    // an asserted bound can drive to the edge of i64. NIA runs IN-PROCESS
    // inside compiler_consumer, so an arithmetic panic here is an ICE that kills the
    // compilation, never a verdict the caller can handle. Each input below
    // is CONSTRUCTED to land on the exact overflowing operation (a random
    // sweep of extremes does not get there), and each carries a companion on
    // the same path over a small box that must still reach a real verdict —
    // a "fix" that declined everything would pass the no-panic assertion
    // alone and be useless.
    // ====================================================================

    /// Which enumeration entry point a constructed box is driven through.
    #[derive(Clone, Copy)]
    enum EnumEntry {
        /// `try_bounded_enumeration`: exact decider, may answer Unsat.
        Exhaustive,
        /// `try_capped_model_search`: SAT-only search, never answers Unsat.
        Capped,
    }

    /// Build `lo <= x <= hi`, `lo <= y <= hi`, `x*y != f` for each `f` in
    /// `forbidden`, and `x*y = c` when `required` is `Some(c)`, all through
    /// the real `assert_literal` ingestion path, then drive `entry`.
    /// Returns the verdict and the recorded witness (if any).
    fn enum_xy_box(
        entry: EnumEntry,
        lo: i64,
        hi: i64,
        forbidden: &[i64],
        required: Option<i64>,
    ) -> (Option<TheoryResult>, Option<HashMap<TermId, BigInt>>) {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let lo_c = terms.mk_int(BigInt::from(lo));
        let hi_c = terms.mk_int(BigInt::from(hi));
        let mut atoms = vec![
            terms.mk_ge(x, lo_c),
            terms.mk_le(x, hi_c),
            terms.mk_ge(y, lo_c),
            terms.mk_le(y, hi_c),
        ];
        for &f in forbidden {
            let f_c = terms.mk_int(BigInt::from(f));
            atoms.push(terms.mk_distinct(vec![xy, f_c]));
        }
        if let Some(c) = required {
            let c_c = terms.mk_int(BigInt::from(c));
            atoms.push(terms.mk_eq(xy, c_c));
        }
        let mut solver = NiaSolver::new(&terms);
        for atom in atoms {
            solver.assert_literal(atom, true);
        }
        let verdict = match entry {
            EnumEntry::Exhaustive => solver.try_bounded_enumeration(),
            EnumEntry::Capped => solver.try_capped_model_search(),
        };
        let model = solver.bounded_enum_model.clone();
        (verdict, model)
    }

    /// Read the witness values of the two enumeration variables `x` and `y`
    /// (by their term ids) as plain i64.
    fn xy_witness(model: &HashMap<TermId, BigInt>, terms_x: TermId, terms_y: TermId) -> (i64, i64) {
        let get = |t: TermId| {
            model
                .get(&t)
                .and_then(|v| v.to_i64())
                .expect("witness must assign every enumeration variable")
        };
        (get(terms_x), get(terms_y))
    }

    #[test]
    fn domain_size_declines_instead_of_panicking_on_full_i64_range() {
        // REGRESSION (2026-09-07, fixed in f5cfe26a9 WITHOUT a test). The
        // domain-size admission check computed `hi - lo + 1` in raw i64,
        // which PANICS ("attempt to subtract with overflow") for a variable
        // bounded to the full i64 range — measured 20 times while compiler_consumer
        // verified `ty`'s workspace. The bounds come straight from the
        // asserted formula, so `[i64::MIN, i64::MAX]` is an ordinary input.
        //
        // The atom is `3*x*x != 27` on purpose: a positive `distinct` is
        // opaque to the interval contractor (Phase 2.5), so nothing shrinks
        // the box before it reaches the admission check. (`3*x*x = 27` would
        // be contracted to `x ∈ [-3, 3]` and never touch the site.) The
        // scaled product also routes `x` in as a scaled-product factor, not a
        // registered monomial (#nia-const-factor), which is the shape the
        // linearization cannot handle and enumeration exists for.
        fn enumerate_scaled_square(lo: i64, hi: i64) -> (Option<TheoryResult>, Option<i64>) {
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", Sort::Int);
            let three = terms.mk_int(BigInt::from(3));
            let sq3 = terms.mk_mul(vec![three, x, x]);
            let c27 = terms.mk_int(BigInt::from(27));
            let lo_c = terms.mk_int(BigInt::from(lo));
            let hi_c = terms.mk_int(BigInt::from(hi));
            let atoms = [
                terms.mk_ge(x, lo_c),
                terms.mk_le(x, hi_c),
                terms.mk_distinct(vec![sq3, c27]),
            ];
            let mut solver = NiaSolver::new(&terms);
            for atom in atoms {
                solver.assert_literal(atom, true);
            }
            let verdict = solver.try_bounded_enumeration();
            let witness = solver
                .bounded_enum_model
                .as_ref()
                .and_then(|m| m.get(&x))
                .and_then(|v| v.to_i64());
            (verdict, witness)
        }

        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            enumerate_scaled_square(i64::MIN, i64::MAX)
        }));
        assert!(
            outcome.is_ok(),
            "try_bounded_enumeration panicked sizing the domain of x ∈ [i64::MIN, i64::MAX] \
             — NIA runs inside compiler_consumer, so a panic here is an ICE, never a solver verdict"
        );
        let (verdict, _) = outcome.unwrap();
        assert!(
            verdict.is_none(),
            "a range too wide to size is a domain too wide to enumerate: the only sound \
             answer is None (not applicable), never a verdict from a saturated size; got \
             {verdict:?}"
        );

        // ANTI-VACUITY: the same path over a small box still decides.
        // x ∈ [-3, 3]: x = ±3 gives 3*9 = 27 (violates), anything else is a
        // witness — enumeration must find one.
        let (verdict, witness) = enumerate_scaled_square(-3, 3);
        assert!(
            matches!(verdict, Some(TheoryResult::Sat)),
            "small box must still be enumerated to a real verdict, got {verdict:?}"
        );
        let w = witness.expect("Sat must record an exact integer witness");
        assert!(
            (-3..=3).contains(&w) && 3 * w * w != 27,
            "witness {w} is not a model"
        );
        // x ∈ [3, 3]: the single point violates the atom, so exhaustive
        // enumeration proves UNSAT.
        let (verdict, _) = enumerate_scaled_square(3, 3);
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "exhausting a box with no model must answer Unsat, got {verdict:?}"
        );
    }

    #[test]
    fn lower_bound_inference_computes_ceil_without_overflow_near_i64_max() {
        // REGRESSION (2026-09-10). Phase 2's lower-bound inference computed
        // `ceil(l / d)` as `(l + d - 1) / d` in raw i64. With `l` (the
        // monomial's lower bound) near i64::MAX and `d` (the product of the
        // other factors' upper bounds) above 1, the intermediate sum PANICS —
        // "attempt to add with overflow" — a refuter reproduced it with a
        // 3-assertion QF_NIA input; the atoms below rebuild that shape. The
        // quotient itself always fits
        // (`1 <= ceil(l/d) <= l`), so the fix computes it as `(l - 1) / d + 1`.
        //
        // Reaching the site needs: `x` with NO lower bound (so the inference
        // fires), `y` strictly positive with `d = 2`, and the aux bound
        // `x*y = i64::MAX` read through `get_monomial_bounds`. With the exact
        // ceiling, `x >= 2^62` contradicts `x <= 10`, so the box is empty and
        // the decider correctly declines (None) — it never claims a verdict.
        fn infer_lower(
            aux_value: i64,
            x_hi: i64,
            leading_atom: Option<fn(&mut TermStore, TermId) -> TermId>,
        ) -> (Option<TheoryResult>, Option<(i64, i64)>) {
            let mut terms = TermStore::new();
            let x = terms.mk_var("x", Sort::Int);
            let y = terms.mk_var("y", Sort::Int);
            let xy = terms.mk_mul(vec![x, y]);
            let mut atoms = Vec::new();
            if let Some(mk) = leading_atom {
                atoms.push(mk(&mut terms, y));
            }
            let one = terms.mk_int(BigInt::from(1));
            let two = terms.mk_int(BigInt::from(2));
            let x_hi_c = terms.mk_int(BigInt::from(x_hi));
            let aux_c = terms.mk_int(BigInt::from(aux_value));
            atoms.push(terms.mk_eq(xy, aux_c));
            atoms.push(terms.mk_ge(y, one));
            atoms.push(terms.mk_le(y, two));
            atoms.push(terms.mk_le(x, x_hi_c));
            let mut solver = NiaSolver::new(&terms);
            for atom in atoms {
                solver.assert_literal(atom, true);
            }
            let verdict = solver.try_bounded_enumeration();
            let witness = solver
                .bounded_enum_model
                .as_ref()
                .map(|m| xy_witness(m, x, y));
            (verdict, witness)
        }

        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            infer_lower(i64::MAX, 10, None)
        }));
        assert!(
            outcome.is_ok(),
            "try_bounded_enumeration panicked inferring x >= ceil(i64::MAX / 2) — NIA runs \
             inside compiler_consumer, so a panic here is an ICE, never a solver verdict"
        );
        let (verdict, _) = outcome.unwrap();
        assert!(
            verdict.is_none(),
            "x >= 2^62 ∧ x <= 10 leaves no box to enumerate; the decider must decline \
             (None), got {verdict:?}"
        );

        // ANTI-VACUITY 1: the same inference over small numbers still
        // completes the box and reaches a real verdict. `x*y = 6`, `y ∈ [1,2]`,
        // `x <= 10` infers `x >= ceil(6/2) = 3`; the box `[3,10]×[1,2]` holds
        // the model (3, 2).
        let (verdict, witness) = infer_lower(6, 10, None);
        assert!(
            matches!(verdict, Some(TheoryResult::Sat)),
            "small-number inference must still complete the box to Sat, got {verdict:?}"
        );
        let (wx, wy) = witness.expect("Sat must record an exact integer witness");
        assert!((3..=10).contains(&wx) && (1..=2).contains(&wy) && wx * wy == 6);

        // ANTI-VACUITY 2 (isolates Phase 2 from the interval contractor,
        // which can derive the same `x >= 3` on its own): a LEADING atom
        // `y*y = 5` is unsatisfiable on `y ∈ [1,2]`, so the contractor hits
        // an empty intersection on it and stops before touching `x*y = 6`
        // (it keeps prior tightenings, derives no more, draws no verdict).
        // Only Phase 2 then supplies `x >= 3`; with it the box is complete and
        // exhaustive enumeration PROVES Unsat. A Phase 2 that skipped the
        // inference would leave `x` unbounded below and answer None instead.
        fn y_squared_is_5(terms: &mut TermStore, y: TermId) -> TermId {
            let yy = terms.mk_mul(vec![y, y]);
            let five = terms.mk_int(BigInt::from(5));
            terms.mk_eq(yy, five)
        }
        let (verdict, _) = infer_lower(6, 10, Some(y_squared_is_5));
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "Phase 2 alone must complete the box so enumeration proves Unsat, got {verdict:?}"
        );

        // EXACTNESS AT THE RIM: the no-panic check above cannot tell the exact
        // ceiling from a saturated `(l.saturating_add(d - 1)) / d`, because
        // with `x <= 10` both `x >= 2^62` (exact) and `x >= 2^62 - 1` (the
        // saturated floor) empty the box and decline. So put the domain
        // exactly AT the cap: `x <= 2^62 + 4999` with `d = 2` gives the exact
        // box `[2^62, 2^62 + 4999] × [1, 2]`, 10_000 points = MAX_ENUM_DOMAIN,
        // admitted and exhausted to a PROVEN Unsat (`x*y = i64::MAX` needs
        // `y = 1`, `x = i64::MAX`, outside the box; `y = 2` cannot produce an
        // odd product — and `y*y = 5` is false throughout anyway). The
        // saturated floor is one point lower, 5001 × 2 = 10_002 > cap, and
        // the decider declines (None) instead. Same leading atom, so the
        // contractor stays out of it and only Phase 2 supplies the bound.
        // `MAX_ENUM_DOMAIN / 2 - 1` = 4999: the x-width that makes the 2-wide box
        // exactly MAX_ENUM_DOMAIN points, so the test moves with the cap.
        let (verdict, _) = infer_lower(
            i64::MAX,
            (1i64 << 62) + (MAX_ENUM_DOMAIN / 2 - 1),
            Some(y_squared_is_5),
        );
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "the exact ceiling x >= 2^62 keeps the box at MAX_ENUM_DOMAIN so enumeration \
             proves Unsat; a floor/saturated bound widens it past the cap and declines — \
             got {verdict:?}"
        );
    }

    #[test]
    fn exhaustive_odometer_reaches_i64_max_without_overflow() {
        // REGRESSION (2026-09-10). The odometer in `try_bounded_enumeration`
        // did `assignment[i] += 1` BEFORE comparing against `hi`, so a digit
        // with `hi == i64::MAX` computed `i64::MAX + 1` on the last step —
        // "attempt to add with overflow", an ICE inside compiler_consumer. Such a box is
        // admitted: the domain-size check only caps the WIDTH, so
        // `[i64::MAX - 1, i64::MAX]²` (4 points) passes. `x*y = 2` has no
        // model there (both factors exceed 2), so enumeration must walk to the
        // last point and then step past it to conclude Unsat. The contractor
        // cannot pre-empt this: its forward interval for `x*y` excludes 2, an
        // empty intersection, which stops it without tightening anything.
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            enum_xy_box(EnumEntry::Exhaustive, i64::MAX - 1, i64::MAX, &[], Some(2))
        }));
        assert!(
            outcome.is_ok(),
            "try_bounded_enumeration panicked stepping the odometer past x = y = i64::MAX \
             — NIA runs inside compiler_consumer, so a panic here is an ICE, never a solver verdict"
        );
        let (verdict, _) = outcome.unwrap();
        match verdict {
            Some(TheoryResult::Unsat(conflict)) => assert_eq!(
                conflict.len(),
                5,
                "the Unsat conflict must cite every asserted atom (4 bounds + x*y = 2)"
            ),
            other => panic!(
                "exhausting [i64::MAX-1, i64::MAX]² with x*y = 2 must be Unsat, got {other:?}"
            ),
        }

        // ANTI-VACUITY: the same odometer over `[1,2]²` visits every point in
        // order. `x*y != 1` and `x*y != 2` reject (1,1), (1,2) and (2,1); the
        // witness must be the LAST point (2,2), proving the odometer walked the
        // whole box rather than short-circuiting.
        let (verdict, model) = enum_xy_box(EnumEntry::Exhaustive, 1, 2, &[1, 2], None);
        assert!(
            matches!(verdict, Some(TheoryResult::Sat)),
            "got {verdict:?}"
        );
        let model = model.expect("Sat must record an exact integer witness");
        let mut vals: Vec<i64> = model.values().filter_map(|v| v.to_i64()).collect();
        vals.sort_unstable();
        assert_eq!(
            vals,
            vec![2, 2, 4],
            "witness must be x = 2, y = 2 (x*y = 4)"
        );
        // And forbidding 4 as well exhausts the box to Unsat.
        let (verdict, _) = enum_xy_box(EnumEntry::Exhaustive, 1, 2, &[1, 2, 4], None);
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "exhausting [1,2]² with every product forbidden must be Unsat, got {verdict:?}"
        );
    }

    // ====================================================================
    // Wall-clock deadline regressions (#nia-enum-deadline).
    //
    // MEASURED 2026-09-11: a `offline deductive checker check` obligation from
    // `ay_sat::symmetry::detector::cc_vertex_classes` pinned one rustc thread
    // at 100% CPU for 7h12m under a 15 s per-function budget. Every sample
    // landed inside ONE `try_capped_model_search` activation. The deadline had
    // reached `NiaSolver::deadline` intact; nothing on the enumeration path
    // ever read it. These tests fix the contract: with an expired deadline
    // every enumeration returns its "no claim" answer promptly, and with a
    // live deadline the same query still reaches its real verdict.
    // ====================================================================

    /// Build the same `x, y ∈ [lo, hi] ∧ x*y = c` box as [`enum_xy_box`] but
    /// install `deadline` on the solver before driving `entry`.
    fn enum_xy_box_with_deadline(
        entry: EnumEntry,
        lo: i64,
        hi: i64,
        required: i64,
        deadline: ay_core::time::Instant,
    ) -> Option<TheoryResult> {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let lo_c = terms.mk_int(BigInt::from(lo));
        let hi_c = terms.mk_int(BigInt::from(hi));
        let c_c = terms.mk_int(BigInt::from(required));
        let atoms = [
            terms.mk_ge(x, lo_c),
            terms.mk_le(x, hi_c),
            terms.mk_ge(y, lo_c),
            terms.mk_le(y, hi_c),
            terms.mk_eq(xy, c_c),
        ];
        let mut solver = NiaSolver::new(&terms);
        for atom in atoms {
            solver.assert_literal(atom, true);
        }
        solver.set_deadline(deadline);
        match entry {
            EnumEntry::Exhaustive => solver.try_bounded_enumeration(),
            EnumEntry::Capped => solver.try_capped_model_search(),
        }
    }

    /// An instant already in the past — an exhausted budget.
    fn expired() -> ay_core::time::Instant {
        ay_core::time::Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("the monotonic clock is more than a second past its epoch")
    }

    /// A budget that cannot plausibly expire during a 10k-point enumeration.
    fn far_future() -> ay_core::time::Instant {
        ay_core::time::Instant::now() + std::time::Duration::from_secs(3600)
    }

    #[test]
    fn capped_search_returns_none_promptly_on_expired_deadline() {
        // A box at the full MAX_ENUM_DOMAIN budget: `[1, 100]²` is 10_000
        // points, each one an exact BigInt evaluation of five atoms. With the
        // deadline already gone the search must decline before walking it.
        let start = ay_core::time::Instant::now();
        let verdict = enum_xy_box_with_deadline(EnumEntry::Capped, 1, 100, 7, expired());
        let took = start.elapsed();
        assert!(
            verdict.is_none(),
            "an expired deadline must abort the capped search at its existing \
             no-witness answer (None), never a verdict — got {verdict:?}"
        );
        assert!(
            took < std::time::Duration::from_millis(250),
            "the capped search must abort at the FIRST poll, not after the box \
             — took {took:?}"
        );

        // ANTI-VACUITY: the identical query under a live deadline still walks
        // the box and finds the witness (1*7 = 7 is inside `[1,100]²`). A
        // "fix" that declined whenever a deadline was installed would pass the
        // assertion above and be useless.
        let verdict = enum_xy_box_with_deadline(EnumEntry::Capped, 1, 100, 7, far_future());
        assert!(
            matches!(verdict, Some(TheoryResult::Sat)),
            "with budget left the capped search must still verify x*y = 7 — got {verdict:?}"
        );
    }

    #[test]
    fn exhaustive_enumeration_declines_instead_of_claiming_unsat_on_expired_deadline() {
        // `x, y ∈ [1, 100] ∧ x*y = 9973` (prime, > 100²-reachable only as
        // 1*9973) is UNSAT over the box, so the decider's normal answer is
        // Unsat after 10_000 points. Aborting must NOT fall out of the loop —
        // that exit IS the Unsat claim — so the verdict must be None.
        let start = ay_core::time::Instant::now();
        let verdict = enum_xy_box_with_deadline(EnumEntry::Exhaustive, 1, 100, 9973, expired());
        let took = start.elapsed();
        assert!(
            verdict.is_none(),
            "an expired deadline must abort the exhaustive decider at None \
             (not applicable); exhausting the box is the ONLY licence for its \
             Unsat — got {verdict:?}"
        );
        assert!(
            took < std::time::Duration::from_millis(250),
            "the exhaustive decider must abort at the FIRST poll — took {took:?}"
        );

        // ANTI-VACUITY: with budget left the same box IS exhausted and the
        // genuine Unsat comes back.
        let verdict = enum_xy_box_with_deadline(EnumEntry::Exhaustive, 1, 100, 9973, far_future());
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "with budget left the box must still be exhausted to Unsat — got {verdict:?}"
        );
    }

    #[test]
    fn capped_search_polls_the_deadline_while_walking_the_box() {
        // The poll must fire INSIDE the walk, not only on entry. Calibrate
        // first: walk the full 10_000-point box with no usable budget pressure
        // and measure it, then re-run with a budget that is a small fraction of
        // that and require the answer back near the budget rather than near the
        // full walk.
        let start = ay_core::time::Instant::now();
        let full = enum_xy_box_with_deadline(EnumEntry::Capped, 1, 100, 9973, far_future());
        let full_took = start.elapsed();
        assert!(
            full.is_none(),
            "x*y = 9973 (prime, > 100) has no witness in [1,100]²; the capped \
             window proves nothing, so the answer is None — got {full:?}"
        );

        let budget = std::time::Duration::from_millis(1);
        let start = ay_core::time::Instant::now();
        let verdict = enum_xy_box_with_deadline(
            EnumEntry::Capped,
            1,
            100,
            9973,
            ay_core::time::Instant::now() + budget,
        );
        let took = start.elapsed();
        assert!(verdict.is_none(), "got {verdict:?}");

        // Only assert the cut when the full walk is long enough for a 1 ms
        // budget to be distinguishable at all; on a machine fast enough to
        // finish the whole box inside a few budgets there is nothing to
        // measure. On THIS hardware the full walk is tens of microseconds, so
        // the guard never fires and this assertion alone would be vacuous —
        // which is why the poll COUNT below, not the clock, is what pins the
        // contract.
        if full_took >= budget * 4 {
            assert!(
                took <= budget + full_took / 4 + std::time::Duration::from_millis(2),
                "the mid-walk poll must cut the walk short: budget {budget:?}, \
                 unbounded walk {full_took:?}, aborted walk {took:?}"
            );
        }
    }

    #[test]
    fn enumerations_poll_the_deadline_once_per_256_points_not_only_on_entry() {
        // REGRESSION (2026-09-11, review of the deadline commit). The two
        // expired-deadline tests above are both discharged by the ENTRY poll
        // alone (`visited == 0`), and the calibration test's cut assertion is
        // gated behind a 4 ms floor that a 10_000-point box never reaches here
        // — so weakening `enum_deadline_expired` to poll once and never again
        // left the whole suite green. That weakened shape IS the defect: the
        // 7h12m hang was ONE `try_capped_model_search` activation that had
        // already passed its entry.
        //
        // Counting polls pins the property exactly and without a clock: an
        // entry-only poll counts 1, the real thing counts one per
        // ENUM_DEADLINE_POLL_POINTS points walked.
        let min_polls = (10_000 / ENUM_DEADLINE_POLL_POINTS) as u64;

        // `x*y = 9973` (prime, > 100) has no witness anywhere in `[1,100]²`,
        // so both entries walk all 10_000 points with a budget that never
        // expires — the longest walk either routine admits.
        reset_enum_deadline_polls();
        let verdict = enum_xy_box_with_deadline(EnumEntry::Capped, 1, 100, 9973, far_future());
        let capped_polls = enum_deadline_polls();
        assert!(verdict.is_none(), "got {verdict:?}");
        assert!(
            capped_polls >= min_polls,
            "try_capped_model_search must read the clock every \
             {ENUM_DEADLINE_POLL_POINTS} points of the 10_000-point box \
             (>= {min_polls} polls), got {capped_polls} — an entry-only poll \
             counts 1 and is exactly what spun for 7h12m"
        );

        // The exhaustive decider first CONTRACTS the box (its intervals are
        // derived from the real constraints), so the walk it actually performs
        // is smaller than 10_000 points and its poll count is the contracted
        // box's, not the nominal one: `x*y = 2003` (prime) leaves ~2_000 points
        // here. The property under test is the same — more than the single
        // entry poll — so assert against the walk it really does.
        reset_enum_deadline_polls();
        let verdict = enum_xy_box_with_deadline(EnumEntry::Exhaustive, 1, 100, 2003, far_future());
        let exhaustive_polls = enum_deadline_polls();
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "x*y = 2003 (prime, > 100) has no model in [1,100]², so the box must \
             be exhausted to Unsat — got {verdict:?}"
        );
        assert!(
            exhaustive_polls >= 4,
            "try_bounded_enumeration must read the clock every \
             {ENUM_DEADLINE_POLL_POINTS} points of the box it walks (>= 1_024 \
             points here), got {exhaustive_polls} polls — 1 means entry-only"
        );

        // ANTI-VACUITY for the counter itself: it counts polls, not calls, so
        // a routine that never enumerates registers none.
        reset_enum_deadline_polls();
        let verdict = enum_xy_box_with_deadline(EnumEntry::Capped, 1, 1, 7, far_future());
        assert!(verdict.is_none(), "1*1 != 7, got {verdict:?}");
        assert_eq!(
            enum_deadline_polls(),
            1,
            "a single-point box polls exactly once (its entry poll)"
        );
    }

    #[test]
    fn capped_search_odometer_reaches_i64_max_without_overflow() {
        // REGRESSION (2026-09-10). Same defect, second odometer:
        // `try_capped_model_search` incremented before comparing, so a
        // genuine bound `hi == i64::MAX` overflowed on the last step. Its
        // admission is the same width cap, so `[i64::MAX - 1, i64::MAX]²`
        // is searched in full. This entry is SAT-only: exhausting the window
        // without a witness must answer None (unknown), never Unsat.
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            enum_xy_box(EnumEntry::Capped, i64::MAX - 1, i64::MAX, &[], Some(2))
        }));
        assert!(
            outcome.is_ok(),
            "try_capped_model_search panicked stepping the odometer past x = y = i64::MAX \
             — NIA runs inside compiler_consumer, so a panic here is an ICE, never a solver verdict"
        );
        let (verdict, _) = outcome.unwrap();
        assert!(
            verdict.is_none(),
            "the capped window is artificial, so exhausting it proves nothing: None, got \
             {verdict:?}"
        );

        // ANTI-VACUITY: the capped odometer over `[1,2]²` still walks to the
        // last point (2,2) and returns the verified witness.
        let (verdict, model) = enum_xy_box(EnumEntry::Capped, 1, 2, &[1, 2], None);
        assert!(
            matches!(verdict, Some(TheoryResult::Sat)),
            "got {verdict:?}"
        );
        let model = model.expect("Sat must record an exact integer witness");
        let mut vals: Vec<i64> = model.values().filter_map(|v| v.to_i64()).collect();
        vals.sort_unstable();
        assert_eq!(
            vals,
            vec![2, 2, 4],
            "witness must be x = 2, y = 2 (x*y = 4)"
        );
    }
}
