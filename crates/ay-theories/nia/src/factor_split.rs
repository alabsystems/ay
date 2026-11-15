// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded factor case-split linearization (#nia-factor-split).
//!
//! Industrial QF_NIA (AProVE / T2 termination and safety VCs) routinely
//! constrains a few monomial factors to TINY asserted boxes — e.g. a strategy
//! flag `0 <= b <= 1` multiplied into most products. Pinning such a factor to
//! one concrete value makes every product it participates in either constant
//! or LINEAR in the remaining factor, so a per-value case split turns big
//! parts of the problem into exact LIA:
//!
//!   `x*y` with `x ∈ [0,1]`  ⇒  branch x=0: `aux = 0`; branch x=1: `aux = y`.
//!
//! The split enumerates every assignment of a budget-capped set of small-box
//! factors. In each branch it pins the chosen factors and asserts the EXACT
//! product equalities implied by the pins, then re-runs the inner LIA check:
//!
//! * **UNSAT** is claimed only when EVERY branch of the complete cover is
//!   refuted by LIA. Soundness: (1) the per-variable boxes come ONLY from
//!   asserted var-vs-constant atoms (`asserted_integer_bound`), never from
//!   tangent-plane-polluted LRA bounds, so the cover is genuinely complete;
//!   (2) the pin cuts and product equalities are exact consequences of the
//!   branch's assignment; (3) any remaining (≥2 unpinned factors) products
//!   stay opaque — an over-approximation — and LIA-UNSAT of a relaxation
//!   refutes the branch a fortiori.
//! * **SAT** is claimed only for a branch model whose integer point passes
//!   exact re-evaluation of EVERY asserted atom (`check_assignment`,
//!   fail-closed) — a verified witness, independent of how it was found.
//! * Anything else falls through as `None` (unknown), never a wrong verdict.

use ay_core::{TheoryLit, TheoryResult};
use ay_lra::rational::Rational;
use num_traits::{One, ToPrimitive, Zero};

use super::factor_split_provenance::{BranchPremises, Premises};
use super::*;

/// Maximum width (`hi - lo + 1`) of an asserted box for a factor to be
/// eligible for pinning.
const MAX_FACTOR_SPLIT_WIDTH: i64 = 8;

/// Maximum total number of branches (product of chosen factor widths).
const MAX_FACTOR_SPLIT_BRANCHES: i64 = 64;

/// Skip the split entirely on very large problems: each invocation costs up
/// to [`MAX_FACTOR_SPLIT_BRANCHES`] inner LIA checks. 512 admits the AProVE
/// multi-flag termination VCs (e.g. aproveSMT7186…: 330 monomials, 6 flag
/// boxes) while still excluding the truly huge mcm/calypto tableaus.
const MAX_FACTOR_SPLIT_MONOMIALS: usize = 512;

/// Maximum number of `±divisor` branches enumerated for one
/// `(= monomial k)` atom by the divisor case-split (each branch is one
/// inner LIA re-check). Matches the box split's [`MAX_FACTOR_SPLIT_BRANCHES`]
/// so the two mechanisms share a cost ceiling.
const MAX_DIVISOR_SPLIT_BRANCHES: usize = 64;

/// Trial-division cost cap for divisor enumeration: a constant `k` with
/// `|k| > MAX_DIVISOR_TRIAL²` would need more than `MAX_DIVISOR_TRIAL`
/// trial steps to factor exactly, so it is skipped (fall back to `unknown`)
/// rather than risk a long factorization. `10⁶` admits `|k|` up to `10¹²`.
const MAX_DIVISOR_TRIAL: i64 = 1_000_000;

/// Enumerate the signed divisor set `±D(|k|) = {d : d | k}` of a NONZERO
/// integer `k`, sorted ascending — or `None` when the enumeration is out of
/// budget (`|k|` too large to factor cheaply, or more than `max` positive
/// divisors). A `None` return NEVER yields a partial list: the caller relies
/// on the returned set being a COMPLETE cover of an integer factor of `k`
/// (every integer factor `v` of a product equal to `k` satisfies `v | k`),
/// so a truncated set would make an UNSAT verdict unsound.
fn signed_divisors_i64(k: i64, max: usize) -> Option<Vec<i64>> {
    // `checked_abs` rejects `i64::MIN` (no positive magnitude).
    let n = k.checked_abs()?;
    if n == 0 {
        return None;
    }
    let mut pos: Vec<i64> = Vec::new();
    let mut i: i64 = 1;
    loop {
        // Stop once i² exceeds n: every divisor pair (i, n/i) has been seen.
        match i.checked_mul(i) {
            Some(sq) if sq <= n => {}
            _ => break,
        }
        if i > MAX_DIVISOR_TRIAL {
            // |k| > MAX_DIVISOR_TRIAL²: too costly to factor exactly. Skip
            // (a partial cover would be unsound); the caller falls back.
            return None;
        }
        if n % i == 0 {
            pos.push(i);
            let j = n / i;
            if j != i {
                pos.push(j);
            }
            if pos.len() > max {
                // Highly composite: more than `max` positive divisors would
                // exceed the branch budget. Skip rather than truncate.
                return None;
            }
        }
        i += 1;
    }
    // Signed, sorted cover: each positive divisor and its negation.
    let mut out: Vec<i64> = Vec::with_capacity(pos.len() * 2);
    for &d in &pos {
        out.push(d);
        out.push(-d);
    }
    out.sort_unstable();
    Some(out)
}

impl NiaSolver<'_> {
    /// Bounded factor case-split linearization (see module docs). Returns
    /// `Some(Sat)` with a verified witness, `Some(Unsat)` from a refuted
    /// complete cover, or `None` (out of fragment / budget / inconclusive).
    /// Whether some monomial factor has a COMPLETE small box only
    /// through this check's contracted bounds
    /// (#nia-mccormick-contracted-bounds): incomplete from asserted
    /// var-vs-constant atoms alone, complete after intersecting the
    /// contractor stash. Gates the `NeedSplit` interception in the
    /// check loop — a contracted finite box is exact progress the
    /// branch-and-bound walk cannot make, while a merely asserted box
    /// keeps the historical forwarding discipline.
    pub(crate) fn has_contracted_factor_candidate(&self) -> bool {
        if self.contracted_bounds.is_empty() {
            return false;
        }
        let mut factor_vars: Vec<TermId> = Vec::new();
        for mon in self.monomials.values() {
            for &v in &mon.vars {
                if !factor_vars.contains(&v) {
                    factor_vars.push(v);
                }
            }
        }
        let mut var_bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::default();
        self.apply_asserted_integer_bounds(&factor_vars, &mut var_bounds);
        factor_vars.iter().any(|&v| {
            let (alo, ahi) = var_bounds.get(&v).copied().unwrap_or((None, None));
            if alo.is_some() && ahi.is_some() {
                return false;
            }
            let Some(&(clo, chi)) = self.contracted_bounds.get(&v) else {
                return false;
            };
            let lo = match (alo, clo) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (a, b) => a.or(b),
            };
            let hi = match (ahi, chi) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            };
            match (lo, hi) {
                (Some(lo), Some(hi)) => {
                    lo <= hi
                        && hi
                            .checked_sub(lo)
                            .and_then(|w| w.checked_add(1))
                            .is_some_and(|w| w <= MAX_FACTOR_SPLIT_WIDTH)
                }
                _ => false,
            }
        })
    }

    pub(crate) fn try_bounded_factor_split(&mut self) -> Option<TheoryResult> {
        // Divisor case-split (#nia-divisor-split): when a monomial is asserted
        // EQUAL to a nonzero integer constant `k`, every integer factor of the
        // product divides `k`, so the finite signed divisor set `±D(|k|)` is a
        // COMPLETE cover of that factor. This decides the unbounded-factor
        // shapes the box split below cannot (e.g. `a*b = 1 ∧ a > 1`, where
        // neither factor has an asserted box). Tried first; it early-returns
        // `None` cheaply when no such atom exists.
        if let Some(result) = self.try_divisor_split() {
            return Some(result);
        }
        if self.monomials.is_empty() || self.monomials.len() > MAX_FACTOR_SPLIT_MONOMIALS {
            return None;
        }
        // Pins go into their own LIA scopes; drop any speculative patch scope
        // first so push/pop bookkeeping below stays exact.
        self.undo_tentative_patch();

        // 1. Candidate factors: monomial factor vars with a COMPLETE small box
        //    derived from asserted var-vs-constant atoms only (sound cover).
        let mut factor_vars: Vec<TermId> = Vec::new();
        for mon in self.monomials.values() {
            for &v in &mon.vars {
                if !factor_vars.contains(&v) {
                    factor_vars.push(v);
                }
            }
        }
        factor_vars.sort_by_key(|t| t.0);
        let mut var_bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::default();
        self.apply_asserted_integer_bounds(&factor_vars, &mut var_bounds);
        // #nia-product-sum-bound: intersect with this check's contracted
        // bounds (stashed by bounded enumeration). A contracted endpoint
        // is implied by the asserted literals as a whole, so a factor
        // whose box only completes through contraction is still a sound
        // cover — its cover reasons below then include every asserted
        // literal. Track which factors the stash actually tightened.
        let mut contracted_sides: Vec<(TermId, bool)> = Vec::new();
        for &v in &factor_vars {
            let Some(&(clo, chi)) = self.contracted_bounds.get(&v) else {
                continue;
            };
            let entry = var_bounds.entry(v).or_insert((None, None));
            let new_lo = match (entry.0, clo) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (a, b) => a.or(b),
            };
            let new_hi = match (entry.1, chi) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            };
            if new_lo == clo && clo.is_some() && new_lo != entry.0 {
                contracted_sides.push((v, true));
            }
            if new_hi == chi && chi.is_some() && new_hi != entry.1 {
                contracted_sides.push((v, false));
            }
            *entry = (new_lo, new_hi);
        }
        let mut candidates: Vec<(TermId, i64, i64)> = Vec::new();
        for &v in &factor_vars {
            if let Some(&(Some(lo), Some(hi))) = var_bounds.get(&v) {
                if lo > hi {
                    // Asserted box already empty: LIA refutes this on its own.
                    return None;
                }
                let width = hi.checked_sub(lo)?.checked_add(1)?;
                if width <= MAX_FACTOR_SPLIT_WIDTH {
                    candidates.push((v, lo, hi));
                }
            }
        }
        if candidates.is_empty() {
            return None;
        }

        // 2. Greedy selection: narrowest boxes first, capped branch product.
        candidates.sort_by_key(|&(v, lo, hi)| (hi - lo, v.0));
        let mut chosen: Vec<(TermId, i64, i64)> = Vec::new();
        let mut branches: i64 = 1;
        for &(v, lo, hi) in &candidates {
            let width = hi - lo + 1;
            match branches.checked_mul(width) {
                Some(b) if b <= MAX_FACTOR_SPLIT_BRANCHES => {
                    branches = b;
                    chosen.push((v, lo, hi));
                }
                _ => break,
            }
        }
        if chosen.is_empty() {
            return None;
        }
        if self.debug {
            safe_eprintln!(
                "[NIA] Factor split: {} branches over {:?}",
                branches,
                chosen
                    .iter()
                    .map(|(v, lo, hi)| format!("{v:?}:[{lo},{hi}]"))
                    .collect::<Vec<_>>()
            );
        }

        // Wall-clock abort BEFORE the priming solve (#nia-enum-deadline). The
        // priming `lia.check()` below is an unbounded LIA solve AND, on its
        // Unsat arm, a RETURNED VERDICT — so with the budget already gone the
        // old order both spent time it did not have and answered out of it.
        // The verdict itself was never wrong (LIA reports `Unknown`, never
        // `Unsat`, on its own expiry), but a deadline that is already past
        // must stop the work from starting. `None` is this routine's ordinary
        // "inconclusive" answer, so declining here claims nothing.
        if self.should_timeout() {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Factor split: wall-clock deadline already exceeded — returning None \
                     (unknown) before the priming LIA check"
                );
            }
            return None;
        }

        // The once-per-solve probe (#nia-split-probe): SAT-only. When this
        // split refutes every branch, nothing downstream offers the local
        // search, which does not depend on the current assignment.
        if let Some(result) = self.try_split_probe() {
            return Some(result);
        }

        // Prime the inner solver: branch scopes stack cuts on top of the
        // CURRENT tableau, so the asserted atoms must have been processed by
        // at least one check. In the solve pipeline a check always precedes
        // this call; direct callers (tests) may not have run one.
        match self.lia.check() {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                // The un-split (exact-only) tableau is already infeasible.
                return Some(TheoryResult::Unsat(self.full_conflict_lits()));
            }
            _ => {}
        }

        // Cover atoms: the asserted var-vs-constant atoms that justify the
        // chosen factors' boxes. Together with each branch's own refutation
        // literals they form a SOUND minimal conflict (see aggregation below).
        let mut cover_reasons: Vec<TheoryLit> = Vec::new();
        for &(term, positive) in &self.asserted {
            if let Some((var, _, _)) = self.asserted_integer_bound(term, positive) {
                if chosen.iter().any(|&(v, _, _)| v == var) {
                    cover_reasons.push(TheoryLit {
                        term,
                        value: positive,
                    });
                }
            }
        }
        // A chosen factor whose box was completed by a contracted
        // endpoint cites that endpoint's recorded product-sum
        // premises when available (a handful of literals); only a
        // contracted side without narrow provenance falls back to
        // citing every asserted literal (the contractor's soundness
        // contract justifies the endpoint from the trail as a whole).
        let mut need_full_cover = false;
        for &(v, _, _) in &chosen {
            for is_lower in [true, false] {
                if !contracted_sides.contains(&(v, is_lower)) {
                    continue;
                }
                match self.contracted_bound_reasons.get(&(v, is_lower)) {
                    Some(lits) => {
                        for &(term, positive) in lits {
                            let lit = TheoryLit {
                                term,
                                value: positive,
                            };
                            if !cover_reasons.contains(&lit) {
                                cover_reasons.push(lit);
                            }
                        }
                    }
                    None => need_full_cover = true,
                }
            }
        }
        if need_full_cover {
            for &(term, positive) in &self.asserted {
                let lit = TheoryLit {
                    term,
                    value: positive,
                };
                if !cover_reasons.contains(&lit) {
                    cover_reasons.push(lit);
                }
            }
        }

        // Per-split precomputation (#nia-factor-split-skeleton): the sorted
        // monomial snapshot and the asserted atoms' linear skeletons are the
        // same for every branch (neither `self.monomials` nor `self.asserted`
        // changes inside one), so build them once here instead of per branch
        // and per pass.
        let monomials = self.monomial_snapshot();
        let skeletons = self.build_atom_skeletons();
        if self.debug {
            safe_eprintln!(
                "[NIA] Factor split: {} monomials, {} atom skeletons, lra rows={}",
                monomials.len(),
                skeletons.len(),
                self.lia.lra_solver().row_count()
            );
        }

        // 3. Enumerate every assignment of the chosen factors. The in-branch
        //    repair search costs up to MAX_ENUM_DOMAIN exact evaluations per
        //    branch, so it is only enabled for small splits.
        let repair_in_branch = branches <= 16;
        let mut assignment: Vec<i64> = chosen.iter().map(|&(_, lo, _)| lo).collect();
        let mut all_branches_unsat = true;
        // Union of the per-branch refutation literals, when EVERY refuted
        // branch produced a minimal explanation (see BranchOutcome::Refuted).
        let mut minimal_union: Option<Vec<TheoryLit>> = Some(Vec::new());
        // Whether any branch was refuted on the tableau (see `split_conflict`).
        let mut tableau_refuted = false;
        let mut visited: i64 = 0;
        loop {
            // Wall-clock abort (#nia-enum-deadline). One branch is a full inner
            // LIA push/check/pop plus (when enabled) a 10k-point exact repair
            // search, so the clock is read once per branch rather than once per
            // 256 points. MUST be a `return None`, not a `break`: leaving this
            // loop normally is what licenses the aggregated UNSAT below, and a
            // partially enumerated cover is not complete. `None` is this
            // routine's ordinary "inconclusive" answer.
            if self.should_timeout() {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Factor split: wall-clock deadline exceeded after {visited} \
                         branches — returning None (unknown), no UNSAT claim"
                    );
                }
                return None;
            }
            // Defensive visit bound (#nia-enum-visit-bound): the odometer
            // exhausts the cover in exactly `branches` steps. Declining rather
            // than breaking keeps the cover-completeness argument honest.
            if visited >= branches {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Factor split: visit bound {branches} reached without the \
                         odometer signalling exhaustion — returning None (unknown)"
                    );
                }
                return None;
            }
            visited += 1;

            let branch_result = self.check_factor_split_branch(
                &chosen,
                &assignment,
                repair_in_branch,
                &monomials,
                &skeletons,
            );
            match branch_result {
                BranchOutcome::Refuted { literals, lra } => {
                    tableau_refuted |= lra;
                    match (&mut minimal_union, literals) {
                        (Some(union), Some(lits)) => union.extend(lits),
                        _ => minimal_union = None,
                    }
                }
                BranchOutcome::VerifiedSat => {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Factor split: verified SAT witness in branch {:?}",
                            assignment
                        );
                    }
                    return Some(TheoryResult::Sat);
                }
                BranchOutcome::Open => {
                    all_branches_unsat = false;
                }
            }

            // Odometer-style advance.
            //
            // Compare BEFORE incrementing — the same fix, and the same reason,
            // as the two odometers in `bounded_enum.rs` (2026-09-10). `+= 1`
            // ahead of the `> hi` test computes `i64::MAX + 1` on the last step
            // of a digit whose `hi == i64::MAX`, and such a box IS admitted
            // here: the admission test is the WIDTH cap `hi - lo + 1 <=
            // MAX_FACTOR_SPLIT_WIDTH` (see the candidate loop above), so
            // `[i64::MAX - 3, i64::MAX]` passes. Under `overflow-checks = true`
            // (ay's own profiles) that is a panic; inside `compiler_consumer`, which is
            // built with overflow checks OFF, it WRAPS to `i64::MIN`, the
            // `> hi` test is false, the carry clears, and the digit counts up
            // from `i64::MIN` — an unbounded branch loop, each step paying a
            // full inner LIA check. Same points, same order: a digit `a` in
            // `[lo, hi]` advances to `a + 1` exactly when `a < hi` (the old
            // `a + 1 > hi` test negated), and otherwise wraps to `lo` and
            // carries; `a ∈ [lo, hi]` holds because `lo > hi` was rejected at
            // candidate selection.
            let mut carry = true;
            for i in (0..chosen.len()).rev() {
                if carry {
                    if assignment[i] < chosen[i].2 {
                        assignment[i] += 1;
                        carry = false;
                    } else {
                        assignment[i] = chosen[i].1;
                        // carry continues
                    }
                }
            }
            if carry {
                break;
            }
        }

        if self.debug {
            safe_eprintln!(
                "[NIA] Factor split: after {} branches lra rows={}",
                branches,
                self.lia.lra_solver().row_count()
            );
        }
        if all_branches_unsat {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Factor split: all {} branches refuted -- UNSAT",
                    branches
                );
            }
            let conflict = self.split_conflict(minimal_union, cover_reasons, tableau_refuted);
            return Some(TheoryResult::Unsat(conflict));
        }
        None
    }

    /// The conflict of a complete case split whose every branch was refuted
    /// (#nia-factor-split-conflict).
    ///
    /// When every branch was refuted in round 0 with an explanation `E_i`
    /// (`BranchOutcome::Refuted { literals: Some(E_i) }`), the union of those
    /// explanations plus the cover atoms is a sound conflict:
    ///   `cover ⇒ ⋁_i pins_i`  (the cover enumerates completely)
    ///   `pins_i ∧ E_i ⇒ ⊥`   (branch i's refutation)
    /// hence `cover ∧ ⋀_i E_i ⇒ ⊥`. `E_i` must name every premise of every
    /// sentinel-reason cut the branch used. The chosen pins and the
    /// linearizations over them are implied by `pins_i` alone; the pins the
    /// linearized-atom contraction DERIVES, the linearizations over those and
    /// the monotonicity cuts are implied by `pins_i` AND the asserted atoms, so
    /// `E_i` carries the asserted literals whenever the branch derived anything
    /// (#nia-factor-split-premises: the union once omitted them — `x ∈ [0,1] ∧
    /// x + y = 3 ∧ y*z >= 5 ∧ z <= 1` was explained without `x + y = 3`, a
    /// clause that is not a theorem, and generated QF_NIA files were answered
    /// `unsat`). A small conflict gives DPLL(T) a usable learned clause
    /// instead of the full set.
    ///
    /// Falls back to [`Self::full_conflict_lits`] when some branch has no
    /// explanation (contraction rounds carry tableau-level justifications no
    /// literal list captures), when a branch was refuted ON THE TABLEAU while
    /// congruence shared-equality lemmas are linked (their premises are
    /// invisible to LRA conflict literals; a branch the linearized-atom
    /// contraction refuted read the asserted atoms alone and cannot have used
    /// one — #nia-factor-split-congruence-scope), or when a literal is not a
    /// live premise (defensive: a stale literal would make the clause
    /// unsound). A live premise is an asserted literal or the reason
    /// of an EUF shared fact the LRA cited because a branch refutation used it.
    fn split_conflict(
        &self,
        minimal_union: Option<Vec<TheoryLit>>,
        cover: Vec<TheoryLit>,
        tableau_refuted: bool,
    ) -> Vec<TheoryLit> {
        let Some(mut union) = minimal_union else {
            return self.full_conflict_lits();
        };
        if tableau_refuted && !self.congruence_linked.is_empty() {
            return self.full_conflict_lits();
        }
        union.extend(cover);
        union.sort_unstable_by_key(|l| (l.term.0, l.value));
        union.dedup_by_key(|l| (l.term.0, l.value));
        let shared: HashSet<TheoryLit> = self.lia.shared_constraint_reasons().into_iter().collect();
        if union.is_empty() || !union.iter().all(|l| self.is_live_premise(l, &shared)) {
            return self.full_conflict_lits();
        }
        union
    }

    /// Divisor case-split (#nia-divisor-split). Returns `Some(Unsat)` from a
    /// refuted complete cover, `Some(Sat)` with a verified witness, or `None`
    /// (no eligible atom / out of budget / inconclusive).
    ///
    /// SOUNDNESS. When an asserted positive equality pins a registered
    /// monomial's aux var to a nonzero integer constant `k`, the monomial
    /// invariant gives `aux == product(vars)` EXACTLY (only const-factor-1
    /// products are registered — see `collect_nonlinear_terms`), so
    /// `product(vars) = k`. Every factor `v ∈ vars` is an integer and
    /// `k = v · (product of the other factors)` with the cofactor an integer,
    /// hence `v | k`. Therefore `v` ranges over the FINITE signed divisor set
    /// `±D(|k|)` in every model: case-splitting `v` over that set is a
    /// COMPLETE cover. UNSAT is claimed only when EVERY branch is refuted
    /// (each branch refutation is an exact LRA/contraction consequence, sound
    /// a fortiori for the integer branch); SAT only for an exactly-verified
    /// branch witness. Budget: the divisor set is capped
    /// ([`MAX_DIVISOR_SPLIT_BRANCHES`]) and enumeration cost is bounded
    /// ([`MAX_DIVISOR_TRIAL`]); anything out of budget falls back to `None`.
    pub(crate) fn try_divisor_split(&mut self) -> Option<TheoryResult> {
        if self.monomials.is_empty() || self.monomials.len() > MAX_FACTOR_SPLIT_MONOMIALS {
            return None;
        }
        // Pins go into their own LIA scopes; drop any speculative patch scope
        // first so push/pop bookkeeping in the branch checker stays exact.
        self.undo_tentative_patch();

        let (factor, divisors, target_atom) = self.find_divisor_split_target()?;
        if self.debug {
            safe_eprintln!(
                "[NIA] Divisor split: factor {:?} over {} divisors {:?}",
                factor,
                divisors.len(),
                divisors
            );
        }

        // Wall-clock abort BEFORE the priming solve (#nia-enum-deadline). The
        // priming `lia.check()` below is an unbounded LIA solve AND, on its
        // Unsat arm, a RETURNED VERDICT — so with the budget already gone the
        // old order both spent time it did not have and answered out of it.
        // The verdict itself was never wrong (LIA reports `Unknown`, never
        // `Unsat`, on its own expiry), but a deadline that is already past
        // must stop the work from starting. `None` is this routine's ordinary
        // "inconclusive" answer, so declining here claims nothing.
        if self.should_timeout() {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Divisor split: wall-clock deadline already exceeded — returning None \
                     (unknown) before the priming LIA check"
                );
            }
            return None;
        }

        // Prime the inner LIA: branch scopes stack cuts on the CURRENT tableau,
        // so the asserted atoms must have been processed by at least one check.
        match self.lia.check() {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                return Some(TheoryResult::Unsat(self.full_conflict_lits()));
            }
            _ => {}
        }

        // The in-branch repair search costs up to MAX_ENUM_DOMAIN exact
        // evaluations per branch; only enable it for small covers.
        let repair_in_branch = divisors.len() <= 16;
        let chosen = [(factor, 0i64, 0i64)];
        // Per-split precomputation (see `try_bounded_factor_split`).
        let monomials = self.monomial_snapshot();
        let skeletons = self.build_atom_skeletons();
        let mut all_refuted = true;
        // Union of the branch explanations, while every refuted branch has one
        // (see `split_conflict`).
        let mut minimal_union: Option<Vec<TheoryLit>> = Some(Vec::new());
        let mut tableau_refuted = false;
        for &d in &divisors {
            // Wall-clock abort (#nia-enum-deadline), one poll per branch as in
            // the box split. Returning `None` mid-cover is required: the UNSAT
            // below is licensed only by refuting EVERY branch of the complete
            // divisor cover.
            if self.should_timeout() {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Divisor split: wall-clock deadline exceeded — returning \
                         None (unknown), no UNSAT claim"
                    );
                }
                return None;
            }
            match self.check_factor_split_branch(
                &chosen,
                &[d],
                repair_in_branch,
                &monomials,
                &skeletons,
            ) {
                BranchOutcome::Refuted { literals, lra } => {
                    tableau_refuted |= lra;
                    match (&mut minimal_union, literals) {
                        (Some(union), Some(lits)) => union.extend(lits),
                        _ => minimal_union = None,
                    }
                }
                BranchOutcome::VerifiedSat => {
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Divisor split: verified SAT witness in branch {factor:?}={d}"
                        );
                    }
                    return Some(TheoryResult::Sat);
                }
                BranchOutcome::Open => all_refuted = false,
            }
        }
        if all_refuted {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Divisor split: all {} branches refuted -- UNSAT",
                    divisors.len()
                );
            }
            // The complete cover is refuted in every branch. Its one premise is
            // the asserted `(= aux k)` atom (with `aux = product(vars)` and every
            // factor an integer, `factor | k`), so the cover literal is that
            // atom; the branches' explanations do the rest (`split_conflict`).
            let cover = vec![TheoryLit::new(target_atom, true)];
            return Some(TheoryResult::Unsat(self.split_conflict(
                minimal_union,
                cover,
                tableau_refuted,
            )));
        }
        None
    }

    /// Find a divisor-split target: an asserted positive equality
    /// `(= aux k)` / `(= k aux)` where `aux` is a registered monomial's aux
    /// var and `k` a NONZERO integer constant. Returns the chosen factor
    /// variable, the complete signed divisor cover `±D(|k|)` and the atom that
    /// licenses it (the cover's premise), preferring
    /// the atom with the FEWEST branches (smallest divisor set) to bound cost.
    /// Skips atoms whose factors are not all integer-sorted (the `v | k`
    /// argument needs every factor to be an integer) and those out of budget.
    fn find_divisor_split_target(&self) -> Option<(TermId, Vec<i64>, TermId)> {
        let mut best: Option<(TermId, Vec<i64>, TermId)> = None;
        for &(term, positive) in &self.asserted {
            if !positive {
                continue;
            }
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                continue;
            };
            if name.as_str() != "=" || args.len() != 2 {
                continue;
            }
            // One side a registered monomial aux, the other a nonzero int const.
            let (aux, k) = if self.aux_to_monomial.contains_key(&args[0]) {
                let Some(k) = self.terms.extract_integer_constant(args[1]) else {
                    continue;
                };
                (args[0], k)
            } else if self.aux_to_monomial.contains_key(&args[1]) {
                let Some(k) = self.terms.extract_integer_constant(args[0]) else {
                    continue;
                };
                (args[1], k)
            } else {
                continue;
            };
            if k.is_zero() {
                continue;
            }
            let Some(k_i64) = k.to_i64() else {
                continue;
            };
            let Some(vars) = self.aux_to_monomial.get(&aux) else {
                continue;
            };
            // The divisor argument requires every factor to be integer-sorted.
            if !vars
                .iter()
                .all(|&v| matches!(self.terms.sort(v), Sort::Int))
            {
                continue;
            }
            let Some(&factor) = vars.first() else {
                continue;
            };
            let Some(divisors) = signed_divisors_i64(k_i64, MAX_DIVISOR_SPLIT_BRANCHES / 2) else {
                continue;
            };
            // Prefer the smallest cover (fewest inner LIA re-checks).
            match &best {
                Some((_, prev, _)) if prev.len() <= divisors.len() => {}
                _ => best = Some((factor, divisors, term)),
            }
        }
        best
    }

    /// Sorted `(aux_var, factor vars)` snapshot of the registered monomials,
    /// taken once per split (#nia-factor-split-skeleton) — previously
    /// `monomials_sorted()` plus a `vars.clone()` per monomial ran at the
    /// start of EVERY branch (`insertion_sort_shift_left<&Monomial>` and
    /// `Vec<&Monomial>` frames in the 2026-09-09 gate sample).
    fn monomial_snapshot(&self) -> Vec<(TermId, Vec<TermId>)> {
        self.monomials_sorted()
            .iter()
            .map(|m| (m.aux_var, m.vars.clone()))
            .collect()
    }

    /// Run one branch of the factor split: pin `vars` to `values` in a fresh
    /// LIA scope, assert the exact product equalities the pins imply, and
    /// classify the branch. The scope is ALWAYS popped before returning.
    ///
    /// After the initial pins, the branch runs a small CONTRACTION FIXPOINT
    /// (interval-propagation style): a pinned flag frequently forces further
    /// variables to single values through the linearized products (e.g.
    /// `b=0 ⇒ aux(b,a2)=0 ⇒ a2=0` via an asserted `aux - a2 = 0`), which in
    /// turn linearizes MORE products (`aux(a2,a3)=0`). Fixed values grow from
    /// two exact sources per round:
    ///
    /// 1. the LRA bound store (`lo == hi` — exact here: the branch contains
    ///    only asserted constraints, exact persistent lemmas, and this
    ///    split's exact cuts; all tangent-plane scopes were popped by the
    ///    caller), and
    /// 2. asserted atoms LINEARIZED under the current fixed set
    ///    (#nia-factor-split-contraction): substituting the pins into an
    ///    asserted equality often leaves a single unknown (`b=0` turns
    ///    `b*a2 - a2 = 0` into `-a2 = 0`, pinning `a2`), and a ground-false
    ///    residual refutes the branch outright.
    ///
    /// The same linearized-atom pass derives single-variable ORDERINGS
    /// (`x <= y`) that justify branch-scoped product monotonicity cuts
    /// (#nia-factor-split-monotone): monomial pairs `P*x` / `P*y` with every
    /// shared factor non-negative are ordered `P*x <= P*y`. All derived facts
    /// are exact consequences of {pins ∪ asserted atoms}, so branch UNSAT
    /// stays sound; rounds run until no new cut/fact or the budget is
    /// exhausted.
    ///
    /// `monomials` (sorted `(aux, vars)` snapshot) and `skeletons` (the
    /// asserted atoms' precompiled linear forms) are computed ONCE per split
    /// by the caller (#nia-factor-split-skeleton); neither `self.monomials`
    /// nor `self.asserted` changes inside a branch.
    fn check_factor_split_branch(
        &mut self,
        chosen: &[(TermId, i64, i64)],
        values: &[i64],
        repair_in_branch: bool,
        monomials: &[(TermId, Vec<TermId>)],
        skeletons: &[AtomSkeleton],
    ) -> BranchOutcome {
        /// Contraction rounds per branch (each round is one LIA re-check).
        const MAX_BRANCH_ROUNDS: usize = 4;

        self.lia.push_tentative();

        // Pin each chosen factor: v <= x AND x <= v as exact bound cuts.
        for (&(var, _, _), &value) in chosen.iter().zip(values) {
            let lra_var = self.lia.lra_solver_mut().ensure_var_registered(var);
            for is_lower in [true, false] {
                self.lia.lra_solver_mut().add_cut_rat(
                    vec![(lra_var, Rational::one())],
                    Rational::from(value),
                    is_lower,
                    SENTINEL_REASONS,
                    var,
                );
            }
        }

        if self.debug {
            for &(var, _, _) in chosen {
                safe_eprintln!(
                    "[NIA] Factor split pin {:?}: post-pin bounds={:?}",
                    var,
                    self.lia
                        .lra_solver()
                        .get_bounds_ref(var)
                        .map(|(l, u)| (l.map(|b| &b.value), u.map(|b| &b.value)))
                );
            }
        }

        // Known-fixed values, seeded with the pins and grown by contraction.
        // Every value is an integer; `Rational` keeps them inline (i64) and
        // its int fast arms never run a bignum gcd (#nia-factor-split-rational).
        let mut fixed: HashMap<TermId, Rational> = chosen
            .iter()
            .map(|&(v, _, _)| v)
            .zip(values.iter().map(|&v| Rational::from(v)))
            .collect();
        // Monomials whose exact linearization was already asserted, so each
        // (aux, shape) cut is emitted at most once per branch.
        let mut linearized: HashSet<TermId> = HashSet::default();
        // Vars whose explicit pin cut was already asserted (the chosen pins
        // were asserted above; contraction-derived pins are asserted as they
        // are discovered so the branch tableau sees them).
        let mut pin_cut_emitted: HashSet<TermId> = chosen.iter().map(|&(v, _, _)| v).collect();
        // Monotonicity cuts already asserted, keyed (lo_aux, hi_aux).
        let mut monotone_emitted: HashSet<(TermId, TermId)> = HashSet::default();
        // What the contraction derived and what each derived fact rests on
        // (#nia-factor-split-provenance): the derived pins, the single-variable
        // orderings `x <= y` entailed by {pins ∪ asserted atoms}, and the
        // union of the premises of every sentinel-reason cut the branch
        // installed. An LRA conflict that used such a cut does not cite it,
        // so the branch explanation names those premises itself
        // (#nia-factor-split-premises) — exactly those, not every asserted
        // literal. Exact in round 0 only: from round 1 on `fixed` also holds
        // values the branch TABLEAU pinned, which no premise set records, and
        // every explanation from then on is `None` (the full set).
        let mut premises = BranchPremises::default();
        // Scratch linear form reused across atoms and passes.
        let mut scratch = LinearScratch::default();
        // Nested LIA scopes opened on top of the branch scope (the derived-cut
        // layer of round 0, see below); popped with it.
        let mut nested_scopes = 0usize;

        let mut outcome = BranchOutcome::Open;
        for round in 0..MAX_BRANCH_ROUNDS {
            // Linearized-atom contraction (#nia-factor-split-contraction):
            // substitute the fixed set into every asserted atom; a ground-false
            // residual refutes the branch, a single-unknown equality pins that
            // unknown, and a two-variable difference comparison records an
            // ordering for the monotonicity cuts below. Iterate to a small
            // fixpoint — each new pin can linearize further atoms.
            let mut derived_pins = false;
            for _pass in 0..8 {
                match self.derive_branch_facts(skeletons, &mut fixed, &mut premises, &mut scratch) {
                    BranchFactStep::Refuted(from) => {
                        if self.debug {
                            safe_eprintln!(
                                "[NIA] Factor split branch {values:?} round {round}: \
                                 refuted by linearized asserted atom"
                            );
                        }
                        for _ in 0..=nested_scopes {
                            self.lia.pop_tentative();
                        }
                        // In round 0 the fixed set is the chosen pins plus what
                        // the asserted atoms derive from them, so the refuting
                        // atom and the premises of the values substituted into
                        // it explain the refutation (the pins are the cover's).
                        // From round 1 on it also holds values the branch
                        // TABLEAU pinned, which only the full set covers.
                        return BranchOutcome::Refuted {
                            literals: if round == 0 {
                                self.asserted_lits_at(&from.0)
                            } else {
                                None
                            },
                            lra: false,
                        };
                    }
                    BranchFactStep::Grew => {
                        derived_pins = true;
                    }
                    BranchFactStep::Fixpoint => break,
                }
            }

            // Round 0 installs its cuts in two layers when the contraction
            // derived anything (#nia-factor-split-provenance): first the cuts
            // that rest on the case pins alone (the pins and the
            // linearizations over case-pinned factors), checked on their own
            // — a refutation there needs no derived fact, so its explanation
            // is the LRA conflict alone, exactly as strong as the conflict
            // itself; only if that layer is feasible do the derived pins,
            // the linearizations over derived values and the monotonicity
            // cuts go in (in a nested scope), whose refutation names their
            // premises. Which sentinel cut an LRA conflict used is not
            // reported, so without the first layer every branch that derived
            // anything paid for all of it.
            let mut premise_free_layer =
                round == 0 && (!premises.pins.is_empty() || !premises.orderings.is_empty());
            let mut added = false;
            let mut layer_refuted: Option<Vec<TheoryLit>> = None;
            loop {
                // Assert explicit pin cuts for contraction-derived fixed values so
                // the branch tableau enforces them (they are exact consequences of
                // the pins + asserted atoms). Every one rests on a derived fact.
                let mut new_pins: Vec<(TermId, Rational)> = if premise_free_layer {
                    Vec::new()
                } else {
                    fixed
                        .iter()
                        .filter(|(v, _)| !pin_cut_emitted.contains(*v))
                        .map(|(&v, val)| (v, val.clone()))
                        .collect()
                };
                new_pins.sort_unstable_by_key(|(v, _)| v.0);
                for (v, val) in new_pins {
                    let from = premises.of_value(v).clone();
                    premises.cuts.union(&from);
                    let lra_var = self.lia.lra_solver_mut().ensure_var_registered(v);
                    for is_lower in [true, false] {
                        self.lia.lra_solver_mut().add_cut_rat(
                            vec![(lra_var, Rational::one())],
                            val.clone(),
                            is_lower,
                            SENTINEL_REASONS,
                            v,
                        );
                    }
                    pin_cut_emitted.insert(v);
                    added = true;
                }

                // Assert the exact product equalities the fixed set implies:
                //   all factors fixed             -> aux = prod(values)
                //   exactly one factor unfixed y  -> aux - c*y = 0 (c = prod fixed)
                //   any fixed factor zero         -> aux = 0
                //   residual multiset registered  -> aux - c*aux_residual = 0
                // Multiplicity matters (x*x with x fixed) — walk mon.vars.
                for (aux, vars) in monomials {
                    if linearized.contains(aux) {
                        continue;
                    }
                    let mut fixed_product = Rational::one();
                    let mut unfixed: Vec<TermId> = Vec::new();
                    // The cut rests on the premises of the fixed factors it
                    // substitutes; a zero factor alone forces `aux = 0`, so then
                    // the cheapest zero factor's premises suffice.
                    let mut cut_from = Premises::default();
                    let mut zero_from: Option<&Premises> = None;
                    for v in vars {
                        match fixed.get(v) {
                            Some(val) => {
                                fixed_product *= val;
                                let from = premises.of_value(*v);
                                cut_from.union(from);
                                if val.is_zero()
                                    && zero_from.is_none_or(|z| from.0.len() < z.0.len())
                                {
                                    zero_from = Some(from);
                                }
                            }
                            None => unfixed.push(*v),
                        }
                    }
                    if unfixed.len() == vars.len() {
                        // Nothing fixed: no exact consequence available.
                        continue;
                    }
                    if let Some(z) = zero_from {
                        cut_from = z.clone();
                    }
                    if premise_free_layer && !cut_from.0.is_empty() {
                        // Rests on a derived value: the second layer's.
                        continue;
                    }
                    let (coeffs, bound): (Vec<(u32, Rational)>, Rational) = if fixed_product
                        .is_zero()
                    {
                        // A fixed factor is zero: aux = 0 exactly, regardless of
                        // how many factors remain unfixed.
                        let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
                        (vec![(aux_var, Rational::one())], Rational::zero())
                    } else if unfixed.is_empty() {
                        // aux = fixed_product
                        let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
                        (vec![(aux_var, Rational::one())], fixed_product)
                    } else if unfixed.len() == 1 {
                        // aux - c*y = 0
                        let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
                        let y_var = self.lia.lra_solver_mut().ensure_var_registered(unfixed[0]);
                        (
                            vec![(aux_var, Rational::one()), (y_var, -&fixed_product)],
                            Rational::zero(),
                        )
                    } else {
                        // >= 2 unfixed factors with a non-zero fixed product: exact
                        // only when the residual multiset is itself a registered
                        // monomial (aux_res == product(unfixed)) — then
                        // aux = fixed_product * aux_res (#nia-factor-split-residual).
                        let mut key = unfixed.clone();
                        key.sort_unstable_by_key(|t| t.0);
                        let Some(residual_aux) = self.monomials.get(&key).map(|m| m.aux_var) else {
                            continue;
                        };
                        if residual_aux == *aux {
                            continue;
                        }
                        let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
                        let res_var = self
                            .lia
                            .lra_solver_mut()
                            .ensure_var_registered(residual_aux);
                        (
                            vec![(aux_var, Rational::one()), (res_var, -&fixed_product)],
                            Rational::zero(),
                        )
                    };
                    for is_lower in [true, false] {
                        self.lia.lra_solver_mut().add_cut_rat(
                            coeffs.clone(),
                            bound.clone(),
                            is_lower,
                            SENTINEL_REASONS,
                            *aux,
                        );
                    }
                    premises.cuts.union(&cut_from);
                    linearized.insert(*aux);
                    added = true;
                }

                // Product monotonicity cuts (#nia-factor-split-monotone): for
                // monomial pairs `P*x` / `P*y` with x <= y entailed and every
                // shared factor non-negative, order the aux vars.
                if !premise_free_layer
                    && self.emit_branch_monotonicity_cuts(
                        monomials,
                        &fixed,
                        &mut premises,
                        &mut monotone_emitted,
                    ) > 0
                {
                    added = true;
                }
                if !premise_free_layer {
                    break;
                }
                // The premise-free layer on its own.
                match self.lia.lra_solver_mut().check() {
                    TheoryResult::Unsat(lits) => {
                        layer_refuted = Some(lits);
                        break;
                    }
                    TheoryResult::UnsatWithFarkas(conflict) => {
                        layer_refuted = Some(conflict.literals);
                        break;
                    }
                    _ => {}
                }
                self.lia.push_tentative();
                nested_scopes += 1;
                premise_free_layer = false;
            }
            if let Some(lits) = layer_refuted {
                if self.debug {
                    safe_eprintln!(
                        "[NIA] Factor split branch {values:?} round 0: refuted before \
                         the derived cuts ({} lits)",
                        lits.len()
                    );
                }
                outcome = BranchOutcome::Refuted {
                    literals: Some(lits),
                    lra: true,
                };
                break;
            }

            if round > 0 && !added && !derived_pins {
                break;
            }

            // Check the branch with the LRA SIMPLEX directly (not
            // `self.lia.check()`): LIA's front-end deciders (finite-domain
            // witness search, IntSat probe, Dioph) reconstruct the problem
            // from the ASSERTED-ATOM view and never see scope-local tableau
            // cuts, so they can report Sat right past the pins. The simplex
            // works on the real tableau, which contains the pins and the
            // product linearizations. An LRA conflict here is sound for the
            // integer branch a fortiori (rational infeasibility over exact
            // constraints implies integer infeasibility).
            let result = self.lia.lra_solver_mut().check();
            if self.debug {
                safe_eprintln!(
                    "[NIA] Factor split branch {:?} round {}: LRA {:?} (lra rows={})",
                    values,
                    round,
                    result,
                    self.lia.lra_solver().row_count()
                );
            }
            // The LRA conflict names the reasons of the bounds it used; a
            // sentinel cut it used is named by nothing, so the branch
            // explanation adds the premises of every cut the round-0 branch
            // installed (#nia-factor-split-premises,
            // #nia-factor-split-provenance). Which cuts the conflict used is
            // not known, so it names them all — but each by the asserted
            // atoms it was derived from, never by every asserted literal.
            let explain = |this: &Self, mut lits: Vec<TheoryLit>| -> Option<Vec<TheoryLit>> {
                if round != 0 {
                    return None;
                }
                lits.extend(this.asserted_lits_at(&premises.cuts.0)?);
                Some(lits)
            };
            match result {
                TheoryResult::Unsat(lits) => {
                    outcome = BranchOutcome::Refuted {
                        literals: explain(self, lits),
                        lra: true,
                    };
                    break;
                }
                TheoryResult::UnsatWithFarkas(conflict) => {
                    outcome = BranchOutcome::Refuted {
                        literals: explain(self, conflict.literals),
                        lra: true,
                    };
                    break;
                }
                _ => {
                    // Not refuted. The branch model (pins + LIA completion)
                    // may be a genuine witness: verify it by exact
                    // substitution into every asserted atom. Fail-closed —
                    // anything unverifiable leaves the branch merely "open".
                    if let Some(TheoryResult::Sat) = self.try_model_point_sat() {
                        outcome = BranchOutcome::VerifiedSat;
                        break;
                    }
                    // The branch model is often ALMOST right (the pins fix the
                    // hard combinatorial part; a few products are off by a
                    // little). Try the SAT-only anchored repair around it —
                    // any hit is a fully verified witness (#nia-repair-search).
                    if repair_in_branch {
                        if let Some(TheoryResult::Sat) = self.try_model_repair_search() {
                            outcome = BranchOutcome::VerifiedSat;
                            break;
                        }
                    }
                    // Integer disequality entailment probes
                    // (#nia-factor-split-diseq): the raw LRA simplex cannot
                    // see asserted disequalities, so a branch whose rows FORCE
                    // `e = 0` against an asserted `e != 0` looks feasible.
                    // Probe both integer sides (`e >= 1`, `e <= -1`) in
                    // throwaway scopes; if both are LRA-infeasible, every
                    // integer point of the branch has e = 0 — refuted.
                    if self.branch_diseq_probes_refute(skeletons, &fixed, &mut scratch) {
                        if self.debug {
                            safe_eprintln!(
                                "[NIA] Factor split branch {values:?} round {round}: \
                                 refuted by disequality entailment probe"
                            );
                        }
                        outcome = BranchOutcome::Refuted {
                            literals: None,
                            lra: true,
                        };
                        break;
                    }
                    // Contraction: absorb every factor variable the branch
                    // tableau now pins to a single integer value. JUSTIFIED
                    // bounds only (#nia-sign-cut-soundness): a pin absorbed
                    // here becomes a fact of the branch refutation, whose
                    // explanation is the full set; a model-derived bound is
                    // no fact. The branch's own case pins are sentinel-only,
                    // which the accessor accepts.
                    let mut grew = false;
                    for (_, vars) in monomials {
                        for v in vars {
                            if fixed.contains_key(v) {
                                continue;
                            }
                            let Some((Some(lb), Some(ub))) = self.lia.justified_bounds_ref(*v)
                            else {
                                continue;
                            };
                            // `lo == hi`, both non-strict, integral — compared
                            // on the inline `Rational`s (no BigRational built).
                            if !lb.strict
                                && !ub.strict
                                && lb.value == ub.value
                                && lb.value.is_integer()
                            {
                                fixed.insert(*v, lb.value.clone());
                                grew = true;
                            }
                        }
                    }
                    if !grew {
                        break;
                    }
                }
            }
        }
        for _ in 0..=nested_scopes {
            self.lia.pop_tentative();
        }
        outcome
    }

    /// Precompile every asserted comparison atom into its linear skeleton
    /// (#nia-factor-split-skeleton). One term walk per atom per SPLIT, instead
    /// of one per atom per pass (<= 8) per round (<= 4) per branch (<= 64).
    /// Atoms that are not binary comparisons get no skeleton (they were
    /// skipped by the walk as well).
    fn build_atom_skeletons(&self) -> Vec<AtomSkeleton> {
        let mut out = Vec::with_capacity(self.asserted.len());
        for (index, &(term, positive)) in self.asserted.iter().enumerate() {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let op = match name.as_str() {
                "=" => AtomOp::Eq,
                "<=" => AtomOp::Le,
                "<" => AtomOp::Lt,
                ">=" => AtomOp::Ge,
                ">" => AtomOp::Gt,
                "distinct" => AtomOp::Distinct,
                _ => continue,
            };
            let mut sk = AtomSkeleton {
                term,
                positive,
                index,
                op,
                nodes: Vec::new(),
                factors: Vec::new(),
            };
            // form = lhs - rhs.
            self.skeleton_push(args[0], 1, &mut sk);
            self.skeleton_push(args[1], -1, &mut sk);
            out.push(sk);
        }
        out
    }

    /// Emit the pre-order skeleton nodes of `sign * term` (see [`SkNode`]).
    /// Mirrors the historical recursive walk with the `fixed` lookups
    /// deferred to substitution time: integer constants are folded, `+`/`-`
    /// recurse (behind a `Check` node), products record their constant
    /// factor and opaque non-constant factor list, everything else is
    /// `Opaque`.
    fn skeleton_push(&self, term: TermId, sign: i8, sk: &mut AtomSkeleton) {
        if let Some(c) = self.terms.extract_integer_constant(term) {
            sk.nodes.push(SkNode::Const {
                sign,
                value: Rational::from(c),
            });
            return;
        }
        match self.terms.get(term) {
            TermData::Var(_, _) => sk.nodes.push(SkNode::Var {
                term,
                sign,
                int_sorted: matches!(self.terms.sort(term), Sort::Int),
            }),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let at = sk.nodes.len();
                    sk.nodes.push(SkNode::Check {
                        term,
                        sign,
                        skip: 0,
                    });
                    for &a in args {
                        self.skeleton_push(a, sign, sk);
                    }
                    Self::skeleton_close(sk, at);
                }
                "-" if args.len() == 1 => {
                    let at = sk.nodes.len();
                    sk.nodes.push(SkNode::Check {
                        term,
                        sign,
                        skip: 0,
                    });
                    self.skeleton_push(args[0], -sign, sk);
                    Self::skeleton_close(sk, at);
                }
                "-" if !args.is_empty() => {
                    let at = sk.nodes.len();
                    sk.nodes.push(SkNode::Check {
                        term,
                        sign,
                        skip: 0,
                    });
                    self.skeleton_push(args[0], sign, sk);
                    for &a in &args[1..] {
                        self.skeleton_push(a, -sign, sk);
                    }
                    Self::skeleton_close(sk, at);
                }
                "*" => {
                    // Constant factors fold into `c`; every other factor is
                    // recorded opaquely (looked up in `fixed`, never recursed —
                    // exactly as before).
                    let mut c = Rational::one();
                    let start = sk.factors.len();
                    for &a in args {
                        if let Some(k) = self.terms.extract_integer_constant(a) {
                            c *= &Rational::from(k);
                        } else {
                            sk.factors.push(a);
                        }
                    }
                    let end = sk.factors.len();
                    sk.nodes.push(SkNode::Prod {
                        term,
                        sign,
                        c,
                        factors: (start as u32, end as u32),
                    });
                }
                _ => sk.nodes.push(SkNode::Opaque { term, sign }),
            },
            _ => sk.nodes.push(SkNode::Opaque { term, sign }),
        }
    }

    /// Record the subtree length of the `Check` node at `at`.
    fn skeleton_close(sk: &mut AtomSkeleton, at: usize) {
        let skip = (sk.nodes.len() - at - 1) as u32;
        if let SkNode::Check { skip: s, .. } = &mut sk.nodes[at] {
            *s = skip;
        }
    }

    /// Substitute `fixed` into a skeleton, producing `coeffs`/`konst` for
    /// `form = Σ coeffs·v + konst` (both cleared first). Returns `false` when
    /// the atom does not linearize exactly under `fixed` — the same cases, in
    /// the same order, as the historical walk: an unfixed non-Int variable,
    /// an unfixed opaque term, or a product with >= 2 unfixed factors whose
    /// residual multiset is not a registered monomial.
    fn skeleton_linearize(
        &self,
        sk: &AtomSkeleton,
        fixed: &HashMap<TermId, Rational>,
        scratch: &mut LinearScratch,
    ) -> bool {
        scratch.coeffs.clear();
        scratch.konst = Rational::zero();
        scratch.used.clear();
        let nodes = &sk.nodes;
        let mut i = 0usize;
        while i < nodes.len() {
            match &nodes[i] {
                SkNode::Const { sign, value } => add_signed(&mut scratch.konst, *sign, value),
                SkNode::Check { term, sign, skip } => {
                    if let Some(val) = fixed.get(term) {
                        add_signed(&mut scratch.konst, *sign, val);
                        scratch.used.push(*term);
                        i += *skip as usize;
                    }
                }
                SkNode::Var {
                    term,
                    sign,
                    int_sorted,
                } => {
                    if let Some(val) = fixed.get(term) {
                        add_signed(&mut scratch.konst, *sign, val);
                        scratch.used.push(*term);
                    } else if !*int_sorted {
                        // Int-sorted variables only: the derived pins and the
                        // ±1 disequality probes rely on integrality.
                        return false;
                    } else {
                        add_signed(
                            scratch.coeffs.entry(*term).or_default(),
                            *sign,
                            &Rational::one(),
                        );
                    }
                }
                SkNode::Prod {
                    term,
                    sign,
                    c,
                    factors,
                } => {
                    if let Some(val) = fixed.get(term) {
                        add_signed(&mut scratch.konst, *sign, val);
                        scratch.used.push(*term);
                    } else {
                        // Reduce the factor list via `fixed` (multiplicity
                        // preserved).
                        let mut cc = c.clone();
                        scratch.unfixed.clear();
                        for f in &sk.factors[factors.0 as usize..factors.1 as usize] {
                            match fixed.get(f) {
                                Some(val) => {
                                    cc *= val;
                                    scratch.used.push(*f);
                                }
                                None => scratch.unfixed.push(*f),
                            }
                        }
                        if cc.is_zero() || scratch.unfixed.is_empty() {
                            add_signed(&mut scratch.konst, *sign, &cc);
                        } else if scratch.unfixed.len() == 1 {
                            add_signed(
                                scratch.coeffs.entry(scratch.unfixed[0]).or_default(),
                                *sign,
                                &cc,
                            );
                        } else {
                            // >= 2 unfixed factors: exact only as a registered
                            // monomial aux (product(vars) == aux by invariant).
                            scratch.unfixed.sort_unstable_by_key(|t| t.0);
                            let Some(mon) = self.monomials.get(&scratch.unfixed) else {
                                return false;
                            };
                            add_signed(scratch.coeffs.entry(mon.aux_var).or_default(), *sign, &cc);
                        }
                    }
                }
                SkNode::Opaque { term, sign } => {
                    if let Some(val) = fixed.get(term) {
                        add_signed(&mut scratch.konst, *sign, val);
                        scratch.used.push(*term);
                    } else {
                        return false;
                    }
                }
            }
            i += 1;
        }
        scratch.coeffs.retain(|_, c| !c.is_zero());
        true
    }

    /// One pass of linearized-atom fact derivation
    /// (#nia-factor-split-contraction). Substitutes `fixed` into every
    /// asserted atom (products reduce exactly: all-fixed → constant, a zero
    /// fixed factor → 0, one unfixed factor → scaled variable, registered
    /// residual multiset → scaled residual aux). From each atom whose residual
    /// is fully linear it derives, in order of strength:
    ///
    /// * a GROUND-FALSE residual  → the branch is refuted (exact integer
    ///   arithmetic over entailed values — no relaxation involved);
    /// * a single-unknown equality `c*v + k = 0` → pins `v = -k/c`
    ///   (non-integral or conflicting forced value refutes the branch: `v`
    ///   is an integer);
    /// * a two-variable difference comparison `c*(x - y) <= k` with
    ///   `k/c <= 0` (after sign normalization) → records the ordering
    ///   `x <= y`; equalities with zero constant record both directions.
    ///
    /// Every derived fact is an exact consequence of {branch pins ∪ asserted
    /// atoms}, so `Refuted` is sound for the branch and pins/orderings can
    /// justify further exact cuts. Atoms that do not fully linearize are
    /// skipped (fail-open: derivation is a completeness device only).
    ///
    /// PROVENANCE (#nia-factor-split-provenance). Each fact carries the
    /// asserted literals it was derived from: the atom itself plus the
    /// premises of every `fixed` value its substitution read (a case pin of
    /// the branch reads as no premise — it is the branch's hypothesis, which
    /// the split's cover names). A derived pin goes into `premises.pins`, an
    /// ordering into `premises.orderings`, and a refutation returns its own
    /// set, so the branch explanation can name exactly what the refutation
    /// rests on instead of every asserted literal.
    fn derive_branch_facts(
        &self,
        skeletons: &[AtomSkeleton],
        fixed: &mut HashMap<TermId, Rational>,
        premises: &mut BranchPremises,
        scratch: &mut LinearScratch,
    ) -> BranchFactStep {
        use std::cmp::Ordering as CmpOrdering;

        let mut grew = false;
        for sk in skeletons {
            // Normalize (op, positive) to an operator on `form OP 0` where
            // form = lhs - rhs = Σ coeffs + konst.
            let rel = match (sk.op, sk.positive) {
                (AtomOp::Eq, true) => Rel::Eq,
                (AtomOp::Eq, false) => Rel::Neq,
                (AtomOp::Le, true) => Rel::Le,
                (AtomOp::Le, false) => Rel::Gt,
                (AtomOp::Lt, true) => Rel::Lt,
                (AtomOp::Lt, false) => Rel::Ge,
                (AtomOp::Ge, true) => Rel::Ge,
                (AtomOp::Ge, false) => Rel::Lt,
                (AtomOp::Gt, true) => Rel::Gt,
                (AtomOp::Gt, false) => Rel::Le,
                (AtomOp::Distinct, _) => continue,
            };
            if !self.skeleton_linearize(sk, fixed, scratch) {
                continue;
            }
            let coeffs = &scratch.coeffs;
            let konst = &scratch.konst;
            // A fact derived from this atom rests on the atom and on the
            // premises of the values substituted into it
            // (`BranchPremises::derivation`).

            match coeffs.len() {
                0 => {
                    // Ground residual: evaluate exactly.
                    let cmp = konst.cmp(&Rational::zero());
                    let holds = match rel {
                        Rel::Eq => cmp == CmpOrdering::Equal,
                        Rel::Neq => cmp != CmpOrdering::Equal,
                        Rel::Le => cmp != CmpOrdering::Greater,
                        Rel::Lt => cmp == CmpOrdering::Less,
                        Rel::Ge => cmp != CmpOrdering::Less,
                        Rel::Gt => cmp == CmpOrdering::Greater,
                    };
                    if !holds {
                        return BranchFactStep::Refuted(
                            premises.derivation(sk.index, &scratch.used),
                        );
                    }
                }
                1 => {
                    if rel != Rel::Eq {
                        continue;
                    }
                    let (&v, c) = coeffs.iter().next().expect("len checked");
                    // c*v + konst = 0  =>  v = -konst/c
                    let value = -(konst / c);
                    if !value.is_integer() {
                        // An integer variable forced to a fractional value:
                        // the branch is infeasible.
                        return BranchFactStep::Refuted(
                            premises.derivation(sk.index, &scratch.used),
                        );
                    }
                    match fixed.get(&v) {
                        Some(existing) if *existing != value => {
                            // Two derivations disagree: both rest here.
                            let mut both = premises.derivation(sk.index, &scratch.used);
                            both.union(premises.of_value(v));
                            return BranchFactStep::Refuted(both);
                        }
                        Some(_) => {}
                        None => {
                            let from = premises.derivation(sk.index, &scratch.used);
                            fixed.insert(v, value);
                            premises.pins.insert(v, from);
                            grew = true;
                        }
                    }
                }
                2 => {
                    // Difference comparison c*(x - y) REL -konst?
                    let mut it = coeffs.iter();
                    let (&v1, c1) = it.next().expect("len checked");
                    let (&v2, c2) = it.next().expect("len checked");
                    if *c1 != -c2 {
                        continue;
                    }
                    // Normalize to positive coefficient on (x - y).
                    let (x, y, c) = if c1.is_positive() {
                        (v1, v2, c1)
                    } else {
                        (v2, v1, c2)
                    };
                    // c*(x - y) + konst REL 0  =>  x - y REL' -konst/c  (c > 0)
                    let bound = -(konst / c);
                    let zero = Rational::zero();
                    // The orderings this atom entails (each direction once).
                    let entailed: &[(TermId, TermId)] = match rel {
                        Rel::Eq if bound == zero => &[(x, y), (y, x)],
                        // x - y <= bound <= 0  =>  x <= y.
                        Rel::Le | Rel::Lt if bound <= zero => &[(x, y)],
                        // x - y >= bound >= 0  =>  y <= x.
                        Rel::Ge | Rel::Gt if bound >= zero => &[(y, x)],
                        _ => &[],
                    };
                    for &pair in entailed {
                        if !premises.orderings.contains_key(&pair) {
                            let from = premises.derivation(sk.index, &scratch.used);
                            premises.orderings.insert(pair, from);
                            grew = true;
                        }
                    }
                }
                _ => {}
            }
        }
        if grew {
            BranchFactStep::Grew
        } else {
            BranchFactStep::Fixpoint
        }
    }

    /// Emit branch-scoped product monotonicity cuts
    /// (#nia-factor-split-monotone): for registered monomial pairs whose
    /// factor multisets differ in exactly ONE occurrence (`P*x` vs `P*y`),
    /// with `x <= y` in `premises.orderings` and every shared factor
    /// non-negative (fixed at a non-negative value, or the subject of an
    /// asserted Positive/NonNegative/Zero sign atom), assert
    /// `aux(P*x) <= aux(P*y)`. Sound: `P >= 0 ∧ x <= y ⇒ P*x <= P*y`, and
    /// every premise is entailed by {branch pins ∪ asserted atoms}: the cut
    /// rests on the ordering's premises and each shared factor's, which go
    /// into `premises.cuts` (#nia-factor-split-provenance). Returns the
    /// number of cuts added (deduped per branch via `emitted`).
    fn emit_branch_monotonicity_cuts(
        &mut self,
        monomials: &[(TermId, Vec<TermId>)],
        fixed: &HashMap<TermId, Rational>,
        premises: &mut BranchPremises,
        emitted: &mut HashSet<(TermId, TermId)>,
    ) -> usize {
        if premises.orderings.is_empty() {
            return 0;
        }
        let nonneg_atoms = self.asserted_nonneg_atoms();
        let mut added = 0;
        for (i, (aux1, vars1)) in monomials.iter().enumerate() {
            for (aux2, vars2) in &monomials[i + 1..] {
                if vars1.len() != vars2.len() {
                    continue;
                }
                // Multiset difference of two sorted vectors.
                let (mut only1, mut only2): (Vec<TermId>, Vec<TermId>) = (Vec::new(), Vec::new());
                let mut shared: Vec<TermId> = Vec::new();
                let (mut a, mut b) = (0usize, 0usize);
                while a < vars1.len() && b < vars2.len() {
                    match vars1[a].0.cmp(&vars2[b].0) {
                        std::cmp::Ordering::Equal => {
                            shared.push(vars1[a]);
                            a += 1;
                            b += 1;
                        }
                        std::cmp::Ordering::Less => {
                            only1.push(vars1[a]);
                            a += 1;
                        }
                        std::cmp::Ordering::Greater => {
                            only2.push(vars2[b]);
                            b += 1;
                        }
                    }
                }
                only1.extend_from_slice(&vars1[a..]);
                only2.extend_from_slice(&vars2[b..]);
                if only1.len() != 1 || only2.len() != 1 {
                    continue;
                }
                let (x, y) = (only1[0], only2[0]);
                // Every shared factor non-negative, and what says so.
                let mut shared_from = Premises::default();
                let all_nonneg = shared.iter().all(|&s| {
                    match Self::branch_var_nonneg(s, fixed, premises, &nonneg_atoms) {
                        Some(from) => {
                            shared_from.union(&from);
                            true
                        }
                        None => false,
                    }
                });
                if !all_nonneg {
                    continue;
                }
                // Both directions may be entailed (equality-derived).
                for (lo_aux, hi_aux, lo, hi) in [(*aux1, *aux2, x, y), (*aux2, *aux1, y, x)] {
                    let Some(order_from) = premises.orderings.get(&(lo, hi)) else {
                        continue;
                    };
                    if !emitted.insert((lo_aux, hi_aux)) {
                        continue;
                    }
                    let mut cut_from = order_from.clone();
                    cut_from.union(&shared_from);
                    premises.cuts.union(&cut_from);
                    let lo_var = self.lia.lra_solver_mut().ensure_var_registered(lo_aux);
                    let hi_var = self.lia.lra_solver_mut().ensure_var_registered(hi_aux);
                    // lo_aux - hi_aux <= 0 (upper bound).
                    self.lia.lra_solver_mut().add_cut_rat(
                        vec![(lo_var, Rational::one()), (hi_var, -Rational::one())],
                        Rational::zero(),
                        false,
                        SENTINEL_REASONS,
                        lo_aux,
                    );
                    if self.debug {
                        safe_eprintln!(
                            "[NIA] Factor split monotone cut: {lo_aux:?} <= {hi_aux:?} \
                             (from {lo:?} <= {hi:?}, shared nonneg)"
                        );
                    }
                    added += 1;
                }
            }
        }
        added
    }

    /// Integer disequality entailment probes (#nia-factor-split-diseq).
    ///
    /// For each asserted disequality `e != 0` (a negated `=` atom or a binary
    /// `distinct`) whose difference linearizes exactly under `fixed`, probe
    /// the two integer sides in throwaway LIA scopes:
    ///
    ///   branch ∪ {e >= 1}  LRA-infeasible, and
    ///   branch ∪ {e <= -1} LRA-infeasible
    ///
    /// ⇒ every rational (hence every integer) point of the branch has
    /// `-1 < e < 1`; `e` is an integer-sorted term, so `e = 0` in every
    /// integer model — contradicting the asserted disequality. The branch has
    /// no integer model: refuted. Returns `true` on the first such
    /// refutation. Probes are budget-capped (each costs two LRA checks) and
    /// fail-open (an unlinearizable or undecided probe proves nothing).
    fn branch_diseq_probes_refute(
        &mut self,
        skeletons: &[AtomSkeleton],
        fixed: &HashMap<TermId, Rational>,
        scratch: &mut LinearScratch,
    ) -> bool {
        /// Max disequalities probed per branch round (2 LRA checks each).
        const MAX_DISEQ_PROBES: usize = 8;

        let mut probes = 0usize;
        for sk in skeletons {
            let is_diseq = matches!(
                (sk.op, sk.positive),
                (AtomOp::Eq, false) | (AtomOp::Distinct, true)
            );
            if !is_diseq {
                continue;
            }
            if !self.skeleton_linearize(sk, fixed, scratch) {
                continue;
            }
            if scratch.coeffs.is_empty() {
                // Ground difference: the disequality is decided exactly.
                if scratch.konst.is_zero() {
                    return true;
                }
                continue;
            }
            if probes >= MAX_DISEQ_PROBES {
                break;
            }
            probes += 1;

            let mut sorted: Vec<(TermId, Rational)> = scratch.coeffs.drain().collect();
            sorted.sort_unstable_by_key(|(t, _)| t.0);
            let mut lra_coeffs: Vec<(u32, Rational)> = Vec::with_capacity(sorted.len());
            for (t, c) in sorted {
                let v = self.lia.lra_solver_mut().ensure_var_registered(t);
                lra_coeffs.push((v, c));
            }
            let konst = std::mem::take(&mut scratch.konst);

            let mut both_refuted = true;
            for ge_side in [true, false] {
                // Σ coeffs >= 1 - konst   (ge side: e >= 1)
                // Σ coeffs <= -1 - konst  (le side: e <= -1)
                let bound = if ge_side {
                    &Rational::one() - &konst
                } else {
                    &(-Rational::one()) - &konst
                };
                self.lia.push_tentative();
                self.lia.lra_solver_mut().add_cut_rat(
                    lra_coeffs.clone(),
                    bound,
                    ge_side,
                    SENTINEL_REASONS,
                    sk.term,
                );
                let probe_result = self.lia.lra_solver_mut().check();
                self.lia.pop_tentative();
                if !matches!(
                    probe_result,
                    TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
                ) {
                    both_refuted = false;
                    break;
                }
            }
            if both_refuted {
                return true;
            }
        }
        false
    }
}

/// `acc += sign * v` for `sign ∈ {+1, -1}` (the only multipliers the walk
/// ever uses), without materialising the product.
#[inline]
fn add_signed(acc: &mut Rational, sign: i8, v: &Rational) {
    if sign > 0 {
        *acc += v;
    } else {
        *acc -= v;
    }
}

/// Sentinel-only justification for branch-scoped cuts: non-empty so
/// `add_cut_rat` does not skip the cut (#4919), filtered to `Axiom`
/// provenance by `Bound::build_provenance_from_reasons`.
const SENTINEL_REASONS: &[(TermId, bool)] = &[(TermId::SENTINEL, true)];

/// Relation of an asserted atom normalized to `form OP 0`
/// (form = lhs - rhs), after folding the literal's polarity.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rel {
    Eq,
    Neq,
    Le,
    Lt,
    Ge,
    Gt,
}

/// Comparison operator of an asserted binary atom (before polarity).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AtomOp {
    Eq,
    Le,
    Lt,
    Ge,
    Gt,
    Distinct,
}

/// One pre-order node of an [`AtomSkeleton`]. `sign` is the ±1 multiplier
/// the historical recursive walk carried as `mult`.
#[derive(Debug)]
enum SkNode {
    /// Integer constant folded at build time: `konst += sign * value`.
    /// (Constants never occur in `fixed`: its keys are variables, monomial
    /// aux vars and non-constant product factors.)
    Const { sign: i8, value: Rational },
    /// A `+`/`-` application. If `fixed` holds `term`, the whole subtree —
    /// the next `skip` nodes — is replaced by `sign * fixed[term]`, exactly
    /// as the walk's leading `fixed` lookup short-circuited the recursion.
    Check { term: TermId, sign: i8, skip: u32 },
    /// A variable: `fixed` value, else `coeffs[term] += sign` when
    /// Int-sorted, else the atom is inexact.
    Var {
        term: TermId,
        sign: i8,
        int_sorted: bool,
    },
    /// A product `sign * c * Π factors` (`c` = folded integer constants;
    /// `factors` = index range into `AtomSkeleton::factors`, in argument
    /// order, multiplicity preserved). Factors are looked up in `fixed`,
    /// never recursed — the historical behaviour.
    Prod {
        term: TermId,
        sign: i8,
        c: Rational,
        factors: (u32, u32),
    },
    /// Any other term: exact only when `fixed` holds it.
    Opaque { term: TermId, sign: i8 },
}

/// Precompiled linear skeleton of one asserted comparison atom
/// (#nia-factor-split-skeleton): the term walk of `lhs - rhs` with every
/// `fixed` lookup deferred, so per-pass substitution is a linear scan over
/// `nodes` with `Rational` (inline-i64, gcd-free) arithmetic.
struct AtomSkeleton {
    /// The asserted atom (reason term for probe cuts).
    term: TermId,
    /// The literal's polarity.
    positive: bool,
    /// The literal's position in `NiaSolver::asserted`: its name in a
    /// [`Premises`] set.
    index: usize,
    /// The comparison operator.
    op: AtomOp,
    /// Pre-order nodes (see [`SkNode`]).
    nodes: Vec<SkNode>,
    /// Non-constant product factors referenced by `SkNode::Prod`.
    factors: Vec<TermId>,
}

/// Reusable output/scratch buffers for [`NiaSolver::skeleton_linearize`].
#[derive(Default)]
struct LinearScratch {
    /// Linear coefficients over atomic terms (variables, monomial aux vars).
    coeffs: HashMap<TermId, Rational>,
    /// Constant term.
    konst: Rational,
    /// Unfixed factor list of the product being reduced.
    unfixed: Vec<TermId>,
    /// Every `fixed` key the last substitution read (#nia-factor-split-provenance):
    /// the linear form is exact only under those values, so a fact derived
    /// from it rests on their premises too.
    used: Vec<TermId>,
}

/// Outcome of one linearized-atom fact-derivation pass
/// (see [`NiaSolver::derive_branch_facts`]).
enum BranchFactStep {
    /// An asserted atom is exactly FALSE under the branch's entailed values —
    /// the branch is infeasible; the refutation rests on these premises.
    Refuted(Premises),
    /// New pins or orderings were derived; another pass may find more.
    Grew,
    /// Nothing new derivable from the current fixed set.
    Fixpoint,
}

/// Classification of one factor-split branch.
enum BranchOutcome {
    /// The branch is refuted — by the LRA (sound: relaxation UNSAT ⊆ true
    /// UNSAT), by a linearized asserted atom, or by a disequality probe.
    /// `literals` is an explanation `E` with `pins ∧ E ⇒ ⊥`, usable for a
    /// MINIMAL aggregated conflict: round-0 refutations only (contraction
    /// rounds introduce tableau-level premises no literal list captures),
    /// and it names the asserted literals whenever the branch derived a fact
    /// from them (#nia-factor-split-premises). `None` forces the full-set
    /// fallback conflict.
    ///
    /// `lra`: the branch TABLEAU refuted it (the LRA check or a disequality
    /// probe) rather than the linearized-atom contraction, which reads the
    /// asserted atoms alone. Only a tableau refutation can have used a
    /// congruence equality the NIA linked into the inner LIA (see
    /// `split_conflict`).
    Refuted {
        literals: Option<Vec<TheoryLit>>,
        lra: bool,
    },
    /// The branch produced an exactly-verified integer witness.
    VerifiedSat,
    /// Neither refuted nor verified — the whole split must return `None`.
    Open,
}

/// Differential tests for the precompiled skeleton (#nia-factor-split-skeleton):
/// the `Rational` skeleton substitution must agree, atom by atom and `fixed`
/// map by `fixed` map, with the historical `BigRational` recursive walk it
/// replaced — same exactness verdict, same coefficients, same constant.
#[cfg(test)]
mod skeleton_tests {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    impl NiaSolver<'_> {
        /// The historical walk (pre-skeleton `branch_linear_accumulate`),
        /// kept VERBATIM as the reference oracle for the tests below.
        fn legacy_linear_accumulate(
            &self,
            term: TermId,
            mult: &BigRational,
            fixed: &HashMap<TermId, BigInt>,
            coeffs: &mut HashMap<TermId, BigRational>,
            konst: &mut BigRational,
        ) -> bool {
            if let Some(val) = fixed.get(&term) {
                *konst += mult * BigRational::from_integer(val.clone());
                return true;
            }
            if let Some(c) = self.terms.extract_integer_constant(term) {
                *konst += mult * BigRational::from_integer(c);
                return true;
            }
            match self.terms.get(term) {
                TermData::Var(_, _) => {
                    if !matches!(self.terms.sort(term), Sort::Int) {
                        return false;
                    }
                    *coeffs.entry(term).or_default() += mult;
                    true
                }
                TermData::App(Symbol::Named(name), args) => match name.as_str() {
                    "+" => args
                        .iter()
                        .all(|&a| self.legacy_linear_accumulate(a, mult, fixed, coeffs, konst)),
                    "-" if args.len() == 1 => {
                        self.legacy_linear_accumulate(args[0], &-mult.clone(), fixed, coeffs, konst)
                    }
                    "-" if !args.is_empty() => {
                        if !self.legacy_linear_accumulate(args[0], mult, fixed, coeffs, konst) {
                            return false;
                        }
                        let neg = -mult.clone();
                        args[1..]
                            .iter()
                            .all(|&a| self.legacy_linear_accumulate(a, &neg, fixed, coeffs, konst))
                    }
                    "*" => {
                        let mut c = BigRational::one();
                        let mut unfixed: Vec<TermId> = Vec::new();
                        for &a in args {
                            if let Some(k) = self.terms.extract_integer_constant(a) {
                                c *= BigRational::from_integer(k);
                            } else if let Some(val) = fixed.get(&a) {
                                c *= BigRational::from_integer(val.clone());
                            } else {
                                unfixed.push(a);
                            }
                        }
                        if c.is_zero() || unfixed.is_empty() {
                            *konst += mult * c;
                            return true;
                        }
                        if unfixed.len() == 1 {
                            *coeffs.entry(unfixed[0]).or_default() += mult * c;
                            return true;
                        }
                        let mut key = unfixed;
                        key.sort_unstable_by_key(|t| t.0);
                        if let Some(mon) = self.monomials.get(&key) {
                            *coeffs.entry(mon.aux_var).or_default() += mult * c;
                            return true;
                        }
                        false
                    }
                    _ => false,
                },
                _ => false,
            }
        }

        /// Reference linearization of an asserted binary atom.
        fn legacy_linearize(
            &self,
            term: TermId,
            fixed: &HashMap<TermId, BigInt>,
        ) -> Option<(Vec<(TermId, BigRational)>, BigRational)> {
            let TermData::App(_, args) = self.terms.get(term) else {
                return None;
            };
            let (lhs, rhs) = (args[0], args[1]);
            let mut coeffs: HashMap<TermId, BigRational> = HashMap::default();
            let mut konst = BigRational::zero();
            if !self.legacy_linear_accumulate(
                lhs,
                &BigRational::one(),
                fixed,
                &mut coeffs,
                &mut konst,
            ) || !self.legacy_linear_accumulate(
                rhs,
                &-BigRational::one(),
                fixed,
                &mut coeffs,
                &mut konst,
            ) {
                return None;
            }
            coeffs.retain(|_, c| !c.is_zero());
            let mut v: Vec<(TermId, BigRational)> = coeffs.into_iter().collect();
            v.sort_unstable_by_key(|(t, _)| t.0);
            Some((v, konst))
        }
    }

    fn big(n: i64) -> BigInt {
        BigInt::from(n)
    }

    #[test]
    fn skeleton_substitution_matches_legacy_walk_on_every_atom_and_fixed_map() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let r = terms.mk_var("r", Sort::Real);
        let k = |terms: &mut TermStore, v: i64| terms.mk_int(BigInt::from(v));
        let c0 = k(&mut terms, 0);
        let c1 = k(&mut terms, 1);
        let c2 = k(&mut terms, 2);
        let c3 = k(&mut terms, 3);
        let c5 = k(&mut terms, 5);
        let cbig = terms.mk_int(BigInt::from(i64::MAX) * BigInt::from(4));
        let xy = terms.mk_mul(vec![x, y]);
        let xz = terms.mk_mul(vec![x, z]);
        let xyz = terms.mk_mul(vec![x, y, z]);
        let xx = terms.mk_mul(vec![x, x]);
        let two_x = terms.mk_mul(vec![c2, x]);
        let x_plus_1 = terms.mk_add(vec![x, c1]);
        let three_xp1 = terms.mk_mul(vec![c3, x_plus_1]);
        let neg_y = terms.mk_neg(y);
        let x_minus_y_z = terms.mk_sub(vec![x, y, z]);
        let sum = terms.mk_add(vec![x, neg_y, xyz]);
        let zero_x = terms.mk_mul(vec![c0, x]);
        let big_x = terms.mk_mul(vec![cbig, x]);
        let intdiv = terms.mk_intdiv(x, c2);
        // Raw (un-normalized) applications so the skeleton sees the exact
        // shapes the walk had to handle: a Real-sorted product factor and a
        // nested `+` that `mk_add` would otherwise flatten away.
        let xr = terms.mk_app(Symbol::named("*"), [x, r], Sort::Real);
        let r_le_x = terms.mk_app(Symbol::named("<="), [r, x], Sort::Bool);
        let xz_eq_xr = terms.mk_app(Symbol::named("="), [xz, xr], Sort::Bool);
        let nested = terms.mk_app(Symbol::named("+"), [x_plus_1, y], Sort::Int);
        let two_x_minus_y = terms.mk_sub(vec![two_x, y]);

        let atoms: Vec<(TermId, bool)> = vec![
            (terms.mk_eq(xy, c5), true),
            (terms.mk_le(two_x_minus_y, c3), true),
            (terms.mk_ge(sum, c0), false),
            (terms.mk_lt(three_xp1, y), true),
            (terms.mk_eq(neg_y, xx), true),
            (terms.mk_gt(x_minus_y_z, c1), true),
            (terms.mk_distinct(vec![x, y]), true),
            (r_le_x, true),
            (terms.mk_eq(intdiv, y), true),
            (terms.mk_eq(zero_x, c0), true),
            (terms.mk_ge(big_x, cbig), true),
            (xz_eq_xr, true),
            (terms.mk_eq(x, c2), false),
            (terms.mk_eq(nested, c5), true),
        ];

        let mut solver = NiaSolver::new(&terms);
        for &(a, v) in &atoms {
            solver.assert_literal(a, v);
        }
        let xy_aux = solver.get_monomial_aux(&[x, y]).expect("x*y registered");
        let mut xyz_key = vec![x, y, z];
        xyz_key.sort_unstable_by_key(|t| t.0);
        let xyz_aux = solver.get_monomial_aux(&xyz_key).expect("x*y*z registered");

        let skeletons = solver.build_atom_skeletons();
        // Every asserted BINARY COMPARISON gets a skeleton (`0*x = 0` folds
        // to a Boolean constant at construction and is not one).
        let comparisons = solver
            .asserted
            .iter()
            .filter(|&&(t, _)| {
                matches!(solver.terms.get(t), TermData::App(Symbol::Named(n), a)
                    if a.len() == 2 && matches!(n.as_str(), "=" | "<=" | "<" | ">=" | ">" | "distinct"))
            })
            .count();
        assert_eq!(skeletons.len(), comparisons);
        assert!(
            comparisons >= 12,
            "expected the constructed atoms to survive: {comparisons}"
        );

        let fixed_maps: Vec<Vec<(TermId, i64)>> = vec![
            vec![],
            vec![(x, 0)],
            vec![(x, 2)],
            vec![(x, 1), (y, -3)],
            vec![(xy_aux, 7)],
            vec![(x, 2), (z, 0)],
            vec![(y, 4), (z, -1)],
            vec![(x, -2), (y, 3), (z, 5)],
            vec![(xyz_aux, 30), (x_plus_1, 9)],
            vec![(intdiv, 1), (r, 2)],
            vec![(x, i64::MAX), (y, i64::MAX)],
        ];

        let mut scratch = LinearScratch::default();
        let mut compared = 0usize;
        let mut exact_seen = 0usize;
        let mut inexact_seen = 0usize;
        for fm in &fixed_maps {
            let fixed_rat: HashMap<TermId, Rational> =
                fm.iter().map(|&(t, v)| (t, Rational::from(v))).collect();
            let fixed_big: HashMap<TermId, BigInt> = fm.iter().map(|&(t, v)| (t, big(v))).collect();
            for sk in &skeletons {
                let legacy = solver.legacy_linearize(sk.term, &fixed_big);
                let ok = solver.skeleton_linearize(sk, &fixed_rat, &mut scratch);
                assert_eq!(
                    ok,
                    legacy.is_some(),
                    "exactness verdict differs for atom {:?} under fixed {fm:?}",
                    sk.term
                );
                compared += 1;
                let Some((legacy_coeffs, legacy_konst)) = legacy else {
                    inexact_seen += 1;
                    continue;
                };
                exact_seen += 1;
                let mut got: Vec<(TermId, BigRational)> = scratch
                    .coeffs
                    .iter()
                    .map(|(t, c)| (*t, c.to_big()))
                    .collect();
                got.sort_unstable_by_key(|(t, _)| t.0);
                assert_eq!(
                    got, legacy_coeffs,
                    "coefficients differ for atom {:?} under fixed {fm:?}",
                    sk.term
                );
                assert_eq!(
                    scratch.konst.to_big(),
                    legacy_konst,
                    "constant differs for atom {:?} under fixed {fm:?}",
                    sk.term
                );
                // Every value is an integer of the pins' magnitude: the
                // skeleton must have kept them inline unless they genuinely
                // exceed i64 (the `cbig` / i64::MAX cases).
                for (_, c) in &scratch.coeffs {
                    assert!(c.is_integer(), "non-integer coefficient {c:?}");
                }
                assert!(scratch.konst.is_integer());
            }
        }
        // Anti-vacuity: both outcomes must be exercised.
        assert!(compared >= 100, "compared only {compared} pairs");
        assert!(
            exact_seen > 20,
            "too few exact linearizations: {exact_seen}"
        );
        assert!(inexact_seen > 5, "too few inexact atoms: {inexact_seen}");
    }

    #[test]
    fn skeleton_check_nodes_short_circuit_fixed_composite_terms() {
        // A composite `+` term pinned in `fixed` (the shape a single-unfixed
        // product factor produces) must replace its whole subtree, exactly
        // like the legacy walk's leading `fixed` lookup.
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let c1 = terms.mk_int(BigInt::from(1));
        let c7 = terms.mk_int(BigInt::from(7));
        let x_plus_1 = terms.mk_add(vec![x, c1]);
        // Raw application: `mk_add` would flatten the nested `+` away.
        let lhs = terms.mk_app(Symbol::named("+"), [x_plus_1, y], Sort::Int);
        let atom = terms.mk_eq(lhs, c7);
        let mut solver = NiaSolver::new(&terms);
        solver.assert_literal(atom, true);
        let skeletons = solver.build_atom_skeletons();
        assert_eq!(skeletons.len(), 1);
        let mut scratch = LinearScratch::default();

        let fixed: HashMap<TermId, Rational> =
            [(x_plus_1, Rational::from(3i64))].into_iter().collect();
        assert!(solver.skeleton_linearize(&skeletons[0], &fixed, &mut scratch));
        // ±((x+1) + y - 7) with (x+1) := 3  ==>  ±(y - 4); `mk_eq` may
        // orient the sides either way, so check the shape and the sign
        // consistency, then pin against the legacy walk.
        assert_eq!(scratch.coeffs.len(), 1);
        let cy = scratch.coeffs.get(&y).expect("y survives").clone();
        assert!(cy == Rational::one() || cy == -Rational::one(), "{cy:?}");
        assert_eq!(&scratch.konst * &cy, Rational::from(-4i64));
        assert!(
            !scratch.coeffs.contains_key(&x),
            "x is inside the skipped subtree"
        );

        let fixed_big: HashMap<TermId, BigInt> =
            [(x_plus_1, BigInt::from(3))].into_iter().collect();
        let (lc, lk) = solver
            .legacy_linearize(atom, &fixed_big)
            .expect("legacy exact");
        assert_eq!(lc, vec![(y, cy.to_big())]);
        assert_eq!(lk, scratch.konst.to_big());
    }
}

/// Wall-clock and i64-rim regressions for the factor case-split
/// (#nia-enum-deadline, #nia-enum-visit-bound).
#[cfg(test)]
mod deadline_and_rim_tests {
    use super::*;
    use num_bigint::BigInt;

    /// `x, y ∈ [lo, hi] ∧ x*y <= -1`, ingested through the real
    /// `assert_literal` path, then driven through the box split.
    ///
    /// The shape is chosen so the split actually ENUMERATES: the product is
    /// opaque to the un-split tableau (so the priming `lia.check()` is
    /// feasible and cannot short-circuit the walk), while every branch pins a
    /// POSITIVE `x`, which linearizes `x*y` exactly and makes `x*y <= -1`
    /// contradict `y >= lo > 0`. So every branch of the complete cover is
    /// refuted — only after the odometer has visited all of them.
    fn split_xy_box(
        lo: i64,
        hi: i64,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<TheoryResult> {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let lo_c = terms.mk_int(BigInt::from(lo));
        let hi_c = terms.mk_int(BigInt::from(hi));
        let neg_one = terms.mk_int(BigInt::from(-1));
        let atoms = [
            terms.mk_ge(x, lo_c),
            terms.mk_le(x, hi_c),
            terms.mk_ge(y, lo_c),
            terms.mk_le(y, hi_c),
            terms.mk_le(xy, neg_one),
        ];
        let mut solver = NiaSolver::new(&terms);
        for atom in atoms {
            solver.assert_literal(atom, true);
        }
        if let Some(dl) = deadline {
            solver.set_deadline(dl);
        }
        solver.try_bounded_factor_split()
    }

    #[test]
    fn factor_split_odometer_reaches_i64_max_without_overflow() {
        // REGRESSION (2026-09-11). The branch odometer did `assignment[i] += 1`
        // BEFORE the `> hi` test, so a chosen factor whose `hi == i64::MAX`
        // computed `i64::MAX + 1` on the last step. Such a box is ADMITTED: the
        // eligibility test is the WIDTH cap (`hi - lo + 1 <=
        // MAX_FACTOR_SPLIT_WIDTH`), so `[i64::MAX - 1, i64::MAX]` (width 2)
        // passes. In ay's own builds (overflow-checks on) that panics; inside
        // `compiler_consumer`, built with overflow checks OFF, it WRAPS to `i64::MIN`, the
        // carry never clears, and the branch loop runs ~2^64 inner LIA checks.
        //
        // The two sibling bounded-enum odometers were fixed on 2026-09-10
        // (6ee065bfea); this one was missed.
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            split_xy_box(i64::MAX - 3, i64::MAX, None)
        }));
        assert!(
            outcome.is_ok(),
            "try_bounded_factor_split panicked stepping the odometer past \
             x = y = i64::MAX — NIA runs inside compiler_consumer, so a panic here is an \
             ICE, never a solver verdict"
        );
        let verdict = outcome.unwrap();
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "every branch pins a positive x, so x*y <= -1 contradicts y > 0: \
             the 16-branch cover at the i64 rim must be walked to the end and \
             refuted — got {verdict:?}"
        );

        // ANTI-VACUITY: the same shape over a small box reaches the same real
        // verdict, so a "fix" that declined every rim box would not pass here.
        let verdict = split_xy_box(1, 4, None);
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "x,y∈[1,4] ∧ x*y<=-1 must be refuted by the complete cover — \
             got {verdict:?}"
        );
    }

    #[test]
    fn factor_split_declines_instead_of_claiming_unsat_on_expired_deadline() {
        // The UNSAT claim is licensed ONLY by refuting every branch of the
        // complete cover, so an aborted enumeration must return None — never
        // fall out of the loop into the aggregated conflict.
        let expired = ay_core::time::Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("the monotonic clock is more than a second past its epoch");
        let start = ay_core::time::Instant::now();
        let verdict = split_xy_box(1, 4, Some(expired));
        let took = start.elapsed();
        assert!(
            verdict.is_none(),
            "an expired deadline must abort the split at None (inconclusive); \
             a partial cover licenses no Unsat — got {verdict:?}"
        );
        assert!(
            took < std::time::Duration::from_millis(250),
            "the split must abort at the FIRST branch poll — took {took:?}"
        );

        // ANTI-VACUITY: with budget left the identical query is still decided.
        let live = ay_core::time::Instant::now() + std::time::Duration::from_secs(3600);
        let verdict = split_xy_box(1, 4, Some(live));
        assert!(
            matches!(verdict, Some(TheoryResult::Unsat(_))),
            "with budget left the complete cover must still refute x*y<=-1 — \
             got {verdict:?}"
        );
    }

    /// `x*y = -6 ∧ x*y = -27 ∧ -1 <= x,y <= 2`: the SAME monomial aux var is
    /// pinned to two different constants, so the un-split tableau is infeasible
    /// on its own and both split entries hit the `Unsat` arm of their PRIMING
    /// `lia.check()` — before ever reaching a branch loop.
    fn split_pinned_aux(
        entry: SplitEntry,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<TheoryResult> {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_mul(vec![x, y]);
        let lo_c = terms.mk_int(BigInt::from(-1));
        let hi_c = terms.mk_int(BigInt::from(2));
        let m6 = terms.mk_int(BigInt::from(-6));
        let m27 = terms.mk_int(BigInt::from(-27));
        let atoms = [
            terms.mk_ge(x, lo_c),
            terms.mk_le(x, hi_c),
            terms.mk_ge(y, lo_c),
            terms.mk_le(y, hi_c),
            terms.mk_eq(xy, m6),
            terms.mk_eq(xy, m27),
        ];
        let mut solver = NiaSolver::new(&terms);
        for atom in atoms {
            solver.assert_literal(atom, true);
        }
        if let Some(dl) = deadline {
            solver.set_deadline(dl);
        }
        match entry {
            SplitEntry::Box => solver.try_bounded_factor_split(),
            SplitEntry::Divisor => solver.try_divisor_split(),
        }
    }

    #[derive(Clone, Copy, Debug)]
    enum SplitEntry {
        Box,
        Divisor,
    }

    #[test]
    fn split_entries_decline_before_the_priming_lia_check_on_an_expired_deadline() {
        // REGRESSION (2026-09-11, review of the deadline commit). Both split
        // entries ran their priming `lia.check()` — an UNBOUNDED inner solve
        // that RETURNS `Some(Unsat(...))` on its infeasible arm — ahead of any
        // deadline poll, so an already-exhausted budget still bought a full LIA
        // solve and still answered out of it. The verdict was never wrong (LIA
        // answers `Unknown`, never `Unsat`, on its own expiry), but an expired
        // budget must not start the work at all.
        let expired = ay_core::time::Instant::now()
            .checked_sub(std::time::Duration::from_secs(1))
            .expect("the monotonic clock is more than a second past its epoch");
        for entry in [SplitEntry::Box, SplitEntry::Divisor] {
            let verdict = split_pinned_aux(entry, Some(expired));
            assert!(
                verdict.is_none(),
                "{entry:?}: an expired deadline must decline BEFORE the priming \
                 lia.check(), so no verdict may come back — got {verdict:?}"
            );

            // ANTI-VACUITY: with budget left the same query still reaches the
            // priming check and still returns its genuine Unsat, so the poll
            // above removed nothing but the post-expiry work.
            let live = ay_core::time::Instant::now() + std::time::Duration::from_secs(3600);
            let verdict = split_pinned_aux(entry, Some(live));
            assert!(
                matches!(verdict, Some(TheoryResult::Unsat(_))),
                "{entry:?}: with budget left the priming check must still refute \
                 x*y = -6 ∧ x*y = -27 — got {verdict:?}"
            );
            // And with no deadline installed at all the behaviour is unchanged.
            let verdict = split_pinned_aux(entry, None);
            assert!(
                matches!(verdict, Some(TheoryResult::Unsat(_))),
                "{entry:?}: with no deadline the priming check must still refute — \
                 got {verdict:?}"
            );
        }
    }
}
