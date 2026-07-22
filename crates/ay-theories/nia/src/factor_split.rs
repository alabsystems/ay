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
use ay_lra::GomoryCut;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

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

        // Prime the inner solver: branch scopes stack cuts on top of the
        // CURRENT tableau, so the asserted atoms must have been processed by
        // at least one check. In the solve pipeline a check always precedes
        // this call; direct callers (tests) may not have run one.
        match self.lia.check() {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                // The un-split (exact-only) tableau is already infeasible.
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return Some(TheoryResult::Unsat(conflict));
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

        // 3. Enumerate every assignment of the chosen factors. The in-branch
        //    repair search costs up to MAX_ENUM_DOMAIN exact evaluations per
        //    branch, so it is only enabled for small splits.
        let repair_in_branch = branches <= 16;
        let mut assignment: Vec<i64> = chosen.iter().map(|&(_, lo, _)| lo).collect();
        let mut all_branches_unsat = true;
        // Union of the per-branch refutation literals, when EVERY refuted
        // branch produced a minimal explanation (see BranchOutcome::Refuted).
        let mut minimal_union: Option<Vec<TheoryLit>> = Some(Vec::new());
        loop {
            let branch_result =
                self.check_factor_split_branch(&chosen, &assignment, repair_in_branch);
            match branch_result {
                BranchOutcome::Refuted { literals } => match (&mut minimal_union, literals) {
                    (Some(union), Some(lits)) => union.extend(lits),
                    _ => minimal_union = None,
                },
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
            let mut carry = true;
            for i in (0..chosen.len()).rev() {
                if carry {
                    assignment[i] += 1;
                    if assignment[i] > chosen[i].2 {
                        assignment[i] = chosen[i].1;
                    } else {
                        carry = false;
                    }
                }
            }
            if carry {
                break;
            }
        }

        if all_branches_unsat {
            if self.debug {
                safe_eprintln!(
                    "[NIA] Factor split: all {} branches refuted -- UNSAT",
                    branches
                );
            }
            // MINIMAL CONFLICT (#nia-factor-split-conflict): when every branch
            // was refuted in round 0 with an LRA conflict citing only live
            // asserted literals, the union of those literals plus the cover
            // atoms is a sound conflict:
            //   cover ⇒ ⋁_i pins_i           (the boxes enumerate completely)
            //   pins_i ∧ C_i ⇒ ⊥              (branch i's LRA refutation; the
            //                                  pins and round-0 linearizations
            //                                  are the only sentinel-reason
            //                                  bounds and are implied by pins_i)
            // hence cover ∧ ⋀_i C_i ⇒ ⊥. A small conflict gives DPLL(T) a
            // usable learned clause instead of the full asserted set.
            // Guards: congruence shared-equality lemmas would add premises
            // invisible to LRA conflict literals, so fall back to the full
            // asserted set when any are linked; likewise when any branch
            // needed contraction rounds (round >= 1 fixes carry tableau-level
            // justifications that the conflict literals do not capture).
            let conflict: Vec<TheoryLit> = match minimal_union {
                Some(mut union) if self.congruence_linked.is_empty() => {
                    union.extend(cover_reasons);
                    union.sort_unstable_by_key(|l| (l.term.0, l.value));
                    union.dedup_by_key(|l| (l.term.0, l.value));
                    // Every literal must actually be asserted (defensive: a
                    // stale literal would make the conflict clause unsound).
                    let all_live = union
                        .iter()
                        .all(|l| self.asserted.contains(&(l.term, l.value)));
                    if all_live && !union.is_empty() {
                        union
                    } else {
                        self.asserted
                            .iter()
                            .map(|&(t, v)| TheoryLit { term: t, value: v })
                            .collect()
                    }
                }
                _ => self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect(),
            };
            return Some(TheoryResult::Unsat(conflict));
        }
        None
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

        let (factor, divisors) = self.find_divisor_split_target()?;
        if self.debug {
            safe_eprintln!(
                "[NIA] Divisor split: factor {:?} over {} divisors {:?}",
                factor,
                divisors.len(),
                divisors
            );
        }

        // Prime the inner LIA: branch scopes stack cuts on the CURRENT tableau,
        // so the asserted atoms must have been processed by at least one check.
        match self.lia.check() {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                let conflict: Vec<TheoryLit> = self
                    .asserted
                    .iter()
                    .map(|&(t, v)| TheoryLit { term: t, value: v })
                    .collect();
                return Some(TheoryResult::Unsat(conflict));
            }
            _ => {}
        }

        // The in-branch repair search costs up to MAX_ENUM_DOMAIN exact
        // evaluations per branch; only enable it for small covers.
        let repair_in_branch = divisors.len() <= 16;
        let chosen = [(factor, 0i64, 0i64)];
        let mut all_refuted = true;
        for &d in &divisors {
            match self.check_factor_split_branch(&chosen, &[d], repair_in_branch) {
                BranchOutcome::Refuted { .. } => {}
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
            // The complete cover is refuted in every branch: the whole asserted
            // set is UNSAT. Use the full asserted set as the conflict (always
            // sound); a minimal core is not required for correctness.
            let conflict: Vec<TheoryLit> = self
                .asserted
                .iter()
                .map(|&(t, v)| TheoryLit { term: t, value: v })
                .collect();
            return Some(TheoryResult::Unsat(conflict));
        }
        None
    }

    /// Find a divisor-split target: an asserted positive equality
    /// `(= aux k)` / `(= k aux)` where `aux` is a registered monomial's aux
    /// var and `k` a NONZERO integer constant. Returns the chosen factor
    /// variable and the complete signed divisor cover `±D(|k|)`, preferring
    /// the atom with the FEWEST branches (smallest divisor set) to bound cost.
    /// Skips atoms whose factors are not all integer-sorted (the `v | k`
    /// argument needs every factor to be an integer) and those out of budget.
    fn find_divisor_split_target(&self) -> Option<(TermId, Vec<i64>)> {
        let mut best: Option<(TermId, Vec<i64>)> = None;
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
                Some((_, prev)) if prev.len() <= divisors.len() => {}
                _ => best = Some((factor, divisors)),
            }
        }
        best
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
    fn check_factor_split_branch(
        &mut self,
        chosen: &[(TermId, i64, i64)],
        values: &[i64],
        repair_in_branch: bool,
    ) -> BranchOutcome {
        /// Contraction rounds per branch (each round is one LIA re-check).
        const MAX_BRANCH_ROUNDS: usize = 4;

        self.lia.push();

        // Pin each chosen factor: v <= x AND x <= v as exact bound cuts.
        for (&(var, _, _), &value) in chosen.iter().zip(values) {
            let lra_var = self.lia.lra_solver_mut().ensure_var_registered(var);
            for is_lower in [true, false] {
                self.lia.lra_solver_mut().add_gomory_cut(
                    &GomoryCut {
                        coeffs: vec![(lra_var, BigRational::one())],
                        bound: BigRational::from_integer(BigInt::from(value)),
                        is_lower,
                        reasons: vec![(TermId::SENTINEL, true)],
                        source_term: None,
                    },
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
                        .get_bounds(var)
                        .map(|(l, u)| (l.map(|b| b.value.to_big()), u.map(|b| b.value.to_big())))
                );
            }
        }

        // Known-fixed values, seeded with the pins and grown by contraction.
        let mut fixed: HashMap<TermId, BigInt> = chosen
            .iter()
            .map(|&(v, _, _)| v)
            .zip(values.iter().map(|&v| BigInt::from(v)))
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
        // Single-variable orderings `x <= y` entailed by {pins ∪ asserted
        // atoms}, grown by the linearized-atom derivation each round.
        let mut orderings: HashSet<(TermId, TermId)> = HashSet::default();

        let monomials: Vec<(TermId, Vec<TermId>)> = self
            .monomials_sorted()
            .iter()
            .map(|m| (m.aux_var, m.vars.clone()))
            .collect();

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
                match self.derive_branch_facts(&mut fixed, &mut orderings) {
                    BranchFactStep::Refuted => {
                        if self.debug {
                            safe_eprintln!(
                                "[NIA] Factor split branch {values:?} round {round}: \
                                 refuted by linearized asserted atom"
                            );
                        }
                        self.lia.pop();
                        return BranchOutcome::Refuted { literals: None };
                    }
                    BranchFactStep::Grew => derived_pins = true,
                    BranchFactStep::Fixpoint => break,
                }
            }

            // Assert explicit pin cuts for contraction-derived fixed values so
            // the branch tableau enforces them (they are exact consequences of
            // the pins + asserted atoms).
            let mut added = false;
            let mut new_pins: Vec<(TermId, BigInt)> = fixed
                .iter()
                .filter(|(v, _)| !pin_cut_emitted.contains(*v))
                .map(|(&v, val)| (v, val.clone()))
                .collect();
            new_pins.sort_unstable_by_key(|(v, _)| v.0);
            for (v, val) in new_pins {
                let lra_var = self.lia.lra_solver_mut().ensure_var_registered(v);
                for is_lower in [true, false] {
                    self.lia.lra_solver_mut().add_gomory_cut(
                        &GomoryCut {
                            coeffs: vec![(lra_var, BigRational::one())],
                            bound: BigRational::from_integer(val.clone()),
                            is_lower,
                            reasons: vec![(TermId::SENTINEL, true)],
                            source_term: None,
                        },
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
            for (aux, vars) in &monomials {
                if linearized.contains(aux) {
                    continue;
                }
                let mut fixed_product = BigInt::one();
                let mut unfixed: Vec<TermId> = Vec::new();
                for v in vars {
                    match fixed.get(v) {
                        Some(val) => fixed_product *= val,
                        None => unfixed.push(*v),
                    }
                }
                if unfixed.len() == vars.len() {
                    // Nothing fixed: no exact consequence available.
                    continue;
                }
                let (coeffs, bound) = if fixed_product.is_zero() {
                    // A fixed factor is zero: aux = 0 exactly, regardless of
                    // how many factors remain unfixed.
                    let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
                    (vec![(aux_var, BigRational::one())], BigRational::zero())
                } else if unfixed.is_empty() {
                    // aux = fixed_product
                    let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
                    (
                        vec![(aux_var, BigRational::one())],
                        BigRational::from_integer(fixed_product),
                    )
                } else if unfixed.len() == 1 {
                    // aux - c*y = 0
                    let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
                    let y_var = self.lia.lra_solver_mut().ensure_var_registered(unfixed[0]);
                    (
                        vec![
                            (aux_var, BigRational::one()),
                            (y_var, -BigRational::from_integer(fixed_product)),
                        ],
                        BigRational::zero(),
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
                        vec![
                            (aux_var, BigRational::one()),
                            (res_var, -BigRational::from_integer(fixed_product)),
                        ],
                        BigRational::zero(),
                    )
                };
                for is_lower in [true, false] {
                    self.lia.lra_solver_mut().add_gomory_cut(
                        &GomoryCut {
                            coeffs: coeffs.clone(),
                            bound: bound.clone(),
                            is_lower,
                            reasons: vec![(TermId::SENTINEL, true)],
                            source_term: None,
                        },
                        *aux,
                    );
                }
                linearized.insert(*aux);
                added = true;
            }

            // Product monotonicity cuts (#nia-factor-split-monotone): for
            // monomial pairs `P*x` / `P*y` with x <= y entailed and every
            // shared factor non-negative, order the aux vars.
            if self.emit_branch_monotonicity_cuts(
                &monomials,
                &fixed,
                &orderings,
                &mut monotone_emitted,
            ) > 0
            {
                added = true;
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
                    "[NIA] Factor split branch {:?} round {}: LRA {:?}",
                    values,
                    round,
                    result
                );
            }
            match result {
                TheoryResult::Unsat(lits) => {
                    outcome = BranchOutcome::Refuted {
                        literals: (round == 0).then_some(lits),
                    };
                    break;
                }
                TheoryResult::UnsatWithFarkas(conflict) => {
                    outcome = BranchOutcome::Refuted {
                        literals: (round == 0).then_some(conflict.literals),
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
                    if self.branch_diseq_probes_refute(&fixed) {
                        if self.debug {
                            safe_eprintln!(
                                "[NIA] Factor split branch {values:?} round {round}: \
                                 refuted by disequality entailment probe"
                            );
                        }
                        outcome = BranchOutcome::Refuted { literals: None };
                        break;
                    }
                    // Contraction: absorb every factor variable the branch
                    // tableau now pins to a single integer value.
                    let mut grew = false;
                    for (_, vars) in &monomials {
                        for v in vars {
                            if fixed.contains_key(v) {
                                continue;
                            }
                            let Some((Some(lb), Some(ub))) = self.lia.lra_solver().get_bounds(*v)
                            else {
                                continue;
                            };
                            let (lo, hi) = (lb.value.to_big(), ub.value.to_big());
                            if lo == hi && !lb.strict && !ub.strict && lo.denom().is_one() {
                                fixed.insert(*v, lo.numer().clone());
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
        self.lia.pop();
        outcome
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
    fn derive_branch_facts(
        &mut self,
        fixed: &mut HashMap<TermId, BigInt>,
        orderings: &mut HashSet<(TermId, TermId)>,
    ) -> BranchFactStep {
        use std::cmp::Ordering as CmpOrdering;

        let mut grew = false;
        // Walk indices to avoid borrowing self.asserted across &self calls.
        for idx in 0..self.asserted.len() {
            let (term, positive) = self.asserted[idx];
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                continue;
            };
            let op = name.as_str();
            if args.len() != 2 || !matches!(op, "=" | "<=" | "<" | ">=" | ">") {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            let mut coeffs: HashMap<TermId, BigRational> = HashMap::default();
            let mut konst = BigRational::zero();
            if !self.branch_linear_accumulate(
                lhs,
                &BigRational::one(),
                fixed,
                &mut coeffs,
                &mut konst,
            ) || !self.branch_linear_accumulate(
                rhs,
                &-BigRational::one(),
                fixed,
                &mut coeffs,
                &mut konst,
            ) {
                continue;
            }
            coeffs.retain(|_, c| !c.is_zero());

            // Normalize (op, positive) to an operator on `form OP 0` where
            // form = lhs - rhs = Σ coeffs + konst.
            #[derive(Clone, Copy, PartialEq)]
            enum Rel {
                Eq,
                Neq,
                Le,
                Lt,
                Ge,
                Gt,
            }
            let rel = match (op, positive) {
                ("=", true) => Rel::Eq,
                ("=", false) => Rel::Neq,
                ("<=", true) => Rel::Le,
                ("<=", false) => Rel::Gt,
                ("<", true) => Rel::Lt,
                ("<", false) => Rel::Ge,
                (">=", true) => Rel::Ge,
                (">=", false) => Rel::Lt,
                (">", true) => Rel::Gt,
                (">", false) => Rel::Le,
                _ => continue,
            };

            match coeffs.len() {
                0 => {
                    // Ground residual: evaluate exactly.
                    let cmp = konst.cmp(&BigRational::zero());
                    let holds = match rel {
                        Rel::Eq => cmp == CmpOrdering::Equal,
                        Rel::Neq => cmp != CmpOrdering::Equal,
                        Rel::Le => cmp != CmpOrdering::Greater,
                        Rel::Lt => cmp == CmpOrdering::Less,
                        Rel::Ge => cmp != CmpOrdering::Less,
                        Rel::Gt => cmp == CmpOrdering::Greater,
                    };
                    if !holds {
                        return BranchFactStep::Refuted;
                    }
                }
                1 => {
                    if rel != Rel::Eq {
                        continue;
                    }
                    let (&v, c) = coeffs.iter().next().expect("len checked");
                    // c*v + konst = 0  =>  v = -konst/c
                    let value = -(&konst / c);
                    if !value.denom().is_one() {
                        // An integer variable forced to a fractional value:
                        // the branch is infeasible.
                        return BranchFactStep::Refuted;
                    }
                    let value = value.numer().clone();
                    match fixed.get(&v) {
                        Some(existing) if *existing != value => {
                            return BranchFactStep::Refuted;
                        }
                        Some(_) => {}
                        None => {
                            fixed.insert(v, value);
                            grew = true;
                        }
                    }
                }
                2 => {
                    // Difference comparison c*(x - y) REL -konst?
                    let mut it = coeffs.iter();
                    let (&v1, c1) = it.next().expect("len checked");
                    let (&v2, c2) = it.next().expect("len checked");
                    if *c1 != -c2.clone() {
                        continue;
                    }
                    // Normalize to positive coefficient on (x - y).
                    let (x, y, c) = if c1 > &BigRational::zero() {
                        (v1, v2, c1.clone())
                    } else {
                        (v2, v1, c2.clone())
                    };
                    // c*(x - y) + konst REL 0  =>  x - y REL' -konst/c  (c > 0)
                    let bound = -(&konst / &c);
                    let zero = BigRational::zero();
                    match rel {
                        Rel::Eq if bound == zero => {
                            if orderings.insert((x, y)) {
                                grew = true;
                            }
                            if orderings.insert((y, x)) {
                                grew = true;
                            }
                        }
                        Rel::Le | Rel::Lt if bound <= zero => {
                            // x - y <= bound <= 0  =>  x <= y.
                            if orderings.insert((x, y)) {
                                grew = true;
                            }
                        }
                        Rel::Ge | Rel::Gt
                            if bound >= zero
                            // x - y >= bound >= 0  =>  y <= x.
                            && orderings.insert((y, x)) =>
                        {
                            grew = true;
                        }
                        _ => {}
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

    /// Accumulate `mult * term` into a linear form over atomic terms
    /// (variables and monomial aux vars), substituting `fixed` values.
    /// Products reduce EXACTLY under the fixed set (see
    /// [`Self::derive_branch_facts`]); returns `false` when the term cannot
    /// be linearized exactly (the caller skips that atom).
    fn branch_linear_accumulate(
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
                // Int-sorted variables only: the derived pins and the ±1
                // disequality probes rely on integrality.
                if !matches!(self.terms.sort(term), Sort::Int) {
                    return false;
                }
                *coeffs.entry(term).or_default() += mult;
                true
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => args
                    .iter()
                    .all(|&a| self.branch_linear_accumulate(a, mult, fixed, coeffs, konst)),
                "-" if args.len() == 1 => {
                    self.branch_linear_accumulate(args[0], &-mult.clone(), fixed, coeffs, konst)
                }
                "-" if !args.is_empty() => {
                    if !self.branch_linear_accumulate(args[0], mult, fixed, coeffs, konst) {
                        return false;
                    }
                    let neg = -mult.clone();
                    args[1..]
                        .iter()
                        .all(|&a| self.branch_linear_accumulate(a, &neg, fixed, coeffs, konst))
                }
                "*" => {
                    // Split into constant factors and the rest; reduce the
                    // rest via `fixed` (multiplicity preserved).
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
                    // >= 2 unfixed factors: exact only as a registered
                    // monomial aux (product(vars) == aux by invariant).
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

    /// Emit branch-scoped product monotonicity cuts
    /// (#nia-factor-split-monotone): for registered monomial pairs whose
    /// factor multisets differ in exactly ONE occurrence (`P*x` vs `P*y`),
    /// with `x <= y` in `orderings` and every shared factor non-negative
    /// (fixed at a non-negative value, or carrying an asserted
    /// Positive/NonNegative/Zero sign constraint), assert
    /// `aux(P*x) <= aux(P*y)`. Sound: `P >= 0 ∧ x <= y ⇒ P*x <= P*y`, and
    /// every premise is entailed by {branch pins ∪ asserted atoms}. Returns
    /// the number of cuts added (deduped per branch via `emitted`).
    fn emit_branch_monotonicity_cuts(
        &mut self,
        monomials: &[(TermId, Vec<TermId>)],
        fixed: &HashMap<TermId, BigInt>,
        orderings: &HashSet<(TermId, TermId)>,
        emitted: &mut HashSet<(TermId, TermId)>,
    ) -> usize {
        if orderings.is_empty() {
            return 0;
        }
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
                if !shared.iter().all(|&s| self.branch_var_nonneg(s, fixed)) {
                    continue;
                }
                // Both directions may be entailed (equality-derived).
                for (lo_aux, hi_aux, lo, hi) in [(*aux1, *aux2, x, y), (*aux2, *aux1, y, x)] {
                    if !orderings.contains(&(lo, hi)) {
                        continue;
                    }
                    if !emitted.insert((lo_aux, hi_aux)) {
                        continue;
                    }
                    let lo_var = self.lia.lra_solver_mut().ensure_var_registered(lo_aux);
                    let hi_var = self.lia.lra_solver_mut().ensure_var_registered(hi_aux);
                    // lo_aux - hi_aux <= 0 (upper bound).
                    self.lia.lra_solver_mut().add_gomory_cut(
                        &GomoryCut {
                            coeffs: vec![
                                (lo_var, BigRational::one()),
                                (hi_var, -BigRational::one()),
                            ],
                            bound: BigRational::zero(),
                            is_lower: false,
                            reasons: vec![(TermId::SENTINEL, true)],
                            source_term: None,
                        },
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
    fn branch_diseq_probes_refute(&mut self, fixed: &HashMap<TermId, BigInt>) -> bool {
        /// Max disequalities probed per branch round (2 LRA checks each).
        const MAX_DISEQ_PROBES: usize = 8;

        let mut probes = 0usize;
        for idx in 0..self.asserted.len() {
            let (term, positive) = self.asserted[idx];
            let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
                continue;
            };
            let is_diseq = (name == "=" && !positive) || (name == "distinct" && positive);
            if !is_diseq || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            let mut coeffs: HashMap<TermId, BigRational> = HashMap::default();
            let mut konst = BigRational::zero();
            if !self.branch_linear_accumulate(
                lhs,
                &BigRational::one(),
                fixed,
                &mut coeffs,
                &mut konst,
            ) || !self.branch_linear_accumulate(
                rhs,
                &-BigRational::one(),
                fixed,
                &mut coeffs,
                &mut konst,
            ) {
                continue;
            }
            coeffs.retain(|_, c| !c.is_zero());
            if coeffs.is_empty() {
                // Ground difference: the disequality is decided exactly.
                if konst.is_zero() {
                    return true;
                }
                continue;
            }
            if probes >= MAX_DISEQ_PROBES {
                break;
            }
            probes += 1;

            let mut lra_coeffs: Vec<(u32, BigRational)> = Vec::with_capacity(coeffs.len());
            let mut sorted: Vec<(TermId, BigRational)> = coeffs.into_iter().collect();
            sorted.sort_unstable_by_key(|(t, _)| t.0);
            for (t, c) in sorted {
                let v = self.lia.lra_solver_mut().ensure_var_registered(t);
                lra_coeffs.push((v, c));
            }

            let mut both_refuted = true;
            for ge_side in [true, false] {
                // Σ coeffs >= 1 - konst   (ge side: e >= 1)
                // Σ coeffs <= -1 - konst  (le side: e <= -1)
                let bound = if ge_side {
                    BigRational::one() - &konst
                } else {
                    -BigRational::one() - &konst
                };
                self.lia.push();
                self.lia.lra_solver_mut().add_gomory_cut(
                    &GomoryCut {
                        coeffs: lra_coeffs.clone(),
                        bound,
                        is_lower: ge_side,
                        reasons: vec![(TermId::SENTINEL, true)],
                        source_term: None,
                    },
                    term,
                );
                let probe_result = self.lia.lra_solver_mut().check();
                self.lia.pop();
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

    /// True when `var` is entailed non-negative in the branch: fixed at a
    /// non-negative value, or carrying an asserted Positive/NonNegative/Zero
    /// sign constraint (recorded from asserted sign atoms in
    /// `record_sign_constraint`).
    fn branch_var_nonneg(&self, var: TermId, fixed: &HashMap<TermId, BigInt>) -> bool {
        use ay_core::nonlinear::SignConstraint;
        if let Some(val) = fixed.get(&var) {
            return val.sign() != num_bigint::Sign::Minus;
        }
        self.var_sign_constraints.get(&var).is_some_and(|cs| {
            cs.iter().any(|(c, _)| {
                matches!(
                    c,
                    SignConstraint::Positive | SignConstraint::NonNegative | SignConstraint::Zero
                )
            })
        })
    }
}

/// Outcome of one linearized-atom fact-derivation pass
/// (see [`NiaSolver::derive_branch_facts`]).
enum BranchFactStep {
    /// An asserted atom is exactly FALSE under the branch's entailed values —
    /// the branch is infeasible.
    Refuted,
    /// New pins or orderings were derived; another pass may find more.
    Grew,
    /// Nothing new derivable from the current fixed set.
    Fixpoint,
}

/// Classification of one factor-split branch.
enum BranchOutcome {
    /// LRA refuted the branch (sound: relaxation UNSAT ⊆ true UNSAT).
    /// `literals` carries the refutation's asserted-literal explanation when
    /// it is usable for a MINIMAL aggregated conflict (round-0 refutation
    /// only — contraction rounds introduce tableau-level premises the
    /// literals do not capture); `None` forces the full-asserted-set
    /// fallback conflict.
    Refuted { literals: Option<Vec<TheoryLit>> },
    /// The branch produced an exactly-verified integer witness.
    VerifiedSat,
    /// Neither refuted nor verified — the whole split must return `None`.
    Open,
}
