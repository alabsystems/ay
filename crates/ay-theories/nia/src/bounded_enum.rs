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

use ay_core::{TheoryLit, TheoryResult};

use super::*;

/// Maximum total domain size for bounded enumeration (product of all variable ranges).
const MAX_ENUM_DOMAIN: i64 = 10_000;

impl NiaSolver<'_> {
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

        // Phase 1: Get direct integer bounds from LRA
        let lra = self.lia.lra_solver();
        let mut var_bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::default();

        for &var in &vars {
            let (lo, hi) = match self.get_integer_bounds(var, lra) {
                Some((lo, hi)) => (Some(lo), Some(hi)),
                None => {
                    // Try partial bounds
                    let (lo_opt, hi_opt) = self.get_partial_integer_bounds(var, lra);
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
                let (aux_lo, aux_hi) = self.get_monomial_bounds(mon, lra);

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
                                        // var >= ceil(l / other_product)
                                        let inferred_lo = (l + other_product - 1) / other_product;
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
        self.contract_enum_bounds(&vars, &mut var_bounds);

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
            let range = hi - lo + 1;
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

        loop {
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

            // Advance to next point (odometer-style increment)
            let mut carry = true;
            for i in (0..n).rev() {
                if carry {
                    assignment[i] += 1;
                    if assignment[i] > var_ranges[i].2 {
                        assignment[i] = var_ranges[i].1;
                        // carry continues
                    } else {
                        carry = false;
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

        let conflict: Vec<TheoryLit> = self
            .asserted
            .iter()
            .map(|(term, val)| TheoryLit::new(*term, *val))
            .collect();
        Some(TheoryResult::Unsat(conflict))
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
        let lra = self.lia.lra_solver();
        let mut var_bounds: HashMap<TermId, (Option<i64>, Option<i64>)> = HashMap::default();
        for &var in &vars {
            let (lo, hi) = match self.get_integer_bounds(var, lra) {
                Some((lo, hi)) => (Some(lo), Some(hi)),
                None => self.get_partial_integer_bounds(var, lra),
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
        let cap = {
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
        loop {
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

            let mut carry = true;
            for i in (0..n).rev() {
                if carry {
                    assignment[i] += 1;
                    if assignment[i] > var_ranges[i].2 {
                        assignment[i] = var_ranges[i].1;
                    } else {
                        carry = false;
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
        match self.terms.get(term) {
            TermData::Var(_, _)
                if matches!(self.terms.sort(term), Sort::Int) && !out.contains(&term) =>
            {
                out.push(term);
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.collect_int_var_leaves(arg, out);
                }
            }
            TermData::Not(inner) => self.collect_int_var_leaves(*inner, out),
            TermData::Ite(c, t, e) => {
                self.collect_int_var_leaves(*c, out);
                self.collect_int_var_leaves(*t, out);
                self.collect_int_var_leaves(*e, out);
            }
            _ => {}
        }
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
        if self.debug {
            safe_eprintln!(
                "[NIA] Repair search: {} suspects of {} vars, cap={} (box {})",
                suspects.len(),
                vars.len(),
                cap,
                (2 * cap + 1).pow(k)
            );
        }
        loop {
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

        self.bounded_enum_model = Some(model);
    }

    /// Get bounds for a monomial, including bounds propagated through equalities.
    ///
    /// Checks: (1) direct LRA bounds on the aux variable, (2) equality constraints
    /// in the asserted atoms like `(= area (* w h))` where `area` has bounds.
    fn get_monomial_bounds(
        &self,
        mon: &Monomial,
        lra: &ay_lra::LraSolver,
    ) -> (Option<i64>, Option<i64>) {
        // First try direct bounds on the monomial's auxiliary variable
        let (mut lo, mut hi) = match self.get_integer_bounds(mon.aux_var, lra) {
            Some((lo, hi)) => (Some(lo), Some(hi)),
            None => self.get_partial_integer_bounds(mon.aux_var, lra),
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
                                .unwrap_or_else(|| {
                                    match self.get_integer_bounds(other_term, lra) {
                                        Some((lo, hi)) => (Some(lo), Some(hi)),
                                        None => self.get_partial_integer_bounds(other_term, lra),
                                    }
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
    fn get_partial_integer_bounds(
        &self,
        var: TermId,
        lra: &ay_lra::LraSolver,
    ) -> (Option<i64>, Option<i64>) {
        let bounds = match lra.get_bounds(var) {
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
    /// Returns `Some((lower, upper))` as i64 integers if the variable has
    /// finite bounds. For strict bounds on integers, adjusts to the nearest
    /// valid integer (e.g., x > 0 strict becomes x >= 1).
    fn get_integer_bounds(&self, var: TermId, lra: &ay_lra::LraSolver) -> Option<(i64, i64)> {
        let (lb_opt, ub_opt) = lra.get_bounds(var)?;

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
        match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                if name == "*" {
                    let mut var_factors = 0usize;
                    let mut const_product = BigInt::one();
                    for &arg in args {
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
                        for &arg in args {
                            if matches!(self.terms.get(arg), TermData::Var(_, _))
                                && matches!(self.terms.sort(arg), Sort::Int)
                                && !vars.contains(&arg)
                            {
                                vars.push(arg);
                            }
                        }
                    }
                }
                for &arg in args {
                    self.collect_scaled_product_vars(arg, vars);
                }
            }
            TermData::Not(inner) => self.collect_scaled_product_vars(*inner, vars),
            TermData::Ite(c, t, e) => {
                self.collect_scaled_product_vars(*c, vars);
                self.collect_scaled_product_vars(*t, vars);
                self.collect_scaled_product_vars(*e, vars);
            }
            _ => {}
        }
    }

    /// Check if a variable assignment satisfies all monomial constraints.
    ///
    /// For each assertion, evaluates it under the given assignment and checks
    /// if the constraint holds.
    fn check_assignment(&self, vars: &[TermId], values: &[i64]) -> Option<bool> {
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
        match self.terms.get(term) {
            TermData::Not(inner) => self.eval_constraint_exact(*inner, !positive, var_map),
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let lhs_val = self.eval_term(args[0], var_map);
                let rhs_val = self.eval_term(args[1], var_map);

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
        }
    }

    /// Evaluate a term to an integer value under the given variable assignment.
    ///
    /// Returns `None` if the term cannot be fully evaluated (e.g., unbound variable).
    ///
    /// Shared with the univariate-integer decider (`univariate_int.rs`) to
    /// materialize monomial aux-var values for the witness model.
    pub(crate) fn eval_term(&self, term: TermId, var_map: &HashMap<TermId, i64>) -> Option<BigInt> {
        match self.terms.get(term) {
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
                        sum += self.eval_term(arg, var_map)?;
                    }
                    Some(sum)
                }
                "-" if args.len() == 1 => {
                    let val = self.eval_term(args[0], var_map)?;
                    Some(-val)
                }
                "-" if args.len() == 2 => {
                    let l = self.eval_term(args[0], var_map)?;
                    let r = self.eval_term(args[1], var_map)?;
                    Some(l - r)
                }
                "*" => {
                    let mut prod = BigInt::one();
                    for &arg in args {
                        prod *= self.eval_term(arg, var_map)?;
                    }
                    Some(prod)
                }
                _ => None,
            },
            _ => None,
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
}
