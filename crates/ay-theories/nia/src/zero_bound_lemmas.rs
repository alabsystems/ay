// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Zero-lower-bound product sign / monotonicity lemmas (#nia-zero-bound).
//!
//! Extends NIA incremental linearization with two families of *exact*
//! (universally valid) ordered-ring lemmas that the model-point tangent /
//! McCormick machinery cannot express for **unbounded** variables. Both are
//! the tangent plane of `m = x*y` taken at the *asserted* lower bound `0`
//! rather than at a model point, so they are theorems, not approximations:
//!
//! 1. **Product sign** — for a monomial `m = x1*...*xn` where every factor
//!    has an asserted weak sign (`xi >= 0` or `xi <= 0`):
//!    `m * prod(sign_i) >= 0`. In particular `x >= 0 && y >= 0 -> x*y >= 0`.
//!    If some factor is asserted zero (`xi = 0`, or both `xi >= 0` and
//!    `xi <= 0`), then `m = 0` (both bounds are emitted).
//!
//! 2. **Multiplication monotonicity** — for two registered monomials
//!    `m_lo = lo*z` and `m_hi = hi*z` sharing the factor `z`, with an
//!    asserted weak order `lo <= hi`:
//!    - `z >= 0 -> lo*z <= hi*z` (since `(hi - lo)*z >= 0`),
//!    - `z <= 0 -> lo*z >= hi*z`.
//!
//! 3. **Ordered-box product comparison** — for two registered monomials
//!    `p = a1*...*an` and `q = b1*...*bn` of the same degree, when the
//!    factors pair up (a bijection) so that each `ai` is asserted
//!    non-negative and each pair is either the identical term or carries an
//!    asserted weak order `ai <= bi`: `p <= q`. Validity: replace `ai` by
//!    `bi` one position at a time; each step changes the product by
//!    `(bi - ai) * cofactor`, where the cofactor is a product of terms that
//!    are all `>= 0` given the reasons (`aj >= 0` asserted, and
//!    `bj >= aj >= 0`), so the product is non-decreasing along the chain.
//!    This is the fully-symbolic upper bound `x <= xb && y <= yb && x >= 0 &&
//!    y >= 0 -> x*y <= xb*yb` (Verus `lemma_mul_upper_bound`, upstream
//!    `nonlinear.rs` test1) that neither family 1/2 nor McCormick (which
//!    needs numeric bounds) can express.
//!
//! ## Soundness
//!
//! Every emitted linear cut is a valid theorem of ordered rings (hence of the
//! integers) *conditional only on its `reasons`* — the exact asserted literals
//! it was derived from:
//!
//! - The preconditions are read **only from `self.asserted`** (via
//!   `nonlinear::extract_sign_constraint` on each asserted literal, and a
//!   direct scan for binary order atoms). They are never read from LRA bounds
//!   or model values, so no tentative sign cut, Gomory cut, tangent plane, or
//!   patch can ever leak into a lemma's justification.
//! - Each cut is asserted through `add_gomory_cut` with a **non-empty
//!   `reasons` list** (the justifying literals), so when the cut participates
//!   in a LIA/LRA Farkas conflict the explanation includes those literals and
//!   the resulting conflict clause `¬r1 ∨ ... ∨ ¬rk ∨ ¬other-bounds` is a
//!   valid clause. This matters on the iteration-0 UNSAT path of
//!   `nia_check_loop`, which returns LIA's conflict verbatim.
//! - Because the lemmas are exact, they intentionally do **not** set
//!   `used_tangent_approximation` in the check loop: an UNSAT they cause is
//!   genuine.
//! - Adding a valid lemma can never remove a genuine model, so no SAT answer
//!   can be lost: any true model of the asserted constraints satisfies the
//!   product semantics of `*` and therefore satisfies both lemma families.
//!
//! ## Motivation
//!
//! Verus/vstd nonlinear-arithmetic lemmas of the shapes
//! `lemma_mul_stay_positive` (`0 <= x && 0 <= y ==> 0 <= x*y`) and
//! `lemma_inequality_after_mul` (`x <= y && 0 <= z ==> x*z <= y*z`) negate to
//! constraint sets over **unbounded** integers. McCormick needs finite bounds,
//! the tangent hyperplane at the model point is an approximation whose UNSAT
//! is rechecked away, and bounded enumeration needs a finite box — so these
//! previously stalled at `unknown`. The zero-bound lemmas close them in the
//! first LIA check.

use ay_core::nonlinear::{self, SignConstraint};
use ay_core::term::{Symbol, TermData, TermId};
use ay_lra::GomoryCut;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

use super::NiaSolver;

/// Weak-sign facts derived from the currently asserted literals.
///
/// `nonneg[t]` / `nonpos[t]` hold the asserted literal (atom term, value)
/// justifying `t >= 0` / `t <= 0`. A strict sign implies its weak form; an
/// asserted `t = 0` justifies both. `BTreeMap` keeps iteration deterministic.
#[derive(Default)]
struct WeakSigns {
    nonneg: BTreeMap<TermId, (TermId, bool)>,
    nonpos: BTreeMap<TermId, (TermId, bool)>,
}

impl NiaSolver<'_> {
    /// Emit the zero-lower-bound product sign / monotonicity lemmas for the
    /// current assertion set (see module docs). Returns the number of cuts
    /// added. Idempotent within a scope via `zero_bound_emitted` (cleared on
    /// `pop`/`reset`; re-deriving after a scope change is sound because each
    /// lemma is valid given its reasons, which are re-checked here).
    pub(crate) fn add_zero_bound_product_lemmas(&mut self) -> usize {
        if self.monomials.is_empty() {
            return 0;
        }

        // Weak signs read ONLY from asserted literals (never LRA bounds /
        // models), so each fact is self-justifying: the reason literal IS the
        // asserted atom it was extracted from.
        let mut signs = WeakSigns::default();
        for &(t, v) in &self.asserted {
            let Some((subject, c)) = nonlinear::extract_sign_constraint(self.terms, t, v) else {
                continue;
            };
            match c {
                SignConstraint::Positive | SignConstraint::NonNegative => {
                    signs.nonneg.entry(subject).or_insert((t, v));
                }
                SignConstraint::Negative | SignConstraint::NonPositive => {
                    signs.nonpos.entry(subject).or_insert((t, v));
                }
                SignConstraint::Zero => {
                    signs.nonneg.entry(subject).or_insert((t, v));
                    signs.nonpos.entry(subject).or_insert((t, v));
                }
            }
        }

        // Asserted weak orders `lo <= hi` (from `<`, `<=`, `>`, `>=` atoms of
        // either polarity; a strict order implies the weak one, a negated weak
        // order implies the reversed strict, hence the reversed weak one).
        // Shared by families 2 and 3.
        let mut orders: Vec<(TermId, TermId, (TermId, bool))> = Vec::new();
        for &(t, v) in &self.asserted {
            let TermData::App(Symbol::Named(name), args) = self.terms.get(t) else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let (lo, hi) = match (name.as_str(), v) {
                ("<", true) | ("<=", true) | (">", false) | (">=", false) => (args[0], args[1]),
                ("<", false) | ("<=", false) | (">", true) | (">=", true) => (args[1], args[0]),
                _ => continue,
            };
            if lo != hi {
                orders.push((lo, hi, (t, v)));
            }
        }

        let mut added = 0;
        added += self.add_product_sign_lemmas(&signs);
        added += self.add_mul_monotonicity_lemmas(&signs, &orders);
        added += self.add_product_pair_order_lemmas(&signs, &orders);
        added += self.add_box_product_upper_lemmas();
        added
    }

    /// Family 4: non-negative-box product upper bound (#nia-zero-bound).
    ///
    /// For a monomial `m = x1*...*xn` whose every factor carries JUSTIFIED
    /// LRA bounds `0 <= li <= xi <= ui` (each bound's reason atoms non-empty),
    /// emit the constant cut `m <= prod(ui)` justified by the union of all
    /// factors' bound reasons. Validity: on the non-negative box each factor
    /// satisfies `0 <= xi <= ui`, and a product of values in `[0, ui]` is at
    /// most `prod(ui)` — an ordered-ring theorem conditional exactly on the
    /// bound reasons. Strict bounds are weakened to their non-strict value
    /// (`xi < c ⇒ xi <= c`), which only loosens the cut (still valid).
    ///
    /// This is the iteration-0 form of the McCormick upper envelope for the
    /// constant-box case (upstream Verus `nonlinear.rs` test5:
    /// `0 <= x, z <= 0xffff ⊢ x*z <= 0xffff*0xffff`, and the range-collapse
    /// step `k = 0` of truncating-`mul` reasoning). McCormick itself only
    /// fires in the post-Sat refinement loop, which a fractional-model
    /// `NeedSplit` exits before reaching; this lemma is in the initial LIA
    /// constraint set, so branch-and-bound sees it immediately.
    ///
    /// Unlike families 1-3 this reads factor bounds from the LRA bound store
    /// (asserted + propagated), not only from asserted literals — the same
    /// justification discipline as the McCormick reason fix
    /// (#nia-mccormick-reasons): every used bound must carry non-empty reason
    /// atoms, which become the cut's reasons, so conflicts explain themselves
    /// with exactly the justifying literals.
    pub(crate) fn add_box_product_upper_lemmas(&mut self) -> usize {
        const MAX_DEGREE: usize = 8;
        let mons: Vec<(TermId, Vec<TermId>)> = self
            .monomials_sorted()
            .iter()
            .filter(|m| (2..=MAX_DEGREE).contains(&m.vars.len()))
            .map(|m| (m.aux_var, m.vars.clone()))
            .collect();
        if mons.is_empty() {
            return 0;
        }

        let mut added = 0;
        for (aux, vars) in &mons {
            let mut bound = BigRational::one();
            let mut reasons: Vec<(TermId, bool)> = Vec::new();
            let mut ok = true;
            for v in vars {
                let Some((Some(lb), Some(ub))) = self.lia.lra_solver().get_bounds(*v) else {
                    ok = false;
                    break;
                };
                if lb.reasons.is_empty()
                    || ub.reasons.is_empty()
                    || lb.value_big() < BigRational::zero()
                {
                    ok = false;
                    break;
                }
                bound *= ub.value_big();
                reasons.extend(
                    lb.reasons
                        .iter()
                        .copied()
                        .zip(lb.reason_values.iter().copied()),
                );
                reasons.extend(
                    ub.reasons
                        .iter()
                        .copied()
                        .zip(ub.reason_values.iter().copied()),
                );
            }
            if !ok || reasons.is_empty() {
                continue;
            }
            reasons.sort_unstable_by_key(|&(t, v)| (t, v));
            reasons.dedup();
            if !self.box_bound_emitted.insert((*aux, bound.clone())) {
                continue;
            }
            if self.debug {
                safe_eprintln!(
                    "[NIA] box product upper lemma: {:?} <= {} (reasons={:?})",
                    aux,
                    bound,
                    reasons
                );
            }
            let aux_var = self.lia.lra_solver_mut().ensure_var_registered(*aux);
            self.lia.lra_solver_mut().add_gomory_cut(
                &GomoryCut {
                    coeffs: vec![(aux_var, BigRational::one())],
                    bound,
                    is_lower: false,
                    reasons,
                    source_term: None,
                },
                *aux,
            );
            added += 1;
        }
        added
    }

    /// Family 1: product sign at the zero bound.
    ///
    /// For each monomial whose factors all carry asserted weak signs, emit
    /// `m >= 0` (evenly many `<= 0` factors) or `m <= 0` (oddly many).
    /// Validity: each chosen literal gives `sign_i * x_i >= 0`; the product
    /// of non-negatives is non-negative, i.e. `prod(sign_i) * m >= 0`.
    /// A definitely-zero factor makes `m = 0` (both bounds).
    fn add_product_sign_lemmas(&mut self, signs: &WeakSigns) -> usize {
        let mons: Vec<(TermId, Vec<TermId>)> = self
            .monomials_sorted()
            .iter()
            .map(|m| (m.aux_var, m.vars.clone()))
            .collect();

        let mut added = 0;
        for (aux, vars) in &mons {
            // Zero factor: x_i >= 0 and x_i <= 0 asserted (possibly the same
            // `x_i = 0` literal) force m = 0 regardless of the other factors.
            let zero_factor = vars.iter().find_map(|v| {
                let lo = signs.nonneg.get(v)?;
                let hi = signs.nonpos.get(v)?;
                Some((*lo, *hi))
            });
            if let Some((r_nonneg, r_nonpos)) = zero_factor {
                let mut reasons = vec![r_nonneg, r_nonpos];
                reasons.sort_unstable_by_key(|&(t, v)| (t, v));
                reasons.dedup();
                added += self.emit_zero_bound_cut(
                    vec![(*aux, BigRational::one())],
                    true,
                    &reasons,
                    (*aux, *aux, true),
                );
                added += self.emit_zero_bound_cut(
                    vec![(*aux, BigRational::one())],
                    false,
                    &reasons,
                    (*aux, *aux, false),
                );
                continue;
            }

            // All factors weakly signed: parity of `<= 0` factors decides the
            // product's weak sign. Prefer `>= 0` when both are available
            // (unreachable here — both available means a zero factor above).
            let mut reasons: Vec<(TermId, bool)> = Vec::with_capacity(vars.len());
            let mut odd_negatives = false;
            let mut all_signed = true;
            for v in vars {
                if let Some(&r) = signs.nonneg.get(v) {
                    reasons.push(r);
                } else if let Some(&r) = signs.nonpos.get(v) {
                    odd_negatives = !odd_negatives;
                    reasons.push(r);
                } else {
                    all_signed = false;
                    break;
                }
            }
            if !all_signed {
                continue;
            }
            reasons.sort_unstable_by_key(|&(t, v)| (t, v));
            reasons.dedup();
            let is_lower = !odd_negatives; // even: m >= 0; odd: m <= 0
            added += self.emit_zero_bound_cut(
                vec![(*aux, BigRational::one())],
                is_lower,
                &reasons,
                (*aux, *aux, is_lower),
            );
        }
        added
    }

    /// Family 2: multiplication monotonicity at the zero bound.
    ///
    /// For every asserted weak order `lo <= hi` (from `<`, `<=`, `>`, `>=`
    /// atoms of either polarity) and every weakly-signed shared factor `z`
    /// such that both `lo*z` and `hi*z` are registered monomials, emit
    /// `lo*z <= hi*z` (when `z >= 0`) or `lo*z >= hi*z` (when `z <= 0`).
    /// Validity: `(hi - lo) * z` is a product of two same-weak-sign values.
    fn add_mul_monotonicity_lemmas(
        &mut self,
        signs: &WeakSigns,
        orders: &[(TermId, TermId, (TermId, bool))],
    ) -> usize {
        if orders.is_empty() {
            return 0;
        }

        // Candidate shared factors: subjects with an asserted weak sign
        // (sorted for determinism).
        let mut signed_terms: Vec<TermId> = signs
            .nonneg
            .keys()
            .chain(signs.nonpos.keys())
            .copied()
            .collect();
        signed_terms.sort_unstable();
        signed_terms.dedup();

        let mut added = 0;
        for &(lo, hi, order_reason) in orders {
            for &z in &signed_terms {
                let mut key_lo = vec![lo, z];
                key_lo.sort_unstable_by_key(|t| t.0);
                let mut key_hi = vec![hi, z];
                key_hi.sort_unstable_by_key(|t| t.0);
                let (Some(m_lo), Some(m_hi)) = (
                    self.monomials.get(&key_lo).map(|m| m.aux_var),
                    self.monomials.get(&key_hi).map(|m| m.aux_var),
                ) else {
                    continue;
                };
                if m_lo == m_hi {
                    continue;
                }
                // Both directions can apply when z is asserted zero (then
                // lo*z = hi*z = 0 and both cuts are valid).
                for (sign_reason, z_nonneg) in
                    [(signs.nonneg.get(&z), true), (signs.nonpos.get(&z), false)]
                {
                    let Some(&sign_reason) = sign_reason else {
                        continue;
                    };
                    let mut reasons = vec![order_reason, sign_reason];
                    reasons.sort_unstable_by_key(|&(t, v)| (t, v));
                    reasons.dedup();
                    // z >= 0: m_lo - m_hi <= 0 (upper). z <= 0: >= 0 (lower).
                    let is_lower = !z_nonneg;
                    added += self.emit_zero_bound_cut(
                        vec![(m_lo, BigRational::one()), (m_hi, -BigRational::one())],
                        is_lower,
                        &reasons,
                        (m_lo, m_hi, is_lower),
                    );
                }
            }
        }
        added
    }

    /// Family 3: ordered-box product comparison (see module docs).
    ///
    /// For two same-degree registered monomials `p = a1*...*an` and
    /// `q = b1*...*bn`, when the factors admit a bijection with every `ai`
    /// asserted non-negative and every pair identical or asserted `ai <= bi`,
    /// emit `p <= q`. This closes fully-symbolic product upper bounds such as
    /// `x <= xb && y <= yb && 0 <= x && 0 <= y -> x*y <= xb*yb` (upstream
    /// Verus `nonlinear.rs` test1, `lemma_mul_upper_bound`), which family 2
    /// cannot see (no shared factor) and McCormick cannot express (no numeric
    /// bounds).
    fn add_product_pair_order_lemmas(
        &mut self,
        signs: &WeakSigns,
        orders: &[(TermId, TermId, (TermId, bool))],
    ) -> usize {
        if orders.is_empty() || self.monomials.len() < 2 {
            return 0;
        }

        // First asserted reason per (lo, hi) pair, deterministic by
        // assertion order.
        let mut order_reason: BTreeMap<(TermId, TermId), (TermId, bool)> = BTreeMap::new();
        for &(lo, hi, reason) in orders {
            order_reason.entry((lo, hi)).or_insert(reason);
        }

        // Candidates: monomials of degree 2..=4 whose factors are ALL
        // asserted non-negative (the `p` side needs this; using the same
        // filter for `q` costs nothing because `bi >= ai >= 0` is implied,
        // never required as an asserted literal on `q`). Deterministic order
        // via monomials_sorted(). Degree cap keeps the bijection search
        // trivial; the candidate cap keeps the pair loop linear-ish on
        // pathological inputs (the lemmas are optional completeness aids —
        // skipping them is always sound).
        const MAX_DEGREE: usize = 4;
        const MAX_CANDIDATES: usize = 64;
        let all_mons: Vec<(TermId, Vec<TermId>)> = self
            .monomials_sorted()
            .iter()
            .map(|m| (m.aux_var, m.vars.clone()))
            .collect();
        let p_candidates: Vec<&(TermId, Vec<TermId>)> = all_mons
            .iter()
            .filter(|(_, vars)| {
                (2..=MAX_DEGREE).contains(&vars.len())
                    && vars.iter().all(|v| signs.nonneg.contains_key(v))
            })
            .take(MAX_CANDIDATES)
            .collect();
        if p_candidates.is_empty() {
            return 0;
        }

        let mut added = 0;
        for &&(p_aux, ref p_vars) in &p_candidates {
            for &(q_aux, ref q_vars) in &all_mons {
                if p_aux == q_aux || p_vars.len() != q_vars.len() {
                    continue;
                }
                let Some(pair_reasons) = match_ordered_factors(p_vars, q_vars, &order_reason)
                else {
                    continue;
                };
                // Reasons: non-negativity of every p factor + the pairwise
                // order literals (identical pairs contribute none).
                let mut reasons: Vec<(TermId, bool)> = pair_reasons;
                for v in p_vars {
                    if let Some(&r) = signs.nonneg.get(v) {
                        reasons.push(r);
                    }
                }
                reasons.sort_unstable_by_key(|&(t, v)| (t, v));
                reasons.dedup();
                // p - q <= 0. Key (p_aux, q_aux, false) — may coincide with a
                // family-2 monotonicity key for the same pair, but that cut is
                // the *identical* inequality, so the dedup skip is harmless.
                added += self.emit_zero_bound_cut(
                    vec![(p_aux, BigRational::one()), (q_aux, -BigRational::one())],
                    false,
                    &reasons,
                    (p_aux, q_aux, false),
                );
            }
        }
        added
    }

    /// Assert `sum(coeffs) >= 0` (`is_lower`) or `<= 0` into the inner LIA
    /// solver as a reason-carrying cut. `reasons` MUST be non-empty and MUST
    /// jointly entail the cut (each caller above emits only ordered-ring
    /// theorems of its reasons). Dedup-keyed per scope so repeated `check()`
    /// calls do not stack identical bounds.
    fn emit_zero_bound_cut(
        &mut self,
        term_coeffs: Vec<(TermId, BigRational)>,
        is_lower: bool,
        reasons: &[(TermId, bool)],
        dedup_key: (TermId, TermId, bool),
    ) -> usize {
        debug_assert!(!reasons.is_empty(), "zero-bound cuts must carry reasons");
        if reasons.is_empty() || !self.zero_bound_emitted.insert(dedup_key) {
            return 0;
        }
        let source = dedup_key.0;
        let coeffs: Vec<(u32, BigRational)> = term_coeffs
            .into_iter()
            .map(|(t, c)| (self.lia.lra_solver_mut().ensure_var_registered(t), c))
            .collect();
        if self.debug {
            safe_eprintln!(
                "[NIA] zero-bound lemma: {:?} {} 0 (reasons={:?})",
                dedup_key,
                if is_lower { ">=" } else { "<=" },
                reasons
            );
        }
        self.lia.lra_solver_mut().add_gomory_cut(
            &GomoryCut {
                coeffs,
                bound: BigRational::zero(),
                is_lower,
                reasons: reasons.to_vec(),
                source_term: None,
            },
            source,
        );
        1
    }
}

/// Find a bijection pairing each `p` factor with a distinct `q` factor such
/// that the pair is either the identical term (no reason needed) or carries
/// an asserted weak order `p_i <= q_j` (reason recorded). Returns the order
/// reasons of the matched pairs, or `None` when no bijection exists.
///
/// Both factor lists are canonically sorted (monomial keys), and the search
/// tries `q` positions in ascending index order, so the first bijection found
/// is deterministic. Factor lists are length <= `MAX_DEGREE`, so the
/// backtracking search is trivially bounded.
fn match_ordered_factors(
    p_vars: &[TermId],
    q_vars: &[TermId],
    order_reason: &BTreeMap<(TermId, TermId), (TermId, bool)>,
) -> Option<Vec<(TermId, bool)>> {
    fn go(
        i: usize,
        p_vars: &[TermId],
        q_vars: &[TermId],
        used: &mut [bool],
        reasons: &mut Vec<(TermId, bool)>,
        order_reason: &BTreeMap<(TermId, TermId), (TermId, bool)>,
    ) -> bool {
        if i == p_vars.len() {
            return true;
        }
        let a = p_vars[i];
        for (j, &b) in q_vars.iter().enumerate() {
            if used[j] {
                continue;
            }
            let matched_reason = if a == b {
                None
            } else if let Some(&r) = order_reason.get(&(a, b)) {
                Some(r)
            } else {
                continue;
            };
            used[j] = true;
            let reason_len = reasons.len();
            if let Some(r) = matched_reason {
                reasons.push(r);
            }
            if go(i + 1, p_vars, q_vars, used, reasons, order_reason) {
                return true;
            }
            reasons.truncate(reason_len);
            used[j] = false;
        }
        false
    }

    let mut used = vec![false; q_vars.len()];
    let mut reasons = Vec::new();
    if go(0, p_vars, q_vars, &mut used, &mut reasons, order_reason) {
        Some(reasons)
    } else {
        None
    }
}

#[cfg(test)]
#[path = "zero_bound_lemmas_tests.rs"]
mod tests;
