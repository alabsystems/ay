// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The sparse multivariate polynomial manager over `Z` — a port of z3's
//! `src/math/polynomial/polynomial.{h,cpp}` core.
//!
//! # Why this module exists
//!
//! Two modules in this crate already carry an *ad-hoc* multivariate
//! representation, each shaped by the one algorithm it was written for:
//!
//! * [`crate::subresultant::MPolyZ`] — a flat `Vec<(Mono, BigInt)>` under
//!   graded-lex, with `Mono` a freshly allocated `Vec<(var, exp)>` per term.
//!   Monomial equality is a vector compare; every product allocates.
//! * [`crate::mroot`] — reuses `MPolyZ` and then re-derives per-variable
//!   degree, coefficient extraction and specialization on top of it.
//!
//! Neither has pseudo-division, content/primitive-part, a multivariate GCD, or
//! a per-variable square-free decomposition — the four operations every CAD
//! projection operator and every nlsat explanation rule is written in terms of.
//! z3 puts all of them behind one manager so there is exactly one normal form,
//! one monomial order, and one set of invariants. This module is that manager.
//!
//! # 1. Representation
//!
//! Monomials are **interned** in the [`PolyManager`] ([`MonoId`] is a `u32`
//! handle), which is the whole point of having a manager at all:
//!
//! * monomial equality is a `u32` compare, not a vector compare;
//! * a [`Poly`] is `Vec<(MonoId, BigInt)>` in a canonical order, so polynomial
//!   equality is a flat structural compare with no normalization step;
//! * a monomial's exponent vector is stored once no matter how many
//!   polynomials mention it.
//!
//! The canonical order is **graded lex with the HIGHER variable index more
//! significant** ([`PolyManager::cmp_mono`]). Total degree first makes it a
//! genuine monomial order (`m1 < m2  ==>  m*m1 < m*m2`, and `1` is minimal),
//! which is what makes leading-term cancellation in [`PolyManager::exact_div`]
//! terminate. Ranking the higher variable first makes the leading term agree
//! with the recursive `Z[y_1..y_{k-1}][x_k]` view that projection uses.
//!
//! Invariants, enforced by the single normalizing constructor
//! [`PolyManager::mk`] and never bypassed:
//!
//! * terms strictly descending under [`PolyManager::cmp_mono`];
//! * no repeated monomial;
//! * no zero coefficient;
//! * the zero polynomial is the empty term list.
//!
//! # 2. Pseudo-division
//!
//! [`PolyManager::pseudo_division`] is z3's `pseudo_division_core`
//! (`polynomial.cpp:5247`): it returns `(d, Q, R)` with
//!
//! ```text
//!     lc(q, x)^d * p  ==  Q * q + R        and       deg_x(R) < deg_x(q)
//! ```
//!
//! in the `Exact` mode `d` is forced to exactly `deg_x(p) - deg_x(q) + 1`, and
//! in the `Loose` mode `d` is whatever the loop consumed (`<=` that). This is
//! the operation the whole projection stack sits on: the subresultant PRS, the
//! GCD, and the square-free decomposition are all written against it.
//!
//! One deliberate divergence from z3 is documented at the call site: z3's
//! `deg_B > deg_A` path falls through into the main loop and computes
//! `deg_A - deg_B + 1` in `unsigned`, which underflows. It is unreachable from
//! z3's own callers (which maintain `deg_A >= deg_B`); here it returns the
//! mathematically correct `d = 0, Q = 0, R = p`.
//!
//! # 3. GCD — two implementations, one of them modular
//!
//! * [`PolyManager::gcd`] is z3's `gcd_prs` (`polynomial.cpp:3891`): the
//!   primitive/subresultant polynomial remainder sequence, recursing on the
//!   content so that a `k`-variate GCD becomes a chain of `(k-1)`-variate ones.
//!   Straightforward and always correct; its intermediate coefficients grow.
//! * [`PolyManager::mod_gcd`] is z3's `mod_gcd` (`polynomial.cpp:4577`):
//!   Brown's modular algorithm. Images are taken in `Z_p` for a sequence of
//!   31-bit primes; inside each prime the non-main variables are eliminated by
//!   evaluation and recovered by dense **Newton interpolation**
//!   (`polynomial.cpp:3142`); the images are lifted to `Z` by CRA. Every
//!   candidate is gated by an **exact-division certificate** — it is returned
//!   only once it has been shown to divide both inputs — so a wrong image
//!   cannot produce a wrong answer, only a `None`.
//!
//! `mod_gcd` is *not* the default: [`PolyManager::gcd`] stays on the PRS. The
//! modular path is offered separately and cross-validated against the PRS in
//! `ay-nra-oracle`, and the coefficient growth of the two is MEASURED rather
//! than assumed (see [`PolyManager::max_coeff_bits`]).
//!
//! # 4. Square-free decomposition
//!
//! [`PolyManager::square_free_in`] (z3 `square_free(p, x)`) and
//! [`PolyManager::square_free`] (z3's recursive whole-polynomial version).
//! Both are `p / gcd(p, dp/dx)`, so they inherit whatever the GCD guarantees —
//! which is why the GCD is the item that had to be built properly.
//!
//! # Fail-closed
//!
//! Exact arithmetic only: `BigInt` coefficients, `u32` exponents, and `u64`
//! residues in the modular layer. There is no floating point anywhere in this
//! file. Every partial operation returns `Option` and every degenerate input is
//! answered explicitly rather than by convention:
//!
//! | input | answer |
//! |---|---|
//! | `exact_div(p, 0)` | `None` |
//! | `exact_div(p, q)` with `q` not dividing `p` | `None` |
//! | `pseudo_division(p, 0, x)` | `None` |
//! | `iccp(0, x)` | `(0, 1, 0)` |
//! | `gcd(0, 0)` | `0` |
//! | `square_free(0)` | `0` |
//! | `mod_gcd` out of primes / points | `None` (never a guess) |
//! | polynomial with no variables | handled as a constant at every entry |
//!
//! # What is NOT ported, and why
//!
//! This module is `polynomial.cpp`'s CORE, not all of it. Deliberately absent:
//!
//! * **Sparse interpolation** (`skeleton`, `sparse_interpolator`,
//!   `polynomial.cpp:3405`). Only the DENSE Newton interpolator is here. Sparse
//!   interpolation is a cache: it reuses the monomial support discovered on the
//!   previous prime to cut the number of sample points. It changes cost, never
//!   answers, and it is only worth having once the dense path has campaign
//!   hours behind it.
//! * **Multivariate factorization** (`factor`), `compose`, `translate`,
//!   `rename`, `polynomial_cache`, `gcd_simplify`. None of them are on the
//!   projection path this port exists to serve.
//! * **`mod_d` / `exact_pseudo_division_mod_d`** — z3's degree-truncated
//!   arithmetic, used only by its Groebner-style simplifier.
//! * z3's `som_buffer` fused arithmetic. [`PolyManager::pseudo_division`] works
//!   on the recursive coefficient view instead: identical ring operations,
//!   more temporaries, degree bookkeeping that can be checked by eye.
//!
//! # Measured status of the modular GCD
//!
//! Over 93,000 mixed oracle cases (seeds 7/23/41), [`PolyManager::mod_gcd`]
//! DECLINED on 322 of 1,428 `pm-mod-gcd` cases at seed 41 — about 23% — and
//! agreed with [`PolyManager::gcd`] on every case it did certify, with zero
//! divergences. A decline is `None`, never a wrong answer. That decline rate is
//! the reason [`PolyManager::gcd`] is still the PRS: the modular path is
//! correct where it answers and not yet complete enough to be the default.
//!
//! # Not wired in
//!
//! Nothing in the solve path calls this module. It cannot change a verdict.

use hashbrown::HashMap;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

// ============================================================================
// Interned monomials
// ============================================================================

/// A variable index. Deliberately *not* `TermId`: this layer is pure algebra
/// and stays independent of the term store, exactly as
/// [`crate::subresultant::MVar`] does.
pub(crate) type PVar = u32;

/// Handle to a monomial interned in a [`PolyManager`].
///
/// Two monomials of the same manager are equal **iff** their `MonoId`s are
/// equal — that is the property the whole representation is built to buy.
/// Handles from different managers are meaningless together; every entry point
/// that could mix them takes `&self`/`&mut self`, so the type system keeps
/// them apart in practice.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) struct MonoId(u32);

/// The stored form of a monomial.
#[derive(Clone, Debug, PartialEq, Eq)]
struct MonoData {
    /// `(variable, exponent)` strictly ascending by variable, every exponent
    /// non-zero. The empty vector is the constant monomial `1`.
    pows: Vec<(PVar, u32)>,
    /// Cached total degree; recomputing it is the inner loop of the order.
    total_degree: u32,
}

/// A sparse multivariate polynomial over `Z`.
///
/// Always in the canonical form described in the module docs. `PartialEq` is
/// therefore semantic equality *within one manager*, at the cost of a flat
/// slice compare.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) struct Poly {
    /// `(monomial, coefficient)` strictly DESCENDING under
    /// [`PolyManager::cmp_mono`]; every coefficient non-zero.
    terms: Vec<(MonoId, BigInt)>,
}

impl Poly {
    /// The zero polynomial.
    pub(crate) fn zero() -> Self {
        Self { terms: Vec::new() }
    }

    /// Whether this is the zero polynomial.
    pub(crate) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Number of non-zero terms.
    pub(crate) fn len(&self) -> usize {
        self.terms.len()
    }

    /// The canonical term list.
    pub(crate) fn terms(&self) -> &[(MonoId, BigInt)] {
        &self.terms
    }
}

/// Which pseudo-division variant to run (z3's `Exact_d` template parameter).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum PseudoMode {
    /// `d` is forced to `deg_x(p) - deg_x(q) + 1` by multiplying the result
    /// through by the missing power of `lc(q, x)`. This is z3's
    /// `exact_pseudo_division`, and it is what the subresultant PRS needs
    /// because the recurrence's exponents assume that exact power.
    Exact,
    /// `d` is whatever the cancellation loop consumed. Smaller coefficients,
    /// but the identity holds with a `d` the caller must read back.
    Loose,
}

/// The result of a pseudo-division: `lc(q, x)^d * p == quot * q + rem`.
#[derive(Clone, Debug)]
pub(crate) struct PseudoDiv {
    /// The power of `lc(q, x)` the identity carries.
    pub(crate) d: u32,
    /// The pseudo-quotient.
    pub(crate) quot: Poly,
    /// The pseudo-remainder, with `deg_x(rem) < deg_x(q)`.
    pub(crate) rem: Poly,
}

// ============================================================================
// Modular-GCD decline diagnosis
// ============================================================================

/// Why one [`PolyManager::mod_gcd`] attempt gave up, counted at every site that
/// can produce a `None`.
///
/// PURELY OBSERVATIONAL. Nothing in [`PolyManager::mod_gcd`] or
/// [`PolyManager::mod_gcd_rec`] ever reads a field of this struct, so it cannot
/// enter the decision path; the only writes are `+= 1` and the final
/// `certified` flag. That property is the whole reason the counters live in a
/// separate struct rather than as loose locals threaded through the recursion.
///
/// It exists because "the modular path declines on 3 of 5 multivariate shapes"
/// was a measured fact with no attached cause, and a fix aimed at the wrong
/// cause is worse than no fix. Every field below is a distinct mechanism.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ModGcdDiag {
    /// Primes actually entered (i.e. not skipped before the recursion).
    pub(crate) primes_used: u32,
    /// Primes rejected because a coefficient of `u` or `v` vanished mod `p`.
    pub(crate) prime_bad_coeff: u32,
    /// Primes rejected because `lc_g` vanished mod `p`.
    pub(crate) prime_bad_lcg: u32,
    /// Primes whose top-level Brown recursion declined outright.
    pub(crate) prime_rec_declined: u32,
    /// CRA steps that could not be combined (`modulus` not invertible mod `p`).
    pub(crate) cra_failed: u32,
    /// Images discarded because a strictly smaller leading monomial appeared
    /// (every earlier prime was unlucky) or was larger (this prime is unlucky).
    pub(crate) img_reset_smaller: u32,
    pub(crate) img_skipped_larger: u32,
    /// Rounds where the reconstructed candidate's leading coefficient did not
    /// divide `lc_g` — CRA has not stabilized yet.
    pub(crate) lc_gate_rejected: u32,
    /// Rounds where the EXACT certificate ran and rejected, per leg.
    pub(crate) cert_reject_u: u32,
    pub(crate) cert_reject_v: u32,
    /// Rounds where the certificate ran and accepted.
    pub(crate) cert_accepted: u32,
    // ---- inside the Z_p recursion (summed over every level and prime) ----
    /// Levels that ran out of evaluation-point budget.
    pub(crate) rec_budget_exhausted: u32,
    /// Levels that exhausted the field (`p` distinct points all used).
    pub(crate) rec_field_exhausted: u32,
    /// Content / lc-gcd / base-case Euclid failures.
    pub(crate) rec_content_failed: u32,
    pub(crate) rec_lcgcd_failed: u32,
    pub(crate) rec_base_failed: u32,
    /// The inner recursion at one evaluation point declined. This used to
    /// abort the whole level; it now discards the point and draws another.
    /// MEASURED: fires 2,480 times across the 871 declining cases in the
    /// pre-fix census. (An earlier draft attributed "155 declines" to this
    /// site; that split does not reproduce — `primary()` tests
    /// `rec_budget_exhausted` first, so all 871 attribute there.)
    pub(crate) rec_inner_declined: u32,
    /// The image at one point could not be made glex-monic (it was zero).
    pub(crate) rec_monic_failed: u32,
    /// Newton interpolation could not be extended (repeated point).
    pub(crate) rec_newton_failed: u32,
    /// Points discarded: `lc_g` vanished there, the image had too high a
    /// degree, the `lc_H == lc_g` gate had not stabilized, or the trial exact
    /// division rejected the interpolant.
    pub(crate) rec_point_lcg_zero: u32,
    pub(crate) rec_unlucky_degree: u32,
    pub(crate) rec_lch_mismatch: u32,
    pub(crate) rec_trialdiv_reject: u32,
    /// Times the accumulated Newton form was DISCARDED because a point
    /// produced a strictly smaller image degree (every earlier point at that
    /// level was unlucky).
    pub(crate) rec_reset_smaller: u32,
    /// The largest number of interpolation points ever accumulated at a single
    /// level, and the largest `deg_bound` any level worked against.
    ///
    /// These two separate "the budget was too small" from "the interpolation
    /// was never going to converge": if the accumulated point count runs far
    /// past `deg_bound + 1` and the trial division still rejects, more budget
    /// is not the fix.
    pub(crate) rec_max_points_at_level: u32,
    pub(crate) rec_max_deg_bound: u32,
    /// Evaluation points consumed in total, across every level and prime.
    pub(crate) rec_points_tried: u32,
    // ---- the ACCEPT sites ----
    //
    // There is deliberately no stored `certified` flag. A verifier proved that
    // a stored one could be hardwired to `true` at the top of `mod_gcd` with
    // ZERO oracle divergences across 4,000 cases — and the headline metric this
    // module is judged on (`0.00% declines`) is read off exactly that flag. So
    // the flag is DERIVED from the four sites that can actually return an
    // answer: an illegal state is now unrepresentable rather than merely
    // detectable. Every one of these is incremented immediately before its
    // `return Some(..)`.
    /// A zero input: `gcd(0, v) == v`.
    pub(crate) shortcut_zero: u32,
    /// A constant input: the answer is the integer content GCD.
    pub(crate) shortcut_const: u32,
    /// The modular image was a unit, so the true GCD is the integer part.
    pub(crate) shortcut_unit_image: u32,
}

impl ModGcdDiag {
    /// The single dominant cause of a decline, as a stable label.
    ///
    /// Ordered so that the most SPECIFIC mechanism wins: a level that ran out
    /// of budget is reported as such even though the prime loop also ran out of
    /// primes afterwards, because "add more primes" is the wrong fix for it.
    /// `certified` short-circuits, so the label is only meaningful on a decline.
    /// Whether the attempt ended in a certified answer — DERIVED from the
    /// accept sites, never stored. See the note on the counters above.
    pub(crate) fn certified(&self) -> bool {
        self.cert_accepted > 0
            || self.shortcut_zero > 0
            || self.shortcut_const > 0
            || self.shortcut_unit_image > 0
    }

    pub(crate) fn primary(&self) -> &'static str {
        if self.certified() {
            return "certified";
        }
        if self.primes_used == 0 {
            if self.prime_bad_coeff > 0 {
                return "every prime divided a coefficient";
            }
            if self.prime_bad_lcg > 0 {
                return "every prime divided lc_g";
            }
            return "no prime entered";
        }
        if self.cert_reject_u > 0 || self.cert_reject_v > 0 {
            return "exact certificate rejected the candidate";
        }
        if self.prime_rec_declined >= self.primes_used {
            // Every prime that ran declined inside the recursion; name the
            // dominant sub-cause.
            if self.rec_budget_exhausted > 0 {
                return "recursion: evaluation-point budget exhausted";
            }
            if self.rec_inner_declined > 0 {
                return "recursion: every evaluation point was refused below";
            }
            if self.rec_base_failed > 0 {
                return "recursion: base-case Euclid refused";
            }
            if self.rec_content_failed > 0 {
                return "recursion: content/pp refused";
            }
            if self.rec_lcgcd_failed > 0 {
                return "recursion: lc gcd refused";
            }
            if self.rec_monic_failed > 0 {
                return "recursion: image was zero";
            }
            if self.rec_field_exhausted > 0 {
                return "recursion: field exhausted";
            }
            if self.rec_newton_failed > 0 {
                return "recursion: newton step refused";
            }
            return "recursion declined, cause unclassified";
        }
        if self.lc_gate_rejected > 0 {
            return "lc gate: CRA never stabilized within the prime list";
        }
        "prime list exhausted before the certificate ran"
    }
}

/// The integer/content/primitive-part split of a polynomial with respect to a
/// variable: `p == i * c * pp` (z3's `iccp`).
#[derive(Clone, Debug)]
pub(crate) struct Iccp {
    /// Integer content, signed so that `pp`'s leading coefficient is positive.
    pub(crate) i: BigInt,
    /// Polynomial content with respect to `x`: the GCD of the coefficients of
    /// the powers of `x`. Free of `x`, with a positive leading coefficient.
    pub(crate) c: Poly,
    /// The primitive part.
    pub(crate) pp: Poly,
}

// ============================================================================
// The manager
// ============================================================================

/// The hash-consed monomial store plus every polynomial operation.
///
/// Operations that can *create* a monomial take `&mut self` (they intern);
/// pure queries take `&self`. That split is not cosmetic — it is what lets the
/// interning table be a plain `HashMap` with no interior mutability and no
/// runtime borrow checking on the hot path.
pub(crate) struct PolyManager {
    monos: Vec<MonoData>,
    index: HashMap<Vec<(PVar, u32)>, MonoId>,
    /// `MonoId` of the constant monomial `1`. Interned at construction so it
    /// is always available to `&self` methods.
    one: MonoId,
    /// Decline counters for the LAST [`PolyManager::mod_gcd`] call. Written
    /// only; never read by the algorithm. See [`ModGcdDiag`].
    diag: ModGcdDiag,
    /// When set, [`PolyManager::gcd`] does NOT try the modular fast path — all
    /// the way down, including the content recursion.
    ///
    /// This exists for the oracle, and it is load-bearing. Four differential
    /// sites compare the modular answer against "the PRS answer"; the moment
    /// `gcd` dispatches to `mod_gcd`, those comparisons compare `mod_gcd`
    /// against itself and the strongest legs in the suite go vacuous. Same for
    /// the `growth` cost tables, whose PRS column would silently start
    /// measuring the modular path. See [`PolyManager::gcd_via_prs`].
    prs_only: bool,
}

impl Default for PolyManager {
    fn default() -> Self {
        Self::new()
    }
}

impl PolyManager {
    /// A fresh manager, with the constant monomial `1` pre-interned.
    pub(crate) fn new() -> Self {
        let mut m = Self {
            monos: Vec::new(),
            index: HashMap::new(),
            one: MonoId(0),
            diag: ModGcdDiag::default(),
            prs_only: false,
        };
        m.one = m.intern(Vec::new());
        m
    }

    /// How many distinct monomials have been interned. Measurement only.
    pub(crate) fn interned(&self) -> usize {
        self.monos.len()
    }

    /// The decline counters recorded by the most recent
    /// [`PolyManager::mod_gcd`] call. Measurement only.
    pub(crate) fn mod_gcd_diag(&self) -> ModGcdDiag {
        self.diag
    }

    // ------------------------------------------------------------------
    // Monomial layer
    // ------------------------------------------------------------------

    /// Intern a *already canonical* exponent vector (ascending by variable,
    /// exponents non-zero).
    fn intern(&mut self, pows: Vec<(PVar, u32)>) -> MonoId {
        debug_assert!(pows.windows(2).all(|w| w[0].0 < w[1].0));
        debug_assert!(pows.iter().all(|&(_, e)| e > 0));
        if let Some(&id) = self.index.get(&pows) {
            return id;
        }
        let total_degree = pows.iter().map(|&(_, e)| e).sum();
        let id = MonoId(u32::try_from(self.monos.len()).expect("monomial table overflow"));
        self.monos.push(MonoData {
            pows: pows.clone(),
            total_degree,
        });
        self.index.insert(pows, id);
        id
    }

    /// The constant monomial `1`.
    pub(crate) fn mono_one(&self) -> MonoId {
        self.one
    }

    /// Intern an arbitrary `(var, exp)` list: duplicates are merged by adding
    /// exponents and zero exponents are dropped.
    pub(crate) fn mk_mono(&mut self, pairs: &[(PVar, u32)]) -> MonoId {
        let mut v: Vec<(PVar, u32)> = pairs.to_vec();
        v.sort_unstable();
        let mut out: Vec<(PVar, u32)> = Vec::with_capacity(v.len());
        for (var, e) in v {
            if e == 0 {
                continue;
            }
            match out.last_mut() {
                Some(last) if last.0 == var => last.1 += e,
                _ => out.push((var, e)),
            }
        }
        self.intern(out)
    }

    /// The exponent vector behind a handle.
    pub(crate) fn mono_pows(&self, m: MonoId) -> &[(PVar, u32)] {
        &self.monos[m.0 as usize].pows
    }

    /// Total degree of a monomial.
    pub(crate) fn mono_total_degree(&self, m: MonoId) -> u32 {
        self.monos[m.0 as usize].total_degree
    }

    /// Degree of `x` in a monomial (`0` when absent).
    pub(crate) fn mono_degree_of(&self, m: MonoId, x: PVar) -> u32 {
        match self.monos[m.0 as usize]
            .pows
            .binary_search_by_key(&x, |&(v, _)| v)
        {
            Ok(i) => self.monos[m.0 as usize].pows[i].1,
            Err(_) => 0,
        }
    }

    /// The canonical monomial order: **graded lex, higher variable index more
    /// significant**.
    ///
    /// Total degree dominates, so `1` is the unique minimum and the order is
    /// multiplicative — both required for [`PolyManager::exact_div`] to
    /// terminate. The tie-break scans variables from the highest index down,
    /// which is what makes the leading term of a `Poly` agree with the leading
    /// term of its recursive `...[x_max]` view.
    pub(crate) fn cmp_mono(&self, a: MonoId, b: MonoId) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        let da = &self.monos[a.0 as usize];
        let db = &self.monos[b.0 as usize];
        match da.total_degree.cmp(&db.total_degree) {
            Ordering::Equal => {}
            other => return other,
        }
        let (mut i, mut j) = (da.pows.len(), db.pows.len());
        loop {
            match (i, j) {
                (0, 0) => return Ordering::Equal,
                // `a` has run out of variables while `b` still carries one at a
                // higher index: `b` is larger.
                (0, _) => return Ordering::Less,
                (_, 0) => return Ordering::Greater,
                _ => {}
            }
            let (va, ea) = da.pows[i - 1];
            let (vb, eb) = db.pows[j - 1];
            if va != vb {
                return va.cmp(&vb);
            }
            if ea != eb {
                return ea.cmp(&eb);
            }
            i -= 1;
            j -= 1;
        }
    }

    /// Product of two monomials.
    pub(crate) fn mono_mul(&mut self, a: MonoId, b: MonoId) -> MonoId {
        let pa = self.monos[a.0 as usize].pows.clone();
        let pb = &self.monos[b.0 as usize].pows;
        let mut out: Vec<(PVar, u32)> = Vec::with_capacity(pa.len() + pb.len());
        let (mut i, mut j) = (0usize, 0usize);
        while i < pa.len() || j < pb.len() {
            match (pa.get(i), pb.get(j)) {
                (Some(&(va, ea)), Some(&(vb, eb))) => match va.cmp(&vb) {
                    Ordering::Less => {
                        out.push((va, ea));
                        i += 1;
                    }
                    Ordering::Greater => {
                        out.push((vb, eb));
                        j += 1;
                    }
                    Ordering::Equal => {
                        out.push((va, ea + eb));
                        i += 1;
                        j += 1;
                    }
                },
                (Some(&t), None) => {
                    out.push(t);
                    i += 1;
                }
                (None, Some(&t)) => {
                    out.push(t);
                    j += 1;
                }
                (None, None) => unreachable!("loop guard"),
            }
        }
        self.intern(out)
    }

    /// `m / x^k`, or `None` when `x` does not occur to at least the power `k`.
    pub(crate) fn mono_div_x_k(&mut self, m: MonoId, x: PVar, k: u32) -> Option<MonoId> {
        if k == 0 {
            return Some(m);
        }
        let mut pows = self.monos[m.0 as usize].pows.clone();
        let i = pows.binary_search_by_key(&x, |&(v, _)| v).ok()?;
        if pows[i].1 < k {
            return None;
        }
        pows[i].1 -= k;
        if pows[i].1 == 0 {
            pows.remove(i);
        }
        Some(self.intern(pows))
    }

    /// Exact monomial division, or `None` when `b` does not divide `a`.
    pub(crate) fn mono_exact_div(&mut self, a: MonoId, b: MonoId) -> Option<MonoId> {
        if b == self.one {
            return Some(a);
        }
        let pa = self.monos[a.0 as usize].pows.clone();
        let pb = self.monos[b.0 as usize].pows.clone();
        let mut out: Vec<(PVar, u32)> = Vec::with_capacity(pa.len());
        let mut i = 0usize;
        for &(vb, eb) in &pb {
            while i < pa.len() && pa[i].0 < vb {
                out.push(pa[i]);
                i += 1;
            }
            let (va, ea) = *pa.get(i)?;
            if va != vb || ea < eb {
                return None;
            }
            if ea > eb {
                out.push((va, ea - eb));
            }
            i += 1;
        }
        out.extend_from_slice(&pa[i..]);
        Some(self.intern(out))
    }

    // ------------------------------------------------------------------
    // Polynomial construction
    // ------------------------------------------------------------------

    /// The single normalizing constructor. Every `Poly` in the system comes
    /// from here (or from a `Poly` that did), which is why the canonical-form
    /// invariants hold without any operation re-establishing them by hand.
    pub(crate) fn mk(&self, terms: Vec<(MonoId, BigInt)>) -> Poly {
        let mut ts = terms;
        ts.retain(|(_, c)| !c.is_zero());
        ts.sort_by(|a, b| self.cmp_mono(b.0, a.0));
        let mut out: Vec<(MonoId, BigInt)> = Vec::with_capacity(ts.len());
        for (m, c) in ts {
            match out.last_mut() {
                Some(last) if last.0 == m => {
                    last.1 += c;
                    if last.1.is_zero() {
                        out.pop();
                    }
                }
                _ => out.push((m, c)),
            }
        }
        Poly { terms: out }
    }

    /// The zero polynomial.
    pub(crate) fn zero(&self) -> Poly {
        Poly::zero()
    }

    /// A constant polynomial.
    pub(crate) fn mk_const(&self, c: BigInt) -> Poly {
        if c.is_zero() {
            Poly::zero()
        } else {
            Poly {
                terms: vec![(self.one, c)],
            }
        }
    }

    /// The polynomial `1`.
    pub(crate) fn one(&self) -> Poly {
        self.mk_const(BigInt::one())
    }

    /// `c * x^k`.
    pub(crate) fn mk_var_pow(&mut self, x: PVar, k: u32, c: BigInt) -> Poly {
        if c.is_zero() {
            return Poly::zero();
        }
        let m = self.mk_mono(&[(x, k)]);
        Poly {
            terms: vec![(m, c)],
        }
    }

    /// Build from `(exponent list, coefficient)` pairs in any order.
    pub(crate) fn mk_from_pairs(&mut self, terms: &[(Vec<(PVar, u32)>, BigInt)]) -> Poly {
        let mut ts = Vec::with_capacity(terms.len());
        for (pows, c) in terms {
            if c.is_zero() {
                continue;
            }
            let m = self.mk_mono(pows);
            ts.push((m, c.clone()));
        }
        self.mk(ts)
    }

    // ------------------------------------------------------------------
    // Queries
    // ------------------------------------------------------------------

    /// Whether `p` has no variables (including the zero polynomial).
    pub(crate) fn is_const(&self, p: &Poly) -> bool {
        p.terms.is_empty() || (p.terms.len() == 1 && p.terms[0].0 == self.one)
    }

    /// The constant value of `p`, or `None` when `p` has a variable.
    pub(crate) fn const_value(&self, p: &Poly) -> Option<BigInt> {
        if p.terms.is_empty() {
            return Some(BigInt::zero());
        }
        if p.terms.len() == 1 && p.terms[0].0 == self.one {
            return Some(p.terms[0].1.clone());
        }
        None
    }

    /// The largest variable index occurring in `p`, or `None` when `p` is
    /// constant. (z3's `max_var`.)
    pub(crate) fn max_var(&self, p: &Poly) -> Option<PVar> {
        let mut best: Option<PVar> = None;
        for &(m, _) in &p.terms {
            if let Some(&(v, _)) = self.monos[m.0 as usize].pows.last() {
                best = Some(match best {
                    Some(b) if b >= v => b,
                    _ => v,
                });
            }
        }
        best
    }

    /// Every variable occurring in `p`, ascending.
    pub(crate) fn vars(&self, p: &Poly) -> Vec<PVar> {
        let mut out: Vec<PVar> = Vec::new();
        for &(m, _) in &p.terms {
            for &(v, _) in &self.monos[m.0 as usize].pows {
                out.push(v);
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// `deg_x(p)`. The zero polynomial and any `p` free of `x` have degree `0`;
    /// callers that must distinguish "degree 0" from "absent" ask
    /// [`Poly::is_zero`] first, exactly as z3 does.
    pub(crate) fn degree(&self, p: &Poly, x: PVar) -> u32 {
        p.terms
            .iter()
            .map(|&(m, _)| self.mono_degree_of(m, x))
            .max()
            .unwrap_or(0)
    }

    /// Total degree of `p` (`0` for the zero polynomial).
    pub(crate) fn total_degree(&self, p: &Poly) -> u32 {
        // Terms are graded-lex descending, so the head has maximal total degree.
        p.terms
            .first()
            .map(|&(m, _)| self.mono_total_degree(m))
            .unwrap_or(0)
    }

    /// The coefficient of `x^k` in `p`, as a polynomial in the other
    /// variables. (z3's `coeff(p, x, k)`.)
    pub(crate) fn coeff(&mut self, p: &Poly, x: PVar, k: u32) -> Poly {
        let mut ts = Vec::new();
        for &(m, ref c) in &p.terms {
            if self.mono_degree_of(m, x) == k {
                let m2 = self
                    .mono_div_x_k(m, x, k)
                    .expect("degree_of(m, x) == k implies x^k divides m");
                ts.push((m2, c.clone()));
            }
        }
        self.mk(ts)
    }

    /// The full recursive view of `p` in `x`: index `i` is the coefficient of
    /// `x^i`, and the vector has length `deg_x(p) + 1` (empty for `p == 0`).
    pub(crate) fn x_coeffs(&mut self, p: &Poly, x: PVar) -> Vec<Poly> {
        if p.is_zero() {
            return Vec::new();
        }
        let d = self.degree(p, x);
        let mut buckets: Vec<Vec<(MonoId, BigInt)>> = vec![Vec::new(); d as usize + 1];
        for &(m, ref c) in &p.terms {
            let k = self.mono_degree_of(m, x);
            let m2 = self
                .mono_div_x_k(m, x, k)
                .expect("k is the degree of x in m");
            buckets[k as usize].push((m2, c.clone()));
        }
        buckets.into_iter().map(|b| self.mk(b)).collect()
    }

    /// Rebuild a polynomial from its recursive view in `x` (the inverse of
    /// [`PolyManager::x_coeffs`]).
    pub(crate) fn from_x_coeffs(&mut self, x: PVar, coeffs: &[Poly]) -> Poly {
        let mut ts: Vec<(MonoId, BigInt)> = Vec::new();
        for (k, c) in coeffs.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let xk = self.mk_mono(&[(x, u32::try_from(k).expect("degree fits in u32"))]);
            for &(m, ref a) in &c.terms {
                let m2 = self.mono_mul(m, xk);
                ts.push((m2, a.clone()));
            }
        }
        self.mk(ts)
    }

    /// `lc(p, x)` — the coefficient of `x^{deg_x(p)}`. The zero polynomial has
    /// leading coefficient zero.
    pub(crate) fn lc(&mut self, p: &Poly, x: PVar) -> Poly {
        if p.is_zero() {
            return Poly::zero();
        }
        let d = self.degree(p, x);
        self.coeff(p, x, d)
    }

    /// Bit length of the widest coefficient in `p`. Measurement only — this is
    /// how coefficient growth is compared between the PRS and modular GCDs.
    pub(crate) fn max_coeff_bits(&self, p: &Poly) -> u64 {
        p.terms
            .iter()
            .map(|(_, c)| c.magnitude().bits())
            .max()
            .unwrap_or(0)
    }

    // ------------------------------------------------------------------
    // Ring operations
    // ------------------------------------------------------------------

    /// Sum.
    pub(crate) fn add(&self, a: &Poly, b: &Poly) -> Poly {
        let mut ts = a.terms.clone();
        ts.extend_from_slice(&b.terms);
        self.mk(ts)
    }

    /// Additive inverse.
    pub(crate) fn neg(&self, a: &Poly) -> Poly {
        Poly {
            terms: a.terms.iter().map(|(m, c)| (*m, -c)).collect(),
        }
    }

    /// Difference.
    pub(crate) fn sub(&self, a: &Poly, b: &Poly) -> Poly {
        let mut ts = a.terms.clone();
        ts.extend(b.terms.iter().map(|(m, c)| (*m, -c)));
        self.mk(ts)
    }

    /// Product.
    pub(crate) fn mul(&mut self, a: &Poly, b: &Poly) -> Poly {
        if a.is_zero() || b.is_zero() {
            return Poly::zero();
        }
        let mut ts: Vec<(MonoId, BigInt)> = Vec::with_capacity(a.terms.len() * b.terms.len());
        for &(ma, ref ca) in &a.terms {
            for &(mb, ref cb) in &b.terms {
                let m = self.mono_mul(ma, mb);
                ts.push((m, ca * cb));
            }
        }
        self.mk(ts)
    }

    /// Multiply by an integer.
    pub(crate) fn mul_int(&self, a: &Poly, c: &BigInt) -> Poly {
        if c.is_zero() {
            return Poly::zero();
        }
        Poly {
            terms: a.terms.iter().map(|(m, x)| (*m, x * c)).collect(),
        }
    }

    /// `a^k`, by square-and-multiply. `k == 0` yields `1`.
    pub(crate) fn pow(&mut self, a: &Poly, k: u32) -> Poly {
        let mut acc = self.one();
        let mut base = a.clone();
        let mut e = k;
        while e > 0 {
            if e & 1 == 1 {
                acc = self.mul(&acc, &base);
            }
            e >>= 1;
            if e > 0 {
                base = self.mul(&base, &base);
            }
        }
        acc
    }

    /// `dp/dx`.
    pub(crate) fn derivative(&mut self, p: &Poly, x: PVar) -> Poly {
        let mut ts = Vec::new();
        for &(m, ref c) in &p.terms {
            let k = self.mono_degree_of(m, x);
            if k == 0 {
                continue;
            }
            let m2 = self.mono_div_x_k(m, x, 1).expect("k >= 1");
            ts.push((m2, c * BigInt::from(k)));
        }
        self.mk(ts)
    }

    /// Substitute an integer for `x`.
    pub(crate) fn eval_var(&mut self, p: &Poly, x: PVar, a: &BigInt) -> Poly {
        let mut ts = Vec::new();
        for &(m, ref c) in &p.terms {
            let k = self.mono_degree_of(m, x);
            if k == 0 {
                ts.push((m, c.clone()));
                continue;
            }
            let m2 = self.mono_div_x_k(m, x, k).expect("k is the degree of x");
            ts.push((m2, c * a.pow(k)));
        }
        self.mk(ts)
    }

    /// Exact polynomial division: `Some(q)` with `q * b == a`, or `None` when
    /// no such polynomial over `Z` exists (including `b == 0`).
    ///
    /// Repeated leading-term cancellation under the graded-lex order. Each
    /// iteration strictly lowers the remainder's leading monomial in a
    /// well-order, so it terminates; integer divisibility is enforced at every
    /// step, so `(2x) / 4` refuses rather than silently producing a rational.
    pub(crate) fn exact_div(&mut self, a: &Poly, b: &Poly) -> Option<Poly> {
        let (dm, dc) = b.terms.first().cloned()?;
        if a.is_zero() {
            return Some(Poly::zero());
        }
        let mut rem = a.clone();
        let mut quot: Vec<(MonoId, BigInt)> = Vec::new();
        while let Some((rm, rc)) = rem.terms.first().cloned() {
            let qm = self.mono_exact_div(rm, dm)?;
            if !(&rc % &dc).is_zero() {
                return None;
            }
            let qc = &rc / &dc;
            let t = Poly {
                terms: vec![(qm, qc)],
            };
            quot.extend_from_slice(&t.terms);
            let prod = self.mul(&t, b);
            rem = self.sub(&rem, &prod);
        }
        Some(self.mk(quot))
    }

    /// Whether `b` divides `a` exactly.
    pub(crate) fn divides(&mut self, b: &Poly, a: &Poly) -> bool {
        self.exact_div(a, b).is_some()
    }

    /// Exact division by an integer.
    pub(crate) fn exact_div_int(&self, a: &Poly, c: &BigInt) -> Option<Poly> {
        if c.is_zero() {
            return None;
        }
        let mut ts = Vec::with_capacity(a.terms.len());
        for (m, x) in &a.terms {
            if !(x % c).is_zero() {
                return None;
            }
            ts.push((*m, x / c));
        }
        Some(Poly { terms: ts })
    }

    // ------------------------------------------------------------------
    // Content and primitive part
    // ------------------------------------------------------------------

    /// The integer content: the positive GCD of the coefficients (`0` for the
    /// zero polynomial).
    pub(crate) fn int_content(&self, p: &Poly) -> BigInt {
        let mut g = BigInt::zero();
        for (_, c) in &p.terms {
            g = g.gcd(c);
            if g.is_one() {
                break;
            }
        }
        g
    }

    /// z3's `ic`: split `p == i * pp` with `pp` integer-primitive and with a
    /// POSITIVE leading coefficient. `i` carries the sign.
    pub(crate) fn ic(&self, p: &Poly) -> (BigInt, Poly) {
        if p.is_zero() {
            return (BigInt::zero(), Poly::zero());
        }
        let mut i = self.int_content(p);
        if p.terms[0].1.is_negative() {
            i = -i;
        }
        let pp = self
            .exact_div_int(p, &i)
            .expect("the integer content divides every coefficient");
        (i, pp)
    }

    /// Negate `p` when its leading coefficient is negative (z3's
    /// `flip_sign_if_lm_neg`). Used to pin down the unit ambiguity in every
    /// GCD, so that two runs that agree mathematically also agree bit for bit.
    pub(crate) fn flip_sign_if_lm_neg(&self, p: &Poly) -> Poly {
        match p.terms.first() {
            Some((_, c)) if c.is_negative() => self.neg(p),
            _ => p.clone(),
        }
    }

    /// z3's `iccp(p, x)`: `p == i * c * pp` where `c` is the content with
    /// respect to `x` and `pp` the primitive part.
    ///
    /// Degenerate inputs are answered explicitly: the zero polynomial gives
    /// `(0, 1, 0)`, a constant gives `(value, 1, 1)`, and a polynomial free of
    /// `x` gives `(int content, integer-primitive part, 1)`.
    pub(crate) fn iccp(&mut self, p: &Poly, x: PVar) -> Option<Iccp> {
        if p.is_zero() {
            return Some(Iccp {
                i: BigInt::zero(),
                c: self.one(),
                pp: Poly::zero(),
            });
        }
        if self.is_const(p) {
            return Some(Iccp {
                i: p.terms[0].1.clone(),
                c: self.one(),
                pp: self.one(),
            });
        }
        let d = self.degree(p, x);
        let (i, pp0) = self.ic(p);
        if d == 0 {
            return Some(Iccp {
                i,
                c: pp0,
                pp: self.one(),
            });
        }
        let mut c = Poly::zero();
        for k in 0..=d {
            let ck = self.coeff(&pp0, x, k);
            if ck.is_zero() {
                continue;
            }
            c = self.gcd(&c, &ck)?;
            if self.is_const(&c) {
                c = self.one();
                break;
            }
        }
        if c.is_zero() {
            // Unreachable for a non-zero `p`, but never guess: refuse instead.
            return None;
        }
        let c = self.flip_sign_if_lm_neg(&c);
        let pp = self.exact_div(&pp0, &c)?;
        Some(Iccp { i, c, pp })
    }

    /// The primitive part of `p` with respect to `x`.
    pub(crate) fn primitive(&mut self, p: &Poly, x: PVar) -> Option<Poly> {
        Some(self.iccp(p, x)?.pp)
    }

    /// The content of `p` with respect to `x`.
    pub(crate) fn content(&mut self, p: &Poly, x: PVar) -> Option<Poly> {
        Some(self.iccp(p, x)?.c)
    }

    // ------------------------------------------------------------------
    // Pseudo-division  (z3 `pseudo_division_core`, polynomial.cpp:5247)
    // ------------------------------------------------------------------

    /// Pseudo-division of `p` by `q` with respect to `x`.
    ///
    /// Returns `(d, Q, R)` satisfying
    ///
    /// ```text
    ///     lc(q, x)^d * p  ==  Q * q + R          deg_x(R) < deg_x(q)
    /// ```
    ///
    /// `None` only for `q == 0`, which has no leading coefficient and for which
    /// no `d` makes the identity meaningful.
    ///
    /// The implementation works on the recursive `x`-coefficient view rather
    /// than z3's `som_buffer` fusion. The arithmetic performed is identical —
    /// one `lc(q,x)` multiply of the surviving coefficients and one
    /// `lc(r,x) * reduct(q)` subtraction per cancellation step — but writing it
    /// on the coefficient list makes the degree bookkeeping checkable by eye,
    /// which matters more here than saving the temporaries.
    pub(crate) fn pseudo_division(
        &mut self,
        p: &Poly,
        q: &Poly,
        x: PVar,
        mode: PseudoMode,
    ) -> Option<PseudoDiv> {
        if q.is_zero() {
            return None;
        }
        let deg_a = self.degree(p, x);
        let deg_b = self.degree(q, x);

        if deg_b == 0 {
            // `lc(q, x) == q`. The remainder is zero and the identity reads
            // `q^d * p == Q * q`, i.e. `Q = p * q^{d-1}`.
            let (d, quot) = match mode {
                PseudoMode::Exact => {
                    let d = deg_a + 1;
                    let qpow = self.pow(q, d - 1);
                    (d, self.mul(p, &qpow))
                }
                PseudoMode::Loose => (1, p.clone()),
            };
            return Some(PseudoDiv {
                d,
                quot,
                rem: Poly::zero(),
            });
        }

        if deg_b > deg_a {
            // `lc^0 * p == 0 * q + p`, and `deg_x(p) < deg_x(q)` already holds.
            //
            // DIVERGENCE FROM z3: `pseudo_division_core` does not return here;
            // it falls into the main loop and evaluates `deg_A - deg_B + 1` in
            // `unsigned`, which underflows. Its own callers keep
            // `deg_A >= deg_B` so the path is unreachable there; this manager
            // does not impose that precondition, so it answers correctly.
            return Some(PseudoDiv {
                d: 0,
                quot: Poly::zero(),
                rem: p.clone(),
            });
        }

        let bc = self.x_coeffs(q, x);
        let l_b = bc[deg_b as usize].clone();
        let r_b = &bc[..deg_b as usize];

        let mut r = self.x_coeffs(p, x);
        let mut quot: Vec<Poly> = vec![Poly::zero(); (deg_a - deg_b + 1) as usize];
        let mut d: u32 = 0;

        loop {
            while matches!(r.last(), Some(t) if t.is_zero()) {
                r.pop();
            }
            if r.is_empty() {
                break;
            }
            let deg_r = u32::try_from(r.len() - 1).expect("degree fits in u32");
            if deg_r < deg_b {
                break;
            }
            let l_r = r[deg_r as usize].clone();
            let shift = (deg_r - deg_b) as usize;

            // R <- l_B * R - l_R * x^shift * reduct(B)
            r.pop(); // the x^deg_r coefficient cancels exactly
            for c in r.iter_mut() {
                *c = self.mul(c, &l_b);
            }
            for (j, rbj) in r_b.iter().enumerate() {
                if rbj.is_zero() {
                    continue;
                }
                let t = self.mul(&l_r, rbj);
                r[shift + j] = self.sub(&r[shift + j], &t);
            }

            // Q <- l_B * Q + l_R * x^shift
            for c in quot.iter_mut() {
                *c = self.mul(c, &l_b);
            }
            quot[shift] = self.add(&quot[shift], &l_r);

            d += 1;
        }

        let mut rem = self.from_x_coeffs(x, &r);
        let mut quot_poly = self.from_x_coeffs(x, &quot);

        if mode == PseudoMode::Exact {
            let exact_d = deg_a - deg_b + 1;
            debug_assert!(d <= exact_d);
            if d < exact_d {
                let mult = self.pow(&l_b, exact_d - d);
                rem = self.mul(&rem, &mult);
                quot_poly = self.mul(&quot_poly, &mult);
            }
            d = exact_d;
        }

        Some(PseudoDiv {
            d,
            quot: quot_poly,
            rem,
        })
    }

    /// z3's `exact_pseudo_remainder`.
    pub(crate) fn pseudo_rem(&mut self, p: &Poly, q: &Poly, x: PVar) -> Option<Poly> {
        Some(self.pseudo_division(p, q, x, PseudoMode::Exact)?.rem)
    }

    // ------------------------------------------------------------------
    // GCD — subresultant PRS  (z3 `gcd_prs`, polynomial.cpp:3891)
    // ------------------------------------------------------------------

    /// The GCD of `u` and `v` over `Z`, normalized to a positive leading
    /// coefficient.
    ///
    /// Dispatches exactly as z3 does: the zero, equal and constant cases are
    /// answered directly, and everything else goes to the primitive PRS on the
    /// largest variable of either input.
    ///
    /// `gcd(0, 0) == 0`. Every other answer is a non-zero polynomial.
    pub(crate) fn gcd(&mut self, u: &Poly, v: &Poly) -> Option<Poly> {
        if u.is_zero() {
            return Some(self.flip_sign_if_lm_neg(v));
        }
        if v.is_zero() {
            return Some(self.flip_sign_if_lm_neg(u));
        }
        if u == v {
            return Some(self.flip_sign_if_lm_neg(u));
        }
        if self.is_const(u) || self.is_const(v) {
            let iu = self.int_content(u);
            let iv = self.int_content(v);
            return Some(self.mk_const(iu.gcd(&iv)));
        }
        // The modular fast path first. It is CERTIFIED — it returns `Some` only
        // after proving the answer divides both inputs exactly — so preferring
        // it cannot change an answer, only the time taken to reach it. A
        // decline falls through to the PRS below, which is what happened on
        // every input before the `Z_p[x]` content fix.
        //
        // MEASURED on `3var deg5 wide coeffs`: 19,884 ms through the PRS
        // against 334 us through here.
        if !self.prs_only {
            if let Some(g) = self.mod_gcd(u, v) {
                return Some(g);
            }
        }
        let xu = self.max_var(u).expect("non-constant");
        let xv = self.max_var(v).expect("non-constant");
        let x = xu.max(xv);
        self.gcd_prs(u, v, x)
    }

    /// The subresultant PRS answer, with the modular fast path disabled ALL THE
    /// WAY DOWN — the content recursion inside `gcd_prs` and `iccp` re-enters
    /// [`PolyManager::gcd`], so a one-level flag would not be enough.
    ///
    /// Every differential check that wants an INDEPENDENT second opinion on
    /// `mod_gcd` must call this rather than `gcd`, and so must every cost
    /// measurement that reports a "PRS" column. Comparing `mod_gcd` against a
    /// `gcd` that dispatches to `mod_gcd` is not a comparison.
    pub(crate) fn gcd_via_prs(&mut self, u: &Poly, v: &Poly) -> Option<Poly> {
        let saved = self.prs_only;
        self.prs_only = true;
        let r = self.gcd(u, v);
        self.prs_only = saved;
        r
    }

    /// The primitive subresultant PRS, recursing on the content.
    ///
    /// Termination is by variable index, not by degree: `x` is the largest
    /// variable of either input, so every recursive [`PolyManager::gcd`] call
    /// (on contents, and inside [`PolyManager::iccp`] on `x`-coefficients)
    /// sees polynomials whose largest variable is strictly smaller.
    fn gcd_prs(&mut self, u: &Poly, v: &Poly, x: PVar) -> Option<Poly> {
        let (u, v) = if self.degree(u, x) < self.degree(v, x) {
            (v, u)
        } else {
            (u, v)
        };
        let iu = self.iccp(u, x)?;
        let iv = self.iccp(v, x)?;
        let d_r = self.gcd(&iu.c, &iv.c)?;
        let d_a = iu.i.gcd(&iv.i);

        let mut pp_u = iu.pp;
        let mut pp_v = iv.pp;
        let mut g = self.one();
        let mut h = self.one();

        loop {
            debug_assert!(self.degree(&pp_u, x) >= self.degree(&pp_v, x));
            let delta = self.degree(&pp_u, x) - self.degree(&pp_v, x);
            let rem = self.pseudo_rem(&pp_u, &pp_v, x)?;
            if rem.is_zero() {
                let pv = self.flip_sign_if_lm_neg(&pp_v);
                let r = self.primitive(&pv, x)?;
                let r = self.mul(&r, &d_r);
                return Some(self.mul_int(&r, &d_a));
            }
            if self.is_const(&rem) {
                let r = self.mul_int(&d_r, &d_a);
                return Some(self.flip_sign_if_lm_neg(&r));
            }
            pp_u = pp_v;
            // pp_v <- rem / (g * h^delta)
            let mut next = self.exact_div(&rem, &g)?;
            for _ in 0..delta {
                next = self.exact_div(&next, &h)?;
            }
            pp_v = next;
            g = self.lc(&pp_u, x);
            // h <- h^{1-delta} * g^{delta}
            let mut new_h = self.one();
            for _ in 0..delta {
                new_h = self.mul(&new_h, &g);
            }
            if delta > 1 {
                for _ in 0..delta - 1 {
                    new_h = self.exact_div(&new_h, &h)?;
                }
            }
            h = new_h;
        }
    }

    // ------------------------------------------------------------------
    // Square-free decomposition  (z3 `square_free`, polynomial.cpp:4872/4913)
    // ------------------------------------------------------------------

    /// The square-free part of `p` with respect to `x`: `p / gcd(p, dp/dx)`.
    ///
    /// `square_free_in(0, x) == 0`, and a `p` free of `x` is returned
    /// unchanged (its derivative is zero, so the GCD is `p` itself and z3's
    /// `is_const(g)` test is what keeps that from collapsing to `1`; the
    /// explicit early return below states it rather than relying on it).
    ///
    /// SIGN. The result is `p / g` with `g` the sign-normalized GCD, so when a
    /// repeated factor is actually removed the answer can come back negated
    /// relative to the "obvious" factorization. z3 behaves identically
    /// (`polynomial.cpp:4913`), and it is harmless: the operation is still
    /// idempotent, because an already square-free input takes the
    /// `is_const(g)` branch and is returned untouched. Callers that need a
    /// canonical sign apply [`PolyManager::flip_sign_if_lm_neg`].
    pub(crate) fn square_free_in(&mut self, p: &Poly, x: PVar) -> Option<Poly> {
        if p.is_zero() || self.is_const(p) {
            return Some(p.clone());
        }
        let dp = self.derivative(p, x);
        if dp.is_zero() {
            // `p` does not mention `x`; there is no square in `x` to remove.
            return Some(p.clone());
        }
        let g = self.gcd(p, &dp)?;
        if self.is_const(&g) {
            Some(p.clone())
        } else {
            self.exact_div(p, &g)
        }
    }

    /// Whether `p` is already square-free with respect to `x`.
    pub(crate) fn is_square_free_in(&mut self, p: &Poly, x: PVar) -> Option<bool> {
        let r = self.square_free_in(p, x)?;
        Some(&r == p)
    }

    /// The square-free part of `p` in every variable, z3's recursive
    /// `square_free(p)`: split off the content in the largest variable, recurse
    /// into it, and take the square-free part of the primitive part.
    pub(crate) fn square_free(&mut self, p: &Poly) -> Option<Poly> {
        if p.is_zero() || self.is_const(p) {
            return Some(p.clone());
        }
        let x = self.max_var(p).expect("non-constant");
        let ic = self.iccp(p, x)?;
        let sqf_c = self.square_free(&ic.c)?;
        let pp_prime = self.derivative(&ic.pp, x);
        let g = self.gcd(&ic.pp, &pp_prime)?;
        let pp = if self.is_const(&g) {
            ic.pp
        } else {
            self.exact_div(&ic.pp, &g)?
        };
        let r = self.mul(&sqf_c, &pp);
        Some(self.mul_int(&r, &ic.i))
    }

    // ------------------------------------------------------------------
    // Modular GCD  (z3 `mod_gcd`, polynomial.cpp:4577)
    // ------------------------------------------------------------------

    /// Brown's modular multivariate GCD.
    ///
    /// Returns `Some(g)` only when `g` has been PROVEN to divide both inputs by
    /// exact division; a bad prime, an unlucky evaluation point or an exhausted
    /// budget produces `None`, never a guess. The caller is expected to fall
    /// back to [`PolyManager::gcd`] — which is precisely what z3 does at
    /// `polynomial.cpp:4690`, silently; here the fallback is the caller's
    /// decision so that the failure is observable.
    ///
    /// The certificate is `g | u` and `g | v` plus the maximality argument
    /// Brown's algorithm supplies: the reconstructed candidate's leading
    /// coefficient divides `gcd(lc(u), lc(v))`, which is the same gate z3
    /// applies before accepting an image.
    ///
    /// DISCLOSED, and broader than first stated: the differential oracle cannot
    /// see this certificate at all. Deleting it outright is invisible across
    /// 6,000 cases, and so is deleting only the `pp_v` half — a verifier proved
    /// both. On generated inputs the reconstruction is already correct, so the
    /// certificate never rejects and its absence changes no answer. It is
    /// covered by direct unit tests on
    /// [`PolyManager::certify_mod_gcd_candidate`] instead, which is why that
    /// acceptance test is a named function rather than an inline conjunction.
    ///
    /// AND, SHARPER STILL: the certificate proves `g | u` and `g | v`, which a
    /// candidate that is TOO SMALL also satisfies. Nothing inside this function
    /// can reject one — maximality is not among the things it proves. The
    /// `pm-mod-gcd` and `pm-mod-gcd-diag` oracle checks carry that leg, by
    /// comparing against the independent subresultant PRS answer and against
    /// the planted common factor. A defect injected into the `Z_p[x]` content
    /// split of [`PolyManager::mod_gcd_rec`] produced exactly such a candidate
    /// and was caught at `fuzz --seed 1 --case 19` and `--case 91`; the
    /// certificate accepted it without complaint.
    pub(crate) fn mod_gcd(&mut self, u: &Poly, v: &Poly) -> Option<Poly> {
        self.diag = ModGcdDiag::default();
        if u.is_zero() {
            self.diag.shortcut_zero += 1;
            return Some(self.flip_sign_if_lm_neg(v));
        }
        if v.is_zero() {
            self.diag.shortcut_zero += 1;
            return Some(self.flip_sign_if_lm_neg(u));
        }
        if self.is_const(u) || self.is_const(v) {
            let iu = self.int_content(u);
            let iv = self.int_content(v);
            self.diag.shortcut_const += 1;
            return Some(self.mk_const(iu.gcd(&iv)));
        }

        // The variable order the recursion eliminates in: smallest
        // min-degree first, so the cheap variables are interpolated away
        // before the expensive one becomes the univariate base case.
        let mut all: Vec<PVar> = self.vars(u);
        for x in self.vars(v) {
            if !all.contains(&x) {
                all.push(x);
            }
        }
        let mut keyed: Vec<(u32, PVar)> = all
            .iter()
            .map(|&x| (self.degree(u, x).min(self.degree(v, x)), x))
            .collect();
        keyed.sort_unstable();
        let vars: Vec<PVar> = keyed.iter().map(|&(_, x)| x).collect();
        if vars.is_empty() {
            return None;
        }

        let (ci_u, pp_u) = self.ic(u);
        let (ci_v, pp_v) = self.ic(v);
        let d_a = ci_u.gcd(&ci_v);
        let lc_u = pp_u.terms[0].1.clone();
        let lc_v = pp_v.terms[0].1.clone();
        let lc_g = lc_u.gcd(&lc_v);

        let mut acc: Option<(Poly, BigInt)> = None; // (image, modulus)
        let mut rng = SplitMix::new(0x5EED_5EED_5EED_5EED);

        for &p in ZP_PRIMES.iter() {
            let zp = Zp::new(p);
            let u_zp = self.to_zp(&pp_u, &zp);
            if u_zp.terms.len() != pp_u.terms.len() {
                self.diag.prime_bad_coeff += 1;
                continue; // bad prime: a coefficient vanished
            }
            let v_zp = self.to_zp(&pp_v, &zp);
            if v_zp.terms.len() != pp_v.terms.len() {
                self.diag.prime_bad_coeff += 1;
                continue;
            }
            let lc_g_zp = zp.from_bigint(&lc_g);
            if lc_g_zp == 0 {
                self.diag.prime_bad_lcg += 1;
                continue;
            }

            self.diag.primes_used += 1;
            let img = match self.mod_gcd_rec(&u_zp, &v_zp, &zp, 0, &vars, &mut rng) {
                Some(g) => g,
                None => {
                    self.diag.prime_rec_declined += 1;
                    continue;
                }
            };
            // Impose the leading coefficient so that images from different
            // primes are scaled consistently and CRA is meaningful.
            // A zero image is this PRIME's problem, not the whole attempt's:
            // move to the next prime rather than abandoning the reconstruction.
            let Some(img) = self.zp_glex_monic(&img, &zp) else {
                self.diag.prime_rec_declined += 1;
                continue;
            };
            let img = self.zp_mul_scalar(&img, lc_g_zp, &zp);

            if img.terms.len() == 1 && img.terms[0].0 == self.one {
                // The modular GCD is a unit: the true GCD is the integer part.
                self.diag.shortcut_unit_image += 1;
                return Some(self.mk_const(d_a));
            }

            let p_big = BigInt::from(p);
            acc = Some(match acc.take() {
                None => (self.from_zp_symmetric(&img, &zp), p_big),
                Some((prev, modulus)) => {
                    let prev_head = prev.terms.first().map(|t| t.0);
                    let img_head = img.terms.first().map(|t| t.0);
                    match (prev_head, img_head) {
                        (Some(a), Some(b)) if self.cmp_mono(b, a) == Ordering::Less => {
                            // The new image has a strictly smaller leading
                            // monomial: every earlier prime was unlucky.
                            self.diag.img_reset_smaller += 1;
                            (self.from_zp_symmetric(&img, &zp), p_big)
                        }
                        (Some(a), Some(b)) if self.cmp_mono(b, a) == Ordering::Greater => {
                            // This prime is unlucky; keep what we had.
                            self.diag.img_skipped_larger += 1;
                            (prev, modulus)
                        }
                        _ => {
                            let Some(combined) = self.cra_combine(&prev, &modulus, &img, &zp)
                            else {
                                self.diag.cra_failed += 1;
                                return None;
                            };
                            (combined, modulus * p_big)
                        }
                    }
                }
            });

            let (cand, _) = acc.as_ref().expect("just set");
            let cand = cand.clone();
            if cand.is_zero() {
                continue;
            }
            let cand_lc = cand.terms[0].1.clone();
            if cand_lc.is_zero() || !(&lc_g % &cand_lc).is_zero() {
                self.diag.lc_gate_rejected += 1;
                continue;
            }
            if let Some(g) = self.certify_mod_gcd_candidate(&cand, &pp_u, &pp_v, &d_a) {
                self.diag.cert_accepted += 1;
                return Some(g);
            }
        }
        None
    }

    /// The acceptance certificate for a reconstructed modular candidate: the
    /// candidate is accepted ONLY if it divides both primitive parts exactly.
    ///
    /// Split out of [`PolyManager::mod_gcd`] so that it can be tested directly,
    /// for a specific reason. A verifier proved that deleting this certificate
    /// entirely — and, more sharply, deleting only the `pp_v` HALF of it — is
    /// invisible to the differential oracle across 6,000 cases. That is not
    /// because the certificate is redundant; it is because on generated inputs
    /// the CRA reconstruction is always already correct, so the certificate is
    /// never the thing that rejects. A guard that never fires on the corpus
    /// cannot be covered by that corpus, no matter how large it grows.
    ///
    /// So it is pinned by construction instead: the unit tests hand it a
    /// candidate that divides one side and not the other and require `None`.
    /// Both halves are separate statements below so that deleting either one
    /// fails a test by name.
    fn certify_mod_gcd_candidate(
        &mut self,
        cand: &Poly,
        pp_u: &Poly,
        pp_v: &Poly,
        d_a: &BigInt,
    ) -> Option<Poly> {
        let cand = self.primitive_z(cand)?;
        if !self.divides(&cand, pp_u) {
            self.diag.cert_reject_u += 1;
            return None;
        }
        if !self.divides(&cand, pp_v) {
            self.diag.cert_reject_v += 1;
            return None;
        }
        let r = self.mul_int(&cand, d_a);
        Some(self.flip_sign_if_lm_neg(&r))
    }

    /// Integer-primitive part with a positive leading coefficient.
    fn primitive_z(&mut self, p: &Poly) -> Option<Poly> {
        if p.is_zero() {
            return None;
        }
        let (_, pp) = self.ic(p);
        Some(pp)
    }

    /// The recursion of Brown's algorithm inside one prime field.
    ///
    /// `vars[idx..]` are the live variables, `x = vars[idx]` is the variable
    /// eliminated at this level by evaluation and recovered by Newton
    /// interpolation, and `Y = vars[idx+1..]` is what the recursion below sees.
    /// `vars[vars.len()-1]` is the main variable the base case runs Euclid on.
    ///
    /// # Which content is removed, and why it is `Z_p[x]`
    ///
    /// This level works in `R[Y]` with `R = Z_p[x]`, NOT in `Z_p[Y][x]`. That
    /// choice is forced, and getting it wrong is the defect this lane found:
    ///
    /// The images cannot be interpolated raw, because `gcd` in a field is only
    /// defined up to a scalar and the scalars at different points are
    /// unrelated. The standard remedy imposes a leading coefficient: each image
    /// is made glex-monic in `Y` and then multiplied by `L(a)`, where
    /// `L = gcd_x(lcglex_Y(pp_u), lcglex_Y(pp_v))` lies in `Z_p[x]`. The
    /// interpolant is therefore not `G` but
    ///
    /// ```text
    ///     H = (L / lcglex_Y(G)) * G ,     L / lcglex_Y(G) ∈ Z_p[x]
    /// ```
    ///
    /// and the spurious factor is a polynomial in `x` ALONE. Removing it means
    /// dividing `H` by its content **in `Z_p[x]`** — the GCD of the
    /// coefficients attached to the distinct `Y`-monomials. Removing the
    /// content in `Z_p[Y]` instead (the split
    /// [`PolyManager::zp_content_pp`] computes) removes NOTHING, because the
    /// spurious factor is `Y`-free; the candidate stays a multiple of the true
    /// GCD, the trial division rejects it, and the level burns its entire
    /// evaluation budget and declines. MEASURED before the fix: 315,728 of the
    /// 415,232 trial-division rejects over 871 declining cases would have
    /// divided both primitive parts had the `Z_p[x]` content been removed
    /// instead (`ay-nra-oracle declines --seed 1 --cases 4000`).
    ///
    /// For `H / cont_Y(H)` to be `G` and not a proper divisor of it, `G` must
    /// be primitive in `Y` — so the content split at the TOP of this level is
    /// `cont_Y` as well, and `gcd(u, v) = gcd_x(cont_Y u, cont_Y v) * G` by
    /// Gauss's lemma over the UFD `Z_p[x]`. The two changes stand or fall
    /// together: with only the recovery changed the answer would be
    /// `G / cont_Y(G)`, which still divides both inputs and would therefore
    /// pass the exact certificate while being too small.
    #[allow(clippy::too_many_arguments)]
    fn mod_gcd_rec(
        &mut self,
        u: &ZpPoly,
        v: &ZpPoly,
        zp: &Zp,
        idx: usize,
        vars: &[PVar],
        rng: &mut SplitMix,
    ) -> Option<ZpPoly> {
        if idx + 1 >= vars.len() {
            let r = self.zp_euclid_gcd(u, v, vars[vars.len() - 1], zp);
            if r.is_none() {
                self.diag.rec_base_failed += 1;
            }
            return r;
        }
        let x = vars[idx];

        // Content and primitive part with respect to `Y`, i.e. in `Z_p[x]`.
        //
        // ORACLE-PINNED. Injecting a defect here — keeping the corrected
        // recovery but skipping this split, i.e. `(one, u.clone())` — makes the
        // answer a PROPER DIVISOR of the true GCD. It still divides both inputs,
        // so the exact certificate accepts it; it was caught at
        // `fuzz --seed 1 --case 19` (`pm-mod-gcd`, `modular = x0^3` against
        // `prs = x0^3*x1^2*x2^2 + 4*x0^3*x1*x2^2`) and at
        // `fuzz --seed 1 --case 91` (`pm-mod-gcd-diag`). The two changes in this
        // function stand or fall together.
        let Some((c_u, pp_u)) = self.zp_cont_pp_y(u, x, zp) else {
            self.diag.rec_content_failed += 1;
            return None;
        };
        let Some((c_v, pp_v)) = self.zp_cont_pp_y(v, x, zp) else {
            self.diag.rec_content_failed += 1;
            return None;
        };
        // Both contents are univariate in `x`, so their GCD is one Euclid run —
        // no recursion, which is also why this level got cheaper.
        let Some(c_g) = self.zp_euclid_gcd(&c_u, &c_v, x, zp) else {
            self.diag.rec_content_failed += 1;
            return None;
        };

        // `lc_glex` of each primitive part, as a polynomial in `x` only: the
        // coefficient attached to the glex-maximal monomial in the remaining
        // variables. z3 `lc_glex_ZpX`, polynomial.cpp:4355.
        let lc_u = self.zp_lc_glex_x(&pp_u, x);
        let lc_v = self.zp_lc_glex_x(&pp_v, x);
        let Some(lc_g) = self.zp_euclid_gcd(&lc_u, &lc_v, x, zp) else {
            self.diag.rec_lcgcd_failed += 1;
            return None;
        };

        // `deg_x(H) = deg_x(G) + deg(L) - deg(lcglex_Y(G)) <= deg_bound + deg(L)`,
        // so `deg_bound + deg(L) + 1` points always suffice; the rest of the
        // budget absorbs unlucky points. The old bound omitted `deg(L)`
        // entirely, which is a second reason a level could run out of points.
        let deg_bound = self.zp_degree(&pp_u, x).min(self.zp_degree(&pp_v, x));
        let deg_l = self.zp_degree(&lc_g, x);
        let need = deg_bound as usize + deg_l as usize + 1;
        let budget = 2 * need + 8;
        self.diag.rec_max_deg_bound = self.diag.rec_max_deg_bound.max(deg_bound + deg_l);

        let mut inputs: Vec<u64> = Vec::new();
        let mut vs: Vec<ZpPoly> = Vec::new(); // Newton coefficients
                                              // The glex-smallest leading `Y`-monomial any image has produced.
                                              //
                                              // This replaces a comparison of the image's degree in the LAST
                                              // variable. At a lucky point the image's leading `Y`-monomial is
                                              // exactly `lm_Y(G)`; at an unlucky one the image carries an extra
                                              // factor `E ∈ Z_p[Y]`, so its leading monomial is `lm_Y(G) * lm_Y(E)`,
                                              // strictly larger. The degree-in-one-variable test sees that only when
                                              // `E` happens to mention that variable — MEASURED: it fired 0 times
                                              // across 813,552 evaluation points, i.e. it was blind. The monomial
                                              // test detects every unlucky point at this level.
        let mut min_lm_y: Option<MonoId> = None;
        let mut tried = 0usize;

        while tried < budget {
            tried += 1;
            if inputs.len() as u64 >= zp.p {
                self.diag.rec_field_exhausted += 1;
                return None; // field exhausted
            }
            let a = loop {
                let a = rng.next() % zp.p;
                if inputs.contains(&a) {
                    continue;
                }
                if self.zp_eval_univ(&lc_g, x, a, zp) != 0 {
                    break a;
                }
                // The imposed leading coefficient vanishes here; the point
                // carries no information. Count it against the budget so a
                // pathological `lc_g` cannot spin forever.
                self.diag.rec_point_lcg_zero += 1;
                tried += 1;
                if tried >= budget {
                    self.diag.rec_budget_exhausted += 1;
                    return None;
                }
            };
            let lc_g_val = self.zp_eval_univ(&lc_g, x, a, zp);

            self.diag.rec_points_tried += 1;
            let u1 = self.zp_eval_var(&pp_u, x, a, zp);
            let v1 = self.zp_eval_var(&pp_v, x, a, zp);
            // A point the level below cannot answer for is a BAD POINT, not a
            // verdict on the level: discard it and draw another. Aborting here
            // was the second-largest decline cause (155 of 871 cases).
            let Some(q) = self.mod_gcd_rec(&u1, &v1, zp, idx + 1, vars, rng) else {
                self.diag.rec_inner_declined += 1;
                continue;
            };
            let Some(q) = self.zp_glex_monic(&q, zp) else {
                self.diag.rec_monic_failed += 1;
                continue;
            };
            let q = self.zp_mul_scalar(&q, lc_g_val, zp);

            let Some(lm_q) = q.terms.first().map(|t| t.0) else {
                self.diag.rec_monic_failed += 1;
                continue;
            };
            match min_lm_y {
                Some(cur) => match self.cmp_mono(lm_q, cur) {
                    Ordering::Less => {
                        self.diag.rec_reset_smaller += 1;
                        min_lm_y = Some(lm_q);
                        inputs.clear();
                        vs.clear();
                    }
                    Ordering::Greater => {
                        self.diag.rec_unlucky_degree += 1;
                        continue; // unlucky point
                    }
                    Ordering::Equal => {}
                },
                None => min_lm_y = Some(lm_q),
            }

            if self.newton_add(&mut inputs, &mut vs, a, &q, zp).is_none() {
                self.diag.rec_newton_failed += 1;
                return None;
            }
            self.diag.rec_max_points_at_level = self
                .diag
                .rec_max_points_at_level
                .max(u32::try_from(inputs.len()).unwrap_or(u32::MAX));
            let h = self.newton_mk(&inputs, &vs, x, zp);

            // z3's `lc_H == lc_g` gate (polynomial.cpp:4527), and it is LOAD
            // BEARING, not an optimization. Every image was scaled so that its
            // glex-leading `x`-coefficient is `lc_g` evaluated at the point, so
            // the interpolant reproduces `lc_g` exactly once enough points have
            // been supplied — and not before.
            //
            // Without it the very first point can produce a CONSTANT `h`, whose
            // primitive part is the unit, which divides everything and is
            // therefore accepted. The oracle caught precisely that:
            // `gcd(y, y^2)` evaluated at `y := a` gives `gcd(a, a^2) = 1` in a
            // field, so one sample point can never distinguish `y` from `1`.
            // Reported at `fuzz --seed 7 --case 145` before this gate existed.
            let lc_h = self.zp_lc_glex_x(&h, x);
            if lc_h != lc_g {
                self.diag.rec_lch_mismatch += 1;
                continue;
            }

            // Strip the `Z_p[x]` content: that, and only that, is what the
            // leading-coefficient imposition added. See this function's docs.
            let cand = match self.zp_cont_pp_y(&h, x, zp) {
                Some(r) => r.1,
                None => {
                    self.diag.rec_content_failed += 1;
                    return None;
                }
            };
            if self.zp_exact_div(&pp_u, &cand, zp).is_none()
                || self.zp_exact_div(&pp_v, &cand, zp).is_none()
            {
                self.diag.rec_trialdiv_reject += 1;
                continue;
            }
            return Some(self.zp_mul(&c_g, &cand, zp));
        }
        self.diag.rec_budget_exhausted += 1;
        None
    }

    // ------------------------------------------------------------------
    // Newton interpolation  (z3 `newton_interpolator`, polynomial.cpp:3142)
    // ------------------------------------------------------------------

    /// Add one sample point `(a, value)` to the incremental Newton form.
    ///
    /// The stored `vs[k]` are the divided differences, so that
    /// `H(x) = vs[0] + (x-a_0) vs[1] + (x-a_0)(x-a_1) vs[2] + ...`.
    fn newton_add(
        &mut self,
        inputs: &mut Vec<u64>,
        vs: &mut Vec<ZpPoly>,
        a: u64,
        value: &ZpPoly,
        zp: &Zp,
    ) -> Option<()> {
        let k = inputs.len();
        if k == 0 {
            inputs.push(a);
            vs.push(value.clone());
            return Some(());
        }
        // temp = H_{k-1}(a), evaluated by Horner on the Newton form.
        let mut temp = vs[k - 1].clone();
        for j in (0..k - 1).rev() {
            let s = zp.sub(a, inputs[j]);
            temp = self.zp_mul_scalar(&temp, s, zp);
            temp = self.zp_add(&temp, &vs[j], zp);
        }
        let mut denom = 1u64;
        for &ai in inputs.iter() {
            denom = zp.mul(denom, zp.sub(a, ai));
        }
        let inv = zp.inv(denom)?;
        let diff = self.zp_sub(value, &temp, zp);
        vs.push(self.zp_mul_scalar(&diff, inv, zp));
        inputs.push(a);
        Some(())
    }

    /// Collapse the Newton form into a polynomial in `x`.
    fn newton_mk(&mut self, inputs: &[u64], vs: &[ZpPoly], x: PVar, zp: &Zp) -> ZpPoly {
        let n = vs.len();
        if n == 0 {
            return ZpPoly::zero();
        }
        let mut r = vs[n - 1].clone();
        for j in (0..n - 1).rev() {
            // r <- r * (x - a_j) + vs[j]
            let shifted = self.zp_mul_var(&r, x, zp);
            let scaled = self.zp_mul_scalar(&r, zp.neg(inputs[j]), zp);
            r = self.zp_add(&shifted, &scaled, zp);
            r = self.zp_add(&r, &vs[j], zp);
        }
        r
    }

    // ------------------------------------------------------------------
    // Chinese remaindering
    // ------------------------------------------------------------------

    /// Combine an integer image modulo `modulus` with a `Z_p` image into an
    /// image modulo `modulus * p`, with coefficients in the symmetric range.
    fn cra_combine(
        &mut self,
        prev: &Poly,
        modulus: &BigInt,
        img: &ZpPoly,
        zp: &Zp,
    ) -> Option<Poly> {
        let p_big = BigInt::from(zp.p);
        let new_mod = modulus * &p_big;
        // m_inv = modulus^{-1} mod p
        let m_mod_p = zp.from_bigint(modulus);
        let m_inv = zp.inv(m_mod_p)?;

        let mut by_mono: HashMap<MonoId, BigInt> = HashMap::new();
        for (m, c) in &prev.terms {
            by_mono.insert(*m, c.clone());
        }
        let mut img_map: HashMap<MonoId, u64> = HashMap::new();
        for (m, c) in &img.terms {
            img_map.insert(*m, *c);
        }
        let mut monos: Vec<MonoId> = by_mono.keys().copied().collect();
        for m in img_map.keys() {
            if !by_mono.contains_key(m) {
                monos.push(*m);
            }
        }

        let mut out: Vec<(MonoId, BigInt)> = Vec::with_capacity(monos.len());
        for m in monos {
            let a = by_mono.get(&m).cloned().unwrap_or_else(BigInt::zero);
            let b = img_map.get(&m).copied().unwrap_or(0);
            // r == a (mod modulus), r == b (mod p)
            let a_mod_p = zp.from_bigint(&a);
            let t = zp.mul(zp.sub(b, a_mod_p), m_inv);
            // `a` sits in the symmetric range for `modulus` and may be
            // negative, so reduce into `[0, new_mod)` first and only then fold
            // into the symmetric range.
            let mut r = (&a + modulus * BigInt::from(t)).mod_floor(&new_mod);
            if &r * 2 > new_mod {
                r -= &new_mod;
            }
            out.push((m, r));
        }
        Some(self.mk(out))
    }

    // ------------------------------------------------------------------
    // The Z_p layer
    // ------------------------------------------------------------------

    /// Reduce an integer polynomial modulo `p`, dropping vanishing terms.
    fn to_zp(&self, p: &Poly, zp: &Zp) -> ZpPoly {
        let mut ts = Vec::with_capacity(p.terms.len());
        for (m, c) in &p.terms {
            let r = zp.from_bigint(c);
            if r != 0 {
                ts.push((*m, r));
            }
        }
        ZpPoly { terms: ts }
    }

    /// Lift a `Z_p` polynomial to `Z` with coefficients in `(-p/2, p/2]`.
    fn from_zp_symmetric(&self, p: &ZpPoly, zp: &Zp) -> Poly {
        let mut ts = Vec::with_capacity(p.terms.len());
        for &(m, c) in &p.terms {
            let val = if c * 2 > zp.p {
                BigInt::from(c) - BigInt::from(zp.p)
            } else {
                BigInt::from(c)
            };
            if !val.is_zero() {
                ts.push((m, val));
            }
        }
        self.mk(ts)
    }

    /// Normalize a `Z_p` term list: sort descending, merge, drop zeros.
    fn zp_mk(&self, terms: Vec<(MonoId, u64)>, zp: &Zp) -> ZpPoly {
        let mut ts = terms;
        ts.retain(|&(_, c)| c != 0);
        ts.sort_by(|a, b| self.cmp_mono(b.0, a.0));
        let mut out: Vec<(MonoId, u64)> = Vec::with_capacity(ts.len());
        for (m, c) in ts {
            match out.last_mut() {
                Some(last) if last.0 == m => {
                    last.1 = zp.add(last.1, c);
                    if last.1 == 0 {
                        out.pop();
                    }
                }
                _ => out.push((m, c)),
            }
        }
        ZpPoly { terms: out }
    }

    fn zp_add(&self, a: &ZpPoly, b: &ZpPoly, zp: &Zp) -> ZpPoly {
        let mut ts = a.terms.clone();
        ts.extend_from_slice(&b.terms);
        self.zp_mk(ts, zp)
    }

    fn zp_sub(&self, a: &ZpPoly, b: &ZpPoly, zp: &Zp) -> ZpPoly {
        let mut ts = a.terms.clone();
        ts.extend(b.terms.iter().map(|&(m, c)| (m, zp.neg(c))));
        self.zp_mk(ts, zp)
    }

    fn zp_mul(&mut self, a: &ZpPoly, b: &ZpPoly, zp: &Zp) -> ZpPoly {
        if a.terms.is_empty() || b.terms.is_empty() {
            return ZpPoly::zero();
        }
        let mut ts: Vec<(MonoId, u64)> = Vec::with_capacity(a.terms.len() * b.terms.len());
        for &(ma, ca) in &a.terms {
            for &(mb, cb) in &b.terms {
                let m = self.mono_mul(ma, mb);
                ts.push((m, zp.mul(ca, cb)));
            }
        }
        self.zp_mk(ts, zp)
    }

    fn zp_mul_scalar(&self, a: &ZpPoly, c: u64, zp: &Zp) -> ZpPoly {
        if c == 0 {
            return ZpPoly::zero();
        }
        ZpPoly {
            terms: a.terms.iter().map(|&(m, x)| (m, zp.mul(x, c))).collect(),
        }
    }

    /// Multiply by the bare variable `x`.
    fn zp_mul_var(&mut self, a: &ZpPoly, x: PVar, zp: &Zp) -> ZpPoly {
        let xm = self.mk_mono(&[(x, 1)]);
        let ts: Vec<(MonoId, u64)> = a
            .terms
            .iter()
            .map(|&(m, c)| (self.mono_mul(m, xm), c))
            .collect();
        self.zp_mk(ts, zp)
    }

    fn zp_degree(&self, p: &ZpPoly, x: PVar) -> u32 {
        p.terms
            .iter()
            .map(|&(m, _)| self.mono_degree_of(m, x))
            .max()
            .unwrap_or(0)
    }

    /// Coefficient of `x^k`, as a `Z_p` polynomial in the other variables.
    fn zp_coeff(&mut self, p: &ZpPoly, x: PVar, k: u32, zp: &Zp) -> ZpPoly {
        let mut ts = Vec::new();
        for &(m, c) in &p.terms {
            if self.mono_degree_of(m, x) == k {
                let m2 = self.mono_div_x_k(m, x, k).expect("degree matches");
                ts.push((m2, c));
            }
        }
        self.zp_mk(ts, zp)
    }

    /// Substitute `x := a`.
    fn zp_eval_var(&mut self, p: &ZpPoly, x: PVar, a: u64, zp: &Zp) -> ZpPoly {
        let mut ts = Vec::with_capacity(p.terms.len());
        for &(m, c) in &p.terms {
            let k = self.mono_degree_of(m, x);
            if k == 0 {
                ts.push((m, c));
                continue;
            }
            let m2 = self.mono_div_x_k(m, x, k).expect("k is the degree of x");
            ts.push((m2, zp.mul(c, zp.pow(a, k))));
        }
        self.zp_mk(ts, zp)
    }

    /// Evaluate a `Z_p` polynomial that mentions only `x` (or nothing) at `a`.
    /// Any other variable makes the question meaningless, and the answer is
    /// `0` — the callers use it only as a "is this point admissible" gate, and
    /// answering `0` refuses the point rather than accepting it wrongly.
    fn zp_eval_univ(&self, p: &ZpPoly, x: PVar, a: u64, zp: &Zp) -> u64 {
        let mut acc = 0u64;
        for &(m, c) in &p.terms {
            let pows = self.mono_pows(m);
            match pows.len() {
                0 => acc = zp.add(acc, c),
                1 if pows[0].0 == x => acc = zp.add(acc, zp.mul(c, zp.pow(a, pows[0].1))),
                _ => return 0,
            }
        }
        acc
    }

    /// Scale so the glex-leading coefficient is `1`.
    fn zp_glex_monic(&self, p: &ZpPoly, zp: &Zp) -> Option<ZpPoly> {
        let lc = p.terms.first()?.1;
        let inv = zp.inv(lc)?;
        Some(self.zp_mul_scalar(p, inv, zp))
    }

    /// z3 `lc_glex_ZpX`: view `p` in `Z_p[y...][x]`, find the glex-maximal
    /// monomial in the `y`s, and return the polynomial in `x` alone that is its
    /// coefficient.
    fn zp_lc_glex_x(&mut self, p: &ZpPoly, x: PVar) -> ZpPoly {
        let mut max_m: Option<MonoId> = None;
        let mut out: Vec<(MonoId, u64)> = Vec::new();
        for &(m, c) in &p.terms {
            let k = self.mono_degree_of(m, x);
            let stripped = self.mono_div_x_k(m, x, k).expect("k is the degree of x");
            let xk = self.mk_mono(&[(x, k)]);
            match max_m {
                Some(cur) if self.cmp_mono(stripped, cur) == Ordering::Greater => {
                    max_m = Some(stripped);
                    out.clear();
                    out.push((xk, c));
                }
                Some(cur) if cur == stripped => out.push((xk, c)),
                Some(_) => {}
                None => {
                    max_m = Some(stripped);
                    out.push((xk, c));
                }
            }
        }
        // The list is built by scanning a canonical polynomial, so it is
        // already free of duplicates; sort it into canonical order.
        out.sort_by(|a, b| self.cmp_mono(b.0, a.0));
        ZpPoly { terms: out }
    }

    /// Exact division in `Z_p[...]`, `None` when it does not divide.
    fn zp_exact_div(&mut self, a: &ZpPoly, b: &ZpPoly, zp: &Zp) -> Option<ZpPoly> {
        let (dm, dc) = *b.terms.first()?;
        let dinv = zp.inv(dc)?;
        if a.terms.is_empty() {
            return Some(ZpPoly::zero());
        }
        let mut rem = a.clone();
        let mut quot: Vec<(MonoId, u64)> = Vec::new();
        while let Some(&(rm, rc)) = rem.terms.first() {
            let qm = self.mono_exact_div(rm, dm)?;
            let qc = zp.mul(rc, dinv);
            let t = ZpPoly {
                terms: vec![(qm, qc)],
            };
            quot.push((qm, qc));
            let prod = self.zp_mul(&t, b, zp);
            rem = self.zp_sub(&rem, &prod, zp);
        }
        Some(self.zp_mk(quot, zp))
    }

    /// Content of `p` with respect to every variable EXCEPT `x`: viewing
    /// `p ∈ Z_p[x][Y]`, the GCD **in `Z_p[x]`** of the coefficients attached to
    /// the distinct `Y`-monomials.
    ///
    /// This is the OTHER content, and it is the one Brown's algorithm needs
    /// when `x` is the variable being interpolated: the leading-coefficient
    /// imposition multiplies the true GCD by a factor that lives in `Z_p[x]`,
    /// and only a content taken in `Z_p[x]` can remove it. Removing the content
    /// in `Z_p[Y]` instead — which is what [`PolyManager::zp_content_pp`] does —
    /// removes nothing, because that factor is `Y`-free.
    ///
    /// Deterministic: the grouping is built in the canonical term order of `p`,
    /// never through a hash iteration.
    fn zp_cont_y(&mut self, p: &ZpPoly, x: PVar, zp: &Zp) -> Option<ZpPoly> {
        if p.terms.is_empty() {
            return Some(ZpPoly::zero());
        }
        // (Y-monomial, its Z_p[x] coefficient as (x^k, c) pairs), in the order
        // the Y-monomials are first seen while scanning `p` canonically.
        let mut groups: Vec<(MonoId, Vec<(MonoId, u64)>)> = Vec::new();
        for &(m, c) in &p.terms {
            let k = self.mono_degree_of(m, x);
            let stripped = self.mono_div_x_k(m, x, k)?;
            let xk = self.mk_mono(&[(x, k)]);
            match groups.iter_mut().find(|(s, _)| *s == stripped) {
                Some((_, ts)) => ts.push((xk, c)),
                None => groups.push((stripped, vec![(xk, c)])),
            }
        }
        let mut acc: Option<ZpPoly> = None;
        for (_, ts) in groups {
            let coeff = self.zp_mk(ts, zp);
            acc = Some(match acc {
                None => coeff,
                Some(cur) => {
                    let g = self.zp_euclid_gcd(&cur, &coeff, x, zp)?;
                    if g.terms.len() == 1 && g.terms[0].0 == self.one {
                        return Some(g); // unit content; nothing left to remove
                    }
                    g
                }
            });
        }
        acc
    }

    /// `(cont_Y(p), p / cont_Y(p))` — the split [`PolyManager::zp_cont_y`]
    /// describes, with the content made monic in `x` so the split is canonical.
    fn zp_cont_pp_y(&mut self, p: &ZpPoly, x: PVar, zp: &Zp) -> Option<(ZpPoly, ZpPoly)> {
        if p.terms.is_empty() {
            return Some((ZpPoly::one(self.one), ZpPoly::zero()));
        }
        let c = self.zp_cont_y(p, x, zp)?;
        if c.terms.is_empty() {
            return None;
        }
        let c = self.zp_glex_monic(&c, zp)?;
        let pp = self.zp_exact_div(p, &c, zp)?;
        Some((c, pp))
    }

    /// Content and primitive part with respect to `x` over `Z_p`.
    fn zp_content_pp(&mut self, p: &ZpPoly, x: PVar, zp: &Zp) -> Option<(ZpPoly, ZpPoly)> {
        if p.terms.is_empty() {
            return Some((ZpPoly::one(self.one), ZpPoly::zero()));
        }
        let d = self.zp_degree(p, x);
        if d == 0 {
            // All of `p` is content with respect to `x`; the primitive part is
            // the unit. Returning `monic(p)` here instead would break the
            // `c * pp == p` invariant every caller relies on.
            return Some((p.clone(), ZpPoly::one(self.one)));
        }
        let mut c = ZpPoly::zero();
        for k in 0..=d {
            let ck = self.zp_coeff(p, x, k, zp);
            if ck.terms.is_empty() {
                continue;
            }
            c = self.zp_gcd_nomain(&c, &ck, zp)?;
            if c.terms.len() == 1 && c.terms[0].0 == self.one {
                break;
            }
        }
        if c.terms.is_empty() {
            return None;
        }
        let c = self.zp_glex_monic(&c, zp)?;
        let pp = self.zp_exact_div(p, &c, zp)?;
        Some((c, pp))
    }

    /// GCD of two `Z_p` polynomials that do not contain the variable being
    /// eliminated: recursive PRS on their own largest variable.
    ///
    /// Only used on contents, which are strictly smaller in variable count
    /// than the polynomial they came from, so the recursion is well-founded.
    fn zp_gcd_nomain(&mut self, u: &ZpPoly, v: &ZpPoly, zp: &Zp) -> Option<ZpPoly> {
        if u.terms.is_empty() {
            return self.zp_glex_monic(v, zp).or(Some(ZpPoly::zero()));
        }
        if v.terms.is_empty() {
            return self.zp_glex_monic(u, zp).or(Some(ZpPoly::zero()));
        }
        let uv = self.zp_max_var(u);
        let vv = self.zp_max_var(v);
        match (uv, vv) {
            (None, _) | (_, None) => Some(ZpPoly::one(self.one)),
            (Some(a), Some(b)) => {
                let x = a.max(b);
                self.zp_gcd_prs(u, v, x, zp)
            }
        }
    }

    fn zp_max_var(&self, p: &ZpPoly) -> Option<PVar> {
        let mut best: Option<PVar> = None;
        for &(m, _) in &p.terms {
            if let Some(&(v, _)) = self.mono_pows(m).last() {
                best = Some(match best {
                    Some(b) if b >= v => b,
                    _ => v,
                });
            }
        }
        best
    }

    /// Euclid's algorithm in `Z_p[x]`, for inputs that mention no other
    /// variable. Any other variable is refused (`None`) rather than silently
    /// producing a wrong answer.
    fn zp_euclid_gcd(&mut self, u: &ZpPoly, v: &ZpPoly, x: PVar, zp: &Zp) -> Option<ZpPoly> {
        let mut a = self.zp_to_dense(u, x)?;
        let mut b = self.zp_to_dense(v, x)?;
        if a.is_empty() && b.is_empty() {
            return Some(ZpPoly::zero());
        }
        while !b.is_empty() {
            let r = zp.dense_rem(&a, &b);
            a = b;
            b = r;
        }
        // Normalize monic.
        let lc = *a.last().expect("non-empty");
        let inv = zp.inv(lc)?;
        for c in a.iter_mut() {
            *c = zp.mul(*c, inv);
        }
        let mut ts = Vec::new();
        for (k, &c) in a.iter().enumerate() {
            if c == 0 {
                continue;
            }
            let m = self.mk_mono(&[(x, u32::try_from(k).expect("degree fits"))]);
            ts.push((m, c));
        }
        Some(self.zp_mk(ts, zp))
    }

    /// Dense low-to-high coefficient vector of a `Z_p` polynomial in `x` alone.
    fn zp_to_dense(&self, p: &ZpPoly, x: PVar) -> Option<Vec<u64>> {
        if p.terms.is_empty() {
            return Some(Vec::new());
        }
        let mut d = 0u32;
        for &(m, _) in &p.terms {
            let pows = self.mono_pows(m);
            match pows.len() {
                0 => {}
                1 if pows[0].0 == x => d = d.max(pows[0].1),
                _ => return None,
            }
        }
        let mut out = vec![0u64; d as usize + 1];
        for &(m, c) in &p.terms {
            let pows = self.mono_pows(m);
            let k = if pows.is_empty() { 0 } else { pows[0].1 };
            out[k as usize] = c;
        }
        while matches!(out.last(), Some(&0)) {
            out.pop();
        }
        Some(out)
    }

    /// Subresultant-free PRS GCD in `Z_p` (a field, so plain primitive PRS with
    /// monic normalization is enough).
    fn zp_gcd_prs(&mut self, u: &ZpPoly, v: &ZpPoly, x: PVar, zp: &Zp) -> Option<ZpPoly> {
        if let (Some(_), Some(_)) = (self.zp_to_dense(u, x), self.zp_to_dense(v, x)) {
            return self.zp_euclid_gcd(u, v, x, zp);
        }
        let (u, v) = if self.zp_degree(u, x) < self.zp_degree(v, x) {
            (v, u)
        } else {
            (u, v)
        };
        let (c_u, pp_u0) = self.zp_content_pp(u, x, zp)?;
        let (c_v, pp_v0) = self.zp_content_pp(v, x, zp)?;
        let c_g = self.zp_gcd_nomain(&c_u, &c_v, zp)?;
        let mut pp_u = pp_u0;
        let mut pp_v = pp_v0;
        loop {
            let rem = self.zp_pseudo_rem(&pp_u, &pp_v, x, zp)?;
            if rem.terms.is_empty() {
                let g = self.zp_content_pp(&pp_v, x, zp)?.1;
                return Some(self.zp_mul(&c_g, &g, zp));
            }
            if self.zp_degree(&rem, x) == 0 && self.zp_max_var(&rem).is_none() {
                return Some(c_g);
            }
            pp_u = pp_v;
            pp_v = self.zp_content_pp(&rem, x, zp)?.1;
        }
    }

    /// Pseudo-remainder over `Z_p` with respect to `x`.
    fn zp_pseudo_rem(&mut self, p: &ZpPoly, q: &ZpPoly, x: PVar, zp: &Zp) -> Option<ZpPoly> {
        if q.terms.is_empty() {
            return None;
        }
        let deg_b = self.zp_degree(q, x);
        if deg_b == 0 {
            return Some(ZpPoly::zero());
        }
        let l_b = self.zp_coeff(q, x, deg_b, zp);
        let mut r = p.clone();
        let mut guard = 0usize;
        loop {
            let deg_r = self.zp_degree(&r, x);
            if r.terms.is_empty() || deg_r < deg_b {
                return Some(r);
            }
            guard += 1;
            if guard > 4096 {
                return None; // fail closed rather than spin
            }
            let l_r = self.zp_coeff(&r, x, deg_r, zp);
            let shift = self.mk_mono(&[(x, deg_r - deg_b)]);
            let shift_poly = ZpPoly {
                terms: vec![(shift, 1)],
            };
            let lhs = self.zp_mul(&l_b, &r, zp);
            let t = self.zp_mul(&l_r, &shift_poly, zp);
            let rhs = self.zp_mul(&t, q, zp);
            r = self.zp_sub(&lhs, &rhs, zp);
        }
    }
}

// ============================================================================
// Z_p scalars and polynomials
// ============================================================================

/// A `Z_p` polynomial, sharing the manager's interned monomials so that the
/// modular layer never builds a second monomial universe.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ZpPoly {
    terms: Vec<(MonoId, u64)>,
}

impl ZpPoly {
    fn zero() -> Self {
        Self { terms: Vec::new() }
    }
    fn one(one_mono: MonoId) -> Self {
        Self {
            terms: vec![(one_mono, 1)],
        }
    }
}

/// Arithmetic modulo a prime below `2^31`, so that every product fits a `u64`.
#[derive(Clone, Copy, Debug)]
struct Zp {
    p: u64,
}

impl Zp {
    fn new(p: u64) -> Self {
        debug_assert!(p > 1 && p < (1u64 << 31));
        Self { p }
    }
    fn add(self, a: u64, b: u64) -> u64 {
        let s = a + b;
        if s >= self.p {
            s - self.p
        } else {
            s
        }
    }
    fn sub(self, a: u64, b: u64) -> u64 {
        if a >= b {
            a - b
        } else {
            a + self.p - b
        }
    }
    fn neg(self, a: u64) -> u64 {
        if a == 0 {
            0
        } else {
            self.p - a
        }
    }
    fn mul(self, a: u64, b: u64) -> u64 {
        (a * b) % self.p
    }
    fn pow(self, a: u64, mut e: u32) -> u64 {
        let mut acc = 1u64;
        let mut base = a % self.p;
        while e > 0 {
            if e & 1 == 1 {
                acc = self.mul(acc, base);
            }
            e >>= 1;
            if e > 0 {
                base = self.mul(base, base);
            }
        }
        acc
    }
    /// Modular inverse by the extended Euclidean algorithm; `None` for `0`.
    fn inv(self, a: u64) -> Option<u64> {
        if a % self.p == 0 {
            return None;
        }
        let (mut old_r, mut r) = (a as i128 % self.p as i128, self.p as i128);
        let (mut old_s, mut s) = (1i128, 0i128);
        while r != 0 {
            let q = old_r / r;
            let nr = old_r - q * r;
            old_r = r;
            r = nr;
            let ns = old_s - q * s;
            old_s = s;
            s = ns;
        }
        if old_r != 1 {
            return None;
        }
        let mut inv = old_s % self.p as i128;
        if inv < 0 {
            inv += self.p as i128;
        }
        Some(inv as u64)
    }
    /// Reduce a `BigInt` into `0..p`.
    fn from_bigint(self, c: &BigInt) -> u64 {
        let m = BigInt::from(self.p);
        let mut r = c % &m;
        if r.is_negative() {
            r += &m;
        }
        u64::try_from(r).expect("reduced modulo a 31-bit prime")
    }
    /// Remainder of dense univariate division, low-to-high, trailing zeros
    /// trimmed. `b` must be non-empty.
    fn dense_rem(self, a: &[u64], b: &[u64]) -> Vec<u64> {
        let mut r = a.to_vec();
        let db = b.len() - 1;
        let binv = self
            .inv(b[db])
            .expect("a normalized dense polynomial has a unit leading coefficient");
        while r.len() > db {
            let dr = r.len() - 1;
            let f = self.mul(r[dr], binv);
            if f != 0 {
                let shift = dr - db;
                for j in 0..=db {
                    r[shift + j] = self.sub(r[shift + j], self.mul(f, b[j]));
                }
            }
            r.pop();
            while matches!(r.last(), Some(&0)) {
                r.pop();
            }
            if r.is_empty() {
                break;
            }
        }
        r
    }
}

/// 31-bit primes used by the modular GCD, in the order they are tried.
///
/// Large primes make each CRA step recover ~31 bits of every coefficient, so a
/// GCD whose coefficients are `k` bits wide needs about `k/31` of them. All are
/// below `2^31`, which is what keeps `a * b` inside a `u64` in [`Zp::mul`].
/// Primality is pinned by a unit test rather than trusted.
const ZP_PRIMES: [u64; 16] = [
    2_147_483_647,
    2_147_483_629,
    2_147_483_587,
    2_147_483_579,
    2_147_483_563,
    2_147_483_549,
    2_147_483_543,
    2_147_483_497,
    2_147_483_489,
    2_147_483_477,
    2_147_483_423,
    2_147_483_399,
    2_147_483_353,
    2_147_483_323,
    2_147_483_269,
    2_147_483_249,
];

/// SplitMix64 — the evaluation-point source for the modular GCD.
///
/// Deterministic and seeded from a constant, so a `mod_gcd` result is a pure
/// function of its inputs and replays identically. Randomness here is only
/// about avoiding unlucky evaluation points; it is never in the decision path,
/// because every candidate is gated by an exact-division certificate.
struct SplitMix {
    state: u64,
}

impl SplitMix {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

#[cfg(test)]
#[path = "polymanager_tests.rs"]
mod polymanager_tests;
