// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dynamic Polynomial Watchdog (DPW) — Paxian, Reimer & Becker, SAT 2018.
//!
//! Encodes `Σ w_i·x_i <= k` over weighted literals with the bound `k` carried
//! ENTIRELY BY ASSUMPTIONS, so retightening `k` costs ZERO clauses and ZERO
//! variables. This is the cardinality encoding behind Pacose/PacoseMP2, the
//! upper-bound-descent solvers that own the af-synthesis family AY is 0/15 on.
//!
//! # Construction
//!
//! 1. **Buckets (base-2 decomposition).** `p = bitlength(max w_i)`;
//!    `B_j = { x_i : bit j of w_i set }`. Then `Σ w_i x_i = Σ_j 2^j·c_j` with
//!    `c_j = #true in B_j` — a base-2 number whose digits are not binary.
//! 2. **Tare variables.** Fresh `t_0..t_{p-2}`, with `t_j` placed INTO bucket
//!    `j`: `I_j = B_j ∪ {t_j}`. They contribute `T = Σ 2^j·[t_j]`, and every
//!    residue mod `2^{p-1}` is representable, so `k` is injected THROUGH `T`
//!    rather than baked into the structure. That is what makes DPW *dynamic*.
//! 3. **Carry chain.** `v_j = c_j + ⌊v_{j-1}/2⌋`, with `S_j` the unary
//!    "at-least" vector of `v_j` truncated at `M_j`. The key identity
//!    `S_{j-1}[2q] ⟺ ⌊v_{j-1}/2⌋ ≥ q` makes `HALF(S_{j-1})` — the stride-2
//!    slice of an ALREADY-SORTED vector — the unary carry, so carry
//!    propagation costs zero variables and zero clauses. That is the whole
//!    trick of the watchdog family:
//!    `S_j = MERGE(TOT(I_j), HALF(S_{j-1}))` truncated at `M_j`.
//! 4. **Clauses.** Only the input→output direction is emitted (all a `<=`
//!    constraint needs, and half a totalizer's clauses): one merge node over
//!    sorted `A`, `B` into `C` emits `(¬A_i ∨ ¬B_j ∨ C_{i+j})`. Every clause
//!    has exactly one positive literal, so the encoding is HORN.
//! 5. **Truncation.** `M_{p-1} = K_init + 1` and `M_j = min(nat_j,
//!    2^{p-1-j}·(K_init+1))`, where `nat_j` is the natural uncapped width.
//!    Sound because outputs only need to be FORCED, not equivalent, and
//!    `M_j = 2·M_{j+1}` keeps the carry from being under-reported below the
//!    index that matters.
//!
//! # Asserting `Σ <= k`
//!
//! `ρ = k mod 2^{p-1}`, `K = ⌊k / 2^{p-1}⌋`, `T* = 2^{p-1} − 1 − ρ`. Assume
//! `t_j = bit_j(T*)` for `j = 0..p-2` plus `¬S_{p-1}[K+1]`. Then
//! `¬S_{p-1}[K+1] ⟺ v_{p-1} ≤ K ⟺ W + T* ≤ 2^{p-1}(K+1) − 1 ⟺ W ≤ k`. EXACT,
//! not a relaxation: the tare is precisely the constant making `k + T ≡ −1
//! (mod 2^{p-1})`, the only case where bounding the top digit alone bounds the
//! whole number.
//!
//! ⚠️ **VACUOUS-SAFETY, NOT A CLAMP.** If `K + 1 > nat_{p-1}` the bound is not
//! representable — the sum can never exceed `k` — and NOTHING is asserted. It
//! must never be clamped with `.min(len)`: that is the exact `.min(len)`
//! mistake [`crate::oll::ResidualBound`] records as having shipped ten wrong
//! answers, and the `clamp` mutant of this construction produced wrong answers
//! on 111 of 78,000 brute-force checks — only 0.14%, invisible to any sweep
//! that does not deliberately drive `k_init` past the representable range.
//! [`dpw_tests::vacuous_bound_is_never_clamped`] is that sweep.
//!
//! ⚠️ **NON-MONOTONE TARE.** `T* = 2^{p-1} − 1 − (k mod 2^{p-1})` is NOT
//! monotone in `k` (k=115→T=4, k=112→T=7, k=111→T=0), so tare literals can
//! never be committed as one-way units. Assumptions are not an optimisation
//! here, they are the single hard requirement DPW places on its host.
//!
//! ⚠️ **STRICTLY WEAKER PROPAGATOR THAN GTE** (measured, 26,948 GAC probes:
//! DPW 81.9% vs GTE 100%, worst at the boundary — 58.5% at excess 1). The
//! trade is 6–11x fewer clauses against a propagator that misses ~1 in 5
//! forced literals, which is why [`crate::oll::OllEngine::select_descent_enc`]
//! only takes DPW when it is decisively smaller.

use ay_sat::{Literal, Solver as SatSolver};

use crate::solver::Weight;

/// Vars/clauses a DPW build would emit, computed WITHOUT touching the solver.
///
/// The whole point of a closed-form pre-check: `gte_build`'s comment records
/// 30+ uninterruptible seconds and gigabytes burned enumerating a doomed
/// node, so a new encoding must be able to decline before emission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DpwSize {
    /// Auxiliary variables (tare vars + one per merge output).
    pub(crate) vars: usize,
    /// Definitional clauses.
    pub(crate) clauses: usize,
    /// Number of bit levels, `bitlength(max w_i)`.
    pub(crate) levels: u32,
    /// Width of the top level's output vector `|S_{p-1}|`.
    pub(crate) top_width: usize,
}

/// A built DPW structure. The bound is NOT stored in the clause set — see
/// [`DpwEnc::assumptions`].
pub(crate) struct DpwEnc {
    /// Tare variables `t_0..t_{p-2}`, in POSITIVE form.
    tare: Vec<Literal>,
    /// The top level's unary output vector `S_{p-1}`, truncated at `M_{p-1}`.
    top: Vec<Literal>,
    /// Number of bit levels.
    p: u32,
    /// `2^{p-1}`, the top level's granularity.
    granularity: Weight,
    /// NATURAL (uncapped) width of the top level: the largest `v_{p-1}` the
    /// structure can ever take. `K + 1 > nat_top` is the vacuous case.
    nat_top: usize,
    /// Loosest bound the structure was built for.
    k_init: Weight,
    /// Emitted size, for tracing and for the predictor's self-check.
    pub(crate) size: DpwSize,
    /// Inclusive variable-id range allocated by this build. Read only by the
    /// debug assertion that no DPW literal ever reaches a core, so release
    /// builds legitimately never touch it.
    #[cfg_attr(not(debug_assertions), allow(dead_code))]
    var_lo: u32,
    #[cfg_attr(not(debug_assertions), allow(dead_code))]
    var_hi: u32,
}

/// Running tallies shared by the builder and the predictor.
#[derive(Clone, Copy, Default)]
struct Tally {
    vars: usize,
    clauses: usize,
}

impl Tally {
    /// `true` when either budget is now exhausted.
    fn over(&self, var_budget: usize, clause_budget: usize) -> bool {
        self.vars > var_budget || self.clauses > clause_budget
    }
}

/// Number of bit levels for a weight multiset: `bitlength(max w_i)`.
///
/// Callers must have filtered zero weights (they contribute nothing to the
/// sum); `w_max >= 1` makes `p >= 1`.
fn levels(w_max: Weight) -> u32 {
    debug_assert!(w_max >= 1);
    Weight::BITS - w_max.leading_zeros()
}

/// Clause count of one merge node over sorted vectors of lengths `a` and `b`
/// truncated at `m`, and the resulting output width.
///
/// Mirrors [`merge`] pair-for-pair rather than using a closed form, so the
/// predictor cannot drift from the emitter (asserted by
/// [`dpw_tests::size_predictor_matches_emitted_build`]).
fn merge_size(a: usize, b: usize, m: usize) -> (usize, usize) {
    // Mirror [`merge`]'s empty-side shortcut. Unreachable as the construction
    // stands — bucket `p-1` always holds the literal that set `p =
    // bitlength(w_max)`, and every bucket below it holds a tare variable, so
    // no level's totalizer is ever empty — but a predictor that silently
    // disagrees with the emitter on a shape nobody currently builds is exactly
    // the kind of latent gap that surfaces as a bad encoding choice later.
    if a == 0 {
        return (b.min(m), 0);
    }
    if b == 0 {
        return (a.min(m), 0);
    }
    let n = (a + b).min(m);
    if n == 0 {
        return (0, 0);
    }
    let mut clauses = 0usize;
    for i in 0..=a.min(n) {
        for j in 0..=b.min(n) {
            let t = i + j;
            if t == 0 || t > n {
                continue;
            }
            clauses += 1;
        }
    }
    (n, clauses)
}

/// Output width of a truncated balanced totalizer over `leaves` unit inputs,
/// accumulating its cost into `tally`.
fn totalize_size(leaves: usize, m: usize, tally: &mut Tally) -> usize {
    if leaves == 0 {
        return 0;
    }
    if leaves == 1 {
        // Leaves reuse the input literal: no fresh var, no clauses.
        return 1;
    }
    let mid = leaves / 2;
    let l = totalize_size(mid, m, tally);
    let r = totalize_size(leaves - mid, m, tally);
    let (n, clauses) = merge_size(l, r, m);
    tally.vars += n;
    tally.clauses += clauses;
    n
}

/// Per-level bucket sizes, natural widths and truncation caps.
///
/// `bucket_sizes[j]` INCLUDES the tare variable for `j <= p-2`.
struct Shape {
    p: u32,
    bucket_sizes: Vec<usize>,
    nat: Vec<usize>,
    caps: Vec<usize>,
}

/// Derive the level shape from the weight multiset and the loosest bound.
fn shape(weights: &[Weight], k_init: Weight) -> Option<Shape> {
    let w_max = weights.iter().copied().max()?;
    if w_max == 0 {
        return None;
    }
    let p = levels(w_max);
    let granularity: Weight = 1 << (p - 1);
    let k_top = k_init / granularity;

    let mut bucket_sizes = vec![0usize; p as usize];
    for &w in weights {
        for (j, size) in bucket_sizes.iter_mut().enumerate() {
            if (w >> j) & 1 == 1 {
                *size += 1;
            }
        }
    }
    // One tare variable per level below the top.
    for size in bucket_sizes.iter_mut().take(p as usize - 1) {
        *size += 1;
    }

    let mut nat = vec![0usize; p as usize];
    let mut prev = 0usize;
    for j in 0..p as usize {
        let cur = bucket_sizes[j] + prev / 2;
        nat[j] = cur;
        prev = cur;
    }

    // Need S_{p-1} up to K_init + 1, hence S_j up to 2^{p-1-j}·(K_init + 1).
    // Widened in u128 so a huge cap saturates into `nat` instead of wrapping —
    // wrapping here would silently UNDER-truncate and make the encoding too
    // strong, the wrong-answer direction.
    let caps: Vec<usize> = (0..p as usize)
        .map(|j| {
            let shift = (p as usize - 1) - j;
            let scaled = (k_top as u128 + 1) << shift;
            (nat[j] as u128).min(scaled) as usize
        })
        .collect();

    Some(Shape {
        p,
        bucket_sizes,
        nat,
        caps,
    })
}

/// Predict a DPW build's exact size without allocating a variable or emitting
/// a clause. `None` = a budget would blow (or the input is degenerate).
///
/// `weights` must already have zero entries removed.
pub(crate) fn dpw_size(
    weights: &[Weight],
    k_init: Weight,
    var_budget: usize,
    clause_budget: usize,
) -> Option<DpwSize> {
    let sh = shape(weights, k_init)?;
    let mut tally = Tally {
        // The tare variables.
        vars: sh.p as usize - 1,
        clauses: 0,
    };
    let mut carry_len = 0usize;
    let mut top_width = 0usize;
    for j in 0..sh.p as usize {
        let m = sh.caps[j];
        let tot = totalize_size(sh.bucket_sizes[j], m, &mut tally);
        let width = if carry_len == 0 {
            tot.min(m)
        } else {
            let (n, clauses) = merge_size(tot, carry_len, m);
            tally.vars += n;
            tally.clauses += clauses;
            n
        };
        if tally.over(var_budget, clause_budget) {
            return None;
        }
        // HALF(S_j): the stride-2 slice S_j[2], S_j[4], ... — free.
        carry_len = width / 2;
        if j == sh.p as usize - 1 {
            top_width = width;
        }
    }
    Some(DpwSize {
        vars: tally.vars,
        clauses: tally.clauses,
        levels: sh.p,
        top_width,
    })
}

/// Merge two sorted unary "at-least" vectors into a fresh one, truncated at
/// `m`. Only the input→output direction is emitted.
///
/// An empty side returns the other side truncated rather than allocating a
/// copy chain: `C_i ⟺ A_i` propagates at least as strongly as `A_i → C_i` and
/// the exact-count assignment still satisfies the encoding, so this is
/// size-only. (The brute-force nets below cover the substitution.)
fn merge(
    a: &[Literal],
    b: &[Literal],
    m: usize,
    sat: &mut SatSolver,
    fresh: &mut dyn FnMut(&mut SatSolver) -> Literal,
    guard: Option<Literal>,
    tally: &mut Tally,
) -> Vec<Literal> {
    if a.is_empty() {
        return b.iter().take(m).copied().collect();
    }
    if b.is_empty() {
        return a.iter().take(m).copied().collect();
    }
    let n = (a.len() + b.len()).min(m);
    if n == 0 {
        return Vec::new();
    }
    let c: Vec<Literal> = (0..n).map(|_| fresh(sat)).collect();
    tally.vars += n;
    for i in 0..=a.len().min(n) {
        for j in 0..=b.len().min(n) {
            let t = i + j;
            if t == 0 || t > n {
                continue;
            }
            let mut clause = Vec::with_capacity(4);
            if i > 0 {
                clause.push(a[i - 1].negated());
            }
            if j > 0 {
                clause.push(b[j - 1].negated());
            }
            clause.push(c[t - 1]);
            if let Some(g) = guard {
                clause.push(g.negated());
            }
            sat.add_clause(clause);
            tally.clauses += 1;
        }
    }
    c
}

/// Balanced truncated totalizer over unit inputs. Leaves reuse the input
/// literals (no fresh variables).
fn totalize(
    lits: &[Literal],
    m: usize,
    sat: &mut SatSolver,
    fresh: &mut dyn FnMut(&mut SatSolver) -> Literal,
    guard: Option<Literal>,
    tally: &mut Tally,
) -> Vec<Literal> {
    if lits.is_empty() {
        return Vec::new();
    }
    if lits.len() == 1 {
        return vec![lits[0]];
    }
    let mid = lits.len() / 2;
    let l = totalize(&lits[..mid], m, sat, fresh, guard, tally);
    let r = totalize(&lits[mid..], m, sat, fresh, guard, tally);
    merge(&l, &r, m, sat, fresh, guard, tally)
}

impl DpwEnc {
    /// Build the watchdog for the LOOSEST bound `k_init` the descent will ever
    /// assert. Every `k <= k_init` is then reachable through
    /// [`DpwEnc::assumptions`] at zero clause cost.
    ///
    /// `inputs` are `(literal, weight)` pairs; zero-weight entries are dropped
    /// (they cannot change the sum). `None` = nothing to encode.
    pub(crate) fn build(
        inputs: &[(Literal, Weight)],
        k_init: Weight,
        sat: &mut SatSolver,
        fresh: &mut dyn FnMut(&mut SatSolver) -> Literal,
        guard: Option<Literal>,
    ) -> Option<DpwEnc> {
        let live: Vec<(Literal, Weight)> = inputs.iter().copied().filter(|&(_, w)| w > 0).collect();
        let weights: Vec<Weight> = live.iter().map(|&(_, w)| w).collect();
        let sh = shape(&weights, k_init)?;
        let p = sh.p;
        let granularity: Weight = 1 << (p - 1);

        let mut tally = Tally::default();
        // Ownership range for the debug core-leak guard. `lo > hi` (the
        // initial state) means "owns nothing", which is correct for a
        // structure that allocated no auxiliaries at all.
        let mut var_lo = u32::MAX;
        let mut var_hi = 0u32;
        // Every auxiliary — tare variables included — is allocated through the
        // caller's `fresh`, so phase saving and `next_var` bookkeeping stay
        // consistent with the other descent encodings.
        let mut tracked = |sat: &mut SatSolver| -> Literal {
            let lit = fresh(sat);
            let id = lit.variable().id();
            var_lo = var_lo.min(id);
            var_hi = var_hi.max(id);
            lit
        };

        // Tare variables t_0..t_{p-2}.
        let mut tare: Vec<Literal> = Vec::with_capacity(p as usize - 1);
        for _ in 0..p - 1 {
            tare.push(tracked(sat));
        }
        tally.vars += tare.len();

        let mut buckets: Vec<Vec<Literal>> = Vec::with_capacity(p as usize);
        for j in 0..p as usize {
            let mut bucket: Vec<Literal> = live
                .iter()
                .filter(|&&(_, w)| (w >> j) & 1 == 1)
                .map(|&(lit, _)| lit)
                .collect();
            if j < p as usize - 1 {
                bucket.push(tare[j]);
            }
            buckets.push(bucket);
        }
        debug_assert_eq!(
            buckets.iter().map(Vec::len).collect::<Vec<_>>(),
            sh.bucket_sizes,
            "DPW size predictor and builder disagree on bucket shape",
        );
        debug_assert!(
            buckets.iter().all(|b| !b.is_empty()),
            "DPW: an empty bucket means an empty level totalizer, and the level \
             chain's merge shape stops matching the predictor's. Bucket p-1 \
             holds the literal that DEFINED p = bitlength(w_max) and every \
             bucket below holds a tare variable, so this cannot happen.",
        );

        let mut top: Vec<Literal> = Vec::new();
        let mut carry: Vec<Literal> = Vec::new();
        for j in 0..p as usize {
            let m = sh.caps[j];
            let tot = totalize(&buckets[j], m, sat, &mut tracked, guard, &mut tally);
            let s_j = if carry.is_empty() {
                tot.into_iter().take(m).collect::<Vec<_>>()
            } else {
                merge(&tot, &carry, m, sat, &mut tracked, guard, &mut tally)
            };
            // HALF(S_j) = (S_j[2], S_j[4], …) IS the unary carry into level
            // j+1: a stride-2 slice of an already-sorted vector, costing zero
            // variables and zero clauses. Starting this slice at index 0
            // instead of 1 is the `carry_odd` mutant — 11,650 wrong answers in
            // 78,000 brute-force checks.
            carry = s_j.iter().skip(1).step_by(2).copied().collect();
            if j == p as usize - 1 {
                top = s_j;
            }
        }
        let size = DpwSize {
            vars: tally.vars,
            clauses: tally.clauses,
            levels: p,
            top_width: top.len(),
        };
        Some(DpwEnc {
            tare,
            top,
            p,
            granularity,
            nat_top: sh.nat[p as usize - 1],
            k_init,
            size,
            var_lo,
            var_hi,
        })
    }

    /// Assumption literals asserting `Σ w_i·x_i <= k`. ZERO clauses, always.
    ///
    /// An EMPTY bound part means VACUOUS — the structure cannot represent a
    /// violation of `k`, i.e. the sum can never exceed it — and that must
    /// never be turned into a real bound by clamping the index into range.
    pub(crate) fn assumptions(&self, k: Weight) -> Vec<Literal> {
        debug_assert!(
            k <= self.k_init,
            "DPW: k={k} exceeds the k_init={} the structure was built for",
            self.k_init,
        );
        if k > self.k_init {
            // Unrepresentable in the LOOSE direction: assert nothing rather
            // than assert something too strong.
            return Vec::new();
        }
        let rho = k % self.granularity;
        let k_top = k / self.granularity;
        let tare_value = self.granularity - 1 - rho;
        let mut out: Vec<Literal> = Vec::with_capacity(self.p as usize);
        for (j, &t) in self.tare.iter().enumerate() {
            // Both polarities. Omitting the negative ones is satisfiability-
            // safe (tare vars occur only negatively — pure literal — and the
            // `tare_no_negatives` mutant passed 78,000/78,000), but it costs
            // p-1 literals to keep any extracted core meaningful.
            out.push(if (tare_value >> j) & 1 == 1 {
                t
            } else {
                t.negated()
            });
        }
        // VACUOUS-SAFE BY CONSTRUCTION, never `.min(len)`.
        let idx = k_top as u128 + 1;
        if idx <= self.top.len() as u128 {
            out.push(self.top[k_top as usize].negated());
        } else {
            debug_assert!(
                idx > self.nat_top as u128,
                "DPW: bound index {idx} lost to truncation (nat_top={}) — the \
                 truncation caps are wrong, and asserting nothing here would \
                 silently drop a REAL bound",
                self.nat_top,
            );
        }
        out
    }

    /// Does `lit` name a variable this structure allocated?
    ///
    /// Debug-only guard for the integration's sharp edge: a tare literal or a
    /// watchdog output reaching OLL's core extraction would put watchdog
    /// internals inside a core and corrupt the cost identity.
    #[cfg_attr(not(debug_assertions), allow(dead_code))]
    pub(crate) fn owns(&self, lit: Literal) -> bool {
        let id = lit.variable().id();
        self.var_lo <= id && id <= self.var_hi
    }

    /// Number of bit levels.
    pub(crate) fn levels(&self) -> u32 {
        self.p
    }

    /// Top-level granularity `2^{p-1}`.
    #[cfg(test)]
    pub(crate) fn granularity(&self) -> Weight {
        self.granularity
    }
}

/// Predicted size of the GTE [`crate::oll::gte_build`] would emit for the same
/// inputs, computed without touching the solver.
///
/// An EXACT mirror of `gte_build` — same recursion, same budget mutations, same
/// bail order — so "the size pass declined" and "the build would have declined"
/// are the same statement. Returns `(aux vars, clauses, root outputs)`.
pub(crate) fn gte_size(
    inputs: &[(Literal, Weight)],
    cap: Weight,
    out_budget: &mut i64,
    clause_budget: &mut i64,
) -> Option<(usize, usize, usize)> {
    fn rec(
        weights: &[Weight],
        cap: Weight,
        out_budget: &mut i64,
        clause_budget: &mut i64,
        vars: &mut usize,
        clauses: &mut usize,
    ) -> Option<Vec<Weight>> {
        if weights.len() == 1 {
            return Some(vec![weights[0].min(cap)]);
        }
        let mid = weights.len() / 2;
        let left = rec(
            &weights[..mid],
            cap,
            out_budget,
            clause_budget,
            vars,
            clauses,
        )?;
        let right = rec(
            &weights[mid..],
            cap,
            out_budget,
            clause_budget,
            vars,
            clauses,
        )?;
        let pairs = (left.len() as i64 + 1).saturating_mul(right.len() as i64 + 1);
        if pairs - 1 > *clause_budget {
            return None;
        }
        let mut sums: Vec<Weight> = Vec::new();
        for &a in std::iter::once(&0).chain(left.iter()) {
            for &b in std::iter::once(&0).chain(right.iter()) {
                let s = a.saturating_add(b).min(cap);
                if s > 0 {
                    sums.push(s);
                }
            }
        }
        sums.sort_unstable();
        sums.dedup();
        *out_budget -= sums.len() as i64;
        if *out_budget < 0 {
            return None;
        }
        *vars += sums.len();
        // One clause per nonzero (left ∪ {0}) x (right ∪ {0}) pair.
        let emitted = pairs - 1;
        *clause_budget -= emitted;
        if *clause_budget < 0 {
            return None;
        }
        *clauses += emitted as usize;
        Some(sums)
    }

    if inputs.is_empty() {
        return None;
    }
    let weights: Vec<Weight> = inputs.iter().map(|&(_, w)| w).collect();
    let mut vars = 0usize;
    let mut clauses = 0usize;
    let outs = rec(
        &weights,
        cap,
        out_budget,
        clause_budget,
        &mut vars,
        &mut clauses,
    )?;
    Some((vars, clauses, outs.len()))
}

#[cfg(test)]
mod dpw_tests {
    use ay_sat::Variable;

    use super::*;

    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Build a DPW over `n` fresh input variables in a fresh solver.
    fn build_fixture(weights: &[Weight], k_init: Weight) -> (SatSolver, Vec<Literal>, DpwEnc) {
        let mut sat = SatSolver::new(0);
        let xs: Vec<Literal> = (0..weights.len())
            .map(|_| Literal::positive(sat.new_var()))
            .collect();
        let inputs: Vec<(Literal, Weight)> =
            xs.iter().copied().zip(weights.iter().copied()).collect();
        let mut fresh = |s: &mut SatSolver| Literal::positive(s.new_var());
        let enc = DpwEnc::build(&inputs, k_init, &mut sat, &mut fresh, None)
            .expect("non-degenerate fixture must build");
        (sat, xs, enc)
    }

    /// Is the encoding satisfiable with `bits` forced onto the inputs and the
    /// bound `k` assumed?
    fn probe(sat: &mut SatSolver, xs: &[Literal], enc: &DpwEnc, bits: u64, k: Weight) -> bool {
        let mut assumptions = enc.assumptions(k);
        for (i, &x) in xs.iter().enumerate() {
            assumptions.push(if (bits >> i) & 1 == 1 { x } else { x.negated() });
        }
        sat.solve_with_assumptions_interruptible(&assumptions, || false)
            .into_inner()
            .is_sat()
    }

    /// The `k` values to test: every achievable subset-sum boundary hit from
    /// BOTH sides, plus the extremes. Boundary saturation is what catches the
    /// off-by-one family — a uniform random sweep over `k` mostly misses them.
    fn boundary_ks(weights: &[Weight], k_init: Weight) -> Vec<Weight> {
        let total: Weight = weights.iter().sum();
        let mut ks: Vec<Weight> = vec![0, k_init];
        let mut sums: Vec<Weight> = vec![0];
        for &w in weights {
            let grown: Vec<Weight> = sums.iter().map(|&s| s + w).collect();
            sums.extend(grown);
            sums.sort_unstable();
            sums.dedup();
        }
        for &s in &sums {
            for d in [s.saturating_sub(1), s, s + 1] {
                if d <= k_init {
                    ks.push(d);
                }
            }
        }
        ks.push(total.min(k_init));
        ks.sort_unstable();
        ks.dedup();
        ks
    }

    /// PRIMARY CORRECTNESS NET. Random weighted instances, exhaustive over
    /// every assignment and boundary-saturating over `k`: the encoding must be
    /// satisfiable EXACTLY when `Σ w_i·x_i <= k`.
    ///
    /// Kill mutation (`tare_off_by_one`): in [`DpwEnc::assumptions`], change
    /// `let tare_value = self.granularity - 1 - rho;` to
    /// `let tare_value = self.granularity - rho;`.
    #[test]
    fn dpw_matches_brute_force_over_assignments_and_bounds() {
        let mut checks = 0u64;
        let mut hit_top = 0u64;
        for seed in 0..900u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(101));
            let n = 1 + rng.below(7) as usize;
            let w_max = [1u64, 2, 3, 4, 5, 7, 9, 15, 16, 17, 31, 64][rng.below(12) as usize];
            let weights: Vec<Weight> = (0..n).map(|_| 1 + rng.below(w_max)).collect();
            let total: Weight = weights.iter().sum();
            let k_init = match rng.below(4) {
                0 => total,
                1 => total + 1,
                2 => (total / 2).max(1),
                _ => 1 + rng.below(total + 3),
            };

            let (mut sat, xs, enc) = build_fixture(&weights, k_init);
            if enc.levels() >= 3 {
                hit_top += 1;
            }

            for k in boundary_ks(&weights, k_init) {
                for bits in 0..(1u64 << n) {
                    let sum: Weight = weights
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| (bits >> i) & 1 == 1)
                        .map(|(_, &w)| w)
                        .sum();
                    let got = probe(&mut sat, &xs, &enc, bits, k);
                    checks += 1;
                    assert_eq!(
                        got,
                        sum <= k,
                        "seed {seed}: weights {weights:?} k_init {k_init} k {k} \
                         bits {bits:b} sum {sum}: encoding says {} but truth is {}",
                        if got { "SAT" } else { "UNSAT" },
                        if sum <= k { "SAT" } else { "UNSAT" },
                    );
                }
            }
        }
        assert!(
            checks > 500_000,
            "net too thin: only {checks} (assignment, k) checks",
        );
        assert!(
            hit_top > 200,
            "net must reach p >= 3 (multi-level carry chains): only {hit_top} instances",
        );
    }

    /// INCREMENTAL TIGHTENING. Build ONCE at `k_init`, then walk `k` down to 0
    /// reusing the same clause set: exactness must hold at every step and the
    /// clause count must never move. This is the property the whole encoding
    /// exists for, and the one AY's GTE pays unit clauses for.
    ///
    /// Kill mutation (`descent_rebuilds`): in [`DpwEnc::assumptions`], change
    /// `let rho = k % self.granularity;` to
    /// `let rho = self.k_init % self.granularity;` — the tare then freezes at
    /// the build-time bound and every tightened `k` silently reads as `k_init`.
    #[test]
    fn incremental_tightening_is_exact_and_adds_no_clauses() {
        for seed in 0..250u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(211));
            let n = 2 + rng.below(6) as usize;
            let w_max = [2u64, 3, 5, 9, 16, 17, 33][rng.below(7) as usize];
            let weights: Vec<Weight> = (0..n).map(|_| 1 + rng.below(w_max)).collect();
            let total: Weight = weights.iter().sum();
            let k_init = total + 2;

            let (mut sat, xs, enc) = build_fixture(&weights, k_init);
            // The solver refreshes `num_original_clauses` from its arena at
            // solve time rather than incrementing it on add, so the reference
            // point is taken after the first solve has registered the build.
            let mut registered: Option<usize> = None;

            // Descend k_init -> 0 over ONE clause set.
            for k in (0..=k_init).rev() {
                for bits in 0..(1u64 << n) {
                    let sum: Weight = weights
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| (bits >> i) & 1 == 1)
                        .map(|(_, &w)| w)
                        .sum();
                    assert_eq!(
                        probe(&mut sat, &xs, &enc, bits, k),
                        sum <= k,
                        "seed {seed}: weights {weights:?} descent k {k} bits {bits:b} sum {sum}",
                    );
                }
                let now = sat.num_original_clauses();
                match registered {
                    None => registered = Some(now),
                    Some(first) => assert!(
                        now <= first,
                        "seed {seed}: retightening to k={k} GREW the formula \
                         ({first} -> {now}); the bound must cost zero clauses",
                    ),
                }
            }
            // The structure's own emitted-clause tally is fixed at build time
            // and `assumptions` cannot reach the solver at all (it takes
            // `&self` and no `SatSolver`), so a descent of k_init+1 distinct
            // bounds ran against one unchanged clause set.
            assert!(enc.size.clauses > 0, "seed {seed}: fixture encoded nothing");
        }
    }

    /// VACUOUS SAFETY. `k_init` deliberately past the representable range, so
    /// the top-bound index falls off the end of `S_{p-1}` and NOTHING may be
    /// asserted. Clamping the index into range here is the `.min(len)` mistake
    /// that shipped ten wrong answers on #descent-residual; as a DPW mutant it
    /// fires on only 0.14% of checks, so it needs its own targeted sweep.
    ///
    /// Kill mutation (`clamp`): in [`DpwEnc::assumptions`], replace the
    /// `if idx <= self.top.len() as u128 { … } else { … }` block with the
    /// unconditional
    /// `out.push(self.top[(k_top as usize).min(self.top.len() - 1)].negated());`.
    #[test]
    fn vacuous_bound_is_never_clamped() {
        let mut vacuous_seen = 0u64;
        for seed in 0..400u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(307));
            let n = 1 + rng.below(6) as usize;
            let weights: Vec<Weight> = (0..n).map(|_| 1 + rng.below(9)).collect();
            let total: Weight = weights.iter().sum();
            // Drive k_init WELL past Σw: the top level can never reach the
            // bound index, so the bound is genuinely vacuous.
            let k_init = total * 4 + 7;

            let (mut sat, xs, enc) = build_fixture(&weights, k_init);

            for k in [k_init, k_init - 1, total * 2, total + 1, total] {
                if k > k_init {
                    continue;
                }
                let bound_part = enc.assumptions(k).len() > enc.levels() as usize - 1;
                if !bound_part {
                    vacuous_seen += 1;
                }
                for bits in 0..(1u64 << n) {
                    let sum: Weight = weights
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| (bits >> i) & 1 == 1)
                        .map(|(_, &w)| w)
                        .sum();
                    assert_eq!(
                        probe(&mut sat, &xs, &enc, bits, k),
                        sum <= k,
                        "seed {seed}: weights {weights:?} VACUOUS-regime k {k} \
                         bits {bits:b} sum {sum} (Σw={total}) — a satisfiable \
                         assignment reading UNSAT here is a wrong answer",
                    );
                }
            }
        }
        assert!(
            vacuous_seen > 300,
            "sweep never entered the vacuous regime ({vacuous_seen} hits): it \
             cannot be evidence for the no-clamp discipline",
        );
    }

    /// The closed-form predictor is what the descent selector declines on, so
    /// it must agree with the emitter to the clause. A predictor that
    /// under-counts would let a doomed build through the budget gate.
    ///
    /// Kill mutation (`predictor_forgets_tare`): in [`dpw_size`], change
    /// `vars: sh.p as usize - 1,` to `vars: 0,`.
    #[test]
    fn size_predictor_matches_emitted_build() {
        for seed in 0..120u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(401));
            let n = 1 + rng.below(40) as usize;
            let w_max = [1u64, 3, 9, 17, 64, 255][rng.below(6) as usize];
            let weights: Vec<Weight> = (0..n).map(|_| 1 + rng.below(w_max)).collect();
            let total: Weight = weights.iter().sum();
            let k_init = 1 + rng.below(total + 1);

            let predicted = dpw_size(&weights, k_init, usize::MAX, usize::MAX)
                .expect("unbudgeted predictor must not decline");
            let (_sat, _xs, enc) = build_fixture(&weights, k_init);
            assert_eq!(
                predicted, enc.size,
                "seed {seed}: weights {weights:?} k_init {k_init}: predictor \
                 {predicted:?} vs emitted {:?}",
                enc.size,
            );
        }
    }

    /// Budgets must be enforced BEFORE emission — the predictor declines, the
    /// solver is never touched.
    ///
    /// Kill mutation (`budget_ignored`): in [`dpw_size`], change
    /// `if tally.over(var_budget, clause_budget) { return None; }` to
    /// `if false { return None; }`.
    #[test]
    fn size_predictor_declines_on_budget() {
        let weights: Vec<Weight> = (0..200).map(|i| 1 + (i % 250) as Weight).collect();
        assert!(
            dpw_size(&weights, 4_000, usize::MAX, usize::MAX).is_some(),
            "unbudgeted build must be predicted",
        );
        assert!(
            dpw_size(&weights, 4_000, usize::MAX, 100).is_none(),
            "a 100-clause budget must decline a build of thousands",
        );
        assert!(
            dpw_size(&weights, 4_000, 10, usize::MAX).is_none(),
            "a 10-variable budget must decline",
        );
    }

    /// The GTE size mirror must reproduce `gte_build`'s own accounting,
    /// otherwise the DPW-vs-GTE choice is made on a fiction.
    ///
    /// Both counts are pinned through the budgets the real builder consumes:
    /// the exact predicted budget must suffice, and one unit less — of either
    /// kind — must decline. An over- or under-counting mirror fails one of the
    /// two directions.
    ///
    /// Kill mutation (`gte_mirror_drops_dedup`): in [`gte_size`], delete
    /// `sums.dedup();`.
    #[test]
    fn gte_size_mirrors_gte_build() {
        let mut tight = 0u64;
        for seed in 0..150u64 {
            let mut rng = Lcg(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(503));
            let n = 1 + rng.below(24) as usize;
            let w_max = [1u64, 3, 9, 17, 64][rng.below(5) as usize];
            let weights: Vec<Weight> = (0..n).map(|_| 1 + rng.below(w_max)).collect();
            let total: Weight = weights.iter().sum();
            let cap = 1 + rng.below(total + 1);

            let inputs: Vec<(Literal, Weight)> = weights
                .iter()
                .map(|&w| (Literal::positive(Variable::new(1)), w))
                .collect();
            let mut ob = 400_000i64;
            let mut cb = 4_000_000i64;
            let predicted = gte_size(&inputs, cap, &mut ob, &mut cb);

            let generous = crate::oll::gte_build_for_test(&weights, cap, 400_000, 4_000_000);
            let Some((pv, pc, po)) = predicted else {
                assert!(
                    generous.is_none(),
                    "seed {seed}: mirror declined but the builder did not",
                );
                continue;
            };
            assert_eq!(
                generous,
                Some((pv, po)),
                "seed {seed}: weights {weights:?} cap {cap}: mirror vars/outs \
                 disagree with the builder",
            );

            // The predicted budgets must be EXACTLY enough...
            assert_eq!(
                crate::oll::gte_build_for_test(&weights, cap, pv as i64, pc as i64),
                Some((pv, po)),
                "seed {seed}: builder declined at the mirror's own predicted budget \
                 ({pv} outs / {pc} clauses) — the mirror UNDER-counts",
            );
            // ...and one unit short of either must decline.
            if pv > 0 {
                tight += 1;
                assert!(
                    crate::oll::gte_build_for_test(&weights, cap, pv as i64 - 1, pc as i64)
                        .is_none(),
                    "seed {seed}: builder survived {} outs when the mirror predicted \
                     {pv} — the mirror OVER-counts outputs",
                    pv - 1,
                );
                assert!(
                    crate::oll::gte_build_for_test(&weights, cap, pv as i64, pc as i64 - 1)
                        .is_none(),
                    "seed {seed}: builder survived {} clauses when the mirror predicted \
                     {pc} — the mirror OVER-counts clauses",
                    pc - 1,
                );
            }
        }
        assert!(
            tight > 100,
            "too few multi-input instances to pin the budgets: {tight}",
        );
    }

    /// The worked example from the spec, on the real instance's shape: 170
    /// unit softs with weights 1..9 at cap 115. Pins the numbers the descent
    /// decision is made on so a refactor cannot quietly move them. This is the
    /// only place the TRUNCATION CAPS themselves are checked against
    /// independently derived values — the brute-force nets are too small for
    /// truncation to bite.
    ///
    /// Kill mutation (`truncation_off_by_one`): in [`shape`], change
    /// `let scaled = (k_top as u128 + 1) << shift;` to
    /// `let scaled = (k_top as u128) << shift;`.
    #[test]
    fn real_instance_shape_matches_spec() {
        // The measured histogram of af-synthesis_wt-af-synthesis_stb_50_120_5.
        let hist: [(Weight, usize); 9] = [
            (1, 17),
            (2, 20),
            (3, 20),
            (4, 16),
            (5, 15),
            (6, 18),
            (7, 22),
            (8, 23),
            (9, 19),
        ];
        let mut weights: Vec<Weight> = Vec::new();
        for (w, count) in hist {
            for _ in 0..count {
                weights.push(w);
            }
        }
        assert_eq!(weights.len(), 170);
        assert_eq!(weights.iter().sum::<Weight>(), 873);

        let sh = shape(&weights, 115).expect("shape");
        assert_eq!(sh.p, 4, "p = bitlength(9) = 4");
        assert_eq!(sh.bucket_sizes, vec![94, 81, 72, 42]);
        assert_eq!(sh.nat, vec![94, 128, 136, 110]);
        assert_eq!(sh.caps, vec![94, 60, 30, 15]);

        let size = dpw_size(&weights, 115, usize::MAX, usize::MAX).expect("size");
        assert_eq!(size.levels, 4);
        assert_eq!(size.top_width, 15);
        // The spec's measured figures: 1,816 aux vars and 13,743 clauses,
        // against the GTE's 3,609 / 118,460 at the same cap.
        assert_eq!(size.vars, 1_816);
        assert_eq!(size.clauses, 13_743);

        // Four assumption literals asserts the bound; retightening costs zero.
        let (_sat, _xs, enc) = build_fixture(&weights, 115);
        assert_eq!(enc.size, size, "predictor vs emitter on the real shape");
        assert_eq!(enc.granularity(), 8);
        let a = enc.assumptions(115);
        assert_eq!(a.len(), 4, "3 tare literals + 1 top-bound literal");
        assert_eq!(enc.assumptions(83).len(), 4);
        assert_eq!(enc.assumptions(0).len(), 4);
    }
}
