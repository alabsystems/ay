// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EXACT lattice proof for the market-split min-total-slack family (markshare1).
//!
//! ## The instance the whole field cannot prove
//!
//! markshare1 is 6 equality rows `a_i·x + s_i = b_i` over 50 binaries `x` and
//! nonneg continuous slacks `s`, minimising `Σ s_i`. Every `b_i` is exactly
//! `½·Σ_j a_ij`, so the LP relaxation puts `x = ½·1`, hits every equality
//! exactly, and reports objective 0 — a bound that never moves. The float
//! solvers then enumerate millions of nodes (Gurobi 4.6M at 60s) and NONE
//! proves the optimum is 1. Every exact cut family AY has (MIR, strong-CG,
//! GMI, cover) leaves the root bound at 0.000000 as well: this is not a
//! cutting problem, it is a LATTICE problem.
//!
//! ## What "optimum = 1" means, exactly
//!
//! `Σ s_i` is a nonneg integer (`a`,`x`,`b` all integer). It is 0 iff `A x = b`
//! has a 0/1 solution — the "objective-0 face". So:
//!   * the objective-0 face is EMPTY  ⟹  optimum ≥ 1  (no exact market split);
//!   * some face `A x = b − e_k` has a 0/1 point ⟹  optimum ≤ 1  (that point
//!     leaves slack 1 in row `k`, 0 elsewhere).
//! Both are decided here by exact lattice enumeration and together prove
//! OPTIMAL 1 — beating the entire field on this instance.
//!
//! ## The device (Aardal–Hurkens–Lenstra reformulation + CVP enumeration)
//!
//! For a target rhs `d` (either `b` or `b−e_k`):
//!   1. `x = x_d + K y` where `A x_d = d` (a particular integer solution) and
//!      `K` is a basis of the SATURATED integer kernel `{x∈ℤ^n : A x = 0}`,
//!      computed by column-Hermite-normal-form with unimodular tracking.
//!   2. LLL-reduce `K` and Babai-reduce `x_d` against it, so the 0/1 box maps
//!      to a well-conditioned region in `y`.
//!   3. Every 0/1 point sits EXACTLY on the sphere `‖x − ½·1‖² = n/4`.
//!      Project `τ = ½·1 − x_d` onto `span(K)` and enumerate every lattice
//!      point `K y` within that radius of the projection (Fincke–Pohst /
//!      Schnorr–Euchner). Projection can only shrink distance, so this is a
//!      conservative superset even when `τ` has a perpendicular component;
//!      every candidate is then checked EXACTLY against the integer box
//!      `0 ≤ x_d + K y ≤ 1`.
//!
//! On markshare1 the objective-0 face enumeration visits ~43.6M nodes and
//! finds NOTHING (proving optimum ≥ 1); the `b − e_0` face yields a 0/1 point
//! of 25 ones (proving optimum ≤ 1). Both run in a few seconds.
//!
//! ## Exactness
//!
//! HNF, kernel, particular solution, Babai reduction and the per-candidate box
//! check are all exact (`BigInt` / `i64`). Enumeration uses the exact rational
//! GSO converted to outward-rounded `f64` intervals: every center, partial
//! distance and integer range encloses its exact value. Therefore a valid point
//! can never be pruned by floating arithmetic. Every point the enumeration
//! keeps is adjudicated by exact integer arithmetic, and the returned witness
//! is finally re-checked by `Model::check_point`. Anything whose interval is
//! non-finite or too wide to enumerate aborts to `None` and hands the model back
//! to the normal search untouched.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::time::Instant;

use crate::model::{exact, Col, Model, Row, Sense};
use crate::outcome::Outcome;

/// Hard cap on the enumeration so a mis-fire can never run away: past this the
/// device aborts to `None` and the normal search takes over. markshare1's
/// objective-0 face is ~43.6M nodes, so 4G is ~100× headroom.
const NODE_BUDGET: u64 = 4_000_000_000;

/// Size caps — the family is tiny (markshare1: 6×62). Anything wider is out of
/// the family and out of the enumeration's budget; it pays one comparison.
const MAX_ROWS: usize = 24;
const MAX_COLS: usize = 160;

/// The market-split min-total-slack structure, compiled from a [`Model`].
struct MarketSplit {
    /// Number of free binary columns.
    n: usize,
    /// Number of equality (target) rows.
    m: usize,
    /// `m × n` integer coefficient matrix over the binaries.
    a: Vec<Vec<i64>>,
    /// `m` integer right-hand sides (adjusted for fixed-column contributions).
    b: Vec<i64>,
    /// Model column index of each binary (length `n`, ascending).
    bin_cols: Vec<usize>,
    /// Model column index of each row's single free continuous slack (length `m`).
    slack_col: Vec<usize>,
}

/// Detect the markshare1-class shape, or `None`. SELF-GATING contract: fires on
/// `Minimize` models whose EVERY row is an equality carrying ≥2 free binaries
/// plus exactly one unit free continuous slack (unit objective, appears in that
/// one row), with the objective living entirely on those slacks and every
/// integral column a free 0/1 or a fixed column. Across the corpus this matches
/// exactly markshare1 and stays silent on everything else (set-partition rows
/// carry no slack; mas74/pk1 carry inequalities; gt2/flugpl carry general
/// integers; milp_speed is Maximize with `≤` rows).
fn detect(model: &Model) -> Option<MarketSplit> {
    // This device currently consumes the public f64 matrix.  A model with true
    // rational overrides must not be classified from those rounded proxies;
    // the ordinary exact rim handles it instead.
    if model.sense() != Sense::Minimize || model.has_inexact_coeffs() {
        return None;
    }
    let nc = model.num_cols();
    let nr = model.num_rows();
    if nr == 0 || nr > MAX_ROWS || nc == 0 || nc > MAX_COLS {
        return None;
    }
    // Column census: every column is a free 0/1, a fixed column, or a free
    // continuous slack on `[0, ub)`.
    let mut is_fixed = vec![false; nc];
    let mut is_bin = vec![false; nc];
    let mut is_cont = vec![false; nc];
    let mut fixed_val = vec![0.0f64; nc];
    for j in 0..nc {
        let c = Col(j as u32);
        let (l, u) = model.col_bounds(c);
        if l == u {
            is_fixed[j] = true;
            fixed_val[j] = l;
        } else if model.col_kind(c).is_integral() {
            if l == 0.0 && u == 1.0 {
                is_bin[j] = true;
            } else {
                return None; // general integer: not this family
            }
        } else {
            if l != 0.0 {
                return None; // a slack lives on [0, ub)
            }
            is_cont[j] = true;
        }
    }
    let bin_cols: Vec<usize> = (0..nc).filter(|&j| is_bin[j]).collect();
    let n = bin_cols.len();
    if n < 2 {
        return None;
    }
    let mut bin_pos = vec![usize::MAX; nc];
    for (k, &j) in bin_cols.iter().enumerate() {
        bin_pos[j] = k;
    }
    // A free continuous column must be the slack of EXACTLY ONE row; count first.
    let mut cont_rows = vec![0usize; nc];
    for i in 0..nr {
        let (coeffs, _, _) = model.row(Row(i as u32));
        for &(c, a) in coeffs {
            if a != 0.0 && is_cont[c as usize] {
                cont_rows[c as usize] += 1;
            }
        }
    }
    for j in 0..nc {
        if is_cont[j] && cont_rows[j] != 1 {
            return None; // a free continuous column not tied to exactly one row
        }
    }
    // Row census: EVERY row is an equality with ≥2 binaries and one free
    // continuous slack. The MPS reader may have scaled a whole row by a power of
    // two (markshare1's rhs 1116 > 1024, so its rows arrive halved), so recover
    // the ORIGINAL integer system by dividing each row through by its slack
    // coefficient — which normalises the slack to unit and cancels the scaling
    // (`s_i = b_i − a_i·x` in original units regardless).
    let mut a = vec![vec![0i64; n]; nr];
    let mut b = vec![0i64; nr];
    let mut slack_col = vec![usize::MAX; nr];
    for i in 0..nr {
        let (coeffs, lo, up) = model.row(Row(i as u32));
        if lo != up || !lo.is_finite() {
            return None; // an inequality/range row: alien shape (mas74/pk1)
        }
        // Locate the single free slack and its (row-scaled) coefficient. Its
        // objective coefficient must be unit, so the objective is exactly Σ s_i.
        let mut slack: Option<(usize, f64)> = None;
        for &(c, coef) in coeffs {
            let cj = c as usize;
            if coef != 0.0 && is_cont[cj] {
                if model.obj_coeff(Col(c)) != 1.0 {
                    return None;
                }
                if slack.replace((cj, coef)).is_some() {
                    return None; // two free slacks in one row
                }
            }
        }
        let (s, sc) = slack?; // every target row must carry its slack
        if !(sc > 0.0) {
            return None; // slack must absorb the deficit side (markshare: +)
        }
        let mut nbin = 0usize;
        let sc_q = exact(sc)?;
        let mut fixed_contrib = BigRational::zero();
        for &(c, coef) in coeffs {
            let cj = c as usize;
            if coef == 0.0 {
                continue;
            }
            if is_bin[cj] {
                let ai_q = exact(coef)? / &sc_q;
                if !ai_q.is_integer() {
                    return None;
                }
                let ai = ai_q.to_integer().to_i64()?;
                a[i][bin_pos[cj]] = ai;
                nbin += 1;
            } else if is_cont[cj] {
                // the slack column itself (coef/sc == 1): nothing to record
            } else {
                // Fixed-column contribution in recovered units, exactly.  A
                // tolerance-based integer cast is not enough here: the proof
                // that Σs is integer requires the normalized system itself to
                // be integer, not merely close to one.
                fixed_contrib += (exact(coef)? / &sc_q) * exact(fixed_val[cj])?;
            }
        }
        if nbin < 2 {
            return None;
        }
        slack_col[i] = s;
        // b_i = rhs/sc − fixed contribution, exactly integral.
        let bi = exact(lo)? / &sc_q - fixed_contrib;
        if !bi.is_integer() {
            return None;
        }
        b[i] = bi.to_integer().to_i64()?;
    }
    // The objective's NONCONSTANT portion lives entirely on the slacks: every
    // binary has objective 0, and every free continuous column was proven
    // above to be one of those slacks. Fixed-column terms and the model offset
    // are harmless constants; `prove` reports the full exact objective value.
    for &j in &bin_cols {
        if model.obj_coeff(Col(j as u32)) != 0.0 {
            return None;
        }
    }
    Some(MarketSplit {
        n,
        m: nr,
        a,
        b,
        bin_cols,
        slack_col,
    })
}

/// Public entry: if `model` is the markshare1-class shape and the lattice device
/// can decide its optimum is 0 or 1 within budget, return the proven
/// `Outcome::Optimal`; otherwise `None` (hand back to the normal search).
pub(crate) fn try_prove(model: &Model, deadline: Instant) -> Option<Outcome> {
    try_prove_configured(
        model,
        deadline,
        std::env::var_os("AY_MILP_NO_LATTICE").is_some(),
    )
}

/// Dispatch split out so the kill-switch pin does not mutate the process-wide
/// environment while other lattice tests are proving in parallel.
fn try_prove_configured(model: &Model, deadline: Instant, disabled: bool) -> Option<Outcome> {
    if disabled {
        return None;
    }
    let ms = detect(model)?;
    let trace = std::env::var_os("AY_MILP_TRACE").is_some();
    if trace {
        eprintln!(
            "AY_MILP_TRACE lattice: market-split shape {}x{} — building AHL reformulation",
            ms.m, ms.n
        );
    }
    // Never starve the normal search: the device may run at most HALF the
    // remaining budget, then aborts to `None` and hands the model back. On
    // markshare1 this is moot (the proof lands in ~1.4s); it only bites a
    // hypothetical hard market-split (optimum ≥ 2, or a large ball) that the
    // normal search would then get a fair share of the clock to attempt.
    let now = Instant::now();
    let sub_deadline = now + deadline.saturating_duration_since(now).mul_f64(0.5);
    let eng = Engine::build(&ms, sub_deadline, trace)?;
    eng.prove(model, &ms)
}

/// Closed `f64` interval with every operation rounded one ulp outward.  The
/// hardware operations are round-to-nearest; stepping the computed endpoint
/// outward encloses the corresponding real operation (including an exact
/// endpoint), which is the same directed-rounding license used by `ns.rs`.
#[derive(Clone, Copy, Debug)]
struct Interval {
    lo: f64,
    hi: f64,
}

impl Interval {
    fn from_rational(v: &BigRational) -> Option<Self> {
        let f = v.to_f64()?;
        if !f.is_finite() {
            return None;
        }
        let fv = BigRational::from_float(f)?;
        Some(if fv < *v {
            Self {
                lo: f,
                hi: f.next_up(),
            }
        } else if fv > *v {
            Self {
                lo: f.next_down(),
                hi: f,
            }
        } else {
            Self { lo: f, hi: f }
        })
    }

    fn add(self, rhs: Self) -> Option<Self> {
        if rhs.lo == 0.0 && rhs.hi == 0.0 {
            return Some(self);
        }
        if self.lo == 0.0 && self.hi == 0.0 {
            return Some(rhs);
        }
        let lo = (self.lo + rhs.lo).next_down();
        let hi = (self.hi + rhs.hi).next_up();
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    fn sub(self, rhs: Self) -> Option<Self> {
        if rhs.lo == 0.0 && rhs.hi == 0.0 {
            return Some(self);
        }
        let lo = (self.lo - rhs.hi).next_down();
        let hi = (self.hi - rhs.lo).next_up();
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    /// Multiply by an exactly-represented scalar.
    fn scale(self, scalar: f64) -> Option<Self> {
        if scalar == 0.0 {
            return Some(Self { lo: 0.0, hi: 0.0 });
        }
        let (lo, hi) = if scalar >= 0.0 {
            ((self.lo * scalar).next_down(), (self.hi * scalar).next_up())
        } else {
            ((self.hi * scalar).next_down(), (self.lo * scalar).next_up())
        };
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    /// Product of two intervals already known nonnegative (distance² × norm).
    fn mul_nonnegative(self, rhs: Self) -> Option<Self> {
        debug_assert!(self.lo >= 0.0 && rhs.lo >= 0.0);
        let lo = (self.lo * rhs.lo).next_down().max(0.0);
        let hi = (self.hi * rhs.hi).next_up();
        (lo.is_finite() && hi.is_finite()).then_some(Self { lo, hi })
    }

    fn square(self) -> Option<Self> {
        if self.lo <= 0.0 && self.hi >= 0.0 {
            let m = self.lo.abs().max(self.hi.abs());
            let hi = (m * m).next_up();
            return hi.is_finite().then_some(Self { lo: 0.0, hi });
        }
        let a = self.lo * self.lo;
        let b = self.hi * self.hi;
        if !a.is_finite() || !b.is_finite() {
            return None;
        }
        Some(Self {
            lo: a.min(b).next_down().max(0.0),
            hi: a.max(b).next_up(),
        })
    }
}

/// The reduced kernel lattice + exact GSO, shared across every face.
struct Engine {
    n: usize,
    /// Reduced kernel basis: `k[t]` is a vector in ℤ^n (length `n`), `t < dim`.
    k: Vec<Vec<i64>>,
    /// Kernel dimension `n − m`.
    dim: usize,
    /// Column-HNF unimodular matrix `U` (n×n) and rank, for particular solutions.
    u: Vec<Vec<BigInt>>,
    hh: Vec<Vec<BigInt>>, // A·U = [H | 0]; H = hh[:][:rank]
    rank: usize,
    /// Exact GSO of the reduced basis (for Babai): orthogonal vectors + sq norms.
    bstar_q: Vec<Vec<BigRational>>,
    cnorm_q: Vec<BigRational>,
    /// Outward-rounded mirrors of the exact GSO for the enumeration hot loop.
    /// These are enclosures, not point approximations: an `Empty` result may
    /// rely on their lower endpoints without trusting round-to-nearest.
    cnorm_i: Vec<Interval>,
    mu_i: Vec<Vec<Interval>>,
    deadline: Instant,
    trace: bool,
}

impl Engine {
    fn build(ms: &MarketSplit, deadline: Instant, trace: bool) -> Option<Engine> {
        let (n, m) = (ms.n, ms.m);
        // A as BigInt (m × n).
        let abig: Vec<Vec<BigInt>> =
            ms.a.iter()
                .map(|row| row.iter().map(|&v| BigInt::from(v)).collect())
                .collect();
        let (u, rank, hh) = col_hnf(&abig, m, n, deadline)?;
        if rank != m {
            return None; // rank-deficient equality system: out of scope
        }
        let dim = n - rank;
        if dim == 0 {
            return None;
        }
        // Raw kernel = columns rank..n of U (exact BigInt — A·U = [H|0] makes
        // every such column an exact kernel vector). LLL in BigInt so no integer
        // overflow can ever corrupt the lattice; the reduced result is tiny.
        let mut k0: Vec<Vec<BigInt>> = Vec::with_capacity(dim);
        for t in 0..dim {
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(u[i][rank + t].clone());
            }
            k0.push(v);
        }
        let kbig = lll(k0, deadline)?;
        // Convert the reduced basis to i64 (entries are ~unit; bail if not) and
        // VERIFY it still lies exactly in the kernel (defence against any bug).
        let mut k: Vec<Vec<i64>> = Vec::with_capacity(dim);
        for v in &kbig {
            let mut row = Vec::with_capacity(n);
            for e in v {
                row.push(e.to_i64()?);
            }
            k.push(row);
        }
        for t in 0..dim {
            for i in 0..m {
                let mut s = BigInt::zero();
                for kk in 0..n {
                    s += BigInt::from(ms.a[i][kk]) * BigInt::from(k[t][kk]);
                }
                if !s.is_zero() {
                    return None; // reduced vector left the kernel: refuse to trust it
                }
            }
        }
        // Exact GSO of the reduced basis.
        let (bstar_q, cnorm_q, mu_q) = gso_exact(&k);
        let cnorm_i: Vec<Interval> = cnorm_q
            .iter()
            .map(Interval::from_rational)
            .collect::<Option<_>>()?;
        if cnorm_i.iter().any(|v| v.lo <= 0.0) {
            return None;
        }
        let mu_i: Vec<Vec<Interval>> = mu_q
            .iter()
            .map(|r| {
                r.iter()
                    .map(Interval::from_rational)
                    .collect::<Option<Vec<_>>>()
            })
            .collect::<Option<_>>()?;
        if trace {
            let norms: Vec<BigInt> = k
                .iter()
                .map(|v| v.iter().map(|&x| BigInt::from(x) * BigInt::from(x)).sum())
                .collect();
            let nrm: BigInt = norms.iter().cloned().sum();
            let mx = norms.into_iter().max().unwrap_or_else(BigInt::zero);
            eprintln!(
                "AY_MILP_TRACE lattice: kernel dim {dim}, LLL basis Σ‖·‖²={nrm} max‖·‖²={mx}"
            );
        }
        Some(Engine {
            n,
            k,
            dim,
            u,
            hh,
            rank,
            bstar_q,
            cnorm_q,
            cnorm_i,
            mu_i,
            deadline,
            trace,
        })
    }

    /// Solve `A x = d` for an integer `x` (or `None` if no integer solution).
    /// Uses `A·U = [H|0]`: solve `H z = d`, then `x = U·[z;0]`.
    fn particular(&self, ms: &MarketSplit, d: &[i64]) -> Option<Vec<BigInt>> {
        if Instant::now() >= self.deadline {
            return None;
        }
        let m = ms.m;
        let r = self.rank;
        // Augmented [H | d] over BigRational, Gaussian elimination.
        let mut hf: Vec<Vec<BigRational>> = (0..m)
            .map(|i| {
                let mut row: Vec<BigRational> = (0..r)
                    .map(|j| BigRational::from(self.hh[i][j].clone()))
                    .collect();
                row.push(BigRational::from(BigInt::from(d[i])));
                row
            })
            .collect();
        let mut piv: Vec<(usize, usize)> = Vec::new();
        let mut pr = 0usize;
        for c in 0..r {
            if Instant::now() >= self.deadline {
                return None;
            }
            let prow = (pr..m).find(|&i| !hf[i][c].is_zero());
            let Some(prow) = prow else { continue };
            hf.swap(pr, prow);
            let pv = hf[pr][c].clone();
            for x in &mut hf[pr] {
                *x /= &pv;
            }
            for i in 0..m {
                if i != pr && !hf[i][c].is_zero() {
                    let f = hf[i][c].clone();
                    for k in 0..=r {
                        let t = &f * &hf[pr][k];
                        hf[i][k] -= t;
                    }
                }
            }
            piv.push((pr, c));
            pr += 1;
        }
        // Consistency: a zero row with nonzero rhs ⟹ no solution.
        for i in 0..m {
            if (0..r).all(|c| hf[i][c].is_zero()) && !hf[i][r].is_zero() {
                return None;
            }
        }
        let mut z1 = vec![BigRational::zero(); r];
        for &(pri, c) in &piv {
            z1[c] = hf[pri][r].clone();
        }
        // z must be integral.
        if z1.iter().any(|v| !v.is_integer()) {
            return None;
        }
        let z: Vec<BigInt> = z1
            .iter()
            .map(|v| v.to_integer())
            .chain(std::iter::repeat(BigInt::zero()).take(self.n - r))
            .collect();
        // x = U · [z; 0].
        let mut x = vec![BigInt::zero(); self.n];
        for i in 0..self.n {
            let mut s = BigInt::zero();
            for j in 0..self.n {
                if !z[j].is_zero() {
                    s += &self.u[i][j] * &z[j];
                }
            }
            x[i] = s;
        }
        Some(x)
    }

    /// Babai nearest-plane: reduce `x_d` modulo the reduced lattice so its entries
    /// are small. Exact (`BigRational` GSO) — the raw `x_d` has ~1e31 entries.
    fn babai(&self, xd: &[BigInt]) -> Option<Vec<i64>> {
        if Instant::now() >= self.deadline {
            return None;
        }
        let mut x: Vec<BigRational> = xd.iter().map(|v| BigRational::from(v.clone())).collect();
        for i in (0..self.dim).rev() {
            if i & 7 == 0 && Instant::now() >= self.deadline {
                return None;
            }
            // c_i = <x, b*_i> / cnorm_i
            let mut num = BigRational::zero();
            for kk in 0..self.n {
                if !self.bstar_q[i][kk].is_zero() {
                    num += &x[kk] * &self.bstar_q[i][kk];
                }
            }
            let ci = &num / &self.cnorm_q[i];
            let q = round_rat(&ci);
            if !q.is_zero() {
                let qr = BigRational::from(q);
                for kk in 0..self.n {
                    let t = &qr * BigRational::from(BigInt::from(self.k[i][kk]));
                    x[kk] -= t;
                }
            }
        }
        // Now integral and small.
        // "Small after Babai" is a performance expectation, not a proof
        // premise.  An alien but structurally matching model may remain wider
        // than i64; decline it instead of panicking or truncating.
        x.iter().map(|v| v.to_integer().to_i64()).collect()
    }

    /// Enumerate integer `y` with `x = x_d + K y ∈ {0,1}^n`, stopping at the
    /// first such `x`. Returns `Feasible(y)` if a valid point exists, `Empty` if
    /// the ball is provably empty (full enumeration), or `Aborted` on
    /// budget/deadline.
    fn enumerate(&self, xd: &[i64]) -> EnumResult {
        let n = self.n;
        let dim = self.dim;
        let r2 = n as f64 / 4.0;
        // τ = ½·1 − x_d ; exact GSO coords
        // tg_i = <τ, b*_i>/cnorm_i, then outward-enclose each rational once.
        // Starting from exact tg avoids a long dot-product interval and keeps
        // the hot enumeration intervals narrow.
        let half = BigRational::new(BigInt::one(), BigInt::from(2));
        let tau: Vec<BigRational> = xd
            .iter()
            .map(|&x| &half - BigRational::from(BigInt::from(x)))
            .collect();
        let mut tg = Vec::with_capacity(dim);
        for i in 0..dim {
            let mut dot = BigRational::zero();
            for (t, b) in tau.iter().zip(&self.bstar_q[i]) {
                if !t.is_zero() && !b.is_zero() {
                    dot += t * b;
                }
            }
            let q = dot / &self.cnorm_q[i];
            let Some(iv) = Interval::from_rational(&q) else {
                return EnumResult::Aborted;
            };
            tg.push(iv);
        }
        let zero = Interval { lo: 0.0, hi: 0.0 };
        let mut st = EnumState {
            eng: self,
            xd,
            tg,
            radius: r2,
            y: vec![0i64; dim],
            // Row `level` holds Σ_{j>level} y_j μ[j][k] for k≤level.
            // A child row is overwritten from its immutable parent row for
            // every candidate, so interval widths never grow from add/subtract
            // restoration roundoff.
            partial: vec![vec![zero; dim]; dim],
            nodes: 0,
            aborted: false,
        };
        let found = st.rec(dim - 1, zero);
        if st.aborted {
            EnumResult::Aborted
        } else if let Some(y) = found {
            EnumResult::Feasible(y)
        } else {
            EnumResult::Empty
        }
    }

    /// Run the whole proof and, on success, build the exact `Outcome::Optimal`.
    fn prove(&self, model: &Model, ms: &MarketSplit) -> Option<Outcome> {
        // Objective-0 face: A x = b.
        let xd0 = self.particular(ms, &ms.b)?;
        let xd0 = self.babai(&xd0)?;
        let (opt, witness_y, witness_xd) = match self.enumerate(&xd0) {
            EnumResult::Feasible(y) => (0i64, y, xd0),
            EnumResult::Aborted => return None,
            EnumResult::Empty => {
                if self.trace {
                    eprintln!("AY_MILP_TRACE lattice: objective-0 face PROVEN EMPTY — optimum ≥ 1");
                }
                // optimum ≥ 1: look for a value-1 witness on a b−e_k face.
                let mut found: Option<(i64, Vec<i64>, Vec<i64>)> = None;
                for k in 0..ms.m {
                    let mut d = ms.b.clone();
                    d[k] = d[k].checked_sub(1)?;
                    let Some(xdk) = self.particular(ms, &d) else {
                        continue;
                    };
                    let xdk = self.babai(&xdk)?;
                    match self.enumerate(&xdk) {
                        EnumResult::Feasible(y) => {
                            if self.trace {
                                eprintln!(
                                    "AY_MILP_TRACE lattice: b−e_{k} face FEASIBLE — optimum = 1 witness"
                                );
                            }
                            found = Some((1, y, xdk));
                            break;
                        }
                        EnumResult::Aborted => return None,
                        EnumResult::Empty => {}
                    }
                }
                let (o, y, xd) = found?; // all faces empty ⟹ optimum ≥ 2: hand back
                (o, y, xd)
            }
        };
        // Reconstruct the binary assignment x = x_d + K·y.
        let mut xbin = vec![0i64; self.n];
        for kk in 0..self.n {
            let mut s = witness_xd[kk];
            for t in 0..self.dim {
                if witness_y[t] != 0 {
                    s = s.checked_add(witness_y[t].checked_mul(self.k[t][kk])?)?;
                }
            }
            xbin[kk] = s;
            debug_assert!(s == 0 || s == 1, "witness not 0/1");
        }
        // Build the full exact model point: binaries, slacks (= b_i − a_i·x),
        // fixed columns at their fixed value.
        let nc = model.num_cols();
        let mut point = vec![BigRational::zero(); nc];
        let mut bin_val = vec![0i64; nc];
        for (kk, &j) in ms.bin_cols.iter().enumerate() {
            point[j] = BigRational::from(BigInt::from(xbin[kk]));
            bin_val[j] = xbin[kk];
        }
        for i in 0..ms.m {
            // slack_i = b_i − a_i·x   (≥ 0 integer)
            let mut ax = BigInt::zero();
            for kk in 0..self.n {
                ax += BigInt::from(ms.a[i][kk]) * BigInt::from(xbin[kk]);
            }
            let s = BigInt::from(ms.b[i]) - ax;
            if s.is_negative() {
                return None;
            }
            point[ms.slack_col[i]] = BigRational::from(s);
        }
        // Fixed columns and any untouched column: use the model's fixed value.
        for j in 0..nc {
            if point[j].is_zero() {
                let (l, u) = model.col_bounds(Col(j as u32));
                if l == u && l != 0.0 {
                    point[j] = exact(l)?;
                }
            }
        }
        // Belt: the witness must survive an independent exact re-check.
        if model.check_point(&point).is_err() {
            if self.trace {
                eprintln!(
                    "AY_MILP_TRACE lattice: witness rejected by check_point — aborting device"
                );
            }
            return None;
        }
        let value = model.objective_value_at(&point);
        if self.trace {
            eprintln!("AY_MILP_TRACE lattice: PROVEN OPTIMAL {opt} (value {value})");
        }
        Some(Outcome::Optimal {
            value,
            model_values: point,
            cert: None,
        })
    }
}

enum EnumResult {
    Feasible(Vec<i64>),
    Empty,
    Aborted,
}

struct EnumState<'a> {
    eng: &'a Engine,
    xd: &'a [i64],
    tg: Vec<Interval>,
    radius: f64,
    y: Vec<i64>,
    partial: Vec<Vec<Interval>>,
    nodes: u64,
    aborted: bool,
}

impl EnumState<'_> {
    /// Recursion over kernel coordinate `level` (dim−1 … 0). `dist_above` is the
    /// outward interval for the squared distance accumulated by already-fixed
    /// higher coordinates.
    fn rec(&mut self, level: usize, dist_above: Interval) -> Option<Vec<i64>> {
        if self.aborted {
            return None;
        }
        let eng = self.eng;
        let cnorm = eng.cnorm_i[level];
        let Some(e) = self.tg[level].sub(self.partial[level][level]) else {
            self.aborted = true;
            return None;
        };
        // Exact remaining radius is at most `radius - dist_above.lo`.
        // Use that upper enclosure and the norm's positive LOWER endpoint to
        // obtain a conservative coordinate width.
        let rem_hi = (self.radius - dist_above.lo).next_up();
        if rem_hi < 0.0 {
            return None;
        }
        let q = (rem_hi / cnorm.lo).next_up();
        let w = q.sqrt().next_up();
        let lo_f = (e.lo - w).next_down().ceil();
        let hi_f = (e.hi + w).next_up().floor();
        // Integers past 2^53 do not have exact f64 representations, so the hot
        // interval updates could not use them soundly.  Abort rather than cast
        // or silently skip such a coordinate.
        const MAX_EXACT_F64_INT: f64 = 9_007_199_254_740_992.0;
        if !q.is_finite()
            || !w.is_finite()
            || !lo_f.is_finite()
            || !hi_f.is_finite()
            || lo_f < -MAX_EXACT_F64_INT
            || hi_f > MAX_EXACT_F64_INT
        {
            self.aborted = true;
            return None;
        }
        let lo = lo_f as i64;
        let hi = hi_f as i64;
        if lo > hi {
            return None;
        }
        for yi in lo..=hi {
            let yi_i = Interval {
                lo: yi as f64,
                hi: yi as f64,
            };
            let Some(d) = yi_i
                .sub(e)
                .and_then(Interval::square)
                .and_then(|v| v.mul_nonnegative(cnorm))
                .and_then(|v| dist_above.add(v))
            else {
                self.aborted = true;
                return None;
            };
            // Only a lower enclosure strictly beyond the exact sphere may
            // prune.  Equality belongs to the 0/1 sphere and is retained.
            if d.lo > self.radius {
                continue;
            }
            self.nodes += 1;
            if self.nodes >= NODE_BUDGET {
                self.aborted = true;
                return None;
            }
            if self.nodes % (1 << 22) == 0 && Instant::now() >= eng.deadline {
                self.aborted = true;
                return None;
            }
            self.y[level] = yi;
            if level == 0 {
                match self.box_ok() {
                    Some(true) => return Some(self.y.clone()),
                    Some(false) => {}
                    None => {
                        self.aborted = true;
                        return None;
                    }
                }
            } else {
                // Push y_level into the lower centers, overwriting the child
                // row from this level's unchanged parent row.
                let mu = &eng.mu_i[level];
                for k in 0..level {
                    let Some(term) = mu[k].scale(yi as f64) else {
                        self.aborted = true;
                        return None;
                    };
                    let Some(next) = self.partial[level][k].add(term) else {
                        self.aborted = true;
                        return None;
                    };
                    self.partial[level - 1][k] = next;
                }
                let hit = self.rec(level - 1, d);
                if hit.is_some() {
                    return hit;
                }
                if self.aborted {
                    return None;
                }
            }
        }
        None
    }

    /// Exact integer box check for the fully-assigned `y`: `x = x_d + K y ∈ {0,1}^n`.
    fn box_ok(&self) -> Option<bool> {
        let eng = self.eng;
        for k in 0..eng.n {
            let mut xk = self.xd[k];
            for t in 0..eng.dim {
                let yt = self.y[t];
                if yt != 0 {
                    xk = xk.checked_add(yt.checked_mul(eng.k[t][k])?)?;
                }
            }
            if xk < 0 || xk > 1 {
                return Some(false);
            }
        }
        Some(true)
    }
}

// ---------------------------------------------------------------------------
// Exact integer linear algebra (column-HNF, LLL, GSO) — all one-time, tiny.
// ---------------------------------------------------------------------------

/// Column-Hermite-normal-form of `a` (m×n) with unimodular tracking. Returns
/// `(U, rank, M)` with `A·U = M = [H | 0]`; columns `rank..n` of `U` span the
/// SATURATED integer kernel of `A`.
fn col_hnf(
    a: &[Vec<BigInt>],
    m: usize,
    n: usize,
    deadline: Instant,
) -> Option<(Vec<Vec<BigInt>>, usize, Vec<Vec<BigInt>>)> {
    let mut mm: Vec<Vec<BigInt>> = a.to_vec(); // m × n
    let mut u: Vec<Vec<BigInt>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    if i == j {
                        BigInt::one()
                    } else {
                        BigInt::zero()
                    }
                })
                .collect()
        })
        .collect(); // n × n
    let mut r = 0usize;
    for i in 0..m {
        loop {
            if Instant::now() >= deadline {
                return None;
            }
            // nonzero columns of row i among [r..n)
            let nz: Vec<usize> = (r..n).filter(|&c| !mm[i][c].is_zero()).collect();
            if nz.is_empty() {
                break;
            }
            // pivot = smallest |value|
            let p = *nz
                .iter()
                .min_by(|&&x, &&y| mm[i][x].magnitude().cmp(mm[i][y].magnitude()))
                .expect("nonempty");
            if p != r {
                col_swap(&mut mm, &mut u, p, r);
            }
            for c in (r + 1)..n {
                if !mm[i][c].is_zero() {
                    let q = &mm[i][c] / &mm[i][r];
                    if !q.is_zero() {
                        col_add(&mut mm, &mut u, c, r, &(-q));
                    }
                }
            }
            if (r + 1..n).all(|c| mm[i][c].is_zero()) {
                break;
            }
        }
        if !mm[i][r].is_zero() {
            if mm[i][r].is_negative() {
                col_neg(&mut mm, &mut u, r);
            }
            r += 1;
            if r == n {
                break;
            }
        }
    }
    Some((u, r, mm))
}

fn col_swap(mm: &mut [Vec<BigInt>], u: &mut [Vec<BigInt>], a: usize, b: usize) {
    for row in mm.iter_mut() {
        row.swap(a, b);
    }
    for row in u.iter_mut() {
        row.swap(a, b);
    }
}

/// column `dst += k · column src`
fn col_add(mm: &mut [Vec<BigInt>], u: &mut [Vec<BigInt>], dst: usize, src: usize, k: &BigInt) {
    for row in mm.iter_mut() {
        let t = &row[src] * k;
        row[dst] += t;
    }
    for row in u.iter_mut() {
        let t = &row[src] * k;
        row[dst] += t;
    }
}

fn col_neg(mm: &mut [Vec<BigInt>], u: &mut [Vec<BigInt>], a: usize) {
    for row in mm.iter_mut() {
        row[a] = -std::mem::take(&mut row[a]);
    }
    for row in u.iter_mut() {
        row[a] = -std::mem::take(&mut row[a]);
    }
}

/// Float-guided LLL (δ = 0.99) over EXACT `BigInt` vectors. Only the GSO
/// decisions use `f64`; the lattice is preserved bit-exactly by unimodular
/// integer operations (no fixed-width overflow possible), so reduction quality
/// — not soundness — is all that depends on the float arithmetic.
fn lll(mut basis: Vec<Vec<BigInt>>, deadline: Instant) -> Option<Vec<Vec<BigInt>>> {
    let nb = basis.len();
    if nb == 0 {
        return Some(basis);
    }
    let dim = basis[0].len();
    let delta = 0.99f64;
    // GSO in f64 (from the exact vectors).  This controls reduction quality
    // only, but NaN/overflow could make the swap loop cycle forever; decline
    // any non-finite guidance rather than treating it as zero.
    let gso = |b: &[Vec<BigInt>]| -> Option<(Vec<Vec<f64>>, Vec<f64>)> {
        let mut bs: Vec<Vec<f64>> = Vec::with_capacity(nb);
        let mut mu = vec![vec![0.0f64; nb]; nb];
        for i in 0..nb {
            let bi: Vec<f64> = b[i]
                .iter()
                .map(|x| x.to_f64().filter(|v| v.is_finite()))
                .collect::<Option<_>>()?;
            let mut v = bi.clone();
            for j in 0..i {
                let dj: f64 = bs[j].iter().map(|x| x * x).sum();
                let dot: f64 = bi.iter().zip(&bs[j]).map(|(a, b)| a * b).sum();
                if !dj.is_finite() || dj <= 0.0 || !dot.is_finite() {
                    return None;
                }
                mu[i][j] = dot / dj;
                if !mu[i][j].is_finite() {
                    return None;
                }
                for k in 0..dim {
                    v[k] -= mu[i][j] * bs[j][k];
                    if !v[k].is_finite() {
                        return None;
                    }
                }
            }
            bs.push(v);
        }
        let norm: Vec<f64> = (0..nb).map(|i| bs[i].iter().map(|x| x * x).sum()).collect();
        if norm.iter().any(|v| !v.is_finite() || *v <= 0.0) {
            return None;
        }
        Some((mu, norm))
    };
    let (mut mu, mut norm) = gso(&basis)?;
    let mut k = 1usize;
    let mut rounds = 0u64;
    while k < nb {
        rounds += 1;
        if rounds >= 1_000_000 || (rounds & 1023 == 0 && Instant::now() >= deadline) {
            return None;
        }
        for j in (0..k).rev() {
            if mu[k][j].abs() > 0.5 {
                let q = mu[k][j].round();
                if q != 0.0 {
                    // Every integer row operation preserves the lattice, but a
                    // saturating float→i64 cast would not apply the chosen q.
                    if !q.is_finite() || q.abs() >= 9_223_372_036_854_775_808.0 {
                        return None;
                    }
                    let qi = BigInt::from(q as i64);
                    for t in 0..dim {
                        let sub = &qi * &basis[j][t];
                        basis[k][t] -= sub;
                    }
                    let g = gso(&basis)?;
                    mu = g.0;
                    norm = g.1;
                }
            }
        }
        if norm[k] >= (delta - mu[k][k - 1] * mu[k][k - 1]) * norm[k - 1] {
            k += 1;
        } else {
            basis.swap(k, k - 1);
            let g = gso(&basis)?;
            mu = g.0;
            norm = g.1;
            k = k.max(2) - 1;
        }
    }
    Some(basis)
}

/// Exact Gram–Schmidt of an integer basis. Returns orthogonal vectors `b*`,
/// their squared norms, and `μ[i][j]` (i>j).
#[allow(clippy::type_complexity)]
fn gso_exact(
    basis: &[Vec<i64>],
) -> (
    Vec<Vec<BigRational>>,
    Vec<BigRational>,
    Vec<Vec<BigRational>>,
) {
    let nb = basis.len();
    let dim = basis[0].len();
    let mut bs: Vec<Vec<BigRational>> = Vec::with_capacity(nb);
    let mut cnorm: Vec<BigRational> = Vec::with_capacity(nb);
    let mut mu = vec![vec![BigRational::zero(); nb]; nb];
    for i in 0..nb {
        let bi: Vec<BigRational> = basis[i]
            .iter()
            .map(|&x| BigRational::from(BigInt::from(x)))
            .collect();
        let mut v = bi.clone();
        for j in 0..i {
            let mut dot = BigRational::zero();
            for k in 0..dim {
                if !bi[k].is_zero() && !bs[j][k].is_zero() {
                    dot += &bi[k] * &bs[j][k];
                }
            }
            let m = &dot / &cnorm[j];
            for k in 0..dim {
                let t = &m * &bs[j][k];
                v[k] -= t;
            }
            mu[i][j] = m;
        }
        let mut nrm = BigRational::zero();
        for k in 0..dim {
            if !v[k].is_zero() {
                nrm += &v[k] * &v[k];
            }
        }
        bs.push(v);
        cnorm.push(nrm);
    }
    (bs, cnorm, mu)
}

/// Round a rational to the nearest integer (`floor(r + ½)`; ties up — irrelevant
/// to Babai correctness, which only needs *a* nearby lattice vector). `denom` is
/// always positive in `BigRational`, so `div_floor` gives the true floor.
fn round_rat(r: &BigRational) -> BigInt {
    use num_integer::Integer;
    let two = BigInt::from(2);
    let num = r.numer() * &two + r.denom();
    let den = r.denom() * &two;
    num.div_floor(&den)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Col, Model, Sense};
    use std::time::Duration;

    /// Build a market-split min-total-slack model: `A x + s = b`, `min Σ s_i`,
    /// `x ∈ {0,1}^n`, `s ≥ 0` — the markshare1 shape in miniature.
    fn market_split(a: &[Vec<i64>], b: &[i64]) -> Model {
        let n = a[0].len();
        let mut m = Model::new();
        let x: Vec<Col> = (0..n).map(|_| m.add_binary_col()).collect();
        let s: Vec<Col> = (0..a.len())
            .map(|_| m.add_col(0.0, f64::INFINITY))
            .collect();
        for (i, row) in a.iter().enumerate() {
            let mut terms: Vec<(Col, f64)> = row
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c != 0)
                .map(|(j, &c)| (x[j], c as f64))
                .collect();
            terms.push((s[i], 1.0));
            m.add_row(b[i] as f64, b[i] as f64, &terms);
        }
        let obj: Vec<(Col, f64)> = s.iter().map(|&c| (c, 1.0)).collect();
        m.set_objective(&obj, Sense::Minimize);
        m
    }

    fn deadline() -> Instant {
        Instant::now() + Duration::from_secs(30)
    }

    fn assert_encloses(iv: Interval, exact: &BigRational) {
        let lo = BigRational::from_float(iv.lo).expect("finite lower endpoint");
        let hi = BigRational::from_float(iv.hi).expect("finite upper endpoint");
        assert!(
            lo <= *exact && *exact <= hi,
            "interval [{}, {}] does not enclose {exact}",
            iv.lo,
            iv.hi,
        );
    }

    /// Pin the directed-arithmetic premise independently of the lattice
    /// search: conversions and every hot-loop operation must enclose the same
    /// calculation performed over exact rationals.
    #[test]
    fn interval_operations_enclose_exact_rationals() {
        let vals: Vec<BigRational> = (-24..=24)
            .flat_map(|n| (1..=11).map(move |d| BigRational::new(n.into(), d.into())))
            .collect();
        for (i, a) in vals.iter().enumerate() {
            let ai = Interval::from_rational(a).expect("finite interval");
            assert_encloses(ai, a);
            assert_encloses(ai.square().expect("finite square"), &(a * a));

            let scalar = (i as i64 % 13) - 6;
            let scaled = a * BigRational::from_integer(scalar.into());
            assert_encloses(ai.scale(scalar as f64).expect("finite scale"), &scaled);

            let b = &vals[(i * 37 + 17) % vals.len()];
            let bi = Interval::from_rational(b).expect("finite interval");
            assert_encloses(ai.add(bi).expect("finite sum"), &(a + b));
            assert_encloses(ai.sub(bi).expect("finite difference"), &(a - b));

            let ap = a.abs();
            let bp = b.abs();
            let api = Interval::from_rational(&ap).expect("finite positive interval");
            let bpi = Interval::from_rational(&bp).expect("finite positive interval");
            assert_encloses(
                api.mul_nonnegative(bpi).expect("finite product"),
                &(ap * bp),
            );
        }
    }

    #[test]
    fn optimum_one_when_zero_face_is_empty() {
        // Row0: Σx = 2 (exactly two ones); Row1: 0·x0+1·x1+2·x2+3·x3 = 6.
        // No two-subset reaches 6 (max 5) ⟹ objective-0 face EMPTY. But b−e_1
        // = [2,5] is met by x=(0,0,1,1) ⟹ optimum = 1.
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let m = market_split(&a, &b);
        match try_prove(&m, deadline()) {
            Some(Outcome::Optimal {
                value,
                model_values,
                ..
            }) => {
                assert_eq!(value, BigRational::from(BigInt::from(1)));
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 1, got {other:?}"),
        }
    }

    #[test]
    fn optimum_zero_when_a_split_exists() {
        // Two independent parity rows, each satisfiable ⟹ objective-0 face
        // NONEMPTY (e.g. x=(1,0,1,0)) ⟹ optimum = 0.
        let a = vec![vec![1, 1, 0, 0], vec![0, 0, 1, 1]];
        let b = vec![1, 1];
        let m = market_split(&a, &b);
        match try_prove(&m, deadline()) {
            Some(Outcome::Optimal {
                value,
                model_values,
                ..
            }) => {
                assert_eq!(value, BigRational::from(BigInt::from(0)));
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 0, got {other:?}"),
        }
    }

    #[test]
    fn kill_switch_disables_the_device() {
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let m = market_split(&a, &b);
        let out = try_prove_configured(&m, deadline(), true);
        assert!(out.is_none(), "kill switch must disable the device");
    }

    #[test]
    fn does_not_fire_on_maximize() {
        let mut m = market_split(&[vec![1, 1, 1, 1], vec![0, 1, 2, 3]], &[2, 6]);
        // flip to Maximize: out of the family.
        let s0 = m.col_at(4).unwrap();
        let s1 = m.col_at(5).unwrap();
        m.set_objective(&[(s0, 1.0), (s1, 1.0)], Sense::Maximize);
        assert!(detect(&m).is_none());
    }

    #[test]
    fn does_not_fire_on_inequality_rows() {
        // A pure covering model (≤ rows, no equality slack structure).
        let mut m = Model::new();
        let x: Vec<Col> = (0..4).map(|_| m.add_binary_col()).collect();
        m.add_row(f64::NEG_INFINITY, 2.0, &[(x[0], 1.0), (x[1], 1.0)]);
        m.add_row(f64::NEG_INFINITY, 2.0, &[(x[2], 1.0), (x[3], 1.0)]);
        m.set_objective(&[(x[0], 1.0)], Sense::Minimize);
        assert!(detect(&m).is_none());
    }

    #[test]
    fn recovers_original_system_under_row_scaling() {
        // The reader halves rows whose largest entry exceeds 1024. Emulate it by
        // hand: a row scaled by ½ must still be detected and solved correctly.
        let a = vec![vec![1, 1, 1, 1], vec![0, 1, 2, 3]];
        let b = vec![2, 6];
        let mut m = Model::new();
        let x: Vec<Col> = (0..4).map(|_| m.add_binary_col()).collect();
        let s: Vec<Col> = (0..2).map(|_| m.add_col(0.0, f64::INFINITY)).collect();
        for (i, row) in a.iter().enumerate() {
            // scale the whole row (coeffs + rhs + slack) by ½.
            let mut terms: Vec<(Col, f64)> = row
                .iter()
                .enumerate()
                .filter(|&(_, &c)| c != 0)
                .map(|(j, &c)| (x[j], c as f64 * 0.5))
                .collect();
            terms.push((s[i], 0.5));
            m.add_row(b[i] as f64 * 0.5, b[i] as f64 * 0.5, &terms);
        }
        m.set_objective(&[(s[0], 1.0), (s[1], 1.0)], Sense::Minimize);
        let ms = detect(&m).expect("detect under ½ scaling");
        assert_eq!(ms.a, a);
        assert_eq!(ms.b, b);
    }

    /// The lower-bound proof needs an EXACT integer normalized system.  A
    /// near-integer coefficient is not licensed by a tolerance: Σs would no
    /// longer be integer, so "zero face empty => optimum >= 1" would be false.
    #[test]
    fn declines_near_integer_normalization() {
        let mut m = Model::new();
        let x0 = m.add_binary_col();
        let x1 = m.add_binary_col();
        let s = m.add_col(0.0, f64::INFINITY);
        let near_two = 2.0 + f64::EPSILON * 2.0;
        m.add_row(3.0, 3.0, &[(x0, near_two), (x1, 2.0), (s, 1.0)]);
        m.set_objective(&[(s, 1.0)], Sense::Minimize);
        assert!(detect(&m).is_none());
    }

    /// Side-store models must be classified from their true rationals, not the
    /// rounded advice matrix.  Until the lattice compiler consumes those exact
    /// accessors directly it declines the device.
    #[test]
    fn declines_exact_side_store_models() {
        let mut m = market_split(&[vec![2, 2, 5]], &[3]);
        let row = m.row_at(0).expect("row");
        let x0 = m.col_at(0).expect("column");
        m.record_inexact_row_coeff(row, x0.0, BigRational::from_integer(3.into()));
        assert!(detect(&m).is_none());
    }

    /// Differential completeness check for the outward interval enumeration.
    /// Whenever the device elects to speak, its optimum must match exhaustive
    /// 0/1 enumeration of the same small integer market-split model.
    #[test]
    fn small_random_lattice_results_match_exhaustive_optimum() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut rnd = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _case in 0..160 {
            let n = 4 + (rnd() % 4) as usize;
            let rows = 1 + (rnd() % 3) as usize;
            let mut a = vec![vec![0i64; n]; rows];
            let mut b = vec![0i64; rows];
            for i in 0..rows {
                for j in 0..n {
                    a[i][j] = (rnd() % 6) as i64;
                }
                // Keep at least two nonzeros so the detector's premise holds.
                a[i][0] = a[i][0].max(1);
                a[i][1] = a[i][1].max(1);
                b[i] = (rnd() % (a[i].iter().sum::<i64>() as u64 + 1)) as i64;
            }
            let model = market_split(&a, &b);
            let mut best: Option<i64> = None;
            for mask in 0..(1usize << n) {
                let mut total = 0i64;
                let mut feasible = true;
                for i in 0..rows {
                    let ax: i64 = (0..n)
                        .filter(|&j| mask & (1usize << j) != 0)
                        .map(|j| a[i][j])
                        .sum();
                    if ax > b[i] {
                        feasible = false;
                        break;
                    }
                    total += b[i] - ax;
                }
                if feasible {
                    best = Some(best.map_or(total, |old| old.min(total)));
                }
            }
            if let Some(Outcome::Optimal { value, .. }) = try_prove(&model, deadline()) {
                assert_eq!(
                    value,
                    BigRational::from_integer(BigInt::from(best.expect("lattice witness"))),
                    "mismatch for A={a:?}, b={b:?}"
                );
            }
        }
    }
}
