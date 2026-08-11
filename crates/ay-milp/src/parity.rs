// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EXACT GF(2) decision for the "lights-out" parity family (enlight*).
//!
//! ## The instance the LP cannot touch
//!
//! `enlight_hard` is a 10×10 lights-out puzzle: 100 binaries `x#i#j` (press
//! button `(i,j)`), 100 nonneg integer slacks `y#i#j`, and 100 EQUALITY rows,
//! one per cell:
//!
//! ```text
//!     Σ_{(i,j)∈cross(r)} x_{ij}  −  2·y_r  =  c_r        (c_r ∈ {0, −1})
//! ```
//!
//! i.e. the number of presses toggling cell `r` must have a fixed PARITY. The
//! objective minimises `Σ x` (total presses). The LP relaxation puts the `x` at
//! fractional values, hits every equality with a fractional `y`, and gives a
//! bound far below the integer optimum (37); LP-diving/rounding never lands on
//! the parity-exact assignment, so AY finds NO feasible point and returns
//! UNKNOWN — while the structure is a *linear system over GF(2)* that Gaussian
//! elimination decides in microseconds.
//!
//! ## The exact reduction (and why it is sound)
//!
//! With `y_r ≥ 0` integer and UNBOUNDED above, and every `x`-coefficient a
//! NONNEGATIVE integer with `c_r ≤ 0`:
//!
//!   * **MILP-feasible ⟹ GF(2)-solvable.** In any feasible point,
//!     `Σ a_j x_j = c_r + 2 y_r`, so `Σ (a_j mod 2) x_j ≡ c_r (mod 2)`. This
//!     needs NOTHING about signs — `2 y_r ≡ 0`. Hence if the GF(2) system is
//!     INCONSISTENT, the MILP is INFEASIBLE (proves enlight4 / enlight9).
//!   * **GF(2)-solvable ⟹ MILP-feasible.** Given a 0/1 `x` with the row parities
//!     right, set `y_r = (Σ a_j x_j − c_r)/2`. It is an integer (parity) and
//!     `≥ 0` because `Σ a_j x_j ≥ 0 ≥ c_r`. So every GF(2) solution is a genuine
//!     MILP point.
//!
//! Because the `y` contribute 0 to the objective, minimising the model objective
//! over MILP-feasible points equals minimising `Σ obj_j x_j` over the (affine)
//! GF(2) solution set. So:
//!
//!   * inconsistent            ⟹  INFEASIBLE;
//!   * unique solution (nullity 0) or a small enumerable kernel ⟹ OPTIMAL, the
//!     min-objective solution over the whole affine set (proves enlight_hard = 37,
//!     whose kernel is trivial — the solution is unique);
//!   * a large kernel          ⟹  return one FEASIBLE point (still beats UNKNOWN).
//!
//! ## Exactness / fail-closed
//!
//! Detection reads only exactly-representable coefficients (`exact`, declines any
//! model with rational overrides). The linear algebra is pure GF(2) bit work
//! (no floating point). Every returned point is independently re-checked by a
//! deadline-polled exact scan of every public column, row, and objective term;
//! any structural doubt returns `None` and hands the model straight to the
//! normal search. Deadline expiry returns `Unknown::Timeout`, never a late
//! verdict. Kill switch: `AY_MILP_NO_PARITY`.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use std::cell::{Cell, RefCell};
use std::time::Instant;

use crate::model::{exact, Col, Model, Row, Sense};
use crate::outcome::{Outcome, UnknownReason};

/// A source-model GF(2) contradiction.
///
/// Adding the named equality rows gives an even coefficient for every model
/// column and an odd right-hand side.  Since every column is integral, the
/// resulting equality would equate an even integer with an odd integer.  The
/// row list is deliberately the whole artifact: the independent checker
/// re-reads every coefficient and the column kinds from the source model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParityInfeasibilityCertificate {
    rows: Vec<u32>,
}

impl ParityInfeasibilityCertificate {
    pub(crate) fn from_rows(rows: Vec<u32>) -> Self {
        Self { rows }
    }

    pub(crate) fn rows(&self) -> &[u32] {
        &self.rows
    }
}

thread_local! {
    /// Typed evidence produced below the public branch-and-bound return type.
    /// Like the replay ledger, this is thread-local and is drained by the
    /// session that owns the solve, so one solve cannot lend evidence to the
    /// next one.
    static PENDING_INFEASIBILITY_CERTIFICATE:
        RefCell<Option<ParityInfeasibilityCertificate>> = const { RefCell::new(None) };
}

pub(crate) fn clear_pending_infeasibility_certificate() {
    PENDING_INFEASIBILITY_CERTIFICATE.with(|pending| {
        pending.borrow_mut().take();
    });
}

pub(crate) fn take_pending_infeasibility_certificate() -> Option<ParityInfeasibilityCertificate> {
    PENDING_INFEASIBILITY_CERTIFICATE.with(|pending| pending.borrow_mut().take())
}

fn publish_infeasibility_certificate(certificate: ParityInfeasibilityCertificate) {
    PENDING_INFEASIBILITY_CERTIFICATE.with(|pending| {
        *pending.borrow_mut() = Some(certificate);
    });
}

/// Independently replay a parity contradiction against the source model.
///
/// This verifier intentionally does not call the lights-out recognizer or the
/// Gaussian eliminator.  It checks the smaller mathematical fact carried by
/// the artifact: a subset of exact integer equalities sums to even column
/// coefficients and an odd right-hand side.
///
/// # Errors
/// Returns a descriptive error when the row list is non-canonical, a selected
/// fact is not an exact integer equality, a participating column is not
/// integral, or the claimed parity contradiction does not hold.
pub fn verify_parity_infeasibility_certificate(
    model: &Model,
    certificate: &ParityInfeasibilityCertificate,
) -> Result<(), String> {
    if certificate.rows.is_empty() {
        return Err("parity certificate selects no source rows".to_owned());
    }
    let mut previous = None;
    let mut coefficient_parity = vec![false; model.num_cols()];
    let mut rhs_parity = false;

    for &row_u32 in &certificate.rows {
        let row_index = row_u32 as usize;
        if previous.is_some_and(|prior| prior >= row_u32) {
            return Err("parity certificate rows are not strictly increasing".to_owned());
        }
        previous = Some(row_u32);
        if row_index >= model.num_rows() {
            return Err(format!(
                "parity certificate row {row_index} is out of range for {} rows",
                model.num_rows()
            ));
        }
        let row = Row(row_u32);
        let (coefficients, lower_float, upper_float) = model.row(row);
        let lower = model.row_lb_exact(row_index, lower_float).ok_or_else(|| {
            format!("parity certificate row {row_index} has no finite lower side")
        })?;
        let upper = model.row_ub_exact(row_index, upper_float).ok_or_else(|| {
            format!("parity certificate row {row_index} has no finite upper side")
        })?;
        if lower != upper || !lower.is_integer() {
            return Err(format!(
                "parity certificate row {row_index} is not an exact integer equality"
            ));
        }
        rhs_parity ^= lower.to_integer().bit(0);

        for &(column, coefficient_float) in coefficients {
            let column_index = column as usize;
            if !model.col_kind(Col(column)).is_integral() {
                return Err(format!(
                    "parity certificate row {row_index} uses non-integral column {column_index}"
                ));
            }
            let coefficient = model.row_coeff_exact(row_index, column, coefficient_float);
            if !coefficient.is_integer() {
                return Err(format!(
                    "parity certificate row {row_index} has non-integer coefficient at column {column_index}"
                ));
            }
            coefficient_parity[column_index] ^= coefficient.to_integer().bit(0);
        }
    }

    if coefficient_parity.iter().any(|&odd| odd) {
        return Err(
            "selected parity rows do not sum to even coefficients for every column".to_owned(),
        );
    }
    if !rhs_parity {
        return Err("selected parity rows do not sum to an odd right-hand side".to_owned());
    }
    Ok(())
}

/// Size cap: the family is small (enlight_hard is 100×100). Anything wider is
/// out of the family and pays one comparison.
const MAX_DIM: usize = 4096;

/// Largest kernel we will ENUMERATE to prove OPTIMAL (`2^k` candidates). Beyond
/// this we still return a feasible point but decline the optimality claim.
const MAX_ENUM_NULLITY: u32 = 18;

/// Internal distinction between "not this exact family" and "the caller's
/// clock expired". The former falls through to normal search; the latter must
/// leave the solver as `Unknown::Timeout`, never as a late parity verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParityAbort {
    Declined,
    Timeout,
}

type ParityResult<T> = Result<T, ParityAbort>;

/// Optional so an unlimited solve stays genuinely unlimited. In particular,
/// do not manufacture the old one-hour deadline for callers that set none.
#[derive(Clone, Copy)]
struct Deadline<'a> {
    at: Option<Instant>,
    /// Test-only deterministic clock: each actual deadline poll consumes one
    /// token and the first poll with none left expires. Production deadlines
    /// leave this `None`, so unlimited solves still avoid reading the clock.
    polls_left: Option<&'a Cell<usize>>,
}

impl Deadline<'_> {
    fn new(at: Option<Instant>) -> Self {
        Self {
            at,
            polls_left: None,
        }
    }

    fn check(self) -> ParityResult<()> {
        if self.at.is_some_and(|deadline| Instant::now() >= deadline) {
            return Err(ParityAbort::Timeout);
        }
        if let Some(polls_left) = self.polls_left {
            let left = polls_left.get();
            if left == 0 {
                return Err(ParityAbort::Timeout);
            }
            polls_left.set(left - 1);
        }
        Ok(())
    }

    fn check_every(self, index: usize, mask: usize) -> ParityResult<()> {
        if index & mask == 0 {
            self.check()
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
impl<'a> Deadline<'a> {
    fn with_poll_budget(polls_left: &'a Cell<usize>) -> Self {
        Self {
            at: None,
            polls_left: Some(polls_left),
        }
    }
}

/// The compiled lights-out / GF(2) parity structure.
struct Parity {
    /// Number of binary columns.
    n: usize,
    /// Number of equality (parity) rows.
    m: usize,
    /// Model column index of each binary (length `n`, ascending).
    bin_cols: Vec<usize>,
    /// Integer coefficient of binary `k` in row `i` (`m × n`), for the exact
    /// `y = (Σ a·x − c)/2` reconstruction. Nonnegative.
    a_int: Vec<Vec<BigInt>>,
    /// Model column index of row `i`'s single free slack `y_i`.
    slack_col: Vec<usize>,
    /// Row `i`'s right-hand side (integer, `≤ 0`).
    c: Vec<BigInt>,
    /// GF(2) matrix rows, each a bitset over the `n` binaries.
    a2: Vec<Bits>,
    /// GF(2) right-hand side, one bit per row.
    b2: Vec<bool>,
    /// Objective coefficient of binary `k`, exactly (for the min-objective pick).
    obj: Vec<BigRational>,
}

/// A fixed-width bitset over the binaries (little-endian words).
#[derive(Clone)]
struct Bits {
    w: Vec<u64>,
}

impl Bits {
    fn zero(n: usize) -> Self {
        Bits {
            w: vec![0u64; n.div_ceil(64).max(1)],
        }
    }
    fn get(&self, i: usize) -> bool {
        (self.w[i >> 6] >> (i & 63)) & 1 == 1
    }
    fn set(&mut self, i: usize, v: bool) {
        let m = 1u64 << (i & 63);
        if v {
            self.w[i >> 6] |= m;
        } else {
            self.w[i >> 6] &= !m;
        }
    }
    fn flip(&mut self, i: usize) {
        self.w[i >> 6] ^= 1u64 << (i & 63);
    }
    /// self ^= other.
    fn xor_assign(&mut self, other: &Bits) {
        for (a, b) in self.w.iter_mut().zip(&other.w) {
            *a ^= *b;
        }
    }
    fn any(&self) -> bool {
        self.w.iter().any(|&x| x != 0)
    }
    /// Index of the lowest set bit strictly ≥ `from`, if any.
    fn first_set_from(&self, from: usize) -> Option<usize> {
        let n = self.w.len() * 64;
        (from..n).find(|&i| self.get(i))
    }

    fn set_indices(&self, limit: usize) -> Vec<usize> {
        let mut indices = Vec::new();
        let mut next = self.first_set_from(0);
        while let Some(index) = next {
            if index >= limit {
                break;
            }
            indices.push(index);
            next = self.first_set_from(index + 1);
        }
        indices
    }
}

/// Detect the lights-out / GF(2) parity shape, or `None`.
///
/// SELF-GATING contract (fail-closed): a `Minimize` model with exact
/// coefficients whose columns split into
///   * `x`: free integral on exactly `[0,1]`, and
///   * `y`: free integral on `[0, +∞)`, objective 0, appearing in EXACTLY ONE
///     row with coefficient exactly `−2` and nowhere else,
/// and whose EVERY row is an equality carrying exactly one such `y` (coeff `−2`),
/// all other coefficients NONNEGATIVE integers on `x`, and rhs an integer `≤ 0`.
/// The `y` columns must be in bijection with the rows. Matches enlight* and stays
/// silent on the rest of the corpus (set-partition rows carry no `−2` integer
/// slack; general-integer / inequality / maximise models fail immediately).
fn detect(model: &Model, deadline: Deadline<'_>) -> ParityResult<Parity> {
    deadline.check()?;
    if model.sense() != Sense::Minimize || model.has_inexact_coeffs() || !model.has_objective() {
        return Err(ParityAbort::Declined);
    }
    let nc = model.num_cols();
    let nr = model.num_rows();
    if nr == 0 || nr > MAX_DIM || nc == 0 || nc > MAX_DIM {
        return Err(ParityAbort::Declined);
    }
    // Column census.
    let mut is_bin = vec![false; nc];
    let mut is_slack = vec![false; nc];
    let mut n_slack = 0usize;
    for j in 0..nc {
        deadline.check_every(j, 63)?;
        let cj = Col(j as u32);
        let (l, u) = model.col_bounds(cj);
        if !model.col_kind(cj).is_integral() {
            return Err(ParityAbort::Declined); // a continuous column: not this family
        }
        if l == 0.0 && u == 1.0 {
            is_bin[j] = true;
        } else if l == 0.0 && u == f64::INFINITY && model.obj_coeff(cj) == 0.0 {
            is_slack[j] = true;
            n_slack += 1;
        } else {
            return Err(ParityAbort::Declined); // neither a 0/1 nor a free slack
        }
    }
    let bin_cols: Vec<usize> = (0..nc).filter(|&j| is_bin[j]).collect();
    let n = bin_cols.len();
    // Gate the slack/row bijection BEFORE allocating the dense m×n exact
    // reconstruction matrix. Since every admitted column is binary or slack,
    // this also proves n + nr == nc <= MAX_DIM (at most ~4.2M entries), rather
    // than letting a malformed 4095-bin/1-slack model allocate ~16.7M BigInts.
    if n == 0 || n_slack != nr {
        return Err(ParityAbort::Declined);
    }
    let mut bin_pos = vec![usize::MAX; nc];
    for (k, &j) in bin_cols.iter().enumerate() {
        deadline.check_every(k, 63)?;
        bin_pos[j] = k;
    }
    // Each slack must appear in EXACTLY ONE row.
    let mut slack_rows = vec![0usize; nc];

    let neg_two = BigRational::from_integer(BigInt::from(-2));
    // Allocate the dense exact reconstruction matrix row-by-row so a large
    // admitted shape cannot spend its whole clock in one uninterruptible clone.
    let mut a_int = Vec::with_capacity(nr);
    let mut a2 = Vec::with_capacity(nr);
    for i in 0..nr {
        deadline.check_every(i, 7)?;
        a_int.push(vec![BigInt::zero(); n]);
        a2.push(Bits::zero(n));
    }
    let mut b2 = vec![false; nr];
    let mut slack_col = vec![usize::MAX; nr];
    let mut c = vec![BigInt::zero(); nr];

    for i in 0..nr {
        deadline.check()?;
        let (coeffs, lo, up) = model.row(Row(i as u32));
        if lo != up || !lo.is_finite() {
            return Err(ParityAbort::Declined); // an inequality/range row
        }
        let mut slack: Option<usize> = None;
        for (term, &(col, coef)) in coeffs.iter().enumerate() {
            deadline.check_every(term, 63)?;
            let cj = col as usize;
            if coef == 0.0 {
                continue;
            }
            if is_slack[cj] {
                // The single parity slack: coefficient must be exactly −2.
                if exact(coef).ok_or(ParityAbort::Declined)? != neg_two {
                    return Err(ParityAbort::Declined);
                }
                if slack.replace(cj).is_some() {
                    return Err(ParityAbort::Declined); // two slacks in one row
                }
                slack_rows[cj] += 1;
            } else if is_bin[cj] {
                let q = exact(coef).ok_or(ParityAbort::Declined)?;
                if !q.is_integer() {
                    return Err(ParityAbort::Declined);
                }
                let ai = q.to_integer();
                if ai.is_negative() {
                    return Err(ParityAbort::Declined); // completeness needs nonnegative x-coeffs
                }
                let k = bin_pos[cj];
                a2[i].set(k, ai.bit(0)); // low bit = coefficient mod 2
                a_int[i][k] = ai;
            } else {
                return Err(ParityAbort::Declined);
            }
        }
        let sc = slack.ok_or(ParityAbort::Declined)?; // every row must carry its slack
        slack_col[i] = sc;
        // rhs: an integer ≤ 0.
        let rhs = exact(lo).ok_or(ParityAbort::Declined)?;
        if !rhs.is_integer() {
            return Err(ParityAbort::Declined);
        }
        let ci = rhs.to_integer();
        if ci.is_positive() {
            return Err(ParityAbort::Declined);
        }
        // Parity of a nonpositive integer is sign-independent: the low bit of
        // its magnitude equals c mod 2, so BigInt::bit(0) is the correct rhs.
        b2[i] = ci.bit(0);
        c[i] = ci;
    }
    // Every slack used exactly once, and slacks are in bijection with rows.
    for j in 0..nc {
        deadline.check_every(j, 63)?;
        if is_slack[j] && slack_rows[j] != 1 {
            return Err(ParityAbort::Declined);
        }
    }
    let mut obj = Vec::with_capacity(n);
    for (k, &j) in bin_cols.iter().enumerate() {
        deadline.check_every(k, 63)?;
        obj.push(exact(model.obj_coeff(Col(j as u32))).ok_or(ParityAbort::Declined)?);
    }
    deadline.check()?;

    Ok(Parity {
        n,
        m: nr,
        bin_cols,
        a_int,
        slack_col,
        c,
        a2,
        b2,
        obj,
    })
}

/// Reduced row-echelon form over GF(2). Returns `(pivots, inconsistency)` where
/// `pivots[r] = (pivot_col, row_bits, rhs)` is the reduced system, or reports the
/// source-row combination that produced a `0 = 1` row.
struct Rref {
    /// One entry per pivot: `(pivot column, reduced row, reduced rhs)`.
    piv: Vec<(usize, Bits, bool)>,
    /// Source rows whose XOR is `0 = 1`, when the system is inconsistent.
    inconsistency: Option<Bits>,
}

fn rref(p: &Parity, deadline: Deadline<'_>) -> ParityResult<Rref> {
    deadline.check()?;
    let mut rows: Vec<(Bits, bool, Bits)> = Vec::with_capacity(p.m);
    for (i, (a, &b)) in p.a2.iter().zip(&p.b2).enumerate() {
        deadline.check_every(i, 31)?;
        let mut source_rows = Bits::zero(p.m);
        source_rows.set(i, true);
        rows.push((a.clone(), b, source_rows));
    }
    let mut piv: Vec<(usize, Bits, bool)> = Vec::new();
    let mut r0 = 0usize;
    for col in 0..p.n {
        deadline.check()?;
        // Find a row at/after r0 with a 1 in this column.
        let mut sel = None;
        for r in r0..rows.len() {
            deadline.check_every(r - r0, 63)?;
            if rows[r].0.get(col) {
                sel = Some(r);
                break;
            }
        }
        let Some(sel) = sel else { continue };
        rows.swap(r0, sel);
        // Eliminate this column from every other row.
        let (pivrow, pivrhs, pivsource) = {
            let (a, b, source) = &rows[r0];
            (a.clone(), *b, source.clone())
        };
        for r in 0..rows.len() {
            deadline.check_every(r, 31)?;
            if r != r0 && rows[r].0.get(col) {
                rows[r].0.xor_assign(&pivrow);
                rows[r].1 ^= pivrhs;
                rows[r].2.xor_assign(&pivsource);
            }
        }
        piv.push((col, pivrow, pivrhs));
        r0 += 1;
    }
    // Any all-zero row with rhs 1 is inconsistent.
    let mut inconsistency = None;
    for (i, (a, b, source)) in rows.iter().enumerate() {
        deadline.check_every(i, 63)?;
        if *b && !a.any() {
            inconsistency = Some(source.clone());
            break;
        }
    }
    deadline.check()?;
    Ok(Rref { piv, inconsistency })
}

/// Complete a solution from values assigned only at the free columns.
fn solve_from_free(
    p: &Parity,
    rr: &Rref,
    free: &[usize],
    freevals: &Bits,
    deadline: Deadline<'_>,
) -> ParityResult<Bits> {
    deadline.check()?;
    let mut x = Bits::zero(p.n);
    for (i, &f) in free.iter().enumerate() {
        deadline.check_every(i, 31)?;
        x.set(f, freevals.get(f));
    }
    // Back-substitute pivots in REVERSE order.
    for (pivot_i, (pc, row, rhs)) in rr.piv.iter().rev().enumerate() {
        deadline.check_every(pivot_i, 15)?;
        // x[pc] = rhs XOR Σ_{j≠pc, row_j=1} x[j].
        let mut val = *rhs;
        let mut j = row.first_set_from(0);
        let mut terms = 0usize;
        while let Some(jj) = j {
            deadline.check_every(terms, 255)?;
            if jj != *pc && x.get(jj) {
                val ^= true;
            }
            j = row.first_set_from(jj + 1);
            terms += 1;
        }
        x.set(*pc, val);
    }
    deadline.check()?;
    Ok(x)
}

/// Exact binary-column objective. Parity slacks have zero objective by the
/// shape gate.
fn parity_obj_of(p: &Parity, x: &Bits, deadline: Deadline<'_>) -> ParityResult<BigRational> {
    deadline.check()?;
    let mut s = BigRational::zero();
    for k in 0..p.n {
        deadline.check_every(k, 63)?;
        if x.get(k) {
            s += &p.obj[k];
        }
    }
    deadline.check()?;
    Ok(s)
}

/// Continue Gray-code enumeration after `best` has already been established
/// from the all-zero free assignment. Any timeout discards that incumbent and
/// propagates `Timeout`; a partial optimum must never escape.
fn enumerate_remaining(
    p: &Parity,
    rr: &Rref,
    free: &[usize],
    mut freevals: Bits,
    mut best: Bits,
    mut best_obj: BigRational,
    deadline: Deadline<'_>,
) -> ParityResult<Bits> {
    let total = 1u64 << free.len();
    let mut g = 0u64;
    for i in 1..total {
        // The candidate helpers also poll inside pivot/objective work; this
        // outer check closes the cheap-small-system case.
        deadline.check_every(i as usize, 63)?;
        let gray = i ^ (i >> 1);
        let changed = (gray ^ g).trailing_zeros() as usize;
        g = gray;
        freevals.flip(free[changed]);
        let x = solve_from_free(p, rr, free, &freevals, deadline)?;
        let o = parity_obj_of(p, &x, deadline)?;
        if o < best_obj {
            best_obj = o;
            best = x;
        }
    }
    deadline.check()?;
    Ok(best)
}

/// Public entry: decide the enlight-class instance exactly, or `None`.
pub(crate) fn try_solve(model: &Model, deadline: Option<Instant>) -> Option<Outcome> {
    clear_pending_infeasibility_certificate();
    if std::env::var_os("AY_MILP_NO_PARITY").is_some() {
        return None;
    }
    try_solve_enabled(model, deadline)
}

/// Core of the parity solver, with the env kill-switch already handled by
/// `try_solve`. The firing tests call this directly so they never read (and so
/// never race) the process-global `AY_MILP_NO_PARITY` env var under parallel
/// `cargo test`; only `kill_switch_disables_device` touches the env.
fn try_solve_enabled(model: &Model, deadline: Option<Instant>) -> Option<Outcome> {
    try_solve_with_deadline(model, Deadline::new(deadline))
}

fn try_solve_with_deadline(model: &Model, deadline: Deadline<'_>) -> Option<Outcome> {
    match try_solve_inner(model, deadline) {
        Ok(outcome) => Some(outcome),
        // A structural or witness failure remains a normal decline only while
        // the caller still has time. If that work crossed the absolute cap,
        // falling through would let time-limit-only callers start ordinary
        // search with a fresh budget.
        Err(ParityAbort::Declined) if deadline.check().is_err() => Some(Outcome::Unknown {
            reason: UnknownReason::Timeout,
        }),
        Err(ParityAbort::Declined) => None,
        Err(ParityAbort::Timeout) => Some(Outcome::Unknown {
            reason: UnknownReason::Timeout,
        }),
    }
}

/// Cached trace predicate. `tests/env_ledger.rs` counts a bare `env::var_os` on
/// the solve path as a LIVE read — a fresh `getenv` a concurrent `set_var` can
/// race — and that ratchet may only move DOWN.
fn trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("AY_MILP_TRACE").is_some())
}

fn try_solve_inner(model: &Model, deadline: Deadline<'_>) -> ParityResult<Outcome> {
    deadline.check()?;
    let trace = trace_enabled();
    let p = detect(model, deadline)?;
    if trace {
        eprintln!(
            "AY_MILP_TRACE parity: lights-out shape {}x{} — GF(2) elimination",
            p.m, p.n
        );
    }
    deadline.check()?;
    let rr = rref(&p, deadline)?;
    if let Some(source_rows) = &rr.inconsistency {
        if trace {
            eprintln!("AY_MILP_TRACE parity: GF(2) system INCONSISTENT — INFEASIBLE");
        }
        let rows = source_rows
            .set_indices(p.m)
            .into_iter()
            .map(|row| u32::try_from(row).map_err(|_| ParityAbort::Declined))
            .collect::<ParityResult<Vec<_>>>()?;
        let certificate = ParityInfeasibilityCertificate::from_rows(rows);
        verify_parity_infeasibility_certificate(model, &certificate)
            .map_err(|_| ParityAbort::Declined)?;
        deadline.check()?;
        publish_infeasibility_certificate(certificate);
        return Ok(Outcome::Infeasible {
            cert: None,
            tree_cert: None,
        });
    }
    let rank = rr.piv.len();
    let nullity = (p.n - rank) as u32;
    if trace {
        eprintln!("AY_MILP_TRACE parity: rank {rank}, nullity {nullity}");
    }

    // Free columns = columns that are not a pivot.
    deadline.check()?;
    let mut is_pivot = vec![false; p.n];
    for (i, (pc, _, _)) in rr.piv.iter().enumerate() {
        deadline.check_every(i, 63)?;
        is_pivot[*pc] = true;
    }
    let mut free = Vec::with_capacity(nullity as usize);
    for (j, &pivot) in is_pivot.iter().enumerate() {
        deadline.check_every(j, 63)?;
        if !pivot {
            free.push(j);
        }
    }

    let can_enumerate = nullity <= MAX_ENUM_NULLITY;

    // Best (min-objective) solution we can justify as OPTIMAL, or just the first
    // feasible one when the kernel is too large to enumerate.
    let (best_x, proved_optimal) = if can_enumerate {
        // Enumerate all 2^nullity free-assignments via Gray code, tracking min.
        let freevals = Bits::zero(p.n);
        let best = solve_from_free(&p, &rr, &free, &freevals, deadline)?;
        let best_obj = parity_obj_of(&p, &best, deadline)?;
        (
            enumerate_remaining(&p, &rr, &free, freevals, best, best_obj, deadline)?,
            true,
        )
    } else {
        // Kernel too large to prove optimal: return one feasible point.
        (
            solve_from_free(&p, &rr, &free, &Bits::zero(p.n), deadline)?,
            false,
        )
    };

    deadline.check()?;
    finish(model, &p, &best_x, proved_optimal, trace, deadline)
}

/// Independently re-read and exactly verify a candidate, polling at every
/// column, row, and row term. Detection has already rejected exact side-store
/// models, and the admitted parity shape is integer-valued, so this checker can
/// accumulate each row as a `BigInt` without the uninterruptible rational-vector
/// conversion and multi-million-term gcd loop in `Model::check_point`.
/// Returns the independently recomputed exact objective on success.
fn verify_point_and_objective(
    model: &Model,
    point: &[BigRational],
    deadline: Deadline<'_>,
) -> ParityResult<BigRational> {
    deadline.check()?;
    if model.has_inexact_coeffs()
        || model.sense() != Sense::Minimize
        || !model.has_objective()
        || point.len() != model.num_cols()
    {
        return Err(ParityAbort::Declined);
    }

    for (j, value) in point.iter().enumerate() {
        deadline.check()?;
        let col = Col(j as u32);
        let (lower, upper) = model.col_bounds(col);
        if !model.col_kind(col).is_integral() || !value.is_integer() {
            return Err(ParityAbort::Declined);
        }
        if lower.is_finite() {
            if value < &exact(lower).ok_or(ParityAbort::Declined)? {
                return Err(ParityAbort::Declined);
            }
        } else if lower != f64::NEG_INFINITY {
            return Err(ParityAbort::Declined);
        }
        if upper.is_finite() {
            if value > &exact(upper).ok_or(ParityAbort::Declined)? {
                return Err(ParityAbort::Declined);
            }
        } else if upper != f64::INFINITY {
            return Err(ParityAbort::Declined);
        }
    }

    for i in 0..model.num_rows() {
        deadline.check()?;
        let (coeffs, lower, upper) = model.row(Row(i as u32));
        if lower != upper || !lower.is_finite() {
            return Err(ParityAbort::Declined);
        }
        let rhs = exact(lower).ok_or(ParityAbort::Declined)?;
        if !rhs.is_integer() {
            return Err(ParityAbort::Declined);
        }
        let mut activity = BigInt::zero();
        for &(col, coefficient) in coeffs {
            // Poll EVERY term: this is the final verdict gate, and a malformed
            // dense shape may contain millions of them.
            deadline.check()?;
            let value = point.get(col as usize).ok_or(ParityAbort::Declined)?;
            let coefficient = exact(coefficient).ok_or(ParityAbort::Declined)?;
            if !coefficient.is_integer() || !value.is_integer() {
                return Err(ParityAbort::Declined);
            }
            if !coefficient.is_zero() && !value.is_zero() {
                activity += coefficient.numer() * value.numer();
            }
        }
        if &activity != rhs.numer() {
            return Err(ParityAbort::Declined);
        }
    }

    deadline.check()?;
    let mut value = exact(model.objective_offset()).ok_or(ParityAbort::Declined)?;
    for (j, point_value) in point.iter().enumerate() {
        deadline.check()?;
        let coefficient = exact(model.obj_coeff(Col(j as u32))).ok_or(ParityAbort::Declined)?;
        if !coefficient.is_zero() && !point_value.is_zero() {
            value += coefficient * point_value;
        }
    }
    deadline.check()?;
    Ok(value)
}

/// Reconstruct the full exact model point from the chosen 0/1 `x`, re-check it
/// with the deadline-polled independent verifier, and package the `Outcome`.
/// `proved_optimal` decides Optimal vs Feasible.
fn finish(
    model: &Model,
    p: &Parity,
    x: &Bits,
    proved_optimal: bool,
    trace: bool,
    deadline: Deadline<'_>,
) -> ParityResult<Outcome> {
    deadline.check()?;
    let nc = model.num_cols();
    let mut point = vec![BigRational::zero(); nc];
    // Binaries.
    for (k, &j) in p.bin_cols.iter().enumerate() {
        deadline.check_every(k, 63)?;
        if x.get(k) {
            point[j] = BigRational::from_integer(BigInt::from(1));
        }
    }
    // Slacks: y_i = (Σ a_ik x_k − c_i) / 2, an integer ≥ 0 by construction.
    for i in 0..p.m {
        deadline.check()?;
        let mut ax = BigInt::zero();
        for k in 0..p.n {
            deadline.check_every(k, 63)?;
            if x.get(k) {
                ax += &p.a_int[i][k];
            }
        }
        let num = &ax - &p.c[i];
        // Must be even and nonnegative — else the structural premise was violated
        // and we decline (fail-closed) rather than emit anything.
        if num.is_negative() || num.bit(0) {
            if trace {
                eprintln!("AY_MILP_TRACE parity: slack reconstruction off — declining");
            }
            return Err(ParityAbort::Declined);
        }
        point[p.slack_col[i]] = BigRational::from_integer(num >> 1);
    }
    // Nothing leaves without a fresh, deadline-polled exact re-read of every
    // public column/row and an independently recomputed objective.
    let value = match verify_point_and_objective(model, &point, deadline) {
        Ok(value) => value,
        Err(ParityAbort::Declined) => {
            if trace {
                eprintln!("AY_MILP_TRACE parity: witness rejected by exact verifier — declining");
            }
            return Err(ParityAbort::Declined);
        }
        Err(ParityAbort::Timeout) => return Err(ParityAbort::Timeout),
    };
    if proved_optimal {
        if trace {
            eprintln!("AY_MILP_TRACE parity: PROVEN OPTIMAL value {value}");
        }
        deadline.check()?;
        Ok(Outcome::Optimal {
            value,
            model_values: point,
            cert: None,
        })
    } else {
        if trace {
            eprintln!(
                "AY_MILP_TRACE parity: FEASIBLE witness value {value} (kernel too large to prove)"
            );
        }
        deadline.check()?;
        Ok(Outcome::Feasible {
            model_values: point,
            incumbent_only: true,
            dual_bound: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{Col, Model, Sense};
    use std::time::Duration;

    fn deadline() -> Option<Instant> {
        Some(Instant::now() + Duration::from_secs(30))
    }

    /// Build a lights-out / parity model: for each row `i`,
    /// `Σ_j a[i][j]·x_j − 2·y_i = c[i]`, `x ∈ {0,1}`, `y ≥ 0` integer, obj 0;
    /// objective `min Σ x_j` (unit coefficients).
    fn parity_model(a: &[Vec<i64>], c: &[i64]) -> Model {
        let n = a[0].len();
        let mut m = Model::new();
        let x: Vec<Col> = (0..n).map(|_| m.add_binary_col()).collect();
        let y: Vec<Col> = (0..a.len())
            .map(|_| m.add_int_col(0.0, f64::INFINITY))
            .collect();
        for (i, row) in a.iter().enumerate() {
            let mut terms: Vec<(Col, f64)> = row
                .iter()
                .enumerate()
                .filter(|&(_, &v)| v != 0)
                .map(|(j, &v)| (x[j], v as f64))
                .collect();
            terms.push((y[i], -2.0));
            m.add_row(c[i] as f64, c[i] as f64, &terms);
        }
        let obj: Vec<(Col, f64)> = x.iter().map(|&col| (col, 1.0)).collect();
        m.set_objective(&obj, Sense::Minimize);
        m
    }

    #[test]
    fn unique_solution_proves_optimal() {
        // x0 − 2y = −1 ⟹ x0 ≡ 1 ⟹ x0 = 1 (unique), obj = 1.
        let m = parity_model(&[vec![1]], &[-1]);
        // `None` is the unlimited-solve path: it must not inherit a synthetic
        // one-hour cutoff from the parity device.
        match try_solve_enabled(&m, None) {
            Some(Outcome::Optimal {
                value,
                model_values,
                ..
            }) => {
                assert_eq!(value, BigRational::from_integer(BigInt::from(1)));
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 1, got {other:?}"),
        }
    }

    #[test]
    fn inconsistent_system_proves_infeasible() {
        // x0 ≡ 0 AND x0 ≡ 1: no binary x ⟹ INFEASIBLE.
        let m = parity_model(&[vec![1], vec![1]], &[0, -1]);
        clear_pending_infeasibility_certificate();
        assert!(matches!(
            try_solve_enabled(&m, deadline()),
            Some(Outcome::Infeasible { .. })
        ));
        let certificate = take_pending_infeasibility_certificate()
            .expect("inconsistent parity solve must publish its row combination");
        assert_eq!(certificate.rows(), &[0, 1]);
        verify_parity_infeasibility_certificate(&m, &certificate)
            .expect("freshly generated GF(2) contradiction must replay");
    }

    #[test]
    fn parity_certificate_tampering_is_rejected() {
        let model = parity_model(&[vec![1], vec![1]], &[0, -1]);
        let missing_row = ParityInfeasibilityCertificate::from_rows(vec![0]);
        assert!(verify_parity_infeasibility_certificate(&model, &missing_row).is_err());

        let duplicate_row = ParityInfeasibilityCertificate::from_rows(vec![0, 0, 1]);
        assert!(verify_parity_infeasibility_certificate(&model, &duplicate_row).is_err());

        let out_of_range = ParityInfeasibilityCertificate::from_rows(vec![0, 2]);
        assert!(verify_parity_infeasibility_certificate(&model, &out_of_range).is_err());
    }

    #[test]
    fn parity_certificate_rejects_a_nonintegral_source_column() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.add_row(0.0, 0.0, &[(x, 1.0)]);
        model.add_row(1.0, 1.0, &[(x, 1.0)]);
        let certificate = ParityInfeasibilityCertificate::from_rows(vec![0, 1]);
        assert!(verify_parity_infeasibility_certificate(&model, &certificate).is_err());
    }

    #[test]
    fn small_kernel_minimises_over_the_coset() {
        // x0 + x1 − 2y = 0 ⟹ x0 ≡ x1. Solutions (0,0) obj 0 and (1,1) obj 2;
        // the device must return OPTIMAL 0, not the weight-2 solution.
        let m = parity_model(&[vec![1, 1]], &[0]);
        match try_solve_enabled(&m, deadline()) {
            Some(Outcome::Optimal {
                value,
                model_values,
                ..
            }) => {
                assert_eq!(value, BigRational::zero());
                assert!(m.check_point(&model_values).is_ok());
            }
            other => panic!("expected Optimal 0, got {other:?}"),
        }
    }

    #[test]
    fn kill_switch_disables_device() {
        let m = parity_model(&[vec![1]], &[-1]);
        let out =
            ay_test_support::env::with_serialized_env_vars(&[("AY_MILP_NO_PARITY", "1")], || {
                try_solve(&m, deadline())
            });
        assert!(out.is_none(), "kill switch must disable the device");
    }

    #[test]
    fn expired_deadline_fails_closed_across_parity_phases() {
        // Nontrivial rank-2/nullity-1 system:
        //   x0 + x1 = 0 (mod 2)
        //   x1 + x2 = 1 (mod 2)
        // It has two feasible points, so every verdict shape is available to
        // catch an accidental late Optimal/Feasible result.
        let m = parity_model(&[vec![1, 1, 0], vec![0, 1, 1]], &[0, -1]);
        let expired_at = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("the monotonic clock must be at least one second old");
        let expired = Deadline::new(Some(expired_at));

        assert!(matches!(
            try_solve_enabled(&m, Some(expired_at)),
            Some(Outcome::Unknown {
                reason: UnknownReason::Timeout
            })
        ));

        // Exercise the independently-polled expensive phases directly. These
        // checks stay deterministic: no sleeps and no scheduler timing race.
        let p = detect(&m, Deadline::new(None)).expect("shape");
        assert!(matches!(detect(&m, expired), Err(ParityAbort::Timeout)));
        assert!(matches!(rref(&p, expired), Err(ParityAbort::Timeout)));

        let mut witness = Bits::zero(p.n);
        witness.set(2, true); // x=(0,0,1), with reconstructed y=(0,1)
        assert!(matches!(
            finish(&m, &p, &witness, false, false, expired),
            Err(ParityAbort::Timeout)
        ));
    }

    #[test]
    fn decline_that_spends_the_last_poll_maps_to_timeout() {
        let mut m = parity_model(&[vec![1]], &[-1]);
        m.set_objective(&[(Col(0), 1.0)], Sense::Maximize);

        // One poll enters the solver and one enters detection. Detection then
        // structurally declines on Maximize with no token left; the boundary's
        // post-decline poll must convert that to Timeout instead of starting a
        // fresh normal-search budget.
        let polls_left = Cell::new(2);
        assert!(matches!(
            try_solve_with_deadline(&m, Deadline::with_poll_budget(&polls_left)),
            Some(Outcome::Unknown {
                reason: UnknownReason::Timeout
            })
        ));
        assert_eq!(polls_left.get(), 0);
    }

    #[test]
    fn mid_enumeration_timeout_discards_an_existing_incumbent() {
        // One equation on three binaries has rank 1/nullity 2, hence four
        // candidates. Establish the all-zero incumbent without a clock, then
        // give continuation only two successful polls. The second candidate
        // begins construction and expires at a periodic pivot poll; returning
        // the already-known incumbent as Feasible/Optimal would be unsound with
        // respect to the hard deadline.
        let m = parity_model(&[vec![1, 1, 1]], &[0]);
        let p = detect(&m, Deadline::new(None)).expect("shape");
        let rr = rref(&p, Deadline::new(None)).expect("rref");
        assert_eq!(rr.piv.len(), 1);
        let pivot = rr.piv[0].0;
        let free: Vec<usize> = (0..p.n).filter(|&j| j != pivot).collect();
        assert_eq!(free.len(), 2);

        let freevals = Bits::zero(p.n);
        let incumbent = solve_from_free(&p, &rr, &free, &freevals, Deadline::new(None))
            .expect("initial candidate");
        let incumbent_obj =
            parity_obj_of(&p, &incumbent, Deadline::new(None)).expect("initial objective");
        assert_eq!(incumbent_obj, BigRational::zero());

        let polls_left = Cell::new(2);
        assert!(matches!(
            enumerate_remaining(
                &p,
                &rr,
                &free,
                freevals,
                incumbent,
                incumbent_obj,
                Deadline::with_poll_budget(&polls_left),
            ),
            Err(ParityAbort::Timeout)
        ));
        assert_eq!(polls_left.get(), 0);
    }

    #[test]
    fn final_exact_verifier_polls_inside_the_scan() {
        let m = parity_model(&[vec![1, 1, 0], vec![0, 1, 1]], &[0, -1]);
        // x=(0,0,1), y=(0,1).
        let point = vec![
            BigRational::zero(),
            BigRational::zero(),
            BigRational::from_integer(BigInt::from(1)),
            BigRational::zero(),
            BigRational::from_integer(BigInt::from(1)),
        ];
        let polls_left = Cell::new(1);
        assert!(matches!(
            verify_point_and_objective(&m, &point, Deadline::with_poll_budget(&polls_left),),
            Err(ParityAbort::Timeout)
        ));
        assert_eq!(polls_left.get(), 0);
    }

    #[test]
    fn declines_non_parity_models() {
        // A continuous slack (market-split shape) is NOT the parity family.
        let mut m = Model::new();
        let x0 = m.add_binary_col();
        let x1 = m.add_binary_col();
        let s = m.add_col(0.0, f64::INFINITY);
        m.add_row(1.0, 1.0, &[(x0, 1.0), (x1, 1.0), (s, 1.0)]);
        m.set_objective(&[(s, 1.0)], Sense::Minimize);
        assert!(try_solve(&m, deadline()).is_none());

        // A general-integer column with a finite upper bound is not a free slack.
        let mut m2 = Model::new();
        let a = m2.add_binary_col();
        let g = m2.add_int_col(0.0, 5.0);
        m2.add_row(0.0, 0.0, &[(a, 1.0), (g, -2.0)]);
        m2.set_objective(&[(a, 1.0)], Sense::Minimize);
        assert!(try_solve(&m2, deadline()).is_none());
    }
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}
