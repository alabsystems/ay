// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact-rational bounded-variable simplex: ay-milp's certification rim.
//!
//! Every verdict it produces is exact, and certificate-bearing verdicts carry
//! model-level evidence ([`FarkasCertificate`] / optimality multipliers) that
//! [`crate::cert`] can re-verify without solver state. The float-first engine
//! uses this tier for exact replay and certificate extraction;
//! [`crate::LpSession`] runs on it directly.
//!
//! Method: Dutertre–de Moura bounded-variable simplex over
//! [`ay_lra::rational::Rational`] (inline i64 fast path, `BigRational`
//! fallback — the workspace's shared exact vocabulary). Variables are the
//! model's structural columns plus one logical variable per row
//! (`s_i = a_i·x`, bounded by the row's range). Feasibility is restored by
//! the standard violated-basic repair loop, optimization by a primal
//! improve loop with bound flips; both use Bland's smallest-index rule
//! throughout, so termination is guaranteed and iteration caps are a belt,
//! not the proof. Anything the budget cuts short is `Unknown` — never a
//! partial verdict (fail-closed).
//!
//! TWO REPRESENTATIONS, ONE TABLEAU. The rows are held either as reduced
//! rationals ([`Form::Reduced`], the historical form and the default) or as
//! integers over a per-row divisor ([`Form::FractionFree`], see
//! [`fraction_free`]), and a solve moves from the first to the second at most
//! once, when the census in [`ExactLp::close_window`] measures the tableau
//! leaving the inline `i64` path. The two forms denote the SAME coefficients —
//! `t/den`, with `den = 1` in the first — so the pivot RULE never sees the
//! difference, the pivot SEQUENCE is identical, and the optimum is
//! bit-identical either way. What differs is only what the arithmetic under
//! the rule costs: the reduced form pays a gcd per entry to keep entries
//! narrow, which is the right trade while they fit in a machine word and the
//! wrong one once they do not. See [`SWITCH_WINDOW`] for the policy and the
//! measurements behind it.

use std::borrow::Cow;
use std::time::Instant;

use ay_lra::rational::Rational;
use num_rational::BigRational;
use num_traits::Zero;

use crate::cert::{BoundSide, FactRef, FarkasCertificate, Multiplier};
use crate::model::{exact, Col, Model, Row};
use crate::outcome::UnknownReason;

mod fraction_free;
#[cfg(test)]
mod probe;

/// Which arithmetic the tableau is held in. See [`ExactLp::form`] for the
/// policy that moves between them; the two forms denote the SAME numbers, so
/// nothing about a verdict depends on which one is in force.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Form {
    /// One fully reduced [`Rational`] per entry, `den = 1` on every row.
    /// The rim's historical representation and still its default.
    Reduced,
    /// Integers over a per-row divisor (Bareiss). See [`fraction_free`].
    FractionFree,
}

/// THE SWITCH, in four constants.
///
/// The signal is the share of tableau entries a pivot writes that stay on
/// `Rational::Small` — the inline `(i64, i64)` path. It costs a branch per
/// sampled entry against the gcd-bearing multiply that produced that entry,
/// and it is exactly the quantity the two representations trade against each
/// other (the reduced form pays gcds to keep entries narrow; the fraction-free
/// form pays width to remove the gcds).
///
/// MEASURED, `cargo test exact::probe -- --ignored`, per-window census with
/// the rim driven directly:
///
/// ```text
///   dcmulti  1,632 pivots   100.000% inline in EVERY window
///   p0201      616 pivots   100.000% inline in EVERY window
///   qiu      9,189 pivots   100.000% inline in EVERY window
///   qnet1   80,733 pivots   100.000% inline in EVERY window
///   mas76      583 pivots   100% to pivot 128, then 96.1 / 60.3 / 50.2 / 3.5 / 0.0
///   mas74      534 pivots   100% to pivot 128, then the same cliff
///   blend2   2,511 pivots   100% to pivot 512, 97-99% to 1,400, then 88 / 79 / 61 / 47
/// ```
///
/// THE CLASSES DO NOT OVERLAP, and the reduced class's side of the gap is not
/// near-100% but EXACTLY it: `dcmulti`, `p0201`, `qiu` and `qnet1` write
/// 11.7M, 1.2M, 2.1 BILLION and 1.3 BILLION tableau entries respectively and
/// not ONE of them leaves the inline path. So no threshold below 100% can
/// fire on that class at all — that is arithmetic, not a margin — and the
/// threshold's only real job is to catch the other class early.
///
/// * [`SWITCH_INLINE_PERCENT`] = 99 — a window is COLD when more than one
///   entry in a hundred left the inline path. It reads tight and is not: the
///   reduced form's whole cost is the gcd it runs on entries that are NOT
///   word-sized, so a small share of them already dominates the window.
///   MEASURED on `blend2`, which sits at 97-99% for 800 pivots before its
///   cliff: converting there is worth 2.4x (29.3s reduced, 12.5s switched,
///   12.9s converted at the first pivot), and a 90% threshold — which waits
///   for the cliff — is a WASH (29.3s).
/// * [`SWITCH_WINDOW`] = 16 pivots — the decision is made on ENTRIES, and 16
///   pivots is 28,000 entries on `mas76` and 64,000 on `blend2`. Sixteen was
///   chosen against 32 and 64 because the cliff is sharp and the delay is
///   pure loss: `mas76` converts at pivot 160 rather than 192 or 256, and its
///   solve goes 1.583s / 2.036s / 3.376s against 1.491s for converting at the
///   first pivot that can.
/// * [`SWITCH_SUSTAIN`] = 2 windows — 32 pivots of agreement before a one-way,
///   tableau-wide rewrite. One window is enough on this corpus; the second is
///   what stops a single wide pivot from committing the solve.
/// * [`SWITCH_SAMPLE_STRIDE`] = 8 — see [`ExactLp::census`]. A share does not
///   need every entry, and charging the reduced class for entries it will
///   never act on is the one way this policy could have cost it anything.
///
/// IF IT NEVER FIRES the rim runs the reduced-rational tableau it has always
/// run: the policy's whole footprint is a sampled counter pair, a window
/// comparison in integer arithmetic, and one `Rational` multiply per pivot to
/// carry `|det B|`. There is no time-based fallback and no second chance — a
/// solve that stays on the inline path stays reduced, and a solve whose model
/// could not be integralised never even counts (see
/// [`ExactLp::convertible`]).
///
/// # What a 67-probe sweep found afterwards (2026-08-20)
///
/// THE CLASS IS FIFTEEN, NOT THREE. Over 46 distinct matrices (14 MILP corpus
/// + 15 witness + 38 oracle LP relaxations, 21 of them the same matrices),
/// the switch fires on `blend2`, `mas74`, `mas76`, `pk1`, `harp2` and all ten
/// `domset_mw19_*` relaxations. `pk1` (sw@688) is a corpus member and was
/// independently confirmed at 2.45x on interleaved reps.
///
/// THERE IS NO CHEAP STATIC PREDICTOR, which vindicates censusing rather than
/// classifying: density crosses the boundary (`mas76` 90.5% dense converts,
/// hexgrid 0.25% does not), matrix integrality crosses it (`pk1` has 0
/// non-integral rows and converts, `p2756` has 380 and does not), row count
/// crosses it (12 rows converts, 12,650 does not), and so does λ.
///
/// AND THE HONEST OTHER HALF OF "the reduced class pays 0.6-1.9%": AT LEAST
/// NINE OF ITS MEMBERS WOULD BE 1.5x TO 24.6x FASTER IF THEY CONVERTED, and
/// this policy cannot see it. Forcing conversion is 24.60x on `air03`, 11.66x
/// on `l152lav`, 10.48x on `air05`, 10.32x on `mod010`, 6.50x on `enigma`,
/// 3.49x on `mod008`, 2.74x on `misc07`, 2.14x on `misc03`, 1.50x on `p0201`
/// — every one bit-identical at identical pivot counts — while costing 3x-7x
/// on `dcmulti`, `gt2`, `lseu`, `p0282`, `p0548`, `p2756`, `qnet1`, `qiu`.
/// ONE quantity separates all 28 measured models with zero exceptions, and it
/// is not the one this policy watches: whether the FRACTION-FREE entries
/// (`Δ·c`) stay inline. Winners are 100.00% FF-inline; losers 0.00-51.13%.
/// `Δ` is already carried in [`ExactLp::det`] from the first pivot, so the
/// missing trigger costs one multiply and one range check per sampled entry
/// and no new state. Tuning THIS threshold is not the lever: at 100% across
/// 18 models exactly one switch point moved and nothing new converted.
///
/// Before building that trigger, settle whether the rim is on a path anyone
/// pays for: across ten 30s MILP solves and 1.36M nodes the rim was entered
/// ONCE for 0.00s, and even the pure-LP lane reaches it only under
/// `--no-float` (`mas76_lprelax` is 0.037s float-first, 1.241s on the rim).
const SWITCH_WINDOW: u64 = 16;
const SWITCH_INLINE_PERCENT: u64 = 99;
const SWITCH_SUSTAIN: u32 = 2;
/// One rewritten row in this many is censused — see [`ExactLp::census`].
const SWITCH_SAMPLE_STRIDE: u64 = 8;

/// The three constants, read once per census window. A test build can move
/// them (that is how the numbers in [`SWITCH_WINDOW`]'s note were produced);
/// a shipped build cannot, and has no input to this decision but the census.
#[inline]
fn switch_params() -> (u64, u64, u32) {
    #[cfg(test)]
    {
        probe::params()
    }
    #[cfg(not(test))]
    {
        (SWITCH_WINDOW, SWITCH_INLINE_PERCENT, SWITCH_SUSTAIN)
    }
}

/// Iteration/deadline budget for one solve.
#[derive(Debug, Clone)]
pub(crate) struct Budget {
    pub deadline: Option<Instant>,
    pub max_iters: u64,
}

impl Budget {
    /// The default iteration cap for a problem with `vars` variables:
    /// generous (Bland terminates on its own), scaled to size.
    pub(crate) fn default_iters(vars: usize) -> u64 {
        20_000 + 200 * vars as u64
    }
}

/// A feasibility verdict.
#[derive(Debug)]
pub(crate) enum LpFeasibility {
    Feasible,
    Infeasible(FarkasCertificate),
    Unknown(UnknownReason),
}

/// An optimization verdict. `value` excludes the model's objective offset
/// (the session layer adds it); `multipliers` are the dual-bound evidence
/// over model facts, ready for [`crate::cert::OptimalityCertificate`].
#[derive(Debug)]
pub(crate) enum LpOptimum {
    Optimal {
        value: BigRational,
        multipliers: Vec<Multiplier>,
    },
    Unbounded,
    Infeasible(FarkasCertificate),
    Unknown(UnknownReason),
}

/// One tableau row: `basic = Σ (terms / den)` where every term variable is
/// nonbasic. Rows are homogeneous (no constant): logical variables carry the
/// row constants as bounds instead.
///
/// ONE STRUCT, TWO REPRESENTATIONS. In [`Form::Reduced`] `den` is 1 and the
/// stored values ARE the coefficients, fully reduced — the rim's historical
/// tableau, unchanged. In [`Form::FractionFree`] the stored values are
/// INTEGERS and the coefficient is `t/den`. `den > 0` in both, so a SIGN test
/// may read the stored value directly; every arithmetic use goes through
/// [`coefficient`].
#[derive(Debug, Clone)]
struct TabRow {
    basic: u32,
    /// Sorted by variable index; no zeros. Numerators over `den`.
    terms: Vec<(u32, Rational)>,
    /// This row's divisor. Always 1 under [`Form::Reduced`]. Under
    /// [`Form::FractionFree`] it is `|det B|` for the basis at the pivot that
    /// last REWROTE this row — which is the current basis only for the rows
    /// that pivot touched. A row a pivot does not touch keeps its value, hence
    /// its numerators AND its divisor, and costs that pivot nothing.
    ///
    /// PER ROW, NOT SHARED, because a single shared divisor makes every pivot
    /// rewrite every row — the reduced form never did, and neither does this.
    /// MEASURED by the round that built the fraction-free arm: one shared
    /// divisor ran `dcmulti` in 7.477s against the reduced form's 0.579s and
    /// got `qnet1` through 12,462 Phase I pivots against its 53,747; per-row
    /// divisors take those to 3.028s and 23,220.
    den: Rational,
}

impl TabRow {
    /// The stored NUMERATOR of `var`'s coefficient — `den` times the true
    /// value. Sign-faithful in both forms (`den > 0`); not the coefficient.
    fn numer_of(&self, var: u32) -> Option<&Rational> {
        self.terms
            .binary_search_by_key(&var, |&(v, _)| v)
            .ok()
            .map(|i| &self.terms[i].1)
    }

    /// The true coefficient of `var`. Borrowed under [`Form::Reduced`], where
    /// the stored value already is it.
    fn coeff_of(&self, var: u32) -> Option<Cow<'_, Rational>> {
        let t = self.numer_of(var)?;
        Some(if is_unit(&self.den) {
            Cow::Borrowed(t)
        } else {
            Cow::Owned(fraction_free::over(t, &self.den))
        })
    }
}

/// The coefficient a stored numerator denotes.
#[inline]
fn coefficient(t: &Rational, den: &Rational) -> Rational {
    if is_unit(den) {
        t.clone()
    } else {
        fraction_free::over(t, den)
    }
}

/// Is this the integer 1? `Rational::Small` is normalised, so the constant is
/// the only representation of it the tableau ever holds.
#[inline]
fn is_unit(r: &Rational) -> bool {
    matches!(r, Rational::Small(1, 1))
}

/// Is this an integer? The invariant the fraction-free form rests on, checked
/// rather than assumed at the one place a solve can enter it.
#[inline]
fn is_integral(r: &Rational) -> bool {
    match r {
        Rational::Small(_, d) => *d == 1,
        Rational::Big(b) => b.is_integer(),
    }
}

/// The exact simplex state. Kept alive across re-solves by
/// [`crate::LpSession`] — the basis persists, so repeated `optimize` calls
/// warm-start (the L0 form of the design's "one factorized model, many
/// objectives").
pub(crate) struct ExactLp {
    n_structural: usize,
    lower: Vec<Option<Rational>>,
    upper: Vec<Option<Rational>>,
    values: Vec<Rational>,
    rows: Vec<TabRow>,
    /// var -> row index when basic.
    basic_of: Vec<Option<u32>>,
    /// The tableau representation in force. Starts [`Form::Reduced`] and moves
    /// to [`Form::FractionFree`] at most once, never back.
    form: Form,
    /// `|det B|` for the current basis of the ROW-INTEGRALISED matrix
    /// `[ΛA | −I]` — a positive integer, 1 at the logical basis, multiplied by
    /// `|c_re|` at each pivot (`det B' = det B · c_re` when a pivot swaps one
    /// basis column). It is the fraction-free form's divisor `Δ`: under
    /// [`Form::FractionFree`] every freshly written row carries it.
    ///
    /// It is also the ONLY thing the reduced form has to carry for the switch
    /// to be legal, and the reason it is carried from the first pivot rather
    /// than reconstructed at the switch: `Δ` has to be a determinant of the
    /// integer matrix for [`fraction_free::fused`]'s divisions to be exact,
    /// and there is no cheap way to recover one from a tableau that did not
    /// track it. Cost is one `Rational` multiply per pivot against a pivot's
    /// whole substitution pass — on `qnet1`, 80,733 of them against 1.3
    /// BILLION entry writes.
    det: Rational,
    /// Per-row integralising scale `λ_r > 0`: the tableau's logical variable
    /// for row `r` is `λ_r·(a_r·x)`, so the matrix it pivots on is integral
    /// and `det` starts at 1. `λ_r = 1` for every row of an
    /// integer-coefficient model. A multiplier over row `r`'s bound is scaled
    /// BACK by `λ_r` on the way out (see [`ExactLp::multiplier`]).
    row_scale: Vec<Rational>,
    /// Set when a fraction-free division left a remainder — i.e. when the
    /// tableau stopped satisfying the identity its arithmetic rests on. Every
    /// verdict then becomes `Unknown`: the rim never reports a result derived
    /// from state it cannot justify.
    poisoned: bool,
    /// May this solve switch at all? Cleared when a row could not be
    /// integralised on the inline path (see [`ExactLp::new_within`]), which
    /// leaves `det` meaningless and the switch unavailable. It also switches
    /// OFF the census and the determinant carry, so a model that cannot use
    /// the policy does not pay for it.
    convertible: bool,
    /// The current census window: entries written, of which inline, and pivots
    /// so far. Reset every [`SWITCH_WINDOW`] pivots.
    window_entries: u64,
    window_inline: u64,
    window_pivots: u64,
    /// Consecutive windows below [`SWITCH_INLINE_PERCENT`].
    cold_windows: u32,
    /// Rewritten rows seen, for the census's fixed-stride sampling.
    census_seq: u64,
}

/// Direction a nonbasic variable is moved.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dir {
    Up,
    Down,
}

mod construction;
mod pivot;

impl ExactLp {
    /// Build from a model, relaxing integrality (binary columns become their
    /// `[lb, ub]` boxes). Model must be validated. An `Infeasible` verdict
    /// from the relaxation is valid for the unrelaxed model too.
    ///
    /// Construction itself is a full exact-rational pass over the matrix — on a
    /// 1.85M-nnz NN model it is SECONDS of gcd-reducing multiplies, and it used to
    /// run un-deadlined before `make_feasible`'s per-iteration checks could fire
    /// (a profiler sample of a deadline overshoot landed 53% of its hits here).
    /// [`Self::new_within`] bounds it; `new` remains for callers with no
    /// construction deadline whose cost the caller owns.
    pub(crate) fn new(model: &Model) -> Self {
        Self::new_within(model, None).expect("no deadline to miss")
    }

    /// The current structural point, exact.
    pub(crate) fn structural_values(&self) -> Vec<BigRational> {
        let mut unlimited = |_| true;
        self.structural_values_with_work(&mut unlimited)
            .expect("unbounded exact point conversion")
    }

    pub(crate) fn structural_values_with_work<F>(&self, work: &mut F) -> Option<Vec<BigRational>>
    where
        F: FnMut(usize) -> bool + ?Sized,
    {
        let mut values = Vec::with_capacity(self.n_structural);
        for (index, value) in self.values[..self.n_structural].iter().enumerate() {
            if index & 0xff == 0 && !work(0x100.min(self.n_structural.saturating_sub(index))) {
                return None;
            }
            values.push(value.to_big());
        }
        Some(values)
    }

    fn fact_of(&self, var: u32, side: BoundSide) -> FactRef {
        if (var as usize) < self.n_structural {
            FactRef::ColBound {
                col: Col(var),
                side,
            }
        } else {
            FactRef::RowBound {
                row: Row(var - self.n_structural as u32),
                side,
            }
        }
    }

    fn below_lower(&self, var: usize) -> bool {
        matches!(&self.lower[var], Some(lb) if self.values[var] < *lb)
    }

    fn above_upper(&self, var: usize) -> bool {
        matches!(&self.upper[var], Some(ub) if self.values[var] > *ub)
    }

    fn can_increase(&self, var: usize) -> bool {
        match &self.upper[var] {
            Some(ub) => self.values[var] < *ub,
            None => true,
        }
    }

    fn can_decrease(&self, var: usize) -> bool {
        match &self.lower[var] {
            Some(lb) => self.values[var] > *lb,
            None => true,
        }
    }

    /// Shift a nonbasic variable by `delta`, updating every dependent basic
    /// value.
    fn shift_nonbasic(&mut self, var: u32, delta: &Rational) {
        if delta.is_zero() {
            return;
        }
        self.values[var as usize] += delta.clone();
        for row in &self.rows {
            if let Some(c) = row.coeff_of(var) {
                let d = c.into_owned() * delta.clone();
                self.values[row.basic as usize] += d;
            }
        }
    }

    /// Phase A: repair basic-variable bound violations (Bland). On success
    /// every variable is within its bounds.
    pub(crate) fn make_feasible(&mut self, budget: &Budget) -> LpFeasibility {
        let mut iters: u64 = 0;
        loop {
            iters += 1;
            if iters > budget.max_iters {
                return LpFeasibility::Unknown(UnknownReason::IterationLimit);
            }
            // EVERY iteration, not every 64th. One iteration of an exact simplex is a pass in
            // rational arithmetic over every column, which on a model like nw04 (87,482 of them)
            // takes about a second -- so a check every 64 iterations first fires a minute after
            // the deadline it is supposed to be enforcing. `Instant::now()` costs ~20ns against
            // that; there was never anything to save by batching it.
            if let Some(d) = budget.deadline {
                if Instant::now() >= d {
                    return LpFeasibility::Unknown(UnknownReason::Timeout);
                }
            }
            // Smallest-index violated basic variable.
            let violated = self
                .rows
                .iter()
                .enumerate()
                .filter(|(_, row)| {
                    self.below_lower(row.basic as usize) || self.above_upper(row.basic as usize)
                })
                .min_by_key(|(_, row)| row.basic);
            let (ri, need_increase) = match violated {
                None => {
                    // Nonbasic variables sit at bounds or at 0 (free) by
                    // construction and only move within bounds; basics are
                    // now repaired.
                    return LpFeasibility::Feasible;
                }
                Some((ri, row)) => (ri, self.below_lower(row.basic as usize)),
            };
            let row = &self.rows[ri];
            let basic = row.basic;
            // Smallest-index nonbasic that can absorb the repair. The sign test
            // reads the stored numerator directly — `den > 0`, so the sign is
            // the coefficient's own, in either representation.
            let mut entering: Option<(u32, Rational)> = None;
            for (v, t) in &row.terms {
                let pos = t > &Rational::zero();
                let suitable = if need_increase {
                    // basic must increase: raise a positive-coeff var or
                    // lower a negative-coeff var.
                    (pos && self.can_increase(*v as usize))
                        || (!pos && self.can_decrease(*v as usize))
                } else {
                    (pos && self.can_decrease(*v as usize))
                        || (!pos && self.can_increase(*v as usize))
                };
                if suitable {
                    entering = Some((*v, t.clone()));
                    break; // terms sorted by index: first hit is Bland's choice
                }
            }
            let Some((evar, enumer)) = entering else {
                return LpFeasibility::Infeasible(self.farkas_from_row(ri, need_increase));
            };
            // Move entering so that basic lands exactly on its violated bound.
            let target = if need_increase {
                self.lower[basic as usize].clone().expect("violated lower")
            } else {
                self.upper[basic as usize].clone().expect("violated upper")
            };
            let delta_basic = target - self.values[basic as usize].clone();
            let delta_e = delta_basic / coefficient(&enumer, &self.rows[ri].den);
            self.shift_nonbasic(evar, &delta_e);
            // basic now sits on its bound (exactly, by construction).
            self.pivot(ri, evar);
            if self.poisoned {
                return LpFeasibility::Unknown(poisoned_reason());
            }
        }
    }

    /// The Farkas certificate from a conflicting row (no suitable entering
    /// variable). `need_increase` is the direction the basic variable had to
    /// move.
    fn farkas_from_row(&self, ri: usize, need_increase: bool) -> FarkasCertificate {
        let row = &self.rows[ri];
        let basic = row.basic;
        let mut multipliers = Vec::with_capacity(row.terms.len() + 1);
        let one = BigRational::from_integer(1.into());
        let basic_side = if need_increase {
            // basic < lb, and every term is saturated against raising it.
            BoundSide::Lower
        } else {
            // basic > ub, and every term is saturated against lowering it.
            BoundSide::Upper
        };
        multipliers.push(self.multiplier(basic, basic_side, one));
        for (v, t) in &row.terms {
            let c = coefficient(t, &row.den);
            let positive = c > Rational::zero();
            let (side, coeff) = match (need_increase, positive) {
                (true, true) => (BoundSide::Upper, c.to_big()),
                (true, false) => (BoundSide::Lower, -c.to_big()),
                (false, true) => (BoundSide::Lower, c.to_big()),
                (false, false) => (BoundSide::Upper, -c.to_big()),
            };
            multipliers.push(self.multiplier(*v, side, coeff));
        }
        FarkasCertificate { multipliers }
    }

    /// One certificate multiplier over a MODEL fact.
    ///
    /// The tableau's logical variable for row `r` is `λ_r·(a_r·x)` (see
    /// [`Self::row_scale`]), so a tableau multiplier `μ` on its bound is `μ·λ_r`
    /// on the model's own row bound: the model fact `a_r·x ≥ b_r` has to be
    /// scaled by `λ_r` to become the fact the tableau reasoned with. Structural
    /// columns are never scaled, so their multipliers pass through untouched —
    /// as does every multiplier of an integer-coefficient model, where every
    /// `λ_r` is 1.
    fn multiplier(&self, var: u32, side: BoundSide, coeff: BigRational) -> Multiplier {
        let coeff = match (var as usize).checked_sub(self.n_structural) {
            Some(r) if !is_unit(&self.row_scale[r]) => coeff * self.row_scale[r].to_big(),
            _ => coeff,
        };
        Multiplier {
            fact: self.fact_of(var, side),
            coeff,
        }
    }

    /// Express a structural objective over the current nonbasic variables.
    fn objective_row(&self, obj: &[(u32, Rational)]) -> Vec<(u32, Rational)> {
        let mut row = Vec::new();
        for (var, coefficient) in obj {
            if coefficient.is_zero() {
                continue;
            }
            match self.basic_of[*var as usize] {
                None => merge_term(&mut row, *var, coefficient.clone()),
                Some(index) => {
                    let tableau = &self.rows[index as usize];
                    let scaled = if is_unit(&tableau.den) {
                        coefficient.clone()
                    } else {
                        coefficient.clone() / tableau.den.clone()
                    };
                    for (term_var, term_coefficient) in &tableau.terms {
                        merge_term(
                            &mut row,
                            *term_var,
                            scaled.clone() * term_coefficient.clone(),
                        );
                    }
                }
            }
        }
        row
    }

    /// Phase B: minimize `Σ obj·x` (structural coefficients) from a feasible
    /// state. Returns the exact optimum and dual evidence.
    pub(crate) fn minimize(&mut self, obj: &[(u32, Rational)], budget: &Budget) -> LpOptimum {
        match self.make_feasible(budget) {
            LpFeasibility::Feasible => {}
            LpFeasibility::Infeasible(cert) => return LpOptimum::Infeasible(cert),
            LpFeasibility::Unknown(r) => return LpOptimum::Unknown(r),
        }
        let mut d = self.objective_row(obj);
        let mut iters: u64 = 0;
        loop {
            iters += 1;
            if iters > budget.max_iters {
                return LpOptimum::Unknown(UnknownReason::IterationLimit);
            }
            // Every iteration -- see `make_feasible`.
            if let Some(dl) = budget.deadline {
                if Instant::now() >= dl {
                    return LpOptimum::Unknown(UnknownReason::Timeout);
                }
            }
            // Bland: smallest-index improving nonbasic.
            let mut chosen: Option<(u32, Rational, Dir)> = None;
            for (v, dc) in &d {
                debug_assert!(
                    self.basic_of[*v as usize].is_none(),
                    "obj term became basic"
                );
                if dc.is_zero() {
                    continue;
                }
                let dir = if dc < &Rational::zero() {
                    Dir::Up
                } else {
                    Dir::Down
                };
                let movable = match dir {
                    Dir::Up => self.can_increase(*v as usize),
                    Dir::Down => self.can_decrease(*v as usize),
                };
                if movable {
                    chosen = Some((*v, dc.clone(), dir));
                    break; // d kept sorted: first hit is Bland's choice
                }
            }
            let Some((evar, _, dir)) = chosen else {
                return self.optimal_from(&d);
            };
            // Step limit: own opposite bound, then ratio test over rows.
            let own_limit: Option<Rational> = match dir {
                Dir::Up => self.upper[evar as usize]
                    .as_ref()
                    .map(|ub| ub.clone() - self.values[evar as usize].clone()),
                Dir::Down => self.lower[evar as usize]
                    .as_ref()
                    .map(|lb| self.values[evar as usize].clone() - lb.clone()),
            };
            // (limit, limiting row, limiting basic var). Bland tie-break on
            // smallest basic index.
            let mut row_limit: Option<(Rational, usize, u32)> = None;
            for (ri, row) in self.rows.iter().enumerate() {
                let Some(t) = row.numer_of(evar) else {
                    continue;
                };
                // basic delta per unit step: +c (Up) or −c (Down). `den > 0`,
                // so the stored numerator carries the sign.
                let increases_basic = match dir {
                    Dir::Up => t > &Rational::zero(),
                    Dir::Down => t < &Rational::zero(),
                };
                let b = row.basic as usize;
                let room = if increases_basic {
                    self.upper[b]
                        .as_ref()
                        .map(|ub| ub.clone() - self.values[b].clone())
                } else {
                    self.lower[b]
                        .as_ref()
                        .map(|lb| self.values[b].clone() - lb.clone())
                };
                let Some(room) = room else { continue };
                let rate = coefficient(t, &row.den).abs();
                let limit = room / rate;
                let replace = match &row_limit {
                    None => true,
                    Some((best, _, best_var)) => {
                        limit < *best || (limit == *best && row.basic < *best_var)
                    }
                };
                if replace {
                    row_limit = Some((limit, ri, row.basic));
                }
            }
            match (own_limit, row_limit) {
                (None, None) => return LpOptimum::Unbounded,
                (Some(own), None) => {
                    // Bound flip: move to the opposite bound.
                    let delta = signed(&own, dir);
                    self.shift_nonbasic(evar, &delta);
                }
                (own, Some((limit, ri, _))) => {
                    if let Some(own) = own {
                        if own <= limit {
                            let delta = signed(&own, dir);
                            self.shift_nonbasic(evar, &delta);
                            continue;
                        }
                    }
                    let delta = signed(&limit, dir);
                    self.shift_nonbasic(evar, &delta);
                    // Update the objective row: substitute the entering
                    // variable using the post-pivot row.
                    self.pivot(ri, evar);
                    if self.poisoned {
                        return LpOptimum::Unknown(poisoned_reason());
                    }
                    let e_coeff = d
                        .binary_search_by_key(&evar, |&(v, _)| v)
                        .ok()
                        .map(|i| d[i].1.clone());
                    if let Some(dc) = e_coeff {
                        d.retain(|&(v, _)| v != evar);
                        // The row is the POST-pivot pivot row, in whatever
                        // divisor's units that pivot left it.
                        let den = self.rows[ri].den.clone();
                        let scaled = if is_unit(&den) { dc } else { dc / den };
                        let expr = self.rows[ri].terms.clone();
                        for (tv, tc) in expr {
                            merge_term(&mut d, tv, scaled.clone() * tc);
                        }
                    }
                }
            }
        }
    }

    /// Build the optimality verdict from the reduced-cost row at optimum.
    fn optimal_from(&self, d: &[(u32, Rational)]) -> LpOptimum {
        let mut value = Rational::zero();
        let mut multipliers = Vec::new();
        for (v, dc) in d {
            if dc.is_zero() {
                continue;
            }
            value += dc.clone() * self.values[*v as usize].clone();
            // dc > 0: v is pinned at its lower bound (else it could improve).
            // dc < 0: pinned at its upper bound.
            let (side, coeff) = if dc > &Rational::zero() {
                (BoundSide::Lower, dc.to_big())
            } else {
                (BoundSide::Upper, -dc.to_big())
            };
            multipliers.push(self.multiplier(*v, side, coeff));
        }
        LpOptimum::Optimal {
            value: value.to_big(),
            multipliers,
        }
    }
}

/// The reason a poisoned tableau reports. It cannot fire on a correct
/// fraction-free pivot: `Δ` divides every combination the identity produces.
/// If it ever does, the rim withholds the verdict rather than continuing on
/// arithmetic it has just caught being wrong.
fn poisoned_reason() -> UnknownReason {
    UnknownReason::WitnessRejected {
        detail: "exact rim: fraction-free tableau division left a remainder".to_string(),
    }
}

/// `terms − d·x_e + d·expr`, keeping sorted order and dropping zeros.
/// `terms` must contain `x_e` with coefficient `d`.
fn substitute(
    terms: &[(u32, Rational)],
    evar: u32,
    d: &Rational,
    expr: &[(u32, Rational)],
) -> Vec<(u32, Rational)> {
    let mut out: Vec<(u32, Rational)> =
        terms.iter().filter(|&&(v, _)| v != evar).cloned().collect();
    for (v, c) in expr {
        merge_term(&mut out, *v, d.clone() * c.clone());
    }
    out
}

/// Add `coeff·var` into a sorted sparse vector, dropping resulting zeros.
fn merge_term(vec: &mut Vec<(u32, Rational)>, var: u32, coeff: Rational) {
    if coeff.is_zero() {
        return;
    }
    match vec.binary_search_by_key(&var, |&(v, _)| v) {
        Ok(i) => {
            vec[i].1 += coeff;
            if vec[i].1.is_zero() {
                vec.remove(i);
            }
        }
        Err(i) => vec.insert(i, (var, coeff)),
    }
}

/// `+magnitude` for `Up`, `−magnitude` for `Down`.
fn signed(magnitude: &Rational, dir: Dir) -> Rational {
    match dir {
        Dir::Up => magnitude.clone(),
        Dir::Down => -magnitude.clone(),
    }
}

#[cfg(test)]
mod tests;
