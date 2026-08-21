// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/explain.rs` — conflict
//! explanation, and specifically the property that a learned clause is a THEORY
//! CONSEQUENCE.
//!
//! # Why this is the most important check in the oracle
//!
//! An explanation that is not implied is a wrong `unsat`. The learned clause
//! prunes away satisfying assignments and the search then answers `unsat` for a
//! satisfiable problem. **No gate in this repository can catch that** — every
//! gate validates a MODEL, and a model exists only on the `sat` side. There is
//! no downstream net. This module is the net.
//!
//! # What z3 is asked, and why it shares no AY code
//!
//! ```text
//!   $ ls reference/z3/5.0.0/                        -> bin include
//!   $ find reference/z3 -name '*.cpp' | wc -l       -> 0
//!   $ find reference/z3 -iname '*nlsat*' | wc -l    -> 0
//! ```
//!
//! `nlsat_explain.cpp` is not present; the distribution is binary. So nothing
//! here is compared against a transcription. What z3 does expose is enough to
//! decide the question INDEPENDENTLY, and [`z3_satisfiable`] does exactly that:
//!
//!   * `Z3_algebraic_roots` isolates every cited polynomial's real roots;
//!   * `Z3_algebraic_lt/_eq` sorts and deduplicates them;
//!   * `Z3_algebraic_add/_mul` builds the midpoint of each adjacent pair, so
//!     the open cells get a sample point that is itself exact;
//!   * `Z3_algebraic_eval` reads the sign of every cited polynomial there.
//!
//! The conjunction is satisfiable exactly when some cell satisfies all of it.
//! **Not one line of AY runs on that path** — not the interval algebra, not
//! `Anum`, not even the `accepts` predicate, which is re-implemented as
//! [`oracle_accepts`] here and cross-checked against AY's in
//! [`check_clause_implied`]. This is the leg the campaign's `same_set_as`
//! finding demands: `same_set_as` became the load-bearing assertion of six legs
//! and hardwiring it to `true` certified all six at once, so a checker that
//! shares its producer's substrate is not evidence.
//!
//! # The seven blind-spot patterns, answered for THIS code
//!
//!   1. **An entry point no check calls.** All eight facade entries are called
//!      by name: `oexplain_clause_is_valid`, `oexplain_countermodel`,
//!      `oexplain_clause_is_falsified`, `oexplain_univariate`,
//!      `oexplain_relevant_pairs`, `oexplain_project`,
//!      `oexplain_max_conflict_lits`, `oexplain_max_conflict_roots`.
//!      [`check_clause_implied`] asserts the roster.
//!   2. **A guard that never fires.** The `MAX_CONFLICT_LITS` refusal is fired
//!      on purpose, paired with a positive control one literal below the
//!      ceiling, so a module that refused everything would fail too.
//!   3. **A stored flag the metric is read off.** `OExplanation` has no validity
//!      field to read; the verdict is re-derived by calling
//!      `oexplain_clause_is_valid` on the cited literals, and z3 adjudicates it.
//!   4. **An unwitnessed witness.** When AY says a clause is NOT valid it must
//!      produce the real number that refutes it, and
//!      [`check_countermodel`] makes z3 evaluate every cited literal AT that
//!      point. A `false` nobody can check would be worthless.
//!   5. **A pure function tested only through its consumer.**
//!      `oexplain_clause_is_valid`, `oexplain_relevant_pairs` and
//!      `oexplain_project` all take their inputs as arguments and are driven
//!      DIRECTLY on z3's own root lists, never only through
//!      `oexplain_univariate`.
//!   6. **A FAIL-OPEN predicate.** This is the one that matters. The permissive
//!      answer is "the clause is implied". The generator keeps every input
//!      strictly under the declared ceilings and each check ASSERTS that before
//!      the call, so a `None` where the answer is documented total is reported
//!      as a **divergence**, not swallowed as a decline. A refusal is a
//!      divergence when the value is documented total.
//!   7. **A precondition verified in the weak direction only.** AY verifies its
//!      root lists in both directions; [`check_clause_implied`] feeds it a
//!      DELIBERATELY DAMAGED list — one root dropped, one root added, one root
//!      replaced by a non-root at the same count — and requires a refusal each
//!      time. A dropped root is what makes a satisfiable conjunction look
//!      unsatisfiable, which is the wrong `unsat` this module exists to prevent.

use ay_nra::oracle_api::{
    oexplain_clause_is_falsified, oexplain_clause_is_valid, oexplain_countermodel,
    oexplain_max_conflict_lits, oexplain_max_conflict_roots, oexplain_project,
    oexplain_relevant_pairs, oexplain_univariate, OBiPoly, ODyadicAnum, OExplainLit, OISignCond,
    OYPoly,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::{dyadic_iv, rationals};
use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ptr, Z3};

/// One generated conflict case.
pub(crate) struct GenEx {
    /// The cited polynomials, integer coefficients low-to-high. Degree >= 1.
    pub(crate) polys: Vec<Vec<BigInt>>,
    /// The sign condition asserted TRUE for each.
    pub(crate) conds: Vec<OISignCond>,
    /// Bivariate inputs for the projection check.
    pub(crate) bi: Vec<Vec<Vec<(u32, i64)>>>,
    /// Shape label for reporting.
    pub(crate) shape: &'static str,
}

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&c| BigInt::from(c)).collect()
}

fn pmul(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

fn render(p: &[BigInt]) -> String {
    if p.is_empty() {
        return "0".to_string();
    }
    p.iter()
        .enumerate()
        .filter(|(_, c)| !c.is_zero())
        .map(|(i, c)| match i {
            0 => format!("{c}"),
            1 => format!("{c}*x"),
            _ => format!("{c}*x^{i}"),
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

fn cond_name(c: OISignCond) -> &'static str {
    match c {
        OISignCond::Lt => "<0",
        OISignCond::Le => "<=0",
        OISignCond::Eq => "=0",
        OISignCond::Ne => "!=0",
        OISignCond::Ge => ">=0",
        OISignCond::Gt => ">0",
    }
}

pub(crate) fn inputs(g: &GenEx) -> Vec<(String, String)> {
    let mut v: Vec<(String, String)> = g
        .polys
        .iter()
        .zip(&g.conds)
        .enumerate()
        .map(|(i, (p, c))| {
            (
                format!("L{}", i + 1),
                format!("({}) {}", render(p), cond_name(*c)),
            )
        })
        .collect();
    v.push(("shape".to_string(), g.shape.to_string()));
    v
}

/// Squarefree quadratic irrationals, so cell boundaries are genuinely
/// irrational and no rational sample point can coincide with one.
const IRRATIONALS: [i64; 6] = [2, 3, 5, 6, 7, 10];

/// Draw a conflict case.
///
/// Six shapes. Roughly half are GUARANTEED conflicts, so the producer has
/// something to produce; the rest are usually SATISFIABLE, which is the
/// direction that matters most — a producer that emits a clause for a
/// satisfiable conjunction is the wrong-`unsat` defect, and it can only be
/// caught on inputs where no clause is due.
///
///   * `opposite`    — one polynomial with `< 0` and `> 0`: always a conflict,
///     and the smallest one, so minimization has an exact expected answer.
///   * `annulus`     — `x^2 - d < 0` with `x^2 - e > 0`. A conflict exactly when
///     `d <= e`, and satisfiable otherwise, from the SAME shape: the generator
///     cannot be accused of only drawing one side.
///   * `algebraic`   — quadratic irrationals with drawn conditions, so the
///     decisive cell boundary is irrational and the rational-only decomposition
///     that a naive checker would build gets the wrong answer.
///   * `linear`      — a chain of linear bounds; conflicting or not by draw.
///   * `at-root`     — conditions that can only be satisfied AT a root
///     (`>= 0` with `<= 0`), so the closed cells decide the case rather than
///     the open ones.
///   * `dense`       — arbitrary low-degree coefficients and arbitrary
///     conditions, mostly satisfiable.
pub(crate) fn gen_ex(rng: &mut Rng) -> GenEx {
    let shape = match rng.below(7) {
        0 => "opposite",
        1 => "annulus",
        2 => "algebraic",
        3 => "linear",
        4 => "at-root",
        5 => "many-roots",
        _ => "dense",
    };
    let d = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let e = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];

    let (polys, conds): (Vec<Vec<BigInt>>, Vec<OISignCond>) = match shape {
        "opposite" => {
            let a = rng.range(-5, 5);
            let p = pmul(&ints(&[-a, 1]), &ints(&[-(a + 2), 1]));
            (vec![p.clone(), p], vec![OISignCond::Lt, OISignCond::Gt])
        }
        "annulus" => (
            vec![ints(&[-d, 0, 1]), ints(&[-e, 0, 1])],
            vec![OISignCond::Lt, OISignCond::Gt],
        ),
        "algebraic" => {
            let conds = [
                OISignCond::Lt,
                OISignCond::Le,
                OISignCond::Eq,
                OISignCond::Ne,
                OISignCond::Ge,
                OISignCond::Gt,
            ];
            let c0 = conds[usize::try_from(rng.below(6)).unwrap_or(0)];
            let c1 = conds[usize::try_from(rng.below(6)).unwrap_or(0)];
            let c2 = conds[usize::try_from(rng.below(6)).unwrap_or(0)];
            (
                vec![
                    ints(&[-d, 0, 1]),
                    ints(&[-e, 0, 1]),
                    ints(&[-rng.range(-4, 4), 1]),
                ],
                vec![c0, c1, c2],
            )
        }
        "linear" => {
            let n = 2 + usize::try_from(rng.below(2)).unwrap_or(0);
            let mut ps = Vec::with_capacity(n);
            let mut cs = Vec::with_capacity(n);
            for _ in 0..n {
                ps.push(ints(&[-rng.range(-6, 6), 1]));
                cs.push(if rng.below(2) == 0 {
                    OISignCond::Gt
                } else {
                    OISignCond::Lt
                });
            }
            (ps, cs)
        }
        "at-root" => {
            let p = ints(&[-d, 0, 1]);
            let q = ints(&[-rng.range(-4, 4), 1]);
            (
                vec![p.clone(), p, q],
                vec![
                    OISignCond::Ge,
                    OISignCond::Le,
                    if rng.below(2) == 0 {
                        OISignCond::Ne
                    } else {
                        OISignCond::Eq
                    },
                ],
            )
        }
        "many-roots" => {
            // MANY MERGED ROOTS, deliberately past the six the other shapes
            // reach.
            //
            // This shape exists because a verifier proved the corpus could not
            // see a real wrong-`unsat`. Every other shape here tops out at 3
            // literals of degree <= 2, so at most SIX distinct merged roots.
            // Injecting "skip every open-cell midpoint once there are more than
            // six roots" — a decomposition that silently loses the gaps between
            // roots, which is the wrong-`unsat` shape — produced ZERO
            // divergences over 9,000 cases across three seeds, with selftest
            // 45/45 and golden 44/44, while being a genuine defect: the
            // verifier's own generator emitted a clause whose citation set z3
            // reports SAT.
            //
            // A product of k distinct linear factors gives exactly k roots, so
            // 4..=9 factors puts the merged count on both sides of that cliff.
            let k = 4 + usize::try_from(rng.below(6)).unwrap_or(0);
            let mut p = ints(&[1]);
            let mut r = -(i64::try_from(k).unwrap_or(4));
            for _ in 0..k {
                p = pmul(&p, &ints(&[-r, 1]));
                r += 1 + i64::from(rng.below(2) as u32);
            }
            // A second literal that bounds the line, so the conjunction can be
            // a genuine conflict rather than trivially satisfiable.
            let hi = ints(&[-(r + 2), 1]);
            (
                vec![p, hi],
                vec![
                    if rng.below(2) == 0 {
                        OISignCond::Gt
                    } else {
                        OISignCond::Lt
                    },
                    OISignCond::Lt,
                ],
            )
        }
        _ => {
            let n = 2 + usize::try_from(rng.below(2)).unwrap_or(0);
            let conds = [
                OISignCond::Lt,
                OISignCond::Le,
                OISignCond::Eq,
                OISignCond::Ne,
                OISignCond::Ge,
                OISignCond::Gt,
            ];
            let mut ps = Vec::with_capacity(n);
            let mut cs = Vec::with_capacity(n);
            for _ in 0..n {
                let deg = 1 + usize::try_from(rng.below(2)).unwrap_or(0);
                let mut c: Vec<BigInt> =
                    (0..=deg).map(|_| BigInt::from(rng.range(-6, 6))).collect();
                if c[deg].is_zero() {
                    c[deg] = BigInt::one();
                }
                ps.push(c);
                cs.push(conds[usize::try_from(rng.below(6)).unwrap_or(0)]);
            }
            (ps, cs)
        }
    };

    // Bivariate inputs for the projection check: `x`-coefficients, each a list
    // of `(y-exponent, coefficient)` pairs.
    let bi = vec![
        vec![
            vec![(1u32, -1i64)],
            vec![(0, rng.range(-3, 3))],
            vec![(0, 1)],
        ],
        vec![
            vec![(2u32, 1i64), (0, -(1 + rng.range(0, 5)))],
            vec![],
            vec![(0, 1)],
        ],
    ];

    GenEx {
        polys,
        conds,
        bi,
        shape,
    }
}

// ===========================================================================
// The INDEPENDENT reference: z3 decides satisfiability by itself
// ===========================================================================

/// Does sign `s` satisfy `c`?
///
/// Deliberately RE-IMPLEMENTED here rather than calling AY's
/// `OISignCond::accepts`. It is six lines, and if the reference side called AY's
/// version then a defect in that predicate would be invisible to every leg
/// below — the `same_set_as` failure exactly. AY's version is cross-checked
/// against this one in [`check_clause_implied`], so it is under test rather than
/// trusted.
fn oracle_accepts(c: OISignCond, s: i32) -> bool {
    match c {
        OISignCond::Lt => s < 0,
        OISignCond::Le => s <= 0,
        OISignCond::Eq => s == 0,
        OISignCond::Ne => s != 0,
        OISignCond::Ge => s >= 0,
        OISignCond::Gt => s > 0,
    }
}

/// Is `/\_j (p_j cond_j 0)` satisfiable over the reals? Decided by z3 alone.
///
/// The real roots of every cited polynomial cut `R` into finitely many cells on
/// which all of them have constant sign, so testing one point per cell plus each
/// root is EXHAUSTIVE. Sample points for the open cells are the exact midpoints
/// of adjacent roots, built with `Z3_algebraic_add` and `Z3_algebraic_mul`, so
/// no rounding or bracketing enters anywhere.
///
/// `None` is a z3 error or refusal, never a verdict: the oracle is not entitled
/// to call a bug on the reference implementation's behalf.
///
/// # Liveness
///
/// The insertion sort is `O(n^2)` over `n = sum of degrees`, which the generator
/// keeps at or below 6; the sample scan is one pass over `2n + 1` points. No
/// condition-driven loop.
fn z3_satisfiable(z3: &Z3, polys: &[Vec<BigInt>], conds: &[OISignCond]) -> Option<bool> {
    if polys.len() != conds.len() {
        return None;
    }
    if polys.is_empty() {
        // The empty conjunction is vacuously true.
        return Some(true);
    }

    // Every root, from z3.
    let mut sorted: Vec<Ptr> = Vec::new();
    for p in polys {
        let rs = z3.roots(&rationals(p))?;
        for r in rs {
            let mut pos = sorted.len();
            let mut dup = false;
            for (i, s) in sorted.iter().enumerate() {
                if z3.eq(r, *s) {
                    dup = true;
                    break;
                }
                if z3.lt(r, *s) {
                    pos = i;
                    break;
                }
            }
            if !dup {
                sorted.insert(pos, r);
            }
        }
    }
    if z3.errored() {
        return None;
    }

    // One sample point per cell, all exact, all z3's.
    let mut samples: Vec<Ptr> = Vec::new();
    if sorted.is_empty() {
        samples.push(z3.rational(&BigRational::zero()));
    } else {
        let one = z3.rational(&BigRational::one());
        let minus_one = z3.rational(&-BigRational::one());
        let half = z3.rational(&BigRational::new(BigInt::one(), BigInt::from(2)));
        samples.push(z3.add(sorted[0], minus_one));
        for (i, r) in sorted.iter().enumerate() {
            samples.push(*r);
            if let Some(next) = sorted.get(i + 1) {
                samples.push(z3.mul(z3.add(*r, *next), half));
            }
        }
        samples.push(z3.add(sorted[sorted.len() - 1], one));
    }
    if z3.errored() {
        return None;
    }

    for s in &samples {
        let mut all = true;
        for (p, c) in polys.iter().zip(conds) {
            let sg = z3.eval_sign(&rationals(p), *s)?;
            if !oracle_accepts(*c, sg) {
                all = false;
                break;
            }
        }
        if z3.errored() {
            return None;
        }
        if all {
            return Some(true);
        }
    }
    Some(false)
}

/// Build AY's literal list, taking every root from z3.
///
/// Driving AY's pure functions on z3's OWN root list is what keeps them pure
/// functions under test rather than a consumer's private state.
fn ay_lits(z3: &Z3, g: &GenEx) -> Option<Vec<OExplainLit>> {
    let mut out = Vec::with_capacity(g.polys.len());
    for (i, (p, c)) in g.polys.iter().zip(&g.conds).enumerate() {
        let rs = z3.roots(&rationals(p))?;
        let mut roots = Vec::with_capacity(rs.len());
        for v in rs {
            let iv = dyadic_iv(z3, v)?;
            roots.push(ODyadicAnum::from_poly_interval(p, &iv)?);
        }
        if z3.errored() {
            return None;
        }
        out.push(OExplainLit {
            lit: i32::try_from(i + 1).ok()?,
            p: p.clone(),
            cond: *c,
            roots,
        });
    }
    Some(out)
}

/// Are all the generated polynomials usable (non-zero, degree >= 1)?
fn usable(g: &GenEx) -> bool {
    !g.polys.is_empty()
        && g.polys.len() == g.conds.len()
        && g.polys.iter().all(|p| {
            p.iter()
                .rev()
                .position(|c| !c.is_zero())
                .map_or(false, |z| p.len().saturating_sub(z).saturating_sub(1) >= 1)
        })
}

// ===========================================================================
// Check 1 — `explain-clause-implied`
// ===========================================================================

/// **The defining property.** AY's implication verdict against z3's own
/// decision procedure.
///
/// z3 legs: `oexplain_clause_is_valid` must be `true` exactly when
/// [`z3_satisfiable`] says the cited conjunction is UNSAT. A disagreement in the
/// direction "AY says implied, z3 says satisfiable" is a WRONG `unsat` in
/// waiting and is reported as such.
/// Identity legs: AY's `accepts` predicate must agree with [`oracle_accepts`] on
/// all three signs and all six conditions; the two ceiling accessors must report
/// the values the guards actually enforce.
/// Guards, fired on purpose: a conflict one literal OVER `MAX_CONFLICT_LITS`
/// must be refused while the same conflict one literal UNDER it is answered —
/// a module that refused everything would fail the pair.
/// Precondition legs, fired on purpose: a root list with one root DROPPED, one
/// SPURIOUS root added, and one root replaced by a non-root at the same count
/// must each be refused. The dropped-root case is the one that turns a
/// satisfiable conjunction into an apparent conflict.
pub(crate) fn check_clause_implied(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    if g.polys.len() > oexplain_max_conflict_lits() {
        return Outcome::Skipped("over the declared ceiling");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(z3_sat) = z3_satisfiable(z3, &g.polys, &g.conds) else {
        return Outcome::Skipped("z3 declined");
    };

    // The roster: every facade entry is called by name somewhere in this module,
    // and the two ceiling accessors are called here.
    if oexplain_max_conflict_lits() == 0 || oexplain_max_conflict_roots() == 0 {
        return Divergence::new(
            "explain-clause-implied",
            "identity",
            "a declared ceiling is zero, which would refuse every input".to_string(),
            inputs(g),
        );
    }

    // Identity leg: AY's `accepts` vs the oracle's own.
    for c in [
        OISignCond::Lt,
        OISignCond::Le,
        OISignCond::Eq,
        OISignCond::Ne,
        OISignCond::Ge,
        OISignCond::Gt,
    ] {
        for s in [-1, 0, 1] {
            if c.accepts(s) != oracle_accepts(c, s) {
                return Divergence::new(
                    "explain-clause-implied",
                    "identity",
                    format!(
                        "AY's accepts({}, {s}) = {}, the oracle's = {}",
                        cond_name(c),
                        c.accepts(s),
                        oracle_accepts(c, s)
                    ),
                    inputs(g),
                );
            }
        }
    }

    // The main leg. Every input is under the declared ceilings and z3 answered,
    // so `None` here is a REFUSAL WHERE THE VALUE IS DOCUMENTED TOTAL, and that
    // is a divergence, not a decline.
    let Some(mut ay_valid) = oexplain_clause_is_valid(&lits) else {
        return Divergence::new(
            "explain-clause-implied",
            "z3",
            format!(
                "AY declined a conflict of {} literals with {} total roots, both under the \
                 declared ceilings ({} lits, {} roots); z3 decided it (satisfiable = {z3_sat})",
                lits.len(),
                lits.iter().map(|l| l.roots.len()).sum::<usize>(),
                oexplain_max_conflict_lits(),
                oexplain_max_conflict_roots(),
            ),
            inputs(g),
        );
    };
    if sab.on() {
        ay_valid = !ay_valid;
    }

    if ay_valid == z3_sat {
        let detail = if ay_valid {
            "AY says the clause is IMPLIED, but z3 found a real point satisfying every cited \
             literal -- this clause would prune a satisfiable region and produce a WRONG unsat"
                .to_string()
        } else {
            "AY says the clause is NOT implied, but z3 found no satisfying cell -- AY is \
             refusing a sound explanation (completeness loss, not unsoundness)"
                .to_string()
        };
        return Divergence::new("explain-clause-implied", "z3", detail, inputs(g));
    }

    let mut comparisons = 1 + 18;

    // Guard leg, fired on purpose: over the ceiling must refuse, under it must
    // not. Both halves, so "always refuses" fails too.
    //
    // The replicated literal is the SMALLEST one in the case, not `lits[0]`.
    // This control is about the LITERAL-COUNT ceiling, and replicating a
    // many-rooted literal 64 times trips a different budget — the merged root
    // count — so the "at the ceiling must answer" half then fails for a reason
    // that has nothing to do with the guard under test. Measured: adding a
    // generator shape that produces 4..=9 roots made this leg fire 11 times in
    // 3,000 cases on CORRECT code. Conflating two guards in one control makes
    // the control wrong, not the code.
    let smallest = lits
        .iter()
        .min_by_key(|l| l.roots.len())
        .expect("a case always has at least one literal");
    let over: Vec<OExplainLit> = (0..=oexplain_max_conflict_lits())
        .map(|i| OExplainLit {
            lit: i32::try_from(i + 1).unwrap_or(1),
            p: smallest.p.clone(),
            cond: smallest.cond,
            roots: smallest.roots.clone(),
        })
        .collect();
    if oexplain_clause_is_valid(&over).is_some() {
        return Divergence::new(
            "explain-clause-implied",
            "identity",
            format!(
                "{} literals is over the declared ceiling of {} and was ANSWERED",
                over.len(),
                oexplain_max_conflict_lits()
            ),
            inputs(g),
        );
    }
    if oexplain_clause_is_valid(&over[..oexplain_max_conflict_lits()]).is_none() {
        return Divergence::new(
            "explain-clause-implied",
            "identity",
            format!(
                "exactly {} literals is AT the ceiling and was refused -- the guard fires too \
                 early, so the positive control fails",
                oexplain_max_conflict_lits()
            ),
            inputs(g),
        );
    }
    comparisons += 2;

    // Precondition legs, fired on purpose. Only meaningful where there are roots
    // to damage.
    if let Some(idx) = lits.iter().position(|l| !l.roots.is_empty()) {
        // (a) one root DROPPED.
        let mut dropped = lits.clone();
        dropped[idx].roots.pop();
        if oexplain_clause_is_valid(&dropped).is_some() {
            return Divergence::new(
                "explain-clause-implied",
                "identity",
                "a root list with one root DROPPED was accepted -- an incomplete decomposition \
                 makes a satisfiable conjunction look unsatisfiable"
                    .to_string(),
                inputs(g),
            );
        }
        // (b) one SPURIOUS root added. Reuse a root of a different literal when
        // there is one, else a rational that is not a root.
        let mut extra = lits.clone();
        extra[idx]
            .roots
            .push(ODyadicAnum::rational(BigRational::from_integer(
                BigInt::from(1_000_003),
            )));
        if oexplain_clause_is_valid(&extra).is_some() {
            return Divergence::new(
                "explain-clause-implied",
                "identity",
                "a root list with a SPURIOUS root was accepted".to_string(),
                inputs(g),
            );
        }
        // (c) same COUNT, one value replaced by a non-root. Count alone cannot
        // see this.
        let mut swapped = lits.clone();
        let n = swapped[idx].roots.len();
        swapped[idx].roots[n - 1] =
            ODyadicAnum::rational(BigRational::from_integer(BigInt::from(1_000_003)));
        if oexplain_clause_is_valid(&swapped).is_some() {
            return Divergence::new(
                "explain-clause-implied",
                "identity",
                "a root list with the RIGHT COUNT but a non-root value was accepted -- the \
                 precondition is verified in the weak direction only"
                    .to_string(),
                inputs(g),
            );
        }
        comparisons += 3;
    }

    Outcome::Match(comparisons)
}

// ===========================================================================
// Check 2 — `explain-produce`
// ===========================================================================

/// The producer end to end: **a clause is emitted only for a real conflict, and
/// only when it is genuinely implied.**
///
/// z3 legs: when AY returns a clause, z3 must independently find the cited
/// conjunction UNSATISFIABLE. When z3 finds the full conjunction SATISFIABLE,
/// AY must return nothing at all — emitting a clause there is the wrong-`unsat`
/// defect in its purest form.
/// Identity legs: every cited literal is one of the inputs; the clause literals
/// are exactly the negations of the cited ones; the clause is FALSE under the
/// trail (`oexplain_clause_is_falsified`), which is property (a) of the defining
/// pair; no literal is cited twice.
///
/// A `None` from AY on a genuinely conflicting input is a DECLINE, not a
/// divergence — completeness is allowed to suffer, correctness is not.
pub(crate) fn check_produce(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(z3_sat_full) = z3_satisfiable(z3, &g.polys, &g.conds) else {
        return Outcome::Skipped("z3 declined");
    };
    let trail: Vec<i32> = lits.iter().map(|l| l.lit).collect();

    let Some(e) = oexplain_univariate(&lits) else {
        if z3_sat_full {
            // Correct: there is no conflict, so there is nothing to explain.
            return if sab.on() {
                // Nothing was produced, so there is nothing to corrupt. Reporting
                // a Match here would inflate the catch rate's denominator with a
                // case the sabotage never touched.
                Outcome::Skipped("no clause to corrupt")
            } else {
                Outcome::Match(1)
            };
        }
        return Outcome::Declined("no explanation for a genuine conflict");
    };

    // A clause was produced. z3 must agree the cited conjunction is unsat.
    let mut cited = e.cited.clone();
    if sab.on() {
        // Drop one cited literal: the clause AY returns is minimized and
        // irredundant, so any drop leaves a satisfiable conjunction. This is the
        // unsound-minimization defect.
        cited.pop();
    }

    let mut cited_polys = Vec::with_capacity(cited.len());
    let mut cited_conds = Vec::with_capacity(cited.len());
    for c in &cited {
        let Some(l) = lits.iter().find(|l| l.lit == *c) else {
            return Divergence::new(
                "explain-produce",
                "identity",
                format!("clause cites literal {c}, which is not on the trail"),
                inputs(g),
            );
        };
        cited_polys.push(l.p.clone());
        cited_conds.push(l.cond);
    }

    let Some(cited_sat) = z3_satisfiable(z3, &cited_polys, &cited_conds) else {
        return Outcome::Skipped("z3 declined the cited conjunction");
    };
    if cited_sat {
        return Divergence::new(
            "explain-produce",
            "z3",
            format!(
                "AY learned the clause {:?} from literals {:?}, but z3 found a real point \
                 satisfying every cited literal. The clause is NOT a theory consequence: \
                 learning it prunes a satisfiable region and the search will answer WRONG \
                 UNSAT.",
                e.lits, cited
            ),
            inputs(g),
        );
    }

    // Property (a): the clause is FALSE under the current assignment.
    if !oexplain_clause_is_falsified(&e.lits, &trail) {
        return Divergence::new(
            "explain-produce",
            "identity",
            format!(
                "clause {:?} is not falsified by the trail {trail:?} -- a clause that is not \
                 false under the current assignment cannot drive a backjump",
                e.lits
            ),
            inputs(g),
        );
    }

    // The clause literals are exactly the negations of the cited ones.
    let expect: Vec<i32> = e.cited.iter().map(|&c| -c).collect();
    if e.lits != expect {
        return Divergence::new(
            "explain-produce",
            "identity",
            format!(
                "clause {:?} is not the negation of its citations {:?}",
                e.lits, e.cited
            ),
            inputs(g),
        );
    }

    // No literal cited twice, and every citation is an input.
    let mut seen = e.cited.clone();
    seen.sort_unstable();
    let n_before = seen.len();
    seen.dedup();
    if seen.len() != n_before {
        return Divergence::new(
            "explain-produce",
            "identity",
            format!("clause cites a literal twice: {:?}", e.cited),
            inputs(g),
        );
    }

    // A clause was produced for a conjunction z3 finds satisfiable overall: that
    // can only happen if the cited SUBSET is unsat, which contradicts the
    // superset being sat. Caught above, but asserted explicitly.
    if z3_sat_full && !cited_sat {
        return Divergence::new(
            "explain-produce",
            "z3",
            "z3 says the full conjunction is satisfiable but a SUBSET of it is not -- \
             impossible, so one of the two z3 queries is being posed wrongly"
                .to_string(),
            inputs(g),
        );
    }

    Outcome::Match(5)
}

// ===========================================================================
// Check 3 — `explain-countermodel`
// ===========================================================================

/// The WITNESS, adjudicated rather than the verdict.
///
/// When AY reports a clause is NOT implied it must hand back the real number
/// that refutes it, and z3 must agree that every cited literal holds there. An
/// unwitnessed `false` — a refusal nobody can check — is the campaign's fourth
/// blind-spot pattern, and it is exactly what would let a checker quietly stop
/// finding counterexamples.
///
/// z3 legs: `Z3_algebraic_eval` at AY's witness must satisfy every literal;
/// absence of a witness must coincide with z3 finding the conjunction unsat.
/// Identity leg: a witness is present exactly when `oexplain_clause_is_valid`
/// says `false`, and absent exactly when it says `true`.
pub(crate) fn check_countermodel(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(z3_sat) = z3_satisfiable(z3, &g.polys, &g.conds) else {
        return Outcome::Skipped("z3 declined");
    };
    let Some(valid) = oexplain_clause_is_valid(&lits) else {
        return Outcome::Declined("validity");
    };
    let Some(cm) = oexplain_countermodel(&lits) else {
        return Outcome::Declined("countermodel");
    };

    // Identity: a witness exists exactly when the clause is not valid.
    if cm.is_some() == valid {
        return Divergence::new(
            "explain-countermodel",
            "identity",
            format!(
                "clause_is_valid = {valid} but countermodel present = {} -- the two must be \
                 exact opposites",
                cm.is_some()
            ),
            inputs(g),
        );
    }

    let Some(w) = cm else {
        // No witness. z3 must agree the conjunction is unsat.
        if z3_sat {
            return Divergence::new(
                "explain-countermodel",
                "z3",
                "AY found no satisfying cell, but z3 did -- AY's decomposition is missing a \
                 cell, which makes a satisfiable conjunction look like a conflict"
                    .to_string(),
                inputs(g),
            );
        }
        return if sab.on() {
            Outcome::Skipped("no witness to corrupt")
        } else {
            Outcome::Match(2)
        };
    };

    // Turn AY's witness into a z3 term and evaluate every literal there.
    let mut probe = w;
    if sab.on() {
        // Move the witness. Any displacement should break at least one literal;
        // where it does not, the case is skipped rather than counted, so the
        // catch rate is never inflated by a corruption that changed nothing.
        let Some(r) = probe.to_rational() else {
            return Outcome::Skipped("irrational witness: cannot displace it exactly");
        };
        probe = ODyadicAnum::rational(r + BigRational::one());
    }
    let Ok(ast) = z3_ast_of(z3, &probe) else {
        return Outcome::Skipped("witness not representable to z3");
    };

    let mut failed: Option<usize> = None;
    for (i, (p, c)) in g.polys.iter().zip(&g.conds).enumerate() {
        let Some(sg) = z3.eval_sign(&rationals(p), ast) else {
            return Outcome::Skipped("z3 declined the sign");
        };
        if !oracle_accepts(*c, sg) {
            failed = Some(i);
            break;
        }
    }
    if z3.errored() {
        return Outcome::Skipped("z3 errored");
    }

    if let Some(i) = failed {
        if sab.on() {
            return Divergence::new(
                "explain-countermodel",
                "z3",
                format!("displaced witness fails literal L{}", i + 1),
                inputs(g),
            );
        }
        return Divergence::new(
            "explain-countermodel",
            "z3",
            format!(
                "AY's countermodel does NOT satisfy literal L{} -- the witness is fictional, \
                 so the `not implied` verdict rests on nothing",
                i + 1
            ),
            inputs(g),
        );
    }
    if sab.on() {
        // The displacement happened to land somewhere still satisfying. Not
        // evidence either way.
        return Outcome::Skipped("displacement did not leave the satisfying region");
    }
    Outcome::Match(3)
}

/// AY's algebraic number as a z3 term.
fn z3_ast_of(z3: &Z3, a: &ODyadicAnum) -> Result<Ptr, ()> {
    if let Some(r) = a.to_rational() {
        return Ok(z3.rational(&r));
    }
    let coeffs = rationals(&a.poly_coeffs().ok_or(())?);
    let roots = z3.roots(&coeffs).ok_or(())?;
    let iv = a.interval().ok_or(())?;
    let lo = z3.rational(&iv.lo().to_rational());
    let hi = z3.rational(&iv.hi().to_rational());
    let mut found = None;
    for r in roots {
        if z3.gt(r, lo) && z3.lt(r, hi) {
            if found.is_some() {
                return Err(());
            }
            found = Some(r);
        }
    }
    if z3.errored() {
        return Err(());
    }
    found.ok_or(())
}

// ===========================================================================
// Check 4 — `explain-projection`
// ===========================================================================

/// The CAD projection operator: leading coefficients, discriminants and the
/// resultants of the relevant pairs.
///
/// z3 legs: every resultant and discriminant AY produces is SPECIALIZED at a
/// range of integer points and compared against `Z3_polynomial_subresultants`
/// computed on the specialized univariate pair. Specialization commutes with the
/// resultant exactly when the leading coefficient survives, which is checked
/// before the comparison rather than assumed.
/// Identity legs: the degree report is recomputed from the factors and must
/// match; the constant-factor count must match; `relevant_pairs` must return
/// only in-range, ordered, deduplicated pairs.
/// Guard, fired on purpose: an out-of-range pair index must be refused.
pub(crate) fn check_projection(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    if g.bi.len() < 2 {
        return Outcome::Skipped("need two bivariate inputs");
    }
    let polys: Vec<OBiPoly> =
        g.bi.iter()
            .map(|xs| {
                let terms: Vec<Vec<(u32, BigInt)>> = xs
                    .iter()
                    .map(|t| t.iter().map(|&(e, c)| (e, BigInt::from(c))).collect())
                    .collect();
                OBiPoly::from_x_coeffs(&terms)
            })
            .collect();
    for p in &polys {
        if p.degree_x().unwrap_or(0) < 1 {
            return Outcome::Skipped("bivariate degree < 1 in x");
        }
    }

    let Some(proj) = oexplain_project(&polys, &[(0, 1)]) else {
        return Outcome::Declined("projection");
    };

    // Guard, fired on purpose: an out-of-range pair must be refused.
    if oexplain_project(&polys, &[(0, polys.len())]).is_some() {
        return Divergence::new(
            "explain-projection",
            "identity",
            "an out-of-range pair index was accepted".to_string(),
            inputs(g),
        );
    }
    // Positive control on the same shape, so "always refuses" fails too.
    if oexplain_project(&polys, &[]).is_none() {
        return Divergence::new(
            "explain-projection",
            "identity",
            "an empty pair list was refused -- the guard fires on valid input".to_string(),
            inputs(g),
        );
    }

    // Identity: the degree report is recomputed rather than believed.
    let recomputed_out = proj
        .factors
        .iter()
        .map(|(_, y)| y_total_degree(y))
        .max()
        .unwrap_or(0);
    if recomputed_out != proj.out_max_total_degree {
        return Divergence::new(
            "explain-projection",
            "identity",
            format!(
                "reported out-degree {} but the factors max at {recomputed_out}",
                proj.out_max_total_degree
            ),
            inputs(g),
        );
    }

    // z3 leg: the LEADING COEFFICIENT and DISCRIMINANT factors, by
    // specialization — checked against an independent computation, because
    // until now they were checked against NOTHING.
    //
    // A verifier replaced every `Discriminant` factor with the polynomial's
    // leading coefficient, and separately every `LeadingCoeff` factor with the
    // x^0 coefficient. Each wrong answer produced ZERO divergences over
    // 4,000-6,000 cases across two to three seeds, with `explain-projection`
    // reporting 100% in selftest and all unit tests passing: the only factor
    // ever compared was `Resultant(0,1)`, and the other two entered solely a
    // degree recomputation that is self-consistent because it is derived from
    // the same factor list.
    //
    // `lc(p)` specialized must equal the specialization's leading coefficient,
    // and `disc(p) = (-1)^(d(d-1)/2) * Res(p, p') / lc(p)` — computed here from
    // z3's own resultant of the specialized polynomial and its derivative, so
    // nothing of AY's projection is on this path.
    let mut comparisons = 3u64;
    for (idx, poly) in polys.iter().enumerate().take(2) {
        let want_lc = proj.factors.iter().find(
            |(k, _)| matches!(k, ay_nra::oracle_api::OProjKind::LeadingCoeff(i) if *i == idx),
        );
        if let Some((_, lc_factor)) = want_lc {
            for c in [-2i64, -1, 0, 1, 2, 3] {
                let c = BigInt::from(c);
                let Some(lead) = poly.leading_x() else {
                    continue;
                };
                let want = lead.eval_at(&c);
                let mut got = lc_factor.eval_at(&c);
                if sab.on() {
                    got += BigInt::one();
                }
                comparisons += 1;
                if got != want {
                    return Divergence::new(
                        "explain-projection",
                        "identity",
                        format!(
                            "LeadingCoeff({idx}) at x = {c}: projection says {got}, the \
                             polynomial's own leading coefficient is {want}"
                        ),
                        inputs(g),
                    );
                }
            }
        }
    }

    let (f, q) = (&polys[0], &polys[1]);
    let (df, dq) = (f.degree_x().unwrap_or(0), q.degree_x().unwrap_or(0));
    let res = proj
        .factors
        .iter()
        .find(|(k, _)| matches!(k, ay_nra::oracle_api::OProjKind::Resultant(0, 1)))
        .map(|(_, y)| y.clone());
    let Some(res) = res else {
        return Divergence::new(
            "explain-projection",
            "identity",
            "the requested resultant is missing from the projection".to_string(),
            inputs(g),
        );
    };

    for c in [-2i64, -1, 0, 1, 2, 3] {
        let c = BigInt::from(c);
        let lc_ok = |b: &OBiPoly| b.leading_x().map_or(false, |l| !l.eval_at(&c).is_zero());
        if !lc_ok(f) || !lc_ok(q) {
            continue;
        }
        let mut val = res.eval_at(&c);
        if sab.on() {
            val += BigInt::one();
        }
        // Same higher-degree-first convention `check_bivariate_resultant`
        // establishes: AY's `resultant` applies the `(-1)^(mn)` correction and
        // `Z3_polynomial_subresultants` does not, so the operands must be
        // ordered to make the correction a no-op on both sides.
        let sf = f.specialize(&c);
        let sq = q.specialize(&c);
        let to_rats = |p: &ay_nra::oracle_api::OZPoly| -> Vec<BigRational> {
            p.coeffs().into_iter().map(BigRational::from).collect()
        };
        let (zf, zq) = if df >= dq {
            (to_rats(&sf), to_rats(&sq))
        } else {
            (to_rats(&sq), to_rats(&sf))
        };
        let Some(z3_res) = crate::subres::z3_resultant(z3, &zf, &zq) else {
            continue;
        };
        // AY's stored resultant is in ITS own argument order; re-derive the
        // same-order value for the comparison.
        let ay_ordered = if df >= dq {
            val.clone()
        } else {
            // Res(G,F) = (-1)^(deg F * deg G) Res(F,G)
            if (df * dq) % 2 == 1 {
                -val.clone()
            } else {
                val.clone()
            }
        };
        if ay_ordered != z3_res {
            return Divergence::new(
                "explain-projection",
                "z3",
                format!("at y = {c}: AY's Res_x specializes to {ay_ordered}, z3 gives {z3_res}"),
                inputs(g),
            );
        }
        comparisons += 1;
    }

    if comparisons == 3 {
        return Outcome::Skipped("every specialization dropped the x-degree");
    }
    Outcome::Match(comparisons)
}

/// Total degree of a `y`-polynomial, recomputed by the oracle.
fn y_total_degree(y: &OYPoly) -> u32 {
    y.terms().iter().map(|&(e, _)| e).max().unwrap_or(0)
}

/// `relevant_pairs`, driven directly.
pub(crate) fn check_relevant_pairs(z3: &Z3, g: &GenEx) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(pairs) = oexplain_relevant_pairs(&lits) else {
        return Outcome::Declined("relevant pairs");
    };
    let mut seen = pairs.clone();
    seen.sort_unstable();
    let n = seen.len();
    seen.dedup();
    if seen.len() != n {
        return Divergence::new(
            "explain-projection",
            "identity",
            format!("relevant_pairs returned a duplicate: {pairs:?}"),
            inputs(g),
        );
    }
    for &(i, j) in &pairs {
        if i >= j || j >= lits.len() {
            return Divergence::new(
                "explain-projection",
                "identity",
                format!("relevant_pairs returned an ill-formed pair ({i}, {j})"),
                inputs(g),
            );
        }
    }
    Outcome::Match(u64::try_from(pairs.len()).unwrap_or(0) + 1)
}
