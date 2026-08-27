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
    oexplain_relevant_pairs, oexplain_univariate, OBiPoly, ODyadicAnum, OExplainLit, OExplanation,
    OISignCond, OProjKind, OProjection, OYPoly,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::anum::{dyadic_iv, rationals};
use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ast, Z3};

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

include!("explain/generator.rs");
include!("explain/implication.rs");
include!("explain/producer.rs");
include!("explain/projection.rs");
