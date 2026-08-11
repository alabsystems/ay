// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded differential check for Cooper quantifier elimination candidates.
//!
//! Every successful `eliminate_exists` candidate is exercised here before it
//! is handed back; any observed disagreement discards the candidate. This is a
//! useful deterministic bug detector, but it is deliberately **not** verdict
//! authority: the free-variable battery is finite and therefore cannot prove a
//! universally quantified equivalence. A public decision path must keep the
//! exact quantified source or obtain a separate symbolic proof that covers all
//! free-variable valuations.
//!
//! # What we check
//!
//! We verify `O ≡ ∃x.φ` over the free variables on a battery of ground
//! assignments. For each assignment `σ`:
//!
//! 1. **O is concrete.** `O[σ]` must evaluate to a definite boolean with the
//!    independent ground evaluator ([`super::eval`]). If it is `Unknown` (an
//!    unmodeled term shape) the check fails.
//! 2. **Decide `∃x.φ[σ]` independently.** With the free variables ground, the
//!    matrix `φ[σ]` is a one-variable LIA conjunction. We decide its
//!    satisfiability by an exhaustive bounded search over `x` whose bound is
//!    derived to be *complete*: a satisfiable one-variable LIA conjunction has
//!    a witness within `[-W, W]` where `W` covers every constant magnitude plus
//!    the divisibility period. (See [`search_bound`].)
//! 3. **Agree.** `O[σ]` must equal `(∃x.φ[σ])`. Any disagreement fails the
//!    check.
//!
//! Both directions are checked for each sampled assignment. The bounded
//! x-search is complete for the resulting one-variable formula **after** a
//! particular free-variable assignment `σ` is fixed; the finite battery does
//! not establish the outer `forall σ` obligation.
//!
//! The battery mixes deterministic boundary points (all-zero, ±1, ±small) with
//! seeded pseudo-random assignments, so the check is reproducible.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::collections::{HashMap, HashSet};

use super::eval::{eval, EvalResult};

/// Number of pseudo-random ground assignments to sample, in addition to the
/// deterministic boundary battery.
const RANDOM_SAMPLES: usize = 200;

/// Range from which random free-variable values are drawn: `[-RV, RV]`.
const RV: i64 = 12;

/// Hard cap on the divisibility period δ (lcm of all input divisors) the
/// bounded `∃x` search will fold into its window. Beyond this the check
/// refuses outright (fail-closed → the elimination is discarded) rather than
/// pay an arbitrarily large exhaustive search.
const DIVISOR_PERIOD_CAP: i64 = 4096;

/// Hard cap on the exhaustive `x` search window `[-W, W]` (#clusterD
/// divergence). The complete small-model bound `W` grows with `Σ|consts|`, so
/// machine-integer type-range guards (|c| ~ 2³¹/2³²) push it to ~10¹⁰ and the
/// bounded search — ~200 battery assignments × (2W+1) candidate values —
/// becomes an effectively-nonterminating 100%-CPU loop inside `check_sat`
/// (reached via the deep-QE pre-pass). Refusing over-cap windows is
/// fail-closed, exactly like [`DIVISOR_PERIOD_CAP`]: the elimination is
/// discarded and the caller keeps the ORIGINAL quantified formula for the
/// downstream quantifier machinery (E-matching/CEGQI/MBQI), which decides the
/// type-range-guarded witness shapes directly. Never skip the self-check
/// instead — that would ship unverified eliminations.
const SEARCH_WINDOW_CAP: i64 = 1 << 16;

/// Verify `result ≡ ∃x.φ` on a battery of ground assignments to the free
/// variables. Returns `true` only if every case agrees and every `O[σ]`
/// evaluated to a definite boolean. Any inconclusive case returns `false`
/// for this bounded candidate check. Passing is not a proof of equivalence over
/// every free-variable valuation.
pub(super) fn equivalence_self_check(
    terms: &TermStore,
    literals: &[TermId],
    var: TermId,
    result: TermId,
) -> bool {
    // Collect the free variables (all integer variables in φ except `x`),
    // plus all constants (to size the search bound and the value battery).
    let mut free_vars: Vec<TermId> = Vec::new();
    let mut free_seen: HashSet<TermId> = HashSet::new();
    let mut consts: Vec<BigInt> = Vec::new();
    for &lit in literals {
        collect_vars_and_consts(terms, lit, var, &mut free_vars, &mut free_seen, &mut consts);
    }
    // Also fold in constants that only appear in the result O (e.g. period
    // offsets) so the search window is wide enough.
    collect_vars_and_consts(
        terms,
        result,
        var,
        &mut free_vars,
        &mut free_seen,
        &mut consts,
    );

    // A complete search bound for the one-variable problem φ[σ]. The window
    // must contain a full divisibility period, so the lcm of every INPUT
    // divisor (negated or not) is folded in; an over-cap period refuses the
    // whole check (fail-closed).
    let Some(bound) = search_bound(&consts, &input_divisor_lcm(terms, literals)) else {
        return false;
    };

    // Build the value battery for the free variables.
    let mut rng = SplitMix64::new(0x5DEE_CE66_D3A1_F00D);
    let assignments = build_assignments(&free_vars, RANDOM_SAMPLES, &mut rng);

    for assign in &assignments {
        // 1. Evaluate O[σ] — must be a definite boolean.
        let o_val = match eval(terms, result, assign) {
            EvalResult::Bool(b) => b,
            _ => return false, // Unknown / non-boolean O — fail closed.
        };

        // 2. Decide ∃x.φ[σ] by complete bounded search.
        let exists_val = match exists_x_holds(terms, literals, var, assign, &bound) {
            Some(b) => b,
            None => return false, // φ evaluation hit an unmodeled shape — fail.
        };

        // 3. They must agree.
        if o_val != exists_val {
            return false;
        }
    }

    true
}

/// Decide `∃x. (⋀ literals)[σ]` by exhaustive search of `x ∈ [-bound, bound]`.
///
/// Returns `Some(true)`/`Some(false)` for the decision, or `None` if evaluating
/// the matrix produced an [`EvalResult::Unknown`] for some `x` (an unmodeled
/// term shape), which the caller treats as a check failure.
fn exists_x_holds(
    terms: &TermStore,
    literals: &[TermId],
    var: TermId,
    base_assign: &HashMap<TermId, BigInt>,
    bound: &BigInt,
) -> Option<bool> {
    let mut assign = base_assign.clone();
    let mut x = -bound.clone();
    let mut saw_unknown = false;
    while x <= *bound {
        assign.insert(var, x.clone());
        let mut all_true = true;
        let mut hit_unknown = false;
        for &lit in literals {
            match eval(terms, lit, &assign) {
                EvalResult::Bool(true) => {}
                EvalResult::Bool(false) => {
                    all_true = false;
                    break;
                }
                _ => {
                    hit_unknown = true;
                    break;
                }
            }
        }
        if hit_unknown {
            saw_unknown = true;
        } else if all_true {
            return Some(true);
        }
        x += 1;
    }
    if saw_unknown {
        // Some x made the matrix unevaluable: we cannot soundly claim UNSAT.
        return None;
    }
    Some(false)
}

/// A search bound `W` that is complete for one-variable LIA conjunctions whose
/// constant magnitudes (after grounding the free variables) are all bounded by
/// `max_c`.
///
/// We use a deliberately generous window: `W = 2·(Σ|consts|) + 2·RV·(#vars
/// folded already into consts) + 64`. In practice, after grounding the free
/// variables, every coefficient/constant of the residual one-variable problem
/// is bounded by these magnitudes; the classic small-model bound for Cooper is
/// `M + δ` where `M` is the largest constant term and `δ` the period. We
/// multiply up and add a large slack so the window strictly contains the
/// theoretical bound even after the free-variable substitution shifts the
/// constants by up to `RV` each.
///
/// The period δ needs care: with several coprime divisors, `δ = lcm` can
/// dwarf `Σ|consts|` (divisors 3,5,7,11,13 → δ = 15015 vs Σ = 39), and when
/// the Cooper OUTPUT constant-folds (contributing no constants of its own)
/// the window would not contain a full period — leaving the bounded search
/// incomplete exactly in the double-failure scenario where the output is
/// also wrong. So: when `divisor_lcm ≤ Σ|consts|` the 3Σ+slack window
/// already contains a full period past every threshold; otherwise the lcm is
/// folded in explicitly, and if it also exceeds [`DIVISOR_PERIOD_CAP`] the
/// check refuses outright (`None`, fail-closed).
///
/// Finally, the window itself is capped: a `W` beyond [`SEARCH_WINDOW_CAP`]
/// (huge input constants, e.g. i32/i64 type-range guards) would make the
/// exhaustive search effectively nonterminating, so the check refuses
/// (`None`, fail-closed) rather than diverge.
fn search_bound(consts: &[BigInt], divisor_lcm: &BigInt) -> Option<BigInt> {
    let mut sum = BigInt::zero();
    for c in consts {
        sum += c.abs();
    }
    // Generous slack accommodating the up-to-RV magnitude of substituted free
    // variables and any coefficient interaction.
    let slack = BigInt::from(2) * &sum + BigInt::from(RV) * BigInt::from(64) + BigInt::from(256);
    let mut w = sum.clone() + slack;
    if *divisor_lcm > sum {
        if *divisor_lcm > BigInt::from(DIVISOR_PERIOD_CAP) {
            return None;
        }
        w += divisor_lcm;
    }
    // Deterministic termination bound: never attempt a window the exhaustive
    // search cannot complete in reasonable time (fail-closed refusal).
    if w > BigInt::from(SEARCH_WINDOW_CAP) {
        return None;
    }
    Some(w)
}

/// The lcm of every constant `mod` divisor appearing in the INPUT literals
/// (positive and negated divisibility alike) — the divisibility period δ of
/// the grounded one-variable problem. Divisors are read from the literal
/// TERMS (pre-normalization), matching what [`exists_x_holds`] evaluates.
fn input_divisor_lcm(terms: &TermStore, literals: &[TermId]) -> BigInt {
    let mut lcm = BigInt::one();
    let mut stack: Vec<TermId> = literals.to_vec();
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::App(Symbol::Named(name), args) => {
                if name == "mod" && args.len() == 2 {
                    if let TermData::Const(Constant::Int(d)) = terms.get(args[1]) {
                        if !d.is_zero() {
                            lcm = lcm.lcm(&d.abs());
                        }
                    }
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    lcm
}

/// Collect (a) the free integer variables (≠ `var`) and (b) every integer
/// constant appearing in `term`.
fn collect_vars_and_consts(
    terms: &TermStore,
    term: TermId,
    var: TermId,
    free_vars: &mut Vec<TermId>,
    free_seen: &mut HashSet<TermId>,
    consts: &mut Vec<BigInt>,
) {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => consts.push(n.clone()),
        TermData::Const(_) => {}
        TermData::Var(_, _) if term != var && free_seen.insert(term) => {
            free_vars.push(term);
        }
        TermData::Var(_, _) => {}
        TermData::Not(inner) => {
            collect_vars_and_consts(terms, *inner, var, free_vars, free_seen, consts);
        }
        TermData::Ite(c, t, e) => {
            collect_vars_and_consts(terms, *c, var, free_vars, free_seen, consts);
            collect_vars_and_consts(terms, *t, var, free_vars, free_seen, consts);
            collect_vars_and_consts(terms, *e, var, free_vars, free_seen, consts);
        }
        TermData::App(Symbol::Named(_), args) => {
            for &a in args {
                collect_vars_and_consts(terms, a, var, free_vars, free_seen, consts);
            }
        }
        _ => {}
    }
}

/// Build the assignment battery: deterministic boundary points crossed across
/// the free variables, plus `random_count` seeded random assignments.
fn build_assignments(
    free_vars: &[TermId],
    random_count: usize,
    rng: &mut SplitMix64,
) -> Vec<HashMap<TermId, BigInt>> {
    let mut out: Vec<HashMap<TermId, BigInt>> = Vec::new();

    // Deterministic boundary values applied uniformly to all free vars.
    let boundary: [i64; 7] = [0, 1, -1, 2, -2, 3, -3];
    for &v in &boundary {
        let mut m = HashMap::new();
        for &fv in free_vars {
            m.insert(fv, BigInt::from(v));
        }
        out.push(m);
    }

    // A few mixed deterministic points (alternating signs across vars).
    for base in &[1i64, 2, 5] {
        let mut m = HashMap::new();
        for (i, &fv) in free_vars.iter().enumerate() {
            let sign = if i % 2 == 0 { 1 } else { -1 };
            m.insert(fv, BigInt::from(sign * base * (i as i64 + 1)));
        }
        out.push(m);
    }

    // Seeded random assignments.
    for _ in 0..random_count {
        let mut m = HashMap::new();
        for &fv in free_vars {
            let r = (rng.next_u64() % (2 * RV as u64 + 1)) as i64 - RV;
            m.insert(fv, BigInt::from(r));
        }
        out.push(m);
    }

    out
}

/// A tiny deterministic SplitMix64 PRNG so the battery is reproducible without
/// pulling extra randomness sources into the check.
struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}
