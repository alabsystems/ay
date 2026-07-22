// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dedicated `is_int`-only existential eliminator for quantified LRA.
//!
//! Loos-Weispfenning ([`crate::qe::lw`]) refuses any body containing an
//! `is_int` atom (it is not in the pure `<= < = >= >` LRA fragment), so a
//! quantifier such as `∀x. is_int(x) ⇒ is_int(x + 1)` is kept and later
//! fail-closes to `unknown`. This module decides the sub-fragment where the
//! bound Real variable `x` occurs **only** inside atoms of the exact shape
//! `is_int(1·x + c)` with `c` a ground rational — the common integrality
//! pattern — and refuses everything else (fail-closed to the status quo).
//!
//! # The decision
//!
//! An atom `is_int(x + c)` is true exactly when `frac(x) = frac(-c)`, a single
//! point in `[0, 1)` we call the atom's *critical residue* `s`. Over all real
//! `x`, the truth of the whole (quantifier-free) matrix `φ` depends only on
//! **which** critical residue (if any) `frac(x)` equals, because every other
//! occurrence of `x` is forbidden. There are `n` distinct residues plus the
//! "matches none" case, so `φ` takes at most `n+1` truth values as `x` ranges
//! over the reals — each attainable by a concrete witness:
//!   * residue `s_j`: witness `x = s_j` (`frac(s_j) = s_j`), making exactly the
//!     atoms with residue `s_j` true;
//!   * none: any `x` whose fraction avoids every `s_j` (there are only finitely
//!     many to avoid in a continuum), making every atom false.
//!
//! Therefore `∃x. φ ≡ ⋁_{witness w} φ[atoms := their truth at w]`, a
//! quantifier-free formula. `∀` is handled by the caller's `¬∃¬` duality.
//!
//! # Soundness discipline (fail-closed)
//!
//! * **Structural fragment gate.** The eliminator refuses unless every `is_int`
//!   atom mentioning `x` normalizes to `1·x + ground` (coefficient exactly one,
//!   no other variable in the offset) AND `x` occurs nowhere else in the matrix
//!   (verified by masking those atoms and checking non-occurrence). Any
//!   `#[non_exhaustive]`/unrecognized node counts as an occurrence.
//! * **Exact rationals only** ([`num_rational::BigRational`]); residues are
//!   computed by exact floor.
//! * **Independent self-check.** The built result is verified against direct
//!   witness evaluation on a battery of ground assignments to the other free
//!   variables — the residue algebra (boolean substitution) is checked against
//!   an is_int-aware evaluator that computes `is_int` by actually testing
//!   integrality. Any disagreement, indefinite evaluation, or a
//!   random-`x`-satisfies-but-result-false witness refuses the elimination.
//! * Any refusal returns `None`; the caller keeps the original quantifier.

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::{HashMap, HashSet};

use super::lw::isint_unit_offset;

/// Cap on the number of *distinct* critical residues (result size is `n + 1`
/// substituted copies of the matrix).
const MAX_RESIDUES: usize = 8;
/// Cap on the total number of qualifying `is_int` atoms mentioning `x`.
const MAX_ISINT_ATOMS: usize = 32;
/// Ground assignments sampled by the self-check (over the OTHER free vars).
const SELF_CHECK_SAMPLES: usize = 96;
/// Random `x` probes per assignment for the `⇐` completeness guard.
const RANDOM_X_PROBES: usize = 8;

/// Eliminate `∃x. matrix` when `x` (Real-sorted) occurs only inside
/// `is_int(1·x + c)` atoms. Returns the quantifier-free equivalent (verified by
/// the self-check) or `None` (out of fragment / unverified — fail-closed).
pub(crate) fn eliminate_exists_isint(
    terms: &mut TermStore,
    matrix: TermId,
    var: TermId,
) -> Option<TermId> {
    if !matches!(terms.get(var), TermData::Var(_, _)) || terms.sort(var) != &Sort::Real {
        return None;
    }

    // 0. Fail-closed shadow gate. A user `(declare-fun is_int (Real) Bool)`
    //    builds `App(Named("is_int"), [arg])` — byte-identical to the builtin
    //    this eliminator matches structurally. `is_int` is deliberately
    //    user-declarable (a `(_ map f)` target; see the frontend's
    //    EXCLUDED_DECLARABLE_OP_NAMES "map-target" row), so applying integrality
    //    (critical-residue) reasoning to it would fabricate semantics for a free
    //    predicate. That is a wrong-UNSAT class: `(forall ((x Real)) (is_int x))`
    //    over the shadowed UF decided `unsat` where z3 exhibits the model
    //    `is_int ≡ λx.true`. When the store records that a user declaration has
    //    shadowed `is_int`, stand down entirely (fail-closed to the status quo:
    //    LW keeps the quantifier → `unknown`). (#isint-shadow)
    if terms.is_int_is_shadowed() {
        return None;
    }

    // 1. All is_int atoms whose argument mentions `x`.
    let isint_atoms = collect_isint_atoms_mentioning(terms, matrix, var);
    if isint_atoms.is_empty() || isint_atoms.len() > MAX_ISINT_ATOMS {
        return None; // Not our fragment (or too large) — let LW refuse it.
    }

    // 2. Each must normalize to `1·x + c` with `c` ground. Refuse otherwise
    //    (e.g. `is_int(2x)`, `is_int(x + y)`).
    let mut offsets: Vec<BigRational> = Vec::with_capacity(isint_atoms.len());
    for &atom in &isint_atoms {
        let arg = match terms.get(atom).clone() {
            TermData::App(_, args) if args.len() == 1 => args[0],
            _ => return None,
        };
        offsets.push(isint_unit_offset(terms, arg, var)?);
    }

    // 3. Structural (I1): `x` must occur ONLY inside these atoms. Mask them with
    //    `true` and require the bound variable to have vanished.
    let true_t = terms.mk_bool(true);
    let masks = vec![true_t; isint_atoms.len()];
    let masked = terms.substitute(matrix, &isint_atoms, &masks);
    if occurs(terms, masked, var) {
        return None;
    }

    // 4. Critical residue s_k = frac(-c_k) ∈ [0,1) for each atom.
    let residues: Vec<BigRational> = offsets.iter().map(frac_neg).collect();
    let mut distinct: Vec<BigRational> = Vec::new();
    for r in &residues {
        if !distinct.iter().any(|d| d == r) {
            distinct.push(r.clone());
        }
    }
    if distinct.len() > MAX_RESIDUES {
        return None;
    }

    // 5. Witnesses: one `x = s_j` per distinct residue + one all-false witness.
    let mut witnesses: Vec<BigRational> = distinct.clone();
    witnesses.push(pick_none_witness(&distinct)?);

    // 6. result = ⋁_w φ[atoms := (residue == frac(w))].
    let mut disjuncts: Vec<TermId> = Vec::with_capacity(witnesses.len());
    for w in &witnesses {
        let fw = frac(w);
        let bool_vals: Vec<TermId> = residues
            .iter()
            .map(|r| {
                let v = *r == fw;
                terms.mk_bool(v)
            })
            .collect();
        disjuncts.push(terms.substitute(matrix, &isint_atoms, &bool_vals));
    }
    let result = terms.mk_or(disjuncts);

    // 7. Independent, fail-closed self-check.
    if !self_check(terms, matrix, var, result, &witnesses) {
        return None;
    }
    Some(result)
}

/// Fractional part `r - floor(r)` in `[0, 1)`.
fn frac(r: &BigRational) -> BigRational {
    r - r.floor()
}

/// Critical residue of an atom `is_int(x + c)`: `frac(-c)`.
fn frac_neg(c: &BigRational) -> BigRational {
    frac(&(-c.clone()))
}

/// A fraction in `[0, 1)` avoiding every value in `forbidden` — the residue of
/// the "matches no atom" witness. Searched over a bounded Farey-like list;
/// `None` (fail-closed) if none is found (cannot happen for `≤ MAX_RESIDUES`
/// forbidden values within this range, but never assume it).
fn pick_none_witness(forbidden: &[BigRational]) -> Option<BigRational> {
    // 0 first, then k/d for small d — far more candidates than MAX_RESIDUES.
    let zero = BigRational::zero();
    if !forbidden.iter().any(|f| *f == zero) {
        return Some(zero);
    }
    for d in 2i64..=20 {
        for k in 1i64..d {
            let cand = BigRational::new(k.into(), d.into());
            if !forbidden.iter().any(|f| *f == cand) {
                return Some(cand);
            }
        }
    }
    None
}

/// All `is_int(arg)` atoms in `term` whose `arg` mentions `var`, deduplicated
/// by node identity, in deterministic discovery order.
fn collect_isint_atoms_mentioning(terms: &TermStore, term: TermId, var: TermId) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(t).clone() {
            if name == "is_int" && args.len() == 1 && occurs(terms, args[0], var) {
                out.push(t);
            }
        }
        match terms.get(t).clone() {
            TermData::Not(inner) => stack.push(inner),
            TermData::App(_, args) => stack.extend(args),
            TermData::Ite(c, a, b) => {
                stack.push(c);
                stack.push(a);
                stack.push(b);
            }
            _ => {}
        }
    }
    // Stable order independent of hashing: by discovery is fine (stack order is
    // deterministic given the DAG); sort by TermId for extra determinism.
    out.sort_unstable();
    out.dedup();
    out
}

/// Whether `var` occurs in `term`. Fail-closed: any untraversable
/// (`#[non_exhaustive]`) node counts as an occurrence.
fn occurs(terms: &TermStore, term: TermId, var: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if t == var {
            return true;
        }
        match terms.get(t) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            _ => return true,
        }
    }
    false
}

// ===========================================================================
// Independent, fail-closed self-check
// ===========================================================================

#[derive(Clone)]
enum EvalVal {
    Rat(BigRational),
    Bool(bool),
}

/// Verify `result ≡ ∃x. matrix` on a battery of ground assignments to the
/// non-`x` free variables. For each assignment `σ`:
///   * `result[σ]` must evaluate to a definite boolean;
///   * `⋁_w matrix[σ, x := w]` (direct is_int-aware evaluation at each witness)
///     must equal it;
///   * for several random `x`, `matrix[σ, x := rx]` true must imply
///     `result[σ]` true (the `⇐`/completeness guard against a missed
///     occurrence of `x`).
/// Any indefinite evaluation or disagreement refuses (returns `false`).
fn self_check(
    terms: &TermStore,
    matrix: TermId,
    var: TermId,
    result: TermId,
    witnesses: &[BigRational],
) -> bool {
    // Collect the other free variables (must be Int/Real-sorted; anything else
    // means the evaluator cannot decide the matrix → refuse conservatively).
    let mut free_vars: Vec<(TermId, bool)> = Vec::new(); // (var, is_int_sorted)
    let mut seen: HashSet<TermId> = HashSet::new();
    if !collect_free_arith_vars(terms, matrix, var, &mut free_vars, &mut seen)
        || !collect_free_arith_vars(terms, result, var, &mut free_vars, &mut seen)
    {
        return false;
    }

    // Value pool for sampling; Int-sorted vars are restricted to integers.
    let real_pool: Vec<BigRational> = value_pool();

    let mut rng: u64 = 0x9E3779B97F4A7C15;
    for sample in 0..SELF_CHECK_SAMPLES {
        let mut assign: HashMap<TermId, BigRational> = HashMap::new();
        for (v, is_int_sort) in &free_vars {
            let val = if sample == 0 {
                BigRational::zero()
            } else {
                let idx = (next_rand(&mut rng) as usize) % real_pool.len();
                let mut val = real_pool[idx].clone();
                if *is_int_sort {
                    val = val.floor();
                }
                val
            };
            assign.insert(*v, val);
        }

        // 1. result[σ] must be a definite boolean.
        let lhs = match eval(terms, result, &assign) {
            Some(EvalVal::Bool(b)) => b,
            _ => return false,
        };

        // 2. OR over witnesses of matrix[σ, x := w].
        let mut rhs = false;
        for w in witnesses {
            assign.insert(var, w.clone());
            match eval(terms, matrix, &assign) {
                Some(EvalVal::Bool(b)) => rhs |= b,
                _ => {
                    assign.remove(&var);
                    return false;
                }
            }
        }
        assign.remove(&var);
        if lhs != rhs {
            return false;
        }

        // 3. Completeness guard: random x satisfying the matrix ⇒ result true.
        for _ in 0..RANDOM_X_PROBES {
            let idx = (next_rand(&mut rng) as usize) % real_pool.len();
            assign.insert(var, real_pool[idx].clone());
            let sat = match eval(terms, matrix, &assign) {
                Some(EvalVal::Bool(b)) => b,
                _ => {
                    assign.remove(&var);
                    return false;
                }
            };
            assign.remove(&var);
            if sat && !lhs {
                return false;
            }
        }
    }
    true
}

/// Collect free `Var` nodes of `term` other than `var`. Returns `false`
/// (caller refuses) if any free variable is not Int/Real-sorted — the
/// evaluator only models arithmetic.
fn collect_free_arith_vars(
    terms: &TermStore,
    term: TermId,
    var: TermId,
    out: &mut Vec<(TermId, bool)>,
    seen: &mut HashSet<TermId>,
) -> bool {
    let mut stack = vec![term];
    let mut visited: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        match terms.get(t).clone() {
            TermData::Var(_, _) => {
                if t != var && seen.insert(t) {
                    match terms.sort(t) {
                        Sort::Int => out.push((t, true)),
                        Sort::Real => out.push((t, false)),
                        _ => return false,
                    }
                }
            }
            TermData::Const(_) => {}
            TermData::Not(inner) => stack.push(inner),
            TermData::App(_, args) => stack.extend(args),
            TermData::Ite(c, a, b) => {
                stack.push(c);
                stack.push(a);
                stack.push(b);
            }
            _ => return false,
        }
    }
    true
}

/// Deterministic sampling pool of rationals.
fn value_pool() -> Vec<BigRational> {
    let mut v = Vec::new();
    for n in -3i64..=3 {
        v.push(BigRational::from_integer(n.into()));
    }
    for (a, b) in [
        (1, 2),
        (-1, 2),
        (1, 3),
        (2, 3),
        (-1, 3),
        (3, 2),
        (-3, 2),
        (5, 4),
        (1, 6),
    ] {
        v.push(BigRational::new(a.into(), b.into()));
    }
    v
}

/// SplitMix64-style step for deterministic pseudo-random sampling.
fn next_rand(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E3779B97F4A7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

/// Exact, is_int-aware ground evaluator. Returns `None` (fail-closed at the
/// caller) on any unassigned variable or unrecognized node.
fn eval(terms: &TermStore, term: TermId, assign: &HashMap<TermId, BigRational>) -> Option<EvalVal> {
    match terms.get(term).clone() {
        TermData::Const(Constant::Int(n)) => Some(EvalVal::Rat(BigRational::from_integer(n))),
        TermData::Const(Constant::Rational(r)) => Some(EvalVal::Rat(r.0)),
        TermData::Const(Constant::Bool(b)) => Some(EvalVal::Bool(b)),
        TermData::Var(_, _) => assign.get(&term).cloned().map(EvalVal::Rat),
        TermData::Not(inner) => match eval(terms, inner, assign)? {
            EvalVal::Bool(b) => Some(EvalVal::Bool(!b)),
            EvalVal::Rat(_) => None,
        },
        TermData::Ite(c, a, b) => match eval(terms, c, assign)? {
            EvalVal::Bool(true) => eval(terms, a, assign),
            EvalVal::Bool(false) => eval(terms, b, assign),
            EvalVal::Rat(_) => None,
        },
        TermData::App(Symbol::Named(name), args) => {
            let rats = |args: &[TermId]| -> Option<Vec<BigRational>> {
                args.iter()
                    .map(|&a| match eval(terms, a, assign) {
                        Some(EvalVal::Rat(r)) => Some(r),
                        _ => None,
                    })
                    .collect()
            };
            let bools = |args: &[TermId]| -> Option<Vec<bool>> {
                args.iter()
                    .map(|&a| match eval(terms, a, assign) {
                        Some(EvalVal::Bool(b)) => Some(b),
                        _ => None,
                    })
                    .collect()
            };
            match name.as_str() {
                "+" => Some(EvalVal::Rat(
                    rats(&args)?
                        .into_iter()
                        .fold(BigRational::zero(), |a, b| a + b),
                )),
                "*" => Some(EvalVal::Rat(
                    rats(&args)?
                        .into_iter()
                        .fold(BigRational::one(), |a, b| a * b),
                )),
                "-" => {
                    let vs = rats(&args)?;
                    match vs.len() {
                        1 => Some(EvalVal::Rat(-vs[0].clone())),
                        n if n >= 2 => {
                            let mut acc = vs[0].clone();
                            for v in &vs[1..] {
                                acc -= v;
                            }
                            Some(EvalVal::Rat(acc))
                        }
                        _ => None,
                    }
                }
                "/" => {
                    let vs = rats(&args)?;
                    if vs.len() != 2 || vs[1].is_zero() {
                        return None;
                    }
                    Some(EvalVal::Rat(&vs[0] / &vs[1]))
                }
                "is_int" if args.len() == 1 => match eval(terms, args[0], assign)? {
                    EvalVal::Rat(r) => Some(EvalVal::Bool(r.is_integer())),
                    EvalVal::Bool(_) => None,
                },
                "=" => {
                    if let Some(vs) = rats(&args) {
                        if vs.len() == 2 {
                            return Some(EvalVal::Bool(vs[0] == vs[1]));
                        }
                        return None;
                    }
                    let vs = bools(&args)?;
                    if vs.len() == 2 {
                        Some(EvalVal::Bool(vs[0] == vs[1]))
                    } else {
                        None
                    }
                }
                "distinct" => {
                    let vs = rats(&args)?;
                    for i in 0..vs.len() {
                        for j in (i + 1)..vs.len() {
                            if vs[i] == vs[j] {
                                return Some(EvalVal::Bool(false));
                            }
                        }
                    }
                    Some(EvalVal::Bool(true))
                }
                "<" | "<=" | ">" | ">=" => {
                    let vs = rats(&args)?;
                    if vs.len() != 2 {
                        return None;
                    }
                    let b = match name.as_str() {
                        "<" => vs[0] < vs[1],
                        "<=" => vs[0] <= vs[1],
                        ">" => vs[0] > vs[1],
                        _ => vs[0] >= vs[1],
                    };
                    Some(EvalVal::Bool(b))
                }
                "and" => Some(EvalVal::Bool(bools(&args)?.into_iter().all(|b| b))),
                "or" => Some(EvalVal::Bool(bools(&args)?.into_iter().any(|b| b))),
                "not" if args.len() == 1 => match eval(terms, args[0], assign)? {
                    EvalVal::Bool(b) => Some(EvalVal::Bool(!b)),
                    EvalVal::Rat(_) => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
#[path = "isint_tests.rs"]
mod tests;
