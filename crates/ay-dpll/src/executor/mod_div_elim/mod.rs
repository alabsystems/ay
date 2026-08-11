// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocess `(mod t k)` / `(div t k)` where `k` is an Int constant.
//!
//! This module implements the standard "quotient + remainder" reduction used in
//! `ay-chc` (see `ChcExpr::eliminate_mod()`), but at the `TermId` level for the
//! main SMT executor.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::Signed;

/// Red zone size for `stacker::maybe_grow` in mod/div elimination recursion (#8414).
const MOD_DIV_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for mod/div elimination recursion.
const MOD_DIV_STACK_SIZE: usize = 1024 * 1024;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

/// Which integer division-family operator a deterministic zero-divisor var
/// belongs to. `div`/`mod`/`rem` are INDEPENDENT functions on a zero divisor
/// (Z3 #9140: `(rem a 0)`, `(mod a 0)`, `(div a 0)` may all differ), so their
/// zero-divisor vars must never be congruence-merged across operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DivModOp {
    Div,
    Mod,
    Rem,
}

/// Extract integer constant from a term, if it is one.
fn extract_int_constant(terms: &TermStore, term: TermId) -> Option<BigInt> {
    if let TermData::Const(Constant::Int(n)) = terms.get(term) {
        Some(n.clone())
    } else {
        None
    }
}

/// If `term` is `(r + c)`, `(c + r)`, or `(r - c)` for a remainder var `r` in
/// `rem` (coefficient +1) and an integer constant `c`, return `(r, offset)` such
/// that `term = r + offset`. Only the coefficient-+1 shapes are matched, so the
/// caller can move the offset across a comparison WITHOUT flipping its sense.
fn match_remainder_affine(
    terms: &TermStore,
    term: TermId,
    rem: &HashSet<TermId>,
) -> Option<(TermId, BigInt)> {
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    match sym.name() {
        "+" => {
            if rem.contains(&args[0]) {
                if let Some(c) = extract_int_constant(terms, args[1]) {
                    return Some((args[0], c));
                }
            }
            if rem.contains(&args[1]) {
                if let Some(c) = extract_int_constant(terms, args[0]) {
                    return Some((args[1], c));
                }
            }
            None
        }
        "-" => {
            // r - c  =  r + (-c)   (only this orientation keeps r at coeff +1)
            if rem.contains(&args[0]) {
                if let Some(c) = extract_int_constant(terms, args[1]) {
                    return Some((args[0], -c));
                }
            }
            None
        }
        _ => None,
    }
}

/// Sound equisatisfiability normalization: rewrite an EQUALITY-family atom
/// `(= (r ± c) k)` / `(distinct (r ± c) k)` (either operand order) whose
/// remainder-affine side isolates to `(= r (k ∓ c))`. The constant-divisor
/// div-def-pinned remainder var `r` propagates its determined value into a BARE
/// atom (`r != k`) but NOT into a linear combination (`(r - c) != k`), leaving a
/// determined disequality wrongly `unknown` (the cast `((x+2^31) mod 2^32) - 2^31
/// != x` regression). Isolating `r` to bare form restores the propagation. Only
/// `=`/`distinct` (order-symmetric, no inequality sense) and coefficient-+1
/// affine sides are touched, so no comparison flips — the rewrite is a pure
/// algebraic identity and cannot change satisfiability.
fn isolate_remainder_eq_atom(
    terms: &mut TermStore,
    formula: TermId,
    rem: &HashSet<TermId>,
) -> TermId {
    enum Shape {
        Neg(TermId),
        EqLike {
            distinct: bool,
            a: TermId,
            b: TermId,
        },
        Other,
    }
    let shape = match terms.get(formula) {
        TermData::Not(inner) => Shape::Neg(*inner),
        TermData::App(sym, args) if args.len() == 2 && matches!(sym.name(), "=" | "distinct") => {
            Shape::EqLike {
                distinct: sym.name() == "distinct",
                a: args[0],
                b: args[1],
            }
        }
        _ => Shape::Other,
    };
    match shape {
        Shape::Neg(inner) => {
            let ni = isolate_remainder_eq_atom(terms, inner, rem);
            if ni != inner {
                terms.mk_not(ni)
            } else {
                formula
            }
        }
        Shape::EqLike { distinct, a, b } => {
            // term = r + offset on one side, constant k on the other.
            // (r + offset) OP k  <=>  r OP (k - offset).
            let hit = match_remainder_affine(terms, a, rem)
                .and_then(|(r, off)| extract_int_constant(terms, b).map(|k| (r, off, k)))
                .or_else(|| {
                    match_remainder_affine(terms, b, rem)
                        .and_then(|(r, off)| extract_int_constant(terms, a).map(|k| (r, off, k)))
                });
            let Some((r, offset, k)) = hit else {
                return formula;
            };
            let new_k = terms.mk_int(k - offset);
            if distinct {
                terms.mk_distinct(vec![r, new_k])
            } else {
                terms.mk_eq(r, new_k)
            }
        }
        Shape::Other => formula,
    }
}

pub(super) struct ModDivElimResult {
    pub constraints: Vec<TermId>,
    pub rewritten: Vec<TermId>,
    /// True if elimination introduced at least one UNCONSTRAINED fresh variable
    /// for a div/mod whose divisor is zero (literal) or not provably non-zero
    /// (symbolic). SMT-LIB leaves `(div a 0)`/`(mod a 0)` under-specified, so we
    /// model them as free vars (#div0). The standard model evaluator cannot
    /// replay the original `(div a 0)` term (it returns Unknown on a zero
    /// divisor), so callers that solve to SAT must route through the
    /// `sat_validated_by_mod_div_or_branch` validation bypass — satisfiability
    /// follows soundly from the rewritten constraints + boolean skeleton +
    /// strict definitive-false gate.
    pub introduced_unconstrained_div_mod: bool,
}

pub(super) fn eliminate_int_mod_div_by_constant(
    terms: &mut TermStore,
    formulas: &[TermId],
) -> ModDivElimResult {
    eliminate_int_mod_div_impl(terms, formulas, false)
}

pub(super) fn eliminate_int_mod_div(
    terms: &mut TermStore,
    formulas: &[TermId],
) -> ModDivElimResult {
    eliminate_int_mod_div_impl(terms, formulas, true)
}

fn eliminate_int_mod_div_impl(
    terms: &mut TermStore,
    formulas: &[TermId],
    symbolic_divisors: bool,
) -> ModDivElimResult {
    let mut state = ModDivElimState {
        constraints: Vec::new(),
        memo: HashMap::default(),
        const_divmod_qr: HashMap::default(),
        sym_divmod_qr: HashMap::default(),
        symbolic_divisors,
        introduced_unconstrained_div_mod: false,
        created_zero_divisor: false,
        symbolic_terms: Vec::new(),
    };
    let rewritten: Vec<TermId> = formulas
        .iter()
        .map(|&term| state.rewrite_term(terms, term))
        .collect();

    // Zero-divisor congruence: `(op a 0)` is a single consistent function of the
    // dividend's value, so equal dividends force equal results. Without this,
    // `(mod -2 0)` and `(mod y 0)` got independent fresh vars even when `y = -2`,
    // letting a contradiction (e.g. the same value forced both `> 0` and `< -2`)
    // be dodged — a wrong-SAT (#bug27).
    state.emit_zero_divisor_congruence(terms);

    // Symbolic-divisor congruence: `mod`/`div` are FUNCTIONS, so two symbolic
    // `(op x1 y1)`, `(op x2 y2)` with `x1 = x2 ∧ y1 = y2` must give equal results.
    // The fresh-var replacement above gives each its own var, dropping that
    // congruence — notably in the zero-divisor case `(mod v1 v1)` vs `(mod 0 v1)`,
    // which both denote `(mod 0 0)` when `v1 = 0` yet got independent free vars,
    // letting a forced contradiction be dodged (a wrong-SAT).
    state.emit_symbolic_divisor_congruence(terms);

    // Cross-class congruence: a LITERAL-zero-divisor var `(op d 0)` and a
    // SYMBOLIC-divisor term `(op x y)` denote the SAME application `op(value, 0)`
    // when `d = x ∧ y = 0`. The two paths build SEPARATE result vars, so neither
    // emitter above pairs them; without this link a model could give `(div x 0)`
    // and `(div (* x x) x)` different values at `x = 0` (both `div(0,0)`), a
    // wrong-SAT (#nia-zero-vs-symbolic-divisor-congruence).
    state.emit_zero_vs_symbolic_divisor_congruence(terms);

    // Isolate lone constant-divisor remainder vars in equality-family atoms so
    // their div-def-pinned value propagates (see `isolate_remainder_eq_atom`).
    // Sound equisatisfiability rewrite; length-preserving.
    let rem_vars: HashSet<TermId> = state.const_divmod_qr.values().map(|&(_, r)| r).collect();
    let rewritten: Vec<TermId> = if rem_vars.is_empty() {
        rewritten
    } else {
        rewritten
            .into_iter()
            .map(|f| isolate_remainder_eq_atom(terms, f, &rem_vars))
            .collect()
    };

    // Output must have same number of formulas as input (#4661)
    debug_assert_eq!(
        rewritten.len(),
        formulas.len(),
        "BUG: mod/div elimination changed formula count from {} to {}",
        formulas.len(),
        rewritten.len()
    );

    ModDivElimResult {
        constraints: state.constraints,
        rewritten,
        introduced_unconstrained_div_mod: state.introduced_unconstrained_div_mod,
    }
}

pub(super) fn contains_int_mod_div_by_constant(terms: &TermStore, formulas: &[TermId]) -> bool {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = formulas.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && (name == "mod" || name == "div") =>
            {
                if extract_int_constant(terms, args[1]).is_some() {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!(
                "unhandled TermData variant in contains_int_mod_div_by_constant(): {other:?}"
            ),
        }
    }
    false
}

/// True if any `(mod a b)` / `(div a b)` has a SYMBOLIC (non-constant) divisor.
///
/// These are exactly the terms `eliminate_int_mod_div_by_constant` leaves
/// intact: the constant-divisor pass only rewrites `(op a k)` for an integer
/// constant `k`. A symbolic divisor needs `eliminate_int_mod_div` (the
/// symbolic-divisor variant) so the term becomes a tableau-supported fresh var
/// constrained by the division axioms — otherwise the LRA layer drops every atom
/// containing it as unsupported (#nia-modxx-zerodiv). Binder bodies are NOT
/// descended: the executor handles quantified terms separately and the
/// elimination must not introduce free vars across binders.
pub(super) fn contains_symbolic_int_mod_div(terms: &TermStore, formulas: &[TermId]) -> bool {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = formulas.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && (name == "mod" || name == "div") =>
            {
                if extract_int_constant(terms, args[1]).is_none() {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            // Do NOT descend into quantifier bodies: `eliminate_int_mod_div`
            // leaves `Forall`/`Exists` unchanged to avoid free vars across
            // binders, so a symbolic mod/div under a binder is not something this
            // pre-pass can (or should) eliminate.
            TermData::Forall(..) | TermData::Exists(..) => {}
            // All current TermData variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => {
                unreachable!(
                    "unhandled TermData variant in contains_symbolic_int_mod_div(): {other:?}"
                )
            }
        }
    }
    false
}

/// True if any `(rem a b)` application survives in `formulas`.
///
/// `TermStore::mk_rem` folds a non-zero CONSTANT divisor before interning, so a
/// surviving `rem` application necessarily has a symbolic or literal-zero
/// divisor — a case `mod_div_elim` does NOT eliminate (lowering it to `mod`/`ite`
/// was path-fragile, see `rewrite_rem`). The aggressive NIA tentative-model
/// patch would otherwise treat such a `(rem a b)` as a FREE integer and wave
/// through a model violating its defining bound (a wrong-SAT), so callers on the
/// NIA path use this to degrade to a sound `unknown` instead. Binder bodies are
/// not descended (consistent with the other detectors here).
pub(super) fn contains_int_rem(terms: &TermStore, formulas: &[TermId]) -> bool {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = formulas.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::App(Symbol::Named(name), args) if args.len() == 2 && name == "rem" => {
                return true;
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(..) | TermData::Exists(..) => {}
            other => {
                unreachable!("unhandled TermData variant in contains_int_rem(): {other:?}")
            }
        }
    }
    false
}

struct ModDivElimState {
    constraints: Vec<TermId>,
    memo: HashMap<TermId, TermId>,
    /// Shared `(quotient, remainder)` per `(rewritten dividend, non-zero
    /// constant divisor k)`, so `(div a k)` and `(mod a k)` over the SAME
    /// dividend reuse ONE `(q, r)` pair constrained once by
    /// `a = k*q + r ∧ 0 ≤ r < |k|`. Without sharing, `div` and `mod` minted
    /// independent pairs and the Euclidean identity
    /// `a = k*(div a k) + (mod a k)` was only derivable via a uniqueness
    /// argument the LIA layer left as `unknown` (and could spin on).
    const_divmod_qr: HashMap<(TermId, BigInt), (TermId, TermId)>,
    /// Shared `(quotient, remainder)` per `(rewritten dividend, rewritten
    /// SYMBOLIC divisor)` — the symbolic-divisor twin of `const_divmod_qr`. One
    /// pair serves both `(div x y)` and `(mod x y)` and is constrained once per
    /// call, so the Euclidean identity linking them is immediate rather than a
    /// uniqueness deduction. See [`ModDivElimState::symbolic_divmod_var`].
    sym_divmod_qr: HashMap<(TermId, TermId), (TermId, TermId)>,
    symbolic_divisors: bool,
    /// See `ModDivElimResult::introduced_unconstrained_div_mod`.
    introduced_unconstrained_div_mod: bool,
    /// True if THIS elimination call minted (or re-interned) at least one
    /// literal-zero-divisor var via [`Self::zero_divisor_var`]. The set of
    /// `_ay_zerodiv_*` vars in the (append-only) store can only change in a
    /// call that sets this flag, so `emit_zero_divisor_congruence` can skip
    /// its whole-store scan whenever the flag is false: every same-op pair it
    /// would find was already emitted by the most recent var-creating call
    /// (which scans globally and pairs old + new vars alike). This is the
    /// gate that keeps per-assertion elimination LINEAR — the unconditional
    /// scan was O(assertions x term-store) and alone consumed the entire
    /// solve budget on large mod/div-free industrial files (Certora
    /// QF_UFLIA, 150k+ assertions: >99% of all CPU samples sat in
    /// `collect_zero_divisor_vars` before the solver ever started).
    created_zero_divisor: bool,
    /// Each SYMBOLIC-divisor mod/div eliminated, as `(is_mod, x, y, result)`
    /// where `x`/`y` are the rewritten dividend/divisor and `result` is the fresh
    /// var standing for `(op x y)`. Used to restore the function congruence the
    /// fresh-var replacement breaks (#nia-symbolic-divisor-congruence): two
    /// symbolic `(mod x1 y1)`, `(mod x2 y2)` with `x1=x2 ∧ y1=y2` must give equal
    /// results — including the zero-divisor case (`(mod v1 v1)` and `(mod 0 v1)`
    /// both become `(mod 0 0)` when `v1 = 0`), which the per-term fresh vars
    /// otherwise leave free.
    symbolic_terms: Vec<(bool, TermId, TermId, TermId)>,
}

impl ModDivElimState {
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn rewrite_term(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        stacker::maybe_grow(MOD_DIV_STACK_RED_ZONE, MOD_DIV_STACK_SIZE, || {
            if let Some(&rewritten) = self.memo.get(&term) {
                return rewritten;
            }

            let sort = terms.sort(term).clone();
            let data = terms.get(term).clone();

            let rewritten = match data {
                TermData::Const(_) | TermData::Var(_, _) => term,

                TermData::Not(inner) => {
                    let inner_rewritten = self.rewrite_term(terms, inner);
                    if inner_rewritten == inner {
                        term
                    } else {
                        terms.mk_not(inner_rewritten)
                    }
                }

                TermData::Ite(cond, then_term, else_term) => {
                    let cond_rewritten = self.rewrite_term(terms, cond);
                    let then_rewritten = self.rewrite_term(terms, then_term);
                    let else_rewritten = self.rewrite_term(terms, else_term);
                    if cond_rewritten == cond
                        && then_rewritten == then_term
                        && else_rewritten == else_term
                    {
                        term
                    } else {
                        terms.mk_ite(cond_rewritten, then_rewritten, else_rewritten)
                    }
                }

                // NOTE: Avoid introducing free vars across binders.
                // Quantified terms are handled separately by the executor; keep them unchanged here.
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => term,

                TermData::App(Symbol::Named(name), args) if name == "mod" && args.len() == 2 => {
                    if let Some(k) = extract_int_constant(terms, args[1]) {
                        self.rewrite_mod(terms, args[0], k)
                    } else if self.symbolic_divisors {
                        self.rewrite_mod_symbolic(terms, args[0], args[1])
                    } else {
                        let (changed, rewritten_args) = self.rewrite_args(terms, &args);
                        if changed {
                            terms.mk_mod(rewritten_args[0], rewritten_args[1])
                        } else {
                            term
                        }
                    }
                }

                TermData::App(Symbol::Named(name), args) if name == "div" && args.len() == 2 => {
                    if let Some(k) = extract_int_constant(terms, args[1]) {
                        self.rewrite_div(terms, args[0], k)
                    } else if self.symbolic_divisors {
                        self.rewrite_div_symbolic(terms, args[0], args[1])
                    } else {
                        let (changed, rewritten_args) = self.rewrite_args(terms, &args);
                        if changed {
                            terms.mk_intdiv(rewritten_args[0], rewritten_args[1])
                        } else {
                            term
                        }
                    }
                }

                // SMT-LIB/Z3 `rem` (remainder takes the sign of the DIVISOR).
                // Lowered to `mod`/`ite` here so no raw `rem` application ever
                // reaches the LIA/NIA solver — see `rewrite_rem` for the
                // soundness argument (#nia-symbolic-rem-wrong-sat).
                TermData::App(Symbol::Named(name), args) if name == "rem" && args.len() == 2 => {
                    self.rewrite_rem(terms, args[0], args[1])
                }

                TermData::App(sym, args) => {
                    let (changed, rewritten_args) = self.rewrite_args(terms, &args);
                    if changed {
                        terms.mk_app(sym, rewritten_args, sort)
                    } else {
                        term
                    }
                }
                // All current TermData variants are handled above.
                // This arm is required by #[non_exhaustive] and catches future variants.
                other => unreachable!("unhandled TermData variant in rewrite_term(): {other:?}"),
            };

            self.memo.insert(term, rewritten);
            rewritten
        }) // stacker::maybe_grow
    }

    fn rewrite_args(&mut self, terms: &mut TermStore, args: &[TermId]) -> (bool, Vec<TermId>) {
        let mut changed = false;
        let mut rewritten_args = Vec::with_capacity(args.len());
        for &arg in args {
            let rewritten = self.rewrite_term(terms, arg);
            changed |= rewritten != arg;
            rewritten_args.push(rewritten);
        }
        (changed, rewritten_args)
    }

    fn rewrite_mod(&mut self, terms: &mut TermStore, dividend: TermId, k: BigInt) -> TermId {
        // SMT-LIB Ints makes `mod` TOTAL but leaves `(mod a 0)` UNCONSTRAINED:
        // it denotes a single consistent but unspecified integer. We therefore
        // return an unconstrained variable rather than pinning it to `a`.
        //
        // Soundness: emitting no constraints over the var allows it to take any
        // value, matching z3 / SMT-LIB. Consistency: the variable is keyed by
        // the (operator, dividend) pair via a deterministic interned NAME, so
        // every occurrence of `(mod a 0)` — even across separately-eliminated
        // assertions — resolves to the SAME variable (so `(= (mod 1 0) 0)` and
        // `(= (mod 1 0) 1)` are jointly UNSAT, as z3 requires). `(mod a 0)` and
        // `(mod b 0)` with distinct dividends get independent variables (#div0).
        if k == BigInt::from(0) {
            self.introduced_unconstrained_div_mod = true;
            let x = self.rewrite_term(terms, dividend);
            return self.zero_divisor_var(terms, "mod", x);
        }

        let x = self.rewrite_term(terms, dividend);
        let (_, r) = self.constant_divmod_qr(terms, x, k);
        r
    }

    /// Canonical `(quotient, remainder)` for `(op dividend k)` with a non-zero
    /// constant `k`, shared between `div` and `mod` of the SAME dividend so the
    /// single defining constraint `dividend = k*q + r ∧ 0 ≤ r < |k|` links them
    /// (emitted exactly once). Sharing is sound — both ops denote the unique
    /// Euclidean `(q, r)` — and makes `dividend = k*(div ..) + (mod ..)`
    /// immediate instead of requiring a uniqueness deduction the LIA layer
    /// otherwise gives up on (`unknown`).
    fn constant_divmod_qr(
        &mut self,
        terms: &mut TermStore,
        dividend: TermId,
        k: BigInt,
    ) -> (TermId, TermId) {
        if let Some(&qr) = self.const_divmod_qr.get(&(dividend, k.clone())) {
            return qr;
        }
        let q = terms.mk_fresh_var("_divmod_q", Sort::Int);
        let r = terms.mk_fresh_var("_divmod_r", Sort::Int);
        self.add_division_constraints(terms, dividend, k.clone(), q, r);
        self.const_divmod_qr.insert((dividend, k), (q, r));
        (q, r)
    }

    fn rewrite_div(&mut self, terms: &mut TermStore, dividend: TermId, k: BigInt) -> TermId {
        // SMT-LIB Ints makes `div` TOTAL but leaves `(div a 0)` UNCONSTRAINED:
        // it denotes a single consistent but unspecified integer. We therefore
        // return an unconstrained variable rather than pinning it to 0.
        //
        // See `rewrite_mod` for the soundness/consistency argument (#div0).
        if k == BigInt::from(0) {
            self.introduced_unconstrained_div_mod = true;
            let x = self.rewrite_term(terms, dividend);
            return self.zero_divisor_var(terms, "div", x);
        }

        let x = self.rewrite_term(terms, dividend);
        let (q, _) = self.constant_divmod_qr(terms, x, k);
        q
    }

    /// Eliminate `(rem dividend divisor)` (SMT-LIB / Z3 `rem`, whose sign
    /// follows the DIVISOR, not the dividend).
    ///
    /// For a non-zero divisor, `rem(x, y) = (mod x y)` when `y > 0` and
    /// `-(mod x y)` when `y < 0`. For a zero divisor it is under-specified and,
    /// per Z3 #9140, DISTINCT from `(mod x 0)`, so it gets its own deterministic
    /// unconstrained var (`_ay_zerodiv_rem_*`) kept consistent across equal
    /// dividends by [`Self::emit_zero_divisor_congruence`].
    ///
    /// SOUNDNESS / WHY THIS EXISTS: this is exactly the semantics ay's constant
    /// folder already assigns `rem` (`TermStore::mk_rem` → `ite(y>=0, mod, -mod)`),
    /// here lowered to `mod`/`ite` at the `TermId` level. The crucial effect is
    /// that it REMOVES the raw `rem` application: `rem` is not in the LIA/NIA
    /// `div`/`mod` support set, so a surviving symbolic `(rem x y)` was treated
    /// as an UNINTERPRETED integer whose defining bound `0 ≤ rem < |y|` was
    /// silently dropped, yielding a wrong-SAT (e.g. `y>0 ∧ (rem x y) < 0`).
    /// `mk_rem` folds a non-zero CONSTANT divisor before interning, so in
    /// practice only the symbolic and literal-zero divisors reach here.
    fn rewrite_rem(&mut self, terms: &mut TermStore, dividend: TermId, divisor: TermId) -> TermId {
        let x = self.rewrite_term(terms, dividend);

        // Constant divisor (defensive — `mk_rem` normally folds the non-zero
        // constant case away before this term is ever interned).
        if let Some(k) = extract_int_constant(terms, divisor) {
            if k == BigInt::from(0) {
                // `(rem x 0)` is unconstrained. Deliberately do NOT set
                // `introduced_unconstrained_div_mod` here: unlike `mod`/`div`,
                // `rem` IS replayable by the model evaluator for a non-zero
                // divisor, so we want ordinary model validation to GATE the SAT
                // verdict. The blanket #div0 bypass would otherwise also wave
                // through a model in which a SYMBOLIC `(rem x y)` (lowered below
                // to `mod`) is left unsolved and violates its defining bound —
                // a wrong-SAT (#nia-symbolic-rem-bypass). A genuine `(rem x 0)`
                // SAT then degrades to a sound `unknown` instead, and a problem
                // that also contains `(mod x 0)`/`(div x 0)` still gets their
                // bypass from `rewrite_mod`/`rewrite_div`.
                return self.zero_divisor_var(terms, "rem", x);
            }
            let (_, r) = self.constant_divmod_qr(terms, x, k.clone());
            return if k.is_negative() { terms.mk_neg(r) } else { r };
        }

        // Symbolic divisor: a non-constant-divisor `rem` is NOT eliminated.
        // Earlier attempts to lower it to `mod`/`ite` proved path-fragile: on the
        // NIA path the ite-wrapped symbolic `mod` was waved through by the
        // tentative-model patch as a wrong-SAT (where a BARE symbolic `mod`
        // soundly yields `unknown`). Symbolic-divisor `rem` is rare (the
        // constant-divisor cases the trust toolchain actually emits are folded
        // by `TermStore::mk_rem` before they reach here), so we keep it as a
        // `rem` application and let it degrade to a sound `unknown`: `rem` now
        // sets `has_int_div_mod` (so the formula leaves the UF/LIA fast path that
        // would otherwise treat `(rem x y)` as a free uninterpreted integer), and
        // the model evaluator can replay `rem` for a non-zero divisor, so an
        // unsound model is rejected by validation rather than accepted. We do NOT
        // set `introduced_unconstrained_div_mod` (no #div0 validation bypass for
        // `rem`). (#nia-symbolic-rem-bypass.)
        let y = self.rewrite_term(terms, divisor);
        terms.mk_rem(x, y)
    }

    /// Deterministic unconstrained variable representing `(op dividend 0)` for a
    /// zero divisor. Keyed by an interned name encoding `(op, dividend)` so that
    /// every occurrence resolves to the SAME `TermId` — the SMT-LIB requirement
    /// that `(op a 0)` denotes a single consistent (if unspecified) value. `div`
    /// and `mod` keep separate names so `(div a 0)` and `(mod a 0)` stay
    /// independent (also matching z3) (#div0).
    fn zero_divisor_var(&mut self, terms: &mut TermStore, op: &str, dividend: TermId) -> TermId {
        self.created_zero_divisor = true;
        let name = format!("_ay_zerodiv_{op}_{}", dividend.index());
        terms.mk_var(name, Sort::Int)
    }

    /// Deterministic quotient/remainder variable for a SYMBOLIC-divisor
    /// `(div a b)` / `(mod a b)` — the counterpart of [`Self::zero_divisor_var`]
    /// for the case the literal-zero path never sees. `kind` is `"q"` (the
    /// quotient, i.e. the value of `(div a b)`) or `"r"` (the remainder, i.e.
    /// the value of `(mod a b)`).
    ///
    /// #symbolic-div0-unpinned — these used to be `mk_fresh_var("_div_q", ..)`,
    /// whose name is a bare counter, so nothing outside this pass could map the
    /// application `(div a b)` back to the variable holding the value the
    /// solver chose for it. When `b` is symbolic but evaluates to 0 the SMT-LIB
    /// result is UNCONSTRAINED, `add_symbolic_division_constraints` leaves the
    /// variable free, the solver picks a value — and the model published none,
    /// so the mandatory independent gate could not confirm a correct `sat`.
    /// There is nothing for the evaluator to RECOMPUTE in that case, so it has
    /// to read the chosen value back, and interning by
    /// `(kind, dividend-id, divisor-id)` is what lets it find the variable —
    /// while also making every occurrence of the SAME application resolve to
    /// the SAME variable, as SMT-LIB requires of a single consistent (if
    /// unspecified) value. `model::eval_arith` reconstructs this exact name;
    /// THE TWO MUST BE CHANGED TOGETHER.
    ///
    /// The name deliberately does NOT encode the OPERATOR: `(div a b)` and
    /// `(mod a b)` over the same operands share ONE `(q, r)` pair, exactly as
    /// [`Self::constant_divmod_qr`] does for a constant divisor. Both operators
    /// are defined by the SAME constraint system (see
    /// [`Self::add_symbolic_division_constraints`], which does not even look at
    /// its `result_kind`), and for `b != 0` the Euclidean pair is unique, so
    /// sharing is sound; it also makes
    /// `a = b*(div a b) + (mod a b)` immediate instead of a uniqueness deduction
    /// the LIA layer leaves as `unknown` (and can spin on). For `b = 0` the
    /// constraint's `b = 0` disjunct leaves both free, and `q` and `r` are
    /// SEPARATE variables, so `(div a 0)` and `(mod a 0)` stay independent as
    /// SMT-LIB (and z3 #9140) require.
    ///
    /// The prefix is deliberately outside the `_mod_q`/`_div_q`/`_divmod_q`
    /// family that `proof_rewrite_division` recognises by name: those matches
    /// are meant to be the CLIENT's quotient/remainder encoding, and a match on
    /// AY's own auxiliaries is what #authored-aux-name-collision is about.
    fn symbolic_divmod_var(
        terms: &mut TermStore,
        kind: &str,
        dividend: TermId,
        divisor: TermId,
    ) -> TermId {
        let name = format!("_ay_symdiv_{kind}_{}_{}", dividend.index(), divisor.index());
        terms.mk_var(name, Sort::Int)
    }

    /// The shared `(quotient, remainder)` pair for a symbolic-divisor
    /// `(op dividend divisor)`, with the defining constraint emitted exactly
    /// ONCE per pair per elimination call. See [`Self::symbolic_divmod_var`] for
    /// why `div` and `mod` share the pair.
    ///
    /// The memo is deliberately per-call state. The variables intern globally by
    /// NAME, but a later call must still re-emit the defining constraint
    /// alongside its own rewritten formulas: suppressing emission because the
    /// variable already exists in the (append-only) store would leave it free
    /// whenever the earlier call's constraints are not in scope — a wrong-SAT.
    fn symbolic_divmod_qr(
        &mut self,
        terms: &mut TermStore,
        dividend: TermId,
        divisor: TermId,
        result_kind: SymbolicDivResult,
    ) -> (TermId, TermId) {
        let q = Self::symbolic_divmod_var(terms, "q", dividend, divisor);
        let r = Self::symbolic_divmod_var(terms, "r", dividend, divisor);
        if self
            .sym_divmod_qr
            .insert((dividend, divisor), (q, r))
            .is_none()
        {
            self.add_symbolic_division_constraints(terms, dividend, divisor, q, r, result_kind);
        }
        (q, r)
    }

    /// Scan the WHOLE store for literal-zero-divisor vars created by
    /// `zero_divisor_var`, returning `(is_mod, dividend, var)` for each distinct
    /// one. Scanning the whole store (not just this call's state) is required
    /// because the two halves of `(and (> (mod -2 0) 0) … (> y (mod y 0)) …)` are
    /// often eliminated in SEPARATE calls; the vars intern by the name
    /// `_ay_zerodiv_{op}_{dividend_index}` and persist in the append-only store,
    /// so a global scan recovers the operator and dividend of every one created.
    /// Deterministically ordered and deduplicated by `(is_mod, var)`.
    fn collect_zero_divisor_vars(terms: &TermStore) -> Vec<(DivModOp, TermId, TermId)> {
        let mut entries: Vec<(DivModOp, TermId, TermId)> = Vec::new();
        for idx in 0..terms.len() {
            let t = TermId::new(idx as u32);
            if let TermData::Var(name, _) = terms.get(t) {
                let Some(rest) = name.strip_prefix("_ay_zerodiv_") else {
                    continue;
                };
                let (op, idx_str) = if let Some(s) = rest.strip_prefix("mod_") {
                    (DivModOp::Mod, s)
                } else if let Some(s) = rest.strip_prefix("div_") {
                    (DivModOp::Div, s)
                } else if let Some(s) = rest.strip_prefix("rem_") {
                    (DivModOp::Rem, s)
                } else {
                    continue;
                };
                if let Ok(div_idx) = idx_str.parse::<u32>() {
                    entries.push((op, TermId::new(div_idx), t));
                }
            }
        }
        entries.sort_unstable_by_key(|&(op, _, v)| (op as u8, v.0));
        entries.dedup_by_key(|&mut (op, _, v)| (op as u8, v));
        entries
    }

    /// Emit zero-divisor congruence: for every pair of same-operator zero-divisor
    /// terms with DISTINCT (syntactic) dividends, add
    /// `(=> (= dividend_i dividend_j) (= var_i var_j))`. `(mod a 0)` / `(div a 0)`
    /// denote a single consistent value that depends only on the dividend's
    /// VALUE, so equal dividends must give equal results. SOUND — it only prunes
    /// models where equal dividends were assigned different zero-divisor results,
    /// which SMT-LIB forbids. Bounded O(n^2) over the distinct zero-divisor vars.
    fn emit_zero_divisor_congruence(&mut self, terms: &mut TermStore) {
        // Whole-store scan gate (see `created_zero_divisor`): a call that
        // minted no zero-divisor var cannot have changed the pair set — every
        // pair among the pre-existing vars was already emitted by the last
        // var-creating call's global scan (and re-emitting them here was pure
        // duplication). Skipping keeps per-assertion elimination linear.
        if !self.created_zero_divisor {
            return;
        }
        let entries = Self::collect_zero_divisor_vars(terms);
        const MAX_ZERO_DIV_TERMS: usize = 64;
        if entries.len() < 2 || entries.len() > MAX_ZERO_DIV_TERMS {
            return;
        }
        for i in 0..entries.len() {
            for j in (i + 1)..entries.len() {
                let (mi, di, vi) = entries[i];
                let (mj, dj, vj) = entries[j];
                // `div`/`mod`/`rem` are independent functions; equal dividends
                // only constrain results within the same operator.
                if mi != mj || di == dj {
                    continue;
                }
                let div_eq = terms.mk_eq(di, dj);
                let var_eq = terms.mk_eq(vi, vj);
                let not_div_eq = terms.mk_not(div_eq);
                let implication = terms.mk_or(vec![not_div_eq, var_eq]);
                self.constraints.push(implication);
            }
        }
    }

    /// Emit symbolic-divisor congruence (#nia-symbolic-divisor-congruence): for
    /// every pair of same-operator symbolic mod/div terms `(op x_i y_i)` /
    /// `(op x_j y_j)` (result vars `res_i` / `res_j`), add
    /// `(=> (and (= x_i x_j) (= y_i y_j)) (= res_i res_j))`. `mod`/`div` are
    /// functions, so equal operands force equal results — this restores the
    /// congruence the per-term fresh-var replacement dropped, including the
    /// zero-divisor case. SOUND: only prunes models that violate function
    /// congruence (which SMT-LIB forbids). Bounded O(n^2).
    fn emit_symbolic_divisor_congruence(&mut self, terms: &mut TermStore) {
        const MAX_SYMBOLIC_DIV_TERMS: usize = 64;
        if self.symbolic_terms.len() < 2 || self.symbolic_terms.len() > MAX_SYMBOLIC_DIV_TERMS {
            return;
        }
        // Deterministic order.
        let mut entries = self.symbolic_terms.clone();
        entries.sort_unstable_by_key(|&(is_mod, x, y, res)| (is_mod, x.0, y.0, res.0));
        for i in 0..entries.len() {
            for j in (i + 1)..entries.len() {
                let (mi, xi, yi, ri) = entries[i];
                let (mj, xj, yj, rj) = entries[j];
                if mi != mj || ri == rj {
                    continue;
                }
                // If operands are SYNTACTICALLY identical the term store would have
                // hash-consed both to the same result var; distinct vars here imply
                // distinct operand syntax, so the implication is non-trivial.
                let x_eq = terms.mk_eq(xi, xj);
                let y_eq = terms.mk_eq(yi, yj);
                let operands_eq = terms.mk_and(vec![x_eq, y_eq]);
                let res_eq = terms.mk_eq(ri, rj);
                let not_operands_eq = terms.mk_not(operands_eq);
                let implication = terms.mk_or(vec![not_operands_eq, res_eq]);
                self.constraints.push(implication);
            }
        }
    }

    /// Emit cross-class congruence linking a LITERAL-zero-divisor var `(op d 0)`
    /// (result var `v`, dividend `d`) to a SYMBOLIC-divisor term `(op x y)`
    /// (result var `r`) of the SAME operator:
    /// `(=> (and (= d x) (= y 0)) (= v r))`.
    ///
    /// Both spellings denote the same function application `op(value, 0)` whenever
    /// `value(d) = value(x)` and `value(y) = 0`, so they must give equal results.
    /// The per-term var replacement keeps these in two SEPARATE classes
    /// (`zero_divisor_var` → `_ay_zerodiv_*` for the literal-0 path,
    /// `symbolic_divmod_var` → `_ay_symdiv_*` for the symbolic path), so neither
    /// `emit_zero_divisor_congruence` nor `emit_symbolic_divisor_congruence`
    /// ever pairs them. Without this link a
    /// model can assign `(div x 0)` and `(div (* x x) x)` different values when
    /// `x = 0` (both are `div(0,0)`), dodging an otherwise-forced contradiction —
    /// a wrong-SAT (e.g. `x=0 ∧ (distinct (div x 0) (div (* x x) x))`).
    ///
    /// SOUND: the implication only prunes models that violate function congruence
    /// (which SMT-LIB forbids); it can never flip a genuine sat/unsat. The guard
    /// `(= y 0)` keeps it inert when the symbolic divisor is non-zero. Bounded
    /// O(zero_div × symbolic) with both classes capped at 64.
    fn emit_zero_vs_symbolic_divisor_congruence(&mut self, terms: &mut TermStore) {
        const MAX_TERMS: usize = 64;
        if self.symbolic_terms.is_empty() || self.symbolic_terms.len() > MAX_TERMS {
            return;
        }
        let zero_vars = Self::collect_zero_divisor_vars(terms);
        if zero_vars.is_empty() || zero_vars.len() > MAX_TERMS {
            return;
        }
        let zero = terms.mk_int(BigInt::from(0));
        // Deterministic order over symbolic terms.
        let mut sym = self.symbolic_terms.clone();
        sym.sort_unstable_by_key(|&(is_mod, x, y, res)| (is_mod, x.0, y.0, res.0));
        for &(z_op, d, v) in &zero_vars {
            for &(s_is_mod, x, y, r) in &sym {
                // `div`/`mod`/`rem` are independent functions. The symbolic side
                // only ever records `mod` (`s_is_mod == true`) or `div`; a `rem`
                // zero-divisor var has no symbolic counterpart to link to.
                let same_op = match z_op {
                    DivModOp::Mod => s_is_mod,
                    DivModOp::Div => !s_is_mod,
                    DivModOp::Rem => false,
                };
                if !same_op {
                    continue;
                }
                // `(op d 0)` (literal) and `(op x y)` (symbolic) are the same
                // application only when `d = x` AND `y = 0`. The `y = 0` guard
                // keeps the implication inert whenever the symbolic divisor is
                // non-zero, so it never constrains a genuine non-zero-divisor
                // model (preserving completeness).
                let d_eq_x = terms.mk_eq(d, x);
                let y_eq_zero = terms.mk_eq(y, zero);
                let antecedent = terms.mk_and(vec![d_eq_x, y_eq_zero]);
                let res_eq = terms.mk_eq(v, r);
                let not_antecedent = terms.mk_not(antecedent);
                let implication = terms.mk_or(vec![not_antecedent, res_eq]);
                self.constraints.push(implication);
            }
        }
    }

    fn rewrite_mod_symbolic(
        &mut self,
        terms: &mut TermStore,
        dividend: TermId,
        divisor: TermId,
    ) -> TermId {
        let x = self.rewrite_term(terms, dividend);
        let y = self.rewrite_term(terms, divisor);

        // A symbolic divisor may be zero; the `divisor == 0` disjunct in the
        // constraints below leaves q/r unconstrained (matching the SMT-LIB
        // under-specification). There is then nothing for the standard model
        // evaluator to recompute, so it reads back the value the solve chose for
        // `r` — possible only because `symbolic_divmod_var` gives it a
        // deterministic name (#symbolic-div0-unpinned). SAT results that depend
        // on this case still route through the validation bypass (#div0): the
        // read-back restores completeness, it does not certify the rewrite.
        self.introduced_unconstrained_div_mod = true;
        let (_, r) = self.symbolic_divmod_qr(terms, x, y, SymbolicDivResult::Mod);
        self.symbolic_terms.push((true, x, y, r));
        r
    }

    fn rewrite_div_symbolic(
        &mut self,
        terms: &mut TermStore,
        dividend: TermId,
        divisor: TermId,
    ) -> TermId {
        let x = self.rewrite_term(terms, dividend);
        let y = self.rewrite_term(terms, divisor);

        // See `rewrite_mod_symbolic`: the symbolic zero-divisor case is
        // unconstrained, so SAT must route through the validation bypass (#div0)
        // and the evaluator reads the chosen `q` back by name. Sharing the pair
        // with `(mod x y)` is what links `x = y*q + r` for both operators.
        self.introduced_unconstrained_div_mod = true;
        let (q, _) = self.symbolic_divmod_qr(terms, x, y, SymbolicDivResult::Div);
        self.symbolic_terms.push((false, x, y, q));
        q
    }

    fn add_division_constraints(
        &mut self,
        terms: &mut TermStore,
        dividend: TermId,
        k: BigInt,
        q: TermId,
        r: TermId,
    ) {
        // Divisor must be non-zero (callers handle k==0 case before reaching here) (#4661)
        debug_assert!(
            k != BigInt::from(0),
            "BUG: add_division_constraints called with zero divisor"
        );

        let zero = terms.mk_int(BigInt::from(0));
        let k_term = terms.mk_int(k.clone());
        let k_abs_term = terms.mk_int(k.abs());

        // x = k*q + r
        let k_times_q = terms.mk_mul(vec![k_term, q]);
        let k_times_q_plus_r = terms.mk_add(vec![k_times_q, r]);
        let eq = terms.mk_eq(dividend, k_times_q_plus_r);

        // 0 <= r
        let r_ge_0 = terms.mk_ge(r, zero);

        // r < |k|
        let r_lt_k = terms.mk_lt(r, k_abs_term);

        self.constraints.push(eq);
        self.constraints.push(r_ge_0);
        self.constraints.push(r_lt_k);
    }

    fn add_symbolic_division_constraints(
        &mut self,
        terms: &mut TermStore,
        dividend: TermId,
        divisor: TermId,
        q: TermId,
        r: TermId,
        _result_kind: SymbolicDivResult,
    ) {
        let zero = terms.mk_int(BigInt::from(0));
        let divisor_eq_zero = terms.mk_eq(divisor, zero);

        let divisor_times_q = terms.mk_mul(vec![divisor, q]);
        let recomposed = terms.mk_add(vec![divisor_times_q, r]);
        let decomposition = terms.mk_eq(dividend, recomposed);
        let r_ge_zero = terms.mk_ge(r, zero);

        let divisor_gt_zero = terms.mk_gt(divisor, zero);
        let r_lt_pos_divisor = terms.mk_lt(r, divisor);
        let positive_case = terms.mk_and(vec![
            divisor_gt_zero,
            decomposition,
            r_ge_zero,
            r_lt_pos_divisor,
        ]);

        let divisor_lt_zero = terms.mk_lt(divisor, zero);
        let neg_divisor = terms.mk_neg(divisor);
        let r_lt_abs_neg_divisor = terms.mk_lt(r, neg_divisor);
        let negative_case = terms.mk_and(vec![
            divisor_lt_zero,
            decomposition,
            r_ge_zero,
            r_lt_abs_neg_divisor,
        ]);

        self.constraints
            .push(terms.mk_or(vec![divisor_eq_zero, positive_case, negative_case]));
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SymbolicDivResult {
    Div,
    Mod,
}
