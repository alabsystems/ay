// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA model evaluation and recovery helpers.
//!
//! Free functions for evaluating integer/boolean terms under a model
//! and recovering variable values from asserted equalities and
//! variable substitutions. Used by `lia.rs` and `combined.rs`.
//!
//! Split from `lia.rs` for code health (#7006, #5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::TermId;
use ay_euf::EufModel;
use ay_lia::LiaModel;

use crate::preprocess::VariableSubstitution;

/// One shared fail-closed envelope for mutually-recursive Int/Bool/BV model
/// evaluation.  Crossing `bv2nat`/`int2bv` or an `ite` condition never resets
/// either limit.
const MAX_LIA_MODEL_EVAL_WORK: usize = 16_384;
const MAX_LIA_MODEL_EVAL_DEPTH: usize = 512;

struct LiaModelEvalBudget {
    remaining: usize,
    depth: usize,
    depth_limit: usize,
    active: HashSet<TermId>,
}

impl LiaModelEvalBudget {
    fn new() -> Self {
        Self {
            remaining: MAX_LIA_MODEL_EVAL_WORK,
            depth: 0,
            depth_limit: MAX_LIA_MODEL_EVAL_DEPTH,
            active: HashSet::default(),
        }
    }

    #[cfg(test)]
    fn limited(remaining: usize, depth_limit: usize) -> Self {
        Self {
            remaining,
            depth: 0,
            depth_limit,
            active: HashSet::default(),
        }
    }

    fn enter(&mut self, term: TermId) -> bool {
        if self.remaining == 0 || self.depth >= self.depth_limit || !self.active.insert(term) {
            return false;
        }
        self.remaining -= 1;
        self.depth += 1;
        true
    }

    fn leave(&mut self, term: TermId) {
        debug_assert!(self.active.remove(&term));
        self.depth = self.depth.saturating_sub(1);
    }
}

fn checked_bv_extract_width(high: u32, low: u32) -> Option<u32> {
    high.checked_sub(low)?.checked_add(1)
}

fn checked_bv_width_sum(left: u32, right: u32) -> Option<u32> {
    left.checked_add(right)
}

/// SMT-LIB integer division: floor division for positive divisor,
/// negated floor division for negative divisor.
fn smtlib_div(n: &num_bigint::BigInt, d: &num_bigint::BigInt) -> num_bigint::BigInt {
    use num_integer::Integer;
    use num_traits::Signed;
    if d.is_positive() {
        n.div_floor(d)
    } else {
        // (div n d) = -(div n (-d)) for d < 0
        -n.div_floor(&(-d))
    }
}

/// Evaluate a boolean condition under the current integer model values.
pub(in crate::executor) fn eval_lia_bool_under_values(
    terms: &ay_core::TermStore,
    tid: TermId,
    values: &HashMap<TermId, num_bigint::BigInt>,
) -> Option<bool> {
    let mut budget = LiaModelEvalBudget::new();
    eval_lia_bool_under_values_inner(terms, tid, values, &mut budget)
}

fn eval_lia_bool_under_values_inner(
    terms: &ay_core::TermStore,
    tid: TermId,
    values: &HashMap<TermId, num_bigint::BigInt>,
    budget: &mut LiaModelEvalBudget,
) -> Option<bool> {
    if !budget.enter(tid) {
        return None;
    }
    let result = (|| {
        use ay_core::term::{Constant, TermData};

        match terms.get(tid) {
            TermData::Const(Constant::Bool(b)) => Some(*b),
            TermData::Not(inner) => {
                eval_lia_bool_under_values_inner(terms, *inner, values, budget).map(|b| !b)
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                match name {
                    "and" => {
                        let mut saw_unknown = false;
                        for &arg in args {
                            match eval_lia_bool_under_values_inner(terms, arg, values, budget) {
                                Some(false) => return Some(false),
                                Some(true) => {}
                                None => saw_unknown = true,
                            }
                        }
                        (!saw_unknown).then_some(true)
                    }
                    "or" => {
                        let mut saw_unknown = false;
                        for &arg in args {
                            match eval_lia_bool_under_values_inner(terms, arg, values, budget) {
                                Some(true) => return Some(true),
                                Some(false) => {}
                                None => saw_unknown = true,
                            }
                        }
                        (!saw_unknown).then_some(false)
                    }
                    "<" if args.len() == 2 => {
                        let a = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        let b = eval_lia_int_under_values_inner(terms, args[1], values, budget)?;
                        Some(a < b)
                    }
                    "<=" if args.len() == 2 => {
                        let a = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        let b = eval_lia_int_under_values_inner(terms, args[1], values, budget)?;
                        Some(a <= b)
                    }
                    ">" if args.len() == 2 => {
                        let a = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        let b = eval_lia_int_under_values_inner(terms, args[1], values, budget)?;
                        Some(a > b)
                    }
                    ">=" if args.len() == 2 => {
                        let a = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        let b = eval_lia_int_under_values_inner(terms, args[1], values, budget)?;
                        Some(a >= b)
                    }
                    "=" if args.len() == 2 => {
                        if let (Some(a), Some(b)) = (
                            eval_lia_int_under_values_inner(terms, args[0], values, budget),
                            eval_lia_int_under_values_inner(terms, args[1], values, budget),
                        ) {
                            Some(a == b)
                        } else if let (Some(a), Some(b)) = (
                            eval_lia_bool_under_values_inner(terms, args[0], values, budget),
                            eval_lia_bool_under_values_inner(terms, args[1], values, budget),
                        ) {
                            Some(a == b)
                        } else {
                            None
                        }
                    }
                    "distinct" if args.len() == 2 => {
                        if let (Some(a), Some(b)) = (
                            eval_lia_int_under_values_inner(terms, args[0], values, budget),
                            eval_lia_int_under_values_inner(terms, args[1], values, budget),
                        ) {
                            Some(a != b)
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    })();
    budget.leave(tid);
    result
}

pub(in crate::executor) fn eval_lia_int_under_values(
    terms: &ay_core::TermStore,
    tid: TermId,
    values: &HashMap<TermId, num_bigint::BigInt>,
) -> Option<num_bigint::BigInt> {
    let mut budget = LiaModelEvalBudget::new();
    eval_lia_int_under_values_inner(terms, tid, values, &mut budget)
}

fn eval_lia_int_under_values_inner(
    terms: &ay_core::TermStore,
    tid: TermId,
    values: &HashMap<TermId, num_bigint::BigInt>,
    budget: &mut LiaModelEvalBudget,
) -> Option<num_bigint::BigInt> {
    if !budget.enter(tid) {
        return None;
    }
    let result = (|| {
        use ay_core::term::{Constant, TermData};

        match terms.get(tid) {
            TermData::Const(Constant::Int(n)) => Some(n.clone()),
            TermData::Var(_, _) => values.get(&tid).cloned(),
            TermData::Ite(cond, then_t, else_t) => {
                let cond_val = eval_lia_bool_under_values_inner(terms, *cond, values, budget)?;
                if cond_val {
                    eval_lia_int_under_values_inner(terms, *then_t, values, budget)
                } else {
                    eval_lia_int_under_values_inner(terms, *else_t, values, budget)
                }
            }
            TermData::App(sym, args) => {
                let name = sym.name();
                match name {
                    "+" => {
                        let mut sum = num_bigint::BigInt::from(0);
                        for &arg in args {
                            sum += eval_lia_int_under_values_inner(terms, arg, values, budget)?;
                        }
                        Some(sum)
                    }
                    "-" if args.len() == 2 => {
                        let a = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        let b = eval_lia_int_under_values_inner(terms, args[1], values, budget)?;
                        Some(a - b)
                    }
                    "-" if args.len() == 1 => {
                        let a = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        Some(-a)
                    }
                    "*" => {
                        let mut prod = num_bigint::BigInt::from(1);
                        for &arg in args {
                            prod *= eval_lia_int_under_values_inner(terms, arg, values, budget)?;
                        }
                        Some(prod)
                    }
                    "div" if args.len() == 2 => {
                        let lhs = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        let rhs = eval_lia_int_under_values_inner(terms, args[1], values, budget)?;
                        if rhs == num_bigint::BigInt::from(0) {
                            return None;
                        }
                        Some(smtlib_div(&lhs, &rhs))
                    }
                    "mod" if args.len() == 2 => {
                        let lhs = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        let rhs = eval_lia_int_under_values_inner(terms, args[1], values, budget)?;
                        if rhs == num_bigint::BigInt::from(0) {
                            return None;
                        }
                        let q = smtlib_div(&lhs, &rhs);
                        Some(lhs - &rhs * q)
                    }
                    "abs" if args.len() == 1 => {
                        let v = eval_lia_int_under_values_inner(terms, args[0], values, budget)?;
                        Some(if v < num_bigint::BigInt::from(0) {
                            -v
                        } else {
                            v
                        })
                    }
                    // `bv2nat` is INTERPRETED, not opaque (#bv2nat-subst-recover).
                    //
                    // The Int<->BV bridge lets variable substitution eliminate a
                    // definition like `(= V (bv2nat (bvand ((_ int2bv 64) a)
                    // ((_ int2bv 64) b))))` by recording `V -> bv2nat(...)`. Model
                    // recovery then has to replay that RHS. Falling into the opaque
                    // arm below is WRONG here twice over: the surviving assertions
                    // were rewritten by the SAME substitution pass, so the LIA model
                    // keys its opaque atom by the REWRITTEN term id, not by this one
                    // (`values.get` misses and recovery yields no value at all); and
                    // even on a hit, an opaque assignment is free to disagree with
                    // the bits, which is exactly the decoupled model the independent
                    // soundness gate refutes. `V` was then left to model completion,
                    // came back as a junk default (`V = 8` against `3 & 3`), and the
                    // gate fail-closed a genuine `sat`/`unsat` to `unknown` —
                    // 17,085 of 17,586 caught invalid models across the fleet's
                    // verify logs are exactly this shape.
                    //
                    // Compute it instead. `bv2nat(t)` is a total function of `t`'s
                    // bits, so whenever the argument is structurally evaluable from
                    // the model's Int leaves there is exactly ONE correct answer and
                    // the opaque assignment is either equal to it or wrong. Prefer
                    // the computed value; keep the opaque read as the fallback for
                    // arguments this walk cannot decompose (e.g. a free BitVec
                    // variable, which carries no value in a LIA model).
                    //
                    // SOUNDNESS: evaluation-side only. It cannot create or remove a
                    // model — it fills in the value an eliminated variable ALREADY
                    // had by definition — and every promotion downstream is still
                    // arbitrated by `validate_model` and by the independent
                    // model-check gate, neither of which is touched here.
                    "bv2nat" if args.len() == 1 => {
                        eval_lia_bv_under_values_inner(terms, args[0], values, budget)
                            .map(|(value, _width)| value)
                            .or_else(|| values.get(&tid).cloned())
                    }
                    // Any OTHER Int-sorted application (an opaque array `select`, a
                    // UF application, ...) is not an arithmetic composite the walk can
                    // decompose: LIA models it as a fresh variable, so its value — if
                    // the model chose one — lives in `values` keyed by the app term
                    // itself. Read it back rather than failing the whole surrounding
                    // evaluation. (#arr-lia-subst-select-recover: a substituted var
                    // `i2 -> (+ (select A idx) k)` cannot recover unless the opaque
                    // read contributes its model value.)
                    _ => values.get(&tid).cloned(),
                }
            }
            _ => None,
        }
    })();
    budget.leave(tid);
    result
}

/// Unsigned value (and width) of a BitVec-sorted term, computed STRUCTURALLY
/// from the Int leaves already valued in `values` (#bv2nat-subst-recover).
///
/// This is the BV half of [`eval_lia_int_under_values`]. It exists so a
/// substituted variable whose definition crossed the Int<->BV boundary —
/// `V -> bv2nat(<bv expr over ((_ int2bv w) <int>) and bv literals>)`, the
/// dominant shape in the fleet's verify logs — can be recovered at its true
/// value instead of being defaulted by model completion.
///
/// Every arm is the SMT-LIB semantics of a TOTAL function of its operands'
/// values, so the result is the unique value the term takes under this model.
/// Anything not decomposable here — a free BitVec variable, an `ite` whose
/// condition is unresolved, a `select` of a BV array, an unmodelled operator —
/// returns `None`, and the caller falls back to whatever the model said. That
/// keeps the pass ADDITIVE: it never contradicts a value it cannot recompute,
/// and it never invents one.
///
/// Widths come from the term's own sort rather than from operand arithmetic, so
/// a mis-sorted term degrades to `None` instead of silently producing a value
/// at the wrong width.
fn eval_lia_bv_under_values_inner(
    terms: &ay_core::TermStore,
    tid: TermId,
    values: &HashMap<TermId, num_bigint::BigInt>,
    budget: &mut LiaModelEvalBudget,
) -> Option<(num_bigint::BigInt, u32)> {
    if !budget.enter(tid) {
        return None;
    }
    let result = (|| {
        use ay_core::term::{Constant, TermData};
        use num_bigint::BigInt;
        use num_traits::{One, Signed, ToPrimitive, Zero};

        /// `2^width - 1`.
        fn mask(width: u32) -> BigInt {
            (BigInt::one() << width as usize) - BigInt::one()
        }
        /// Euclidean reduction into `[0, 2^width)`.
        fn wrap(value: BigInt, width: u32) -> BigInt {
            let modulus = BigInt::one() << width as usize;
            let r = value % &modulus;
            if r.is_negative() {
                r + modulus
            } else {
                r
            }
        }
        /// Two's-complement signed reading of an in-range unsigned value.
        fn signed(value: &BigInt, width: u32) -> BigInt {
            let half = BigInt::one() << (width as usize - 1);
            if *value >= half {
                value - (BigInt::one() << width as usize)
            } else {
                value.clone()
            }
        }

        let width = match terms.sort(tid) {
            ay_core::Sort::BitVec(bv) => bv.width,
            _ => return None,
        };
        if width == 0 || width > 1 << 16 {
            // Degenerate or absurd widths are not worth materializing a BigInt for.
            return None;
        }

        let value = match terms.get(tid) {
            TermData::Const(Constant::BitVec {
                value,
                width: const_width,
            }) => {
                if *const_width != width {
                    return None;
                }
                wrap(value.clone(), width)
            }
            TermData::Ite(cond, then_t, else_t) => {
                let branch = if eval_lia_bool_under_values_inner(terms, *cond, values, budget)? {
                    *then_t
                } else {
                    *else_t
                };
                let (v, w) = eval_lia_bv_under_values_inner(terms, branch, values, budget)?;
                if w != width {
                    return None;
                }
                v
            }
            TermData::App(sym, args) => {
                fn operand(
                    terms: &ay_core::TermStore,
                    args: &[TermId],
                    index: usize,
                    values: &HashMap<TermId, BigInt>,
                    budget: &mut LiaModelEvalBudget,
                ) -> Option<(BigInt, u32)> {
                    eval_lia_bv_under_values_inner(terms, *args.get(index)?, values, budget)
                }
                fn same_width_operand(
                    terms: &ay_core::TermStore,
                    args: &[TermId],
                    index: usize,
                    width: u32,
                    values: &HashMap<TermId, BigInt>,
                    budget: &mut LiaModelEvalBudget,
                ) -> Option<BigInt> {
                    let (v, w) = operand(terms, args, index, values, budget)?;
                    (w == width).then_some(v)
                }
                match (sym, args.len()) {
                    // `((_ int2bv w) s)` — the residue of the Int source mod 2^w.
                    // This is the boundary the whole recovery hinges on.
                    (ay_core::term::Symbol::Indexed(name, indices), 1)
                        if name == "int2bv" && indices.len() == 1 && indices[0] == width =>
                    {
                        wrap(
                            eval_lia_int_under_values_inner(terms, args[0], values, budget)?,
                            width,
                        )
                    }
                    (ay_core::term::Symbol::Indexed(name, indices), 1)
                        if name == "extract" && indices.len() == 2 =>
                    {
                        let (high, low) = (indices[0], indices[1]);
                        if checked_bv_extract_width(high, low) != Some(width) {
                            return None;
                        }
                        let (v, source_width) = operand(terms, args, 0, values, budget)?;
                        if high >= source_width {
                            return None;
                        }
                        (v >> low as usize) & mask(width)
                    }
                    (ay_core::term::Symbol::Indexed(name, indices), 1)
                        if name == "zero_extend" && indices.len() == 1 =>
                    {
                        let (v, source_width) = operand(terms, args, 0, values, budget)?;
                        if checked_bv_width_sum(source_width, indices[0]) != Some(width) {
                            return None;
                        }
                        v
                    }
                    (ay_core::term::Symbol::Indexed(name, indices), 1)
                        if name == "sign_extend" && indices.len() == 1 =>
                    {
                        let (v, source_width) = operand(terms, args, 0, values, budget)?;
                        if checked_bv_width_sum(source_width, indices[0]) != Some(width) {
                            return None;
                        }
                        wrap(signed(&v, source_width), width)
                    }
                    (ay_core::term::Symbol::Indexed(name, indices), 1)
                        if matches!(name.as_str(), "rotate_left" | "rotate_right")
                            && indices.len() == 1 =>
                    {
                        let v = same_width_operand(terms, args, 0, width, values, budget)?;
                        let by = u64::from(indices[0] % width) as usize;
                        let left = if name == "rotate_left" {
                            by
                        } else {
                            width as usize - by
                        };
                        ((v.clone() << left) | (v >> (width as usize - left))) & mask(width)
                    }
                    (ay_core::term::Symbol::Named(name), 2) if name == "concat" => {
                        let (hi, hi_width) = operand(terms, args, 0, values, budget)?;
                        let (lo, lo_width) = operand(terms, args, 1, values, budget)?;
                        if checked_bv_width_sum(hi_width, lo_width) != Some(width) {
                            return None;
                        }
                        (hi << lo_width as usize) | lo
                    }
                    (ay_core::term::Symbol::Named(name), 1) if name == "bvnot" => {
                        !same_width_operand(terms, args, 0, width, values, budget)? & mask(width)
                    }
                    (ay_core::term::Symbol::Named(name), 1) if name == "bvneg" => wrap(
                        -same_width_operand(terms, args, 0, width, values, budget)?,
                        width,
                    ),
                    (ay_core::term::Symbol::Named(name), n)
                        if n >= 2 && matches!(name.as_str(), "bvand" | "bvor" | "bvxor") =>
                    {
                        let mut acc = same_width_operand(terms, args, 0, width, values, budget)?;
                        for i in 1..n {
                            let rhs = same_width_operand(terms, args, i, width, values, budget)?;
                            acc = match name.as_str() {
                                "bvand" => acc & rhs,
                                "bvor" => acc | rhs,
                                _ => acc ^ rhs,
                            };
                        }
                        acc & mask(width)
                    }
                    (ay_core::term::Symbol::Named(name), n)
                        if n >= 2 && matches!(name.as_str(), "bvadd" | "bvmul") =>
                    {
                        let mut acc = same_width_operand(terms, args, 0, width, values, budget)?;
                        for i in 1..n {
                            let rhs = same_width_operand(terms, args, i, width, values, budget)?;
                            acc = if name == "bvadd" {
                                acc + rhs
                            } else {
                                acc * rhs
                            };
                        }
                        wrap(acc, width)
                    }
                    (ay_core::term::Symbol::Named(name), 2) if name == "bvsub" => wrap(
                        same_width_operand(terms, args, 0, width, values, budget)?
                            - same_width_operand(terms, args, 1, width, values, budget)?,
                        width,
                    ),
                    // Shifts: SMT-LIB defines an out-of-range shift amount as a full
                    // flush (0 for the logical shifts; the sign bit for `bvashr`).
                    (ay_core::term::Symbol::Named(name), 2)
                        if matches!(name.as_str(), "bvshl" | "bvlshr" | "bvashr") =>
                    {
                        let v = same_width_operand(terms, args, 0, width, values, budget)?;
                        let by = same_width_operand(terms, args, 1, width, values, budget)?;
                        let by = by.to_u64().unwrap_or(u64::from(width));
                        if by >= u64::from(width) {
                            match name.as_str() {
                                "bvashr" if signed(&v, width).is_negative() => mask(width),
                                _ => BigInt::zero(),
                            }
                        } else {
                            let by = by as usize;
                            match name.as_str() {
                                "bvshl" => (v << by) & mask(width),
                                "bvlshr" => v >> by,
                                _ => wrap(signed(&v, width) >> by, width),
                            }
                        }
                    }
                    // Division by zero is TOTALIZED by SMT-LIB, not undefined:
                    // `bvudiv x 0 = all-ones`, `bvurem x 0 = x`.
                    (ay_core::term::Symbol::Named(name), 2)
                        if matches!(name.as_str(), "bvudiv" | "bvurem") =>
                    {
                        let a = same_width_operand(terms, args, 0, width, values, budget)?;
                        let b = same_width_operand(terms, args, 1, width, values, budget)?;
                        if b.is_zero() {
                            if name == "bvudiv" {
                                mask(width)
                            } else {
                                a
                            }
                        } else if name == "bvudiv" {
                            a / b
                        } else {
                            a % b
                        }
                    }
                    _ => return None,
                }
            }
            _ => return None,
        };

        debug_assert!(
            !value.is_negative() && value <= mask(width),
            "structural BV evaluation escaped [0, 2^width)"
        );
        Some((value, width))
    })();
    budget.leave(tid);
    result
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EqualityRecoveryAuthority {
    /// Closed arithmetic/literal expression; independent of model guesses.
    Ground,
    /// Variables and arithmetic structure, but no opaque theory application.
    NonOpaque,
    /// `select`, `default`, UF, or another Int application registered as an
    /// opaque LIA atom.
    Opaque,
}

fn equality_recovery_authority(
    terms: &ay_core::TermStore,
    root: TermId,
) -> EqualityRecoveryAuthority {
    use ay_core::term::TermData;

    match terms.get(root) {
        TermData::Const(_) => EqualityRecoveryAuthority::Ground,
        TermData::Var(_, _) => EqualityRecoveryAuthority::NonOpaque,
        TermData::Not(inner) => equality_recovery_authority(terms, *inner),
        TermData::Ite(condition, then_term, else_term) => [
            equality_recovery_authority(terms, *condition),
            equality_recovery_authority(terms, *then_term),
            equality_recovery_authority(terms, *else_term),
        ]
        .into_iter()
        .max()
        .unwrap_or(EqualityRecoveryAuthority::Ground),
        TermData::App(symbol, args) => {
            if matches!(terms.sort(root), ay_core::Sort::Int)
                && !matches!(symbol.name(), "+" | "-" | "*" | "div" | "mod" | "abs")
            {
                return EqualityRecoveryAuthority::Opaque;
            }
            args.iter()
                .map(|&arg| equality_recovery_authority(terms, arg))
                .max()
                .unwrap_or(EqualityRecoveryAuthority::Ground)
        }
        TermData::Let(_, _) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
            EqualityRecoveryAuthority::Opaque
        }
        _ => EqualityRecoveryAuthority::Opaque,
    }
}

/// Recover variable values from direct asserted equalities in the original formula.
///
/// Authority is staged so assertion order cannot let a speculative opaque atom
/// win over an exact literal.  Ground equalities are applied first (and may
/// repair a stale extracted variable value), then non-opaque arithmetic fills
/// remaining variables, and opaque `select`/`default`/UF observations are used
/// only last.  The subsequent opaque backfill therefore flows from the exact
/// variable anchor to the application, never in the opposite direction merely
/// because `(= x (default a))` appeared before `(= x 5)`.
pub(in crate::executor) fn recover_lia_equalities_from_assertions(
    terms: &ay_core::TermStore,
    assertions: &[TermId],
    model: &mut LiaModel,
) {
    use ay_core::term::TermData;

    // Collect exact ground anchors as a set before mutating the model.  This is
    // deliberately independent of assertion order.  A contradictory pair of
    // ground anchors is left unrepaired so ordinary validation exposes the
    // inconsistent candidate instead of arbitrarily choosing the last one.
    let mut ground_anchors: HashMap<TermId, Option<num_bigint::BigInt>> = HashMap::default();
    for &assertion in assertions {
        let TermData::App(symbol, args) = terms.get(assertion) else {
            continue;
        };
        if symbol.name() != "=" || args.len() != 2 {
            continue;
        }
        for &(var, expr) in &[(args[0], args[1]), (args[1], args[0])] {
            if !matches!(terms.get(var), TermData::Var(_, _))
                || !matches!(terms.sort(var), ay_core::Sort::Int)
                || equality_recovery_authority(terms, expr) != EqualityRecoveryAuthority::Ground
            {
                continue;
            }
            let Some(value) = eval_lia_int_under_values(terms, expr, &model.values) else {
                continue;
            };
            ground_anchors
                .entry(var)
                .and_modify(|anchor| {
                    if anchor.as_ref().is_some_and(|old| old != &value) {
                        *anchor = None;
                    }
                })
                .or_insert(Some(value));
        }
    }
    let mut ordered_ground_anchors: Vec<_> = ground_anchors.into_iter().collect();
    ordered_ground_anchors.sort_by_key(|(var, _)| var.index());
    let mut authoritative = HashSet::default();
    for (var, value) in ordered_ground_anchors {
        if let Some(value) = value {
            model.values.insert(var, value);
            authoritative.insert(var);
        }
    }

    fn depends_only_on_authoritative_vars(
        terms: &ay_core::TermStore,
        root: TermId,
        authoritative: &HashSet<TermId>,
    ) -> bool {
        use ay_core::term::TermData;

        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::Const(_) => {}
                TermData::Var(_, _) => {
                    if !authoritative.contains(&term) {
                        return false;
                    }
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                _ => return false,
            }
        }
        true
    }

    for authority in [
        EqualityRecoveryAuthority::NonOpaque,
        EqualityRecoveryAuthority::Opaque,
    ] {
        let max_passes = assertions.len().max(1);
        for _ in 0..max_passes {
            let mut progress = false;
            for &assertion in assertions {
                let TermData::App(sym, args) = terms.get(assertion) else {
                    continue;
                };
                if sym.name() != "=" || args.len() != 2 {
                    continue;
                }

                for &(var, expr) in &[(args[0], args[1]), (args[1], args[0])] {
                    if !matches!(terms.get(var), TermData::Var(_, _))
                        || !matches!(terms.sort(var), ay_core::Sort::Int)
                        || equality_recovery_authority(terms, expr) != authority
                    {
                        continue;
                    }
                    let Some(value) = eval_lia_int_under_values(terms, expr, &model.values) else {
                        continue;
                    };
                    let existing_matches = model.values.get(&var) == Some(&value);
                    let has_existing = model.values.contains_key(&var);
                    let exact_derived = authority == EqualityRecoveryAuthority::NonOpaque
                        && depends_only_on_authoritative_vars(terms, expr, &authoritative);
                    // Exact authority propagates through variable/arithmetic
                    // definitions and may repair a stale extracted dependent.
                    // Other sources remain fill-only so tableau assignments and
                    // opaque model choices are preserved.
                    if authoritative.contains(&var) {
                        continue;
                    }
                    if exact_derived {
                        // Even a coincidentally correct extracted value must be
                        // promoted to exact authority.  Otherwise a later
                        // dependent (`z = y + 1`) cannot distinguish that y's
                        // value is now justified and leaves stale z untouched.
                        if !existing_matches {
                            model.values.insert(var, value);
                        }
                        if authoritative.insert(var) {
                            progress = true;
                        }
                        continue;
                    }
                    if has_existing {
                        continue;
                    }
                    model.values.insert(var, value);
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }
    }
}

/// Unify uninterpreted-sort element values for top-level asserted equalities
/// (#uflia-uninterp-eq-recover).
///
/// The EUF model can assign two terms DIFFERENT sort elements even though a
/// top-level `(= x y)` asserts them equal — observed on the verification-consumer mut-ref
/// carrier `a == mk_mut_ref(a_current, a_final, a_id)` when the constructor's
/// Int args are LIA-constrained (`a_current < a_final`): extraction yields
/// `a = @S!0` but `mk(..) = @S!1`. The model's own validation gate then refutes
/// the asserted equality and degrades a genuine `sat` to `unknown`. (The AUFLIA
/// array path happens to avoid the split; the plain UFLIA path did not repair
/// it, and `reunify_lia_values_across_euf_classes` only touches Int classes.)
///
/// Repair: for each top-level asserted-equal uninterpreted-sort pair, propagate
/// one representative element to both sides of `euf_model.term_values`
/// (fill-only when one side is unvalued; overwrite the RHS when they disagree).
///
/// SOUND / fail-closed: the two sides MUST agree in any satisfying model, so
/// adopting one element for both never makes a correct model wrong; and the
/// strict validation gate re-checks EVERY assertion afterward, so a unification
/// that violates some other assertion (e.g. a disequality) simply leaves the
/// verdict degraded exactly as before — it can never admit a false `sat` (an
/// UNSAT formula has no assignment that passes all ground checks).
pub(in crate::executor) fn recover_uninterpreted_equalities_from_assertions(
    terms: &ay_core::TermStore,
    assertions: &[TermId],
    euf_model: &mut EufModel,
) {
    use ay_core::term::TermData;
    use ay_core::Sort;

    let max_passes = assertions.len().max(1);
    for _ in 0..max_passes {
        let mut progress = false;
        for &assertion in assertions {
            let TermData::App(sym, args) = terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            let (lhs, rhs) = (args[0], args[1]);
            // Only uninterpreted-sort equalities: Int/Bool/etc. have their own
            // dedicated model recovery.
            if !matches!(terms.sort(lhs), Sort::Uninterpreted(_)) {
                continue;
            }
            match (
                euf_model.term_values.get(&lhs).cloned(),
                euf_model.term_values.get(&rhs).cloned(),
            ) {
                (Some(lv), Some(rv)) if lv != rv => {
                    euf_model.term_values.insert(rhs, lv);
                    progress = true;
                }
                (Some(lv), None) => {
                    euf_model.term_values.insert(rhs, lv);
                    progress = true;
                }
                (None, Some(rv)) => {
                    euf_model.term_values.insert(lhs, rv);
                    progress = true;
                }
                _ => {}
            }
        }
        if !progress {
            break;
        }
    }
}

/// Recover model values for variables eliminated by variable substitution (#2767).
///
/// When `VariableSubstitution` replaces `result_a -> (+ self_a 1)`, the LIA model
/// only has a value for `self_a`. This function evaluates the replacement expression
/// to compute `result_a`'s value.
pub(in crate::executor) fn recover_substituted_lia_values(
    terms: &ay_core::TermStore,
    var_subst: &VariableSubstitution,
    model: &mut LiaModel,
) {
    recover_substituted_lia_values_protecting(terms, var_subst, model, &HashSet::default());
}

/// Variant of [`recover_substituted_lia_values`] that PROTECTS
/// diseq-constrained variables from the RHS-recompute overwrite
/// (#qf-auflia-subst-clobber, scoped retry of the reverted global guard).
///
/// The storecomm/storeinv element variables are BOTH substitution keys
/// (`e_17 -> (select a2 i1)`) AND live tableau variables whose values LIA
/// chose to satisfy their pairwise disequalities. Blindly re-deriving
/// `e_17 := eval(select ...)` pulls the select's completion default (0) over
/// the tableau's diseq-satisfying value, re-colliding the pair the split
/// machinery just separated — the model then violates `(not (= e_17 e_18))`
/// and the strict gate degrades a genuine `sat`. For PROTECTED vars we keep
/// the tableau value and instead push it into an opaque RHS leaf (Var or
/// select) so the substitution equality still holds. Scoping to
/// diseq-fact vars avoids the measured regression of the global variant
/// (QF_AUFLIA 400-sample 239 -> 230): ordinary eliminated vars keep the
/// RHS-recompute direction.
pub(in crate::executor) fn recover_substituted_lia_values_protecting(
    terms: &ay_core::TermStore,
    var_subst: &VariableSubstitution,
    model: &mut LiaModel,
    protected: &HashSet<TermId>,
) {
    use ay_core::term::TermData;

    // Collect leaf variables from substitution RHS expressions.
    //
    // Opaque Int-sorted array observations (`select` and `default`) are treated
    // as leaves too. When a substituted variable's RHS observes a FREE array
    // (`i2 -> (+ (select A idx) k)` or `x -> (default A)`), the observation
    // carries no LIA value and the whole recovery would otherwise fail, leaving
    // the eliminated variable to be defaulted independently of the emitted
    // array — a model whose own evaluator refutes it. Seeding the observation
    // with the same canonical value (0) used for an unconstrained array cell or
    // else-value makes recovery and array-model extraction share one authority.
    // A constrained observation already has a value and is never overwritten
    // (fill-only below); the independent model-check gate catches any residual
    // disagreement.
    fn collect_vars(terms: &ay_core::TermStore, tid: TermId, vars: &mut HashSet<TermId>) {
        match terms.get(tid) {
            TermData::Var(_, _) => {
                vars.insert(tid);
            }
            TermData::App(sym, args) => {
                if matches!(sym.name(), "select" | "default")
                    && matches!(terms.sort(tid), ay_core::Sort::Int)
                {
                    vars.insert(tid);
                }
                for &arg in args {
                    collect_vars(terms, arg, vars);
                }
            }
            TermData::Ite(cond, then_t, else_t) => {
                collect_vars(terms, *cond, vars);
                collect_vars(terms, *then_t, vars);
                collect_vars(terms, *else_t, vars);
            }
            TermData::Not(inner) => {
                collect_vars(terms, *inner, vars);
            }
            _ => {}
        }
    }

    let substituted_from: HashSet<TermId> = var_subst.substitutions().keys().copied().collect();

    // Seed default values (0) for free integer variables referenced in substitution
    // expressions but not present in the model (#3201).
    let mut rhs_vars = HashSet::default();
    for &to in var_subst.substitutions().values() {
        collect_vars(terms, to, &mut rhs_vars);
    }
    for var_tid in rhs_vars {
        if substituted_from.contains(&var_tid) {
            continue;
        }
        if matches!(terms.sort(var_tid), ay_core::Sort::Int) && !model.values.contains_key(&var_tid)
        {
            model.values.insert(var_tid, num_bigint::BigInt::from(0));
        }
    }

    // Recover Int substitutions through a dependency worklist.  A substitution
    // key can retain a speculative/stale tableau value even though its defining
    // equality was eliminated.  Letting a dependent RHS read that value makes
    // recovery order-dependent: `x -> y + 1` can commit from stale `y` before
    // `y -> z + 1` is replayed.  Keep those keys in `model.values` for the
    // fail-closed validator, but mask every unresolved key from the evaluation
    // view until its own RHS has been recovered.
    let mut substitutions: Vec<_> = var_subst
        .substitutions()
        .iter()
        .filter(|(from, _)| matches!(terms.sort(**from), ay_core::Sort::Int))
        .map(|(&from, &to)| (from, to))
        .collect();
    substitutions.sort_by_key(|(from, _)| from.index());

    let int_substitution_keys: HashSet<TermId> =
        substitutions.iter().map(|&(from, _)| from).collect();
    let mut unresolved: HashSet<TermId> = substitutions
        .iter()
        .filter_map(|&(from, _)| {
            (!protected.contains(&from) || !model.values.contains_key(&from)).then_some(from)
        })
        .collect();
    let mut eval_values = model.values.clone();
    for from in &unresolved {
        eval_values.remove(from);
    }

    fn rhs_is_opaque_int_leaf(terms: &ay_core::TermStore, term: TermId) -> bool {
        if !matches!(terms.sort(term), ay_core::Sort::Int) {
            return false;
        }
        match terms.get(term) {
            TermData::Var(_, _) => true,
            TermData::App(sym, args) => match sym.name() {
                "select" => args.len() == 2,
                "default" => args.len() == 1,
                _ => false,
            },
            _ => false,
        }
    }

    // Protected disequality variables keep their live tableau value.  Push it
    // into an opaque RHS observation before scheduling dependents; a protected
    // substitution key is already authoritative and therefore is not masked.
    for &(from, to) in &substitutions {
        if unresolved.contains(&from) {
            continue;
        }
        let Some(existing) = model.values.get(&from).cloned() else {
            continue;
        };
        if rhs_is_opaque_int_leaf(terms, to)
            && eval_lia_int_under_values(terms, to, &eval_values).as_ref() != Some(&existing)
        {
            model.values.insert(to, existing.clone());
            // If the opaque RHS is itself an unresolved substitution key, its
            // own definition remains authoritative and must resolve first.
            if !unresolved.contains(&to) {
                eval_values.insert(to, existing);
            }
        }
    }

    // Fast dynamic readiness pass.  Static dependency collection must be
    // conservative, but evaluators short-circuit (`ite true t e`, `and`/`or`).
    // Trying every RHS once under the masked view resolves definitions whose
    // value does not actually depend on a syntactically mentioned unresolved
    // key, preventing an irrelevant branch from blocking them forever.
    for &(from, to) in &substitutions {
        if !unresolved.contains(&from) {
            continue;
        }
        let Some(value) = eval_lia_int_under_values(terms, to, &eval_values) else {
            continue;
        };
        model.values.insert(from, value.clone());
        eval_values.insert(from, value);
        unresolved.remove(&from);
    }

    // Collect only dependencies that the LIA evaluator actually descends
    // through.  Other Int applications (select/default/UF) are opaque atoms
    // read by their own TermId, so dependencies in their arguments must not
    // create false cycles in this worklist.
    fn collect_eval_dependencies(
        terms: &ay_core::TermStore,
        root: TermId,
        substitution_keys: &HashSet<TermId>,
        eval_values: &HashMap<TermId, num_bigint::BigInt>,
        dependencies: &mut HashSet<TermId>,
    ) {
        let mut seen = HashSet::default();
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if substitution_keys.contains(&term) {
                dependencies.insert(term);
                continue;
            }
            match terms.get(term) {
                TermData::Ite(cond, then_term, else_term) => {
                    match eval_lia_bool_under_values(terms, *cond, eval_values) {
                        Some(true) => stack.push(*then_term),
                        Some(false) => stack.push(*else_term),
                        // Wait only for the condition.  Once its substitution
                        // dependencies resolve, the worklist re-evaluates the
                        // ITE and never waits on the unselected branch.
                        None => stack.push(*cond),
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::App(sym, args) => {
                    let evaluator_descends = match terms.sort(term) {
                        ay_core::Sort::Int => {
                            matches!(sym.name(), "+" | "-" | "*" | "div" | "mod" | "abs")
                                // `bv2nat` is decomposed by
                                // `eval_lia_bv_under_values`, so its operands'
                                // substitution keys are REAL dependencies: a
                                // definition `V -> bv2nat(((_ int2bv 64) a))`
                                // must wait for `a` to resolve, or it commits
                                // from the masked view and never retries
                                // (#bv2nat-subst-recover).
                                || sym.name() == "bv2nat"
                        }
                        ay_core::Sort::Bool => matches!(
                            sym.name(),
                            "and" | "or" | "<" | "<=" | ">" | ">=" | "=" | "distinct"
                        ),
                        // Mirror of the BV walk in `eval_lia_bv_under_values`:
                        // these are the operators it decomposes, so a
                        // substitution key underneath one is reachable.
                        ay_core::Sort::BitVec(_) => matches!(
                            sym.name(),
                            "int2bv"
                                | "extract"
                                | "zero_extend"
                                | "sign_extend"
                                | "rotate_left"
                                | "rotate_right"
                                | "concat"
                                | "bvnot"
                                | "bvneg"
                                | "bvand"
                                | "bvor"
                                | "bvxor"
                                | "bvadd"
                                | "bvmul"
                                | "bvsub"
                                | "bvshl"
                                | "bvlshr"
                                | "bvashr"
                                | "bvudiv"
                                | "bvurem"
                        ),
                        _ => false,
                    };
                    if evaluator_descends {
                        stack.extend(args.iter().copied());
                    }
                }
                _ => {}
            }
        }
    }

    let rhs_by_from: HashMap<TermId, TermId> = substitutions.iter().copied().collect();
    let mut pending_dependencies: HashMap<TermId, usize> = HashMap::default();
    let mut dependents: HashMap<TermId, Vec<TermId>> = HashMap::default();
    for &from in &unresolved {
        let to = rhs_by_from[&from];
        let mut dependencies = HashSet::default();
        collect_eval_dependencies(
            terms,
            to,
            &int_substitution_keys,
            &eval_values,
            &mut dependencies,
        );
        dependencies.retain(|dependency| unresolved.contains(dependency));
        pending_dependencies.insert(from, dependencies.len());
        for dependency in dependencies {
            dependents.entry(dependency).or_default().push(from);
        }
    }

    let mut ready: Vec<TermId> = unresolved
        .iter()
        .copied()
        .filter(|from| pending_dependencies.get(from) == Some(&0))
        .collect();
    ready.sort_by_key(|term| term.index());
    let mut ready: std::collections::VecDeque<TermId> = ready.into();

    while let Some(from) = ready.pop_front() {
        if !unresolved.contains(&from) {
            continue;
        }
        let to = rhs_by_from[&from];
        if ay_core::misc_cli_flags().debug_subst {
            eprintln!(
                "[subst-dbg] from={} protected={} has_val={:?} to={} to_data={:?}",
                from.0,
                protected.contains(&from),
                model.values.get(&from),
                to.0,
                terms.get(to)
            );
        }
        let Some(value) = eval_lia_int_under_values(terms, to, &eval_values) else {
            // An ITE whose condition was unresolved when the initial graph was
            // built can expose a NEW dependency after that condition becomes
            // concrete. Register that selected-branch dependency now. Without
            // this dynamic refresh the failed node has pending-count zero and is
            // never enqueued again when the newly exposed key resolves.
            let mut dependencies = HashSet::default();
            collect_eval_dependencies(
                terms,
                to,
                &int_substitution_keys,
                &eval_values,
                &mut dependencies,
            );
            dependencies.retain(|dependency| unresolved.contains(dependency));
            pending_dependencies.insert(from, dependencies.len());
            for dependency in dependencies {
                dependents.entry(dependency).or_default().push(from);
            }
            continue;
        };
        model.values.insert(from, value.clone());
        eval_values.insert(from, value);
        unresolved.remove(&from);

        if let Some(waiting) = dependents.get(&from) {
            for &dependent in waiting {
                let Some(pending) = pending_dependencies.get_mut(&dependent) else {
                    continue;
                };
                *pending = pending.saturating_sub(1);
                if *pending == 0 {
                    ready.push_back(dependent);
                }
            }
        }
    }
}

/// Recompute Int-sorted composite arithmetic term values from the final
/// (post-recovery) LIA variable assignment (#A1 / #8373 root cause).
///
/// In the AUFLIA path, `euf_with_int_values` assigns SPECULATIVE fresh
/// integers to equivalence classes without concrete constants. For composite
/// arithmetic terms like `(+ B1 (* R 4))` that the LIA model does not list
/// (it only lists variables and opaque select terms), the speculative EUF
/// value survives `merge_lia_values` and feeds array-model extraction
/// (`ArraySolver::extract_model` keys interpretation entries by these
/// strings). The result is an array model whose index keys are inconsistent
/// with the LIA variable assignment (observed: store keys 6/0/9 while
/// `B1 + 4*P = -3` and `B1 + 4*R = 1`).
///
/// This pass evaluates every Int-sorted arithmetic composite among
/// `candidate_terms` bottom-up from the LIA model's variable values and
/// writes the result into `model.values`, so the subsequent merge overrides
/// the speculative EUF values. Fill-and-overwrite is sound: full model
/// validation still gates acceptance (#8373 backstop).
///
/// Returns the number of terms recomputed.
pub(in crate::executor) fn recompute_composite_int_values(
    terms: &ay_core::TermStore,
    candidate_terms: &[TermId],
    model: &mut LiaModel,
) -> usize {
    use ay_core::term::TermData;

    let mut computed: Vec<(TermId, num_bigint::BigInt)> = Vec::new();
    for &tid in candidate_terms {
        if !matches!(terms.sort(tid), ay_core::Sort::Int) {
            continue;
        }
        let is_composite = match terms.get(tid) {
            TermData::App(sym, _) => matches!(sym.name(), "+" | "-" | "*" | "div" | "mod" | "abs"),
            TermData::Ite(..) => true,
            _ => false,
        };
        if !is_composite {
            continue;
        }
        if let Some(val) = eval_lia_int_under_values(terms, tid, &model.values) {
            if model.values.get(&tid) != Some(&val) {
                computed.push((tid, val));
            }
        }
    }
    let recomputed = computed.len();
    for (tid, val) in computed {
        model.values.insert(tid, val);
    }
    recomputed
}

/// Restore read congruence among opaque `select` terms in the LIA model
/// (#A1 / #8373 root cause).
///
/// AUFLIA preprocessing substitutes definitional equalities (e.g.
/// `G -> (+ B1 (* R 4))`), so the solved constraints mention
/// `(select Q (+ B1 (* R 4)))` while the ORIGINAL assertions mention
/// `(select Q G)`. Both reach the LIA solver as independent opaque
/// variables (the original form via array-axiom instantiation). After
/// `recover_substituted_lia_values` reassigns the substituted index variable
/// (G := 1), the two selects denote the SAME array read, but the LIA model
/// may carry DIFFERENT values for them (the original form's value was chosen
/// while G was unconstrained). Model completion then replays
/// `H -> (select Q G)` with the stale value and constructs a model that
/// violates its own assertions → #8373 degrade to Unknown.
///
/// This pass groups select terms in `model.values` by
/// `(array argument, index VALUE under the final assignment)` and, when the
/// group's values disagree, overwrites stale members with the value of a
/// member whose index term mentions no substituted variable (the
/// solved-form select, which carries the constraints the solver actually
/// enforced). Groups without a solved-form witness are left untouched —
/// validation degrades exactly as before (sound).
///
/// `euf` (#A1 chain member): the PRE-substitution select (`(select Q G)`)
/// often has NO LIA per-term value at all — it reaches the model only as a
/// speculative EUF class string — so the LIA-only grouping never saw the
/// stale member and the pre-/post-substitution reads stayed incongruent
/// (observed: committed 0 vs -3 for one `(Q, 1)` cell, which fails the
/// read-congruence materialization check and degrades a genuine `sat` to
/// unknown, escalating into the diverging axiom-expanded re-solve). Passing
/// the EUF view lets those reads join their congruence group; reconciled
/// values are written into the LIA model, which the subsequent merge and
/// array extraction treat as authoritative. Candidate-model repair only —
/// every validation gate still decides acceptance afterwards.
///
/// Returns the number of select values rewritten.
pub(in crate::executor) fn reconcile_lia_select_congruence(
    terms: &ay_core::TermStore,
    var_subst: &VariableSubstitution,
    model: &mut LiaModel,
    euf: Option<&EufModel>,
) -> usize {
    use ay_core::term::TermData;

    let subst_keys: HashSet<TermId> = var_subst.substitutions().keys().copied().collect();
    if subst_keys.is_empty() {
        return 0;
    }

    /// Parse an EUF term-value string as an integer (`"7"` or `"(- 7)"`).
    fn parse_int_string(s: &str) -> Option<num_bigint::BigInt> {
        let t = s.trim();
        if let Some(inner) = t.strip_prefix("(-").and_then(|r| r.strip_suffix(')')) {
            return inner.trim().parse::<num_bigint::BigInt>().ok().map(|n| -n);
        }
        t.parse::<num_bigint::BigInt>().ok()
    }

    fn mentions_any(
        terms: &ay_core::TermStore,
        tid: TermId,
        keys: &HashSet<TermId>,
        seen: &mut HashSet<TermId>,
    ) -> bool {
        if !seen.insert(tid) {
            return false;
        }
        if keys.contains(&tid) {
            return true;
        }
        match terms.get(tid) {
            TermData::App(_, args) => args.iter().any(|&a| mentions_any(terms, a, keys, seen)),
            TermData::Not(inner) => mentions_any(terms, *inner, keys, seen),
            TermData::Ite(c, t, e) => {
                mentions_any(terms, *c, keys, seen)
                    || mentions_any(terms, *t, keys, seen)
                    || mentions_any(terms, *e, keys, seen)
            }
            _ => false,
        }
    }

    // Collect select terms with a committed value: from the LIA model, and —
    // when the EUF view is provided — Int-sorted selects whose only committed
    // value is an EUF class string that parses as an integer (#A1 chain).
    // `sel_values` is each member's CURRENT committed value.
    let mut sel_values: HashMap<TermId, num_bigint::BigInt> = HashMap::default();
    let mut selects: Vec<(TermId, TermId, TermId)> = model
        .values
        .keys()
        .filter_map(|&t| match terms.get(t) {
            TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                Some((t, args[0], args[1]))
            }
            _ => None,
        })
        .collect();
    for &(sel, _, _) in &selects {
        sel_values.insert(sel, model.values[&sel].clone());
    }
    if let Some(euf) = euf {
        let n_terms = terms.len() as u32;
        let mut euf_selects: Vec<(TermId, TermId, TermId)> = euf
            .term_values
            .iter()
            .filter_map(|(&t, s)| {
                // Sentinel keys (e.g. the per-model repair marker at
                // `u32::MAX - 7`) live in `term_values` but are not real
                // terms — keep only ids the term store can resolve.
                if t.0 >= n_terms {
                    return None;
                }
                if sel_values.contains_key(&t) {
                    return None;
                }
                if !matches!(terms.sort(t), ay_core::Sort::Int) {
                    return None;
                }
                match terms.get(t) {
                    TermData::App(sym, args) if sym.name() == "select" && args.len() == 2 => {
                        let v = parse_int_string(s)?;
                        sel_values.insert(t, v);
                        Some((t, args[0], args[1]))
                    }
                    _ => None,
                }
            })
            .collect();
        // Deterministic order regardless of EUF map iteration.
        euf_selects.sort_unstable();
        selects.extend(euf_selects);
    }
    if selects.len() < 2 {
        return 0;
    }

    // Group by (array term, concrete index value under the final assignment).
    let mut groups: HashMap<(TermId, num_bigint::BigInt), Vec<(TermId, TermId)>> =
        HashMap::default();
    for (sel, array, index) in selects {
        let Some(idx_val) = eval_lia_int_under_values(terms, index, &model.values) else {
            continue;
        };
        groups
            .entry((array, idx_val))
            .or_default()
            .push((sel, index));
    }

    let mut rewritten = 0usize;
    for members in groups.values() {
        if members.len() < 2 {
            continue;
        }
        let values: Vec<&num_bigint::BigInt> =
            members.iter().map(|(sel, _)| &sel_values[sel]).collect();
        if values.windows(2).all(|w| w[0] == w[1]) {
            continue; // already congruent
        }
        // Prefer the value of a solved-form member (index mentions no
        // substituted variable). If solved-form members disagree among
        // themselves, leave the group alone (validation backstop).
        //
        // Internal witness-index reads (`__ay_arr2lia_wit_*`,
        // `__ay_ext_diff_*`: solver-minted extensionality/bridge skolems)
        // never carry authority:
        // class-merge repairs can MOVE the witness variable onto a program
        // cell AFTER its read value was committed for a different cell, so
        // the stale witness read would otherwise veto (solved-form conflict)
        // or overwrite the genuinely constrained program read (#A1 chain).
        // They still RECEIVE the group's reconciled value below.
        let index_is_internal_witness = |index: TermId| match terms.get(index) {
            TermData::Var(name, _) => name.starts_with("__ay_"),
            _ => false,
        };
        let mut preferred: Option<num_bigint::BigInt> = None;
        let mut solved_conflict = false;
        for (sel, index) in members {
            if index_is_internal_witness(*index) {
                continue;
            }
            let mut seen = HashSet::default();
            if !mentions_any(terms, *index, &subst_keys, &mut seen) {
                match &preferred {
                    None => preferred = Some(sel_values[sel].clone()),
                    Some(p) if p != &sel_values[sel] => {
                        solved_conflict = true;
                        break;
                    }
                    Some(_) => {}
                }
            }
        }
        if solved_conflict {
            continue;
        }
        let Some(preferred) = preferred else { continue };
        for (sel, _) in members {
            if sel_values[sel] != preferred {
                // Write into the LIA model even for EUF-sourced members: the
                // LIA value is what the merge / array extraction treat as
                // authoritative, so the congruent value reaches every view.
                model.values.insert(*sel, preferred.clone());
                rewritten += 1;
            }
        }
    }
    if rewritten > 0 {
        tracing::debug!(
            rewritten,
            "reconciled stale opaque select values to solved-form congruence (#A1)"
        );
    }
    rewritten
}

/// Backfill OPAQUE application values from their asserted defining equalities
/// (#qf-auflia-select-backfill).
///
/// The `_pp_` skolemized-extensionality benchmarks pin element variables via
/// `(= e_i (select A j))` facts. LIA values the VARIABLE (it carries the
/// disequality constraints) while the opaque select keeps a registration
/// default — the materialized model then violates the very equality that
/// defined it, and validation degrades a genuine `sat`. The asserted equality
/// IS the trustworthy oracle (extraction-time e-graph find() merges by
/// speculative value and cannot be used — observed one 60-member blob):
/// copy the LIA-valued variable's value onto the opaque application side.
/// Fill-and-overwrite on the APP side only; variables are never touched.
pub(in crate::executor) fn backfill_opaque_app_values_from_equalities(
    terms: &ay_core::TermStore,
    assertions: &[TermId],
    model: &mut LiaModel,
) -> usize {
    use ay_core::term::TermData;
    let is_opaque_app = |t: TermId| match terms.get(t) {
        TermData::App(sym, _) => {
            matches!(terms.sort(t), ay_core::Sort::Int)
                && !matches!(
                    sym.name(),
                    "+" | "-" | "*" | "div" | "mod" | "abs" | "ite" | "to_int" | "to_real"
                )
        }
        _ => false,
    };
    let mut rewritten = 0usize;
    for &a in assertions {
        let TermData::App(sym, args) = terms.get(a) else {
            continue;
        };
        if sym.name() != "=" || args.len() != 2 {
            continue;
        }
        for &(var, app) in &[(args[0], args[1]), (args[1], args[0])] {
            if !matches!(terms.get(var), TermData::Var(_, _)) || !is_opaque_app(app) {
                continue;
            }
            let Some(val) = model.values.get(&var).cloned() else {
                continue;
            };
            if model.values.get(&app) != Some(&val) {
                if ay_core::misc_cli_flags().debug_subst {
                    eprintln!("[backfill-dbg] var={} -> app={} val={val}", var.0, app.0);
                }
                model.values.insert(app, val);
                rewritten += 1;
            }
        }
    }
    if ay_core::misc_cli_flags().debug_subst {
        eprintln!(
            "[backfill-dbg] assertions={} rewritten={rewritten}",
            assertions.len()
        );
    }
    rewritten
}

/// Recover Bool variable values eliminated by `VariableSubstitution`.
///
/// When `VariableSubstitution` replaces a Bool variable (e.g., `p -> (> x 0)`),
/// the SAT model has no assignment for `p`. This function evaluates the
/// substitution RHS expression using the LIA model values and returns a map
/// of recovered Bool variable values that can be stored in `Model.bool_overrides`.
pub(in crate::executor) fn recover_substituted_bool_values(
    terms: &ay_core::TermStore,
    var_subst: &VariableSubstitution,
    lia_values: &HashMap<TermId, num_bigint::BigInt>,
) -> HashMap<TermId, bool> {
    let mut bool_overrides = HashMap::default();

    for (&from, &to) in var_subst.substitutions() {
        // Only recover Bool-sorted substituted variables.
        if !matches!(terms.sort(from), ay_core::Sort::Bool) {
            continue;
        }
        if let Some(val) = eval_lia_bool_under_values(terms, to, lia_values) {
            bool_overrides.insert(from, val);
        }
    }

    bool_overrides
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Sort, TermStore};

    #[test]
    fn substituted_int_array_default_seeds_one_shared_value() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let default = terms.mk_array_default(array);
        let x = terms.mk_var("x", Sort::Int);
        let var_subst = VariableSubstitution::from_recorded_map(HashMap::from_iter([(x, default)]));
        let mut model = LiaModel {
            values: HashMap::default(),
        };

        recover_substituted_lia_values(&terms, &var_subst, &mut model);

        let zero = num_bigint::BigInt::from(0);
        assert_eq!(model.values.get(&default), Some(&zero));
        assert_eq!(model.values.get(&x), Some(&zero));
    }

    #[test]
    fn exact_equality_anchor_precedes_opaque_default_in_both_orders() {
        for opaque_first in [false, true] {
            let mut terms = TermStore::new();
            let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
            let default = terms.mk_array_default(array);
            let x = terms.mk_var("x", Sort::Int);
            let five = terms.mk_int(num_bigint::BigInt::from(5));
            let x_default = terms.mk_eq(x, default);
            let x_five = terms.mk_eq(x, five);
            let assertions = if opaque_first {
                vec![x_default, x_five]
            } else {
                vec![x_five, x_default]
            };
            let mut values = HashMap::default();
            // Both entries model the stale extraction shape: the opaque atom
            // was defaulted and even x may already carry that guess.
            values.insert(default, num_bigint::BigInt::from(0));
            values.insert(x, num_bigint::BigInt::from(0));
            let mut model = LiaModel { values };

            recover_lia_equalities_from_assertions(&terms, &assertions, &mut model);
            backfill_opaque_app_values_from_equalities(&terms, &assertions, &mut model);

            let expected = num_bigint::BigInt::from(5);
            assert_eq!(model.values.get(&x), Some(&expected));
            assert_eq!(model.values.get(&default), Some(&expected));
        }
    }

    #[test]
    fn exact_equality_authority_propagates_through_stale_dependents() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let one = terms.mk_int(num_bigint::BigInt::from(1));
        let five = terms.mk_int(num_bigint::BigInt::from(5));
        let x_five = terms.mk_eq(x, five);
        let y_x = terms.mk_eq(y, x);
        let y_plus_one = terms.mk_add(vec![y, one]);
        let z_y_plus_one = terms.mk_eq(z, y_plus_one);
        let mut values = HashMap::default();
        values.insert(x, num_bigint::BigInt::from(0));
        // y already happens to have the right value, but is not authoritative
        // until `y = x` is recovered from authoritative x.
        values.insert(y, num_bigint::BigInt::from(5));
        values.insert(z, num_bigint::BigInt::from(0));
        let mut model = LiaModel { values };

        recover_lia_equalities_from_assertions(&terms, &[z_y_plus_one, y_x, x_five], &mut model);

        assert_eq!(model.values.get(&x), Some(&num_bigint::BigInt::from(5)));
        assert_eq!(model.values.get(&y), Some(&num_bigint::BigInt::from(5)));
        assert_eq!(model.values.get(&z), Some(&num_bigint::BigInt::from(6)));
    }

    #[test]
    fn substituted_int_chain_masks_stale_unresolved_dependency() {
        let mut terms = TermStore::new();
        let seed = terms.mk_var("seed", Sort::Int);
        let one = terms.mk_int(num_bigint::BigInt::from(1));
        let zero = terms.mk_int(num_bigint::BigInt::from(0));
        let keys: Vec<TermId> = (0..12)
            .map(|index| terms.mk_var(format!("x_{index}"), Sort::Int))
            .collect();

        // Pick the first and last keys in the map's actual iteration order so
        // the old one-pass-removal behavior deterministically evaluated the
        // dependent from a stale intermediate before repairing that
        // intermediate.  Keeping all keys in the map preserves that order for
        // both the normal deterministic hash map and Kani's BTreeMap alias.
        let mut substitutions: HashMap<TermId, TermId> =
            keys.iter().copied().map(|key| (key, zero)).collect();
        let order: Vec<TermId> = substitutions.keys().copied().collect();
        let dependent = order[0];
        let dependency = *order.last().expect("non-empty substitution map");
        let dependency_rhs = terms.mk_add(vec![seed, one]);
        let dependent_rhs = terms.mk_add(vec![dependency, one]);
        substitutions.insert(dependent, dependent_rhs);
        substitutions.insert(dependency, dependency_rhs);

        let var_subst = VariableSubstitution::from_recorded_map(substitutions);
        let mut values = HashMap::default();
        values.insert(seed, num_bigint::BigInt::from(5));
        values.insert(dependency, num_bigint::BigInt::from(100));
        values.insert(dependent, num_bigint::BigInt::from(200));
        let mut model = LiaModel { values };

        recover_substituted_lia_values(&terms, &var_subst, &mut model);

        assert_eq!(
            model.values.get(&dependency),
            Some(&num_bigint::BigInt::from(6))
        );
        assert_eq!(
            model.values.get(&dependent),
            Some(&num_bigint::BigInt::from(7)),
            "dependent recovery must wait for the dependency's defining RHS"
        );
    }

    #[test]
    fn substituted_ite_does_not_wait_for_unselected_unresolved_branch() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let opaque = terms.mk_app(
            ay_core::Symbol::named("opaque"),
            Vec::<TermId>::new(),
            Sort::Int,
        );
        let seven = terms.mk_int(num_bigint::BigInt::from(7));
        let condition = terms.mk_bool(true);
        let choose_seven = terms.mk_ite(condition, seven, y);
        let var_subst = VariableSubstitution::from_recorded_map(HashMap::from_iter([
            (x, choose_seven),
            (y, opaque),
        ]));
        let mut model = LiaModel {
            values: HashMap::default(),
        };

        recover_substituted_lia_values(&terms, &var_subst, &mut model);

        assert_eq!(model.values.get(&x), Some(&num_bigint::BigInt::from(7)));
        assert!(!model.values.contains_key(&y));
    }

    #[test]
    fn substituted_ite_registers_branch_dependency_after_condition_resolves() {
        let mut terms = TermStore::new();
        // TermId order is intentional.  The one-shot readiness pass leaves c
        // and w ready; resolving c enqueues x before resolving w enqueues y.
        // Thus x observes the now-true condition while y is still masked and
        // must dynamically register y as its newly selected dependency.
        let x = terms.mk_var("x", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let w = terms.mk_var("w", Sort::Int);
        let u = terms.mk_var("u", Sort::Int);
        let one = terms.mk_int(num_bigint::BigInt::from(1));
        let nine = terms.mk_int(num_bigint::BigInt::from(9));
        let condition = terms.mk_eq(c, one);
        let choose_y = terms.mk_ite(condition, y, one);
        let var_subst = VariableSubstitution::from_recorded_map(HashMap::from_iter([
            (x, choose_y),
            (c, z),
            (y, w),
            (z, one),
            (w, u),
            (u, nine),
        ]));
        let mut model = LiaModel {
            values: HashMap::default(),
        };

        recover_substituted_lia_values(&terms, &var_subst, &mut model);

        assert_eq!(model.values.get(&c), Some(&num_bigint::BigInt::from(1)));
        assert_eq!(model.values.get(&y), Some(&num_bigint::BigInt::from(9)));
        assert_eq!(model.values.get(&x), Some(&num_bigint::BigInt::from(9)));
    }

    #[test]
    fn lia_bool_short_circuit_is_order_independent_with_unknown_operand() {
        let mut terms = TermStore::new();
        let missing = terms.mk_var("missing", Sort::Int);
        let zero = terms.mk_int(num_bigint::BigInt::from(0));
        let unknown = terms.mk_eq(missing, zero);
        let false_term = terms.mk_bool(false);
        let true_term = terms.mk_bool(true);
        let values = HashMap::default();

        for args in [[unknown, false_term], [false_term, unknown]] {
            let conjunction = terms.mk_app(ay_core::Symbol::named("and"), args, Sort::Bool);
            assert_eq!(
                eval_lia_bool_under_values(&terms, conjunction, &values),
                Some(false)
            );
        }
        for args in [[unknown, true_term], [true_term, unknown]] {
            let disjunction = terms.mk_app(ay_core::Symbol::named("or"), args, Sort::Bool);
            assert_eq!(
                eval_lia_bool_under_values(&terms, disjunction, &values),
                Some(true)
            );
        }
    }

    #[test]
    fn bv2nat_int2bv_round_trip_shares_one_depth_budget() {
        let mut terms = TermStore::new();
        let source = terms.mk_var("source", Sort::Int);
        let as_bv = terms.mk_int2bv(8, source);
        let round_trip = terms.mk_bv2nat(as_bv);
        let values = HashMap::from_iter([(source, num_bigint::BigInt::from(5))]);

        assert_eq!(
            eval_lia_int_under_values(&terms, round_trip, &values),
            Some(num_bigint::BigInt::from(5))
        );

        // Int(bv2nat) -> BV(int2bv) -> Int(source) is three frames. A
        // per-sort budget would reset at each bridge and incorrectly succeed.
        let mut budget = LiaModelEvalBudget::limited(100, 2);
        assert_eq!(
            eval_lia_int_under_values_inner(&terms, round_trip, &values, &mut budget),
            None
        );
        assert_eq!(budget.depth, 0);
        assert!(budget.active.is_empty());
    }

    #[test]
    fn lia_model_evaluation_work_budget_is_fail_closed() {
        let mut terms = TermStore::new();
        let vars: Vec<_> = (0..4)
            .map(|index| terms.mk_var(format!("work_{index}"), Sort::Int))
            .collect();
        let sum = terms.mk_add(vars.clone());
        let values = HashMap::from_iter(
            vars.iter()
                .copied()
                .enumerate()
                .map(|(index, term)| (term, num_bigint::BigInt::from(index + 1))),
        );

        assert_eq!(
            eval_lia_int_under_values(&terms, sum, &values),
            Some(num_bigint::BigInt::from(10))
        );
        // The root plus four leaves needs five units of work.
        let mut budget = LiaModelEvalBudget::limited(4, 32);
        assert_eq!(
            eval_lia_int_under_values_inner(&terms, sum, &values, &mut budget),
            None
        );
        assert_eq!(budget.depth, 0);
        assert!(budget.active.is_empty());
    }

    #[test]
    fn lia_model_evaluation_cycle_guard_is_balanced() {
        let mut terms = TermStore::new();
        let term = terms.mk_var("cycle", Sort::Int);
        let mut budget = LiaModelEvalBudget::limited(3, 3);

        assert!(budget.enter(term));
        assert!(!budget.enter(term), "an active TermId must not re-enter");
        budget.leave(term);
        assert!(budget.enter(term), "leaving restores the active-path guard");
        budget.leave(term);
        assert_eq!(budget.depth, 0);
        assert!(budget.active.is_empty());
    }

    #[test]
    fn malformed_bv_width_arithmetic_returns_none_without_overflow() {
        let mut terms = TermStore::new();
        let source = terms.mk_bitvec(num_bigint::BigInt::from(1), 8);
        let malformed_extract = terms.mk_app(
            ay_core::Symbol::indexed("extract", vec![u32::MAX, 0]),
            [source],
            Sort::bitvec(1),
        );
        let malformed_zero_extend = terms.mk_app(
            ay_core::Symbol::indexed("zero_extend", vec![u32::MAX]),
            [source],
            Sort::bitvec(8),
        );
        let malformed_sign_extend = terms.mk_app(
            ay_core::Symbol::indexed("sign_extend", vec![u32::MAX]),
            [source],
            Sort::bitvec(8),
        );
        let values = HashMap::default();

        for malformed in [
            malformed_extract,
            malformed_zero_extend,
            malformed_sign_extend,
        ] {
            let mut budget = LiaModelEvalBudget::new();
            assert_eq!(
                eval_lia_bv_under_values_inner(&terms, malformed, &values, &mut budget),
                None
            );
            assert_eq!(budget.depth, 0);
            assert!(budget.active.is_empty());
        }

        assert_eq!(checked_bv_extract_width(u32::MAX, 0), None);
        assert_eq!(checked_bv_width_sum(u32::MAX, 1), None);
    }

    #[test]
    fn bv_ite_with_bv_equality_condition_remains_outside_recovery_scope() {
        let mut terms = TermStore::new();
        let left_int = terms.mk_var("left_int", Sort::Int);
        let right_int = terms.mk_var("right_int", Sort::Int);
        let left = terms.mk_int2bv(8, left_int);
        let right = terms.mk_int2bv(8, right_int);
        let condition = terms.mk_eq(left, right);
        let one = terms.mk_bitvec(num_bigint::BigInt::from(1), 8);
        let two = terms.mk_bitvec(num_bigint::BigInt::from(2), 8);
        let choice = terms.mk_ite(condition, one, two);
        let values = HashMap::from_iter([
            (left_int, num_bigint::BigInt::from(7)),
            (right_int, num_bigint::BigInt::from(7)),
        ]);
        let mut budget = LiaModelEvalBudget::new();

        // The recovery evaluator deliberately has no independent BV-relation
        // lane. It must decline this condition instead of borrowing the
        // producer's bitvector comparison authority.
        assert_eq!(
            eval_lia_bv_under_values_inner(&terms, choice, &values, &mut budget),
            None
        );
        assert_eq!(budget.depth, 0);
        assert!(budget.active.is_empty());
    }
}
