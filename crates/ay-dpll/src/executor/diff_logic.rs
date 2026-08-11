// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Phase 5 difference-logic routing: an opt-in, fail-closed pre-check that hands
//! *pure* QF_IDL / QF_RDL instances to the standalone, self-certifying
//! [`ay_diff_logic`] Bellman-Ford engine.
//!
//! # Safety contract (load-bearing)
//!
//! - **Default OFF.** The whole path is gated on `(set-option :ay-diff-logic
//!   true)`. When the option is absent or false, [`Executor::try_diff_logic`]
//!   returns `Ok(None)` *before touching any state*, so behavior is byte-identical
//!   to today. This is the primary soundness property.
//! - **Fail-closed routing.** We only run the engine when *every* hard assertion
//!   is a single pure difference-logic atom (`x − y ⋈ c`, `x ⋈ c`, or a `not` of
//!   one). The moment any assertion is not such an atom — boolean structure,
//!   three+ variables, non-unit coefficients, mixed Int/Real, etc. — we return
//!   `Ok(None)` and the normal solver runs. The conjunctive engine has no boolean
//!   reasoning, so we never feed it anything but a conjunction of atoms.
//! - **Self-cert + fall-through.** The engine self-certifies every verdict with
//!   always-on `debug_assert!`s (SAT model substituted back into each stored
//!   constraint; UNSAT cycle re-walked and confirmed negative). If it ever
//!   `Rejected`s an atom we thought was pure (it must not, but we never assume),
//!   we fall through to the normal solver.
//!
//! The result is mapped into the executor's [`Model`] so `(get-value)` /
//! `(get-model)` work: an IDL model populates [`LiaModel`], an RDL model
//! populates [`LraModel`], each keyed by the variable's `TermId`.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData, TermStore};
use ay_core::{Sort, TermId};
use ay_diff_logic::atom::Op;
use ay_diff_logic::{solve_int_atoms, solve_rational_atoms, BuildResult, DiffAtom};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::model::Model;
use super::Executor;
use crate::executor_types::{Result, SolveResult};

/// A single atom collected from one top-level assertion, in a sort-agnostic
/// rational normal form (`lhs − rhs ⋈ c`, with `rhs = None` for var-vs-const).
/// Coefficients have already been validated to be exactly unit / opposite-unit.
///
/// Shared with the DPLL(T) difference-logic theory solver
/// ([`super::dl_theory`]), which reuses the SAME fail-closed recognition
/// routines below rather than re-deriving them.
pub(super) struct CollectedAtom {
    pub(super) lhs: TermId,
    pub(super) rhs: Option<TermId>,
    pub(super) op: Op,
    /// Constant `c` as an exact rational (integer when the sort is Int).
    pub(super) c: BigRational,
}

/// Negate a comparison operator (used for `not (atom)`).
pub(super) fn negate_op(op: Op) -> Op {
    match op {
        Op::Le => Op::Gt,
        Op::Lt => Op::Ge,
        Op::Ge => Op::Lt,
        Op::Gt => Op::Le,
        // `not (a = b)` is `a != b`, which is a *disjunction* (`a < b ∨ a > b`),
        // NOT a difference-logic atom. Handled by the caller (it rejects).
        Op::Eq => Op::Eq,
    }
}

impl Executor {
    /// Phase 5 entry point: if `:ay-diff-logic` is ON and every hard assertion is
    /// a pure difference-logic atom, decide the instance with the standalone
    /// [`ay_diff_logic`] engine and return its (self-certified) verdict.
    ///
    /// Returns:
    /// - `Ok(None)` — the option is OFF, or the instance is not pure DL, or the
    ///   engine declined (`Rejected`). In every such case the caller MUST fall
    ///   through to the normal solver; no executor state has been mutated except,
    ///   on an accepted SAT, `last_model` (set only on the `Some(Sat)` path).
    /// - `Ok(Some(Sat))` / `Ok(Some(Unsat))` — the engine decided. For SAT,
    ///   `last_model` / `last_model_validated` have been populated.
    pub(super) fn try_diff_logic(&mut self) -> Result<Option<SolveResult>> {
        // Default-OFF gate. This is the load-bearing safety property: when the
        // option is not explicitly `true`, return before touching ANY state.
        if !matches!(
            self.ctx.get_option("ay-diff-logic"),
            Some(ay_frontend::OptionValue::Bool(true))
        ) {
            return Ok(None);
        }

        // Collect one atom per top-level assertion. Any non-DL assertion aborts
        // the whole pre-check (fail-closed) — we never approximate.
        let assertions: Vec<TermId> = self.ctx.assertions.clone();
        if assertions.is_empty() {
            // Empty conjunction is trivially SAT, but let the normal (already
            // correct) empty-assertions fast path handle it to stay minimal.
            return Ok(None);
        }

        let mut collected: Vec<CollectedAtom> = Vec::with_capacity(assertions.len());
        for &a in &assertions {
            match self.collect_dl_atom(a) {
                Some(atom) => collected.push(atom),
                None => return Ok(None), // not pure DL — fall through
            }
        }

        // Decide the sort uniformly: every variable must be Int (→ IDL) or every
        // variable must be Real (→ RDL). Mixed or unknown ⇒ fall through.
        let Some(is_int) = self.dl_sort_is_int(&collected) else {
            return Ok(None);
        };

        // Assign a dense `0..n` index to each distinct variable `TermId`.
        let mut index_of: HashMap<TermId, usize> = HashMap::default();
        let mut var_terms: Vec<TermId> = Vec::new();
        let mut intern = |t: TermId, index_of: &mut HashMap<TermId, usize>| -> usize {
            if let Some(&i) = index_of.get(&t) {
                i
            } else {
                let i = var_terms.len();
                index_of.insert(t, i);
                var_terms.push(t);
                i
            }
        };

        if is_int {
            let mut atoms: Vec<DiffAtom<BigInt>> = Vec::with_capacity(collected.len());
            for ca in &collected {
                // The constant is an integer here (validated by dl_sort_is_int).
                debug_assert!(ca.c.is_integer(), "IDL atom with non-integer constant");
                let c = ca.c.to_integer();
                let lhs = intern(ca.lhs, &mut index_of);
                let rhs = ca.rhs.map(|r| intern(r, &mut index_of));
                atoms.push(match rhs {
                    Some(y) => DiffAtom::diff(lhs, y, ca.op, c),
                    None => DiffAtom::var_const(lhs, ca.op, c),
                });
            }
            match solve_int_atoms(&atoms) {
                BuildResult::Sat { model } => {
                    let values: HashMap<TermId, BigInt> =
                        var_terms.iter().zip(model).map(|(&t, v)| (t, v)).collect();
                    self.install_idl_model(values);
                    Ok(Some(SolveResult::Sat))
                }
                BuildResult::Unsat { .. } => Ok(Some(SolveResult::unsat())),
                // Should not happen (we only build pure-DL atoms), but never
                // assume: fall through to the normal solver.
                BuildResult::Rejected => Ok(None),
            }
        } else {
            let mut atoms: Vec<DiffAtom<BigRational>> = Vec::with_capacity(collected.len());
            for ca in &collected {
                let lhs = intern(ca.lhs, &mut index_of);
                let rhs = ca.rhs.map(|r| intern(r, &mut index_of));
                atoms.push(match rhs {
                    Some(y) => DiffAtom::diff(lhs, y, ca.op, ca.c.clone()),
                    None => DiffAtom::var_const(lhs, ca.op, ca.c.clone()),
                });
            }
            match solve_rational_atoms(&atoms) {
                BuildResult::Sat { model } => {
                    let values: HashMap<TermId, BigRational> =
                        var_terms.iter().zip(model).map(|(&t, v)| (t, v)).collect();
                    self.install_rdl_model(values);
                    Ok(Some(SolveResult::Sat))
                }
                BuildResult::Unsat { .. } => Ok(Some(SolveResult::unsat())),
                BuildResult::Rejected => Ok(None),
            }
        }
    }

    /// Decide whether the collected atoms are all-Int (→ IDL) or all-Real
    /// (→ RDL). Returns `None` (fall through) on a mix, on a non-arith sort, or
    /// when an Int atom carries a non-integer constant.
    fn dl_sort_is_int(&self, atoms: &[CollectedAtom]) -> Option<bool> {
        let mut saw_int = false;
        let mut saw_real = false;
        for ca in atoms {
            for &v in std::iter::once(&ca.lhs).chain(ca.rhs.as_ref()) {
                match self.ctx.terms.sort(v) {
                    Sort::Int => saw_int = true,
                    Sort::Real => saw_real = true,
                    _ => return None,
                }
            }
        }
        match (saw_int, saw_real) {
            (true, false) => {
                // Every Int atom's constant must be an integer (parsing already
                // produced exact rationals; a fractional one means the constant
                // came from `/` over reals and this is not really IDL).
                if atoms.iter().all(|a| a.c.is_integer()) {
                    Some(true)
                } else {
                    None
                }
            }
            (false, true) => Some(false),
            // No arith vars (e.g. all var-vs-const got folded away) or a mix:
            // fall through to the normal solver.
            _ => None,
        }
    }

    /// Parse one top-level assertion into a single difference-logic atom, or
    /// `None` if it is not a pure DL atom. Thin delegator to the free function
    /// [`collect_dl_atom`], which the DPLL(T) theory solver shares.
    fn collect_dl_atom(&self, term: TermId) -> Option<CollectedAtom> {
        collect_dl_atom(&self.ctx.terms, term)
    }

    /// Install an IDL model into `last_model` so `(get-value)`/`(get-model)` work.
    ///
    /// We deliberately do NOT set `last_model_validated`: leaving it `false` makes
    /// the check-sat boundary run the executor's own independent, always-on (not
    /// debug-only) model validation (`finalize_sat_model_validation`), which
    /// re-evaluates every assertion against this model and degrades SAT to Unknown
    /// on any violation. That is a second safety net on top of the diff-logic
    /// engine's own self-certification — soundness over completeness.
    fn install_idl_model(&mut self, values: HashMap<TermId, BigInt>) {
        self.last_model = Some(empty_model_with(Some(ay_lia::LiaModel { values }), None));
    }

    /// Install an RDL model into `last_model`. See [`Self::install_idl_model`] for
    /// why `last_model_validated` is intentionally left `false`.
    fn install_rdl_model(&mut self, values: HashMap<TermId, BigRational>) {
        self.last_model = Some(empty_model_with(None, Some(ay_lra::LraModel { values })));
    }
}

/// Parse one top-level assertion into a single difference-logic atom, or
/// `None` if it is not a pure DL atom. Handles `not (atom)` by negating the
/// operator; `not (= ..)` is rejected (it is a disjunction, not a DL atom).
pub(super) fn collect_dl_atom(terms: &TermStore, term: TermId) -> Option<CollectedAtom> {
    match terms.get(term) {
        TermData::Not(inner) => {
            let atom = collect_comparison(terms, *inner)?;
            if matches!(atom.op, Op::Eq) {
                // not (a = b) is a != b, a disjunction — not DL.
                return None;
            }
            Some(CollectedAtom {
                op: negate_op(atom.op),
                ..atom
            })
        }
        _ => collect_comparison(terms, term),
    }
}

/// Parse a comparison application `(op A B)` (op ∈ {<,<=,=,>,>=}) into a
/// normalized DL atom by linearizing `A − B`.
pub(super) fn collect_comparison(terms: &TermStore, term: TermId) -> Option<CollectedAtom> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let op = match name.as_str() {
        "<=" => Op::Le,
        "<" => Op::Lt,
        "=" => Op::Eq,
        ">=" => Op::Ge,
        ">" => Op::Gt,
        _ => return None,
    };
    let (a, b) = (args[0], args[1]);
    // `=` is only a difference atom when both sides are arithmetic (Int/Real).
    // A Bool `(= p q)` must NOT be treated as a DL atom.
    if !matches!(terms.sort(a), Sort::Int | Sort::Real)
        || !matches!(terms.sort(b), Sort::Int | Sort::Real)
    {
        return None;
    }

    // Linearize A − B into a coefficient map plus a constant. `A op B` is then
    // `(A − B) op 0`, i.e. (vars) op (−const).
    let mut coeffs: HashMap<TermId, BigRational> = HashMap::default();
    let mut constant = BigRational::zero();
    linearize(terms, a, BigRational::one(), &mut coeffs, &mut constant)?;
    linearize(terms, b, -BigRational::one(), &mut coeffs, &mut constant)?;

    // Drop zero coefficients.
    coeffs.retain(|_, c| !c.is_zero());

    // The DL constant is `c` such that `lhs − rhs ⋈ c`, where `lhs − rhs`
    // is the variable part and `c = −constant`.
    let c = -constant;

    // Classify the variable part: it must be `x` (unit), `−y` (opposite),
    // or `x − y` (one unit + one opposite). Anything else is not DL.
    let mut pos: Option<TermId> = None; // coeff +1
    let mut neg: Option<TermId> = None; // coeff −1
    for (t, coeff) in &coeffs {
        if coeff.is_one() {
            if pos.is_some() {
                return None; // two +1 vars ⇒ not DL
            }
            pos = Some(*t);
        } else if (-coeff).is_one() {
            if neg.is_some() {
                return None; // two −1 vars ⇒ not DL
            }
            neg = Some(*t);
        } else {
            return None; // non-unit coefficient ⇒ not DL
        }
    }

    match (pos, neg) {
        // x − y ⋈ c
        (Some(x), Some(y)) => Some(CollectedAtom {
            lhs: x,
            rhs: Some(y),
            op,
            c,
        }),
        // x ⋈ c
        (Some(x), None) => Some(CollectedAtom {
            lhs: x,
            rhs: None,
            op,
            c,
        }),
        // −y ⋈ c  ⇔  y ⋈ −c, with the operator flipped (multiply by −1).
        (None, Some(y)) => Some(CollectedAtom {
            lhs: y,
            rhs: None,
            op: flip_op_for_negation(op),
            c: -c,
        }),
        // 0 ⋈ c — a constant predicate with no variables. Not a DL atom in
        // the engine's variable space; fall through (the normal solver folds
        // it). This keeps the engine's `from_atoms` happy (it needs ≥1 var).
        (None, None) => None,
    }
}

/// Linearize an Int/Real term into `coeffs` (per-leaf coefficient) and a
/// running `constant`, scaled by `scale`. Returns `None` on any shape that is
/// not a linear combination over atomic arithmetic leaves (e.g. nonlinear
/// `*`, division by a variable, ITE, etc.) — fail-closed.
fn linearize(
    terms: &TermStore,
    term: TermId,
    scale: BigRational,
    coeffs: &mut HashMap<TermId, BigRational>,
    constant: &mut BigRational,
) -> Option<()> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => {
            *constant += &scale * BigRational::from(n.clone());
            Some(())
        }
        TermData::Const(Constant::Rational(r)) => {
            *constant += &scale * &r.0;
            Some(())
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "+" => {
                for &arg in args {
                    linearize(terms, arg, scale.clone(), coeffs, constant)?;
                }
                Some(())
            }
            "-" if args.len() == 1 => linearize(terms, args[0], -scale, coeffs, constant),
            "-" if args.len() >= 2 => {
                linearize(terms, args[0], scale.clone(), coeffs, constant)?;
                for &arg in &args[1..] {
                    linearize(terms, arg, -scale.clone(), coeffs, constant)?;
                }
                Some(())
            }
            "*" => {
                // Linear only: at most one non-constant factor; all other
                // factors must be numeric constants.
                let mut const_factor = BigRational::one();
                let mut var_arg: Option<TermId> = None;
                for &arg in args {
                    if let Some(k) = numeric_constant(terms, arg) {
                        const_factor *= k;
                    } else if var_arg.is_none() {
                        var_arg = Some(arg);
                    } else {
                        return None; // ≥2 variable factors ⇒ nonlinear
                    }
                }
                match var_arg {
                    Some(v) => linearize(terms, v, &scale * const_factor, coeffs, constant),
                    None => {
                        *constant += &scale * const_factor;
                        Some(())
                    }
                }
            }
            // Any other function symbol applied to args is treated as an
            // atomic arithmetic leaf ONLY if it is genuinely a variable-like
            // term. Reject interpreted ops we do not model (div, mod, abs,
            // to_int, ...) so we never mis-linearize them.
            _ => try_atomic_leaf(terms, term, scale, coeffs),
        },
        // A bare variable (or any other atomic term) is a leaf.
        _ => try_atomic_leaf(terms, term, scale, coeffs),
    }
}

/// Accept `term` as an atomic difference-logic variable leaf: add `scale` to
/// its coefficient. Only Int/Real-sorted, non-constant terms qualify.
fn try_atomic_leaf(
    terms: &TermStore,
    term: TermId,
    scale: BigRational,
    coeffs: &mut HashMap<TermId, BigRational>,
) -> Option<()> {
    // Must be arithmetic-sorted to be a DL variable.
    if !matches!(terms.sort(term), Sort::Int | Sort::Real) {
        return None;
    }
    // Reject interpreted arithmetic operators we cannot model as a single
    // variable (they would silently become opaque variables and could make a
    // non-DL instance look like DL). Only un-interpreted leaves are allowed:
    // a `Var`, or an uninterpreted function application (e.g. `(f x)` in
    // QF_UFIDL is a legitimate atomic Int term). Constants are not leaves.
    match terms.get(term) {
        TermData::Const(_) => None,
        TermData::App(Symbol::Named(name), _)
            if matches!(
                name.as_str(),
                "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_int" | "to_real"
            ) =>
        {
            // Interpreted arithmetic op that we did not destructure above ⇒
            // not a pure atomic leaf; reject.
            None
        }
        _ => {
            *coeffs.entry(term).or_insert_with(BigRational::zero) += scale;
            Some(())
        }
    }
}

/// A numeric (Int / integral-or-fractional Rational) constant value of a
/// term, including unary minus over a constant. `None` if not a constant.
fn numeric_constant(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            numeric_constant(terms, args[0]).map(|v| -v)
        }
        _ => None,
    }
}

/// Flip a comparison operator under multiplication by −1 (`−y ⋈ c ⇔ y ⋈′ −c`).
fn flip_op_for_negation(op: Op) -> Op {
    match op {
        Op::Le => Op::Ge,
        Op::Lt => Op::Gt,
        Op::Ge => Op::Le,
        Op::Gt => Op::Lt,
        Op::Eq => Op::Eq,
    }
}

/// Build a `Model` with all theory sub-models empty except the supplied
/// arithmetic one. The SAT layer is empty: pure-DL instances have no Boolean
/// structure, and unassigned arithmetic vars default to 0 in `evaluate_var`.
fn empty_model_with(lia: Option<ay_lia::LiaModel>, lra: Option<ay_lra::LraModel>) -> Model {
    let mut model = Model::empty();
    model.lia_model = lia;
    model.lra_model = lra;
    model
}
