// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, under-approximating model-based projection (Workstream B R2,
//! `DESIGN_spacer_pob_lemma_pipeline.md` §4.1.3–§4.1.4).
//!
//! [`Mbp::project_exact`] computes, for a formula `φ`, variables `X` and a model
//! `M ⊨ φ`, a conjunction of literals `ψ` with
//!
//! 1. `M ⊨ ψ`,
//! 2. `ψ ⇒ ∃X. φ` (an UNDER-approximation of the projection — never an
//!    over-approximation, which is what makes a Spacer child POB a subset of the
//!    parent's pre-image, INV-P),
//! 3. no variable of `X` occurs in `ψ`.
//!
//! It is a separate entry point: the legacy projector (`theory.rs`) keeps only
//! the model-greatest lower bound and resolves it with the real shadow, which
//! over-approximates on non-unit coefficients and whenever another lower bound
//! is dropped (G8). Legacy callers are untouched.
//!
//! The algorithm eliminates one variable at a time and keeps, per step, the
//! invariant `M ⊨ C_k` and `C_k ⇒ ∃x. C_{k-1}` (so the composition satisfies 1
//! and 2). For a variable `x`:
//!
//! - **Equality** `a·x + r = 0` (linear): with `|a| = 1`, or any `a` over the
//!   reals, `x := -r/a` is substituted into EVERY literal mentioning `x` (linear
//!   ones by exact linear combination, any other literal syntactically) — exact.
//!   Integer `|a| > 1`: the same with the divisibility literal `r mod |a| = 0`
//!   (then `x = -r/a` is an integer), and `x := (-r) div a` in non-linear
//!   literals — exact.
//! - **Bounds only** (every literal on `x` is a linear bound or a disequality,
//!   which is split by the model into `<`/`>` first): one side empty ⇒ drop
//!   them (`x` is unbounded on the other side). Integers — Bjørner–Janota: the
//!   model-greatest lower bound `a*·x ≥ t*`, `d = (-t*(M)) mod a*`, witness
//!   `x := (t* + d) / a*` (= ⌈t*/a*⌉), emitting `(t* + d) mod a* = 0` when
//!   `a* > 1` and every other bound instantiated at the witness. Reals —
//!   model-based Loos–Weispfenning at the model-tightest lower bound, strictness
//!   carried (`|lowers| + |uppers| − 1` literals).
//! - **Anything else** (a `mod`/`div`/ITE/non-linear occurrence with no defining
//!   equality): `x := M(x)` in the literals that mention it (Spacer's per-variable
//!   `dont_sub = false`) — sound (`M ⊨ φ[M(x)/x]`, `φ[M(x)/x] ⇒ ∃x. φ`), counted
//!   by the caller. A variable with no usable model value is reported
//!   ([`ExactFail::NoValue`]); the caller falls back to a point cube.
//!
//! Before elimination, arithmetic ITE terms inside literals that mention an
//! eliminated variable are split by the model ([`Mbp::split_term_ites`]).

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::Mbp;

type Model = FxHashMap<String, SmtValue>;

/// Per-call counters of [`Mbp::project_exact`] (telemetry only).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct ExactStats {
    /// Variables eliminated through a unit-coefficient (or real) equality.
    pub(crate) unit_eq: usize,
    /// Integer variables eliminated through a non-unit equality (+ divisibility literal).
    pub(crate) nonunit_eq: usize,
    /// Integer variables eliminated by the Bjørner–Janota bounds rule.
    pub(crate) bj_bounds: usize,
    /// Real variables eliminated by model-based Loos–Weispfenning.
    pub(crate) lw_bounds: usize,
    /// Variables bounded on one side only (their bounds are dropped).
    pub(crate) one_sided: usize,
    /// Disequalities split by the model into a strict bound.
    pub(crate) diseq_splits: usize,
    /// Arithmetic ITE terms split by the model.
    pub(crate) ite_splits: usize,
    /// Divisibility literals emitted.
    pub(crate) div_literals: usize,
    /// Boolean variables eliminated through a definition (`x = e`, `x`, `¬x`).
    pub(crate) bool_defs: usize,
}

/// Result of [`Mbp::project_exact`]: the literals of `ψ` and the variables that
/// were eliminated by model-value substitution.
#[derive(Debug, Clone)]
pub(crate) struct ExactProjection {
    /// The literals of `ψ` (a conjunction; `Bool(true)` never appears).
    pub(crate) lits: Vec<ChcExpr>,
    /// Variables eliminated by per-variable model substitution (not exactly).
    pub(crate) substituted: Vec<ChcVar>,
    /// Counters.
    pub(crate) stats: ExactStats,
}

/// Why [`Mbp::project_exact`] produced no projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExactFail {
    /// `var` had to be substituted by its model value but the model has none
    /// (or none representable as a literal).
    NoValue(ChcVar),
}

// ------------------------------------------------------------------ linear forms

/// A linear term `Σ c_v·v + k` with rational coefficients (variables sorted by
/// name, no zero coefficient).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Lin {
    terms: Vec<(ChcVar, BigRational)>,
    konst: BigRational,
}

fn rat(n: i128) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

impl Lin {
    fn constant(k: BigRational) -> Self {
        Self {
            terms: Vec::new(),
            konst: k,
        }
    }

    fn var(v: &ChcVar) -> Self {
        Self {
            terms: vec![(v.clone(), BigRational::one())],
            konst: BigRational::zero(),
        }
    }

    fn add(&self, other: &Self) -> Self {
        let mut terms: Vec<(ChcVar, BigRational)> =
            Vec::with_capacity(self.terms.len() + other.terms.len());
        let (mut i, mut j) = (0, 0);
        while i < self.terms.len() || j < other.terms.len() {
            let take_left = j >= other.terms.len()
                || (i < self.terms.len() && self.terms[i].0.name < other.terms[j].0.name);
            let take_right = i >= self.terms.len()
                || (j < other.terms.len() && other.terms[j].0.name < self.terms[i].0.name);
            if take_left {
                terms.push(self.terms[i].clone());
                i += 1;
            } else if take_right {
                terms.push(other.terms[j].clone());
                j += 1;
            } else {
                let c = &self.terms[i].1 + &other.terms[j].1;
                if !c.is_zero() {
                    terms.push((self.terms[i].0.clone(), c));
                }
                i += 1;
                j += 1;
            }
        }
        Self {
            terms,
            konst: &self.konst + &other.konst,
        }
    }

    fn scale(&self, c: &BigRational) -> Self {
        if c.is_zero() {
            return Self::constant(BigRational::zero());
        }
        Self {
            terms: self.terms.iter().map(|(v, k)| (v.clone(), k * c)).collect(),
            konst: &self.konst * c,
        }
    }

    fn neg(&self) -> Self {
        self.scale(&-BigRational::one())
    }

    fn coeff(&self, name: &str) -> BigRational {
        self.terms
            .iter()
            .find(|(v, _)| v.name == name)
            .map(|(_, c)| c.clone())
            .unwrap_or_else(BigRational::zero)
    }

    fn without(&self, name: &str) -> Self {
        Self {
            terms: self
                .terms
                .iter()
                .filter(|(v, _)| v.name != name)
                .cloned()
                .collect(),
            konst: self.konst.clone(),
        }
    }

    fn is_ground(&self) -> bool {
        self.terms.is_empty()
    }

    fn all_integer(&self) -> bool {
        self.konst.is_integer() && self.terms.iter().all(|(_, c)| c.is_integer())
    }

    /// Value under `model` (every variable must have an Int/Real value).
    fn eval(&self, model: &Model) -> Option<BigRational> {
        let mut acc = self.konst.clone();
        for (v, c) in &self.terms {
            let val = match model.get(&v.name)? {
                SmtValue::Int(n) => rat(*n),
                SmtValue::BigInt(n) => BigRational::from_integer(n.as_ref().clone()),
                SmtValue::Real(r) => r.clone(),
                _ => return None,
            };
            acc += c * val;
        }
        Some(acc)
    }

    /// Parse a linear arithmetic term (`Int`/`Real` literals and variables,
    /// n-ary `+`/`-`, unary `-`, multiplication by constants, real division by
    /// a non-zero constant). `None` for anything else.
    pub(crate) fn from_expr(e: &ChcExpr) -> Option<Self> {
        crate::expr::maybe_grow_expr_stack(|| {
            let _g = crate::expr::ExprDepthGuard::check()?;
            match e {
                ChcExpr::Int(n) => Some(Self::constant(rat(*n))),
                ChcExpr::Real(n, d) if *d != 0 => Some(Self::constant(BigRational::new(
                    BigInt::from(*n),
                    BigInt::from(*d),
                ))),
                ChcExpr::Var(v) if matches!(v.sort, ChcSort::Int | ChcSort::Real) => {
                    Some(Self::var(v))
                }
                ChcExpr::Op(ChcOp::Add, args) => {
                    let mut acc = Self::constant(BigRational::zero());
                    for a in args {
                        acc = acc.add(&Self::from_expr(a)?);
                    }
                    Some(acc)
                }
                ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                    let first = Self::from_expr(&args[0])?;
                    if args.len() == 1 {
                        return Some(first.neg());
                    }
                    let mut acc = first;
                    for a in &args[1..] {
                        acc = acc.add(&Self::from_expr(a)?.neg());
                    }
                    Some(acc)
                }
                ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                    Some(Self::from_expr(&args[0])?.neg())
                }
                ChcExpr::Op(ChcOp::Mul, args) if !args.is_empty() => {
                    let mut acc = Self::constant(BigRational::one());
                    for a in args {
                        let f = Self::from_expr(a)?;
                        if acc.is_ground() {
                            acc = f.scale(&acc.konst);
                        } else if f.is_ground() {
                            acc = acc.scale(&f.konst);
                        } else {
                            return None; // non-linear
                        }
                    }
                    Some(acc)
                }
                ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 && e.sort() == ChcSort::Real => {
                    let num = Self::from_expr(&args[0])?;
                    let den = Self::from_expr(&args[1])?;
                    if !den.is_ground() || den.konst.is_zero() {
                        return None;
                    }
                    Some(num.scale(&den.konst.recip()))
                }
                _ => None,
            }
        })
    }

    /// Render as an arithmetic term of sort Int (`real == false`) or Real.
    fn to_expr(&self, real: bool) -> Option<ChcExpr> {
        let mut acc: Option<ChcExpr> = None;
        for (v, c) in &self.terms {
            let var = ChcExpr::var(v.clone());
            let mag = c.abs();
            let term = if mag.is_one() {
                var
            } else {
                ChcExpr::mul(const_expr(&mag, real)?, var)
            };
            acc = Some(match acc {
                None if c.is_negative() => ChcExpr::neg(term),
                None => term,
                Some(a) if c.is_negative() => ChcExpr::sub(a, term),
                Some(a) => ChcExpr::add(a, term),
            });
        }
        if !self.konst.is_zero() || acc.is_none() {
            let k = const_expr(&self.konst.abs(), real)?;
            acc = Some(match acc {
                None if self.konst.is_negative() => const_expr(&self.konst, real)?,
                None => k,
                Some(a) if self.konst.is_negative() => ChcExpr::sub(a, k),
                Some(a) => ChcExpr::add(a, k),
            });
        }
        acc
    }
}

/// A constant of the requested sort (`None` when it does not fit the literal).
fn const_expr(c: &BigRational, real: bool) -> Option<ChcExpr> {
    if real {
        let n = c.numer().to_i64()?;
        let d = c.denom().to_i64()?;
        Some(ChcExpr::Real(n, d))
    } else {
        if !c.is_integer() {
            return None;
        }
        Some(ChcExpr::Int(c.to_integer().to_i128()?))
    }
}

/// `lin ⋈ 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Rel {
    Eq,
    Ge,
    Gt,
}

#[derive(Debug, Clone)]
struct LinAtom {
    lin: Lin,
    rel: Rel,
    int: bool,
}

fn arith_sort(e: &ChcExpr) -> Option<bool> {
    match e.sort() {
        ChcSort::Int => Some(true),
        ChcSort::Real => Some(false),
        _ => None,
    }
}

/// `a - b` for two arithmetic operands of the same sort, with the sort flag.
fn diff(a: &ChcExpr, b: &ChcExpr) -> Option<(Lin, bool)> {
    let int_a = arith_sort(a)?;
    let int_b = arith_sort(b)?;
    if int_a != int_b {
        return None;
    }
    let la = Lin::from_expr(a)?;
    let lb = Lin::from_expr(b)?;
    Some((la.add(&lb.neg()), int_a))
}

impl LinAtom {
    /// Parse a comparison literal (possibly negated) into `lin ⋈ 0`.
    fn parse(e: &ChcExpr) -> Option<Self> {
        let (op, args, positive) = match e {
            ChcExpr::Op(ChcOp::Not, inner) if inner.len() == 1 => match inner[0].as_ref() {
                ChcExpr::Op(op, args) => (*op, args, false),
                _ => return None,
            },
            ChcExpr::Op(op, args) => (*op, args, true),
            _ => return None,
        };
        if args.len() != 2 {
            return None;
        }
        let (a, b) = (args[0].as_ref(), args[1].as_ref());
        // Normalize to `x ⋈ 0` over `a - b` (or `b - a`).
        let (lin, rel, int) = match (op, positive) {
            (ChcOp::Eq, true) => {
                let (l, i) = diff(a, b)?;
                (l, Rel::Eq, i)
            }
            (ChcOp::Ge, true) | (ChcOp::Lt, false) => {
                let (l, i) = diff(a, b)?;
                (l, Rel::Ge, i)
            }
            (ChcOp::Gt, true) | (ChcOp::Le, false) => {
                let (l, i) = diff(a, b)?;
                (l, Rel::Gt, i)
            }
            (ChcOp::Le, true) | (ChcOp::Gt, false) => {
                let (l, i) = diff(b, a)?;
                (l, Rel::Ge, i)
            }
            (ChcOp::Lt, true) | (ChcOp::Ge, false) => {
                let (l, i) = diff(b, a)?;
                (l, Rel::Gt, i)
            }
            _ => return None,
        };
        Self { lin, rel, int }.normalize()
    }

    /// Integer atoms: strict ⇒ non-strict with `-1`, and gcd tightening
    /// (`Σ c·v + k ≥ 0` ⟺ `Σ (c/g)·v + ⌊k/g⌋ ≥ 0` over the integers). Exact.
    fn normalize(mut self) -> Option<Self> {
        if !self.int {
            return Some(self);
        }
        if !self.lin.all_integer() {
            return None;
        }
        if self.rel == Rel::Gt {
            self.lin.konst -= BigRational::one();
            self.rel = Rel::Ge;
        }
        let g = self
            .lin
            .terms
            .iter()
            .fold(BigInt::zero(), |g, (_, c)| g.gcd(&c.to_integer()));
        if g > BigInt::one() {
            let k = self.lin.konst.to_integer();
            match self.rel {
                Rel::Ge => {
                    let gq = BigRational::from_integer(g.clone());
                    for (_, c) in &mut self.lin.terms {
                        *c = &*c / &gq;
                    }
                    self.lin.konst = BigRational::from_integer(k.div_floor(&g));
                }
                Rel::Eq if (&k % &g).is_zero() => {
                    let gq = BigRational::from_integer(g);
                    for (_, c) in &mut self.lin.terms {
                        *c = &*c / &gq;
                    }
                    self.lin.konst = &self.lin.konst / &gq;
                }
                _ => {}
            }
        }
        Some(self)
    }

    fn holds(&self, model: &Model) -> Option<bool> {
        let v = self.lin.eval(model)?;
        Some(match self.rel {
            Rel::Eq => v.is_zero(),
            Rel::Ge => !v.is_negative(),
            Rel::Gt => v.is_positive(),
        })
    }

    /// Render as a literal with the variables on the left (leading coefficient
    /// positive) and the constant on the right. Ground atoms fold to a Bool.
    fn to_expr(&self) -> Option<ChcExpr> {
        let real = !self.int;
        if self.lin.is_ground() {
            let v = &self.lin.konst;
            return Some(ChcExpr::Bool(match self.rel {
                Rel::Eq => v.is_zero(),
                Rel::Ge => !v.is_negative(),
                Rel::Gt => v.is_positive(),
            }));
        }
        let flip = self.lin.terms[0].1.is_negative();
        let lin = if flip {
            self.lin.neg()
        } else {
            self.lin.clone()
        };
        let lhs = Lin {
            terms: lin.terms.clone(),
            konst: BigRational::zero(),
        }
        .to_expr(real)?;
        let rhs = const_expr(&-lin.konst.clone(), real)?;
        Some(match (self.rel, flip) {
            (Rel::Eq, _) => ChcExpr::eq(lhs, rhs),
            (Rel::Ge, false) => ChcExpr::ge(lhs, rhs),
            (Rel::Ge, true) => ChcExpr::le(lhs, rhs),
            (Rel::Gt, false) => ChcExpr::gt(lhs, rhs),
            (Rel::Gt, true) => ChcExpr::lt(lhs, rhs),
        })
    }
}

/// `lin mod m = 0` for an integer linear term (ground ⇒ folded).
fn div_literal(lin: &Lin, m: &BigInt) -> Option<ChcExpr> {
    if lin.is_ground() {
        let k = lin.konst.to_integer();
        return Some(ChcExpr::Bool(k.mod_floor(m).is_zero()));
    }
    // Reduce the constant into [0, m) so the literal is canonical.
    let mut reduced = lin.clone();
    reduced.konst = BigRational::from_integer(lin.konst.to_integer().mod_floor(m));
    Some(ChcExpr::eq(
        ChcExpr::mod_op(reduced.to_expr(false)?, ChcExpr::Int(m.to_i128()?)),
        ChcExpr::Int(0),
    ))
}

/// A disequality literal `a ≠ b` over arithmetic operands: `(a - b, int)`.
fn parse_diseq(e: &ChcExpr) -> Option<(Lin, bool)> {
    match e {
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => diff(&args[0], &args[1]),
        ChcExpr::Op(ChcOp::Not, inner) if inner.len() == 1 => match inner[0].as_ref() {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => diff(&args[0], &args[1]),
            _ => None,
        },
        _ => None,
    }
}

fn is_trivially_true(e: &ChcExpr) -> bool {
    matches!(e, ChcExpr::Bool(true))
}

// ------------------------------------------------------------------ projection

impl Mbp {
    /// The model value of `var` as a literal of its sort (`None` when absent
    /// or not representable). Crate-visible wrapper for the free constructor.
    pub(crate) fn value_expr_for(var: &ChcVar, model: &Model) -> Option<ChcExpr> {
        Self::model_value_expr(var, model)
    }

    /// Exact under-approximating projection of `formula` onto the complement of
    /// `vars` under `model` (module docs). `model` must satisfy `formula`; when
    /// it does not, the result may be falsified by the model and the caller's
    /// model check (INV-P guard) catches it.
    pub(crate) fn project_exact(
        &self,
        formula: &ChcExpr,
        vars: &[ChcVar],
        model: &Model,
    ) -> Result<ExactProjection, ExactFail> {
        let mut stats = ExactStats::default();
        let elim: FxHashSet<&str> = vars.iter().map(|v| v.name.as_str()).collect();
        let mentions_elim = |e: &ChcExpr| e.vars().iter().any(|v| elim.contains(v.name.as_str()));

        let implicant: Vec<ChcExpr> = self
            .get_implicant(formula, model)
            .iter()
            .map(super::Literal::to_expr)
            .collect();
        let mut lits =
            self.split_term_ites(implicant, model, &mentions_elim, &mut stats.ite_splits);

        let mut substituted = Vec::new();
        for var in vars {
            lits = self.eliminate_exact(var, lits, model, &mut stats, &mut substituted)?;
        }

        // Model substitution can leave compound Boolean literals
        // (`(= true (and a b))` ⇒ `(and a b)`); the implicant under the model
        // splits them back into literals (it implies each literal and the model
        // satisfies it, so both invariants are kept).
        let mut out: Vec<ChcExpr> = Vec::new();
        for lit in self.resplit(lits, model) {
            if is_trivially_true(&lit) || out.contains(&lit) {
                continue;
            }
            out.push(lit);
        }
        Ok(ExactProjection {
            lits: out,
            substituted,
            stats,
        })
    }

    fn eliminate_exact(
        &self,
        var: &ChcVar,
        lits: Vec<ChcExpr>,
        model: &Model,
        stats: &mut ExactStats,
        substituted: &mut Vec<ChcVar>,
    ) -> Result<Vec<ChcExpr>, ExactFail> {
        let (with, mut without): (Vec<ChcExpr>, Vec<ChcExpr>) = lits
            .into_iter()
            .partition(|l| l.contains_var_name(&var.name));
        if with.is_empty() {
            return Ok(without);
        }
        if var.sort == ChcSort::Bool {
            if let Some(projected) = self.eliminate_bool_by_definition(var, &with, model) {
                stats.bool_defs += 1;
                without.extend(projected);
                return Ok(without);
            }
        }
        if matches!(var.sort, ChcSort::Int | ChcSort::Real) {
            if let Some(projected) = self.eliminate_arith(var, &with, model, stats) {
                without.extend(projected.into_iter().filter(|l| !is_trivially_true(l)));
                return Ok(without);
            }
        }
        // Per-variable model substitution (Spacer dont_sub = false). Any
        // constant keeps `ψ ⇒ ∃x. φ`; the model's own value also keeps `M ⊨ ψ`.
        // A variable the (partial) model does not assign may take a sort
        // default only when every literal it occurs in then holds in the model.
        let rewritten = |value: &ChcExpr| -> Vec<ChcExpr> {
            with.iter()
                .map(|lit| {
                    lit.substitute(&[(var.clone(), value.clone())])
                        .simplify_constants()
                })
                .collect()
        };
        let chosen = match Self::model_value_expr(var, model) {
            Some(value) => rewritten(&value),
            None => {
                let defaults: &[ChcExpr] = match var.sort {
                    ChcSort::Bool => &[ChcExpr::Bool(false), ChcExpr::Bool(true)],
                    ChcSort::Int => &[ChcExpr::Int(0)],
                    ChcSort::Real => &[ChcExpr::Real(0, 1)],
                    _ => &[],
                };
                let completed = defaults
                    .iter()
                    .map(|d| rewritten(d))
                    .find(|lits| lits.iter().all(|l| self.eval_bool(l, model) == Some(true)));
                match completed {
                    Some(lits) => lits,
                    None => return Err(ExactFail::NoValue(var.clone())),
                }
            }
        };
        substituted.push(var.clone());
        without.extend(self.resplit(chosen, model));
        Ok(without)
    }

    /// Split rewritten literals back into implicant literals under `model`
    /// (each is implied-by its split and the model satisfies the split). A
    /// literal that folded to `false` is kept verbatim: dropping it would
    /// over-approximate, and the caller's model check rejects it.
    fn resplit(&self, lits: Vec<ChcExpr>, model: &Model) -> Vec<ChcExpr> {
        let mut out = Vec::with_capacity(lits.len());
        for lit in lits {
            let lit = lit.simplify_constants();
            match lit {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => out.push(lit),
                _ => {
                    let split = self.get_implicant(&lit, model);
                    if split.is_empty() {
                        // Never drop a constraint the implicant walk cannot see.
                        out.push(lit);
                    } else {
                        out.extend(split.iter().map(super::Literal::to_expr));
                    }
                }
            }
        }
        out
    }

    /// Exact elimination of a Boolean variable through a definition among the
    /// literals that mention it: `x = e` / `e = x` / `x ⇔ e` (`e` free of `x`;
    /// a variable `e` preferred — the canonical renaming `c_i = x`), a unit
    /// literal `x` / `¬x`, or `¬(x = e)`. `∃x. (x = e) ∧ φ ≡ φ[e/x]`, so the
    /// step is exact; `None` when no definition exists.
    fn eliminate_bool_by_definition(
        &self,
        var: &ChcVar,
        with: &[ChcExpr],
        model: &Model,
    ) -> Option<Vec<ChcExpr>> {
        let is_x = |e: &ChcExpr| matches!(e, ChcExpr::Var(v) if v.name == var.name);
        let defines = |lit: &ChcExpr| -> Option<ChcExpr> {
            let bool_other =
                |e: &ChcExpr| e.sort() == ChcSort::Bool && !e.contains_var_name(&var.name);
            match lit {
                ChcExpr::Var(v) if v.name == var.name => Some(ChcExpr::Bool(true)),
                ChcExpr::Op(ChcOp::Eq | ChcOp::Iff, a) if a.len() == 2 => {
                    if is_x(&a[0]) && bool_other(&a[1]) {
                        Some(a[1].as_ref().clone())
                    } else if is_x(&a[1]) && bool_other(&a[0]) {
                        Some(a[0].as_ref().clone())
                    } else {
                        None
                    }
                }
                ChcExpr::Op(ChcOp::Not, n) if n.len() == 1 => match n[0].as_ref() {
                    ChcExpr::Var(v) if v.name == var.name => Some(ChcExpr::Bool(false)),
                    ChcExpr::Op(ChcOp::Eq | ChcOp::Iff, a) if a.len() == 2 => {
                        if is_x(&a[0]) && bool_other(&a[1]) {
                            Some(ChcExpr::not(a[1].as_ref().clone()))
                        } else if is_x(&a[1]) && bool_other(&a[0]) {
                            Some(ChcExpr::not(a[0].as_ref().clone()))
                        } else {
                            None
                        }
                    }
                    _ => None,
                },
                _ => None,
            }
        };
        let candidates: Vec<(usize, ChcExpr)> = with
            .iter()
            .enumerate()
            .filter_map(|(i, l)| defines(l).map(|d| (i, d)))
            .collect();
        // Rank: a variable definiens (renaming) < a constant < anything else.
        let rank = |d: &ChcExpr| match d {
            ChcExpr::Var(_) => 0,
            ChcExpr::Bool(_) => 1,
            _ => 2,
        };
        let (di, def) = candidates.into_iter().min_by_key(|(_, d)| rank(d))?;
        let rewritten: Vec<ChcExpr> = with
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != di)
            .map(|(_, l)| l.substitute(&[(var.clone(), def.clone())]))
            .collect();
        Some(self.resplit(rewritten, model))
    }

    /// Exact elimination of an Int/Real variable; `None` ⇒ the caller
    /// substitutes the model value instead.
    fn eliminate_arith(
        &self,
        var: &ChcVar,
        with: &[ChcExpr],
        model: &Model,
        stats: &mut ExactStats,
    ) -> Option<Vec<ChcExpr>> {
        let int = var.sort == ChcSort::Int;
        let name = var.name.as_str();
        // Linear view of each literal (None = not a linear comparison).
        let atoms: Vec<Option<LinAtom>> = with
            .iter()
            .map(|l| LinAtom::parse(l).filter(|a| a.int == int))
            .collect();

        // 1. Equalities (exact for any other literal shape).
        let pick = atoms
            .iter()
            .enumerate()
            .filter_map(|(i, a)| {
                let a = a.as_ref()?;
                if a.rel != Rel::Eq {
                    return None;
                }
                let c = a.lin.coeff(name);
                if c.is_zero() {
                    return None;
                }
                Some((i, c.abs()))
            })
            .min_by(|x, y| x.1.cmp(&y.1));
        if let Some((ei, _)) = pick {
            let out = self.eliminate_by_equality(var, with, &atoms, ei, int, model, stats);
            if out.is_some() {
                return out;
            }
        }

        // 2. Bounds (every literal on `var` must be a linear bound or a
        //    disequality the model splits).
        let mut bounds: Vec<LinAtom> = Vec::with_capacity(with.len());
        for (lit, atom) in with.iter().zip(atoms) {
            if let Some(a) = atom {
                bounds.push(a);
                continue;
            }
            let (d, d_int) = parse_diseq(lit)?;
            if d_int != int {
                return None;
            }
            let v = d.eval(model)?;
            if v.is_zero() {
                return None; // the model violates the literal
            }
            stats.diseq_splits += 1;
            let lin = if v.is_positive() { d } else { d.neg() };
            bounds.push(
                LinAtom {
                    lin,
                    rel: Rel::Gt,
                    int,
                }
                .normalize()?,
            );
        }
        self.eliminate_by_bounds(var, bounds, model, int, stats)
    }

    #[allow(clippy::too_many_arguments)]
    fn eliminate_by_equality(
        &self,
        var: &ChcVar,
        with: &[ChcExpr],
        atoms: &[Option<LinAtom>],
        ei: usize,
        int: bool,
        model: &Model,
        stats: &mut ExactStats,
    ) -> Option<Vec<ChcExpr>> {
        let name = var.name.as_str();
        let eq = atoms[ei].as_ref()?;
        let a = eq.lin.coeff(name);
        let r = eq.lin.without(name); // a·x + r = 0
        let abs_a = a.abs();
        let unit = abs_a.is_one();
        let mut out: Vec<ChcExpr> = Vec::with_capacity(with.len());
        if int && !unit {
            out.push(div_literal(&r, &abs_a.to_integer())?);
            stats.div_literals += 1;
        }
        // The syntactic witness term for non-linear literals: x = -r / a.
        let witness = if int {
            let neg_r = if a.is_positive() { r.neg() } else { r.clone() };
            let t = neg_r.to_expr(false)?;
            if unit {
                t
            } else {
                ChcExpr::Op(
                    ChcOp::Div,
                    vec![
                        std::sync::Arc::new(t),
                        std::sync::Arc::new(ChcExpr::Int(abs_a.to_integer().to_i128()?)),
                    ],
                )
            }
        } else {
            r.scale(&(-a.recip())).to_expr(true)?
        };
        for (i, (lit, atom)) in with.iter().zip(atoms).enumerate() {
            if i == ei {
                continue;
            }
            match atom {
                Some(at) if !at.lin.coeff(name).is_zero() => {
                    // b·x + s ⋈ 0 → |a|·s − sign(a)·b·r ⋈ 0 (multiplied by |a| > 0).
                    let b = at.lin.coeff(name);
                    let s = at.lin.without(name);
                    let factor = if a.is_positive() { -b } else { b };
                    let lin = s.scale(&abs_a).add(&r.scale(&factor));
                    let na = LinAtom {
                        lin,
                        rel: at.rel,
                        int,
                    }
                    .normalize()?;
                    out.push(na.to_expr()?);
                }
                _ => {
                    out.extend(self.resplit(
                        vec![lit.substitute(&[(var.clone(), witness.clone())])],
                        model,
                    ));
                }
            }
        }
        if int && !unit {
            stats.nonunit_eq += 1;
        } else {
            stats.unit_eq += 1;
        }
        Some(out)
    }

    fn eliminate_by_bounds(
        &self,
        var: &ChcVar,
        bounds: Vec<LinAtom>,
        model: &Model,
        int: bool,
        stats: &mut ExactStats,
    ) -> Option<Vec<ChcExpr>> {
        let name = var.name.as_str();
        // Lower: a·x ⋈ t (a > 0); upper: b·x ⋈ s (b > 0); `strict` over the reals.
        let mut lowers: Vec<(BigRational, Lin, bool)> = Vec::new();
        let mut uppers: Vec<(BigRational, Lin, bool)> = Vec::new();
        let mut out: Vec<ChcExpr> = Vec::new();
        for at in bounds {
            let c = at.lin.coeff(name);
            if c.is_zero() {
                out.push(at.to_expr()?);
                continue;
            }
            if at.rel == Rel::Eq {
                return None; // equalities were handled (or failed) above
            }
            let strict = at.rel == Rel::Gt;
            let rest = at.lin.without(name); // c·x + rest ⋈ 0
            if c.is_positive() {
                lowers.push((c, rest.neg(), strict)); // c·x ⋈ −rest
            } else {
                uppers.push((c.abs(), rest, strict)); // |c|·x ⋈' rest
            }
        }
        if lowers.is_empty() || uppers.is_empty() {
            stats.one_sided += 1;
            return Some(out);
        }
        // Model value t_j / a_j of every lower bound.
        let mut best: Option<(usize, BigRational, bool)> = None;
        for (j, (a, t, strict)) in lowers.iter().enumerate() {
            let v = t.eval(model)? / a;
            let better = match &best {
                None => true,
                Some((_, bv, bs)) => v > *bv || (v == *bv && *strict && !*bs),
            };
            if better {
                best = Some((j, v, *strict));
            }
        }
        let (js, _, s_star) = best?;
        let (a_star, t_star, _) = lowers[js].clone();
        let emit = |lin: Lin, strict: bool, out: &mut Vec<ChcExpr>| -> Option<()> {
            let at = LinAtom {
                lin,
                rel: if strict { Rel::Gt } else { Rel::Ge },
                int,
            }
            .normalize()?;
            out.push(at.to_expr()?);
            Some(())
        };
        if int {
            // Bjørner–Janota: witness x := (t* + d) / a*, d = (−t*(M)) mod a*.
            let a_int = a_star.to_integer();
            let t_val = t_star.eval(model)?;
            if !t_val.is_integer() {
                return None;
            }
            let d = (-t_val.to_integer()).mod_floor(&a_int);
            let big_t = t_star.add(&Lin::constant(BigRational::from_integer(d)));
            if a_int > BigInt::one() {
                out.push(div_literal(&big_t, &a_int)?);
                stats.div_literals += 1;
            }
            for (j, (a_j, t_j, _)) in lowers.iter().enumerate() {
                if j == js {
                    continue;
                }
                // a_j·T ≥ a*·t_j
                emit(
                    big_t.scale(a_j).add(&t_j.scale(&a_star).neg()),
                    false,
                    &mut out,
                )?;
            }
            for (b_i, s_i, _) in &uppers {
                // b_i·T ≤ a*·s_i
                emit(
                    s_i.scale(&a_star).add(&big_t.scale(b_i).neg()),
                    false,
                    &mut out,
                )?;
            }
            stats.bj_bounds += 1;
        } else {
            // Loos–Weispfenning at the model-tightest lower bound.
            for (j, (a_j, t_j, s_j)) in lowers.iter().enumerate() {
                if j == js {
                    continue;
                }
                // t_j / a_j ⋈ t*/a*  ⟺  a_j·t* − a*·t_j ⋈ 0
                emit(
                    t_star.scale(a_j).add(&t_j.scale(&a_star).neg()),
                    *s_j && !s_star,
                    &mut out,
                )?;
            }
            for (b_i, s_i, u_i) in &uppers {
                // t*/a* ⋈ s_i/b_i  ⟺  a*·s_i − b_i·t* ⋈ 0
                emit(
                    s_i.scale(&a_star).add(&t_star.scale(b_i).neg()),
                    s_star || *u_i,
                    &mut out,
                )?;
            }
            stats.lw_bounds += 1;
        }
        // Defence in depth: every emitted literal holds in the model.
        for lit in &out {
            if let Some(at) = LinAtom::parse(lit) {
                if at.holds(model) == Some(false) {
                    debug_assert!(
                        false,
                        "BUG: exact MBP emitted a literal the model falsifies: {lit}"
                    );
                    return None;
                }
            }
        }
        Some(out)
    }
}
