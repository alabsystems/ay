// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Int→BV blasting for the BV<->LIA bridge (#int2bv-invalid-model).
//!
//! The conservative bridge in the parent module hands a mixed Int/BitVec
//! query to AUFLIA, which treats every BitVec operation as an uninterpreted
//! function. For `bv2nat(bvshl #x1 (int2bv 64 v0))`, `bvand`, `extract`,
//! `sign_extend`, … the arithmetic side therefore learns nothing beyond a
//! range, its SAT candidate is routinely spurious, and the query stalls at
//! `unknown (incomplete)` — which is every masking/shifting obligation a
//! Rust program generates once its integers are Int-lifted.
//!
//! This module decides such queries EXACTLY with the eager bit-blaster
//! (`solve_bv_core`), the established "int2bv"/bounded-integer tactic:
//!
//!   * every Int variable is either
//!       - BOUNDED: `lo <= x <= hi` is PROVED by top-level facts (comparison
//!         conjuncts of the roots, propagated through top-level Int
//!         equalities), and is encoded as a signed W-bit vector `X`; or
//!       - RESIDUE-ONLY: `x` occurs solely as the direct argument of
//!         `int2bv`, and is encoded as a FREE vector `R` of the widest such
//!         occurrence (`int2bv_w(x) := R[w-1:0]`). Exact: `int2bv_w(x)`
//!         depends on `x` only through `x mod 2^wmax`, every residue is
//!         realised by some integer, and every integer has one residue;
//!       - HALF-BOUNDED: `x` is read only inside `int2bv` arguments (through
//!         `+`, `-`, `*`, so only `x mod 2^wmax` matters there), by TOP-LEVEL
//!         atoms comparing it with a constant (`x <= c`, `k*x < c`,
//!         `not (x < c)`, `x != c`, `(distinct x c1 c2)`, `x = c`, …), by
//!         TOP-LEVEL offset equalities `x = y + c` to other such
//!         variables, and by the same constant comparisons UNASSERTED (under
//!         a connective, an `ite` condition or a Bool definition such as
//!         `q = (distinct c x)`). Offset equalities group the variables into
//!         classes `m = r + off_m`; the class's top-level constant atoms,
//!         moved onto `r`, bound it on at most one side and exclude `k`
//!         values, and its unasserted ones cut the integers at their
//!         constants (split points). `r` is encoded as BOUNDED on a SYNTHETIC
//!         interval: every run between the bound and the split points whole,
//!         plus `(k+1) * 2^wmax` consecutive integers past the last bound or
//!         point on each unbounded side (`[0, ...)` when there is neither;
//!         the real interval when both sides are bounded), each member on
//!         that interval shifted by `off_m`, and every interval is asserted
//!         on its vector. Exact: an unasserted comparison has one truth value
//!         on each cell of the partition by the split points; moving `r` by a
//!         multiple of `2^wmax` inside an unbounded cell moves every member
//!         by the same amount, which keeps each `int2bv` value, each offset
//!         equality and each comparison; every residue class mod `2^wmax`
//!         meets such a cell's part of the interval in `k+1` integers that
//!         all satisfy the one-sided bounds, and at most `k` of them are
//!         excluded, so any model of the query maps to one inside the
//!         intervals with every atom unchanged. A class whose top-level atoms
//!         bound it on BOTH sides is instead encoded on that real interval,
//!         which is exact whatever else reads its members (they are then
//!         simply BOUNDED);
//!     anything else (an unbounded Int with an arithmetic occurrence, a
//!     Real, an array/UF/datatype term, `div`/`mod`, a nonlinear product, a
//!     quantifier, …) makes the translator DECLINE, and the bridge keeps its
//!     previous verdict (`unknown`);
//!   * W is chosen so that EVERY Int-sorted subterm's proven interval fits a
//!     signed W-bit vector and `W > w` for every `int2bv`/`bv2nat` width, so
//!     `+`, `-`, `*const`, `=`, `distinct` and the orders are exact (no
//!     wrap), `int2bv_w(t)` is the low `w` bits of `T` (two's complement:
//!     `T[w-1:0] = t mod 2^w` for either sign), and `bv2nat(t)` is
//!     `zero_extend(W-w, T)` (non-negative in signed W bits since W > w);
//!   * BitVec subterms keep their own width; only the `int2bv`/`bv2nat` seams
//!     are rewritten. BitVec leaves (variables, literals) are reused verbatim
//!     and every operator is rebuilt through the theory's own constructors,
//!     so an operator outside FixedSizeBitVectors — a UF application, an
//!     array `select`, a datatype selector — DECLINES instead of reaching the
//!     QF_BV blaster, whose `qf_bv` configuration asserts no congruence or
//!     array axioms.
//!
//! SOUNDNESS. Under the proven bounds the translation is a bijection between
//! the models of the original query and the models of the pure-BV query, atom
//! by atom — every encoding above is an exact identity at the chosen width,
//! never an approximation — so BV-UNSAT ⟹ UNSAT. For SAT the bit-blaster's
//! model is mapped back to an Int model (signed value of `X`, unsigned value of
//! `R`) and RE-VALIDATED against the ORIGINAL roots by the strict bridge
//! validator, which remains the sole SAT authority; a translation slip could
//! therefore only cost completeness, never manufacture a `sat`.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use ay_lia::LiaModel;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::super::super::Executor;
use super::bv_lia_aux_vars::{mint_bv_lia_aux_var, BvLiaAuxVar};
use super::{collect_int_facts, int_const_value};
use crate::executor::model::EvalValue;
use crate::executor::theories::bv::BvSolveConfig;
use crate::executor_types::{ExecutorError, Result, SolveResult};

/// Widest signed encoding the blaster will build. Every Rust-derived
/// obligation (u128 arithmetic included) fits far below it; beyond it the
/// translator declines rather than bit-blast an unbounded-looking query.
const INT_BLAST_MAX_WIDTH: u32 = 512;

/// Rounds of interval propagation through top-level Int equalities. Each
/// round can only tighten, and a handful suffices for the `x = bv2nat(..)`,
/// `y = x + 1` chains real obligations carry.
const BOUND_PROPAGATION_ROUNDS: usize = 8;

/// A closed integer interval `[lo, hi]`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Interval {
    lo: BigInt,
    hi: BigInt,
}

impl Interval {
    fn point(v: BigInt) -> Self {
        Self {
            lo: v.clone(),
            hi: v,
        }
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            lo: &self.lo + &other.lo,
            hi: &self.hi + &other.hi,
        }
    }

    fn sub(&self, other: &Self) -> Self {
        Self {
            lo: &self.lo - &other.hi,
            hi: &self.hi - &other.lo,
        }
    }

    fn neg(&self) -> Self {
        Self {
            lo: -&self.hi,
            hi: -&self.lo,
        }
    }

    fn scale(&self, c: &BigInt) -> Self {
        if c.is_negative() {
            Self {
                lo: &self.hi * c,
                hi: &self.lo * c,
            }
        } else {
            Self {
                lo: &self.lo * c,
                hi: &self.hi * c,
            }
        }
    }

    fn hull(&self, other: &Self) -> Self {
        Self {
            lo: self.lo.clone().min(other.lo.clone()),
            hi: self.hi.clone().max(other.hi.clone()),
        }
    }

    /// Intersection; an empty result is kept as-is (`lo > hi`), which the
    /// bit-blasted bound facts then refute — no verdict is drawn from it here.
    fn meet(&self, other: &Self) -> Self {
        Self {
            lo: self.lo.clone().max(other.lo.clone()),
            hi: self.hi.clone().min(other.hi.clone()),
        }
    }

    /// Number of bits a signed two's-complement vector needs to hold every
    /// value of the interval: `bits(max(|lo|, |hi|)) + 1`.
    fn signed_width(&self) -> u32 {
        let magnitude = self.lo.abs().max(self.hi.abs());
        let bits = u32::try_from(magnitude.bits()).unwrap_or(u32::MAX);
        bits.saturating_add(1)
    }
}

/// How one Int variable is encoded.
#[derive(Clone, Copy, Debug)]
enum IntVarEncoding {
    /// Proven `lo <= x <= hi`: a signed W-bit vector.
    Bounded,
    /// Occurs only as a direct `int2bv` argument: a free vector of this width.
    ResidueOnly { width: u32 },
}

/// Analysis result: how every Int variable is encoded and the common width.
struct IntBlastPlan {
    encodings: HashMap<TermId, IntVarEncoding>,
    width: u32,
    /// HALF-BOUNDED variables and the synthetic interval each is encoded on
    /// (module doc); the translator asserts each interval on its vector.
    synthetic: Vec<(TermId, Interval)>,
}

/// Occurrence census of the Int variables reachable from the roots.
#[derive(Default)]
struct IntVarOccurrences {
    /// Widest `int2bv` the variable is a direct argument of.
    int2bv_width: HashMap<TermId, u32>,
    /// Variables with at least one occurrence that is NOT a direct `int2bv`
    /// argument (arithmetic, comparison, equality, `ite` branch, …).
    arithmetic: HashSet<TermId>,
}

fn is_int2bv(terms: &TermStore, term: TermId) -> Option<(u32, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Indexed(name, indices), args)
            if name == "int2bv" && indices.len() == 1 && args.len() == 1 =>
        {
            Some((indices[0], args[0]))
        }
        _ => None,
    }
}

fn is_bv2nat(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
            Some(args[0])
        }
        _ => None,
    }
}

fn is_int_var(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(_, _)) && *terms.sort(term) == Sort::Int
}

/// Every child of a term, in a fixed order (DAG walk helper).
fn children(terms: &TermStore, term: TermId) -> Vec<TermId> {
    match terms.get(term) {
        TermData::App(_, args) => args.clone(),
        TermData::Not(inner) => vec![*inner],
        TermData::Ite(c, t, e) => vec![*c, *t, *e],
        TermData::Let(bindings, body) => {
            let mut out: Vec<TermId> = bindings.iter().map(|(_, bound)| *bound).collect();
            out.push(*body);
            out
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            let mut out = vec![*body];
            for trigger in triggers {
                out.extend(trigger.iter().copied());
            }
            out
        }
        _ => Vec::new(),
    }
}

fn census_int_vars(terms: &TermStore, roots: &[TermId]) -> IntVarOccurrences {
    fn visit(
        terms: &TermStore,
        term: TermId,
        seen: &mut HashSet<TermId>,
        out: &mut IntVarOccurrences,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let Some((width, arg)) = is_int2bv(terms, term) {
            if is_int_var(terms, arg) {
                out.int2bv_width
                    .entry(arg)
                    .and_modify(|w| *w = (*w).max(width))
                    .or_insert(width);
                return;
            }
        }
        for child in children(terms, term) {
            if is_int_var(terms, child) {
                out.arithmetic.insert(child);
            } else {
                visit(terms, child, seen, out);
            }
        }
    }
    let mut seen = HashSet::default();
    let mut out = IntVarOccurrences::default();
    for &root in roots {
        if is_int_var(terms, root) {
            // An Int-sorted root is ill-sorted; leave it to the caller's
            // decline path by recording an arithmetic occurrence.
            out.arithmetic.insert(root);
        } else {
            visit(terms, root, &mut seen, &mut out);
        }
    }
    out
}

/// A top-level atom that reads Int variables only through constants.
enum ConstantAtom {
    /// `var >= lower` and/or `var <= upper`; a pin `var = c` is both.
    Bound {
        var: TermId,
        lower: Option<BigInt>,
        upper: Option<BigInt>,
    },
    /// `var` differs from `excluded` pairwise distinct constants.
    Disequality { var: TermId, excluded: usize },
    /// `a = b + offset` between two variables.
    Offset {
        a: TermId,
        b: TermId,
        offset: BigInt,
    },
}

/// `v`, `(+ v c)`, `(+ c v)` or `(- v c)`: the variable and its offset.
fn var_plus_constant(terms: &TermStore, term: TermId) -> Option<(TermId, BigInt)> {
    if is_int_var(terms, term) {
        return Some((term, BigInt::zero()));
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    match (name.as_str(), args.as_slice()) {
        ("+", [a, b]) if is_int_var(terms, *a) => Some((*a, int_const_value(terms, *b)?)),
        ("+", [a, b]) if is_int_var(terms, *b) => Some((*b, int_const_value(terms, *a)?)),
        ("-", [a, b]) if is_int_var(terms, *a) => Some((*a, -int_const_value(terms, *b)?)),
        _ => None,
    }
}

/// `v`, `(- v)`, or a product of `v` with integer constants `(* k v)`: the
/// variable and its coefficient, which is never zero. The term store writes
/// `(* -1 v)` as `(- v)` (`TermStore::mk_mul`), so both spellings arrive.
fn scaled_var(terms: &TermStore, term: TermId) -> Option<(TermId, BigInt)> {
    if is_int_var(terms, term) {
        return Some((term, BigInt::one()));
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name == "-" {
        let [negated] = args.as_slice() else {
            return None;
        };
        return is_int_var(terms, *negated).then(|| (*negated, -BigInt::one()));
    }
    if name != "*" {
        return None;
    }
    let (coefficient, factor) = split_constant_product(terms, args)?;
    let var = factor?;
    (is_int_var(terms, var) && !coefficient.is_zero()).then_some((var, coefficient))
}

/// `lhs <= rhs` (or `lhs < rhs` when `strict`) with one side `k·v` and the
/// other a constant, read exactly as a one-sided bound on `v`:
/// `k·v <= c` is `v <= floor(c/k)` for `k > 0` and `v >= ceil(c/k)` for
/// `k < 0`; a strict order first moves the constant by one.
fn scaled_bound(terms: &TermStore, lhs: TermId, rhs: TermId, strict: bool) -> Option<ConstantAtom> {
    use num_integer::Integer;
    let step = if strict {
        BigInt::one()
    } else {
        BigInt::zero()
    };
    let floor_div = |c: &BigInt, k: &BigInt| c.div_floor(k);
    let ceil_div = |c: &BigInt, k: &BigInt| -(-c).div_floor(k);
    if let (Some((var, k)), Some(c)) = (scaled_var(terms, lhs), int_const_value(terms, rhs)) {
        // k·v <= c - step
        let c = c - step;
        let (lower, upper) = if k.is_positive() {
            (None, Some(floor_div(&c, &k)))
        } else {
            (Some(ceil_div(&c, &k)), None)
        };
        return Some(ConstantAtom::Bound { var, lower, upper });
    }
    let (Some(c), Some((var, k))) = (int_const_value(terms, lhs), scaled_var(terms, rhs)) else {
        return None;
    };
    // c + step <= k·v
    let c = c + step;
    let (lower, upper) = if k.is_positive() {
        (Some(ceil_div(&c, &k)), None)
    } else {
        (None, Some(floor_div(&c, &k)))
    };
    Some(ConstantAtom::Bound { var, lower, upper })
}

/// `(distinct ...)` of ONE Int variable and pairwise distinct Int constants:
/// the variable and how many values it must avoid. Anything else (a
/// repeated argument, which makes the atom false; a second variable) is not
/// a constant atom.
fn distinct_from_constants(terms: &TermStore, args: &[TermId]) -> Option<ConstantAtom> {
    let mut var = None;
    let mut constants = Vec::with_capacity(args.len());
    for &arg in args {
        if is_int_var(terms, arg) {
            if var.replace(arg).is_some() {
                return None;
            }
        } else {
            constants.push(int_const_value(terms, arg)?);
        }
    }
    let var = var?;
    let excluded = constants.len();
    constants.sort_unstable();
    constants.dedup();
    (excluded >= 1 && constants.len() == excluded)
        .then_some(ConstantAtom::Disequality { var, excluded })
}

fn constant_atom(terms: &TermStore, atom: TermId) -> Option<ConstantAtom> {
    // (variable, constant, whether the variable is the left operand)
    let var_and_constant = |a: TermId, b: TermId| {
        if is_int_var(terms, a) {
            Some((a, int_const_value(terms, b)?, true))
        } else if is_int_var(terms, b) {
            Some((b, int_const_value(terms, a)?, false))
        } else {
            None
        }
    };
    match terms.get(atom) {
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2 && matches!(name.as_str(), "<" | "<=" | ">" | ">=") =>
        {
            // `a > b` is `b < a`: every order becomes `lhs (<|<=) rhs`.
            let (lhs, rhs) = match name.as_str() {
                "<" | "<=" => (args[0], args[1]),
                _ => (args[1], args[0]),
            };
            scaled_bound(terms, lhs, rhs, matches!(name.as_str(), "<" | ">"))
        }
        TermData::App(Symbol::Named(name), args) if args.len() == 2 && name == "=" => {
            if let Some((var, c, _)) = var_and_constant(args[0], args[1]) {
                return Some(ConstantAtom::Bound {
                    var,
                    lower: Some(c.clone()),
                    upper: Some(c),
                });
            }
            let (a, a_offset) = var_plus_constant(terms, args[0])?;
            let (b, b_offset) = var_plus_constant(terms, args[1])?;
            Some(ConstantAtom::Offset {
                a,
                b,
                offset: b_offset - a_offset,
            })
        }
        TermData::App(Symbol::Named(name), args) if args.len() >= 2 && name == "distinct" => {
            distinct_from_constants(terms, args)
        }
        TermData::Not(inner) => match terms.get(*inner) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 && name == "=" => {
                let (var, _, _) = var_and_constant(args[0], args[1])?;
                Some(ConstantAtom::Disequality { var, excluded: 1 })
            }
            // The negation of a one-sided bound is the opposite one:
            // `not (v <= u)` is `v >= u + 1`, `not (v >= l)` is `v <= l - 1`.
            _ => match constant_atom(terms, *inner)? {
                ConstantAtom::Bound {
                    var,
                    lower: None,
                    upper: Some(u),
                } => Some(ConstantAtom::Bound {
                    var,
                    lower: Some(u + BigInt::one()),
                    upper: None,
                }),
                ConstantAtom::Bound {
                    var,
                    lower: Some(l),
                    upper: None,
                } => Some(ConstantAtom::Bound {
                    var,
                    lower: None,
                    upper: Some(l - BigInt::one()),
                }),
                _ => None,
            },
        },
        _ => None,
    }
}

/// A comparison of ONE Int variable with constants that need not be
/// asserted (under a connective, an `ite` condition, a Bool definition):
/// the variable and the constants where the atom's truth can change.
/// `v >= l` changes only between `l - 1` and `l`, `v <= u` only between `u`
/// and `u + 1`, `v = c` and `(distinct v c ..)` only at each `c`, so the atom
/// is constant on every cell of the partition of the integers by these
/// points (each point alone, each run strictly between two neighbours, and
/// the two unbounded ends). A comparison between two variables is not one.
fn split_points(terms: &TermStore, atom: TermId) -> Option<(TermId, Vec<BigInt>)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
        return None;
    };
    if name == "distinct" && args.len() >= 2 {
        let mut var = None;
        let mut points = Vec::with_capacity(args.len() - 1);
        for &arg in args {
            if is_int_var(terms, arg) {
                if var.replace(arg).is_some() {
                    return None;
                }
            } else {
                points.push(int_const_value(terms, arg)?);
            }
        }
        return Some((var?, points));
    }
    match constant_atom(terms, atom)? {
        ConstantAtom::Bound { var, lower, upper } => {
            Some((var, lower.into_iter().chain(upper).collect()))
        }
        ConstantAtom::Disequality { .. } | ConstantAtom::Offset { .. } => None,
    }
}

/// Where each Int variable is read: inside an `int2bv` argument polynomial
/// (with the widest such `int2bv`), by a constant comparison that is not
/// asserted ([`split_points`]), or anywhere else.
#[derive(Default)]
struct ResidueCensus {
    residue_width: HashMap<TermId, u32>,
    split_points: HashMap<TermId, Vec<BigInt>>,
    elsewhere: HashSet<TermId>,
    seen: HashSet<(TermId, Option<u32>)>,
}

impl ResidueCensus {
    /// `residue_width` is `Some(w)` while the walk is inside the Int argument
    /// of an `int2bv_w`, reached from it through `+`, `-` and `*` only.
    fn visit(&mut self, terms: &TermStore, term: TermId, residue_width: Option<u32>) {
        if !self.seen.insert((term, residue_width)) {
            return;
        }
        if is_int_var(terms, term) {
            match residue_width {
                Some(w) => {
                    self.residue_width
                        .entry(term)
                        .and_modify(|seen_w| *seen_w = (*seen_w).max(w))
                        .or_insert(w);
                }
                None => {
                    self.elsewhere.insert(term);
                }
            }
            return;
        }
        // Outside an `int2bv` argument a constant comparison of one variable
        // is read through its split points only, whatever its polarity.
        if residue_width.is_none() {
            if let Some((var, points)) = split_points(terms, term) {
                self.split_points.entry(var).or_default().extend(points);
                return;
            }
        }
        if let Some((w, arg)) = is_int2bv(terms, term) {
            self.visit(terms, arg, Some(w));
            return;
        }
        let polynomial = residue_width.is_some()
            && matches!(
                terms.get(term),
                TermData::App(Symbol::Named(name), _) if matches!(name.as_str(), "+" | "-" | "*")
            );
        let inherited = if polynomial { residue_width } else { None };
        for child in children(terms, term) {
            self.visit(terms, child, inherited);
        }
    }
}

/// Union-find with offsets over offset equalities: `var = parent + offset`.
#[derive(Default)]
struct OffsetClasses {
    parent: HashMap<TermId, (TermId, BigInt)>,
    /// Roots (at the time) of classes two equalities disagree on.
    inconsistent: Vec<TermId>,
}

impl OffsetClasses {
    /// The class root of `var` and `var`'s offset from it.
    fn find(&mut self, var: TermId) -> (TermId, BigInt) {
        let Some((up, offset)) = self.parent.get(&var).cloned() else {
            return (var, BigInt::zero());
        };
        if up == var {
            return (var, BigInt::zero());
        }
        let (root, up_offset) = self.find(up);
        let total = offset + up_offset;
        self.parent.insert(var, (root, total.clone()));
        (root, total)
    }

    /// Record `a = b + offset`.
    fn link(&mut self, a: TermId, b: TermId, offset: &BigInt) {
        let (ra, oa) = self.find(a);
        let (rb, ob) = self.find(b);
        if ra == rb {
            // a = r + oa and b = r + ob, so a = b + offset needs oa = ob + offset.
            if oa != ob + offset {
                self.inconsistent.push(ra);
            }
        } else {
            // ra = a - oa = b + offset - oa = rb + (ob + offset - oa).
            self.parent.insert(ra, (rb, ob + offset - oa));
        }
    }
}

/// One class's constant atoms, moved onto its root.
#[derive(Default)]
struct ClassBounds {
    residue_width: u32,
    lower: Option<BigInt>,
    upper: Option<BigInt>,
    /// Values excluded by the class's disequality atoms, counted per value.
    disequalities: usize,
    /// The split points of its members' unasserted constant comparisons,
    /// moved onto the root.
    split_points: Vec<BigInt>,
    /// Some member is read outside `int2bv` polynomials and constant atoms.
    read_elsewhere: bool,
    /// Two offset equalities disagree on a member's offset.
    inconsistent: bool,
}

impl ClassBounds {
    /// `member = root + offset`: `member >= l` iff `root >= l - offset`.
    fn add_bound(&mut self, lower: Option<&BigInt>, upper: Option<&BigInt>, offset: &BigInt) {
        if let Some(l) = lower {
            let moved = l - offset;
            self.lower = Some(self.lower.take().map_or(moved.clone(), |c| c.max(moved)));
        }
        if let Some(u) = upper {
            let moved = u - offset;
            self.upper = Some(self.upper.take().map_or(moved.clone(), |c| c.min(moved)));
        }
    }

    /// The root's interval: the real one when both sides are bounded (`None`
    /// when it is empty). Otherwise every run between the bound and the split
    /// points, whole, and on each unbounded side the synthetic
    /// `(k+1) * 2^wmax` integers past the last bound or split point there
    /// (from 0 when there is neither).
    ///
    /// Exact: a model value `r` of the root lies in one cell of the
    /// partition by the split points (which fixes every unasserted
    /// comparison) and in one residue class mod `2^wmax` (which fixes every
    /// `int2bv` polynomial). A point or a bounded run is inside the interval,
    /// so `r` itself is; an unbounded run meets it in `(k+1) * 2^wmax`
    /// consecutive integers within the asserted bound, `k+1` of them in
    /// `r`'s class, and the `k` asserted disequalities exclude at most `k`.
    fn root_interval(&self) -> Option<Interval> {
        let span = (BigInt::from(self.disequalities) + BigInt::one()) << self.residue_width;
        let lowest = self.split_points.iter().min();
        let highest = self.split_points.iter().max();
        match (&self.lower, &self.upper) {
            (Some(lo), Some(hi)) => (lo <= hi).then(|| Interval {
                lo: lo.clone(),
                hi: hi.clone(),
            }),
            (Some(lo), None) => {
                // The unbounded run starts past the highest point at or
                // above `lo`; points below `lo` cut no feasible value.
                let start = match highest {
                    Some(point) if point >= lo => point + BigInt::one(),
                    _ => lo.clone(),
                };
                Some(Interval {
                    lo: lo.clone(),
                    hi: start + &span - BigInt::one(),
                })
            }
            (None, Some(hi)) => {
                let end = match lowest {
                    Some(point) if point <= hi => point - BigInt::one(),
                    _ => hi.clone(),
                };
                Some(Interval {
                    lo: end - &span + BigInt::one(),
                    hi: hi.clone(),
                })
            }
            (None, None) => match (lowest, highest) {
                (Some(lowest), Some(highest)) => Some(Interval {
                    lo: lowest - &span,
                    hi: highest + &span,
                }),
                _ => Some(Interval {
                    lo: BigInt::zero(),
                    hi: span - BigInt::one(),
                }),
            },
        }
    }
}

/// The intervals of the HALF-BOUNDED variables (module doc), per variable.
///
/// A variable qualifies when every occurrence is a top-level
/// [`ConstantAtom`], an unasserted comparison with constants
/// ([`split_points`]), or lies inside the Int argument of an `int2bv`,
/// reached from it through `+`, `-` and `*` only (integer polynomials respect
/// congruences, so `int2bv_w(p(x))` depends on `x` only through
/// `x mod 2^w`). Offset equalities join variables into classes
/// `m = r + off_m`; a class qualifies when all of its members do and its
/// offsets are consistent. Its bounds, disequalities and split points, moved
/// onto `r`, give `r` its interval ([`ClassBounds::root_interval`]), and each
/// member gets that interval shifted by `off_m`. A class with consistent
/// offsets that is bounded on both sides qualifies whatever else reads its
/// members: its real interval needs no restriction on them.
fn half_bounded_intervals(terms: &TermStore, roots: &[TermId]) -> HashMap<TermId, Interval> {
    let mut census = ResidueCensus::default();
    let mut atoms = Vec::new();
    for conjunct in top_level_conjuncts(terms, roots) {
        match constant_atom(terms, conjunct) {
            Some(atom) => atoms.push(atom),
            None => census.visit(terms, conjunct, None),
        }
    }

    let mut offsets = OffsetClasses::default();
    let mut members: Vec<TermId> = census.residue_width.keys().copied().collect();
    members.extend(census.split_points.keys().copied());
    for atom in &atoms {
        match atom {
            ConstantAtom::Bound { var, .. } | ConstantAtom::Disequality { var, .. } => {
                members.push(*var);
            }
            ConstantAtom::Offset { a, b, offset } => {
                members.extend([*a, *b]);
                offsets.link(*a, *b, offset);
            }
        }
    }
    members.sort_unstable_by_key(|var| var.0);
    members.dedup();

    let mut classes: HashMap<TermId, ClassBounds> = HashMap::default();
    let mut root_of: HashMap<TermId, (TermId, BigInt)> = HashMap::default();
    for &var in &members {
        let (root, offset) = offsets.find(var);
        root_of.insert(var, (root, offset.clone()));
        let class = classes.entry(root).or_default();
        class.read_elsewhere |= census.elsewhere.contains(&var);
        if let Some(&w) = census.residue_width.get(&var) {
            class.residue_width = class.residue_width.max(w);
        }
        // `member ⋈ c` iff `root ⋈ c - offset`.
        if let Some(points) = census.split_points.get(&var) {
            class
                .split_points
                .extend(points.iter().map(|point| point - &offset));
        }
    }
    for stale_root in offsets.inconsistent.clone() {
        let (root, _) = offsets.find(stale_root);
        classes.entry(root).or_default().inconsistent = true;
    }
    for atom in &atoms {
        match atom {
            ConstantAtom::Bound { var, lower, upper } => {
                let (root, offset) = &root_of[var];
                classes
                    .entry(*root)
                    .or_default()
                    .add_bound(lower.as_ref(), upper.as_ref(), offset);
            }
            ConstantAtom::Disequality { var, excluded } => {
                classes.entry(root_of[var].0).or_default().disequalities += excluded;
            }
            ConstantAtom::Offset { .. } => {}
        }
    }

    let mut out = HashMap::default();
    for &var in &members {
        let (root, offset) = &root_of[&var];
        let class = &classes[root];
        // A synthetic window is exact only because nothing but `int2bv`
        // polynomials and constant atoms reads the members; a class bounded
        // on BOTH sides gets its real interval, which is exact whatever else
        // reads them.
        let two_sided = class.lower.is_some() && class.upper.is_some();
        if class.inconsistent || (class.read_elsewhere && !two_sided) {
            continue;
        }
        let Some(root_interval) = class.root_interval() else {
            continue;
        };
        out.insert(
            var,
            Interval {
                lo: &root_interval.lo + offset,
                hi: &root_interval.hi + offset,
            },
        );
    }
    out
}

/// Top-level conjuncts of the roots (`and` flattened), the only place a fact
/// is asserted unconditionally.
fn top_level_conjuncts(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    fn visit(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) {
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                for &arg in args {
                    visit(terms, arg, out);
                }
            }
            _ => out.push(term),
        }
    }
    let mut out = Vec::new();
    for &root in roots {
        visit(terms, root, &mut out);
    }
    out
}

/// Interval of an Int-sorted term under the current variable bounds, or
/// `None` when it is not bounded by the supported fragment.
fn interval_of(
    terms: &TermStore,
    term: TermId,
    bounds: &HashMap<TermId, Interval>,
    memo: &mut HashMap<TermId, Option<Interval>>,
) -> Option<Interval> {
    if let Some(cached) = memo.get(&term) {
        return cached.clone();
    }
    // Guard against re-entrancy in a malformed DAG.
    memo.insert(term, None);
    let result = interval_of_inner(terms, term, bounds, memo);
    memo.insert(term, result.clone());
    result
}

fn interval_of_inner(
    terms: &TermStore,
    term: TermId,
    bounds: &HashMap<TermId, Interval>,
    memo: &mut HashMap<TermId, Option<Interval>>,
) -> Option<Interval> {
    if *terms.sort(term) != Sort::Int {
        return None;
    }
    match terms.get(term).clone() {
        TermData::Const(Constant::Int(v)) => Some(Interval::point(v)),
        TermData::Var(_, _) => bounds.get(&term).cloned(),
        TermData::Ite(_, t, e) => {
            let t = interval_of(terms, t, bounds, memo)?;
            let e = interval_of(terms, e, bounds, memo)?;
            Some(t.hull(&e))
        }
        TermData::App(Symbol::Named(name), args) => match name.as_str() {
            "bv2nat" if args.len() == 1 => {
                let width = terms.sort(args[0]).bitvec_width()?;
                Some(Interval {
                    lo: BigInt::zero(),
                    hi: (BigInt::one() << width) - BigInt::one(),
                })
            }
            "+" if !args.is_empty() => {
                let mut acc = interval_of(terms, args[0], bounds, memo)?;
                for &arg in &args[1..] {
                    acc = acc.add(&interval_of(terms, arg, bounds, memo)?);
                }
                Some(acc)
            }
            "-" if !args.is_empty() => {
                let first = interval_of(terms, args[0], bounds, memo)?;
                if args.len() == 1 {
                    return Some(first.neg());
                }
                let mut acc = first;
                for &arg in &args[1..] {
                    acc = acc.sub(&interval_of(terms, arg, bounds, memo)?);
                }
                Some(acc)
            }
            "*" if !args.is_empty() => {
                let (constant, symbolic) = split_constant_product(terms, &args)?;
                match symbolic {
                    None => Some(Interval::point(constant)),
                    Some(t) => Some(interval_of(terms, t, bounds, memo)?.scale(&constant)),
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Split a product into its constant factor and at most ONE symbolic factor
/// (a linear term). Two symbolic factors are nonlinear: decline.
fn split_constant_product(terms: &TermStore, args: &[TermId]) -> Option<(BigInt, Option<TermId>)> {
    let mut constant = BigInt::one();
    let mut symbolic = None;
    for &arg in args {
        match int_const_value(terms, arg) {
            Some(c) => constant *= c,
            None => {
                if symbolic.is_some() {
                    return None;
                }
                symbolic = Some(arg);
            }
        }
    }
    Some((constant, symbolic))
}

/// Proven bounds for Int variables: the comparison facts of the roots
/// (`collect_int_facts`) tightened through the top-level Int equalities.
fn infer_var_bounds(terms: &TermStore, roots: &[TermId]) -> HashMap<TermId, Interval> {
    let facts = collect_int_facts(terms, roots);
    let occurrences = census_int_vars(terms, roots);
    let mut bounds: HashMap<TermId, Interval> = HashMap::default();
    for &var in occurrences
        .arithmetic
        .iter()
        .chain(occurrences.int2bv_width.keys())
    {
        if let (Some(lo), Some(hi)) = (facts.lower_bound(var), facts.upper_bound(var)) {
            bounds.insert(
                var,
                Interval {
                    lo: lo.clone(),
                    hi: hi.clone(),
                },
            );
        }
    }

    let equalities: Vec<(TermId, TermId)> = top_level_conjuncts(terms, roots)
        .into_iter()
        .filter_map(|conjunct| match terms.get(conjunct) {
            TermData::App(Symbol::Named(name), args)
                if name == "=" && args.len() == 2 && *terms.sort(args[0]) == Sort::Int =>
            {
                Some((args[0], args[1]))
            }
            _ => None,
        })
        .collect();
    if equalities.is_empty() {
        return bounds;
    }

    for _ in 0..BOUND_PROPAGATION_ROUNDS {
        let mut changed = false;
        let mut memo = HashMap::default();
        for &(lhs, rhs) in &equalities {
            let lhs_iv = interval_of(terms, lhs, &bounds, &mut memo);
            let rhs_iv = interval_of(terms, rhs, &bounds, &mut memo);
            for (var, other) in [(lhs, rhs_iv.as_ref()), (rhs, lhs_iv.as_ref())] {
                let Some(other) = other else {
                    continue;
                };
                if !is_int_var(terms, var) {
                    continue;
                }
                let tightened = match bounds.get(&var) {
                    Some(current) => current.meet(other),
                    None => other.clone(),
                };
                if bounds.get(&var) != Some(&tightened) {
                    bounds.insert(var, tightened);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    bounds
}

impl IntBlastPlan {
    /// Classify every Int variable and choose the common signed width, or
    /// `None` when some Int variable is neither bounded nor residue-only, or
    /// some Int-sorted subterm falls outside the supported fragment.
    fn analyze(terms: &TermStore, roots: &[TermId]) -> Option<Self> {
        let occurrences = census_int_vars(terms, roots);
        let mut bounds = infer_var_bounds(terms, roots);

        let mut encodings: HashMap<TermId, IntVarEncoding> = HashMap::default();
        let mut width = 2u32;
        for (&var, &w) in &occurrences.int2bv_width {
            if occurrences.arithmetic.contains(&var) {
                continue;
            }
            match bounds.get(&var) {
                // A bounded variable stays bounded even when every occurrence
                // is an `int2bv` argument: the bound facts must be honoured.
                Some(_) => {
                    encodings.insert(var, IntVarEncoding::Bounded);
                }
                None => {
                    encodings.insert(var, IntVarEncoding::ResidueOnly { width: w });
                    width = width.max(w.checked_add(1)?);
                }
            }
        }
        let mut synthetic = Vec::new();
        let mut half_bounded: Option<HashMap<TermId, Interval>> = None;
        for &var in &occurrences.arithmetic {
            if !bounds.contains_key(&var) {
                let interval = half_bounded
                    .get_or_insert_with(|| half_bounded_intervals(terms, roots))
                    .get(&var)?
                    .clone();
                bounds.insert(var, interval.clone());
                synthetic.push((var, interval));
            }
            encodings.insert(var, IntVarEncoding::Bounded);
        }
        synthetic.sort_unstable_by_key(|(var, _)| var.0);

        // Every Int-sorted subterm must have a proven interval that fits, and
        // every conversion width must be strictly below W.
        let mut memo = HashMap::default();
        let mut seen = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if let Some((w, arg)) = is_int2bv(terms, term) {
                width = width.max(w.checked_add(1)?);
                if is_int_var(terms, arg)
                    && matches!(
                        encodings.get(&arg),
                        Some(IntVarEncoding::ResidueOnly { .. })
                    )
                {
                    continue;
                }
            }
            if let Some(arg) = is_bv2nat(terms, term) {
                let w = terms.sort(arg).bitvec_width()?;
                width = width.max(w.checked_add(1)?);
            }
            if *terms.sort(term) == Sort::Int {
                let interval = interval_of(terms, term, &bounds, &mut memo)?;
                width = width.max(interval.signed_width());
            }
            stack.extend(children(terms, term));
        }
        if width > INT_BLAST_MAX_WIDTH {
            return None;
        }
        Some(Self {
            encodings,
            width,
            synthetic,
        })
    }
}

/// Int→BV translator over a fixed plan. Every method returns `None` to
/// decline; nothing is asserted on a decline.
struct IntBlaster<'a> {
    terms: &'a mut TermStore,
    plan: IntBlastPlan,
    /// Bounded Int var → its signed W-bit vector; residue-only var → its free
    /// residue vector.
    var_bv: HashMap<TermId, TermId>,
    memo: HashMap<TermId, TermId>,
    /// Translate a product of two or more symbolic factors with `bvmul`
    /// instead of declining. Only the small-box NIA lane (`int_blast_box.rs`)
    /// sets it, and only with a plan whose width bounds every product's
    /// interval, so the product cannot wrap.
    nonlinear_products: bool,
}

impl<'a> IntBlaster<'a> {
    fn new(terms: &'a mut TermStore, plan: IntBlastPlan) -> Self {
        Self {
            terms,
            plan,
            var_bv: HashMap::default(),
            memo: HashMap::default(),
            nonlinear_products: false,
        }
    }

    fn width(&self) -> u32 {
        self.plan.width
    }

    fn var_vector(&mut self, var: TermId) -> Option<TermId> {
        if let Some(&bv) = self.var_bv.get(&var) {
            return Some(bv);
        }
        let (kind, width) = match self.plan.encodings.get(&var)? {
            IntVarEncoding::Bounded => (BvLiaAuxVar::BoundedBlastVector, self.plan.width),
            IntVarEncoding::ResidueOnly { width } => (BvLiaAuxVar::ResidueBlastVector, *width),
        };
        let bv = mint_bv_lia_aux_var(self.terms, kind, Sort::bitvec(width));
        self.var_bv.insert(var, bv);
        Some(bv)
    }

    fn translate(&mut self, term: TermId) -> Option<TermId> {
        if let Some(&t) = self.memo.get(&term) {
            return Some(t);
        }
        let sort = self.terms.sort(term).clone();
        let translated = match sort {
            Sort::Bool => self.translate_bool(term),
            Sort::Int => self.translate_int(term),
            Sort::BitVec(_) => self.translate_bv(term),
            _ => None,
        }?;
        self.memo.insert(term, translated);
        Some(translated)
    }

    fn translate_all(&mut self, args: &[TermId]) -> Option<Vec<TermId>> {
        args.iter().map(|&arg| self.translate(arg)).collect()
    }

    fn translate_bool(&mut self, term: TermId) -> Option<TermId> {
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Bool(_)) | TermData::Var(_, _) => Some(term),
            TermData::Not(inner) => {
                let inner = self.translate(inner)?;
                Some(self.terms.mk_not(inner))
            }
            TermData::Ite(c, t, e) => {
                let c = self.translate(c)?;
                let t = self.translate(t)?;
                let e = self.translate(e)?;
                Some(self.terms.mk_ite(c, t, e))
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "and" => {
                    let args = self.translate_all(&args)?;
                    Some(self.terms.mk_and(args))
                }
                "or" => {
                    let args = self.translate_all(&args)?;
                    Some(self.terms.mk_or(args))
                }
                "not" if args.len() == 1 => {
                    let inner = self.translate(args[0])?;
                    Some(self.terms.mk_not(inner))
                }
                "xor" if args.len() >= 2 => {
                    let args = self.translate_all(&args)?;
                    let mut iter = args.into_iter();
                    let mut acc = iter.next()?;
                    for arg in iter {
                        acc = self.terms.mk_xor(acc, arg);
                    }
                    Some(acc)
                }
                "=>" | "implies" if args.len() >= 2 => {
                    // Right-associative: (=> a b c) = (=> a (=> b c)).
                    let args = self.translate_all(&args)?;
                    let mut iter = args.into_iter().rev();
                    let mut acc = iter.next()?;
                    for arg in iter {
                        acc = self.terms.mk_implies(arg, acc);
                    }
                    Some(acc)
                }
                "=" if args.len() >= 2 => {
                    if !self.equality_sort_supported(args[0]) {
                        return None;
                    }
                    let args = self.translate_all(&args)?;
                    let mut conjuncts = Vec::with_capacity(args.len() - 1);
                    for pair in args.windows(2) {
                        conjuncts.push(self.terms.mk_eq(pair[0], pair[1]));
                    }
                    if conjuncts.len() == 1 {
                        Some(conjuncts[0])
                    } else {
                        Some(self.terms.mk_and(conjuncts))
                    }
                }
                "distinct" if args.len() >= 2 => {
                    if !self.equality_sort_supported(args[0]) {
                        return None;
                    }
                    let args = self.translate_all(&args)?;
                    Some(self.terms.mk_distinct(args))
                }
                "<" | "<=" | ">" | ">=" if args.len() == 2 => {
                    if *self.terms.sort(args[0]) != Sort::Int {
                        return None;
                    }
                    let lhs = self.translate(args[0])?;
                    let rhs = self.translate(args[1])?;
                    // Signed W-bit order is the exact Int order: no operand
                    // wraps at the chosen width.
                    Some(match name.as_str() {
                        "<" => self.terms.mk_bvslt(lhs, rhs),
                        "<=" => self.terms.mk_bvsle(lhs, rhs),
                        ">" => self.terms.mk_bvsgt(lhs, rhs),
                        _ => self.terms.mk_bvsge(lhs, rhs),
                    })
                }
                "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
                    if args.len() == 2 =>
                {
                    let args = self.translate_all(&args)?;
                    self.rebuild_bv_app(&Symbol::Named(name.clone()), args)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn equality_sort_supported(&self, arg: TermId) -> bool {
        matches!(
            self.terms.sort(arg),
            Sort::Bool | Sort::Int | Sort::BitVec(_)
        )
    }

    /// Int-sorted term → signed W-bit vector.
    fn translate_int(&mut self, term: TermId) -> Option<TermId> {
        let width = self.width();
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Int(v)) => Some(self.terms.mk_bitvec(v, width)),
            TermData::Var(_, _) => match *self.plan.encodings.get(&term)? {
                IntVarEncoding::Bounded => self.var_vector(term),
                // A residue-only variable never occurs in Int context.
                IntVarEncoding::ResidueOnly { .. } => None,
            },
            TermData::Ite(c, t, e) => {
                let c = self.translate(c)?;
                let t = self.translate(t)?;
                let e = self.translate(e)?;
                Some(self.terms.mk_ite(c, t, e))
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "bv2nat" if args.len() == 1 => {
                    let w = self.terms.sort(args[0]).bitvec_width()?;
                    let bv = self.translate(args[0])?;
                    if width <= w {
                        return None;
                    }
                    Some(self.terms.mk_bvzero_extend(width - w, bv))
                }
                "+" if !args.is_empty() => {
                    let args = self.translate_all(&args)?;
                    let mut iter = args.into_iter();
                    let mut acc = iter.next()?;
                    for arg in iter {
                        acc = self.terms.mk_bvadd(vec![acc, arg]);
                    }
                    Some(acc)
                }
                "-" if !args.is_empty() => {
                    let unary = args.len() == 1;
                    let args = self.translate_all(&args)?;
                    let mut iter = args.into_iter();
                    let first = iter.next()?;
                    if unary {
                        return Some(self.terms.mk_bvneg(first));
                    }
                    let mut acc = first;
                    for arg in iter {
                        acc = self.terms.mk_bvsub(vec![acc, arg]);
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let Some((constant, symbolic)) = split_constant_product(self.terms, &args)
                    else {
                        if !self.nonlinear_products {
                            return None;
                        }
                        let args = self.translate_all(&args)?;
                        return fold_binary(self.terms, args, |t, a, b| t.mk_bvmul(vec![a, b]));
                    };
                    let constant_bv = self.terms.mk_bitvec(constant.clone(), width);
                    match symbolic {
                        None => Some(constant_bv),
                        Some(t) => {
                            let t = self.translate(t)?;
                            if constant.is_one() {
                                Some(t)
                            } else {
                                Some(self.terms.mk_bvmul(vec![constant_bv, t]))
                            }
                        }
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// BitVec-sorted term: rewrite the `int2bv` seams, rebuild every
    /// FixedSizeBitVectors operator, decline anything else.
    fn translate_bv(&mut self, term: TermId) -> Option<TermId> {
        if let Some((w, arg)) = is_int2bv(self.terms, term) {
            let source = if is_int_var(self.terms, arg) {
                match *self.plan.encodings.get(&arg)? {
                    IntVarEncoding::ResidueOnly { width } => {
                        let residue = self.var_vector(arg)?;
                        return if w == width {
                            Some(residue)
                        } else if w < width {
                            Some(self.terms.mk_bvextract(w - 1, 0, residue))
                        } else {
                            None
                        };
                    }
                    IntVarEncoding::Bounded => self.translate(arg)?,
                }
            } else {
                self.translate(arg)?
            };
            let width = self.width();
            // Low `w` bits of the two's-complement W-bit value are exactly
            // `arg mod 2^w`, for either sign, since W > w.
            return if w < width {
                Some(self.terms.mk_bvextract(w - 1, 0, source))
            } else if w == width {
                Some(source)
            } else {
                None
            };
        }
        match self.terms.get(term).clone() {
            // A leaf is the same term on both sides of the translation. An
            // operator is never passed through verbatim — even one with no
            // Int beneath it — so that a UF application, a `select` or a
            // datatype selector declines in `rebuild_bv_app` rather than reach
            // the `qf_bv` blaster, which asserts no congruence or array axioms
            // and about whose reading of such a term this module claims nothing.
            TermData::Const(_) | TermData::Var(_, _) => Some(term),
            TermData::Ite(c, t, e) => {
                let c = self.translate(c)?;
                let t = self.translate(t)?;
                let e = self.translate(e)?;
                Some(self.terms.mk_ite(c, t, e))
            }
            TermData::App(sym, args) => {
                let args = self.translate_all(&args)?;
                self.rebuild_bv_app(&sym, args)
            }
            _ => None,
        }
    }

    /// Rebuild a BitVec operation over translated operands through the same
    /// constructors the frontend uses, so the bit-blaster sees canonical terms.
    /// Unknown operators decline.
    fn rebuild_bv_app(&mut self, sym: &Symbol, args: Vec<TermId>) -> Option<TermId> {
        let terms = &mut *self.terms;
        match sym {
            Symbol::Named(name) => match (name.as_str(), args.as_slice()) {
                ("bvand", [_, _, ..]) => {
                    fold_binary(terms, args.clone(), |t, a, b| t.mk_bvand(vec![a, b]))
                }
                ("bvor", [_, _, ..]) => {
                    fold_binary(terms, args.clone(), |t, a, b| t.mk_bvor(vec![a, b]))
                }
                ("bvxor", [_, _, ..]) => {
                    fold_binary(terms, args.clone(), |t, a, b| t.mk_bvxor(vec![a, b]))
                }
                ("bvadd", [_, _, ..]) => {
                    fold_binary(terms, args.clone(), |t, a, b| t.mk_bvadd(vec![a, b]))
                }
                ("bvsub", [_, _, ..]) => {
                    fold_binary(terms, args.clone(), |t, a, b| t.mk_bvsub(vec![a, b]))
                }
                ("bvmul", [_, _, ..]) => {
                    fold_binary(terms, args.clone(), |t, a, b| t.mk_bvmul(vec![a, b]))
                }
                ("bvnand", [a, b]) => Some(terms.mk_bvnand(vec![*a, *b])),
                ("bvnor", [a, b]) => Some(terms.mk_bvnor(vec![*a, *b])),
                ("bvxnor", [a, b]) => Some(terms.mk_bvxnor(vec![*a, *b])),
                ("bvnot", [a]) => Some(terms.mk_bvnot(*a)),
                ("bvneg", [a]) => Some(terms.mk_bvneg(*a)),
                ("bvshl", [a, b]) => Some(terms.mk_bvshl(vec![*a, *b])),
                ("bvlshr", [a, b]) => Some(terms.mk_bvlshr(vec![*a, *b])),
                ("bvashr", [a, b]) => Some(terms.mk_bvashr(vec![*a, *b])),
                ("bvudiv", [a, b]) => Some(terms.mk_bvudiv(vec![*a, *b])),
                ("bvurem", [a, b]) => Some(terms.mk_bvurem(vec![*a, *b])),
                ("bvsdiv", [a, b]) => Some(terms.mk_bvsdiv(vec![*a, *b])),
                ("bvsrem", [a, b]) => Some(terms.mk_bvsrem(vec![*a, *b])),
                ("bvsmod", [a, b]) => Some(terms.mk_bvsmod(vec![*a, *b])),
                ("bvcomp", [a, b]) => Some(terms.mk_bvcomp(*a, *b)),
                ("concat", [_, _, ..]) => Some(terms.mk_bvconcat(args.clone())),
                ("bvult", [a, b]) => Some(terms.mk_bvult(*a, *b)),
                ("bvule", [a, b]) => Some(terms.mk_bvule(*a, *b)),
                ("bvugt", [a, b]) => Some(terms.mk_bvugt(*a, *b)),
                ("bvuge", [a, b]) => Some(terms.mk_bvuge(*a, *b)),
                ("bvslt", [a, b]) => Some(terms.mk_bvslt(*a, *b)),
                ("bvsle", [a, b]) => Some(terms.mk_bvsle(*a, *b)),
                ("bvsgt", [a, b]) => Some(terms.mk_bvsgt(*a, *b)),
                ("bvsge", [a, b]) => Some(terms.mk_bvsge(*a, *b)),
                _ => None,
            },
            Symbol::Indexed(name, indices) => {
                match (name.as_str(), indices.as_slice(), args.as_slice()) {
                    ("extract", [high, low], [a]) => Some(terms.mk_bvextract(*high, *low, *a)),
                    ("zero_extend", [i], [a]) => Some(terms.mk_bvzero_extend(*i, *a)),
                    ("sign_extend", [i], [a]) => Some(terms.mk_bvsign_extend(*i, *a)),
                    ("rotate_left", [i], [a]) => Some(terms.mk_bvrotate_left(*i, *a)),
                    ("rotate_right", [i], [a]) => Some(terms.mk_bvrotate_right(*i, *a)),
                    ("repeat", [i], [a]) => Some(terms.mk_bvrepeat(*i, *a)),
                    _ => None,
                }
            }
            // `Symbol` is `#[non_exhaustive]`: decline anything unknown.
            _ => None,
        }
    }

    /// Each HALF-BOUNDED variable's synthetic interval, asserted on its signed
    /// W-bit vector (module doc). The translated roots do not carry it: the
    /// bounds they do carry are one-sided.
    fn synthetic_bounds(&mut self) -> Option<Vec<TermId>> {
        let width = self.width();
        let synthetic = self.plan.synthetic.clone();
        let mut constraints = Vec::with_capacity(2 * synthetic.len());
        for (var, interval) in synthetic {
            let vector = self.var_vector(var)?;
            let lo = self.terms.mk_bitvec(interval.lo, width);
            let hi = self.terms.mk_bitvec(interval.hi, width);
            constraints.push(self.terms.mk_bvsge(vector, lo));
            constraints.push(self.terms.mk_bvsle(vector, hi));
        }
        Some(constraints)
    }

    fn into_bindings(self) -> (u32, Vec<(TermId, TermId, IntVarEncoding)>) {
        let mut bindings: Vec<_> = self
            .var_bv
            .iter()
            .filter_map(|(&var, &bv)| Some((var, bv, *self.plan.encodings.get(&var)?)))
            .collect();
        bindings.sort_unstable_by_key(|(var, _, _)| var.0);
        (self.plan.width, bindings)
    }
}

fn fold_binary(
    terms: &mut TermStore,
    args: Vec<TermId>,
    mut f: impl FnMut(&mut TermStore, TermId, TermId) -> TermId,
) -> Option<TermId> {
    let mut iter = args.into_iter();
    let mut acc = iter.next()?;
    for arg in iter {
        acc = f(terms, acc, arg);
    }
    Some(acc)
}

/// Signed two's-complement reading of a width-`width` unsigned value.
fn signed_value(value: BigInt, width: u32) -> BigInt {
    let modulus = BigInt::one() << width;
    let value = ((value % &modulus) + &modulus) % &modulus;
    if value >= (&modulus >> 1u32) {
        value - modulus
    } else {
        value
    }
}

impl Executor {
    /// Decide the bridge `roots` exactly by bounded Int→BV blasting (module
    /// doc). `Ok(None)` means the translator declined or the bit-blaster could
    /// not decide — the caller keeps its previous verdict; solver state is
    /// restored on every path except a validated SAT, which installs the
    /// reconstructed Int model as `last_model`.
    ///
    /// Everything the lane builds lives in a DISPOSABLE executor: the
    /// translation is made in the probe's clone of the term store, never in
    /// the caller's, and no transformed proof or internal solver state crosses
    /// back. That is load-bearing for incremental use. The caller's store is
    /// shared by every later solve of the session and the AUF/LIA search
    /// reads the whole of it, so a translation left behind there changed which
    /// candidate a later `check-sat` found and cost that check its verdict
    /// (2026-09-23 bit-vector verification, `im_275_asis`).
    pub(super) fn solve_bv_lia_by_int_blast(
        &mut self,
        roots: &[TermId],
    ) -> Result<Option<SolveResult>> {
        if self.should_abort_theory_loop() {
            return Ok(None);
        }
        let Some(plan) = IntBlastPlan::analyze(&self.ctx.terms, roots) else {
            return Ok(None);
        };

        // The translated query owns a disposable executor. Its DRAT proof,
        // assumption core, delegated roots and replay state describe the BV
        // residue, so none may become authority for the original Int query.
        let Some(mut probe) = self.int_blast_probe() else {
            return Ok(None);
        };
        // Ids below this bound name the same terms in the probe's clone and in
        // the caller's store; the probe's own terms lie at or above it.
        let shared_terms = self.ctx.terms.len();
        let (translated, (width, bindings)) = {
            let mut blaster = IntBlaster::new(&mut probe.ctx.terms, plan);
            let translated: Option<Vec<TermId>> = roots
                .iter()
                .map(|&root| blaster.translate(root))
                .collect::<Option<Vec<TermId>>>()
                .and_then(|mut translated| {
                    translated.extend(blaster.synthetic_bounds()?);
                    Some(translated)
                });
            (translated, blaster.into_bindings())
        };
        let Some(translated) = translated else {
            return Ok(None);
        };
        probe.ctx.assertions = translated;
        let result = probe.solve_bv_core(BvSolveConfig::qf_bv(), &[]);
        if self.should_abort_theory_loop() {
            return Ok(None);
        }

        let decided = match result {
            Ok(SolveResult::Unsat(_)) => {
                self.last_statistics
                    .set_string("bv_lia_bridge.int_blast", "unsat");
                return Ok(Some(SolveResult::unsat()));
            }
            Ok(SolveResult::Sat) => probe.last_model.take(),
            Ok(SolveResult::Unknown) | Err(ExecutorError::ModelValidation(_)) => None,
            Err(error) => return Err(error),
        };
        let Some(bv_model) = decided else {
            return Ok(None);
        };

        // Map the vectors back to integers: signed value of a bounded
        // variable's W-bit vector, unsigned value of a residue vector (which
        // is itself a witness for every `int2bv` the variable feeds). The
        // vectors are the probe's own terms, so the probe evaluates them.
        let mut values: HashMap<TermId, BigInt> = HashMap::default();
        for (var, bv, encoding) in bindings {
            let EvalValue::BitVec { value, width: got } = probe.evaluate_term(&bv_model, bv) else {
                return Ok(None);
            };
            let value = match encoding {
                IntVarEncoding::Bounded => signed_value(value, width.min(got)),
                IntVarEncoding::ResidueOnly { width: w } => {
                    let modulus = BigInt::one() << w.min(got);
                    ((value % &modulus) + &modulus) % &modulus
                }
            };
            values.insert(var, value);
        }
        drop(probe);
        // Only entries of terms the caller's store shares may cross back: a
        // probe-only id would name an unrelated term once that store grows.
        let Some(mut model) = bv_model.restricted_to_shared_terms(shared_terms) else {
            return Ok(None);
        };
        model.lia_model = Some(LiaModel { values });

        // The strict bridge validator is the SAT authority: only a model that
        // independently re-evaluates every ORIGINAL root to true is published.
        let prior = self.last_model.replace(model);
        if self.bridge_sat_model_validates(roots) {
            self.last_statistics
                .set_string("bv_lia_bridge.int_blast", "sat");
            Ok(Some(SolveResult::Sat))
        } else {
            self.last_model = prior;
            Ok(None)
        }
    }

    /// Clone only within the caller's resource envelope. Term IDs already in
    /// the shared source universe retain their meaning in the candidate model.
    /// The probe starts with no assertions; the caller installs the
    /// translation it builds in the probe's own store.
    fn int_blast_probe(&self) -> Option<Executor> {
        if !crate::memory::probe_clone_fits(self.ctx.terms.true_memory_bytes(), self.memory_limit())
            || self.ctx.terms.true_memory_bytes() > self.predictive_term_clone_budget()
        {
            return None;
        }
        let mut probe = Executor::new();
        probe.ctx = self.ctx.clone();
        probe.random_seed = self.random_seed;
        probe.ctx.assertions = Vec::new();
        probe.set_verification_level(self.verification_level());
        probe.set_self_check(self.self_check());
        probe.set_learned_clause_limit(self.learned_clause_limit());
        probe.set_clause_db_bytes_limit(self.clause_db_bytes_limit());
        probe.set_resource_limit(self.resource_limit());
        probe.set_decision_limit(self.decision_limit());
        probe.set_ground_budget_enabled(self.ground_budget_enabled());
        probe.set_memory_limit(self.memory_limit());
        probe.set_term_memory_limit(self.term_memory_limit());
        probe.set_solve_controls(self.solve_interrupt.clone(), self.current_solve_deadline());
        Some(probe)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signed_value_reads_two_s_complement() {
        assert_eq!(signed_value(BigInt::from(5), 8), BigInt::from(5));
        assert_eq!(signed_value(BigInt::from(255), 8), BigInt::from(-1));
        assert_eq!(signed_value(BigInt::from(128), 8), BigInt::from(-128));
        assert_eq!(signed_value(BigInt::from(127), 8), BigInt::from(127));
    }

    #[test]
    fn interval_signed_width_covers_both_ends() {
        let iv = Interval {
            lo: BigInt::from(-128),
            hi: BigInt::from(127),
        };
        assert_eq!(iv.signed_width(), 9);
        let iv = Interval {
            lo: BigInt::zero(),
            hi: (BigInt::one() << 64u32) - BigInt::one(),
        };
        assert_eq!(iv.signed_width(), 65);
        let iv = Interval::point(BigInt::zero());
        assert_eq!(iv.signed_width(), 1);
    }

    /// `v3 = bv2nat(bvshl 1 (int2bv 64 v0)) ∧ v3 = 1`: `v0` is residue-only,
    /// `v3` is bounded through the equalities, and W clears 64 bits.
    #[test]
    fn plan_classifies_residue_only_and_bounded_vars() {
        let mut terms = TermStore::new();
        let v0 = terms.mk_var("v0", Sort::Int);
        let v3 = terms.mk_var("v3", Sort::Int);
        let one_bv = terms.mk_bitvec(BigInt::one(), 64);
        let conv = terms.mk_int2bv(64, v0);
        let shifted = terms.mk_bvshl(vec![one_bv, conv]);
        let nat = terms.mk_bv2nat(shifted);
        let def = terms.mk_eq(v3, nat);
        let one = terms.mk_int(BigInt::one());
        let pin = terms.mk_eq(v3, one);

        let plan = IntBlastPlan::analyze(&terms, &[def, pin]).expect("in fragment");
        assert!(matches!(
            plan.encodings.get(&v0),
            Some(IntVarEncoding::ResidueOnly { width: 64 })
        ));
        assert!(matches!(
            plan.encodings.get(&v3),
            Some(IntVarEncoding::Bounded)
        ));
        assert!(plan.width >= 65);
    }

    /// A BitVec-sorted operator outside FixedSizeBitVectors (here a UF
    /// application with no Int beneath it) declines: it must never reach the
    /// `qf_bv` blaster verbatim, which asserts no congruence axioms.
    #[test]
    fn translator_declines_uninterpreted_bv_app() {
        let mut terms = TermStore::new();
        let k = terms.mk_var("k", Sort::bitvec(8));
        let x = terms.mk_var("x", Sort::Int);
        let f_k = terms.mk_app(Symbol::named("f"), vec![k], Sort::bitvec(8));
        let conv = terms.mk_int2bv(8, x);
        let masked = terms.mk_bvand(vec![f_k, conv]);
        let nat = terms.mk_bv2nat(masked);
        let def = terms.mk_eq(x, nat);
        let zero = terms.mk_int(BigInt::zero());
        let lo = terms.mk_le(zero, x);
        let bound = terms.mk_int(BigInt::from(256));
        let hi = terms.mk_lt(x, bound);
        let roots = [lo, hi, def];

        let plan = IntBlastPlan::analyze(&terms, &roots).expect("Int side is in fragment");
        let mut blaster = IntBlaster::new(&mut terms, plan);
        assert!(blaster.translate(def).is_none(), "UF app must decline");
        // The pure-BV shape of the same query translates.
        let pure = {
            let terms = &mut *blaster.terms;
            let masked = terms.mk_bvand(vec![k, conv]);
            let nat = terms.mk_bv2nat(masked);
            terms.mk_eq(x, nat)
        };
        assert!(blaster.translate(pure).is_some());
    }

    /// The lane's vectors spell a counter, never the Int variable's `TermId`
    /// (`bv_lia_aux_vars`): a bounded and a residue-only variable.
    #[test]
    fn lane_vectors_spell_a_counter() {
        let mut terms = TermStore::new();
        let v0 = terms.mk_var("v0", Sort::Int);
        let v3 = terms.mk_var("v3", Sort::Int);
        let one_bv = terms.mk_bitvec(BigInt::one(), 64);
        let conv = terms.mk_int2bv(64, v0);
        let shifted = terms.mk_bvshl(vec![one_bv, conv]);
        let nat = terms.mk_bv2nat(shifted);
        let def = terms.mk_eq(v3, nat);
        let one = terms.mk_int(BigInt::one());
        let pin = terms.mk_eq(v3, one);
        let plan = IntBlastPlan::analyze(&terms, &[def, pin]).expect("in fragment");
        let mut blaster = IntBlaster::new(&mut terms, plan);
        let bounded = blaster.var_vector(v3).expect("v3 is bounded");
        let residue = blaster.var_vector(v0).expect("v0 is residue-only");
        for (vector, prefix) in [(bounded, "__ay_bv_lia_ib_"), (residue, "__ay_bv_lia_ir_")] {
            let name = match blaster.terms.get(vector) {
                TermData::Var(name, _) => name.clone(),
                other => format!("{other:?}"),
            };
            assert!(name.starts_with(prefix), "{name}");
            assert!(
                crate::executor::theories::bv_lia_aux_vars::is_bv_lia_aux_var_name(&name),
                "{name}"
            );
        }
        assert!(
            !crate::executor::quantifier_loop::result_mapping::carries_name_encoded_term_ids(
                blaster.terms
            )
        );
    }

    /// `x <= 5 ∧ bv2nat(int2bv_8(x)) > 5` (the D5 witness): `x` is read by a
    /// one-sided bound and an `int2bv`, so it is HALF-BOUNDED on the 256
    /// integers ending at 5; a `(distinct x c)` atom doubles the span, and a
    /// variable read only through `(+ x 3)` under `int2bv` with no bound at
    /// all gets `[0, 2^w)`.
    #[test]
    fn plan_encodes_half_bounded_vars_on_a_synthetic_interval() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let at_most_five = terms.mk_le(x, five);
        let conv = terms.mk_int2bv(8, x);
        let nat = terms.mk_bv2nat(conv);
        let above_five = terms.mk_gt(nat, five);

        let plan =
            IntBlastPlan::analyze(&terms, &[at_most_five, above_five]).expect("x is half-bounded");
        assert!(matches!(
            plan.encodings.get(&x),
            Some(IntVarEncoding::Bounded)
        ));
        assert_eq!(
            plan.synthetic,
            vec![(
                x,
                Interval {
                    lo: BigInt::from(-250),
                    hi: BigInt::from(5),
                }
            )]
        );

        let three = terms.mk_int(BigInt::from(3));
        let not_three = terms.mk_distinct(vec![x, three]);
        let plan = IntBlastPlan::analyze(&terms, &[at_most_five, above_five, not_three])
            .expect("a constant disequality keeps x half-bounded");
        assert_eq!(plan.synthetic[0].1.lo, BigInt::from(5 - 511));

        let y = terms.mk_var("y", Sort::Int);
        let shifted = terms.mk_add(vec![y, three]);
        let conv = terms.mk_int2bv(4, shifted);
        let nat = terms.mk_bv2nat(conv);
        let small = terms.mk_lt(nat, three);
        let plan = IntBlastPlan::analyze(&terms, &[small]).expect("y is read mod 16 only");
        assert_eq!(
            plan.synthetic,
            vec![(
                y,
                Interval {
                    lo: BigInt::zero(),
                    hi: BigInt::from(15),
                }
            )]
        );
    }

    /// Any other reading of the variable keeps the translator out: a bound
    /// against a non-constant, asserted or under `or`, an offset equality
    /// under `or`, an `ite` inside the `int2bv` argument.
    #[test]
    fn plan_declines_half_bounded_vars_read_elsewhere() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let five = terms.mk_int(BigInt::from(5));
        let conv = terms.mk_int2bv(8, x);
        let nat = terms.mk_bv2nat(conv);
        let above_five = terms.mk_gt(nat, five);

        let against_var = terms.mk_le(x, z);
        assert!(IntBlastPlan::analyze(&terms, &[against_var, above_five]).is_none());

        let at_most_five = terms.mk_le(x, five);
        let flag = terms.mk_var("p", Sort::Bool);
        let nested_against_var = terms.mk_or(vec![against_var, flag]);
        assert!(IntBlastPlan::analyze(&terms, &[nested_against_var, above_five]).is_none());

        let one = terms.mk_int(BigInt::one());
        let x_plus_one = terms.mk_add(vec![x, one]);
        let offset = terms.mk_eq(z, x_plus_one);
        let nested_offset = terms.mk_or(vec![offset, flag]);
        let z_bound = terms.mk_ge(z, one);
        assert!(IntBlastPlan::analyze(&terms, &[nested_offset, z_bound, above_five]).is_none());

        let zero = terms.mk_int(BigInt::zero());
        let cond = terms.mk_var("q", Sort::Bool);
        let guarded = terms.mk_ite(cond, x, zero);
        let conv = terms.mk_int2bv(8, guarded);
        let nat = terms.mk_bv2nat(conv);
        let guarded_above = terms.mk_gt(nat, five);
        assert!(IntBlastPlan::analyze(&terms, &[at_most_five, guarded_above]).is_none());

        // Two offset equalities that disagree (`z = x + 1`, `z = x + 2`).
        let one = terms.mk_int(BigInt::one());
        let two = terms.mk_int(BigInt::from(2));
        let x_plus_one = terms.mk_add(vec![x, one]);
        let x_plus_two = terms.mk_add(vec![x, two]);
        let first = terms.mk_eq(z, x_plus_one);
        let second = terms.mk_eq(z, x_plus_two);
        let z_bound = terms.mk_ge(z, one);
        assert!(IntBlastPlan::analyze(&terms, &[first, second, z_bound, above_five]).is_none());
    }

    /// `z = x + 2 ∧ z >= 1 ∧ bv2nat(int2bv_8 x) > 5` (the hunt's `eq-var`
    /// shape): `x` and `z` form one class; `z >= 1` moves onto `x` as
    /// `x >= -1`, so `x` gets the 256 integers from -1 and `z` the same
    /// interval shifted by 2. A second bound on the other member closes it.
    #[test]
    fn plan_moves_bounds_across_offset_equalities() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let one = terms.mk_int(BigInt::one());
        let two = terms.mk_int(BigInt::from(2));
        let five = terms.mk_int(BigInt::from(5));
        let x_plus_two = terms.mk_add(vec![x, two]);
        let link = terms.mk_eq(z, x_plus_two);
        let z_bound = terms.mk_ge(z, one);
        let conv = terms.mk_int2bv(8, x);
        let nat = terms.mk_bv2nat(conv);
        let above_five = terms.mk_gt(nat, five);

        let plan = IntBlastPlan::analyze(&terms, &[link, z_bound, above_five])
            .expect("the class is half-bounded");
        let interval_of = |var: TermId| {
            plan.synthetic
                .iter()
                .find(|(v, _)| *v == var)
                .map(|(_, iv)| iv.clone())
                .expect("both members are encoded")
        };
        assert_eq!(
            interval_of(x),
            Interval {
                lo: BigInt::from(-1),
                hi: BigInt::from(254),
            }
        );
        assert_eq!(
            interval_of(z),
            Interval {
                lo: BigInt::one(),
                hi: BigInt::from(256),
            }
        );

        let x_bound = terms.mk_le(x, five);
        let plan = IntBlastPlan::analyze(&terms, &[link, z_bound, x_bound, above_five])
            .expect("bounded on both sides through the class");
        let x_interval = plan
            .synthetic
            .iter()
            .find(|(v, _)| *v == x)
            .map(|(_, iv)| iv.clone());
        assert_eq!(
            x_interval,
            Some(Interval {
                lo: BigInt::from(-1),
                hi: BigInt::from(5),
            })
        );
    }

    /// Unasserted constant comparisons cut the synthetic interval at their
    /// constants: `bv2nat(int2bv_8 x) > 5` with `(or (<= x 5) p)` gets every
    /// integer from `5 - 256` to `5 + 256`; an asserted `x >= 0` keeps the
    /// cut from 0; an asserted `x <= 100` keeps the 256 integers below the
    /// point; an offset member's point moves onto the class.
    #[test]
    fn plan_cuts_the_interval_at_unasserted_constant_comparisons() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let z = terms.mk_var("z", Sort::Int);
        let flag = terms.mk_var("p", Sort::Bool);
        let zero = terms.mk_int(BigInt::zero());
        let two = terms.mk_int(BigInt::from(2));
        let five = terms.mk_int(BigInt::from(5));
        let hundred = terms.mk_int(BigInt::from(100));
        let conv = terms.mk_int2bv(8, x);
        let nat = terms.mk_bv2nat(conv);
        let above_five = terms.mk_gt(nat, five);
        let at_most_five = terms.mk_le(x, five);
        let nested = terms.mk_or(vec![at_most_five, flag]);
        let interval = |lo: i64, hi: i64| Interval {
            lo: BigInt::from(lo),
            hi: BigInt::from(hi),
        };
        let synthetic_of = |terms: &TermStore, roots: &[TermId], var: TermId| {
            IntBlastPlan::analyze(terms, roots)
                .expect("x is half-bounded")
                .synthetic
                .into_iter()
                .find(|(v, _)| *v == var)
                .map(|(_, iv)| iv)
                .expect("the variable is encoded")
        };

        assert_eq!(
            synthetic_of(&terms, &[nested, above_five], x),
            interval(5 - 256, 5 + 256)
        );
        let non_negative = terms.mk_ge(x, zero);
        assert_eq!(
            synthetic_of(&terms, &[nested, non_negative, above_five], x),
            interval(0, 5 + 256)
        );
        let at_most_hundred = terms.mk_le(x, hundred);
        assert_eq!(
            synthetic_of(&terms, &[nested, at_most_hundred, above_five], x),
            interval(5 - 256, 100)
        );
        // `(distinct x 5 7)` under `not`, beside `x >= 0`: two points.
        let seven = terms.mk_int(BigInt::from(7));
        let differs = terms.mk_distinct(vec![x, five, seven]);
        let negated = terms.mk_not(differs);
        let nested_differs = terms.mk_or(vec![negated, flag]);
        assert_eq!(
            synthetic_of(&terms, &[nested_differs, non_negative, above_five], x),
            interval(0, 7 + 256)
        );
        // `z = x + 2` asserted, `(or (<= z 5) p)`: the point 5 on `z` is 3 on
        // `x`.
        let x_plus_two = terms.mk_add(vec![x, two]);
        let link = terms.mk_eq(z, x_plus_two);
        let z_at_most_five = terms.mk_le(z, five);
        let nested_z = terms.mk_or(vec![z_at_most_five, flag]);
        assert_eq!(
            synthetic_of(&terms, &[link, nested_z, above_five], x),
            interval(3 - 256, 3 + 256)
        );
    }

    /// `bv_lia_int_blast_lane`'s `hi_00483` check 3: `x0` is read mod 256
    /// and by the Bool definition `q1 = (distinct c x0)` with
    /// `c = 1091634752581323207310`. The AUF/LIA candidate sees the
    /// `extract` as uninterpreted, so it decided this query only in some
    /// term-store layouts; the blaster now decides it exactly.
    #[test]
    fn a_bool_defined_disequality_is_decided_by_the_blaster() {
        let smt = "(set-logic ALL) (declare-fun x0 () Int) (declare-fun q1 () Bool) \
                   (declare-fun q0 () Bool) \
                   (assert (= ((_ extract 1 1) ((_ int2bv 8) (- x0 3))) (_ bv1 1))) \
                   (assert (= q0 (= ((_ int2bv 2) (+ (* (- 2) x0) 7)) #b01))) \
                   (assert (= q1 (distinct 1091634752581323207310 x0)))";
        let commands = ay_frontend::parse(smt).expect("valid query");
        let mut executor = Executor::new();
        executor.execute_all(&commands).expect("install query");
        let roots = executor.ctx.assertions.clone();
        let got = executor
            .solve_bv_lia_by_int_blast(&roots)
            .expect("probe does not error");
        assert!(got.as_ref().is_some_and(SolveResult::is_sat), "{got:?}");

        // `not q1` forces `x0 = c`, the split point itself: `c - 3` has bit 1
        // set, so the query stays satisfiable, with `q0` false because
        // `-2c + 7 = 3 (mod 4)`; asserting `q0` as well makes it
        // unsatisfiable.
        let with = |extra: &str| format!("{smt} {extra}");
        for (extra, sat) in [
            ("(assert (not q1))", true),
            ("(assert (not q1)) (assert q0)", false),
        ] {
            let commands = ay_frontend::parse(&with(extra)).expect("valid query");
            let mut executor = Executor::new();
            executor.execute_all(&commands).expect("install query");
            let roots = executor.ctx.assertions.clone();
            let got = executor
                .solve_bv_lia_by_int_blast(&roots)
                .expect("probe does not error");
            assert!(
                got.as_ref()
                    .is_some_and(|r| if sat { r.is_sat() } else { r.is_unsat() }),
                "{extra}: {got:?}"
            );
        }
    }

    /// One generated D5-family query (see the test below).
    struct HalfBoundedCase {
        width: u32,
        offset: i64,
        op: u64,
        add: i64,
        greater: bool,
        threshold: i64,
        side: u64,
        bound: i64,
        excluded: Option<i64>,
        /// Sometimes the bound sits on `z = x + link` instead of on `x`.
        link: Option<i64>,
    }

    fn lit(v: i64) -> String {
        if v < 0 {
            format!("(- {})", -v)
        } else {
            v.to_string()
        }
    }

    impl HalfBoundedCase {
        fn draw(next: &mut impl FnMut(u64) -> u64) -> Self {
            let width = 1 + next(5) as u32;
            let modulus = 1u64 << width;
            Self {
                width,
                offset: next(7) as i64 - 3,
                op: next(5),
                add: next(modulus) as i64,
                greater: next(2) == 0,
                threshold: next(modulus) as i64,
                side: next(3),
                bound: next(41) as i64 - 20,
                excluded: (next(3) == 0).then(|| next(41) as i64 - 20),
                link: (next(3) == 0).then(|| next(7) as i64 - 3),
            }
        }

        /// The vector term `op(int2bv_w(x + offset))`.
        fn term(&self) -> String {
            let width = self.width;
            let source = if self.offset == 0 {
                "x".to_string()
            } else {
                format!("(+ x {})", lit(self.offset))
            };
            let conv = format!("((_ int2bv {width}) {source})");
            match self.op {
                0 => conv,
                1 => format!("(bvnot {conv})"),
                2 => format!("(bvneg {conv})"),
                3 => format!("(bvadd {conv} (_ bv{} {width}))", self.add),
                _ => format!("(bvlshr {conv} (_ bv1 {width}))"),
            }
        }

        /// The unsigned value of [`Self::term`] at `x`.
        fn term_value(&self, x: i64) -> i64 {
            let modulus = 1i64 << self.width;
            let r = (x + self.offset).rem_euclid(modulus);
            match self.op {
                0 => r,
                1 => modulus - 1 - r,
                2 => (modulus - r) % modulus,
                3 => (r + self.add) % modulus,
                _ => r >> 1,
            }
        }

        fn smt(&self) -> String {
            let cmp = if self.greater { ">" } else { "<" };
            self.smt_with_obligation(&format!(
                "({cmp} (bv2nat {}) {})",
                self.term(),
                self.threshold
            ))
        }

        /// The query with `obligation` in place of the comparison on
        /// [`Self::term`]: the declarations, then the obligation, the link,
        /// the bound and the exclusion.
        fn smt_with_obligation(&self, obligation: &str) -> String {
            let mut smt = format!(
                "(set-logic ALL) (declare-const x Int) (declare-const z Int) \
                 (assert {obligation})"
            );
            let bounded_var = match self.link {
                Some(c) => {
                    smt.push_str(&format!(" (assert (= z (+ x {})))", lit(c)));
                    "z"
                }
                None => "x",
            };
            match self.side {
                0 => smt.push_str(&format!(" (assert (>= {bounded_var} {}))", lit(self.bound))),
                1 => smt.push_str(&format!(" (assert (<= {bounded_var} {}))", lit(self.bound))),
                _ => {}
            }
            if let Some(d) = self.excluded {
                smt.push_str(&format!(" (assert (distinct x {}))", lit(d)));
            }
            smt
        }

        fn holds(&self, x: i64) -> bool {
            let v = self.term_value(x);
            let obligation = if self.greater {
                v > self.threshold
            } else {
                v < self.threshold
            };
            self.holds_with(x, obligation)
        }

        /// [`Self::holds`] with the obligation's value given.
        fn holds_with(&self, x: i64, obligation: bool) -> bool {
            let bounded_value = x + self.link.unwrap_or(0);
            let bounded = match self.side {
                0 => bounded_value >= self.bound,
                1 => bounded_value <= self.bound,
                _ => true,
            };
            obligation && bounded && self.excluded != Some(x)
        }
    }

    /// Generated D5-family queries — a one-sided (or no) bound on `x` or on
    /// `z = x + c`, an obligation on `bv2nat(op(int2bv_w(x + c)))`, sometimes
    /// `x != d` — are DECIDED by the blaster, and its verdict is the
    /// brute-force one: the window `[-200, 200]` holds every residue class on
    /// either side of any bound in `[-20, 20]` several times over.
    #[test]
    fn half_bounded_queries_decide_as_brute_force_says() {
        let mut state = 0x5eed_d5d5_1234_5678u64;
        let mut next = |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        let (mut sat, mut unsat) = (0, 0);
        for case in 0..300 {
            let query = HalfBoundedCase::draw(&mut next);
            let smt = query.smt();
            let expected_sat = (-200..=200).any(|x| query.holds(x));

            let commands = ay_frontend::parse(&smt).expect("valid query");
            let mut executor = Executor::new();
            executor.execute_all(&commands).expect("install query");
            let roots = executor.ctx.assertions.clone();
            let got = executor
                .solve_bv_lia_by_int_blast(&roots)
                .expect("probe does not error");
            match got {
                Some(result) if result.is_sat() && expected_sat => sat += 1,
                Some(result) if result.is_unsat() && !expected_sat => unsat += 1,
                other => panic!(
                    "case {case}: {smt}\nbrute force says {}, the blaster {other:?}",
                    if expected_sat { "sat" } else { "unsat" }
                ),
            }
        }
        assert!(sat > 50 && unsat > 20, "sat {sat}, unsat {unsat}");
    }

    /// A D5-family query whose obligation switches on an UNASSERTED constant
    /// comparison `n`: `(ite n (cmp nat t) (cmp2 nat t2))`, `n` on `x` or on
    /// the linked `z`.
    struct NestedCase {
        base: HalfBoundedCase,
        kind: u64,
        constant: i64,
        on_z: bool,
        alt_greater: bool,
        alt_threshold: i64,
    }

    impl NestedCase {
        fn draw(next: &mut impl FnMut(u64) -> u64) -> Self {
            let base = HalfBoundedCase::draw(next);
            let modulus = 1u64 << base.width;
            let on_z = base.link.is_some() && next(2) == 0;
            Self {
                kind: next(5),
                constant: next(41) as i64 - 20,
                on_z,
                alt_greater: next(2) == 0,
                alt_threshold: next(modulus) as i64,
                base,
            }
        }

        fn condition(&self) -> String {
            let v = if self.on_z { "z" } else { "x" };
            let c = self.constant;
            match self.kind {
                0 => format!("(< {v} {})", lit(c)),
                1 => format!("(<= (* 2 {v}) {})", lit(c)),
                2 => format!("(= {v} {})", lit(c)),
                3 => format!("(distinct {v} {} {})", lit(c), lit(c + 3)),
                _ => format!("(not (>= (* (- 3) {v}) {}))", lit(c)),
            }
        }

        fn condition_holds(&self, x: i64) -> bool {
            let v = if self.on_z {
                x + self.base.link.unwrap_or(0)
            } else {
                x
            };
            let c = self.constant;
            match self.kind {
                0 => v < c,
                1 => 2 * v <= c,
                2 => v == c,
                3 => v != c && v != c + 3,
                _ => -3 * v < c,
            }
        }

        fn smt(&self) -> String {
            let cmp = |greater: bool| if greater { ">" } else { "<" };
            let nat = format!("(bv2nat {})", self.base.term());
            self.base.smt_with_obligation(&format!(
                "(ite {} ({} {nat} {}) ({} {nat} {}))",
                self.condition(),
                cmp(self.base.greater),
                self.base.threshold,
                cmp(self.alt_greater),
                self.alt_threshold
            ))
        }

        fn holds(&self, x: i64) -> bool {
            let v = self.base.term_value(x);
            let obligation = if self.condition_holds(x) {
                if self.base.greater {
                    v > self.base.threshold
                } else {
                    v < self.base.threshold
                }
            } else if self.alt_greater {
                v > self.alt_threshold
            } else {
                v < self.alt_threshold
            };
            self.base.holds_with(x, obligation)
        }
    }

    /// The D5 family with the obligation switched by an unasserted constant
    /// comparison (`<`, a scaled `<=`, `=`, a two-constant `distinct`, a
    /// negated scaled `>=`; on `x` or on `z = x + c`): DECIDED, with the
    /// brute-force verdict. Every split point lies in `[-20, 23]` and every
    /// modulus is at most 32, so `[-200, 200]` holds every residue class of
    /// every cell, beyond any bound, several times over.
    #[test]
    fn nested_constant_comparison_queries_decide_as_brute_force_says() {
        let mut state = 0x0b5e_55ed_2026_1108u64;
        let mut next = |n: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % n
        };
        let (mut sat, mut unsat) = (0, 0);
        for case in 0..300 {
            let query = NestedCase::draw(&mut next);
            let smt = query.smt();
            let expected_sat = (-200..=200).any(|x| query.holds(x));

            let commands = ay_frontend::parse(&smt).expect("valid query");
            let mut executor = Executor::new();
            executor.execute_all(&commands).expect("install query");
            let roots = executor.ctx.assertions.clone();
            let got = executor
                .solve_bv_lia_by_int_blast(&roots)
                .expect("probe does not error");
            match got {
                Some(result) if result.is_sat() && expected_sat => sat += 1,
                Some(result) if result.is_unsat() && !expected_sat => unsat += 1,
                other => panic!(
                    "case {case}: {smt}\nbrute force says {}, the blaster {other:?}",
                    if expected_sat { "sat" } else { "unsat" }
                ),
            }
        }
        assert!(sat > 50 && unsat > 20, "sat {sat}, unsat {unsat}");
    }

    /// An unbounded Int with an arithmetic occurrence is outside the fragment.
    #[test]
    fn plan_declines_unbounded_arithmetic_var() {
        let mut terms = TermStore::new();
        let y = terms.mk_var("y", Sort::Int);
        let x = terms.mk_var("x", Sort::Int);
        let conv = terms.mk_int2bv(8, y);
        let nat = terms.mk_bv2nat(conv);
        let def = terms.mk_eq(x, nat);
        let cmp = terms.mk_lt(x, y);
        assert!(IntBlastPlan::analyze(&terms, &[def, cmp]).is_none());
    }

    #[test]
    fn disposable_bv_probe_preserves_outer_authority_and_repair_state() {
        for (extra, expected) in [
            ("(assert (= x 1)) (assert (= y 1))", "unsat"),
            ("(assert (= x 1)) (assert (= y 2))", "sat"),
            ("(assert (< y x))", "declined"),
        ] {
            let commands = ay_frontend::parse(&format!(
                "(set-option :produce-proofs true) (set-logic ALL)
                 (declare-const x Int) (declare-const y Int)
                 (assert (= y (bv2nat (bvshl #x01 ((_ int2bv 8) x))))) {extra}"
            ))
            .expect("valid query");
            let mut executor = Executor::new();
            executor.execute_all(&commands).expect("install query");
            executor.proof_tracker.enable();
            let roots = executor.ctx.assertions.clone();
            let marker = executor.ctx.terms.true_term();
            executor.read_pin_repair_done = true;
            executor.bv_subst_lane = true;
            executor.last_bv_drat_self_cert = false;
            executor.last_assumption_core = Some(vec![marker]);
            executor
                .model_validation_delegated_assertions
                .insert(marker);
            executor.last_result = Some(SolveResult::Unknown);
            let result = executor
                .solve_bv_lia_by_int_blast(&roots)
                .expect("probe does not error");
            match expected {
                "unsat" => assert!(result.is_some_and(|r| r.is_unsat())),
                "sat" => assert!(result.is_some_and(|r| r.is_sat())),
                _ => assert!(result.is_none()),
            }
            assert_eq!(executor.ctx.assertions, roots);
            assert!(executor.read_pin_repair_done);
            assert!(executor.bv_subst_lane);
            assert!(!executor.last_bv_drat_self_cert);
            assert_eq!(executor.last_assumption_core, Some(vec![marker]));
            assert_eq!(
                executor.model_validation_delegated_assertions,
                HashSet::from_iter([marker])
            );
            assert!(matches!(executor.last_result, Some(SolveResult::Unknown)));
            assert!(executor.last_clause_trace.is_none());
            assert!(executor.last_lrat_certificate.is_none());
            assert!(executor.last_unsat_certificate.is_none());
            assert!(executor.proof_tracker.is_enabled());
        }
    }
}

#[cfg(test)]
#[path = "int_blast_lane_tests.rs"]
mod lane_tests;

#[path = "int_blast_box.rs"]
mod box_lane;
