// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The FloatingPoint word-level rewriter: z3's `fpa_rewriter` role, the first
//! pass of the FP pipeline, before the bit-blaster (`fpa2bv`) sees a term.
//!
//! It folds every FP operation whose operands are constants into the constant
//! it denotes, computed by the exact arithmetic of [`crate::exact`]:
//!
//! * arithmetic (`fp.add` .. `fp.fma`, `fp.rem`, `fp.min`/`fp.max`, `fp.abs`,
//!   `fp.neg`), conversions (`to_fp` from a FloatingPoint, a bit-vector or a
//!   ground Real/Int, `to_fp_unsigned`, `fp.to_ubv`, `fp.to_sbv`, `fp.to_real`,
//!   `fp.to_ieee_bv`), the classification predicates, the comparisons, and
//!   `=`/`distinct` over numerals or rounding-mode literals;
//! * under a SYMBOLIC rounding mode too, when the result is the same under all
//!   five modes. The `RoundingMode` domain is exactly those five, so such a
//!   term denotes that constant whatever the mode is: `((_ to_fp 11 53) rm 1.0)`
//!   is `1.0`;
//! * over constant case splits: an application whose arguments are constants
//!   or `ite` trees of constants, or whose mode is symbolic, distributes over
//!   them and folds each case (`distribute.rs`, bounded by
//!   `distribute::MAX_LEAVES` leaves).
//!
//! Every rule is an equivalence, so the rewritten assertions have exactly the
//! models of the input. A result SMT-LIB leaves unspecified (`fp.to_ubv` of
//! NaN, `fp.min` of `+0` and `-0`, `fp.to_real` of an infinity, ...) is never
//! folded: the term stays and the solver keeps its freedom.
//!
//! The traversal is iterative and memoized per rewriter, so a shared subterm is
//! rewritten once and a deep term cannot exhaust the stack. It does not enter
//! quantifier bodies: the FP pipeline is quantifier-free, and a binder's
//! variables are never constants.

mod distribute;
mod numeral;
#[cfg(test)]
#[path = "rewriter/numeral_contract_tests.rs"]
mod numeral_contract_tests;
#[cfg(test)]
mod tests;

pub use numeral::{fp_numeral, is_rounding_mode_sort, mk_fp_numeral, rounding_mode_literal};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::{exact::wide as exact, RoundingMode};
use exact::Value;
use numeral::{bv_constant, ground_rational, signed_value};

const MODES: [RoundingMode; 5] = [
    RoundingMode::RNE,
    RoundingMode::RNA,
    RoundingMode::RTP,
    RoundingMode::RTN,
    RoundingMode::RTZ,
];

/// Memoized bottom-up rewriting of terms in one `TermStore`.
#[derive(Debug, Default)]
pub struct FpRewriter {
    cache: HashMap<TermId, TermId>,
    source: Option<(ay_core::term::TermStoreSnapshotStamp, u64)>,
    folds: u64,
}

enum Frame {
    Enter(TermId),
    Exit(TermId),
}

impl FpRewriter {
    /// A rewriter with an empty cache.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// How many applications were folded to a constant so far.
    pub fn folds(&self) -> u64 {
        self.folds
    }

    /// Rewrite `root`, returning an equivalent term.
    pub fn rewrite(&mut self, terms: &mut TermStore, root: TermId) -> TermId {
        let metadata = terms.checker_visible_metadata_generation();
        if self.source.as_ref().is_some_and(|(source, generation)| {
            !source.is_append_only_prefix_of(terms) || *generation != metadata
        }) {
            self.cache.clear();
        }
        // Bind before traversal too: an unwind must not leave an unbound cache
        // that a subsequent call can interpret in another physical universe.
        self.source = Some((terms.snapshot_stamp(), metadata));
        let mut stack = vec![Frame::Enter(root)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(term) => {
                    if self.cache.contains_key(&term) {
                        continue;
                    }
                    let children = children(terms.get(term));
                    if children.is_empty() {
                        self.cache.insert(term, term);
                        continue;
                    }
                    stack.push(Frame::Exit(term));
                    stack.extend(children.into_iter().map(Frame::Enter));
                }
                Frame::Exit(term) => {
                    if !self.cache.contains_key(&term) {
                        let rebuilt = self.rebuild(terms, term);
                        self.cache.insert(term, rebuilt);
                    }
                }
            }
        }
        self.cache.get(&root).copied().unwrap_or(root)
    }

    fn rewritten(&self, term: TermId) -> TermId {
        self.cache.get(&term).copied().unwrap_or(term)
    }

    fn rebuild(&mut self, terms: &mut TermStore, term: TermId) -> TermId {
        match terms.get(term).clone() {
            TermData::Not(inner) => {
                let new = self.rewritten(inner);
                if new == inner {
                    term
                } else {
                    terms.mk_not(new)
                }
            }
            TermData::Ite(c, t, e) => {
                let new = (self.rewritten(c), self.rewritten(t), self.rewritten(e));
                if new == (c, t, e) {
                    term
                } else {
                    terms.mk_ite(new.0, new.1, new.2)
                }
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<_> = bindings
                    .iter()
                    .map(|(name, value)| (name.clone(), self.rewritten(*value)))
                    .collect();
                let new_body = self.rewritten(body);
                if new_body == body && new_bindings == bindings {
                    term
                } else {
                    terms.mk_let(new_bindings, new_body)
                }
            }
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args.iter().map(|&a| self.rewritten(a)).collect();
                let sort = terms.sort(term).clone();
                if let Some(folded) = distribute::rewrite_app(terms, &sym, &new_args, &sort) {
                    self.folds += 1;
                    folded
                } else if new_args == args {
                    term
                } else {
                    terms.mk_app(sym, new_args, sort)
                }
            }
            _ => term,
        }
    }
}

/// The subterms the rewriter descends into (none for leaves and binders).
fn children(data: &TermData) -> Vec<TermId> {
    match data {
        TermData::App(_, args) => args.clone(),
        TermData::Not(inner) => vec![*inner],
        TermData::Ite(c, t, e) => vec![*c, *t, *e],
        TermData::Let(bindings, body) => bindings
            .iter()
            .map(|(_, value)| *value)
            .chain(std::iter::once(*body))
            .collect(),
        _ => Vec::new(),
    }
}

/// A folded constant before it is interned.
#[derive(Clone, Debug)]
enum Folded {
    Fp(Value),
    Bv(BigInt, u32),
    Real(BigRational),
    Bool(bool),
}

impl Folded {
    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Fp(a), Self::Fp(b)) => exact::same_element(a, b) == Some(true),
            (Self::Bv(a, w), Self::Bv(b, v)) => a == b && w == v,
            (Self::Real(a), Self::Real(b)) => a == b,
            (Self::Bool(a), Self::Bool(b)) => a == b,
            _ => false,
        }
    }

    fn intern(self, terms: &mut TermStore) -> TermId {
        match self {
            Self::Fp(value) => numeral::mk_wide_numeral(terms, &value),
            Self::Bv(value, width) => terms.mk_bitvec(value, width),
            Self::Real(value) => terms.mk_rational(value),
            Self::Bool(value) => terms.mk_bool(value),
        }
    }
}

/// One rewrite step on an application whose arguments are already rewritten:
/// the constant it denotes, if its operands determine one. `sort` is the
/// application's sort.
pub fn fold_app(
    terms: &mut TermStore,
    sym: &Symbol,
    args: &[TermId],
    sort: &Sort,
) -> Option<TermId> {
    let folded = fold_constant(terms, sym, args, sort)?;
    let valid_sort = match &folded {
        Folded::Fp(value) => {
            !terms.is_declared_function("to_fp")
                && sort == &Sort::FloatingPoint(value.eb(), value.sb())
        }
        Folded::Bv(_, width) => sort == &Sort::bitvec(*width),
        Folded::Real(_) => sort == &Sort::Real,
        Folded::Bool(_) => sort == &Sort::Bool,
    };
    if !valid_sort {
        return None;
    }
    Some(folded.intern(terms))
}

/// The operator's name, when `sym` is spelled the way its theory spells it:
/// the conversions are indexed (`(_ to_fp eb sb)`, `(_ fp.to_ubv w)`, ...),
/// every other FP operator and `=`/`distinct` is a plain name. A symbol spelled
/// the other way is not a theory operator and is never folded.
fn theory_operator<'a>(terms: &TermStore, sym: &'a Symbol) -> Option<&'a str> {
    let name = sym.name();
    if terms.is_declared_function(name) {
        return None;
    }
    let indexed = matches!(name, "to_fp" | "to_fp_unsigned" | "fp.to_ubv" | "fp.to_sbv");
    (indexed == matches!(sym, Symbol::Indexed(..))).then_some(name)
}

fn fold_constant(terms: &TermStore, sym: &Symbol, args: &[TermId], sort: &Sort) -> Option<Folded> {
    let name = theory_operator(terms, sym)?;
    if let Symbol::Indexed(_, indices) = sym {
        let valid = match (name, sort) {
            ("to_fp" | "to_fp_unsigned", Sort::FloatingPoint(eb, sb)) => {
                indices.as_slice() == [*eb, *sb]
            }
            ("fp.to_ubv" | "fp.to_sbv", Sort::BitVec(bv)) => indices.as_slice() == [bv.width],
            _ => false,
        };
        if !valid {
            return None;
        }
    }
    let fp = |i: usize| numeral::wide_numeral(terms, *args.get(i)?);
    match (name, args.len()) {
        ("=" | "distinct", 2) => fold_equality(terms, name == "=", args),
        (
            "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
            | "fp.isNegative" | "fp.isPositive",
            1,
        ) => Some(Folded::Bool(exact::classify(name, &fp(0)?)?)),
        ("fp.eq", 2) => Some(Folded::Bool(exact::fp_eq(&fp(0)?, &fp(1)?)?)),
        ("fp.lt", 2) => Some(Folded::Bool(exact::fp_lt(&fp(0)?, &fp(1)?)?)),
        ("fp.leq", 2) => Some(Folded::Bool(exact::fp_leq(&fp(0)?, &fp(1)?)?)),
        ("fp.gt", 2) => Some(Folded::Bool(exact::fp_lt(&fp(1)?, &fp(0)?)?)),
        ("fp.geq", 2) => Some(Folded::Bool(exact::fp_leq(&fp(1)?, &fp(0)?)?)),
        ("fp.abs", 1) => exact::abs(&fp(0)?).map(Folded::Fp),
        ("fp.neg", 1) => exact::neg(&fp(0)?).map(Folded::Fp),
        ("fp.rem", 2) => exact::rem(&fp(0)?, &fp(1)?).map(Folded::Fp),
        ("fp.min", 2) => exact::min(&fp(0)?, &fp(1)?).map(Folded::Fp),
        ("fp.max", 2) => exact::max(&fp(0)?, &fp(1)?).map(Folded::Fp),
        ("fp.to_real", 1) => exact::to_real(&fp(0)?).map(Folded::Real),
        ("fp.to_ieee_bv", 1) => {
            let (bits, width) = numeral::non_nan_ieee_bits(terms, args[0])?;
            matches!(sort, Sort::BitVec(bv) if bv.width == width).then_some(Folded::Bv(bits, width))
        }
        _ => fold_rounded(terms, sym, args, sort),
    }
}

/// `=` / `distinct` over two FloatingPoint numerals (element identity) or two
/// rounding-mode literals.
fn fold_equality(terms: &TermStore, positive: bool, args: &[TermId]) -> Option<Folded> {
    let equal = if let (Some(a), Some(b)) = (
        numeral::wide_numeral(terms, args[0]),
        numeral::wide_numeral(terms, args[1]),
    ) {
        exact::same_element(&a, &b)?
    } else {
        rounding_mode_literal(terms, args[0])? == rounding_mode_literal(terms, args[1])?
    };
    Some(Folded::Bool(equal == positive))
}

/// Operations that take a rounding mode as their first argument. A literal
/// mode folds directly; any other mode folds only when all five modes agree.
fn fold_rounded(terms: &TermStore, sym: &Symbol, args: &[TermId], sort: &Sort) -> Option<Folded> {
    let (&rm_term, operands) = args.split_first()?;
    if !is_rounding_mode_sort(terms.sort(rm_term)) {
        return None;
    }
    let under = |rm: RoundingMode| rounded_constant(terms, sym, operands, sort, rm);
    if let Some(rm) = rounding_mode_literal(terms, rm_term) {
        return under(rm);
    }
    let first = under(MODES[0])?;
    for rm in &MODES[1..] {
        if !under(*rm)?.same(&first) {
            return None;
        }
    }
    Some(first)
}

fn rounded_constant(
    terms: &TermStore,
    sym: &Symbol,
    operands: &[TermId],
    sort: &Sort,
    rm: RoundingMode,
) -> Option<Folded> {
    let fp = |i: usize| numeral::wide_numeral(terms, *operands.get(i)?);
    let result = match (sym.name(), operands.len()) {
        ("fp.add", 2) => exact::add(rm, &fp(0)?, &fp(1)?)?,
        ("fp.sub", 2) => exact::sub(rm, &fp(0)?, &fp(1)?)?,
        ("fp.mul", 2) => exact::mul(rm, &fp(0)?, &fp(1)?)?,
        ("fp.div", 2) => exact::div(rm, &fp(0)?, &fp(1)?)?,
        ("fp.fma", 3) => exact::fma(rm, &fp(0)?, &fp(1)?, &fp(2)?)?,
        ("fp.sqrt", 1) => exact::sqrt(rm, &fp(0)?)?,
        ("fp.roundToIntegral", 1) => exact::round_to_integral(rm, &fp(0)?)?,
        ("to_fp" | "to_fp_unsigned", 1) => {
            let Sort::FloatingPoint(eb, sb) = *sort else {
                return None;
            };
            return to_fp_constant(terms, sym.name() == "to_fp", rm, operands[0], eb, sb)
                .map(Folded::Fp);
        }
        ("fp.to_ubv" | "fp.to_sbv", 1) => {
            let Sort::BitVec(ref bv) = *sort else {
                return None;
            };
            let value = fp(0)?;
            let bits = if sym.name() == "fp.to_ubv" {
                exact::to_ubv(rm, &value, bv.width)?
            } else {
                exact::to_sbv(rm, &value, bv.width)?
            };
            return Some(Folded::Bv(bits, bv.width));
        }
        _ => return None,
    };
    Some(Folded::Fp(result))
}

/// `((_ to_fp eb sb) rm x)` (`signed`) or `((_ to_fp_unsigned eb sb) rm x)`
/// for a constant `x` of FloatingPoint, bit-vector, Real or Int sort.
fn to_fp_constant(
    terms: &TermStore,
    signed: bool,
    rm: RoundingMode,
    x: TermId,
    eb: u32,
    sb: u32,
) -> Option<Value> {
    match terms.sort(x) {
        Sort::FloatingPoint(..) if signed => {
            exact::to_fp_from_fp(rm, &numeral::wide_numeral(terms, x)?, eb, sb)
        }
        Sort::BitVec(_) => {
            let (value, width) = bv_constant(terms, x)?;
            let integer = if signed {
                signed_value(&value, width)
            } else {
                value
            };
            exact::to_fp_from_rational(rm, &BigRational::from_integer(integer), eb, sb)
        }
        Sort::Real | Sort::Int if signed => {
            exact::to_fp_from_rational(rm, &ground_rational(terms, x)?, eb, sb)
        }
        _ => None,
    }
}
