// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Independent, fail-closed validation for ground arithmetic `evaluate` steps.
//!
//! This module deliberately interprets a small, exact SMT-LIB fragment instead
//! of asking any solver component to replay its own simplification.  A term is
//! accepted only when every node is closed, well-sorted, uses a recognized
//! builtin head, stays inside the work envelope, and evaluates to Boolean
//! `true`.  Unsupported and under-specified operations (notably division by
//! zero) fail closed.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use super::ProofCheckError;
mod unsigned_order;

/// Maximum number of term visits/argument edges checked for one literal.
///
/// Counting visits rather than only distinct DAG nodes also bounds a single
/// application with an adversarially large argument vector.
const MAX_EVAL_WORK: usize = 100_000;

/// Bound recursive descent independently of the total work budget.
const MAX_EVAL_DEPTH: usize = 512;

/// Bound every exact integer/rational value retained by the evaluator.
const MAX_VALUE_BITS: u64 = 65_536;

/// Bound the aggregate bit-size of exact values returned by evaluation.
///
/// Cached values are charged again on every lookup because the caller receives
/// an owned clone and may retain many such clones in an n-ary operator.
const MAX_TOTAL_VALUE_BITS: u64 = 4 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Int(BigInt),
    Real(BigRational),
    /// A bit-vector of `width` bits holding `value`, `0 <= value < 2^width`.
    BitVec {
        width: u32,
        value: BigInt,
    },
}

impl Value {
    fn matches_sort(&self, sort: &Sort) -> bool {
        match (self, sort) {
            (Self::Bool(_), Sort::Bool)
            | (Self::Int(_), Sort::Int)
            | (Self::Real(_), Sort::Real) => true,
            (Self::BitVec { width, .. }, Sort::BitVec(sort)) => *width == sort.width,
            _ => false,
        }
    }

    fn same_kind(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bool(_), Self::Bool(_))
            | (Self::Int(_), Self::Int(_))
            | (Self::Real(_), Self::Real(_)) => true,
            (Self::BitVec { width: left, .. }, Self::BitVec { width: right, .. }) => left == right,
            _ => false,
        }
    }

    fn bit_size(&self) -> u64 {
        match self {
            Self::Bool(_) => 1,
            Self::Int(value) => value.bits().max(1),
            Self::Real(value) => value
                .numer()
                .bits()
                .max(1)
                .saturating_add(value.denom().bits().max(1)),
            Self::BitVec { width, .. } => u64::from(*width).max(1),
        }
    }
}

struct Evaluator<'a> {
    terms: &'a TermStore,
    memo: HashMap<TermId, Option<Value>>,
    active: HashSet<TermId>,
    work: usize,
    total_value_bits: u64,
}

impl<'a> Evaluator<'a> {
    fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            memo: HashMap::default(),
            active: HashSet::default(),
            work: 0,
            total_value_bits: 0,
        }
    }

    fn charge_work(&mut self, amount: usize) -> Option<()> {
        self.work = self.work.checked_add(amount)?;
        (self.work <= MAX_EVAL_WORK).then_some(())
    }

    fn check_estimated_bits(&self, bits: u64) -> Option<()> {
        (bits <= MAX_VALUE_BITS).then_some(())
    }

    fn charge_value(&mut self, value: &Value) -> Option<()> {
        self.charge_value_bits(value.bit_size())
    }

    fn charge_value_bits(&mut self, bits: u64) -> Option<()> {
        self.check_estimated_bits(bits)?;
        self.total_value_bits = self.total_value_bits.checked_add(bits)?;
        (self.total_value_bits <= MAX_TOTAL_VALUE_BITS).then_some(())
    }

    fn eval(&mut self, term: TermId, depth: usize) -> Option<Value> {
        self.charge_work(1)?;
        if depth > MAX_EVAL_DEPTH || term.index() >= self.terms.len() {
            return None;
        }
        if let Some(cached_bits) = self
            .memo
            .get(&term)
            .map(|cached| cached.as_ref().map(Value::bit_size))
        {
            let bits = cached_bits?;
            // Charge before cloning. Every cached value was bounded when it
            // entered `memo`, so even the single clone below has a fixed
            // per-value ceiling.
            self.charge_value_bits(bits)?;
            return self.memo.get(&term).and_then(Clone::clone);
        }
        if !self.active.insert(term) {
            return None;
        }

        let value = self.eval_uncached(term, depth);
        self.active.remove(&term);
        let value = match value {
            Some(value) if self.charge_value(&value).is_some() => Some(value),
            _ => None,
        };
        self.memo.insert(term, value.clone());
        value
    }

    fn eval_uncached(&mut self, term: TermId, depth: usize) -> Option<Value> {
        // Preflight every allocation carried by `TermData::clone`. In
        // particular, reject oversized literals, unknown arbitrarily-long
        // symbol names, and over-wide application vectors before copying
        // them. Charging all edges here also makes the documented work bound
        // independent of how soon evaluation of a child fails.
        let (literal_bits, application_arity) = match self.terms.get(term) {
            TermData::Const(Constant::Bool(_)) => (Some(1), 0),
            TermData::Const(Constant::Int(value)) => (Some(value.bits().max(1)), 0),
            TermData::Const(Constant::Rational(value)) => (
                Some(
                    value
                        .0
                        .numer()
                        .bits()
                        .max(1)
                        .saturating_add(value.0.denom().bits().max(1)),
                ),
                0,
            ),
            TermData::Const(Constant::BitVec { width, .. }) => (Some(u64::from(*width).max(1)), 0),
            TermData::Not(_) | TermData::Ite(_, _, _) => (None, 0),
            TermData::App(Symbol::Named(name), args) if supported_builtin_name(name) => {
                (None, args.len())
            }
            TermData::App(Symbol::Indexed(name, indices), args)
                if supported_indexed_name(name, indices.len()) =>
            {
                (None, args.len())
            }
            _ => return None,
        };
        if let Some(bits) = literal_bits {
            self.check_estimated_bits(bits)?;
        }
        self.charge_work(application_arity)?;

        let data = self.terms.get(term).clone();
        let value = match data {
            TermData::Const(Constant::Bool(value)) => Value::Bool(value),
            TermData::Const(Constant::Int(value)) => Value::Int(value),
            TermData::Const(Constant::Rational(value)) => Value::Real(value.0),
            TermData::Const(Constant::BitVec { value, width }) => {
                if width == 0 {
                    return None;
                }
                bit_vector(width, value)
            }
            TermData::Not(inner) => {
                let Value::Bool(value) = self.eval(inner, depth + 1)? else {
                    return None;
                };
                Value::Bool(!value)
            }
            TermData::Ite(condition, then_term, else_term) => {
                let Value::Bool(condition) = self.eval(condition, depth + 1)? else {
                    return None;
                };
                // Evaluate both branches.  This deliberately rejects a hidden
                // variable/UF even when the other branch is selected.
                let then_value = self.eval(then_term, depth + 1)?;
                let else_value = self.eval(else_term, depth + 1)?;
                if !then_value.same_kind(&else_value) {
                    return None;
                }
                if condition {
                    then_value
                } else {
                    else_value
                }
            }
            TermData::App(Symbol::Named(name), args) => self.eval_app(&name, &args, depth + 1)?,
            TermData::App(Symbol::Indexed(name, indices), args) => {
                self.eval_indexed_app(&name, &indices, &args, depth + 1)?
            }
            // Variables, UFs (handled by the unknown-head arm in `eval_app`),
            // binders, lets, indexed symbols, non-arithmetic constants, and
            // all future term variants are outside this strict fragment.
            _ => return None,
        };

        value.matches_sort(self.terms.sort(term)).then_some(value)
    }

    fn eval_app(&mut self, name: &str, args: &[TermId], depth: usize) -> Option<Value> {
        match name {
            "not" if args.len() == 1 => {
                let Value::Bool(value) = self.eval(args[0], depth)? else {
                    return None;
                };
                Some(Value::Bool(!value))
            }
            "and" if args.len() >= 2 => {
                let values = self.eval_bools(args, depth)?;
                Some(Value::Bool(values.into_iter().all(|value| value)))
            }
            "or" if args.len() >= 2 => {
                let values = self.eval_bools(args, depth)?;
                Some(Value::Bool(values.into_iter().any(|value| value)))
            }
            "=>" | "implies" if args.len() >= 2 => {
                let values = self.eval_bools(args, depth)?;
                let (last, prefix) = values.split_last()?;
                let value = prefix
                    .iter()
                    .rev()
                    .fold(*last, |consequent, antecedent| !antecedent || consequent);
                Some(Value::Bool(value))
            }
            "xor" if args.len() >= 2 => {
                let values = self.eval_bools(args, depth)?;
                Some(Value::Bool(
                    values.into_iter().fold(false, |acc, value| acc ^ value),
                ))
            }
            "ite" if args.len() == 3 => {
                let Value::Bool(condition) = self.eval(args[0], depth)? else {
                    return None;
                };
                let then_value = self.eval(args[1], depth)?;
                let else_value = self.eval(args[2], depth)?;
                if !then_value.same_kind(&else_value) {
                    return None;
                }
                Some(if condition { then_value } else { else_value })
            }
            "=" if args.len() >= 2 => {
                let values = self.eval_values(args, depth)?;
                let first = values.first()?;
                if !values.iter().all(|value| value.same_kind(first)) {
                    return None;
                }
                Some(Value::Bool(values[1..].iter().all(|value| value == first)))
            }
            "distinct" if args.len() >= 2 => {
                let values = self.eval_values(args, depth)?;
                let first = values.first()?;
                if !values.iter().all(|value| value.same_kind(first)) {
                    return None;
                }
                for (index, value) in values.iter().enumerate() {
                    for previous in &values[..index] {
                        self.charge_work(1)?;
                        if value == previous {
                            return Some(Value::Bool(false));
                        }
                    }
                }
                Some(Value::Bool(true))
            }
            "+" if args.len() >= 2 => {
                let values = self.eval_values(args, depth)?;
                self.eval_add(values)
            }
            "-" if !args.is_empty() => {
                let values = self.eval_values(args, depth)?;
                self.eval_sub(values)
            }
            "*" if args.len() >= 2 => {
                let values = self.eval_values(args, depth)?;
                self.eval_mul(values)
            }
            "/" if args.len() >= 2 => {
                let values = self.eval_values(args, depth)?;
                self.eval_real_div(values)
            }
            "<" | "<=" | ">" | ">=" if args.len() >= 2 => {
                let values = self.eval_values(args, depth)?;
                self.eval_comparison(name, &values).map(Value::Bool)
            }
            "to_real" if args.len() == 1 && !self.terms.to_real_is_shadowed() => {
                let Value::Int(value) = self.eval(args[0], depth)? else {
                    return None;
                };
                Some(Value::Real(BigRational::from(value)))
            }
            "to_int" if args.len() == 1 => {
                let Value::Real(value) = self.eval(args[0], depth)? else {
                    return None;
                };
                Some(Value::Int(rational_floor(&value)))
            }
            "is_int" if args.len() == 1 && !self.terms.is_int_is_shadowed() => {
                let Value::Real(value) = self.eval(args[0], depth)? else {
                    return None;
                };
                Some(Value::Bool(value.denom().is_one()))
            }
            "div" | "mod" | "rem" if args.len() == 2 => {
                let Value::Int(dividend) = self.eval(args[0], depth)? else {
                    return None;
                };
                let Value::Int(divisor) = self.eval(args[1], depth)? else {
                    return None;
                };
                if divisor.is_zero() {
                    return None;
                }
                let remainder = euclidean_mod(&dividend, &divisor);
                let value = match name {
                    "div" => (dividend - &remainder) / divisor,
                    "mod" => remainder,
                    // Z3's integer `rem` follows the sign of the divisor:
                    // rem(a,b) = ite(b >= 0, mod(a,b), -mod(a,b)).
                    _ if divisor.is_negative() => -remainder,
                    _ => remainder,
                };
                Some(Value::Int(value))
            }
            "bvnot" | "bvneg" if args.len() == 1 => {
                let Value::BitVec { width, value } = self.eval(args[0], depth)? else {
                    return None;
                };
                let modulus = BigInt::one() << width;
                Some(bit_vector(
                    width,
                    if name == "bvnot" {
                        &modulus - BigInt::one() - value
                    } else {
                        modulus - value
                    },
                ))
            }
            "bvand" | "bvor" | "bvxor" | "bvadd" | "bvmul" if args.len() >= 2 => {
                let (width, values) = self.eval_bit_vectors(args, depth)?;
                let mut values = values.into_iter();
                let first = values.next()?;
                let result = values.try_fold(first, |acc, value| {
                    Some(match name {
                        "bvand" => acc & value,
                        "bvor" => acc | value,
                        "bvxor" => acc ^ value,
                        "bvadd" => acc + value,
                        _ => {
                            self.check_estimated_bits(acc.bits().saturating_add(value.bits()))?;
                            acc * value
                        }
                    })
                })?;
                Some(bit_vector(width, result))
            }
            "bvsub" if args.len() == 2 => {
                let (width, values) = self.eval_bit_vectors(args, depth)?;
                let modulus = BigInt::one() << width;
                Some(bit_vector(width, &values[0] + modulus - &values[1]))
            }
            "concat" if args.len() >= 2 => {
                let mut width = 0u32;
                let mut result = BigInt::zero();
                for &arg in args {
                    let Value::BitVec {
                        width: part_width,
                        value,
                    } = self.eval(arg, depth)?
                    else {
                        return None;
                    };
                    width = width.checked_add(part_width)?;
                    self.check_estimated_bits(u64::from(width))?;
                    result = (result << part_width) | value;
                }
                Some(bit_vector(width, result))
            }
            // Unsigned value; `bv2int` is Z3's name for SMT-LIB `bv2nat`.
            "bv2nat" | "bv2int" | "ubv_to_int" if args.len() == 1 => {
                let Value::BitVec { value, .. } = self.eval(args[0], depth)? else {
                    return None;
                };
                Some(Value::Int(value))
            }
            _ => self.eval_unsigned_order(name, args, depth),
        }
    }

    fn eval_indexed_app(
        &mut self,
        name: &str,
        indices: &[u32],
        args: &[TermId],
        depth: usize,
    ) -> Option<Value> {
        match (name, indices, args) {
            // `((_ int2bv w) n)` is `n mod 2^w`.
            ("int2bv", [width], [arg]) if *width > 0 => {
                self.check_estimated_bits(u64::from(*width))?;
                let Value::Int(value) = self.eval(*arg, depth)? else {
                    return None;
                };
                let modulus = BigInt::one() << *width;
                Some(bit_vector(*width, euclidean_mod(&value, &modulus)))
            }
            ("extract", [high, low], [arg]) if high >= low => {
                let Value::BitVec { width, value } = self.eval(*arg, depth)? else {
                    return None;
                };
                if *high >= width {
                    return None;
                }
                Some(bit_vector(high - low + 1, value >> *low))
            }
            ("zero_extend", [extra], [arg]) => {
                let Value::BitVec { width, value } = self.eval(*arg, depth)? else {
                    return None;
                };
                let width = width.checked_add(*extra)?;
                self.check_estimated_bits(u64::from(width))?;
                Some(bit_vector(width, value))
            }
            _ => None,
        }
    }

    /// Evaluate same-width bit-vector operands.
    fn eval_bit_vectors(&mut self, args: &[TermId], depth: usize) -> Option<(u32, Vec<BigInt>)> {
        let mut width = None;
        let mut values = Vec::with_capacity(args.len());
        for &arg in args {
            let Value::BitVec {
                width: arg_width,
                value,
            } = self.eval(arg, depth)?
            else {
                return None;
            };
            if *width.get_or_insert(arg_width) != arg_width {
                return None;
            }
            values.push(value);
        }
        Some((width?, values))
    }

    fn eval_values(&mut self, args: &[TermId], depth: usize) -> Option<Vec<Value>> {
        let mut values = Vec::with_capacity(args.len());
        for &arg in args {
            values.push(self.eval(arg, depth)?);
        }
        Some(values)
    }

    fn eval_bools(&mut self, args: &[TermId], depth: usize) -> Option<Vec<bool>> {
        self.eval_values(args, depth)?
            .into_iter()
            .map(|value| match value {
                Value::Bool(value) => Some(value),
                _ => None,
            })
            .collect()
    }

    fn eval_add(&self, values: Vec<Value>) -> Option<Value> {
        match values.first()? {
            Value::Int(_) => {
                let mut sum = BigInt::zero();
                for value in values {
                    let Value::Int(value) = value else {
                        return None;
                    };
                    self.check_estimated_bits(sum.bits().max(value.bits()).saturating_add(1))?;
                    sum += value;
                }
                Some(Value::Int(sum))
            }
            Value::Real(_) => {
                let mut sum = BigRational::zero();
                for value in values {
                    let Value::Real(value) = value else {
                        return None;
                    };
                    self.check_rational_add(&sum, &value)?;
                    sum += value;
                }
                Some(Value::Real(sum))
            }
            Value::Bool(_) | Value::BitVec { .. } => None,
        }
    }

    fn eval_sub(&self, mut values: Vec<Value>) -> Option<Value> {
        let first = values.drain(..1).next()?;
        if values.is_empty() {
            return match first {
                Value::Int(value) => Some(Value::Int(-value)),
                Value::Real(value) => Some(Value::Real(-value)),
                Value::Bool(_) | Value::BitVec { .. } => None,
            };
        }
        match first {
            Value::Int(mut difference) => {
                for value in values {
                    let Value::Int(value) = value else {
                        return None;
                    };
                    self.check_estimated_bits(
                        difference.bits().max(value.bits()).saturating_add(1),
                    )?;
                    difference -= value;
                }
                Some(Value::Int(difference))
            }
            Value::Real(mut difference) => {
                for value in values {
                    let Value::Real(value) = value else {
                        return None;
                    };
                    self.check_rational_add(&difference, &value)?;
                    difference -= value;
                }
                Some(Value::Real(difference))
            }
            Value::Bool(_) | Value::BitVec { .. } => None,
        }
    }

    fn eval_mul(&self, values: Vec<Value>) -> Option<Value> {
        match values.first()? {
            Value::Int(_) => {
                let mut product = BigInt::one();
                for value in values {
                    let Value::Int(value) = value else {
                        return None;
                    };
                    self.check_estimated_bits(product.bits().saturating_add(value.bits()))?;
                    product *= value;
                }
                Some(Value::Int(product))
            }
            Value::Real(_) => {
                let mut product = BigRational::one();
                for value in values {
                    let Value::Real(value) = value else {
                        return None;
                    };
                    self.check_rational_mul(&product, &value)?;
                    product *= value;
                }
                Some(Value::Real(product))
            }
            Value::Bool(_) | Value::BitVec { .. } => None,
        }
    }

    fn eval_real_div(&self, values: Vec<Value>) -> Option<Value> {
        let mut values = values.into_iter();
        let Value::Real(mut quotient) = values.next()? else {
            return None;
        };
        for value in values {
            let Value::Real(value) = value else {
                return None;
            };
            if value.is_zero() {
                return None;
            }
            self.check_rational_div(&quotient, &value)?;
            quotient /= value;
        }
        Some(Value::Real(quotient))
    }

    fn eval_comparison(&self, name: &str, values: &[Value]) -> Option<bool> {
        match values.first()? {
            Value::Int(_) => values.windows(2).try_fold(true, |acc, pair| {
                let [Value::Int(left), Value::Int(right)] = pair else {
                    return None;
                };
                Some(acc && compare(name, left, right)?)
            }),
            Value::Real(_) => values.windows(2).try_fold(true, |acc, pair| {
                let [Value::Real(left), Value::Real(right)] = pair else {
                    return None;
                };
                Some(acc && compare(name, left, right)?)
            }),
            Value::Bool(_) | Value::BitVec { .. } => None,
        }
    }

    fn check_rational_add(&self, left: &BigRational, right: &BigRational) -> Option<()> {
        let left_cross = left.numer().bits().saturating_add(right.denom().bits());
        let right_cross = right.numer().bits().saturating_add(left.denom().bits());
        let numerator = left_cross.max(right_cross).saturating_add(1);
        let denominator = left.denom().bits().saturating_add(right.denom().bits());
        self.check_estimated_bits(numerator.saturating_add(denominator))
    }

    fn check_rational_mul(&self, left: &BigRational, right: &BigRational) -> Option<()> {
        let numerator = left.numer().bits().saturating_add(right.numer().bits());
        let denominator = left.denom().bits().saturating_add(right.denom().bits());
        self.check_estimated_bits(numerator.saturating_add(denominator))
    }

    fn check_rational_div(&self, left: &BigRational, right: &BigRational) -> Option<()> {
        let numerator = left.numer().bits().saturating_add(right.denom().bits());
        let denominator = left.denom().bits().saturating_add(right.numer().bits());
        self.check_estimated_bits(numerator.saturating_add(denominator))
    }
}

fn supported_builtin_name(name: &str) -> bool {
    matches!(
        name,
        "not"
            | "and"
            | "or"
            | "=>"
            | "implies"
            | "xor"
            | "ite"
            | "="
            | "distinct"
            | "+"
            | "-"
            | "*"
            | "/"
            | "<"
            | "<="
            | ">"
            | ">="
            | "to_real"
            | "to_int"
            | "is_int"
            | "div"
            | "mod"
            | "rem"
            | "bvnot"
            | "bvneg"
            | "bvand"
            | "bvor"
            | "bvxor"
            | "bvadd"
            | "bvsub"
            | "bvmul"
            | "concat"
            | "bv2nat"
            | "bv2int"
            | "ubv_to_int"
    ) || unsigned_order::UNSIGNED_ORDERS.contains(&name)
}

/// Indexed heads interpreted by [`Evaluator::eval_indexed_app`].
fn supported_indexed_name(name: &str, index_count: usize) -> bool {
    matches!(
        (name, index_count),
        ("int2bv" | "zero_extend", 1) | ("extract", 2)
    )
}

/// A `width`-bit vector holding `value mod 2^width`.
fn bit_vector(width: u32, value: BigInt) -> Value {
    let modulus = BigInt::one() << width;
    Value::BitVec {
        width,
        value: euclidean_mod(&value, &modulus),
    }
}

fn compare<T: Ord>(name: &str, left: &T, right: &T) -> Option<bool> {
    match name {
        "<" => Some(left < right),
        "<=" => Some(left <= right),
        ">" => Some(left > right),
        ">=" => Some(left >= right),
        _ => None,
    }
}

/// SMT-LIB Euclidean remainder: `0 <= mod(a,b) < |b|` for `b != 0`.
fn euclidean_mod(dividend: &BigInt, divisor: &BigInt) -> BigInt {
    let modulus = divisor.abs();
    let remainder = dividend % &modulus;
    if remainder.is_negative() {
        remainder + modulus
    } else {
        remainder
    }
}

/// Mathematical floor, not Rust's truncation toward zero.
fn rational_floor(value: &BigRational) -> BigInt {
    let numerator = value.numer();
    let denominator = value.denom();
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if numerator.is_negative() && !remainder.is_zero() {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

/// Recognize one closed, well-sorted ground arithmetic/Boolean truth.
///
/// This is intentionally a literal-level API so a proof producer can ask the
/// exact same independent checker whether an `evaluate` step will be admitted.
#[must_use]
pub fn recognize_ground_evaluate(terms: &TermStore, literal: TermId) -> bool {
    if literal.index() >= terms.len() || terms.sort(literal) != &Sort::Bool {
        return false;
    }
    matches!(
        Evaluator::new(terms).eval(literal, 0),
        Some(Value::Bool(true))
    )
}

/// Strictly validate the Alethe `evaluate` schema for the arithmetic fragment.
pub(crate) fn validate_ground_evaluate(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("evaluate: {reason}"),
    };
    if premise_count != 0 {
        return Err(invalid("ground evaluation must not have premises"));
    }
    if !args.is_empty() {
        return Err(invalid("ground evaluation must not have arguments"));
    }
    let [literal] = clause else {
        return Err(invalid("ground evaluation must conclude one literal"));
    };
    if literal.index() >= terms.len() || terms.sort(*literal) != &Sort::Bool {
        return Err(invalid("conclusion must have Bool sort"));
    }
    let TermData::App(Symbol::Named(name), equality_args) = terms.get(*literal) else {
        return Err(invalid("conclusion must be an equality application"));
    };
    let [evaluated_term, expected_term] = equality_args.as_slice() else {
        return Err(invalid("conclusion must be a binary equality"));
    };
    if name != "=" {
        return Err(invalid("conclusion must be a binary equality"));
    }

    // Carcara's `evaluate` rule is deliberately directional: its right-hand
    // side is already a literal constant, and it evaluates only the left-hand
    // term.  Do not accept an arbitrary true Boolean expression here even
    // though `recognize_ground_evaluate` can prove one for producer-internal
    // use.
    let expected = supported_constant(terms, *expected_term)
        .ok_or_else(|| invalid("right-hand side must be a Bool, Int, or Real constant"))?;
    let actual = Evaluator::new(terms)
        .eval(*evaluated_term, 0)
        .ok_or_else(|| invalid("left-hand side is not a supported closed ground term"))?;
    if actual != expected {
        return Err(invalid(
            "left-hand side does not evaluate to the asserted constant",
        ));
    }
    Ok(())
}

fn supported_constant(terms: &TermStore, term: TermId) -> Option<Value> {
    if term.index() >= terms.len() {
        return None;
    }
    let value = match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Value::Bool(*value),
        TermData::Const(Constant::Int(value)) if value.bits().max(1) <= MAX_VALUE_BITS => {
            Value::Int(value.clone())
        }
        TermData::Const(Constant::Rational(value))
            if value
                .0
                .numer()
                .bits()
                .max(1)
                .saturating_add(value.0.denom().bits().max(1))
                <= MAX_VALUE_BITS =>
        {
            Value::Real(value.0.clone())
        }
        _ => return None,
    };
    value.matches_sort(terms.sort(term)).then_some(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
        terms.mk_app(Symbol::named(name), args, sort)
    }

    fn raw_eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
        app(terms, "=", &[left, right], Sort::Bool)
    }

    fn indexed(
        terms: &mut TermStore,
        name: &str,
        indices: Vec<u32>,
        args: &[TermId],
        sort: Sort,
    ) -> TermId {
        terms.mk_app(Symbol::indexed(name, indices), args, sort)
    }

    fn bv(width: u32) -> Sort {
        Sort::BitVec(ay_core::BitVecSort::new(width))
    }

    /// `(bv2int ((_ extract 3 0) (bvand (bvnot ((_ int2bv 8) 8))
    /// (bvsub ((_ int2bv 8) 8) ((_ int2bv 8) 1)))))`: the low bits below the
    /// lowest set bit of 8, i.e. `7`.
    fn trailing_mask(terms: &mut TermStore) -> TermId {
        let eight = terms.mk_int(BigInt::from(8));
        let one = terms.mk_int(BigInt::from(1));
        let eight_bv = indexed(terms, "int2bv", vec![8], &[eight], bv(8));
        let one_bv = indexed(terms, "int2bv", vec![8], &[one], bv(8));
        let not_eight = app(terms, "bvnot", &[eight_bv], bv(8));
        let seven_bv = app(terms, "bvsub", &[eight_bv, one_bv], bv(8));
        let mask = app(terms, "bvand", &[not_eight, seven_bv], bv(8));
        let low = indexed(terms, "extract", vec![3, 0], &[mask], bv(4));
        app(terms, "bv2int", &[low], Sort::Int)
    }

    #[test]
    fn evaluates_closed_bit_vector_arithmetic_through_integer_conversions() {
        let mut terms = TermStore::new();
        let mask = trailing_mask(&mut terms);
        let seven = terms.mk_int(BigInt::from(7));
        let equality = raw_eq(&mut terms, mask, seven);
        assert!(recognize_ground_evaluate(&terms, equality));
        assert!(validate_ground_evaluate(&terms, ProofId(0), &[equality], 0, &[]).is_ok());

        // Mutant: any other value is refused.
        let eight = terms.mk_int(BigInt::from(8));
        let wrong = raw_eq(&mut terms, mask, eight);
        assert!(!recognize_ground_evaluate(&terms, wrong));
        assert!(validate_ground_evaluate(&terms, ProofId(0), &[wrong], 0, &[]).is_err());
    }

    #[test]
    fn bit_vector_evaluation_wraps_and_concatenates_exactly() {
        let mut terms = TermStore::new();
        // `((_ int2bv 4) -1)` is `#xF`; `bv2nat` of its concatenation with
        // `#x1` is 0xF1.
        let minus_one = terms.mk_int(BigInt::from(-1));
        let wrapped = indexed(&mut terms, "int2bv", vec![4], &[minus_one], bv(4));
        let low = terms.mk_bitvec(BigInt::from(1), 4);
        let joined = app(&mut terms, "concat", &[wrapped, low], bv(8));
        let value = app(&mut terms, "bv2nat", &[joined], Sort::Int);
        let expected = terms.mk_int(BigInt::from(0xF1));
        let equality = raw_eq(&mut terms, value, expected);
        assert!(recognize_ground_evaluate(&terms, equality));

        // `bvneg`/`bvadd` wrap modulo 2^w; `zero_extend` keeps the value.
        let three = terms.mk_bitvec(BigInt::from(3), 4);
        let negated = app(&mut terms, "bvneg", &[three], bv(4));
        let sum = app(&mut terms, "bvadd", &[negated, three], bv(4));
        let widened = indexed(&mut terms, "zero_extend", vec![4], &[sum], bv(8));
        let zero = app(&mut terms, "bv2nat", &[widened], Sort::Int);
        let zero_value = terms.mk_int(BigInt::zero());
        let zero_equality = raw_eq(&mut terms, zero, zero_value);
        assert!(recognize_ground_evaluate(&terms, zero_equality));
    }

    #[test]
    fn bit_vector_evaluation_refuses_ill_formed_operands() {
        let mut terms = TermStore::new();
        let four_bits = terms.mk_bitvec(BigInt::from(1), 4);
        let eight_bits = terms.mk_bitvec(BigInt::from(1), 8);
        // Width mismatch.
        let mixed = app(&mut terms, "bvand", &[four_bits, eight_bits], bv(4));
        let mixed_value = app(&mut terms, "bv2nat", &[mixed], Sort::Int);
        let one = terms.mk_int(BigInt::from(1));
        let mixed_equality = raw_eq(&mut terms, mixed_value, one);
        assert!(!recognize_ground_evaluate(&terms, mixed_equality));
        // Extract beyond the operand width.
        let beyond = indexed(&mut terms, "extract", vec![4, 0], &[four_bits], bv(5));
        let beyond_value = app(&mut terms, "bv2nat", &[beyond], Sort::Int);
        let beyond_equality = raw_eq(&mut terms, beyond_value, one);
        assert!(!recognize_ground_evaluate(&terms, beyond_equality));
        // A free bit-vector variable is not closed.
        let free = terms.mk_var("b", bv(4));
        let free_value = app(&mut terms, "bv2nat", &[free], Sort::Int);
        let free_equality = raw_eq(&mut terms, free_value, one);
        assert!(!recognize_ground_evaluate(&terms, free_equality));
    }

    #[test]
    fn recognizes_boolean_integer_and_ite_truths() {
        let mut terms = TermStore::new();
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));
        let sum = app(&mut terms, "+", &[one, two], Sort::Int);
        let sum_eq = raw_eq(&mut terms, sum, three);
        let false_term = terms.false_term();
        let not_false = app(&mut terms, "not", &[false_term], Sort::Bool);
        let condition = terms.true_term();
        let selected = app(
            &mut terms,
            "ite",
            &[condition, sum_eq, not_false],
            Sort::Bool,
        );
        let truth = app(&mut terms, "and", &[sum_eq, selected], Sort::Bool);

        assert!(recognize_ground_evaluate(&terms, truth));
    }

    #[test]
    fn recognizes_nary_arithmetic_comparisons_and_boolean_operators() {
        let mut terms = TermStore::new();
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));
        let six = terms.mk_int(BigInt::from(6));
        let minus_two = terms.mk_int(BigInt::from(-2));

        let unary_minus = app(&mut terms, "-", &[two], Sort::Int);
        let unary_minus_eq = raw_eq(&mut terms, unary_minus, minus_two);
        let nary_minus = app(&mut terms, "-", &[six, three, one], Sort::Int);
        let nary_minus_eq = raw_eq(&mut terms, nary_minus, two);
        let product = app(&mut terms, "*", &[one, two, three], Sort::Int);
        let product_eq = raw_eq(&mut terms, product, six);
        let comparison = app(&mut terms, "<", &[one, two, three], Sort::Bool);
        let distinct = app(&mut terms, "distinct", &[one, two, three], Sort::Bool);

        let true_term = terms.true_term();
        let false_term = terms.false_term();
        let xor = app(&mut terms, "xor", &[true_term, false_term], Sort::Bool);
        let implication = app(
            &mut terms,
            "=>",
            &[false_term, false_term, false_term],
            Sort::Bool,
        );
        let truth = app(
            &mut terms,
            "and",
            &[
                unary_minus_eq,
                nary_minus_eq,
                product_eq,
                comparison,
                distinct,
                xor,
                implication,
            ],
            Sort::Bool,
        );

        assert!(recognize_ground_evaluate(&terms, truth));
    }

    #[test]
    fn recognizes_real_conversion_floor_and_integrality() {
        let mut terms = TermStore::new();
        let negative_three_halves =
            terms.mk_rational(BigRational::new(BigInt::from(-3), BigInt::from(2)));
        let minus_two = terms.mk_int(BigInt::from(-2));
        let floor = app(&mut terms, "to_int", &[negative_three_halves], Sort::Int);
        let floor_eq = raw_eq(&mut terms, floor, minus_two);

        let three = terms.mk_int(BigInt::from(3));
        let three_real = app(&mut terms, "to_real", &[three], Sort::Real);
        let is_int = app(&mut terms, "is_int", &[three_real], Sort::Bool);
        let truth = app(&mut terms, "and", &[floor_eq, is_int], Sort::Bool);

        assert!(recognize_ground_evaluate(&terms, truth));
    }

    #[test]
    fn recognizes_exact_real_division() {
        let mut terms = TermStore::new();
        let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
        let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
        let three_halves = terms.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
        let quotient = app(&mut terms, "/", &[three, two], Sort::Real);
        let truth = raw_eq(&mut terms, quotient, three_halves);

        assert!(recognize_ground_evaluate(&terms, truth));
    }

    #[test]
    fn recognizes_exact_real_add_subtract_and_multiply() {
        let mut terms = TermStore::new();
        let half = terms.mk_rational(BigRational::new(BigInt::one(), BigInt::from(2)));
        let three_halves = terms.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
        let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
        let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

        let sum = app(&mut terms, "+", &[half, three_halves], Sort::Real);
        let sum_eq = raw_eq(&mut terms, sum, two);
        let difference = app(&mut terms, "-", &[three_halves, half], Sort::Real);
        let one = terms.mk_rational(BigRational::one());
        let difference_eq = raw_eq(&mut terms, difference, one);
        let product = app(&mut terms, "*", &[half, two, three], Sort::Real);
        let product_eq = raw_eq(&mut terms, product, three);
        let truth = app(
            &mut terms,
            "and",
            &[sum_eq, difference_eq, product_eq],
            Sort::Bool,
        );

        assert!(recognize_ground_evaluate(&terms, truth));
    }

    #[test]
    fn div_mod_and_rem_follow_euclidean_and_z3_sign_rules() {
        let mut terms = TermStore::new();
        let seven = terms.mk_int(BigInt::from(7));
        let minus_two = terms.mk_int(BigInt::from(-2));
        let minus_three = terms.mk_int(BigInt::from(-3));
        let one = terms.mk_int(BigInt::from(1));
        let minus_one = terms.mk_int(BigInt::from(-1));

        let div = app(&mut terms, "div", &[seven, minus_two], Sort::Int);
        let modulo = app(&mut terms, "mod", &[seven, minus_two], Sort::Int);
        let rem = app(&mut terms, "rem", &[seven, minus_two], Sort::Int);
        let div_eq = raw_eq(&mut terms, div, minus_three);
        let mod_eq = raw_eq(&mut terms, modulo, one);
        let rem_eq = raw_eq(&mut terms, rem, minus_one);
        let truth = app(&mut terms, "and", &[div_eq, mod_eq, rem_eq], Sort::Bool);

        assert!(recognize_ground_evaluate(&terms, truth));
    }

    #[test]
    fn rejects_false_symbolic_uf_binder_and_unsupported_literals() {
        let mut terms = TermStore::new();
        let one = terms.mk_int(BigInt::from(1));
        let two = terms.mk_int(BigInt::from(2));
        let false_eq = raw_eq(&mut terms, one, two);
        assert!(!recognize_ground_evaluate(&terms, false_eq));

        let variable = terms.mk_var("x", Sort::Int);
        let symbolic_eq = raw_eq(&mut terms, variable, variable);
        assert!(!recognize_ground_evaluate(&terms, symbolic_eq));

        let uf = app(&mut terms, "f", &[one], Sort::Int);
        let uf_eq = raw_eq(&mut terms, uf, uf);
        assert!(!recognize_ground_evaluate(&terms, uf_eq));

        let quantified = terms.mk_forall(vec![("x".to_string(), Sort::Int)], false_eq);
        assert!(!recognize_ground_evaluate(&terms, quantified));

        let indexed = terms.mk_app(Symbol::indexed("mystery", vec![0]), [one], Sort::Int);
        let indexed_eq = raw_eq(&mut terms, indexed, indexed);
        assert!(!recognize_ground_evaluate(&terms, indexed_eq));
    }

    #[test]
    fn rejects_zero_divisors_wrong_sorts_and_shadowed_conversions() {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(BigInt::zero());
        let one = terms.mk_int(BigInt::one());
        let division = app(&mut terms, "div", &[one, zero], Sort::Int);
        let division_eq = raw_eq(&mut terms, division, zero);
        assert!(!recognize_ground_evaluate(&terms, division_eq));

        let ill_sorted_sum = app(&mut terms, "+", &[one, one], Sort::Real);
        let rational_two = terms.mk_rational(BigRational::from(BigInt::from(2)));
        let ill_sorted_eq = raw_eq(&mut terms, ill_sorted_sum, rational_two);
        assert!(!recognize_ground_evaluate(&terms, ill_sorted_eq));

        let real_one = terms.mk_rational(BigRational::one());
        let to_real = app(&mut terms, "to_real", &[one], Sort::Real);
        let to_real_eq = raw_eq(&mut terms, to_real, real_one);
        assert!(recognize_ground_evaluate(&terms, to_real_eq));
        terms.mark_to_real_shadowed();
        assert!(!recognize_ground_evaluate(&terms, to_real_eq));

        let is_int = app(&mut terms, "is_int", &[real_one], Sort::Bool);
        assert!(recognize_ground_evaluate(&terms, is_int));
        terms.mark_is_int_shadowed();
        assert!(!recognize_ground_evaluate(&terms, is_int));
    }

    #[test]
    fn rejects_terms_beyond_the_depth_bound() {
        let mut terms = TermStore::new();
        let mut term = terms.true_term();
        for _ in 0..=MAX_EVAL_DEPTH {
            term = app(&mut terms, "not", &[term], Sort::Bool);
        }
        assert!(!recognize_ground_evaluate(&terms, term));
    }

    #[test]
    fn rejects_wide_applications_at_preallocation_work_gate() {
        let mut terms = TermStore::new();
        let arguments = vec![terms.true_term(); MAX_EVAL_WORK];
        let wide = app(&mut terms, "and", &arguments, Sort::Bool);
        let mut evaluator = Evaluator::new(&terms);

        assert_eq!(evaluator.eval(wide, 0), None);
        assert!(evaluator.work > MAX_EVAL_WORK);
        assert_eq!(evaluator.memo.get(&wide), Some(&None));
    }

    #[test]
    fn charges_each_owned_clone_returned_from_the_memo() {
        let mut terms = TermStore::new();
        let large_value = BigInt::one() << ((MAX_VALUE_BITS - 1) as usize);
        let large = terms.mk_int(large_value.clone());
        let repeated_count = (MAX_TOTAL_VALUE_BITS / MAX_VALUE_BITS + 1) as usize;
        let arguments = vec![large; repeated_count];
        let sum = app(&mut terms, "+", &arguments, Sort::Int);
        let expected = terms.mk_int(large_value * BigInt::from(repeated_count));
        let claim = raw_eq(&mut terms, sum, expected);

        // Charging a shared DAG node only once would admit this expression
        // while retaining `repeated_count` owned 64-Kibit clones in `values`.
        assert!(!recognize_ground_evaluate(&terms, claim));
    }

    #[test]
    fn strict_schema_rejects_oversized_rhs_before_cloning_it() {
        let mut terms = TermStore::new();
        let zero = terms.mk_int(BigInt::zero());
        let oversized = terms.mk_int(BigInt::one() << (MAX_VALUE_BITS as usize));
        let claim = raw_eq(&mut terms, zero, oversized);

        validate_ground_evaluate(&terms, ProofId(0), &[claim], 0, &[])
            .expect_err("an oversized expected literal is outside the evaluation envelope");
    }

    #[test]
    fn strict_schema_rejects_premises_arguments_and_non_unit_clauses() {
        let mut terms = TermStore::new();
        let one = terms.mk_int(BigInt::one());
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));
        let sum = app(&mut terms, "+", &[one, two], Sort::Int);
        let evaluation = raw_eq(&mut terms, sum, three);
        let step = ProofId(7);

        validate_ground_evaluate(&terms, step, &[evaluation], 0, &[])
            .expect("one premise-free equality to a constant is a valid evaluate step");
        validate_ground_evaluate(&terms, step, &[evaluation], 1, &[])
            .expect_err("evaluate must not consume premises");
        validate_ground_evaluate(&terms, step, &[evaluation], 0, &[one])
            .expect_err("evaluate must not consume arguments");
        validate_ground_evaluate(&terms, step, &[evaluation, evaluation], 0, &[])
            .expect_err("evaluate must conclude exactly one literal");
    }

    #[test]
    fn strict_schema_rejects_bare_truth_nonconstant_rhs_and_wrong_value() {
        let mut terms = TermStore::new();
        let truth = terms.true_term();
        let one = terms.mk_int(BigInt::one());
        let two = terms.mk_int(BigInt::from(2));
        let three = terms.mk_int(BigInt::from(3));
        let sum = app(&mut terms, "+", &[one, two], Sort::Int);
        let nonconstant_rhs = app(&mut terms, "+", &[one, two], Sort::Int);
        let rhs_expression = raw_eq(&mut terms, three, nonconstant_rhs);
        let wrong_value = raw_eq(&mut terms, sum, two);

        validate_ground_evaluate(&terms, ProofId(0), &[truth], 0, &[])
            .expect_err("an arbitrary true Boolean is not Carcara evaluate syntax");
        validate_ground_evaluate(&terms, ProofId(0), &[rhs_expression], 0, &[])
            .expect_err("evaluate requires an already-constant right-hand side");
        validate_ground_evaluate(&terms, ProofId(0), &[wrong_value], 0, &[])
            .expect_err("evaluate must compare against the exact computed value");
    }
}
