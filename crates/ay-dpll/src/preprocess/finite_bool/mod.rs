// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Original-owner finite integer/Boolean circuit preparation for enumeration.
//!
//! Boolean enumeration uses literal integer leaves; finite scalar enumeration
//! additionally derives Int-variable covers from original assertions. Interval
//! hulls and all intermediate arithmetic prefixes determine
//! one exact signed width, as in the ordinary `combined::int_blast` lane.
//! This is compilation DATA, never a model or an exhaustiveness certificate.

use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use ay_core::term::{
    reserve_counted, CountedBuiltin as Op, CountedTermBuilder, CountedTermError,
    TermStoreSnapshotStamp,
};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

mod bounds;
mod range;
use range::Range;
#[cfg(test)]
mod tests;

/// Versioned logical units cover source visits/edges, arbitrary-precision
/// arithmetic, scratch/copy storage and the existing counted term builder.
/// These are not CPU instructions or an allocator/RSS guarantee.
pub(crate) const WORK_VERSION: u32 = 3;

#[derive(Clone, Copy)]
enum Domains {
    BooleanLeaves,
    FiniteIntegers,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub(crate) enum Error {
    #[error(transparent)]
    Stopped(#[from] CountedAdmissionError),
    #[error("unsupported finite Boolean/integer source")]
    Unsupported,
    #[error("invalid finite Boolean/integer source identity or signature")]
    Invalid,
}
type Result<T> = std::result::Result<T, Error>;

impl From<CountedTermError> for Error {
    fn from(error: CountedTermError) -> Self {
        match error {
            CountedTermError::Stopped(error) => Self::Stopped(error),
            CountedTermError::Unsupported => Self::Unsupported,
            CountedTermError::InvalidInput | CountedTermError::ReadOnlySnapshot => Self::Invalid,
        }
    }
}

/// One immutable source snapshot and an exact scalar circuit in a fresh store.
/// Numeric source IDs and this stamp are data, not declaration authentication;
/// the native API must authenticate the caller's handles before compilation.
pub(crate) struct Compiled {
    pub(crate) terms: TermStore,
    pub(crate) roots: Vec<TermId>,
    pub(crate) projection: Vec<TermId>,
    pub(crate) leaves: Vec<(TermId, TermId)>,
    pub(crate) signed_width: u32,
    pub(crate) source_order: Vec<TermId>,
    source: TermStoreSnapshotStamp,
    original_roots: Vec<TermId>,
}

impl Compiled {
    pub(crate) fn matches_source(&self, terms: &TermStore, roots: &[TermId]) -> bool {
        self.source == terms.snapshot_stamp() && self.original_roots == roots
    }
}

fn overflow(owner: &CountedAdmission) -> Error {
    Error::Stopped(owner.refuse(CountedAdmissionError::WorkExhausted))
}
fn copy<T: Copy>(values: &[T], owner: &CountedAdmission) -> Result<Vec<T>> {
    owner.admit(values.len(), 0)?;
    let mut result = Vec::new();
    reserve_counted(&mut result, values.len(), owner)?;
    result.extend_from_slice(values);
    Ok(result)
}
fn slots<T>(n: usize, owner: &CountedAdmission) -> Result<Vec<Option<T>>> {
    let mut result = Vec::new();
    reserve_counted(&mut result, n, owner)?;
    owner.admit(n, 0)?;
    result.resize_with(n, || None);
    Ok(result)
}

/// Inspect the entire reached DAG, including every dead ITE arm. The postorder
/// is iterative and memoized; a child must precede its parent in the source.
fn order(
    source: &TermStore,
    roots: &[TermId],
    domains: Domains,
    owner: &CountedAdmission,
) -> Result<Vec<TermId>> {
    let mut status = Vec::new();
    reserve_counted(&mut status, source.len(), owner)?;
    owner.admit(source.len(), 0)?;
    status.resize(source.len(), 0u8);
    let mut pending = Vec::new();
    reserve_counted(&mut pending, roots.len(), owner)?;
    owner.admit(roots.len(), 0)?;
    pending.extend(roots.iter().copied().map(|id| (id, false)));
    let mut result = Vec::new();
    while let Some((id, finish)) = pending.pop() {
        owner.admit(1, 0)?;
        if id.index() >= source.len() {
            return Err(Error::Invalid);
        }
        if status[id.index()] == 2 {
            continue;
        }
        if finish {
            status[id.index()] = 2;
            reserve_counted(&mut result, 1, owner)?;
            result.push(id);
            continue;
        }
        if !matches!(source.sort(id), Sort::Bool | Sort::Int) {
            return Err(Error::Unsupported);
        }
        status[id.index()] = 1;
        reserve_counted(&mut pending, 1, owner)?;
        pending.push((id, true));
        let mut child = |value: TermId| -> Result<()> {
            owner.admit(1, 0)?;
            if value.index() >= id.index() {
                return Err(Error::Invalid);
            }
            reserve_counted(&mut pending, 1, owner)?;
            pending.push((value, false));
            Ok(())
        };
        match source.get(id) {
            TermData::Const(Constant::Bool(_)) | TermData::Const(Constant::Int(_)) => {}
            TermData::Var(_, _)
                if source.sort(id) == &Sort::Bool
                    || (matches!(domains, Domains::FiniteIntegers)
                        && source.sort(id) == &Sort::Int) => {}
            TermData::Not(value) => child(*value)?,
            TermData::Ite(c, t, e) => {
                child(*e)?;
                child(*t)?;
                child(*c)?;
            }
            TermData::App(Symbol::Named(name), args) => {
                owner.admit(
                    name.len()
                        .checked_add(args.len())
                        .ok_or_else(|| overflow(owner))?,
                    0,
                )?;
                if source.is_declared_function(name) {
                    return Err(Error::Unsupported);
                }
                for &argument in args.iter().rev() {
                    child(argument)?;
                }
            }
            _ => return Err(Error::Unsupported),
        }
    }
    Ok(result)
}

fn range<'a>(ranges: &'a [Option<Range>], id: TermId) -> Result<&'a Range> {
    ranges
        .get(id.index())
        .and_then(Option::as_ref)
        .ok_or(Error::Invalid)
}

fn integer_range(
    source: &TermStore,
    id: TermId,
    ranges: &[Option<Range>],
    leaf_bounds: &[Option<Range>],
    width: &mut u32,
    owner: &CountedAdmission,
) -> Result<Range> {
    let result = match source.get(id) {
        TermData::Const(Constant::Int(value)) => Range::point(value, owner)?,
        TermData::Var(..) => range(leaf_bounds, id)?.copied(owner)?,
        TermData::Ite(condition, yes, no) if source.sort(*condition) == &Sort::Bool => {
            range(ranges, *yes)?.hull(range(ranges, *no)?, owner)?
        }
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "div" | "mod") && args.len() == 2 =>
        {
            let result = if name == "div" {
                range::DivisionResult::Quotient
            } else {
                range::DivisionResult::Remainder
            };
            range(ranges, args[0])?.divided(range(ranges, args[1])?, result, owner)?
        }
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "+" | "-" | "*") && !args.is_empty() =>
        {
            let mut value = range(ranges, args[0])?.copied(owner)?;
            if name == "-" && args.len() == 1 {
                value = value.negated(owner)?;
            }
            for &arg in &args[1..] {
                value = match name.as_str() {
                    "+" => value.add(range(ranges, arg)?, owner)?,
                    "-" => value.sub(range(ranges, arg)?, owner)?,
                    "*" => value.mul(range(ranges, arg)?, owner)?,
                    _ => return Err(Error::Unsupported),
                };
                // The translated n-ary operation is a left fold. Its transient
                // prefix may exceed both the children and the final interval.
                *width = (*width).max(value.width()?);
            }
            value
        }
        _ => return Err(Error::Unsupported),
    };
    *width = (*width).max(result.width()?);
    Ok(result)
}

fn joined(
    builder: &mut CountedTermBuilder<'_, '_>,
    operation: Op,
    values: &[TermId],
) -> Result<TermId> {
    match values {
        [] => Ok(builder.boolean(operation == Op::And)?),
        [one] => Ok(*one),
        _ => Ok(builder.apply(operation, values)?),
    }
}

fn application(
    source: &TermStore,
    id: TermId,
    name: &str,
    args: &[TermId],
    width: u32,
    builder: &mut CountedTermBuilder<'_, '_>,
    owner: &CountedAdmission,
) -> Result<TermId> {
    if source.sort(id) == &Sort::Int {
        if matches!(name, "div" | "mod") && args.len() == 2 {
            let result = if name == "div" {
                range::DivisionResult::Quotient
            } else {
                range::DivisionResult::Remainder
            };
            return division_application(result, args[0], args[1], width, builder, owner);
        }
        let operation = match name {
            "+" => Op::BvAdd,
            "-" if args.len() == 1 => return Ok(builder.apply(Op::BvNeg, args)?),
            "-" => Op::BvSub,
            "*" => Op::BvMul,
            _ => return Err(Error::Unsupported),
        };
        let (&first, rest) = args.split_first().ok_or(Error::Invalid)?;
        return rest.iter().try_fold(first, |left, &right| {
            owner.admit(1, 0)?;
            Ok(builder.apply(operation, &[left, right])?)
        });
    }
    let operation = match name {
        "and" => return joined(builder, Op::And, args),
        "or" => return joined(builder, Op::Or, args),
        "not" if args.len() == 1 => Op::Not,
        "=>" if args.len() == 2 => Op::Implies,
        "xor" if args.len() == 2 => Op::Xor,
        "=" | "distinct" if args.len() >= 2 => {
            let mut pairs = Vec::new();
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    if name == "=" && i > 0 {
                        break;
                    }
                    owner.admit(1, 0)?;
                    reserve_counted(&mut pairs, 1, owner)?;
                    let equality = builder.apply(Op::Eq, &[args[i], args[j]])?;
                    pairs.push(if name == "distinct" {
                        builder.apply(Op::Not, &[equality])?
                    } else {
                        equality
                    });
                }
            }
            return joined(builder, Op::And, &pairs);
        }
        "<" if args.len() == 2 => Op::BvSLt,
        "<=" if args.len() == 2 => Op::BvSLe,
        ">" if args.len() == 2 => Op::BvSGt,
        ">=" if args.len() == 2 => Op::BvSGe,
        _ => return Err(Error::Unsupported),
    };
    Ok(builder.apply(operation, args)?)
}

/// Compile the entire exact ordered source and projection under one owner.
/// The resulting circuit must still undergo SAT, original model validation
/// and a strict original-source completeness check before enumeration grants.
pub(crate) fn compile(
    source: &TermStore,
    roots: &[TermId],
    projection: &[TermId],
    owner: &CountedAdmission,
) -> Result<Compiled> {
    compile_with_domains(source, roots, projection, Domains::BooleanLeaves, owner)
}

pub(crate) fn compile_finite(
    source: &TermStore,
    roots: &[TermId],
    projection: &[TermId],
    owner: &CountedAdmission,
) -> Result<Compiled> {
    compile_with_domains(source, roots, projection, Domains::FiniteIntegers, owner)
}

fn integer_literal(
    value: &BigInt,
    width: u32,
    builder: &mut CountedTermBuilder<'_, '_>,
    owner: &CountedAdmission,
) -> Result<TermId> {
    let bits = if value.is_negative() {
        range::pay_binary(width as u64, value.bits(), false, owner)?;
        (BigInt::one() << width) + value
    } else {
        range::paid_copy(value, owner)?
    };
    Ok(builder.bitvector(&bits, width)?)
}

fn compile_with_domains(
    source: &TermStore,
    roots: &[TermId],
    projection: &[TermId],
    domains: Domains,
    owner: &CountedAdmission,
) -> Result<Compiled> {
    owner.admit(1, 0)?;
    let mut all = copy(roots, owner)?;
    reserve_counted(&mut all, projection.len(), owner)?;
    owner.admit(projection.len(), 0)?;
    all.extend_from_slice(projection);
    for &root in roots {
        owner.admit(1, 0)?;
        if root.index() >= source.len() || source.sort(root) != &Sort::Bool {
            return Err(Error::Invalid);
        }
    }
    for &term in projection {
        owner.admit(1, 0)?;
        if term.index() >= source.len()
            || !(source.sort(term) == &Sort::Bool
                || (matches!(domains, Domains::FiniteIntegers) && source.sort(term) == &Sort::Int))
        {
            return Err(Error::Invalid);
        }
    }
    let order = order(source, &all, domains, owner)?;
    let leaf_bounds = match domains {
        Domains::BooleanLeaves => slots(source.len(), owner)?,
        Domains::FiniteIntegers => bounds::infer(source, roots, &order, owner)?,
    };
    let mut ranges = slots(source.len(), owner)?;
    let mut width = 2;
    for &id in &order {
        owner.admit(1, 0)?;
        if source.sort(id) == &Sort::Int {
            ranges[id.index()] = Some(integer_range(
                source,
                id,
                &ranges,
                &leaf_bounds,
                &mut width,
                owner,
            )?);
        }
    }
    let mut translated = TermStore::try_new_with_admission(owner)?;
    let mut mapping = slots(source.len(), owner)?;
    let mut leaves = Vec::new();
    let mut domain_roots = Vec::new();
    let mut builder = CountedTermBuilder::new(&mut translated, owner)?;
    for &id in &order {
        owner.admit(1, 0)?;
        let mapped =
            |child: TermId| -> Result<TermId> { mapping[child.index()].ok_or(Error::Invalid) };
        let value = match source.get(id) {
            TermData::Const(Constant::Bool(value)) => builder.boolean(*value)?,
            TermData::Const(Constant::Int(value)) => {
                integer_literal(value, width, &mut builder, owner)?
            }
            TermData::Var(name, _) if matches!(source.sort(id), Sort::Bool | Sort::Int) => {
                owner.admit(name.len(), 0)?;
                let name = ay_core::render_admission::format(
                    Some(owner),
                    format_args!("__ay_enum_{}", id.0),
                );
                owner.check()?;
                let sort = if source.sort(id) == &Sort::Bool {
                    Sort::Bool
                } else {
                    Sort::bitvec(width)
                };
                let value = builder.variable(&name, &sort)?;
                reserve_counted(&mut leaves, 1, owner)?;
                leaves.push((id, value));
                if source.sort(id) == &Sort::Int {
                    let interval = range(&leaf_bounds, id)?;
                    let lo = integer_literal(&interval.lo, width, &mut builder, owner)?;
                    let hi = integer_literal(&interval.hi, width, &mut builder, owner)?;
                    let lower = builder.apply(Op::BvSGe, &[value, lo])?;
                    let upper = builder.apply(Op::BvSLe, &[value, hi])?;
                    reserve_counted(&mut domain_roots, 2, owner)?;
                    domain_roots.extend([lower, upper]);
                }
                value
            }
            TermData::Not(child) => builder.apply(Op::Not, &[mapped(*child)?])?,
            TermData::Ite(c, t, e) => {
                builder.apply(Op::Ite, &[mapped(*c)?, mapped(*t)?, mapped(*e)?])?
            }
            TermData::App(Symbol::Named(name), args) => {
                owner.admit(
                    name.len()
                        .checked_add(args.len())
                        .ok_or_else(|| overflow(owner))?,
                    0,
                )?;
                let mut mapped_args = Vec::new();
                reserve_counted(&mut mapped_args, args.len(), owner)?;
                for &arg in args {
                    mapped_args.push(mapped(arg)?);
                }
                application(source, id, name, &mapped_args, width, &mut builder, owner)?
            }
            _ => return Err(Error::Unsupported),
        };
        if (source.sort(id) == &Sort::Bool) != (builder.terms().sort(value) == &Sort::Bool) {
            return Err(Error::Invalid);
        }
        mapping[id.index()] = Some(value);
    }
    builder.finish()?;
    let translate_list = |input: &[TermId]| -> Result<Vec<TermId>> {
        let mut out = Vec::new();
        reserve_counted(&mut out, input.len(), owner)?;
        owner.admit(input.len(), 0)?;
        for &id in input {
            out.push(mapping[id.index()].ok_or(Error::Invalid)?);
        }
        Ok(out)
    };
    let mut roots_translated = translate_list(roots)?;
    reserve_counted(&mut roots_translated, domain_roots.len(), owner)?;
    owner.admit(domain_roots.len(), 0)?;
    roots_translated.extend(domain_roots);
    let projection_translated = translate_list(projection)?;
    let original_roots = copy(roots, owner)?;
    owner.admit(1, std::mem::size_of::<Compiled>())?;
    drop(ranges);
    drop(mapping);
    drop(all);
    owner.check()?;
    Ok(Compiled {
        terms: translated,
        roots: roots_translated,
        projection: projection_translated,
        leaves,
        signed_width: width,
        source_order: order,
        source: source.snapshot_stamp(),
        original_roots,
    })
}

/// Convert truncating signed BV division/remainder to SMT-LIB Ints Euclidean
/// arithmetic. With r0 = a srem b, a negative remainder requires q0 +/- 1
/// (the direction follows b's sign) and r0 + abs(b). A source-derived nonzero
/// divisor property is checked by interval analysis before this circuit exists.
/// See https://smt-lib.org/theories-Ints.shtml (Boute's Euclidean definition).
fn division_application(
    result: range::DivisionResult,
    dividend: TermId,
    divisor: TermId,
    width: u32,
    builder: &mut CountedTermBuilder<'_, '_>,
    owner: &CountedAdmission,
) -> Result<TermId> {
    owner.admit(2, std::mem::size_of::<BigInt>() * 2 + 16)?;
    let zero = integer_literal(&BigInt::zero(), width, builder, owner)?;
    let one = integer_literal(&BigInt::one(), width, builder, owner)?;
    let remainder = builder.apply(Op::BvSRem, &[dividend, divisor])?;
    let negative_remainder = builder.apply(Op::BvSLt, &[remainder, zero])?;
    let negative_divisor = builder.apply(Op::BvSLt, &[divisor, zero])?;
    let (raw, adjusted) = match result {
        range::DivisionResult::Quotient => {
            let raw = builder.apply(Op::BvSDiv, &[dividend, divisor])?;
            let lower = builder.apply(Op::BvSub, &[raw, one])?;
            let upper = builder.apply(Op::BvAdd, &[raw, one])?;
            let adjusted = builder.apply(Op::Ite, &[negative_divisor, upper, lower])?;
            (raw, adjusted)
        }
        range::DivisionResult::Remainder => {
            let negated = builder.apply(Op::BvNeg, &[divisor])?;
            let magnitude = builder.apply(Op::Ite, &[negative_divisor, negated, divisor])?;
            let adjusted = builder.apply(Op::BvAdd, &[remainder, magnitude])?;
            (remainder, adjusted)
        }
    };
    Ok(builder.apply(Op::Ite, &[negative_remainder, adjusted, raw])?)
}
