// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Price complete borrowed Hash/Eq payloads without performing either yet.

use std::mem::size_of;

use num_bigint::BigInt;

use super::*;
use meter::{add, mul};

fn string(value: &str, meter: &mut CanonicalMeter<'_>) -> Result<usize, ProofCheckError> {
    meter.charge(1, 0)?;
    add(value.len(), 16)
}

fn slice<T>(value: &[T], meter: &mut CanonicalMeter<'_>) -> Result<usize, ProofCheckError> {
    meter.charge(1, 0)?;
    add(mul(value.len(), size_of::<T>())?, 16)
}

fn integer(value: &BigInt, meter: &mut CanonicalMeter<'_>) -> Result<usize, ProofCheckError> {
    meter.charge(1, 0)?;
    // u32 iterator length is O(1). Sixteen extra units cover the sign,
    // length, and a partially occupied native u64 limb on 64-bit hosts.
    add(mul(value.iter_u32_digits().len(), 4)?, 16)
}

fn constant(value: &Constant, meter: &mut CanonicalMeter<'_>) -> Result<usize, ProofCheckError> {
    meter.charge(1, 0)?;
    match value {
        Constant::Bool(_) | Constant::FiniteField { .. } => Ok(16),
        Constant::Int(value) | Constant::BitVec { value, .. } => integer(value, meter),
        Constant::Rational(value) => add(
            integer(value.0.numer(), meter)?,
            integer(value.0.denom(), meter)?,
        ),
        Constant::String(value) => string(value, meter),
        _ => Err(ProofCheckError::ResourceLimit),
    }
}

fn symbol(value: &Symbol, meter: &mut CanonicalMeter<'_>) -> Result<usize, ProofCheckError> {
    meter.charge(1, 0)?;
    match value {
        Symbol::Named(name) => string(name, meter),
        Symbol::Indexed(name, indices) => add(string(name, meter)?, slice(indices, meter)?),
        _ => Err(ProofCheckError::ResourceLimit),
    }
}

pub(super) fn data(
    value: &TermData,
    meter: &mut CanonicalMeter<'_>,
) -> Result<usize, ProofCheckError> {
    meter.charge(1, 0)?;
    let payload = match value {
        TermData::Const(value) => constant(value, meter)?,
        TermData::Var(name, _) => string(name, meter)?,
        TermData::App(function, args) => add(symbol(function, meter)?, slice(args, meter)?)?,
        TermData::Let(bindings, _) => {
            let mut work = slice(bindings, meter)?;
            for (name, _) in bindings {
                work = add(work, string(name, meter)?)?;
            }
            work
        }
        TermData::Forall(bindings, _, triggers) | TermData::Exists(bindings, _, triggers) => {
            let mut work = slice(bindings, meter)?;
            for (name, binding_sort) in bindings {
                work = add(work, string(name, meter)?)?;
                work = add(work, sort(binding_sort, meter, 0)?)?;
            }
            work = add(work, slice(triggers, meter)?)?;
            for trigger in triggers {
                work = add(work, slice(trigger, meter)?)?;
            }
            work
        }
        TermData::Not(_) | TermData::Ite(..) => 16,
        _ => return Err(ProofCheckError::ResourceLimit),
    };
    add(payload, 16)
}

pub(super) fn sort(
    value: &Sort,
    meter: &mut CanonicalMeter<'_>,
    depth: usize,
) -> Result<usize, ProofCheckError> {
    meter.charge(1, 0)?;
    if depth > 256 {
        return Err(ProofCheckError::ResourceLimit);
    }
    let payload = match value {
        Sort::Array(array) => add(
            sort(&array.index_sort, meter, add(depth, 1)?)?,
            sort(&array.element_sort, meter, add(depth, 1)?)?,
        )?,
        Sort::Seq(element) => sort(element, meter, add(depth, 1)?)?,
        Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
            string(name, meter)?
        }
        Sort::Datatype(datatype) => {
            let mut work = string(&datatype.name, meter)?;
            work = add(work, slice(&datatype.constructors, meter)?)?;
            for constructor in &datatype.constructors {
                work = add(work, string(&constructor.name, meter)?)?;
                work = add(work, slice(&constructor.fields, meter)?)?;
                for field in &constructor.fields {
                    work = add(work, string(&field.name, meter)?)?;
                    work = add(work, sort(&field.sort, meter, add(depth, 1)?)?)?;
                }
            }
            work
        }
        Sort::Bool
        | Sort::Int
        | Sort::Real
        | Sort::BitVec(_)
        | Sort::String
        | Sort::RegLan
        | Sort::FloatingPoint(..)
        | Sort::FiniteField(_)
        | Sort::Char => 16,
        _ => return Err(ProofCheckError::ResourceLimit),
    };
    add(payload, 16)
}
