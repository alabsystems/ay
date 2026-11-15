// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::mem::size_of;

pub(super) fn bigint(
    value: &num_bigint::BigInt,
    owner: &dyn TermConstructionAdmission,
    usage: PayloadUse,
) -> Result<()> {
    integer_bits(value.bits(), owner, usage)
}

pub(super) fn unsigned(
    value: &num_bigint::BigUint,
    owner: &dyn TermConstructionAdmission,
    usage: PayloadUse,
) -> Result<()> {
    integer_bits(value.bits(), owner, usage)
}

fn integer_bits(bits: u64, owner: &dyn TermConstructionAdmission, usage: PayloadUse) -> Result<()> {
    let bits = usize::try_from(bits).map_err(|_| storage::work(owner))?;
    let bytes = bits
        .checked_add(63)
        .and_then(|n| (n / 64).max(1).checked_mul(8))
        .ok_or_else(|| storage::storage(owner))?;
    owner.admit(
        bytes.checked_add(1).ok_or_else(|| storage::work(owner))?,
        usage.bytes(bytes),
    )?;
    Ok(())
}

pub(super) fn visit(
    term: &TermData,
    sort: &Sort,
    owner: &dyn TermConstructionAdmission,
    usage: PayloadUse,
) -> Result<()> {
    owner.admit(1, 0)?;
    sorts::visit(sort, owner, usage)?;
    match term {
        TermData::Const(Constant::Bool(_)) | TermData::Not(_) | TermData::Ite(..) => {}
        TermData::Const(Constant::FiniteField { value, field }) => {
            if *value >= field.modulus() || sort != &Sort::FiniteField(*field) {
                return Err(CountedTermError::InvalidInput);
            }
        }
        TermData::Const(Constant::BitVec { value, .. }) => bigint(value, owner, usage)?,
        TermData::Var(name, _) => {
            owner.admit(
                name.len()
                    .checked_add(1)
                    .ok_or_else(|| storage::work(owner))?,
                usage.bytes(name.len()),
            )?;
        }
        TermData::App(symbol, args) => {
            let bytes = args
                .len()
                .checked_mul(size_of::<TermId>())
                .ok_or_else(|| storage::storage(owner))?;
            owner.admit(
                args.len()
                    .checked_add(1)
                    .ok_or_else(|| storage::work(owner))?,
                usage.bytes(bytes),
            )?;
            owner.admit(
                symbol
                    .name()
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| storage::work(owner))?,
                0,
            )?;
            if let Symbol::Indexed(_, indices) = symbol {
                let bytes = indices
                    .len()
                    .checked_mul(size_of::<u32>())
                    .ok_or_else(|| storage::storage(owner))?;
                owner.admit(
                    indices
                        .len()
                        .checked_add(1)
                        .ok_or_else(|| storage::work(owner))?,
                    usage.bytes(bytes),
                )?;
            }
        }
        _ => return Err(CountedTermError::Unsupported),
    }
    Ok(())
}

pub(super) fn application(
    symbol: Symbol,
    args: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<TermData> {
    let mut copied = Vec::new();
    storage::reserve(&mut copied, args.len(), owner)?;
    owner.admit(args.len(), 0)?;
    copied.extend_from_slice(args);
    Ok(TermData::App(symbol, copied))
}

pub(super) fn named(
    name: &str,
    args: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<TermData> {
    owner.admit(
        name.len()
            .checked_add(1)
            .ok_or_else(|| storage::work(owner))?,
        name.len()
            .checked_add(128)
            .ok_or_else(|| storage::storage(owner))?,
    )?;
    application(Symbol::named(storage::text(name, owner)?), args, owner)
}

pub(super) fn copy(term: &TermData, owner: &dyn TermConstructionAdmission) -> Result<TermData> {
    match term {
        TermData::App(symbol, args) => {
            let symbol = match symbol {
                Symbol::Named(name) => Symbol::Named(name.clone()),
                Symbol::Indexed(name, indices) => {
                    let mut copied = Vec::new();
                    storage::reserve(&mut copied, indices.len(), owner)?;
                    owner.admit(indices.len(), 0)?;
                    copied.extend_from_slice(indices);
                    Symbol::Indexed(name.clone(), copied)
                }
            };
            application(symbol, args, owner)
        }
        TermData::Var(name, id) => Ok(TermData::Var(storage::text(name, owner)?, *id)),
        TermData::Const(
            Constant::Bool(_) | Constant::BitVec { .. } | Constant::FiniteField { .. },
        )
        | TermData::Not(_)
        | TermData::Ite(..) => Ok(term.clone()),
        _ => Err(CountedTermError::Unsupported),
    }
}
