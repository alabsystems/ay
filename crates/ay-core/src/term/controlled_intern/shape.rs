// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::term::Symbol;
use num_bigint::Sign;

mod sequence;
pub(super) fn admit_owned_sort(sort: &Sort, admission: &mut Admission<'_>) -> Result<SortCost> {
    sequence::admit(sort, admission)
}
pub(super) use sequence::SortCost;

fn scalar(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool)
        || matches!(sort, Sort::BitVec(width) if (1..=128).contains(&width.width))
}

pub(super) fn validate(
    store: &TermStore,
    term: &TermData,
    sort: &Sort,
    admission: &mut Admission<'_>,
) -> Result<Option<SortCost>> {
    admission.pay(16, 0)?;
    if matches!(term, TermData::App(Symbol::Named(name), args) if name == "seq.empty" && args.is_empty())
        && matches!(sort, Sort::Seq(_))
    {
        return sequence::admit(sort, admission).map(Some);
    }
    let admitted_sort = scalar(sort)
        || sort == &Sort::Int
        || matches!(sort,
        Sort::Array(array) if matches!(&array.index_sort,
            Sort::BitVec(width) if width.width == 64) && scalar(&array.element_sort))
        || matches!(sort, Sort::Array(array) if array.index_sort == Sort::Int
            && matches!(array.element_sort, Sort::Bool | Sort::Int));
    if !admitted_sort {
        return Err(ControlledTermInternError::UnsupportedFragment);
    }
    let live = |id: TermId| store.entry_stamp(id).is_some();
    match term {
        TermData::Const(Constant::Bool(_)) if sort == &Sort::Bool => Ok(()),
        TermData::Const(Constant::Int(_)) if sort == &Sort::Int => Ok(()),
        TermData::Const(Constant::BitVec { value, width })
            if matches!(sort, Sort::BitVec(s) if s.width == *width)
                && value.sign() != Sign::Minus
                && value.bits() <= u64::from(*width) =>
        {
            Ok(())
        }
        TermData::App(Symbol::Named(name), args) if name.len() <= 64 && args.len() <= 3 => {
            if args.iter().copied().all(live) {
                Ok(())
            } else {
                Err(ControlledTermInternError::InvalidInput)
            }
        }
        TermData::Not(arg) if live(*arg) => {
            if sort == &Sort::Bool && store.sort(*arg) == &Sort::Bool {
                Ok(())
            } else {
                Err(ControlledTermInternError::InvalidInput)
            }
        }
        TermData::Ite(c, t, e) if live(*c) && live(*t) && live(*e) => {
            if store.sort(*c) == &Sort::Bool && store.sort(*t) == sort && store.sort(*e) == sort {
                Ok(())
            } else {
                Err(ControlledTermInternError::InvalidInput)
            }
        }
        TermData::Not(_)
        | TermData::Ite(_, _, _)
        | TermData::Const(Constant::Int(_))
        | TermData::Const(Constant::BitVec { .. })
        | TermData::Const(Constant::Bool(_)) => Err(ControlledTermInternError::InvalidInput),
        _ => Err(ControlledTermInternError::UnsupportedFragment),
    }
    .map(|()| None)
}

pub(super) fn copy(term: &TermData) -> Result<TermData> {
    match term {
        TermData::App(symbol, args) => {
            let mut copied = Vec::new();
            copied
                .try_reserve_exact(args.len())
                .map_err(|_| ControlledTermInternError::ResourceLimit)?;
            copied.extend_from_slice(args);
            Ok(TermData::App(symbol.clone(), copied))
        }
        // Only the fixed-purpose fresh factory can reach this arm: public
        // shape validation above continues to reject caller-supplied Var data.
        TermData::Var(name, id) => {
            let mut copied = String::new();
            copied
                .try_reserve_exact(name.len())
                .map_err(|_| ControlledTermInternError::ResourceLimit)?;
            copied.push_str(name);
            Ok(TermData::Var(copied, *id))
        }
        TermData::Forall(..) | TermData::Exists(..) => Ok(term.clone()),
        TermData::Const(
            Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_) | Constant::BitVec { .. },
        )
        | TermData::Not(_)
        | TermData::Ite(_, _, _) => Ok(term.clone()),
        _ => Err(ControlledTermInternError::UnsupportedFragment),
    }
}

/// Owned payload is prepaid before hashing, collision comparison and copy.
/// Dedicated factories admit Var names; public shape validation stays unchanged.
pub(super) fn owned_payload_bytes(term: &TermData) -> Result<usize> {
    match term {
        TermData::Var(name, _) => Ok(name.len()),
        // The original bounded small-App envelope prepays its physical
        // payload. Extended native-proof nodes retain full payload pricing.
        TermData::App(Symbol::Named(name), args) if name.len() <= 64 && args.len() <= 3 => Ok(0),
        TermData::Const(Constant::Int(value)) => integer_magnitude_bytes(value.bits()),
        TermData::Const(Constant::Rational(value)) => {
            integer_magnitude_bytes(value.0.numer().bits())?
                .checked_add(integer_magnitude_bytes(value.0.denom().bits())?)
                .ok_or(ControlledTermInternError::ResourceLimit)
        }
        _ => Ok(super::native_proof::owned_payload(term)?.unwrap_or(0)),
    }
}

fn integer_magnitude_bytes(bits: u64) -> Result<usize> {
    usize::try_from(bits)
        .ok()
        .and_then(|bits| bits.checked_add(63))
        .and_then(|bits| (bits / 64).max(1).checked_mul(8))
        .ok_or(ControlledTermInternError::ResourceLimit)
}
