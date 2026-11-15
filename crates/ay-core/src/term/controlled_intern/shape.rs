// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::term::Symbol;
use num_bigint::Sign;

fn scalar(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool)
        || matches!(sort, Sort::BitVec(width) if (1..=128).contains(&width.width))
}

pub(super) fn validate(
    store: &TermStore,
    term: &TermData,
    sort: &Sort,
    admission: &mut Admission<'_>,
) -> Result<()> {
    admission.pay(16, 0)?;
    let admitted_sort = scalar(sort)
        || matches!(sort,
        Sort::Array(array) if matches!(&array.index_sort,
            Sort::BitVec(width) if width.width == 64) && scalar(&array.element_sort));
    if !admitted_sort {
        return Err(ControlledTermInternError::UnsupportedFragment);
    }
    let live = |id: TermId| store.entry_stamp(id).is_some();
    match term {
        TermData::Const(Constant::Bool(_)) if sort == &Sort::Bool => Ok(()),
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
        | TermData::Const(Constant::BitVec { .. })
        | TermData::Const(Constant::Bool(_)) => Err(ControlledTermInternError::InvalidInput),
        _ => Err(ControlledTermInternError::UnsupportedFragment),
    }
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
        TermData::Var(name, id) if name.len() <= 64 => {
            let mut copied = String::new();
            copied
                .try_reserve_exact(name.len())
                .map_err(|_| ControlledTermInternError::ResourceLimit)?;
            copied.push_str(name);
            Ok(TermData::Var(copied, *id))
        }
        TermData::Const(Constant::Bool(_) | Constant::BitVec { .. })
        | TermData::Not(_)
        | TermData::Ite(_, _, _) => Ok(term.clone()),
        _ => Err(ControlledTermInternError::UnsupportedFragment),
    }
}
