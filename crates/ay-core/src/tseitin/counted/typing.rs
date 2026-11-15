// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
mod bv;

pub(super) fn classify(terms: &TermStore, id: TermId, owner: &CountedAdmission) -> Result<Kind> {
    let sort = terms.sort(id);
    valid_sort(sort, 0, owner)?;
    let kind = match terms.get(id) {
        TermData::Const(Constant::Bool(value)) if sort == &Sort::Bool => Kind::Constant(*value),
        TermData::Const(Constant::BitVec { value, width }) => {
            owner.admit(
                usize::try_from(value.bits() / 8)
                    .map_err(|_| memory::work(owner))?
                    .checked_add(1)
                    .ok_or_else(|| memory::work(owner))?,
                0,
            )?;
            if *width == 0
                || value.sign() == num_bigint::Sign::Minus
                || value.bits() > u64::from(*width)
                || sort != &Sort::bitvec(*width)
            {
                return Err(Error::Invalid);
            }
            Kind::Value
        }
        TermData::Const(_) => return Err(Error::Unsupported),
        TermData::Var(name, _) => {
            owner.admit(
                name.len()
                    .checked_add(1)
                    .ok_or_else(|| memory::work(owner))?,
                0,
            )?;
            if sort == &Sort::Bool {
                Kind::Variable
            } else {
                Kind::Value
            }
        }
        TermData::Not(arg) => {
            boolean(terms.sort(*arg))?;
            boolean(sort)?;
            Kind::Not
        }
        TermData::Ite(c, t, e) => {
            boolean(terms.sort(*c))?;
            equal(terms.sort(*t), terms.sort(*e), 0, owner)?;
            equal(sort, terms.sort(*t), 0, owner)?;
            if sort == &Sort::Bool {
                Kind::Ite
            } else {
                Kind::Value
            }
        }
        TermData::App(symbol, args) => application(terms, symbol, args, sort, owner)?,
        _ => return Err(Error::Unsupported),
    };
    Ok(kind)
}

fn application(
    terms: &TermStore,
    symbol: &Symbol,
    args: &[TermId],
    sort: &Sort,
    owner: &CountedAdmission,
) -> Result<Kind> {
    owner.admit(
        symbol
            .name()
            .len()
            .checked_add(args.len())
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| memory::work(owner))?,
        0,
    )?;
    let Symbol::Named(name) = symbol else {
        let Symbol::Indexed(_, indices) = symbol else {
            return Err(Error::Unsupported);
        };
        owner.admit(indices.len(), 0)?;
        return bv::indexed(terms, symbol, args, sort);
    };
    let kind = match name.as_ref() {
        "and" | "or" => {
            boolean(sort)?;
            for &arg in args {
                boolean(terms.sort(arg))?;
            }
            if name == "and" {
                Kind::And
            } else {
                Kind::Or
            }
        }
        "=>" | "xor" if args.len() == 2 => {
            boolean(sort)?;
            boolean(terms.sort(args[0]))?;
            boolean(terms.sort(args[1]))?;
            if name == "=>" {
                Kind::Implies
            } else {
                Kind::Xor
            }
        }
        "=" | "distinct" if args.len() == 2 => {
            boolean(sort)?;
            equal(terms.sort(args[0]), terms.sort(args[1]), 0, owner)?;
            if name == "distinct" {
                Kind::Distinct
            } else if terms.sort(args[0]) == &Sort::Bool {
                Kind::Eq
            } else {
                Kind::Atom
            }
        }
        "select" if args.len() == 2 => {
            let Sort::Array(array) = terms.sort(args[0]) else {
                return Err(Error::Invalid);
            };
            equal(&array.index_sort, terms.sort(args[1]), 0, owner)?;
            equal(&array.element_sort, sort, 0, owner)?;
            if sort == &Sort::Bool {
                Kind::Atom
            } else {
                Kind::Value
            }
        }
        "store" if args.len() == 3 => {
            let Sort::Array(array) = terms.sort(args[0]) else {
                return Err(Error::Invalid);
            };
            equal(&array.index_sort, terms.sort(args[1]), 0, owner)?;
            equal(&array.element_sort, terms.sort(args[2]), 0, owner)?;
            equal(terms.sort(args[0]), sort, 0, owner)?;
            Kind::Value
        }
        "const-array" if args.len() == 1 => {
            let Sort::Array(array) = sort else {
                return Err(Error::Invalid);
            };
            equal(&array.element_sort, terms.sort(args[0]), 0, owner)?;
            Kind::Value
        }
        "=>" | "xor" | "=" | "distinct" | "select" | "store" | "const-array" => {
            return Err(Error::Invalid);
        }
        _ => return bv::named(terms, name, args, sort),
    };
    Ok(kind)
}

fn boolean(sort: &Sort) -> Result<()> {
    if sort == &Sort::Bool {
        Ok(())
    } else {
        Err(Error::Invalid)
    }
}

fn valid_sort(sort: &Sort, depth: usize, owner: &CountedAdmission) -> Result<()> {
    owner.admit(1, 0)?;
    if depth > 256 {
        return Err(Error::Unsupported);
    }
    match sort {
        Sort::Bool => Ok(()),
        Sort::BitVec(bits) if bits.width > 0 => Ok(()),
        Sort::BitVec(_) => Err(Error::Invalid),
        Sort::Array(array) => {
            valid_sort(&array.index_sort, depth + 1, owner)?;
            valid_sort(&array.element_sort, depth + 1, owner)
        }
        _ => Err(Error::Unsupported),
    }
}

fn equal(a: &Sort, b: &Sort, depth: usize, owner: &CountedAdmission) -> Result<()> {
    owner.admit(1, 0)?;
    if depth > 256 {
        return Err(Error::Unsupported);
    }
    match (a, b) {
        (Sort::Bool, Sort::Bool) => Ok(()),
        (Sort::BitVec(a), Sort::BitVec(b)) if a.width == b.width => Ok(()),
        (Sort::Array(a), Sort::Array(b)) => {
            equal(&a.index_sort, &b.index_sort, depth + 1, owner)?;
            equal(&a.element_sort, &b.element_sort, depth + 1, owner)
        }
        _ => Err(Error::Invalid),
    }
}
