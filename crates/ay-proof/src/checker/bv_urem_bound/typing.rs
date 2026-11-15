// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Iterative whole-DAG typing. Unsupported syntax cannot hide in a dead arm.

use super::*;
use ay_core::kani_compat::DetHashSet;

pub(super) fn validate(
    terms: &TermStore,
    roots: &[TermId],
    meter: &mut Meter<'_>,
) -> Result<(), ProofCheckError> {
    let mut seen = DetHashSet::default();
    let mut pending = Vec::new();
    push(&mut pending, roots, meter)?;
    let result = (|| {
        while let Some(id) = pending.pop() {
            meter.admit(1, 0)?;
            if id.index() >= terms.len() {
                return Err(meter.invalid());
            }
            if seen.contains(&id) {
                continue;
            }
            meter.admit(1, 64)?;
            seen.try_reserve(1).map_err(|_| meter.exhausted())?;
            seen.insert(id);
            if !valid_sort(terms.sort(id)) {
                return Err(meter.invalid());
            }
            let inline;
            let children: &[TermId] = match terms.get(id) {
                TermData::App(_, args) => args,
                TermData::Not(arg) => std::slice::from_ref(arg),
                TermData::Ite(c, a, b) => {
                    inline = [*c, *a, *b];
                    &inline
                }
                TermData::Const(_) | TermData::Var(..) => &[],
                _ => return Err(meter.invalid()),
            };
            meter.admit(children.len(), 0)?;
            // A TermStore application refers only to already-interned nodes.
            // Also reject forged forward edges before reading child sorts.
            if children.iter().any(|child| child.index() >= id.index()) {
                return Err(meter.invalid());
            }
            if !typed_node(terms, id, meter)? {
                return Err(meter.invalid());
            }
            push(&mut pending, children, meter)?;
        }
        Ok(())
    })();
    drop(pending);
    drop(seen);
    result?;
    meter.admit(0, 0)
}

fn push(
    stack: &mut Vec<TermId>,
    ids: &[TermId],
    meter: &mut Meter<'_>,
) -> Result<(), ProofCheckError> {
    let bytes = ids
        .len()
        .checked_mul(size_of::<TermId>())
        .ok_or_else(|| meter.exhausted())?;
    meter.admit(ids.len(), bytes)?;
    stack
        .try_reserve(ids.len())
        .map_err(|_| meter.exhausted())?;
    stack.extend_from_slice(ids);
    Ok(())
}

fn valid_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool)
        || matches!(sort, Sort::BitVec(bits) if (1..=MAX_WIDTH).contains(&bits.width))
}

fn typed_node(
    terms: &TermStore,
    id: TermId,
    meter: &mut Meter<'_>,
) -> Result<bool, ProofCheckError> {
    let sort = terms.sort(id);
    Ok(match terms.get(id) {
        TermData::Var(name, _) => {
            meter.admit(name.len(), 0)?;
            !name.contains('\0')
        }
        TermData::Const(Constant::Bool(_)) => sort == &Sort::Bool,
        TermData::Const(Constant::BitVec { value, width }) => {
            let work = usize::try_from(value.bits() / 8)
                .map_err(|_| meter.exhausted())?
                .saturating_add(1);
            meter.admit(work, 0)?;
            value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(*width)
                && sort == &Sort::bitvec(*width)
        }
        TermData::Not(arg) => sort == &Sort::Bool && terms.sort(*arg) == &Sort::Bool,
        TermData::Ite(c, a, b) => {
            terms.sort(*c) == &Sort::Bool && sort == terms.sort(*a) && sort == terms.sort(*b)
        }
        TermData::App(Symbol::Named(name), args) => {
            let work = name
                .len()
                .checked_add(args.len())
                .ok_or_else(|| meter.exhausted())?;
            meter.admit(work, 0)?;
            !terms.is_declared_function(name) && named(terms, name, args, sort)
        }
        TermData::App(Symbol::Indexed(name, indices), args) => {
            let work = name
                .len()
                .checked_add(indices.len())
                .ok_or_else(|| meter.exhausted())?;
            meter.admit(work, 0)?;
            !terms.is_declared_function(name) && indexed(terms, name, indices, args, sort)
        }
        _ => false,
    })
}

fn named(terms: &TermStore, name: &str, args: &[TermId], sort: &Sort) -> bool {
    let boolean = sort == &Sort::Bool;
    let bool_args = || args.iter().all(|a| terms.sort(*a) == &Sort::Bool);
    match (name, args) {
        ("and" | "or", _) => boolean && bool_args(),
        ("not", [_]) => boolean && bool_args(),
        ("=>" | "xor", [_, _]) => boolean && bool_args(),
        ("=" | "distinct", [a, b]) => boolean && terms.sort(*a) == terms.sort(*b),
        ("ite", [c, a, b]) => {
            terms.sort(*c) == &Sort::Bool && sort == terms.sort(*a) && sort == terms.sort(*b)
        }
        ("bvnot" | "bvneg", [a]) => width(terms.sort(*a)).is_some() && sort == terms.sort(*a),
        ("concat", [a, b]) => width(terms.sort(*a))
            .zip(width(terms.sort(*b)))
            .and_then(|(a, b)| a.checked_add(b))
            .is_some_and(|w| Some(w) == width(sort)),
        (
            "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv" | "bvsrem" | "bvsmod"
            | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor" | "bvxnor" | "bvshl" | "bvlshr"
            | "bvashr",
            [a, b],
        ) => width(sort).is_some() && terms.sort(*a) == sort && terms.sort(*b) == sort,
        (
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            | "bvcomp",
            [a, b],
        ) => {
            width(terms.sort(*a)).is_some()
                && terms.sort(*a) == terms.sort(*b)
                && if name == "bvcomp" {
                    width(sort) == Some(1)
                } else {
                    boolean
                }
        }
        _ => false,
    }
}

fn width(sort: &Sort) -> Option<u32> {
    match sort {
        Sort::BitVec(bits) => Some(bits.width),
        _ => None,
    }
}

fn indexed(terms: &TermStore, name: &str, indices: &[u32], args: &[TermId], sort: &Sort) -> bool {
    let [arg] = args else { return false };
    let Some(bits) = width(terms.sort(*arg)) else {
        return false;
    };
    let output = match (name, indices) {
        ("extract", [high, low]) if high >= low && *high < bits => Some(high - low + 1),
        ("zero_extend" | "sign_extend", [extra]) => bits.checked_add(*extra),
        ("rotate_left" | "rotate_right", [_]) => Some(bits),
        ("repeat", [count]) if *count > 0 => bits.checked_mul(*count),
        _ => None,
    };
    output.is_some() && output == width(sort)
}
