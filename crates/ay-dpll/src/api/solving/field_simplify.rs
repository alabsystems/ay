// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Model-preserving prime-field constant propagation and ring reductions.
//!
//! The standard ring identities are the same preprocessing building blocks as
//! Z3 5.3.3 ast/simplifiers/ff_simplify.cpp. Defining equalities are retained:
//! unlike wire elimination, this needs no assignment reconstruction converter.
//! No decision, fresh variable, division, or polynomial enumeration is used.

use ay_core::term::{
    reserve_counted, Constant, CountedBuiltin, CountedFieldBuiltin, CountedTermBuilder, Symbol,
    TermConstructionAdmission, TermData,
};
use ay_core::{FiniteFieldSort, Sort, TermId, TermStore};

use super::tactics::TacticFailure;

fn fail() -> TacticFailure {
    TacticFailure::new("ff-simplify original construction admission refused")
}

fn pay(
    owner: &dyn TermConstructionAdmission,
    work: usize,
    bytes: usize,
) -> Result<(), TacticFailure> {
    owner.admit(work, bytes).map_err(|_| fail())
}

struct Borrowed<'a>(&'a dyn TermConstructionAdmission);
impl TermConstructionAdmission for Borrowed<'_> {
    fn admit(
        &self,
        work: usize,
        bytes: usize,
    ) -> Result<(), ay_core::original_query::CountedAdmissionError> {
        self.0.admit(work, bytes)
    }
    fn refuse(
        &self,
        error: ay_core::original_query::CountedAdmissionError,
    ) -> ay_core::original_query::CountedAdmissionError {
        self.0.refuse(error)
    }
}

fn residue(store: &TermStore, id: TermId, field: FiniteFieldSort) -> Option<u32> {
    match store.get(id) {
        TermData::Const(Constant::FiniteField {
            value,
            field: actual,
        }) if *actual == field && *value < field.modulus() => Some(*value),
        _ => None,
    }
}

fn field(store: &TermStore, id: TermId) -> Option<FiniteFieldSort> {
    match store.sort(id) {
        Sort::FiniteField(f) => Some(*f),
        _ => None,
    }
}

/// The immutable source prefix determines the walk; appended output cannot
/// replenish traversal or original work/storage. Every owned buffer and native
/// intern is prepaid. Unknown syntax is retained, never interpreted as algebra.
pub(super) fn apply(
    store: &mut TermStore,
    roots: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    let n = store.len();
    pay(owner, n, 0)?;
    let mut flat = Vec::new();
    let mut seen = Vec::new();
    reserve_counted(&mut flat, n, owner).map_err(|_| fail())?;
    reserve_counted(&mut seen, n, owner).map_err(|_| fail())?;
    seen.resize(n, 0u8);
    let mut pending = Vec::new();
    reserve_counted(&mut pending, roots.len(), owner).map_err(|_| fail())?;
    pending.extend(roots.iter().rev().copied());
    while let Some(id) = pending.pop() {
        pay(owner, 1, 0)?;
        if id.index() >= n || store.sort(id) != &Sort::Bool {
            return Err(fail());
        }
        if seen[id.index()] != 0 {
            continue;
        }
        seen[id.index()] = 1;
        if let TermData::App(Symbol::Named(name), args) = store.get(id) {
            pay(owner, name.len(), 0)?;
            if name == "and" && !store.is_declared_function(name) {
                pay(owner, args.len(), 0)?;
                reserve_counted(&mut pending, args.len(), owner).map_err(|_| fail())?;
                pending.extend(args.iter().rev().copied());
                continue;
            }
        }
        flat.push(id);
    }
    // Conjunction is idempotent. Visiting each AND once avoids exponential
    // expansion of a shared Boolean DAG while exposing authored definitions.
    let roots = flat.as_slice();
    let mut values = Vec::new();
    let mut definitions = Vec::new();
    let mut reachable = Vec::new();
    reserve_counted(&mut values, n, owner).map_err(|_| fail())?;
    reserve_counted(&mut definitions, n, owner).map_err(|_| fail())?;
    reserve_counted(&mut reachable, n, owner).map_err(|_| fail())?;
    values.resize(n, None);
    definitions.resize(n, None);
    reachable.resize(n, 0u8);
    let mut todo = Vec::new();
    reserve_counted(&mut todo, roots.len(), owner).map_err(|_| fail())?;
    todo.extend_from_slice(roots);
    // Only authored top-level equalities supply substitutions. Keeping each
    // original equality also preserves contradictory definitions and all free
    // variables in models of the transformed goal.
    for &root in roots {
        pay(owner, 1, 0)?;
        if root.index() >= n || store.sort(root) != &Sort::Bool {
            return Err(fail());
        }
        if let TermData::App(sym, args) = store.get(root) {
            pay(owner, sym.name().len(), 0)?;
            if matches!(sym, Symbol::Named(name) if name == "=" && !store.is_declared_function(name))
                && args.len() == 2
            {
                if args.iter().any(|id| id.index() >= n) {
                    return Err(fail());
                }
                for (variable, value) in [(args[0], args[1]), (args[1], args[0])] {
                    if let Some(f) = field(store, variable) {
                        if matches!(store.get(variable), TermData::Var(_, _))
                            && residue(store, value, f).is_some()
                        {
                            definitions[variable.index()].get_or_insert(value);
                        }
                    }
                }
            }
        }
    }
    while let Some(id) = todo.pop() {
        pay(owner, 1, 0)?;
        if id.index() >= n {
            return Err(fail());
        }
        if reachable[id.index()] != 0 {
            continue;
        }
        reachable[id.index()] = 1;
        if let TermData::App(_, args) = store.get(id) {
            pay(owner, args.len(), 0)?;
            reserve_counted(&mut todo, args.len(), owner).map_err(|_| fail())?;
            for &child in args {
                // Native constructors only refer to already-interned children.
                // Refuse a malformed forward edge rather than rely on ordering.
                if child.index() >= id.index() {
                    return Err(fail());
                }
                todo.push(child);
            }
        }
    }
    let borrowed = Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| fail())?;
    for index in 0..n {
        if reachable[index] == 0 {
            continue;
        }
        pay(owner, 1, 0)?;
        let id = TermId(index as u32);
        if let Some(value) = definitions[index] {
            values[index] = Some(value);
            continue;
        }
        let TermData::App(symbol, original) = builder.terms().get(id) else {
            values[index] = Some(id);
            continue;
        };
        // Only scalar field arithmetic and its typed Boolean consumers are
        // rebuilt. Other theories/binders stay opaque (and keep their inputs).
        let Symbol::Named(name) = symbol else {
            values[index] = Some(id);
            continue;
        };
        let name = name.as_str();
        pay(owner, name.len(), 0)?;
        if builder.terms().is_declared_function(name) {
            values[index] = Some(id);
            continue;
        }
        if matches!(name, "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum")
            && field(builder.terms(), id).is_none()
        {
            return Err(fail());
        }
        let supported = matches!(
            name,
            "ff.add"
                | "ff.mul"
                | "ff.neg"
                | "ff.bitsum"
                | "="
                | "distinct"
                | "and"
                | "or"
                | "not"
                | "=>"
                | "xor"
                | "ite"
        );
        if !supported {
            values[index] = Some(id);
            continue;
        }
        let scalar_sort = match builder.terms().sort(id) {
            Sort::Bool => Sort::Bool,
            Sort::FiniteField(f) => Sort::FiniteField(*f),
            _ => {
                values[index] = Some(id);
                continue;
            }
        };
        pay(owner, original.len(), name.len())?;
        let mut args = Vec::new();
        reserve_counted(&mut args, original.len(), owner).map_err(|_| fail())?;
        args.extend(original.iter().map(|a| values[a.index()].unwrap_or(*a)));
        let name = name.to_owned();
        let result = reduce(&mut builder, &name, &args, &scalar_sort, owner)?;
        values[index] = Some(match result {
            Some(id) => id,
            None => {
                if let Some(op) = field_op(&name) {
                    builder.field_apply(op, &args).map_err(|_| fail())?
                } else if let Some(op) = bool_op(&name, args.len()) {
                    builder.apply(op, &args).map_err(|_| fail())?
                } else {
                    id
                }
            }
        });
    }
    pay(owner, roots.len(), 0)?;
    let mut result = Vec::new();
    reserve_counted(&mut result, roots.len(), owner).map_err(|_| fail())?;
    for &root in roots {
        // Original defining equations are retained, not rewritten to true.
        let is_definition = match builder.terms().get(root) {
            TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
                args.iter().any(|a| definitions[a.index()].is_some())
            }
            _ => false,
        };
        result.push(if is_definition {
            root
        } else {
            values[root.index()].unwrap_or(root)
        });
    }
    builder.finish().map_err(|_| fail())?;
    pay(owner, 0, 0)?;
    Ok(result)
}

fn field_op(name: &str) -> Option<CountedFieldBuiltin> {
    Some(match name {
        "ff.add" => CountedFieldBuiltin::Add,
        "ff.mul" => CountedFieldBuiltin::Mul,
        "ff.neg" => CountedFieldBuiltin::Neg,
        "ff.bitsum" => CountedFieldBuiltin::BitSum,
        _ => return None,
    })
}

fn bool_op(name: &str, arity: usize) -> Option<CountedBuiltin> {
    Some(match (name, arity) {
        ("=", 2) => CountedBuiltin::Eq,
        ("distinct", 2) => CountedBuiltin::Distinct,
        ("not", 1) => CountedBuiltin::Not,
        ("=>", 2) => CountedBuiltin::Implies,
        ("xor", 2) => CountedBuiltin::Xor,
        ("ite", 3) => CountedBuiltin::Ite,
        ("and", n) if n >= 2 => CountedBuiltin::And,
        ("or", n) if n >= 2 => CountedBuiltin::Or,
        _ => return None,
    })
}

fn reduce<O: TermConstructionAdmission>(
    builder: &mut CountedTermBuilder<'_, '_, O>,
    name: &str,
    args: &[TermId],
    sort: &Sort,
    owner: &dyn TermConstructionAdmission,
) -> Result<Option<TermId>, TacticFailure> {
    if let Sort::FiniteField(f) = sort {
        let arity = match name {
            "ff.neg" => args.len() == 1,
            "ff.add" | "ff.mul" | "ff.bitsum" => args.len() >= 2,
            "ite" => args.len() == 3,
            _ => false,
        };
        if !arity {
            return Err(fail());
        }
        if name == "ite" {
            if builder.terms().sort(args[0]) != &Sort::Bool
                || args[1..].iter().any(|a| builder.terms().sort(*a) != sort)
            {
                return Err(fail());
            }
        } else if args.iter().any(|a| builder.terms().sort(*a) != sort) {
            return Err(fail());
        }
        let p = u64::from(f.modulus());
        if name == "ff.neg" {
            return residue(builder.terms(), args[0], *f)
                .map(|v| {
                    builder
                        .finite_field(if v == 0 { 0 } else { f.modulus() - v }, *f)
                        .map_err(|_| fail())
                })
                .transpose();
        }
        if name == "ff.add" || name == "ff.mul" {
            let mut constant = u64::from(name == "ff.mul");
            let mut other = Vec::new();
            reserve_counted(&mut other, args.len(), owner).map_err(|_| fail())?;
            for &arg in args {
                if let Some(v) = residue(builder.terms(), arg, *f) {
                    constant = if name == "ff.add" {
                        (constant + u64::from(v)) % p
                    } else {
                        constant * u64::from(v) % p
                    };
                } else {
                    other.push(arg);
                }
            }
            if name == "ff.mul" && constant == 0 {
                return builder.finite_field(0, *f).map(Some).map_err(|_| fail());
            }
            let neutral = u64::from(name == "ff.mul");
            if constant != neutral || other.is_empty() {
                other.push(
                    builder
                        .finite_field(constant as u32, *f)
                        .map_err(|_| fail())?,
                );
            }
            return Ok(Some(if other.len() == 1 {
                other[0]
            } else {
                builder
                    .field_apply(field_op(name).ok_or_else(fail)?, &other)
                    .map_err(|_| fail())?
            }));
        }
        if name == "ff.bitsum"
            && args
                .iter()
                .all(|a| residue(builder.terms(), *a, *f).is_some())
        {
            let mut sum = 0u64;
            for &arg in args.iter().rev() {
                sum =
                    (sum * 2 + u64::from(residue(builder.terms(), arg, *f).ok_or_else(fail)?)) % p;
            }
            return builder
                .finite_field(sum as u32, *f)
                .map(Some)
                .map_err(|_| fail());
        }
    }
    if name == "="
        && args.len() == 2
        && builder.terms().sort(args[0]) == builder.terms().sort(args[1])
    {
        if args[0] == args[1] {
            return builder.boolean(true).map(Some).map_err(|_| fail());
        }
        if let Some(f) = field(builder.terms(), args[0]) {
            if let (Some(a), Some(b)) = (
                residue(builder.terms(), args[0], f),
                residue(builder.terms(), args[1], f),
            ) {
                return builder.boolean(a == b).map(Some).map_err(|_| fail());
            }
        }
    }
    if name == "ite" && args.len() == 3 {
        if let TermData::Const(Constant::Bool(c)) = builder.terms().get(args[0]) {
            return Ok(Some(args[if *c { 1 } else { 2 }]));
        }
        if args[1] == args[2] {
            return Ok(Some(args[1]));
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::Arc;

    fn owner(work: u64, bytes: usize) -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(work, bytes),
            None,
            Arc::new(|| false),
        )
        .unwrap()
    }

    #[test]
    fn field_simplify_modular_propagation_retains_the_model_definition() {
        let mut store = TermStore::new();
        let f = FiniteFieldSort::new(7).unwrap();
        let x = store.mk_var("x", Sort::FiniteField(f));
        let three = store.mk_finite_field(3, f);
        let six = store.mk_finite_field(6, f);
        let def = store.mk_eq(x, three);
        let twice = store.mk_ff_app("ff.add", &[x, x]).unwrap();
        let equation = store.mk_eq(twice, six);
        let result = apply(&mut store, &[def, equation], &owner(1_000_000, 1 << 20)).unwrap();
        assert_eq!(result[0], def);
        assert_eq!(store.get(result[1]), &TermData::Const(Constant::Bool(true)));
        // Inconsistent authored definitions must survive even after choosing
        // one propagation value; replacing both by true would be unsound.
        let wrong = store.mk_eq(x, six);
        let conflict = apply(&mut store, &[def, wrong], &owner(1_000_000, 1 << 20)).unwrap();
        assert_eq!(conflict, [def, wrong]);
    }

    #[test]
    fn field_simplify_preserves_registered_function_identities_with_builtin_spellings() {
        for spelling in ["and", "=", "ff.mul"] {
            let mut store = TermStore::new();
            let f = FiniteFieldSort::new(7).unwrap();
            store.register_declared_function(spelling);
            let zero = store.mk_finite_field(0, f);
            let one = store.mk_finite_field(1, f);
            let x = store.mk_var("x", Sort::FiniteField(f));
            let root = match spelling {
                "and" => {
                    let p = store.mk_var("p", Sort::Bool);
                    let no = store.mk_bool(false);
                    store.mk_app_structural(Symbol::named(spelling), [p, no], Sort::Bool)
                }
                "=" => store.mk_app_structural(Symbol::named(spelling), [x, one], Sort::Bool),
                _ => {
                    let product = store.mk_app_structural(
                        Symbol::named(spelling),
                        [zero, zero],
                        Sort::FiniteField(f),
                    );
                    store.mk_eq(product, one)
                }
            };
            let result = apply(&mut store, &[root], &owner(1_000_000, 1 << 20)).unwrap();
            assert_eq!(result, [root], "registered {spelling} is uninterpreted");
        }
    }

    #[test]
    fn field_simplify_bitsum_keeps_positions_and_uses_full_u32_products() {
        for prime in [7, 4294967291] {
            let mut store = TermStore::new();
            let f = FiniteFieldSort::new(prime).unwrap();
            let a = store.mk_finite_field(prime - 1, f);
            let product = store.mk_ff_app("ff.mul", &[a, a]).unwrap();
            let one = store.mk_finite_field(1, f);
            let p = store.mk_eq(product, one);
            let two = store.mk_finite_field(2, f);
            let three = store.mk_finite_field(3, f);
            let bits = store.mk_ff_app("ff.bitsum", &[one, two, three]).unwrap();
            let expected = store.mk_finite_field(17 % prime, f);
            let b = store.mk_eq(bits, expected);
            let result = apply(&mut store, &[p, b], &owner(1_000_000, 1 << 20)).unwrap();
            assert!(result
                .iter()
                .all(|id| store.get(*id) == &TermData::Const(Constant::Bool(true))));
        }
    }

    #[test]
    fn field_simplify_refuses_before_scratch_and_cannot_renew_a_stopped_owner() {
        let mut store = TermStore::new();
        let before = store.snapshot_stamp();
        let stopped = owner(0, 0);
        assert!(apply(&mut store, &[], &stopped).is_err());
        assert_eq!(store.snapshot_stamp(), before);
        assert!(apply(&mut store, &[], &stopped).is_err());
        let tiny = owner(1_000_000, 1);
        assert!(apply(&mut store, &[], &tiny).is_err());
        assert_eq!(store.snapshot_stamp(), before);
    }

    #[test]
    fn field_simplify_does_not_reinterpret_indexed_or_ill_typed_symbols() {
        let mut store = TermStore::new();
        let f = FiniteFieldSort::new(7).unwrap();
        let g = FiniteFieldSort::new(5).unwrap();
        let a = store.mk_finite_field(1, f);
        let b = store.mk_finite_field(2, f);
        let opaque = store.mk_app_structural(
            Symbol::Indexed("ff.add".into(), vec![9]),
            [a, b],
            Sort::FiniteField(f),
        );
        let c = store.mk_finite_field(3, f);
        let equation = store.mk_eq(opaque, c);
        assert_eq!(
            apply(&mut store, &[equation], &owner(1_000_000, 1 << 20)).unwrap(),
            [equation]
        );
        let foreign = store.mk_finite_field(2, g);
        let bad =
            store.mk_app_structural(Symbol::named("ff.mul"), [a, foreign], Sort::FiniteField(f));
        let root = store.mk_eq(bad, c);
        assert!(apply(&mut store, &[root], &owner(1_000_000, 1 << 20)).is_err());
    }

    #[test]
    fn field_simplify_shared_conjunction_does_not_expand_exponentially() {
        let mut store = TermStore::new();
        let q = store.mk_var("q", Sort::Bool);
        let mut shared = q;
        for _ in 0..512 {
            shared = store.mk_app_structural(Symbol::named("and"), [shared, shared], Sort::Bool);
        }
        // This represents 2^512 occurrences of q, but conjunction is
        // idempotent. Real bounded construction must not enumerate that tree.
        assert_eq!(
            apply(&mut store, &[shared], &owner(1_000_000, 1 << 20)).unwrap(),
            [q]
        );
    }
}
