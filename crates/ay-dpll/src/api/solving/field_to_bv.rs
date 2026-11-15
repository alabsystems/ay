// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact residue encoding, as used by Z3's ff2bv tactic (5.3.3,
//! tactic/ff/ff2bv_tactic.cpp). A k-bit representative is below p; products
//! and sums are computed at 2k bits before reduction, never modulo 2^k.
//! This module supplies DATA/model reconstruction, not a proof converter.

use super::tactics::TacticFailure;
use ay_core::term::{
    reserve_counted, CountedBuiltin as Op, CountedTermBuilder, TermConstructionAdmission,
};
use ay_core::{Constant, FiniteFieldSort, Sort, Symbol, TermData, TermId, TermStore};

#[derive(Clone, Copy, Debug)]
pub(super) struct Binding {
    pub source: TermId,
    pub representative: TermId,
    pub field: Option<FiniteFieldSort>,
}

pub(super) struct Encoded {
    pub formulas: Vec<TermId>,
    pub bindings: Vec<Binding>,
}

fn failure(owner: &dyn TermConstructionAdmission) -> TacticFailure {
    let message = "ff2bv requires an admitted quantifier-free Bool/prime-field goal";
    if owner.admit(message.len(), message.len()).is_err() {
        return TacticFailure::new("ff2bv original owner stopped");
    }
    TacticFailure::new(message)
}

pub(super) struct Borrowed<'a>(pub(super) &'a dyn TermConstructionAdmission);
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

fn literal(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    owner: &dyn TermConstructionAdmission,
    value: u32,
    width: u32,
) -> Result<TermId, TacticFailure> {
    owner
        .admit(
            1,
            if value == 0 {
                0
            } else {
                std::mem::size_of::<u64>()
            },
        )
        .map_err(|_| failure(owner))?;
    builder
        .bitvector_unsigned(&value.into(), width)
        .map_err(|_| failure(owner))
}

fn modular(
    builder: &mut CountedTermBuilder<'_, '_, Borrowed<'_>>,
    operation: Op,
    left: TermId,
    right: TermId,
    field: FiniteFieldSort,
    owner: &dyn TermConstructionAdmission,
) -> Result<TermId, TacticFailure> {
    let width = u32::BITS - (field.modulus() - 1).leading_zeros();
    let a = builder
        .apply(Op::BvZeroExtend(width), &[left])
        .map_err(|_| failure(owner))?;
    let b = builder
        .apply(Op::BvZeroExtend(width), &[right])
        .map_err(|_| failure(owner))?;
    let value = builder
        .apply(operation, &[a, b])
        .map_err(|_| failure(owner))?;
    let modulus = literal(builder, owner, field.modulus(), width * 2)?;
    let residue = builder
        .apply(Op::BvURem, &[value, modulus])
        .map_err(|_| failure(owner))?;
    builder
        .apply(Op::BvExtract(width - 1, 0), &[residue])
        .map_err(|_| failure(owner))
}

pub(super) fn reachable_nodes(
    store: &TermStore,
    roots: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<u8>, TacticFailure> {
    let n = store.len();
    let mut reachable = Vec::new();
    reserve_counted(&mut reachable, n, owner).map_err(|_| failure(owner))?;
    reachable.resize(n, 0u8);
    let mut pending = Vec::new();
    reserve_counted(&mut pending, roots.len(), owner).map_err(|_| failure(owner))?;
    pending.extend_from_slice(roots);
    while let Some(id) = pending.pop() {
        owner.admit(1, 0).map_err(|_| failure(owner))?;
        if id.index() >= n {
            return Err(failure(owner));
        }
        if reachable[id.index()] != 0 {
            continue;
        }
        reachable[id.index()] = 1;
        if !matches!(store.sort(id), Sort::Bool | Sort::FiniteField(_)) {
            return Err(failure(owner));
        }
        let children: &[TermId] = match store.get(id) {
            TermData::App(_, args) => args,
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::Ite(_, _, _) => {
                // Handle the fixed-size native representation without an owned
                // traversal copy or recursive stack.
                let TermData::Ite(a, b, c) = store.get(id) else {
                    return Err(failure(owner));
                };
                if a.index() >= id.index()
                    || b.index() >= id.index()
                    || c.index() >= id.index()
                    || store.sort(*a) != &Sort::Bool
                    || store.sort(*b) != store.sort(id)
                    || store.sort(*c) != store.sort(id)
                {
                    return Err(failure(owner));
                }
                reserve_counted(&mut pending, 3, owner).map_err(|_| failure(owner))?;
                for child in [*a, *b, *c] {
                    if child.index() >= id.index() {
                        return Err(failure(owner));
                    }
                    pending.push(child);
                }
                continue;
            }
            TermData::Var(_, _) | TermData::Const(_) => &[],
            _ => return Err(failure(owner)),
        };
        owner.admit(children.len(), 0).map_err(|_| failure(owner))?;
        reserve_counted(&mut pending, children.len(), owner).map_err(|_| failure(owner))?;
        for &child in children {
            if child.index() >= id.index() {
                return Err(failure(owner));
            }
            pending.push(child);
        }
    }
    Ok(reachable)
}

/// The namespace is captured from the original frontend as well as the term
/// store, before construction. Unused declarations count as occupied names.
pub(super) fn fresh_scalar_name<'a>(
    store: &TermStore,
    namespace: impl Iterator<Item = &'a str> + Clone,
    prefix: &str,
    index: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<String, TacticFailure> {
    let mut serial = 0usize;
    loop {
        let candidate = ay_core::render_admission::format(
            Some(owner),
            format_args!("{prefix}.{index}.{serial}"),
        );
        owner.check().map_err(|_| failure(owner))?;
        let mut occupied = false;
        for name in namespace.clone() {
            owner
                .admit(name.len().saturating_add(candidate.len()), 0)
                .map_err(|_| failure(owner))?;
            occupied |= name == candidate;
        }
        for id in store.term_ids() {
            owner.admit(1, 0).map_err(|_| failure(owner))?;
            let name = match store.get(id) {
                TermData::Var(name, _) => Some(name.as_str()),
                TermData::App(Symbol::Named(name), a) if a.is_empty() => Some(name.as_str()),
                _ => None,
            };
            if let Some(name) = name {
                owner
                    .admit(name.len().saturating_add(candidate.len()), 0)
                    .map_err(|_| failure(owner))?;
                occupied |= name == candidate;
            }
        }
        if !occupied {
            return Ok(candidate);
        }
        serial = serial.checked_add(1).ok_or_else(|| failure(owner))?;
    }
}

pub(super) fn encode<'a>(
    store: &mut TermStore,
    roots: &[TermId],
    namespace: impl Iterator<Item = &'a str> + Clone,
    owner: &dyn TermConstructionAdmission,
) -> Result<Encoded, TacticFailure> {
    let n = store.len();
    let reachable = reachable_nodes(store, roots, owner)?;
    let mut mapped = Vec::new();
    reserve_counted(&mut mapped, n, owner).map_err(|_| failure(owner))?;
    mapped.resize(n, None);
    let mut bindings = Vec::new();
    let mut constraints = Vec::new();
    let mut args = Vec::new();
    let borrowed = Borrowed(owner);
    let mut builder =
        CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| failure(owner))?;
    for index in 0..n {
        if reachable[index] == 0 {
            continue;
        }
        owner.admit(1, 0).map_err(|_| failure(owner))?;
        let id = TermId(index as u32);
        let field = match builder.terms().sort(id) {
            Sort::FiniteField(field) => Some(*field),
            Sort::Bool => None,
            _ => return Err(failure(owner)),
        };
        let width = field.map(|f| u32::BITS - (f.modulus() - 1).leading_zeros());
        let leaf = matches!(builder.terms().get(id), TermData::Var(_, _))
            || matches!(builder.terms().get(id), TermData::App(Symbol::Named(_), a) if a.is_empty());
        let value = if leaf {
            if let Some(field) = field {
                let name = fresh_scalar_name(
                    builder.terms(),
                    namespace.clone(),
                    "@ay.ff2bv",
                    index,
                    owner,
                )?;
                let k = width.ok_or_else(|| failure(owner))?;
                let variable = builder
                    .variable(&name, &Sort::bitvec(k))
                    .map_err(|_| failure(owner))?;
                if field.modulus() != 2 {
                    let p = literal(&mut builder, owner, field.modulus(), k)?;
                    let bound = builder
                        .apply(Op::BvULt, &[variable, p])
                        .map_err(|_| failure(owner))?;
                    reserve_counted(&mut constraints, 1, owner).map_err(|_| failure(owner))?;
                    constraints.push(bound);
                }
                reserve_counted(&mut bindings, 1, owner).map_err(|_| failure(owner))?;
                bindings.push(Binding {
                    source: id,
                    representative: variable,
                    field: Some(field),
                });
                variable
            } else {
                reserve_counted(&mut bindings, 1, owner).map_err(|_| failure(owner))?;
                bindings.push(Binding {
                    source: id,
                    representative: id,
                    field: None,
                });
                id
            }
        } else {
            args.clear();
            let operation = match builder.terms().get(id) {
                TermData::Const(Constant::Bool(_)) if field.is_none() => {
                    mapped[index] = Some(id);
                    continue;
                }
                TermData::Const(Constant::FiniteField { value, field: f })
                    if Some(*f) == field && *value < f.modulus() =>
                {
                    let value = *value;
                    let encoded = literal(
                        &mut builder,
                        owner,
                        value,
                        width.ok_or_else(|| failure(owner))?,
                    )?;
                    mapped[index] = Some(encoded);
                    continue;
                }
                TermData::Not(a) if field.is_none() => {
                    reserve_counted(&mut args, 1, owner).map_err(|_| failure(owner))?;
                    args.push(mapped[a.index()].ok_or_else(|| failure(owner))?);
                    "not"
                }
                TermData::Ite(a, b, c) => {
                    reserve_counted(&mut args, 3, owner).map_err(|_| failure(owner))?;
                    for child in [*a, *b, *c] {
                        args.push(mapped[child.index()].ok_or_else(|| failure(owner))?);
                    }
                    "ite"
                }
                TermData::App(Symbol::Named(name), original) => {
                    let operation = match name.as_str() {
                        "ff.add" => "ff.add",
                        "ff.mul" => "ff.mul",
                        "ff.neg" => "ff.neg",
                        "ff.bitsum" => "ff.bitsum",
                        "=" => "=",
                        "distinct" => "distinct",
                        "and" => "and",
                        "or" => "or",
                        "not" => "not",
                        "=>" => "=>",
                        "xor" => "xor",
                        "ite" => "ite",
                        _ => return Err(failure(owner)),
                    };
                    owner.admit(original.len(), 0).map_err(|_| failure(owner))?;
                    match operation {
                        "=" | "distinct" => {
                            let Some(first) = original.first() else {
                                return Err(failure(owner));
                            };
                            if field.is_some()
                                || original.iter().any(|&a| {
                                    builder.terms().sort(a) != builder.terms().sort(*first)
                                })
                            {
                                return Err(failure(owner));
                            }
                        }
                        "ite" => {
                            if original.len() != 3
                                || builder.terms().sort(original[0]) != &Sort::Bool
                                || builder.terms().sort(original[1]) != builder.terms().sort(id)
                                || builder.terms().sort(original[2]) != builder.terms().sort(id)
                            {
                                return Err(failure(owner));
                            }
                        }
                        "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum" if field.is_some() => {}
                        "and" | "or" | "not" | "=>" | "xor"
                            if field.is_none()
                                && original
                                    .iter()
                                    .all(|&a| builder.terms().sort(a) == &Sort::Bool) => {}
                        _ => return Err(failure(owner)),
                    }
                    reserve_counted(&mut args, original.len(), owner)
                        .map_err(|_| failure(owner))?;
                    for &child in original {
                        args.push(mapped[child.index()].ok_or_else(|| failure(owner))?);
                    }
                    operation
                }
                _ => return Err(failure(owner)),
            };
            if let Some(field) = field {
                // Revalidate source sorts before changing their representation.
                let source = builder.terms().get(id);
                if let TermData::App(_, original) = source {
                    if operation != "ite"
                        && original
                            .iter()
                            .any(|&a| builder.terms().sort(a) != &Sort::FiniteField(field))
                    {
                        return Err(failure(owner));
                    }
                }
                match operation {
                    "ff.neg" if args.len() == 1 => {
                        let k = width.ok_or_else(|| failure(owner))?;
                        let p = literal(&mut builder, owner, field.modulus(), k * 2)?;
                        let a = builder
                            .apply(Op::BvZeroExtend(k), &args)
                            .map_err(|_| failure(owner))?;
                        let difference = builder
                            .apply(Op::BvSub, &[p, a])
                            .map_err(|_| failure(owner))?;
                        let residue = builder
                            .apply(Op::BvURem, &[difference, p])
                            .map_err(|_| failure(owner))?;
                        builder
                            .apply(Op::BvExtract(k - 1, 0), &[residue])
                            .map_err(|_| failure(owner))?
                    }
                    "ff.add" | "ff.mul" | "ff.bitsum" if args.len() >= 2 => {
                        let k = width.ok_or_else(|| failure(owner))?;
                        let mut result = if operation == "ff.bitsum" {
                            literal(&mut builder, owner, 0, k)?
                        } else {
                            args[0]
                        };
                        let mut coefficient = 1u32;
                        for (position, &arg) in args.iter().enumerate() {
                            owner.admit(1, 0).map_err(|_| failure(owner))?;
                            if operation == "ff.bitsum" {
                                let weight = literal(&mut builder, owner, coefficient, k)?;
                                let term =
                                    modular(&mut builder, Op::BvMul, arg, weight, field, owner)?;
                                result =
                                    modular(&mut builder, Op::BvAdd, result, term, field, owner)?;
                                coefficient = (u64::from(coefficient) * 2
                                    % u64::from(field.modulus()))
                                    as u32;
                            } else if position != 0 {
                                result = modular(
                                    &mut builder,
                                    if operation == "ff.add" {
                                        Op::BvAdd
                                    } else {
                                        Op::BvMul
                                    },
                                    result,
                                    arg,
                                    field,
                                    owner,
                                )?;
                            }
                        }
                        result
                    }
                    "ite" if args.len() == 3 => {
                        builder.apply(Op::Ite, &args).map_err(|_| failure(owner))?
                    }
                    _ => return Err(failure(owner)),
                }
            } else {
                let op = match operation {
                    "=" => Op::Eq,
                    "distinct" => Op::Distinct,
                    "and" => Op::And,
                    "or" => Op::Or,
                    "not" => Op::Not,
                    "=>" => Op::Implies,
                    "xor" => Op::Xor,
                    "ite" => Op::Ite,
                    _ => return Err(failure(owner)),
                };
                builder.apply(op, &args).map_err(|_| failure(owner))?
            }
        };
        mapped[index] = Some(value);
    }
    reserve_counted(&mut constraints, roots.len(), owner).map_err(|_| failure(owner))?;
    for &root in roots {
        if builder.terms().sort(root) != &Sort::Bool {
            return Err(failure(owner));
        }
        constraints.push(mapped[root.index()].ok_or_else(|| failure(owner))?);
    }
    builder.finish().map_err(|_| failure(owner))?;
    Ok(Encoded {
        formulas: constraints,
        bindings,
    })
}
