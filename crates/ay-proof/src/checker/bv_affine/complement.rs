// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A bounded affine consequence of one exact bitwise-complement identity.

use super::*;

pub(crate) struct ComplementRelation {
    pub(crate) left: TermId,
    pub(crate) right: TermId,
    pub(crate) operand: TermId,
    pub(crate) constant: TermId,
    pub(crate) constant_first: bool,
    pub(crate) width: u32,
    pub(crate) coefficient: u128,
}

/// Return a witness only when the goal difference equals plus or minus
/// `operand + (operand xor all_ones) + 1` modulo its exact width. Both complete
/// source trees are validated before any term is treated as an affine atom.
pub(crate) fn complement_relation(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<ComplementRelation>, ProofCheckError> {
    let Some((left, right, width)) = equality(terms, clause) else {
        return Ok(None);
    };
    if !progress(MAX_WORK, MAX_ALLOCATION) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let mask = u128::MAX >> (128 - width);
    let mut normalizer = Normalizer {
        terms,
        width,
        mask,
        nodes: 0,
        work: 0,
        metadata_work: 0,
        scale_constant_products: false,
        accept_elaborated_shifts: false,
    };
    let result = (|| {
        normalizer.validate(left, 0)?;
        normalizer.validate(right, 0)?;
        let mut difference = normalizer.normalize(left, 0)?;
        let rhs = normalizer.normalize(right, 0)?;
        combine(&mut normalizer, &mut difference, rhs, mask)?;
        for (&atom, &coefficient) in difference.iter().take(16) {
            if coefficient != 1 && coefficient != mask {
                continue;
            }
            let Some(atom) = atom else { continue };
            let TermData::App(Symbol::Named(op), args) = terms.get(atom) else {
                continue;
            };
            if op != "bvxor" || terms.is_declared_function(op) {
                continue;
            }
            let [a, b] = args.as_slice() else { return None };
            let all_ones = |id| matches!(terms.get(id), TermData::Const(Constant::BitVec { value, .. }) if value.to_u128() == Some(mask));
            let (operand, constant, constant_first) = if all_ones(*a) {
                (*b, *a, true)
            } else if all_ones(*b) {
                (*a, *b, false)
            } else {
                continue;
            };
            let mut expected = normalizer.normalize(operand, 0)?;
            combine(
                &mut normalizer,
                &mut expected,
                BTreeMap::from([(Some(atom), 1), (None, 1)]),
                1,
            )?;
            for value in expected.values_mut() {
                *value = value.wrapping_mul(coefficient) & mask;
            }
            if difference == expected {
                return Some(ComplementRelation {
                    left,
                    right,
                    operand,
                    constant,
                    constant_first,
                    width,
                    coefficient,
                });
            }
        }
        None
    })();
    Ok(result)
}

fn combine(
    normalizer: &mut Normalizer<'_>,
    result: &mut Affine,
    other: Affine,
    factor: u128,
) -> Option<()> {
    for (atom, coefficient) in other {
        normalizer.work = normalizer.work.checked_add(1)?;
        if normalizer.work > MAX_MERGES {
            return None;
        }
        let next = result
            .get(&atom)
            .copied()
            .unwrap_or(0)
            .wrapping_add(coefficient.wrapping_mul(factor))
            & normalizer.mask;
        if next == 0 {
            result.remove(&atom);
        } else {
            result.insert(atom, next);
        }
    }
    Some(())
}
