// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Three adjacent unsigned intervals cover each in-range constant exactly once.
//! Only the original conjunction's ordered-endpoint guard licenses this rule.

use super::*;

mod shape;

pub(crate) struct PartitionIdentity {
    pub(crate) root: TermId,
    pub(crate) equality: TermId,
    pub(crate) negated_equality: TermId,
    pub(crate) body: TermId,
    pub(crate) width: u32,
    pub(crate) ordered: TermId,
    pub(crate) start: TermId,
    pub(crate) end: TermId,
    pub(crate) leaves: Vec<IntervalLeaf>,
}

pub(crate) struct IntervalLeaf {
    pub(crate) equality: TermId,
    pub(crate) sum: TermId,
    pub(crate) point: TermId,
    pub(crate) upper: TermId,
    pub(crate) upper_value: u128,
}

pub(crate) fn partition_identity(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<PartitionIdentity>, ProofCheckError> {
    let [negative] = clause else { return Ok(None) };
    if terms.entry_stamp(*negative).is_none() || terms.sort(*negative) != &Sort::Bool {
        return Ok(None);
    }
    let TermData::Not(root) = terms.get(*negative) else {
        return Ok(None);
    };
    if !progress(MAX_WORK, MAX_ALLOCATION) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let result = (|| {
        let mut nodes = 0;
        let mut facts = Vec::new();
        shape::flatten(terms, *root, &mut facts, &mut nodes, 0)?;
        let mut selected = None;
        for &fact in &facts {
            let TermData::Not(eq) = terms.get(fact) else {
                continue;
            };
            let Some([yes, body]) = shape::binary(terms, *eq, "=") else {
                continue;
            };
            if !matches!(terms.get(yes), TermData::Const(Constant::Bool(true))) {
                continue;
            }
            if selected.is_some() {
                return None;
            }
            selected = Some((fact, *eq, body));
        }
        let (negated_equality, eq, body) = selected?;
        let mut leaves = Vec::new();
        shape::flatten(terms, body, &mut leaves, &mut nodes, 0)?;
        if leaves.is_empty() || leaves.len() > 32 {
            return None;
        }
        let (_, _, width) = equality(terms, &[*leaves.first()?])?;
        context::validate_source(terms, *root, width)?;
        let mut normalizer = Normalizer {
            terms,
            width,
            mask: u128::MAX >> (128 - width),
            nodes: 0,
            work: 0,
            metadata_work: 0,
            scale_constant_products: false,
            accept_elaborated_shifts: false,
        };
        let mut parsed = Vec::new();
        let mut endpoints = None;
        for leaf in leaves {
            let (entry, start, end) = shape::leaf(&mut normalizer, leaf)?;
            if endpoints.is_some_and(|pair| pair != (start, end)) {
                return None;
            }
            endpoints = Some((start, end));
            parsed.push(entry);
        }
        let (start, end) = endpoints?;
        let ordered = facts.into_iter().find(|&fact| {
            shape::binary(terms, fact, "bvule") == Some([start, end])
                || shape::binary(terms, fact, "bvuge") == Some([end, start])
        })?;
        Some(PartitionIdentity {
            root: *root,
            equality: eq,
            negated_equality,
            body,
            width,
            ordered,
            start,
            end,
            leaves: parsed,
        })
    })();
    Ok(result)
}

#[cfg(test)]
mod tests;
