// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact (quoted name, comma-sort string, original ID) predicate ranking.

use super::super::{
    bytes::{self, Bytes},
    expression, order, spelling, Control, QueryError,
};
use crate::{ChcProblem, PredicateId};
use std::cmp::Ordering;

struct Signature {
    name: Bytes,
    sorts: Bytes,
    id: usize,
}
pub(in crate::proof_metadata::normalization::prepared) struct Labels(Vec<(usize, usize)>);

impl Labels {
    pub(in crate::proof_metadata::normalization::prepared) fn empty() -> Self {
        Self(Vec::new())
    }

    pub(in crate::proof_metadata::normalization::prepared) fn write<C: Control>(
        &self,
        out: &mut Bytes,
        pred: PredicateId,
        control: &mut C,
    ) -> Result<(), QueryError> {
        control.offer(2, 0)?;
        // Last canonical-rank insertion wins, exactly like the old BTreeMap.
        // Fixed-size linear reads are explicitly paid; no hash/tree probes hide.
        for index in (0..self.0.len()).rev() {
            control.offer(2 * std::mem::size_of::<usize>() + 1, 0)?;
            let (original, rank) = self.0[index];
            if original == pred.index() {
                out.text("p", control)?;
                return spelling::unsigned(out, rank as u128, control);
            }
        }
        out.text("p?", control)?;
        spelling::unsigned(out, pred.index() as u128, control)
    }
}

pub(super) fn build<C: Control>(
    problem: &ChcProblem,
    control: &mut C,
) -> Result<Labels, QueryError> {
    control.offer(2 * std::mem::size_of::<Vec<Signature>>(), 0)?;
    let mut signatures = Vec::new();
    for index in 0..problem.predicates().len() {
        control.offer(3, 0)?;
        let predicate = &problem.predicates()[index];
        let mut name = Bytes::new(control)?;
        spelling::quoted(&mut name, &predicate.name, control)?;
        let mut sorts = Bytes::new(control)?;
        for argument in 0..predicate.arg_sorts.len() {
            control.offer(2, 0)?;
            if argument != 0 {
                sorts.text(",", control)?;
            }
            let sort = expression::sort(&predicate.arg_sorts[argument], control)?;
            sorts.append(&sort.0, control)?;
        }
        bytes::push(&mut signatures, control, || Signature {
            name,
            sorts,
            id: predicate.id.index(),
        })?;
    }
    let indices = order::indices(signatures.len(), control, |a, b, control| {
        let names = order::compare(&signatures[a].name.0, &signatures[b].name.0, control)?;
        if names != Ordering::Equal {
            return Ok(names);
        }
        let sorts = order::compare(&signatures[a].sorts.0, &signatures[b].sorts.0, control)?;
        if sorts != Ordering::Equal {
            return Ok(sorts);
        }
        control.offer(3, 0)?;
        Ok(signatures[a].id.cmp(&signatures[b].id))
    })?;
    control.offer(2 * std::mem::size_of::<Vec<(usize, usize)>>(), 0)?;
    let mut labels = Vec::new();
    for (rank, index) in indices.into_iter().enumerate() {
        control.offer(2, 0)?;
        bytes::push(&mut labels, control, || (signatures[index].id, rank))?;
    }
    Ok(Labels(labels))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn duplicate_original_label_ids_retain_the_last_canonical_rank() {
        let labels = Labels(vec![(7, 0), (9, 1), (7, 2)]);
        let mut control = super::super::super::Legacy;
        let mut out = Bytes::new(&mut control).unwrap();
        labels
            .write(&mut out, PredicateId::new(7), &mut control)
            .unwrap();
        assert_eq!(out.finish(&mut control), Ok("p2".to_string()));
    }
}
