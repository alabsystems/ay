// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Select congruence for synthesized carrier classes (#carrier-select-congruence).
//!
//! Phase 3 of model completion (`complete_uninterpreted_sort_model`) mints one
//! abstract element per equality class of opaque carrier terms, merging two
//! terms only on an equality atom the model commits to. Two reads of ONE array
//! at model-equal indices, `(select A i)` and `(select A j)` under `i = j`, are
//! linked by no such atom. In
//! `dt_array_field_model_witness::datatype_array_field_select_congruence_certifies`
//! variable substitution eliminates `j := i` (from `i = j + 0`), so the solve
//! never sees `(select A j)`; phase 3 runs over the restored original
//! assertions, where it is a distinct term. Without a substitution the eager
//! BV/AUFBV lane still never bit-blasts a datatype- or uninterpreted-sorted
//! element, so no atom commits the equality either.
//!
//! The two reads received two different elements (`@Slice!0`, `@Slice!1`) for
//! the single cell `A[#x00]`. Total datatype construction (W6) then built one
//! value per carrier, each from its own field reads, and filled the other
//! class's unobserved field cells with the canonical default:
//! `(mk #xff #xff (store (store c #x00 #x11) #x05 #x22))` for one read and
//! `(mk #xff #xff (store c #x05 #x22))` for the other. Array completion wrote
//! both to key `#x00`, the later one won, and the independent gate refuted
//! `(= (select (dat (select A i)) #x00) #x11)` against the committed `A`, so
//! the test answered `unknown` although the census had already certified the
//! model.
//!
//! Functional consistency of `select` makes such reads ONE element in every
//! model, so their classes are merged before any element is minted. The merge
//! key is a conservative subset of the census's select-congruence groups: the
//! same array TERM (not its model identity class) and an exactly evaluated
//! scalar index. An index the model does not determine merges nothing (the
//! pre-existing behavior). This is not SAT authority: a merge only removes a
//! split the model could never realize, and the strict and independent gates
//! still re-check every assertion. Two reads that already carry different
//! elements put their class in the existing `blocked_class` path, so a
//! candidate that splits one cell fails closed rather than minting a value for
//! either side.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, TermId};

use super::{EvalValue, Model};
use crate::executor::Executor;

#[cfg(test)]
mod tests;

impl Executor {
    /// Positions in `carrier_terms` of reads that must share one class: each
    /// pair names a read and the first earlier read of the same array at the
    /// same exactly evaluated index. Sequence carriers keep their own
    /// completion (#seq-exact-equality-carrier) and are skipped.
    pub(super) fn select_congruent_carrier_pairs(
        &self,
        model: &Model,
        carrier_terms: &[TermId],
    ) -> Vec<(usize, usize)> {
        let mut first_read: HashMap<(TermId, String), usize> = HashMap::default();
        let mut pairs = Vec::new();
        for (position, &term) in carrier_terms.iter().enumerate() {
            if matches!(self.ctx.terms.sort(term), Sort::Seq(_)) {
                continue;
            }
            let Some((array, index)) = self.exact_cegar_select_parts(term) else {
                continue;
            };
            let Some(key) = exact_index_key(&self.evaluate_term(model, index)) else {
                continue;
            };
            match first_read.get(&(array, key.clone())) {
                Some(&first) => pairs.push((first, position)),
                None => {
                    first_read.insert((array, key), position);
                }
            }
        }
        pairs
    }
}

/// An injective spelling of a scalar model value whose equality is exact.
/// Anything else (unknown, algebraic, floating point, sequence) yields `None`:
/// such an index proves no congruence, so it merges nothing.
fn exact_index_key(value: &EvalValue) -> Option<String> {
    match value {
        EvalValue::Bool(value) => Some(format!("bool:{value}")),
        EvalValue::BitVec { value, width } => Some(format!("bv{width}:{value}")),
        EvalValue::Rational(value) => Some(format!("rational:{value}")),
        EvalValue::String(value) => Some(format!("string:{value:?}")),
        EvalValue::Element(value) => Some(format!("element:{value}")),
        _ => None,
    }
}
