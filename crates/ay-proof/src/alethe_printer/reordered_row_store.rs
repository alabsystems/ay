// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A ROW lemma whose printed store chain is the certified chain in the
//! problem's write order.
//!
//! `TermStore::mk_store` commutes adjacent stores at distinct constant indices
//! into ascending order (`store_index_rewrite`, `SwapDistinct`), so the
//! authored `(store (store F 7 true) 5 true)` is interned as
//! `store(store(F, 5, true), 7, true)`, and the authored-surface channel
//! prints the problem's order back. A ROW1/ROW2 lemma certified over the
//! interned chain then prints a store whose OUTER write is not the certified
//! one. `arrays_idx` and `arrays_row` read the store positionally and the
//! pinned checker has no rule that reorders stores, so no lowering of the
//! certified step checks over that text.
//!
//! The printed clause is still the certified clause:
//! [`reorders_certified_store`] establishes on the printed text that both
//! chains write the same values at the same pairwise-distinct constant indices
//! over one root, so they denote one array. The ROW printer then refuses with
//! [`reordered_store_refusal`], an `InvalidSurfaceStep`. Inside
//! `with_refused_surface_steps_declined_to_hole` (the explicit `--proof FILE`
//! export) that step prints as the honest `hole` over its own valid clause.
//! Every other caller still sees a refusal. Every other mismatch (a different
//! value, index or base, a symbolic index, a chain this reader cannot decode)
//! keeps the `InvalidArrayStep` refusal.
//!
//! MEASURED 2026-10-31: with `c = (store (store ((as const (Array Int Bool))
//! false) 7 true) 5 true)`, `x != 5`, `x != 7` and `(select c x)`, an explicit
//! `--proof FILE` exited 1 with no verdict on `ROW2 select surface override
//! changes the certified array or indices` (#8821) once the folded Bool read
//! lemma beside it certified. The symbolic-base twin (`(store (store d 7 true)
//! 5 true)`) already did so on main.

use super::*;

/// The deepest store chain the reader decodes; a longer one keeps the refusal.
const MAX_REORDERED_WRITES: usize = 64;

/// A write index the printed text spells as a constant, by value.
#[derive(PartialEq, Eq)]
enum ConstantIndex {
    Numeral(num_rational::BigRational),
    BitVec(num_bigint::BigUint, u32),
}

impl ConstantIndex {
    /// A bit-vector literal (value and width), or an arithmetic numeral or
    /// decimal, optionally under one unary minus. Any other text is not a
    /// constant to this reader.
    fn read(printed: &str) -> Option<Self> {
        if let Some((value, width)) = parse_printed_bitvec_literal(printed) {
            return Some(Self::BitVec(value, width));
        }
        let printed = printed.trim();
        let (negative, body) = match printed
            .strip_prefix("(-")
            .and_then(|rest| rest.strip_suffix(')'))
        {
            Some(body) => (true, body.trim()),
            None => (false, printed),
        };
        if body.is_empty()
            || !body
                .bytes()
                .all(|byte| byte.is_ascii_digit() || byte == b'.')
        {
            return None;
        }
        let value = crate::la_generic_signs::parse_numeric_constant(body)?;
        Some(Self::Numeral(if negative { -value } else { value }))
    }
}

type ConstantWrite = (ConstantIndex, String);

/// The root and the writes of a printed store chain, outermost first, when
/// every write index is a constant; `None` otherwise.
fn constant_writes(chain: &str) -> Option<(String, Vec<ConstantWrite>)> {
    let mut writes = Vec::new();
    let mut current = chain.to_string();
    while let Some(arguments) = split_application(&current, "store") {
        let [array, index, value] = <[String; 3]>::try_from(arguments).ok()?;
        if writes.len() == MAX_REORDERED_WRITES {
            return None;
        }
        writes.push((ConstantIndex::read(&index)?, value));
        current = array;
    }
    Some((current, writes))
}

fn pairwise_distinct(writes: &[ConstantWrite]) -> bool {
    writes.iter().enumerate().all(|(position, (index, _))| {
        writes[..position]
            .iter()
            .all(|(earlier, _)| earlier != index)
    })
}

/// Whether two printed store chains denote one array because they write the
/// same values at the same pairwise-distinct constant indices over the same
/// root: one is the other with its writes reordered.
///
/// SOUNDNESS. For a chain over root `R` whose write indices `i_1 .. i_n` are
/// pairwise distinct, a read at `k` is the value written at `k` when `k` is
/// some `i_j`, and `R[k]` otherwise, whatever the order of the writes. Two
/// such chains over one root (one term to the checker's parser,
/// `same_printed_term`) with the same index-to-value map (indices compared by
/// value and width, values by `same_printed_term`) therefore agree at every
/// index. Equal lengths plus distinctness on both sides make the
/// containment below a bijection.
pub(super) fn same_array_by_distinct_constant_writes(surface: &str, certified: &str) -> bool {
    let (Some((surface_root, surface_writes)), Some((certified_root, certified_writes))) =
        (constant_writes(surface), constant_writes(certified))
    else {
        return false;
    };
    !surface_writes.is_empty()
        && surface_writes.len() == certified_writes.len()
        && pairwise_distinct(&surface_writes)
        && pairwise_distinct(&certified_writes)
        && surface_literal::same_printed_term(&surface_root, &certified_root)
        && surface_writes.iter().all(|(index, value)| {
            certified_writes
                .iter()
                .any(|(certified_index, certified_value)| {
                    certified_index == index
                        && surface_literal::same_printed_term(value, certified_value)
                })
        })
}

/// Whether the printed store a ROW lemma reads is the certified
/// `(store base store_index value)` with its writes reordered (see
/// [`same_array_by_distinct_constant_writes`]).
pub(super) fn reorders_certified_store(
    printed_store: &str,
    base: &str,
    store_index: &str,
    value: &str,
) -> bool {
    same_array_by_distinct_constant_writes(
        printed_store,
        &format!("(store {base} {store_index} {value})"),
    )
}

/// Whether a packed ROW `or` term prints as exactly the two flat literals, in
/// either order, so the hole over the packed clause states the flat one.
fn packed_or_prints_the_flat_clause(packed: &str, first: &str, second: &str) -> bool {
    split_application(packed, "or").is_some_and(|children| match children.as_slice() {
        [left, right] => (left == first && right == second) || (left == second && right == first),
        _ => false,
    })
}

/// The surface refusal for a ROW step over a reordered store chain: the
/// printed clause is the certified one, but no pinned rule spells it.
fn reordered_store_refusal(id: ProofId, row: &str) -> AlethePrintError {
    AlethePrintError::InvalidSurfaceStep {
        id,
        reason: format!(
            "{row} reads the certified store chain in the problem's write order (the same writes \
             at pairwise-distinct constant indices over one root); arrays_idx/arrays_row read the \
             store positionally and the pinned checker has no store-reordering rule"
        ),
    }
}

impl AlethePrinter<'_> {
    /// The refusal for a ROW1 step whose printed store [`reorders_certified_store`]
    /// and whose printed row the caller already matched to the certified one
    /// (either orientation): the surface refusal when the guard, if any, prints
    /// as the certified `(not (= store_index read_index))` (either orientation)
    /// and a packed `or`, if any, prints as exactly the flat clause; otherwise
    /// the `InvalidArrayStep` refusal, so a hole never states a clause off the
    /// certified one.
    pub(super) fn reordered_row1_refusal(
        &self,
        id: ProofId,
        [guard, packed_or]: [Option<TermId>; 2],
        [store_index, read_index]: [&str; 2],
        printed_row: &str,
    ) -> AlethePrintError {
        let printed_guard = guard.map(|guard| self.format_term(guard));
        let guard_is_certified = printed_guard.as_deref().is_none_or(|printed_guard| {
            [
                format!("(not (= {store_index} {read_index}))"),
                format!("(not (= {read_index} {store_index}))"),
            ]
            .iter()
            .any(|certified| surface_literal::same_printed_term(printed_guard, certified))
        });
        let packed_is_flat = packed_or.is_none_or(|packed| {
            printed_guard.as_deref().is_some_and(|printed_guard| {
                packed_or_prints_the_flat_clause(
                    &self.format_term(packed),
                    printed_guard,
                    printed_row,
                )
            })
        });
        if guard_is_certified && packed_is_flat {
            return reordered_store_refusal(id, "ROW1");
        }
        AlethePrintError::InvalidArrayStep {
            id,
            reason: "ROW1 over a reordered store chain prints a guard or packed clause off the \
                     certified one"
                .to_string(),
        }
    }

    /// The refusal for a ROW2 step whose printed store [`reorders_certified_store`]
    /// and whose printed row and guard the caller already matched to the
    /// certified ones: the surface refusal unless a packed `or` prints as
    /// anything but exactly the flat clause, which keeps the
    /// `InvalidArrayStep` refusal.
    pub(super) fn reordered_row2_refusal(
        &self,
        id: ProofId,
        packed_or: Option<TermId>,
        printed_guard: &str,
        printed_row: &str,
    ) -> AlethePrintError {
        if packed_or.is_none_or(|packed| {
            packed_or_prints_the_flat_clause(&self.format_term(packed), printed_guard, printed_row)
        }) {
            return reordered_store_refusal(id, "ROW2");
        }
        AlethePrintError::InvalidArrayStep {
            id,
            reason:
                "ROW2 over a reordered store chain prints a packed clause off the certified one"
                    .to_string(),
        }
    }
}

#[cfg(test)]
#[path = "reordered_row_store_tests.rs"]
mod tests;
