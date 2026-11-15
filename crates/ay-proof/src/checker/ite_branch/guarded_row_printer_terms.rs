// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The roles of a THREE-literal guarded ROW expansion, for the Alethe
//! printer's lowering to pinned Carcara's `arrays_row` / `arrays_idx` /
//! `cong` / `trans` (`alethe_printer/guarded_row_expansion.rs`).
//!
//! Two spellings are lowered, each a sub-case of
//! [`super::validate_array_guarded_row_expansion`]:
//!
//! * [`GuardedRowCase::Untouched`] — shapes B and D:
//!   `(cl (not (= L R)) (= i j) (= (select L' j) (select R' j)))`, where each
//!   of `L'`/`R'` is that side itself or, when the side is `(store X i v)`,
//!   its base `X` — and at least one side is such a store. Under `L = R` and
//!   `i ≠ j` every store side reads its own base at `j`, and the two sides
//!   read alike at `j`.
//! * [`GuardedRowCase::ReadBack`] — shape C:
//!   `(cl (not (= L R)) (not (= i j)) (= v (select E j)))`, one side
//!   `(store A i v)` and the other `E`. Under `L = R` and `i = j` the store
//!   reads `v` back at `j`, and so does `E`.
//!
//! Every other spelling the validator accepts has no extractor here and keeps
//! the honest `hole`: the two-literal `ite` (shape A), a store pair whose
//! payload is an `ite`, and the constant-array fold (an untouched cell spelled
//! as the fill `d`, for which pinned Carcara has no rule).

use ay_core::{Sort, TermId, TermStore};

use super::{decode_eq, decode_select, decode_store, flatten_clause_literals, strip_not};

/// How the conclusion reads one side `X` of the guard's array equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardedRowRead {
    /// `(select X j)` itself.
    Direct,
    /// `X` is `(store base i v)` and the conclusion reads `(select base j)`.
    Skipped,
}

/// Which guarded read-over-write case the clause states.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardedRowCase {
    /// Shapes B and D: the untouched cell, read through each guard side.
    Untouched {
        left: GuardedRowRead,
        right: GuardedRowRead,
    },
    /// Shape C: the stored value read back; `store_is_left` names the guard
    /// side that is `(store A i v)`.
    ReadBack { store_is_left: bool },
}

/// The clause's literals by role, as positions into its flat literal list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GuardedRowPrinterTerms {
    /// The single `(or ..)` literal the clause packs its literals into.
    pub packed_or: Option<TermId>,
    /// The flat literals, in recorded order.
    pub literals: Vec<TermId>,
    /// Position of `(not (= L R))`.
    pub guard: usize,
    /// Position of `(= i j)` (untouched) or `(not (= i j))` (read-back).
    pub index: usize,
    /// Position of the concluding equality.
    pub conclusion: usize,
    /// Whether the index equality spells the STORE index first.
    pub store_index_first: bool,
    pub case: GuardedRowCase,
}

/// The lowerable roles of `clause`, or `None` when it is not one of the two
/// spellings above.
pub(crate) fn array_guarded_row_printer_terms(
    terms: &TermStore,
    clause: &[TermId],
) -> Option<GuardedRowPrinterTerms> {
    let literals = flatten_clause_literals(terms, clause);
    if literals.len() != 3 {
        return None;
    }
    let packed_or = match clause {
        [packed] => Some(*packed),
        _ => None,
    };
    for (guard, index, conclusion) in [
        (0, 1, 2),
        (0, 2, 1),
        (1, 0, 2),
        (1, 2, 0),
        (2, 0, 1),
        (2, 1, 0),
    ] {
        let (guard_atom, guard_negated) = strip_not(terms, literals[guard]);
        if !guard_negated {
            continue;
        }
        let Some((left, right)) = decode_eq(terms, guard_atom) else {
            continue;
        };
        if !matches!(terms.sort(left), Sort::Array(_)) || terms.sort(left) != terms.sort(right) {
            continue;
        }
        let Some((case, store_index_first)) =
            guarded_row_case(terms, (left, right), literals[index], literals[conclusion])
        else {
            continue;
        };
        return Some(GuardedRowPrinterTerms {
            packed_or,
            literals,
            guard,
            index,
            conclusion,
            store_index_first,
            case,
        });
    }
    None
}

/// The case `index` and `conclusion` state about the guard sides, and whether
/// the index equality names the store index first.
fn guarded_row_case(
    terms: &TermStore,
    sides: (TermId, TermId),
    index: TermId,
    conclusion: TermId,
) -> Option<(GuardedRowCase, bool)> {
    let (index_atom, index_negated) = strip_not(terms, index);
    let (first, second) = decode_eq(terms, index_atom)?;
    let reads = decode_eq(terms, conclusion)?;
    for (store_index, probe, store_index_first) in [(first, second, true), (second, first, false)] {
        if terms.sort(store_index) != terms.sort(probe) {
            continue;
        }
        let case = if index_negated {
            read_back_case(terms, sides, (store_index, probe), reads)
        } else {
            untouched_case(terms, sides, (store_index, probe), reads)
        };
        if let Some(case) = case {
            return Some((case, store_index_first));
        }
    }
    None
}

/// Shapes B/D: each conclusion side reads one guard side at `probe`, through
/// that side's store at `store_index` when [`GuardedRowRead::Skipped`].
fn untouched_case(
    terms: &TermStore,
    (left, right): (TermId, TermId),
    (store_index, probe): (TermId, TermId),
    (read_a, read_b): (TermId, TermId),
) -> Option<GuardedRowCase> {
    use GuardedRowRead::{Direct, Skipped};
    let reads = |side: TermId, read: GuardedRowRead, term: TermId| {
        let array = match read {
            Direct => side,
            Skipped => match decode_store(terms, side) {
                Some((base, index, _)) if index == store_index => base,
                _ => return false,
            },
        };
        decode_select(terms, term) == Some((array, probe))
    };
    // Direct/Direct is pure congruence, which the validator does not accept as
    // a guarded ROW expansion: at least one side must skip its store.
    for (left_read, right_read) in [(Skipped, Direct), (Direct, Skipped), (Skipped, Skipped)] {
        let matched = (reads(left, left_read, read_a) && reads(right, right_read, read_b))
            || (reads(left, left_read, read_b) && reads(right, right_read, read_a));
        if matched {
            return Some(GuardedRowCase::Untouched {
                left: left_read,
                right: right_read,
            });
        }
    }
    None
}

/// Shape C: one guard side is `(store A store_index v)`, and the conclusion
/// equates `v` with the OTHER side read at `probe`.
fn read_back_case(
    terms: &TermStore,
    (left, right): (TermId, TermId),
    (store_index, probe): (TermId, TermId),
    (read_a, read_b): (TermId, TermId),
) -> Option<GuardedRowCase> {
    for (store, other, store_is_left) in [(left, right, true), (right, left, false)] {
        let Some((_, index, value)) = decode_store(terms, store) else {
            continue;
        };
        if index != store_index {
            continue;
        }
        let reads_other = |term: TermId| decode_select(terms, term) == Some((other, probe));
        if (read_a == value && reads_other(read_b)) || (read_b == value && reads_other(read_a)) {
            return Some(GuardedRowCase::ReadBack { store_is_left });
        }
    }
    None
}
