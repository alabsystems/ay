// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lower an internally checked three-literal `ArrayGuardedRowExpansion` to
//! pinned Carcara's `arrays_row` / `arrays_idx` / `cong` / `trans`.
//!
//! MEASURED 2026-10-08 at 8a0e18584, carcara 1.1.0 (git 9a352ee), plain
//! invocation: `benchmarks/smt/QF_AUFLIA/storeinv_sf_size3.smt2` published a
//! `holey` certificate whose only unproved steps were two clauses of this
//! kind (`c !! wire downgrade at ProofId(7): kind ArrayGuardedRowExpansion
//! prints as hole`), e.g., with `S = (store V i3 x)` and `W = (store U i3 y)`,
//! `(cl (or (= i3 k) (not (= S W)) (= (select V k) (select W k))))`. No
//! lowering existed for the kind, so every instance printed as `hole`.
//!
//! The derivation is ONE subproof whose assumptions are the negations of the
//! guard and index literals, so its discharge restates the clause:
//!
//! * untouched cell, `(cl (not (= L R)) (= i j) (= (select L' j) (select R' j)))`:
//!   assume `(not (= i j))` and `(= L R)`; `arrays_row` reads each store side
//!   `(store X i v)` at `j` as `(select X j)`, `cong` equates `(select L j)`
//!   with `(select R j)`, and `trans` chains the links into the conclusion.
//!   `not_not` and `resolution` turn the discharged `(not (not (= i j)))`
//!   back into the clause's own `(= i j)`.
//! * read-back, `(cl (not (= L R)) (not (= i j)) (= v (select E j)))`:
//!   assume `(= i j)` and `(= L R)`; `arrays_idx` reads `v` at `i`, `cong`
//!   moves the read to `j` and across `L = R`, `trans` closes, and the
//!   discharge is the clause up to `reordering`.
//!
//! Every text a step names is cut out of the clause's OWN printed literals
//! (exactly what `format_clause` prints for the step), and every identity a
//! rule relies on is checked on those texts first: the guard's store side and
//! its index, the probe, and both conclusion reads. Any difference — a
//! surface override that is not the compositional rendering, a constant-array
//! fill standing for an untouched cell, two chain links that print alike —
//! returns `None`, and the caller keeps the honest `hole`. The roles come from
//! `crate::checker::array_guarded_row_printer_terms`, a sub-case of the strict
//! validator that admitted the step.

use super::*;
use crate::checker::{
    array_guarded_row_printer_terms, GuardedRowCase, GuardedRowPrinterTerms, GuardedRowRead,
};

/// Rendering allowance of one wire-gap screen question; past it the screen
/// reports the gap rather than paying for the answer.
const SCREEN_WORK_BUDGET: u64 = 4 * 1024 * 1024;

/// The clause's printed literals, cut into the pieces the rules name.
struct GuardedRowTexts {
    /// The flat literals as the step prints them, in recorded order.
    literals: Vec<String>,
    /// `(= L R)`, the atom of the guard literal.
    guard_atom: String,
    /// `L` and `R`.
    sides: [String; 2],
    /// `(= i j)` or `(= j i)`: the index literal's atom.
    index_atom: String,
    store_index: String,
    probe: String,
    /// The concluding equality and its two sides.
    conclusion: String,
    reads: [String; 2],
}

impl AlethePrinter<'_> {
    /// The checked derivation of a three-literal guarded ROW expansion, or
    /// `None` (keep the `hole`) outside the lowerable subset or past the work
    /// budget. The derivation's text is charged like any rendering work
    /// (#A2b), so the export's emission budget and the screen's shared
    /// allowance both count it.
    pub(super) fn format_array_guarded_row_expansion(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let shape = array_guarded_row_printer_terms(self.terms, clause)?;
        let packed = shape
            .packed_or
            .map(|packed| self.format_derived_literal(packed));
        let texts = self.guarded_row_texts(&shape, packed.as_deref())?;
        let flat_id = match packed {
            Some(_) => format!("{id}.flat"),
            None => id.to_string(),
        };
        let flat_clause = format!("(cl {})", texts.literals.join(" "));
        let mut lines = match shape.case {
            GuardedRowCase::Untouched { left, right } => {
                untouched_cell(id, &texts, [left, right], &flat_id, &flat_clause)?
            }
            GuardedRowCase::ReadBack { store_is_left } => {
                read_back(id, &texts, store_is_left, &flat_id, &flat_clause)?
            }
        };
        if let Some(packed) = packed {
            let mut premises = vec![flat_id];
            for (position, literal) in texts.literals.iter().enumerate() {
                let label = format!("{id}.o{position}");
                lines.push(format!(
                    "(step {label} (cl {packed} (not {literal})) :rule or_neg :args ({position}))"
                ));
                premises.push(label);
            }
            lines.push(format!(
                "(step {id} (cl {packed}) :rule resolution :premises ({}))",
                premises.join(" ")
            ));
        }
        let text = lines.join("\n");
        self.charge(text.len() as u64);
        (!self.work_budget_exhausted()).then_some(text)
    }

    fn guarded_row_texts(
        &self,
        shape: &GuardedRowPrinterTerms,
        packed: Option<&str>,
    ) -> Option<GuardedRowTexts> {
        let literals = match packed {
            Some(packed) => split_application(packed, "or")?,
            None => self.format_derived_clause_literals(&shape.literals),
        };
        if literals.len() != 3 {
            return None;
        }
        let guard_atom = negated(&literals[shape.guard])?;
        let sides = equality_sides(&guard_atom)?;
        let index_atom = match shape.case {
            GuardedRowCase::Untouched { .. } => literals[shape.index].clone(),
            GuardedRowCase::ReadBack { .. } => negated(&literals[shape.index])?,
        };
        let [first, second] = equality_sides(&index_atom)?;
        let (store_index, probe) = if shape.store_index_first {
            (first, second)
        } else {
            (second, first)
        };
        let conclusion = literals[shape.conclusion].clone();
        let reads = equality_sides(&conclusion)?;
        Some(GuardedRowTexts {
            literals,
            guard_atom,
            sides,
            index_atom,
            store_index,
            probe,
            conclusion,
            reads,
        })
    }
}

/// Shapes B/D. `reads` says, per guard side, whether the conclusion reads it
/// directly or through its store.
fn untouched_cell(
    id: ProofId,
    texts: &GuardedRowTexts,
    reads: [GuardedRowRead; 2],
    flat_id: &str,
    flat_clause: &str,
) -> Option<Vec<String>> {
    let GuardedRowTexts {
        guard_atom,
        sides,
        index_atom: index,
        store_index,
        probe,
        conclusion,
        ..
    } = texts;
    let mut lines = vec![
        format!("(anchor :step {id}.sp)"),
        format!("(assume {id}.h0 (not {index}))"),
        format!("(assume {id}.h1 {guard_atom})"),
    ];
    // `arrays_row` reads its premise POSITIONALLY as
    // `(not (= store_index probe))`; the mirror spelling is bridged.
    let apart = format!("(not (= {store_index} {probe}))");
    let row_premise = if format!("(not {index})") == apart {
        format!("{id}.h0")
    } else {
        lines.push(format!(
            "(step {id}.hs (cl {apart}) :rule not_symm :premises ({id}.h0))"
        ));
        format!("{id}.hs")
    };
    let heads = sides.clone().map(|side| format!("(select {side} {probe})"));
    let mut ends = heads.clone();
    let mut rows: [Option<String>; 2] = [None, None];
    for position in 0..2 {
        if reads[position] == GuardedRowRead::Direct {
            continue;
        }
        let [base, index_at, _] = store_fields(&sides[position])?;
        if &index_at != store_index {
            return None;
        }
        ends[position] = format!("(select {base} {probe})");
        let label = format!("{id}.r{position}");
        lines.push(format!(
            "(step {label} (cl (= {} {})) :rule arrays_row :premises ({row_premise}))",
            heads[position], ends[position]
        ));
        rows[position] = Some(label);
    }
    if !same_pair(&texts.reads, &ends) {
        return None;
    }
    // The `trans` chain `ends[0] - heads[0] - heads[1] - ends[1]`, keeping an
    // end only where an `arrays_row` link reaches it.
    let mut links: Vec<&str> = Vec::new();
    if rows[0].is_some() {
        links.push(&ends[0]);
    }
    links.extend([heads[0].as_str(), heads[1].as_str()]);
    if rows[1].is_some() {
        links.push(&ends[1]);
    }
    if !pairwise_distinct(&links) {
        return None;
    }
    lines.push(format!(
        "(step {id}.cg (cl (= {} {})) :rule cong :premises ({id}.h1))",
        heads[0], heads[1]
    ));
    let [left_row, right_row] = rows;
    let premises: Vec<String> = left_row
        .into_iter()
        .chain([format!("{id}.cg")])
        .chain(right_row)
        .collect();
    lines.push(format!(
        "(step {id}.tr (cl {conclusion}) :rule trans :premises ({}))",
        premises.join(" ")
    ));
    lines.push(format!(
        "(step {id}.sp (cl (not (not {index})) (not {guard_atom}) {conclusion}) \
         :rule subproof :discharge ({id}.h0 {id}.h1))"
    ));
    lines.push(format!(
        "(step {id}.nn (cl (not (not (not {index}))) {index}) :rule not_not)"
    ));
    lines.push(format!(
        "(step {flat_id} {flat_clause} :rule resolution :premises ({id}.sp {id}.nn))"
    ));
    Some(lines)
}

/// Shape C. `store_is_left` names the guard side that is `(store A i v)`.
fn read_back(
    id: ProofId,
    texts: &GuardedRowTexts,
    store_is_left: bool,
    flat_id: &str,
    flat_clause: &str,
) -> Option<Vec<String>> {
    let GuardedRowTexts {
        guard_atom,
        sides: [left, right],
        index_atom,
        store_index,
        probe,
        conclusion,
        ..
    } = texts;
    let (store, other) = if store_is_left {
        (left, right)
    } else {
        (right, left)
    };
    let [_, index_at, value] = store_fields(store)?;
    if &index_at != store_index {
        return None;
    }
    let at_index = format!("(select {store} {store_index})");
    let at_probe = format!("(select {store} {probe})");
    let other_read = format!("(select {other} {probe})");
    if !same_pair(&texts.reads, &[value.clone(), other_read.clone()]) {
        return None;
    }
    if !pairwise_distinct(&[&value, &at_index, &at_probe, &other_read]) {
        return None;
    }
    Some(vec![
        format!("(anchor :step {id}.sp)"),
        format!("(assume {id}.h0 {index_atom})"),
        format!("(assume {id}.h1 {guard_atom})"),
        format!("(step {id}.ix (cl (= {at_index} {value})) :rule arrays_idx)"),
        format!("(step {id}.ci (cl (= {at_index} {at_probe})) :rule cong :premises ({id}.h0))"),
        format!("(step {id}.cg (cl (= {at_probe} {other_read})) :rule cong :premises ({id}.h1))"),
        format!("(step {id}.tr (cl {conclusion}) :rule trans :premises ({id}.ix {id}.ci {id}.cg))"),
        format!(
            "(step {id}.sp (cl (not {index_atom}) (not {guard_atom}) {conclusion}) \
             :rule subproof :discharge ({id}.h0 {id}.h1))"
        ),
        format!("(step {flat_id} {flat_clause} :rule reordering :premises ({id}.sp))"),
    ])
}

/// `X` for the printed literal `(not X)`, which must re-spell exactly.
fn negated(literal: &str) -> Option<String> {
    let [inner]: [String; 1] = split_application(literal, "not")?.try_into().ok()?;
    (format!("(not {inner})") == literal).then_some(inner)
}

/// `[a, b]` for the printed `(= a b)`, which must re-spell exactly.
fn equality_sides(equality: &str) -> Option<[String; 2]> {
    let [left, right]: [String; 2] = split_application(equality, "=")?.try_into().ok()?;
    (format!("(= {left} {right})") == equality).then_some([left, right])
}

/// `[base, index, value]` for the printed `(store base index value)`, which
/// must re-spell exactly.
fn store_fields(store: &str) -> Option<[String; 3]> {
    let [base, index, value]: [String; 3] = split_application(store, "store")?.try_into().ok()?;
    (format!("(store {base} {index} {value})") == store).then_some([base, index, value])
}

/// Whether the printed conclusion sides are `expected`, in either order.
fn same_pair(reads: &[String; 2], expected: &[String; 2]) -> bool {
    (reads[0] == expected[0] && reads[1] == expected[1])
        || (reads[0] == expected[1] && reads[1] == expected[0])
}

/// Carcara's `trans` walks its premises greedily from the conclusion's left
/// side; with pairwise-distinct links every link sits in exactly one unused
/// premise, so the walk cannot take a wrong turn.
fn pairwise_distinct(links: &[&str]) -> bool {
    links
        .iter()
        .enumerate()
        .all(|(position, link)| !links[position + 1..].contains(link))
}

/// Whether the exporter lowers this `ArrayGuardedRowExpansion` clause to the
/// checked derivation above under `term_overrides` — the wire-gap screen's
/// question (`Executor::proof_has_known_wire_gap`). Each ask renders under at
/// most `SCREEN_WORK_BUDGET` and is charged to `remaining_work`, the
/// allowance the screen shares across one proof's guarded ROW lemmas, so many
/// individually bounded lemmas cannot multiply it; an exhausted allowance
/// answers `false` and the screen keeps the gap.
#[must_use]
pub fn checked_guarded_row_expansion_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    if *remaining_work == 0 {
        return false;
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        term_overrides,
        Some((*remaining_work).min(SCREEN_WORK_BUDGET)),
    );
    let supported = printer
        .format_array_guarded_row_expansion(ProofId(0), clause)
        .is_some();
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}

#[cfg(test)]
#[path = "guarded_row_expansion_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "guarded_row_expansion_surface_tests.rs"]
mod surface_tests;
