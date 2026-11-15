// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pruning the official checker's lists of fresh variables: the collection
//! step.
//!
//! CakePB keeps, per variable, the ids of the constraints that mention it
//! (`anchor.rs` has the mechanism). A variable the formula does not mention,
//! such as one factoring introduces, is indexed from its first constraint for
//! good, and the ids of deleted constraints leave its lists only when a `red`
//! step's witness names it. Factoring's variables then sit in most learned
//! clauses: on 48432767 (schooltt, 13,755 of them beside 15,470 formula
//! variables) the 12.3M derived constraints hold 260M occurrences of them,
//! and CakePB exhausted its 12 GB heap even with the anchors in place.
//!
//! So every [`COLLECT_EVERY`] occurrences of fresh variables in derived
//! constraints, the writer writes `red >= 0 : v -> v … ;` naming each fresh
//! variable seen so far, and deletes it by id. In CakePB the witness names
//! only indexed variables, so each one's lists are cut back to live
//! constraints (`fold_get_inds_rhs`, `reindex`); the identity changes no
//! constraint, so the step has no proof goal, and the trivial constraint
//! names no variable. The pinned VeriPB and CakePB accept the shape.

use super::*;

/// Fresh-variable occurrences in derived constraints between collection
/// steps: about 400 MB of CakePB list cells (24 bytes each).
const COLLECT_EVERY: u64 = 16_000_000;

/// The fresh variables a proof has written and how much CakePB has indexed
/// for them since the last collection step.
#[derive(Default)]
pub(super) struct FreshIndex {
    /// Per variable, whether a written constraint has named it.
    seen: Vec<bool>,
    /// The variables `seen` marks, in first-written order.
    named: Vec<u32>,
    /// Occurrences written since the last collection step.
    since: u64,
    /// Collection steps written.
    pub(super) collections: u64,
    /// The interval, when not [`COLLECT_EVERY`] (tests).
    pub(super) every: u64,
}

impl FreshIndex {
    /// Count the fresh variables (at or past `formula_vars`) of a derived
    /// constraint; true once a collection step is due.
    fn note(&mut self, lits: &[Literal], formula_vars: usize) -> bool {
        for lit in lits {
            let var = lit.variable().0;
            let index = var as usize;
            if index < formula_vars {
                continue;
            }
            if index >= self.seen.len() {
                self.seen.resize(index + 1, false);
            }
            if !self.seen[index] {
                self.seen[index] = true;
                self.named.push(var);
            }
            self.since = self.since.saturating_add(1);
        }
        self.since
            >= if self.every == 0 {
                COLLECT_EVERY
            } else {
                self.every
            }
    }
}

impl<W: Write> VeripbWriter<W> {
    /// After writing a derived constraint with literals `lits`: count its
    /// fresh variables and write the collection step when one is due. A writer
    /// that knows no formula clause (hints off) or cannot number its lines
    /// writes none.
    pub(super) fn note_fresh(&mut self, lits: &[Literal]) -> io::Result<()> {
        let formula_vars = self.anchor.formula_vars();
        if formula_vars == 0 || !self.fresh.note(lits, formula_vars) {
            return Ok(());
        }
        self.fresh.since = 0;
        let Some(base) = self.original_constraints else {
            return Ok(());
        };
        let Some(seq) = self.derived_seq.checked_add(1) else {
            return Ok(());
        };
        let Some(id) = base.checked_add(seq) else {
            return Ok(());
        };
        if !self.accepting() {
            return Ok(());
        }
        let named = std::mem::take(&mut self.fresh.named);
        let result = self.write_line(|line| {
            line.extend_from_slice(b"red >= 0 :");
            for &var in &named {
                let lit = Literal::positive(crate::literal::Variable(var));
                line.push(b' ');
                push_literal_name(line, lit);
                line.extend_from_slice(b" -> ");
                push_literal_name(line, lit);
            }
            line.extend_from_slice(b" ;");
        });
        self.fresh.named = named;
        self.latch(result)?;
        self.derived_seq = seq;
        let result = self.write_line(|line| {
            line.extend_from_slice(b"del id ");
            push_u64_decimal(line, id);
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        self.fresh.collections = self.fresh.collections.saturating_add(1);
        Ok(())
    }
}

#[cfg(test)]
#[path = "collect_tests.rs"]
mod tests;
