// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keeping the official checker's variable index small: the anchor.
//!
//! CakePB (CP2026, the verified checker behind SAT-COMP 2026's UNSAT route)
//! keeps, per variable, the ids of the constraints that mention it, so a `red`
//! step can find the constraints its witness touches (`vimap`,
//! `npbc_listScript.sml` in CakeML's `examples/pseudo_bool/array`). A formula
//! variable's list is complete while loading; the first derived constraint
//! that mentions it once it is in 10 constraints (`ind_lim`) drops the list
//! for good, so a learned clause costs nothing there. But a `red` whose
//! witness names only indexed variables re-indexes each one and marks it
//! *tracked forever*, and a single-variable `red` on a dropped variable
//! rebuilds its list by scanning every id the proof has created
//! (`get_set_indices`). From then on every derived constraint mentioning a
//! tracked variable is consed onto its list, and deleted ids leave only when
//! a later witness names the variable again.
//!
//! AY wrote both shapes: the symmetry routes' witnesses (fix-and-cut's first
//! line maps all 320 variables of vdw_3_13_n160) and the pivot witness of an
//! unhinted addition (`x_p -> 1`, vivification's hint fallbacks). On
//! 996bd632 the first made every variable tracked, and the 11.4M learned
//! clauses after it put 281M entries on the lists: CakePB exhausted its 12 GB
//! heap. On b3c58750 13,385 pivot witnesses each rescanned up to 80M ids, and
//! the check timed out at 62,829 s before it too ran out of heap.
//!
//! A witness that names a variable whose list was dropped takes the other
//! branch: one pass over the live ids (which also prunes CakePB's id list)
//! and no change to any variable's list. So the writer makes two formula
//! variables dropped up front, the anchors, and adds the identity `a -> a` of
//! one to every witness that would otherwise take the indexing branch. The
//! anchoring step is `red 1 a 1 b 1 ay_anchor >= 1 : ay_anchor -> 1 ;`
//! (redundant because `ay_anchor` occurs nowhere else, a name no `x<n>` can
//! collide with), deleted by id at once: a derived constraint naming `a` and
//! `b` while each is in at least 10 formula constraints drops both lists. Every
//! `red` step already makes CakePB hash its whole live database to look up
//! the witness's goals, so the pass costs at most that again.
//!
//! Witnesses that name only fresh variables (factoring's definitions) are left
//! alone: a fresh variable is tracked from its first constraint either way,
//! and its list is short.

use super::*;

/// Formula clauses a variable must occur in to anchor: CakePB drops a list at
/// 10 (`ind_lim`); two spare for clauses its parser normalizes differently.
const ANCHOR_MIN_OCCURRENCES: u32 = 12;

/// The anchoring step's fresh variable.
const ANCHOR_FRESH: &[u8] = b"ay_anchor";

/// The anchor state of one proof (see the module docs).
#[derive(Default)]
pub(super) struct CakepbAnchor {
    /// Per variable, the formula clauses it occurs in (tautologies skipped,
    /// each variable once per clause): CakePB's load-time count.
    occurrences: Vec<u32>,
    /// `note_clause`'s reusable buffer of (variable, polarity).
    scratch: Vec<(u32, bool)>,
    /// `None` until the first witness that needs an anchor; then the two
    /// anchors (0-based variables), or `None` inside when there are none.
    anchors: Option<Option<[u32; 2]>>,
    /// `red` steps written with an anchor's identity added.
    pub(super) anchored: u64,
}

impl CakepbAnchor {
    /// Count a formula clause's variables.
    pub(super) fn note_clause(&mut self, clause: &[Literal]) {
        self.scratch.clear();
        self.scratch.extend(
            clause
                .iter()
                .map(|lit| (lit.variable().0, lit.is_positive())),
        );
        self.scratch.sort_unstable();
        self.scratch.dedup();
        if self.scratch.windows(2).any(|w| w[0].0 == w[1].0) {
            return;
        }
        for &(var, _) in &self.scratch {
            let index = var as usize;
            if index >= self.occurrences.len() {
                self.occurrences.resize(index + 1, 0);
            }
            self.occurrences[index] = self.occurrences[index].saturating_add(1);
        }
    }

    /// The number of variables the formula's clauses span (0 when the writer
    /// has seen none): every variable from here on is fresh to CakePB.
    pub(super) fn formula_vars(&self) -> usize {
        self.occurrences.len()
    }

    /// A variable some formula clause names.
    fn is_formula_variable(&self, var: u32) -> bool {
        self.occurrences
            .get(var as usize)
            .is_some_and(|&count| count > 0)
    }

    /// The two variables with the fewest occurrences of at least
    /// [`ANCHOR_MIN_OCCURRENCES`]: an identity on a variable makes VeriPB
    /// visit its constraints, so the rarest qualifying ones cost least.
    fn pick(&self) -> Option<[u32; 2]> {
        let mut best: [Option<(u32, u32)>; 2] = [None, None];
        for (var, &count) in self.occurrences.iter().enumerate() {
            if count < ANCHOR_MIN_OCCURRENCES {
                continue;
            }
            let entry = (count, var as u32);
            if best[0].is_none_or(|b| entry < b) {
                best[1] = best[0];
                best[0] = Some(entry);
            } else if best[1].is_none_or(|b| entry < b) {
                best[1] = Some(entry);
            }
        }
        match best {
            [Some((_, a)), Some((_, b))] => Some([a, b]),
            _ => None,
        }
    }
}

impl<W: Write> VeripbWriter<W> {
    /// The anchor whose identity `map` (a witness about to be written) needs,
    /// writing the anchoring step first if this is the first such witness.
    /// `None` when the witness names no formula variable, already names an
    /// anchor beside another variable, or the proof has no anchors.
    pub(super) fn anchor_for(&mut self, map: &[(u32, SubImage)]) -> io::Result<Option<u32>> {
        if !map
            .iter()
            .any(|&(var, _)| self.anchor.is_formula_variable(var))
        {
            return Ok(None);
        }
        let anchors = match self.anchor.anchors {
            Some(anchors) => anchors,
            None => self.write_anchoring_step()?,
        };
        let Some([a, b]) = anchors else {
            return Ok(None);
        };
        let names = |var: u32| map.iter().any(|&(v, _)| v == var);
        if map.len() >= 2 && (names(a) || names(b)) {
            return Ok(None);
        }
        self.anchor.anchored = self.anchor.anchored.saturating_add(1);
        Ok(Some(if names(a) { b } else { a }))
    }

    /// Decide the anchors and, when there are two, write the anchoring step
    /// and its deletion. Without the formula's line count the step could not
    /// be deleted by id, and a witness written before the anchors would have
    /// tracked its variables already, so then there are none for this proof.
    fn write_anchoring_step(&mut self) -> io::Result<Option<[u32; 2]>> {
        let picked = self.original_constraints.and_then(|base| {
            let seq = self.derived_seq.checked_add(1)?;
            Some((self.anchor.pick()?, seq, base.checked_add(seq)?))
        });
        let Some(([a, b], seq, id)) = picked else {
            self.anchor.anchors = Some(None);
            return Ok(None);
        };
        self.anchor.anchors = Some(Some([a, b]));
        let result = self.write_line(|line| {
            line.extend_from_slice(b"red ");
            for var in [a, b] {
                line.extend_from_slice(b"1 ");
                push_literal_name(line, Literal::positive(crate::literal::Variable(var)));
                line.push(b' ');
            }
            line.extend_from_slice(b"1 ");
            line.extend_from_slice(ANCHOR_FRESH);
            line.extend_from_slice(b" >= 1 : ");
            line.extend_from_slice(ANCHOR_FRESH);
            line.extend_from_slice(b" -> 1 ;");
        });
        self.latch(result)?;
        self.derived_seq = seq;
        let result = self.write_line(|line| {
            line.extend_from_slice(b"del id ");
            push_u64_decimal(line, id);
            line.extend_from_slice(b" ;");
        });
        self.latch(result)?;
        Ok(Some([a, b]))
    }
}

#[cfg(test)]
#[path = "anchor_tests.rs"]
mod tests;
