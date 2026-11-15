// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Version one of Clean's checked literal-offset-spine equality rule.
//!
//! Peeling literal additions and right-literal subtractions gives `B + k`
//! in Z/(2^w). Identical opaque bases cancel; their offsets alone decide the
//! asserted Boolean equality. No alias, polynomial or solver is consulted.

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_traits::{Signed, ToPrimitive};

use super::ProofCheckError;

pub(crate) const WORK: usize = 8_192;
pub(crate) const BYTES: usize = 4_096;
const MAX_FRAMES: usize = 16;

/// The inspector has no heap, recursion, argument copies or materialized terms.
/// Accounting, before inspection: binary header/slots 4; entry/sort 3;
/// canonical literal (including at most two words) 12; Boolean constant 2;
/// frame/poll 2; modular update 3; terminal comparison 2. At most two roots,
/// two spines of 16 frames plus one lookahead, and their leaves are read.
/// Even charging every row at every frame stays below 2048 units; the shared
/// 8192 ceiling conservatively includes all failed shapes and root checks.
struct Inspector<'a, 'p> {
    terms: &'a TermStore,
    remaining: usize,
    exhausted: bool,
    stopped: bool,
    poll: &'p mut dyn FnMut() -> bool,
}

impl Inspector<'_, '_> {
    fn spend(&mut self, units: usize) -> Option<()> {
        let Some(next) = self.remaining.checked_sub(units) else {
            self.exhausted = true;
            return None;
        };
        if self.exhausted || self.stopped {
            return None;
        }
        self.remaining = next;
        Some(())
    }

    fn width(&mut self, term: TermId) -> Option<u32> {
        self.spend(3)?;
        self.terms.entry_stamp(term)?;
        let width = self.terms.sort(term).bitvec_width()?;
        (1..=128).contains(&width).then_some(width)
    }

    fn equality(&mut self, term: TermId) -> Option<(TermId, TermId)> {
        let terms = self.terms;
        self.spend(4)?;
        terms.entry_stamp(term)?;
        let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
            return None;
        };
        let &[left, right] = args.as_slice() else {
            return None;
        };
        self.spend(3)?;
        (op == "=" && terms.sort(term) == &Sort::Bool).then_some((left, right))
    }

    fn boolean(&mut self, term: TermId) -> Option<Option<bool>> {
        self.spend(2)?;
        self.terms.entry_stamp(term)?;
        if self.terms.sort(term) != &Sort::Bool {
            return None;
        }
        Some(match self.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(*value),
            _ => None,
        })
    }

    /// An invalid encountered BV literal refuses; it never becomes an atom.
    fn literal(&mut self, term: TermId, width: u32) -> Option<Option<u128>> {
        self.spend(12)?;
        self.terms.entry_stamp(term)?;
        if self.terms.sort(term).bitvec_width() != Some(width) {
            return None;
        }
        Some(match self.terms.get(term) {
            TermData::Const(Constant::BitVec {
                value,
                width: actual,
            }) => {
                if *actual != width || value.is_negative() || value.bits() > u64::from(width) {
                    return None;
                }
                Some(value.to_u128()?)
            }
            TermData::Const(_) => return None,
            _ => None,
        })
    }

    fn spine(&mut self, mut term: TermId, width: u32, mask: u128) -> Option<(TermId, u128)> {
        let terms = self.terms;
        let mut offset = 0u128;
        for frames in 0..=MAX_FRAMES {
            self.spend(2)?;
            if !(self.poll)() {
                self.stopped = true;
                return None;
            }
            if self.width(term)? != width {
                return None;
            }
            self.spend(4)?;
            let TermData::App(Symbol::Named(op), args) = terms.get(term) else {
                // A literal is not the single opaque, nonliteral base.
                return (!matches!(terms.get(term), TermData::Const(_))).then_some((term, offset));
            };
            if op != "bvadd" && op != "bvsub" {
                return Some((term, offset));
            }
            let &[left, right] = args.as_slice() else {
                return None;
            };
            let first = self.literal(left, width)?;
            let second = self.literal(right, width)?;
            let (next, value, subtract) = match (op.as_str(), first, second) {
                ("bvadd", None, Some(value)) => (left, value, false),
                ("bvadd", Some(value), None) => (right, value, false),
                ("bvsub", None, Some(value)) => (left, value, true),
                (_, Some(_), Some(_)) => return None,
                _ => return Some((term, offset)),
            };
            if frames == MAX_FRAMES {
                return None;
            }
            self.spend(3)?;
            offset = if subtract {
                offset.wrapping_sub(value)
            } else {
                offset.wrapping_add(value)
            } & mask;
            term = next;
        }
        None
    }

    fn holds(&mut self, clause: &[TermId]) -> Option<bool> {
        self.spend(1)?;
        let &[root] = clause else { return None };
        let (left, right) = self.equality(root)?;
        let (source, expected) = match (self.boolean(left)?, self.boolean(right)?) {
            (None, Some(value)) => (left, value),
            (Some(value), None) => (right, value),
            _ => return None,
        };
        let (left, right) = self.equality(source)?;
        let width = self.width(left)?;
        if self.width(right)? != width {
            return None;
        }
        self.spend(2)?;
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let (left_base, first) = self.spine(left, width, mask)?;
        let (right_base, second) = self.spine(right, width, mask)?;
        self.spend(2)?;
        Some(left_base == right_base && expected == (first == second))
    }
}

fn inspect(
    terms: &TermStore,
    clause: &[TermId],
    remaining: usize,
    poll: &mut dyn FnMut() -> bool,
) -> Result<bool, ProofCheckError> {
    let mut inspector = Inspector {
        terms,
        remaining,
        exhausted: false,
        stopped: false,
        poll,
    };
    let accepted = inspector.holds(clause).unwrap_or(false);
    if inspector.exhausted || inspector.stopped {
        Err(ProofCheckError::ResourceLimit)
    } else {
        Ok(accepted)
    }
}

pub(crate) fn recognizes(terms: &TermStore, clause: &[TermId]) -> bool {
    inspect(terms, clause, WORK, &mut || true).unwrap_or(false)
}

/// Propose one bounded offset-spine unit under the caller's progress owner.
/// Every attempt requests the strict rule's fixed account through the callback
/// and polls the same semantic inspector. A stop-only proposal callback is not
/// an aggregate work ledger: the whole source-scoped candidate still needs its
/// ordinary strict replay and aggregate admission.
pub fn recognize_bv_offset_spines_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> bool {
    validate(terms, ProofId(0), clause, 0, 0, progress).is_ok()
}

pub(crate) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premises: usize,
    arguments: usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    // Every attempt, including malformed IDs and unused payload, prepays.
    if !progress(WORK, BYTES) {
        return Err(ProofCheckError::ResourceLimit);
    }
    if premises == 0 && arguments == 0 && inspect(terms, clause, WORK, &mut || progress(0, 0))? {
        return Ok(());
    }
    Err(ProofCheckError::InvalidBvOffsetSpines { step })
}

#[cfg(test)]
mod tests;
