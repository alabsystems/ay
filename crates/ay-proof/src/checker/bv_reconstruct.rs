// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! `bv_reconstruct_v1`: the ordered unit `(= packed word)`.
//!
//! A bounded OR/constant-left-shift/zero-extension tree contributes aligned
//! extracts of the identical opaque word. Disjoint coverage of every word bit
//! proves the equality. Intermediate widths bound each piece's live range, so
//! no truncating shift can lose a claimed bit. The word body is never opened.

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_traits::{Signed, ToPrimitive};

use super::ProofCheckError;

pub(crate) const WORK: usize = 524_288;
pub(crate) const BYTES: usize = 16_384;
const MAX_NODES: usize = 2_048;
const MAX_DEPTH: u16 = 256;

#[derive(Clone, Copy)]
struct Visit {
    term: TermId,
    width: u32,
    shift: u32,
    limit: u32,
    depth: u16,
}

/// One shared meter, including failures. Each occurrence costs at most 128
/// units (poll, entry/sort, builtin head/slots/indices, two bounded literals,
/// checked arithmetic and mask). 2048*128 + 4096 header/scratch units is below
/// WORK. The DFS stack has 257 fixed slots, no recursive calls or heap, maps,
/// copied arguments, intermediate terms, solver or polynomial fallback.
struct Inspector<'a, 'p> {
    terms: &'a TermStore,
    remaining: usize,
    exhausted: bool,
    stopped: bool,
    poll: &'p mut dyn FnMut() -> bool,
    nodes: usize,
}

impl Inspector<'_, '_> {
    fn spend(&mut self, cost: usize) -> Option<()> {
        if self.exhausted || self.stopped {
            return None;
        }
        let Some(next) = self.remaining.checked_sub(cost) else {
            self.exhausted = true;
            return None;
        };
        self.remaining = next;
        Some(())
    }

    fn occurrence(&mut self, depth: u16) -> Option<()> {
        self.spend(2)?;
        if !(self.poll)() {
            self.stopped = true;
            return None;
        }
        self.nodes = self.nodes.checked_add(1)?;
        (self.nodes <= MAX_NODES && depth <= MAX_DEPTH).then_some(())
    }

    fn width(&mut self, term: TermId) -> Option<u32> {
        self.spend(3)?;
        self.terms.entry_stamp(term)?;
        let width = self.terms.sort(term).bitvec_width()?;
        (1..=128).contains(&width).then_some(width)
    }

    fn literal(&mut self, term: TermId, width: u32) -> Option<Option<u128>> {
        self.spend(12)?;
        if self.width(term)? != width {
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

    fn holds(&mut self, clause: &[TermId]) -> Option<bool> {
        self.spend(4096)?;
        if !(self.poll)() {
            self.stopped = true;
            return None;
        }
        let &[root] = clause else {
            return None;
        };
        self.terms.entry_stamp(root)?;
        let terms = self.terms;
        let TermData::App(Symbol::Named(op), args) = terms.get(root) else {
            return None;
        };
        let &[packed, word] = args.as_slice() else {
            return None;
        };
        if op != "=" || terms.sort(root) != &Sort::Bool {
            return None;
        }
        let width = self.width(word)?;
        if self.width(packed)? != width {
            return None;
        }
        // Canonical literal checks apply even when the opaque word is a literal.
        self.literal(word, width)?;
        let root_visit = Visit {
            term: packed,
            width,
            shift: 0,
            limit: width,
            depth: 0,
        };
        let mut pending = [root_visit; MAX_DEPTH as usize + 1];
        let mut length = 1usize;
        let mut coverage = 0u128;
        let all = u128::MAX >> (128 - width);
        while length != 0 {
            length -= 1;
            let visit = pending[length];
            self.occurrence(visit.depth)?;
            if self.width(visit.term)? != visit.width
                || visit.limit > width
                || visit.shift >= visit.limit
            {
                return None;
            }
            self.spend(16)?;
            if visit.term == word {
                if visit.width != width || visit.shift != 0 || visit.limit < width || coverage != 0
                {
                    return None;
                }
                coverage = all;
                continue;
            }
            if let Some(value) = self.literal(visit.term, visit.width)? {
                if value != 0 {
                    return None;
                }
                continue;
            }
            let next_depth = visit.depth.checked_add(1)?;
            let (first, second) = match terms.get(visit.term) {
                TermData::App(Symbol::Named(op), args) if op == "bvor" => {
                    let &[left, right] = args.as_slice() else {
                        return None;
                    };
                    (
                        Visit {
                            term: left,
                            depth: next_depth,
                            ..visit
                        },
                        Some(Visit {
                            term: right,
                            depth: next_depth,
                            ..visit
                        }),
                    )
                }
                TermData::App(Symbol::Named(op), args) if op == "bvshl" => {
                    let &[value, amount] = args.as_slice() else {
                        return None;
                    };
                    self.occurrence(next_depth)?;
                    let amount = self.literal(amount, visit.width)??;
                    if amount >= u128::from(visit.width) {
                        return None;
                    }
                    let shift = visit.shift.checked_add(u32::try_from(amount).ok()?)?;
                    if shift >= visit.limit {
                        return None;
                    }
                    (
                        Visit {
                            term: value,
                            shift,
                            depth: next_depth,
                            ..visit
                        },
                        None,
                    )
                }
                TermData::App(Symbol::Indexed(op, indices), args) if op == "zero_extend" => {
                    let &[extra] = indices.as_slice() else {
                        return None;
                    };
                    let &[child] = args.as_slice() else {
                        return None;
                    };
                    let child_width = self.width(child)?;
                    if child_width.checked_add(extra)? != visit.width {
                        return None;
                    }
                    let limit = visit.limit.min(visit.shift.checked_add(child_width)?);
                    (
                        Visit {
                            term: child,
                            width: child_width,
                            limit,
                            depth: next_depth,
                            ..visit
                        },
                        None,
                    )
                }
                TermData::App(Symbol::Indexed(op, indices), args) if op == "extract" => {
                    let &[high, low] = indices.as_slice() else {
                        return None;
                    };
                    let &[source] = args.as_slice() else {
                        return None;
                    };
                    if source != word
                        || self.width(source)? != width
                        || high < low
                        || high >= width
                        || high.checked_sub(low)?.checked_add(1)? != visit.width
                        || visit.shift != low
                        || visit.shift.checked_add(visit.width)? > visit.limit
                    {
                        return None;
                    }
                    self.spend(8)?;
                    let mask = (u128::MAX >> (128 - visit.width)) << visit.shift;
                    if coverage & mask != 0 {
                        return None;
                    }
                    coverage |= mask;
                    continue;
                }
                _ => return None,
            };
            if next_depth > MAX_DEPTH {
                return None;
            }
            let added = 1 + usize::from(second.is_some());
            if length.checked_add(added)? > pending.len() {
                return None;
            }
            pending[length] = first;
            length += 1;
            if let Some(second) = second {
                pending[length] = second;
                length += 1;
            }
        }
        self.spend(2)?;
        Some(coverage == all)
    }
}

fn inspect(
    terms: &TermStore,
    clause: &[TermId],
    work: usize,
    poll: &mut dyn FnMut() -> bool,
) -> Result<bool, ProofCheckError> {
    let mut inspector = Inspector {
        terms,
        remaining: work,
        exhausted: false,
        stopped: false,
        poll,
        nodes: 0,
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

/// Propose one bounded reconstruction unit under the caller's progress owner.
/// The callback requests exactly the strict rule's fixed account and polls its
/// inspector. A stop-only proposal callback grants no source or aggregate
/// authority; the whole candidate still needs its ordinary source-scoped
/// strict replay and aggregate admission.
pub fn recognize_bv_reconstruct_with_progress(
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
    // Prepay every attempted judgment before inspecting IDs, payload or AST.
    if !progress(WORK, BYTES) {
        return Err(ProofCheckError::ResourceLimit);
    }
    if premises == 0 && arguments == 0 && inspect(terms, clause, WORK, &mut || progress(0, 0))? {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidBvReconstruct { step })
    }
}

#[cfg(test)]
mod tests;
