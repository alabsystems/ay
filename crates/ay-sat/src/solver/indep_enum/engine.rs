// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bit-parallel enumeration engine: `ENUM_WIDTH` candidate assignments
//! propagated simultaneously as columns of machine words.
//!
//! # Representation
//!
//! Every literal owns a `ENUM_WORDS`-word bitset: bit `c` of `pos[lit]` is
//! "literal `lit` is TRUE in column `c`". A column is therefore a partial
//! assignment, `pos[lit] | pos[¬lit]` is its assigned mask, and propagation
//! only ever SETS bits (it is monotone within a block), which is what lets a
//! whole block share one clause queue.
//!
//! # Per-constraint step (one clause visit, all `ENUM_WIDTH` columns at once)
//!
//! For a clause, per word:
//!
//! ```text
//! sat      = OR  over literals of pos[l]           (already satisfied)
//! unsat    = AND over literals of pos[¬l]          (fully falsified)
//! u_i      = ~(pos[l_i] | pos[¬l_i])               (literal i unassigned)
//! unassign = OR u_i,  invalid = (>=2 of the u_i) & ~sat
//! assign   = ~sat & ~invalid & unassign            (clause is UNIT here)
//! pos[l_i] |= u_i & assign                         (propagate)
//! ```
//!
//! `unsat` accumulates into `prop_unsat`; a column with its `prop_unsat` bit
//! set is refuted. When `prop_unsat` reaches all-ones the block is finished
//! EARLY — this is the single most important performance property of the
//! route, because it means a block costs a prefix of the constraint list
//! rather than all of it.
//!
//! `invalid` (some column still has >= 2 unassigned literals) requeues the
//! constraint. A block ends when the queue drains, at which point every
//! constraint is, in every column, either satisfied or falsified — so any
//! column outside `prop_unsat` is a genuine total model of the constraint set.
//!
//! XOR constraints (a complete parity class of clauses collapsed into one
//! constraint — see `indep_enum.rs`) run the same skeleton with
//! `x = XOR pos[l_i]`, `unsat = ~x & ~unassign`, and a two-sided write.
//!
//! # Constraint ordering
//!
//! `ctick` records the order in which constraints were RESOLVED in the
//! previous block and rebuilds the next block's queue in exactly that order
//! (kissat-sup `indepsup.c` does the same). Over a few blocks the queue
//! self-organises into a propagation order, which is what makes the early
//! exit fire inside a short prefix.

mod visit;

use visit::{dead_pattern, first_zero, period_pattern, visit_clause, visit_xor};

/// log2 of the number of assignments evaluated per block.
///
/// 12 (4096 columns, 64 words per literal) is kissat-sup's `BITSET_BITS` and
/// is the right point on the curve: the total word work is INVARIANT in the
/// width (it is `2^support * Σ|constraint| / 64` either way), so the width
/// only trades per-block fixed cost (queue rebuild + block reset, O(#constraints
/// + #touched vars)) against per-literal working-set size. At 12 the fixed
/// cost is ~1% of a block and the live bitsets of a family-sized formula
/// (~1.8 MB) sit in L2; at 8 the fixed cost would dominate (2^24 blocks), and
/// at 16 the working set (~29 MB) leaves cache.
pub(super) const ENUM_BITS: u32 = 12;
/// Assignments (columns) evaluated per block.
pub(super) const ENUM_WIDTH: usize = 1 << ENUM_BITS;
/// 64-bit words per per-literal column bitset.
pub(super) const ENUM_WORDS: usize = ENUM_WIDTH / 64;

/// One block's worth of column bits.
type Bits = [u64; ENUM_WORDS];

/// Plain CNF clause constraint.
pub(super) const KIND_CLAUSE: u8 = 0;
/// XOR constraint: an ODD number of its literals must be true.
pub(super) const KIND_XOR: u8 = 1;

/// How a run ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum EnumOutcome {
    /// A column survived a fully drained block: a candidate total model.
    Candidate { block: u64, column: usize },
    /// The whole support space was enumerated and every column was refuted.
    /// NOT reported as UNSAT — see `indep_enum.rs`.
    Exhausted,
    /// Propagation saturated with constraints still unresolved (the support
    /// does not unit-propagate the formula). No verdict.
    Stalled,
    /// Interrupted / deadline / effort cap. No verdict.
    Stopped,
}

/// The engine. Owns the column bitsets and the constraint queue; nothing here
/// touches solver state.
pub(super) struct BitEnum {
    /// Dense variable count (root-fixed variables are compiled out).
    n_vars: usize,
    /// Per-literal column bitsets, `pos[lit * ENUM_WORDS + w]`.
    pos: Vec<u64>,
    /// Constraint kinds, parallel to `starts`.
    kinds: Vec<u8>,
    /// CSR bounds into `lits` (length `nc + 1`).
    starts: Vec<u32>,
    /// CSR literal payload (dense literal indices).
    lits: Vec<u32>,
    /// Constraint count.
    nc: usize,
    /// Next block's queue position per constraint (self-organising order).
    ctick: Vec<u32>,
    /// The block's circular constraint queue.
    queue: Vec<u32>,
    /// Dense variables whose bitsets were written this block. Support
    /// variables and never-written variables stay out of it, so the block
    /// reset is proportional to the work actually done.
    touched: Vec<u32>,
    /// `dirty[v]` — already in `touched`, or permanently exempt (support).
    dirty: Vec<bool>,
    /// Enumerated variables, dense ids. `support[i]` carries bit `i` of the
    /// assignment index.
    support: Vec<u32>,
    /// log2 of the columns actually used per block (`min(ENUM_BITS, |S|)`).
    bits: u32,
    /// Columns beyond `2^bits` — pre-refuted so they never produce a model.
    dead: Bits,
    /// `period[i]` is the column pattern of support bit `i` (`i < bits`).
    period: Vec<Bits>,
    /// Blocks completed.
    pub(super) blocks: u64,
    /// Constraint visits performed.
    pub(super) visits: u64,
    /// First block of the NEXT slice. A run that stops on its wall budget
    /// leaves this at the block it did not get to, so the enumeration resumes
    /// exactly where it paused instead of re-sweeping from zero
    /// (`indep_enum.rs`: the probe runs in slices interleaved with search).
    next_block: u64,
}

impl BitEnum {
    /// Build from a dense constraint set. `support` holds dense variable ids.
    pub(super) fn new(
        n_vars: usize,
        kinds: Vec<u8>,
        starts: Vec<u32>,
        lits: Vec<u32>,
        support: Vec<u32>,
    ) -> Self {
        let nc = kinds.len();
        let bits = ENUM_BITS.min(support.len() as u32);
        let period: Vec<Bits> = (0..bits).map(period_pattern).collect();
        let mut dirty = vec![false; n_vars];
        // Support variables are rewritten wholesale every block, so they must
        // never enter the touched list (and propagation can never write to
        // them: they are fully assigned in every column).
        for &v in &support {
            dirty[v as usize] = true;
        }
        Self {
            n_vars,
            pos: vec![0u64; n_vars * 2 * ENUM_WORDS],
            kinds,
            starts,
            lits,
            nc,
            ctick: (0..nc as u32).collect(),
            queue: vec![0u32; nc.max(1)],
            touched: Vec::with_capacity(n_vars),
            dirty,
            support,
            bits,
            dead: dead_pattern(bits),
            period,
            blocks: 0,
            visits: 0,
            next_block: 0,
        }
    }

    /// Number of blocks the full enumeration takes.
    pub(super) fn block_count(&self) -> u64 {
        1u64 << (self.support.len() as u32 - self.bits)
    }

    /// Columns evaluated per block.
    pub(super) fn columns_per_block(&self) -> u64 {
        1u64 << self.bits
    }

    /// Enumerate the rest of the support space (or until `should_stop`).
    ///
    /// Resumable: a `Stopped` run can be re-entered and continues from the
    /// block it did not reach, so the caller can hand the enumeration the
    /// budget in slices without ever redoing work.
    pub(super) fn run<F>(&mut self, should_stop: &F, visit_cap: u64) -> EnumOutcome
    where
        F: Fn() -> bool,
    {
        if self.nc == 0 {
            // No constraints left: every assignment is a model.
            return EnumOutcome::Candidate {
                block: 0,
                column: 0,
            };
        }
        let blocks = self.block_count();
        let mut prop_unsat = [0u64; ENUM_WORDS];
        let mut assign = [0u64; ENUM_WORDS];
        let mut xbuf = [0u64; ENUM_WORDS];
        for block in self.next_block..blocks {
            if should_stop() || self.visits >= visit_cap {
                self.next_block = block;
                return EnumOutcome::Stopped;
            }
            self.next_block = block + 1;
            self.reset_block(block, &mut prop_unsat);
            match self.propagate_block(&mut prop_unsat, &mut assign, &mut xbuf) {
                BlockOutcome::AllRefuted => {}
                BlockOutcome::Stalled => return EnumOutcome::Stalled,
                BlockOutcome::Survivor(column) => {
                    self.blocks += 1;
                    return EnumOutcome::Candidate { block, column };
                }
            }
            self.blocks += 1;
        }
        EnumOutcome::Exhausted
    }

    /// Clear the previous block's propagation and install `block`'s support
    /// pattern.
    fn reset_block(&mut self, block: u64, prop_unsat: &mut Bits) {
        for &v in &self.touched {
            let b = v as usize * 2 * ENUM_WORDS;
            self.pos[b..b + 2 * ENUM_WORDS].fill(0);
            self.dirty[v as usize] = false;
        }
        self.touched.clear();
        for (i, &v) in self.support.iter().enumerate() {
            let b = v as usize * 2 * ENUM_WORDS;
            let (t, f) = self.pos[b..b + 2 * ENUM_WORDS].split_at_mut(ENUM_WORDS);
            if (i as u32) < self.bits {
                let pat = &self.period[i];
                t.copy_from_slice(pat);
                for (slot, &p) in f.iter_mut().zip(pat.iter()) {
                    *slot = !p;
                }
            } else {
                let high = (block >> (i as u32 - self.bits)) & 1 == 1;
                let (tv, fv) = if high { (!0u64, 0u64) } else { (0u64, !0u64) };
                t.fill(tv);
                f.fill(fv);
            }
        }
        *prop_unsat = self.dead;
    }

    /// Propagate one block to saturation.
    fn propagate_block(
        &mut self,
        prop_unsat: &mut Bits,
        assign: &mut Bits,
        xbuf: &mut Bits,
    ) -> BlockOutcome {
        let nc = self.nc;
        for i in 0..nc {
            self.queue[self.ctick[i] as usize] = i as u32;
        }
        let (mut ql, mut qr, mut qcnt) = (0usize, 0usize, nc);
        let mut tick = 0u32;
        let mut idle = 0usize;
        let mut refuted = false;
        while qcnt > 0 {
            if idle > nc {
                return BlockOutcome::Stalled;
            }
            let cidx = self.queue[ql] as usize;
            ql += 1;
            if ql == nc {
                ql = 0;
            }
            qcnt -= 1;
            self.visits += 1;
            let s = self.starts[cidx] as usize;
            let e = self.starts[cidx + 1] as usize;
            let step = if self.kinds[cidx] == KIND_XOR {
                visit_xor(
                    &mut self.pos,
                    &self.lits[s..e],
                    &mut self.dirty,
                    &mut self.touched,
                    prop_unsat,
                    assign,
                    xbuf,
                )
            } else {
                visit_clause(
                    &mut self.pos,
                    &self.lits[s..e],
                    &mut self.dirty,
                    &mut self.touched,
                    prop_unsat,
                    assign,
                )
            };
            if step.assigned {
                idle = 0;
            } else {
                idle += 1;
            }
            if step.invalid {
                self.queue[qr] = cidx as u32;
                qr += 1;
                if qr == nc {
                    qr = 0;
                }
                qcnt += 1;
            } else {
                self.ctick[cidx] = tick;
                tick += 1;
            }
            if step.all_refuted {
                refuted = true;
                break;
            }
        }
        // Every constraint gets exactly one tick, so the next block's queue is
        // a permutation: resolved ones in resolution order, the rest behind.
        while qcnt > 0 {
            let cidx = self.queue[ql] as usize;
            ql += 1;
            if ql == nc {
                ql = 0;
            }
            qcnt -= 1;
            self.ctick[cidx] = tick;
            tick += 1;
        }
        debug_assert_eq!(tick as usize, nc, "ctick must stay a permutation");
        if refuted {
            return BlockOutcome::AllRefuted;
        }
        match first_zero(prop_unsat) {
            Some(column) => BlockOutcome::Survivor(column),
            None => BlockOutcome::AllRefuted,
        }
    }

    /// Value of dense variable `v` in `column`, or `None` when it stayed
    /// unassigned (it then occurs only in already-satisfied constraints).
    pub(super) fn column_value(&self, v: usize, column: usize) -> Option<bool> {
        debug_assert!(v < self.n_vars);
        let (w, bit) = (column / 64, column % 64);
        let t = self.pos[(v * 2) * ENUM_WORDS + w] >> bit & 1;
        let f = self.pos[(v * 2 + 1) * ENUM_WORDS + w] >> bit & 1;
        match (t, f) {
            (1, 0) => Some(true),
            (0, 1) => Some(false),
            _ => None,
        }
    }
}

/// Why a block ended.
enum BlockOutcome {
    /// Every column was refuted.
    AllRefuted,
    /// Some column survived a fully drained block.
    Survivor(usize),
    /// Propagation saturated with constraints unresolved.
    Stalled,
}
