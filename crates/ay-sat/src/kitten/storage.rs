// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Kitten {
    pub(super) fn ensure_internal(&mut self, num_lits: usize) {
        let num_vars = num_lits / 2;
        if num_vars <= self.num_internal_vars {
            return;
        }
        let old_vars = self.num_internal_vars;
        self.num_internal_vars = num_vars;
        self.values.resize(num_lits, 0);
        self.phases.resize(num_vars, 0);
        self.vars.resize(num_vars, Var::default());
        self.marks.resize(num_vars, 0);
        self.links.resize(num_vars, Link::default());
        self.watches.resize(num_lits, Vec::new());
        self.failed.resize(num_lits, false);
        for idx in old_vars..num_vars {
            self.unassigned += 1;
            self.enqueue(idx as u32);
        }
        if self.queue_last != INVALID {
            self.queue_search = self.queue_last;
        }
    }

    pub(super) fn import_literal(&mut self, ext_lit: u32) -> u32 {
        let ext_idx = (ext_lit / 2) as usize;
        if ext_idx >= self.ext_to_int.len() {
            self.ext_to_int.resize(ext_idx + 1, 0);
        }
        let mut int_idx = self.ext_to_int[ext_idx];
        if int_idx == 0 {
            int_idx = self.int_to_ext.len() as u32 + 1;
            self.ext_to_int[ext_idx] = int_idx;
            self.int_to_ext.push(ext_idx as u32);
            let needed_lits = (int_idx as usize) * 2 + 2;
            self.ensure_internal(needed_lits);
        }
        let int_var = int_idx - 1;
        int_var * 2 + (ext_lit & 1)
    }

    pub(super) fn enqueue(&mut self, idx: u32) {
        let last = self.queue_last;
        if last == INVALID {
            self.queue_first = idx;
        } else {
            self.links[last as usize].next = idx;
        }
        self.links[idx as usize].prev = last;
        self.links[idx as usize].next = INVALID;
        self.queue_last = idx;
        self.links[idx as usize].stamp = self.queue_stamp;
        self.queue_stamp += 1;
    }

    pub(super) fn dequeue(&mut self, idx: u32) {
        let prev = self.links[idx as usize].prev;
        let next = self.links[idx as usize].next;
        if prev == INVALID {
            self.queue_first = next;
        } else {
            self.links[prev as usize].next = next;
        }
        if next == INVALID {
            self.queue_last = prev;
        } else {
            self.links[next as usize].prev = prev;
        }
    }

    pub(super) fn move_to_front(&mut self, idx: u32) {
        if idx == self.queue_last {
            return;
        }
        self.dequeue(idx);
        self.enqueue(idx);
    }

    pub(super) fn update_search(&mut self, idx: u32) {
        self.queue_search = idx;
    }

    #[inline]
    pub(super) fn clause_size(&self, ref_: u32) -> u32 {
        self.clause_data[ref_ as usize + 1]
    }

    #[inline]
    pub(super) fn clause_flags(&self, ref_: u32) -> u32 {
        self.clause_data[ref_ as usize + 2]
    }

    #[inline]
    pub(super) fn clause_lits_range(&self, ref_: u32) -> (usize, usize) {
        let start = ref_ as usize + 3;
        let size = self.clause_data[ref_ as usize + 1] as usize;
        (start, start + size)
    }

    #[inline]
    pub(super) fn clause_lit(&self, ref_: u32, pos: usize) -> u32 {
        self.clause_data[ref_ as usize + 3 + pos]
    }

    pub(super) fn set_clause_lit(&mut self, ref_: u32, pos: usize, val: u32) {
        self.clause_data[ref_ as usize + 3 + pos] = val;
    }

    pub(super) fn set_clause_flag(&mut self, ref_: u32, flag: u32) {
        self.clause_data[ref_ as usize + 2] |= flag;
    }

    pub(super) fn new_clause_ref(&self) -> u32 {
        self.clause_data.len() as u32
    }

    pub(super) fn add_clause_to_arena(&mut self, lits: &[u32], flags: u32, aux: u32) -> u32 {
        let ref_ = self.new_clause_ref();
        let stored_aux = if self.track_antecedents && (flags & LEARNED_FLAG) != 0 {
            debug_assert_eq!(
                aux as usize,
                self.resolved.len(),
                "BUG: learned kitten clause aux must match resolved antecedents",
            );
            self.resolved.len() as u32
        } else {
            aux
        };
        self.clause_data.push(stored_aux);
        self.clause_data.push(lits.len() as u32);
        self.clause_data.push(flags);
        self.clause_data.extend_from_slice(lits);
        if self.track_antecedents && (flags & LEARNED_FLAG) != 0 {
            self.clause_data.extend_from_slice(&self.resolved);
        }
        ref_
    }

    pub(super) fn connect_clause(&mut self, ref_: u32) {
        let size = self.clause_size(ref_) as usize;
        if size == 0 {
            self.mark_inconsistent(ref_);
            return;
        }
        if size == 1 {
            self.units.push(ref_);
            return;
        }
        let lit0 = self.clause_lit(ref_, 0);
        let lit1 = self.clause_lit(ref_, 1);
        self.watches[lit0 as usize].push(ref_);
        self.watches[lit1 as usize].push(ref_);
    }

    /// Add an original clause. `id` is for core extraction; `except` is a
    /// literal to exclude from the clause (INVALID = include all).
    pub(crate) fn add_clause_with_id(&mut self, id: u32, ext_lits: &[u32], except: u32) {
        if self.inconsistent != INVALID {
            return;
        }
        self.clause_buf.clear();
        let mut tautological = false;
        for &ext_lit in ext_lits {
            if ext_lit == except {
                continue;
            }
            let int_lit = self.import_literal(ext_lit);
            // No value-based simplification: CaDiCaL citten_clause_with_id
            // (kitten.c:1779-1804) adds all literals verbatim. Simplification
            // using kitten's values[] would depend on stale state from prior
            // solves, causing over-simplified clauses in COI construction (#7049).
            // Check for tautology (x and ~x) only.
            //
            // O(1) duplicate/tautology check via the marks array (was an
            // O(len) `clause_buf.contains` scan per literal = O(len^2) per
            // clause, which cost seconds per import on 100K+-literal clauses
            // reached through BVE gate extraction). `marks[var]` is all-zero
            // outside conflict analysis (every user in search.rs restores its
            // marks before returning); we set +1/-1 per polarity while
            // building the clause and restore every touched entry to 0 below,
            // preserving that invariant. A mark is set iff the literal was
            // pushed to clause_buf, so iterating clause_buf restores exactly
            // the touched set (on the tautology break the clashing literal's
            // mark was never set). Semantics identical to the contains scan:
            // same tautology detection, same first-occurrence dedup order.
            let var = (int_lit >> 1) as usize;
            let sign: i8 = if int_lit & 1 == 0 { 1 } else { -1 };
            let m = self.marks[var];
            if m == -sign {
                tautological = true;
                break;
            }
            if m == 0 {
                self.marks[var] = sign;
                self.clause_buf.push(int_lit);
            }
        }
        for &l in &self.clause_buf {
            self.marks[(l >> 1) as usize] = 0;
        }
        if tautological {
            self.clause_buf.clear();
            return;
        }
        let lits: Vec<u32> = self.clause_buf.clone();
        self.clause_buf.clear();
        let ref_ = self.add_clause_to_arena(&lits, 0, id);
        self.connect_clause(ref_);
    }

    /// Mark end of original clauses (before solving adds learned clauses).
    pub(crate) fn seal_original(&mut self) {
        self.end_original = self.clause_data.len();
    }

    /// Add an assumption for the next solve call.
    pub(crate) fn assume(&mut self, ext_lit: u32) {
        if self.status != 0 {
            self.reset_incremental();
        }
        let int_lit = self.import_literal(ext_lit);
        self.assumptions.push(int_lit);
    }
}
