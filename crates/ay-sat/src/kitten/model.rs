// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Kitten {
    /// Get literal value after SAT. Returns -1, 0, or +1.
    pub(crate) fn value(&self, ext_lit: u32) -> i8 {
        let ext_idx = (ext_lit / 2) as usize;
        if ext_idx >= self.ext_to_int.len() {
            return 0;
        }
        let int_idx = self.ext_to_int[ext_idx];
        if int_idx == 0 {
            return 0;
        }
        let int_lit = (int_idx - 1) * 2 + (ext_lit & 1);
        if (int_lit as usize) < self.values.len() {
            self.values[int_lit as usize]
        } else {
            0
        }
    }

    /// Get a literal's fixed level-0 value. Returns -1, 0, or +1.
    pub(crate) fn fixed_value(&self, ext_lit: u32) -> i8 {
        let ext_idx = (ext_lit / 2) as usize;
        if ext_idx >= self.ext_to_int.len() {
            return 0;
        }
        let int_idx = self.ext_to_int[ext_idx];
        if int_idx == 0 {
            return 0;
        }
        let int_var = (int_idx - 1) as usize;
        let int_lit = (int_idx - 1) * 2 + (ext_lit & 1);
        if int_var >= self.vars.len() || self.vars[int_var].level != 0 {
            return 0;
        }
        self.values.get(int_lit as usize).copied().unwrap_or(0)
    }

    /// Try to flip a literal's assignment. Returns true if all watched
    /// clauses remain satisfied (O(watchlist) operation).
    ///
    /// The literal must currently be satisfied (value > 0 in external terms).
    /// On success, the literal's value is flipped in-place.
    /// On failure, the watch lists are left consistent.
    pub(crate) fn flip_literal(&mut self, ext_lit: u32) -> bool {
        let ext_idx = (ext_lit / 2) as usize;
        if ext_idx >= self.ext_to_int.len() {
            return false;
        }
        let int_idx = self.ext_to_int[ext_idx];
        if int_idx == 0 {
            return false;
        }
        // CaDiCaL kitten.c:2250-2261: refuse to flip level-0 (root) literals.
        // Level-0 assignments are permanent and survive reset_incremental().
        // Flipping them corrupts the state: the flipped value persists as a
        // "level-0 fact" that contradicts the original propagation reason,
        // causing false backbone/equivalence claims in subsequent probing.
        let int_var = (int_idx - 1) as usize;
        if int_var < self.vars.len() && self.vars[int_var].level == 0 {
            return false;
        }
        let mut lit = (int_idx - 1) * 2 + (ext_lit & 1);
        if self.values[lit as usize] < 0 {
            lit ^= 1;
        }
        if self.values[lit as usize] <= 0 {
            return false;
        }

        let mut watch_list = std::mem::take(&mut self.watches[lit as usize]);
        let mut j = 0;
        let mut success = true;
        let mut ticks: u64 = (watch_list.len() as u64 / 16) + 1;

        let mut i = 0;
        while i < watch_list.len() {
            let ref_ = watch_list[i];
            i += 1;
            ticks += 1;

            let lit0 = self.clause_lit(ref_, 0);
            let lit1 = self.clause_lit(ref_, 1);
            let other = lit0 ^ lit1 ^ lit;
            let other_value = self.values[other as usize];

            if other_value > 0 {
                watch_list[j] = ref_;
                j += 1;
                continue;
            }

            let size = self.clause_size(ref_) as usize;
            let mut replacement = INVALID;
            let mut replacement_value: i8 = -1;
            let mut replacement_pos = 0;
            for k in 2..size {
                let r = self.clause_lit(ref_, k);
                let rv = self.values[r as usize];
                if rv > 0 {
                    replacement = r;
                    replacement_value = rv;
                    replacement_pos = k;
                    break;
                }
            }

            if replacement_value > 0 {
                debug_assert!(replacement != INVALID);
                self.set_clause_lit(ref_, 0, other);
                self.set_clause_lit(ref_, 1, replacement);
                self.set_clause_lit(ref_, replacement_pos, lit);
                self.watches[replacement as usize].push(ref_);
            } else {
                watch_list[j] = ref_;
                j += 1;
                success = false;
                break;
            }
        }

        while i < watch_list.len() {
            watch_list[j] = watch_list[i];
            j += 1;
            i += 1;
        }
        watch_list.truncate(j);
        self.watches[lit as usize] = watch_list;
        self.ticks += ticks;

        if success {
            self.values[lit as usize] = -1;
            self.values[(lit ^ 1) as usize] = 1;
        }

        success
    }

    /// Compute the clausal core after UNSAT. Returns the core clause IDs.
    pub(crate) fn compute_clausal_core(&mut self) -> Vec<u32> {
        if !self.track_antecedents || self.inconsistent == INVALID {
            return Vec::new();
        }

        self.reset_core_marks();

        let mut queue: Vec<u32> = vec![self.inconsistent];
        let mut qi = 0;
        while qi < queue.len() {
            let ref_ = queue[qi];
            qi += 1;
            if (self.clause_flags(ref_) & CORE_FLAG) != 0 {
                continue;
            }
            self.set_clause_flag(ref_, CORE_FLAG);

            if (self.clause_flags(ref_) & LEARNED_FLAG) != 0 {
                let aux = self.clause_data[ref_ as usize] as usize;
                let size = self.clause_size(ref_) as usize;
                let ante_start = ref_ as usize + 3 + size;
                for j in 0..aux {
                    let ante_ref = self.clause_data[ante_start + j];
                    if ante_ref != INVALID {
                        queue.push(ante_ref);
                    }
                }
            }
        }

        let mut core_ids = Vec::new();
        let mut offset = 0;
        while offset + 2 < self.end_original {
            let aux = self.clause_data[offset];
            let size = self.clause_data[offset + 1] as usize;
            let flags = self.clause_data[offset + 2];
            if (flags & CORE_FLAG) != 0 {
                core_ids.push(aux);
            }
            offset += 3 + size;
        }

        core_ids
    }

    fn reset_core_marks(&mut self) {
        let mut offset = 0;
        while offset + 2 < self.clause_data.len() {
            let size = self.clause_data[offset + 1] as usize;
            let flags = self.clause_data[offset + 2];
            if (flags & CORE_FLAG) != 0 {
                self.clause_data[offset + 2] = flags & !CORE_FLAG;
            }
            let extra = if (flags & LEARNED_FLAG) != 0 && self.track_antecedents {
                self.clause_data[offset] as usize
            } else {
                0
            };
            offset += 3 + size + extra;
        }
    }
}
