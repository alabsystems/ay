// Copyright 2026 Andrew Yates
// Hash-based clause database for the DRAT proof checker.
// XOR hash for order-independent clause matching, power-of-two buckets.

use crate::literal::Literal;

use super::{DratChecker, Watch};

impl DratChecker {
    pub(super) fn hash_clause(clause: &[Literal]) -> u64 {
        // Order-independent multiset hash. A plain XOR loses every
        // even-multiplicity literal, producing systematic collisions for
        // non-normalized clauses. Combining an additive lane with a rotated
        // XOR lane retains multiplicity information while remaining invariant
        // under watched-literal reordering.
        let mut sum = 0u64;
        let mut xor = 0u64;
        for &lit in clause {
            let mut mixed = (lit.index() as u64).wrapping_add(0x9e37_79b9_7f4a_7c15);
            mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            mixed ^= mixed >> 31;
            sum = sum.wrapping_add(mixed);
            xor ^= mixed.rotate_left((mixed >> 58) as u32);
        }
        let combined =
            sum ^ xor.rotate_left(23) ^ (clause.len() as u64).wrapping_mul(0xd6e8_feb8_6659_fd93);
        (combined ^ (combined >> 32)).wrapping_mul(0xd6e8_feb8_6659_fd93)
    }

    pub(super) fn bucket_idx(&self, hash: u64) -> usize {
        assert!(
            self.hash_buckets.len().is_power_of_two(),
            "BUG: hash_buckets.len() = {} is not a power of two",
            self.hash_buckets.len()
        );
        (hash as usize) & (self.hash_buckets.len() - 1)
    }

    pub(super) fn maybe_rehash(&mut self) {
        if self.live_clauses <= self.hash_buckets.len() {
            return;
        }
        let new_cap = match self.hash_buckets.len().checked_mul(2) {
            Some(c) => c,
            None => return, // usize overflow — keep current capacity
        };
        let mut new_buckets = vec![Vec::new(); new_cap];
        let mask = new_cap - 1;
        for bucket in &self.hash_buckets {
            for &cidx in bucket {
                if let Some(ref clause) = self.clauses[cidx] {
                    let hash = Self::hash_clause(clause);
                    new_buckets[(hash as usize) & mask].push(cidx);
                }
            }
        }
        self.hash_buckets = new_buckets;
    }

    pub(super) fn insert_clause(&mut self, clause: Vec<Literal>) -> usize {
        let cidx = self.free_clause_slots.pop().unwrap_or(self.clauses.len());
        if clause.is_empty() {
            // Empty clause cannot be hashed or watched. Caller should handle
            // the empty-clause case (UNSAT) before reaching insert_clause.
            // Previously a debug_assert that silently passed in release builds,
            // leaving a corrupt entry in the hash table (no watch literals,
            // zero-hash bucket collision).
            if cidx == self.clauses.len() {
                self.clauses.push(Some(clause));
            } else {
                self.clauses[cidx] = Some(clause);
            }
            return cidx;
        }
        for &lit in &clause {
            self.ensure_capacity(lit.variable().index());
        }
        if clause.len() >= 2 {
            let (c0, c1) = (clause[0], clause[1]);
            self.watches[c0.index()].push(Watch {
                blocking: c1,
                clause_idx: cidx,
                core: false,
            });
            self.watches[c1.index()].push(Watch {
                blocking: c0,
                clause_idx: cidx,
                core: false,
            });
        }
        self.add_clause_occurrences(cidx, &clause);
        let bucket = self.bucket_idx(Self::hash_clause(&clause));
        self.hash_buckets[bucket].push(cidx);
        self.live_clauses += 1;
        if cidx == self.clauses.len() {
            self.clauses.push(Some(clause));
        } else {
            debug_assert!(self.clauses[cidx].is_none());
            self.clauses[cidx] = Some(clause);
        }
        self.maybe_rehash();
        cidx
    }

    /// Add a clause to each distinct literal's occurrence list.
    pub(super) fn add_clause_occurrences(&mut self, cidx: usize, clause: &[Literal]) {
        // Multiple copies of a literal in one non-normalized clause all have
        // the same cidx, which is already the last entry in that literal's
        // occurrence list after the first copy.
        for &lit in clause {
            let occurrences = &mut self.occ_lists[lit.index()];
            if occurrences.last() != Some(&cidx) {
                occurrences.push(cidx);
            }
        }
    }

    /// Re-add occurrence entries for a clause retained in the arena.
    pub(super) fn add_stored_clause_occurrences(&mut self, cidx: usize) {
        let (clauses, occ_lists) = (&self.clauses, &mut self.occ_lists);
        let Some(clause) = clauses.get(cidx).and_then(Option::as_ref) else {
            return;
        };
        for &lit in clause {
            let occurrences = &mut occ_lists[lit.index()];
            if occurrences.last() != Some(&cidx) {
                occurrences.push(cidx);
            }
        }
    }

    /// Remove a clause from each distinct literal's occurrence list.
    pub(super) fn remove_clause_occurrences(&mut self, cidx: usize) {
        let Some(clause) = self.clauses.get(cidx).and_then(Option::as_ref) else {
            return;
        };

        // Collect distinct literals into retained scratch before mutating the
        // occurrence lists. This also avoids repeated scans for duplicate
        // literals in non-normalized clauses.
        let mut literals = std::mem::take(&mut self.scratch_resolvent);
        literals.clear();
        for &lit in clause {
            if !self.marks[lit.index()] {
                self.marks[lit.index()] = true;
                literals.push(lit);
            }
        }
        for &lit in &literals {
            self.marks[lit.index()] = false;
        }

        for &lit in &literals {
            if let Some(position) = self.occ_lists[lit.index()]
                .iter()
                .position(|&candidate| candidate == cidx)
            {
                self.occ_lists[lit.index()].swap_remove(position);
            }
        }
        self.scratch_resolvent = literals;
    }

    /// Remove all index entries for a clause and make its arena slot reusable.
    /// The caller removes the hash-bucket entry and checks reason protection.
    pub(super) fn unlink_clause(&mut self, cidx: usize) {
        let Some(clause) = self.clauses.get(cidx).and_then(Option::as_ref) else {
            return;
        };
        let watched = (clause.len() >= 2).then(|| (clause[0], clause[1]));

        if let Some((first, second)) = watched {
            self.watches[first.index()].retain(|watch| watch.clause_idx != cidx);
            if second != first {
                self.watches[second.index()].retain(|watch| watch.clause_idx != cidx);
            }
        }
        self.remove_clause_occurrences(cidx);
        self.clauses[cidx] = None;
        self.free_clause_slots.push(cidx);
    }

    /// Find a clause index matching the given literal multiset
    /// (order-independent).
    ///
    /// Uses retained count/consumption scratch so matching a long clause is
    /// O(k), including exact duplicate multiplicities, without allocating on
    /// each deletion.
    pub(crate) fn find_clause_idx(&mut self, clause: &[Literal]) -> Option<usize> {
        let hash = Self::hash_clause(clause);
        let bucket = self.bucket_idx(hash);
        let mut counts = std::mem::take(&mut self.clause_match_counts);
        let mut consumed = std::mem::take(&mut self.clause_match_consumed);
        counts.clear();
        consumed.clear();
        for &lit in clause {
            *counts.entry(lit).or_insert(0) += 1;
        }

        let mut found = None;
        for &cidx in &self.hash_buckets[bucket] {
            if let Some(ref stored) = self.clauses[cidx] {
                if stored.len() != clause.len() {
                    continue;
                }
                let mut matches = true;
                for &lit in stored {
                    match counts.get_mut(&lit) {
                        Some(remaining) if *remaining > 0 => {
                            *remaining -= 1;
                            consumed.push(lit);
                        }
                        _ => {
                            matches = false;
                            break;
                        }
                    }
                }
                for &lit in &consumed {
                    if let Some(remaining) = counts.get_mut(&lit) {
                        *remaining += 1;
                    } else {
                        // Defensive only: every consumed literal was obtained
                        // from this map immediately above.
                        matches = false;
                    }
                }
                consumed.clear();
                if matches {
                    found = Some(cidx);
                    break;
                }
            }
        }
        counts.clear();
        self.clause_match_counts = counts;
        self.clause_match_consumed = consumed;
        found
    }
}
