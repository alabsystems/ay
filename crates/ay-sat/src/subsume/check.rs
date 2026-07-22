// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Marking and subsumption check logic (CaDiCaL subsume.cpp:74-305).

use super::Subsumer;
use crate::clause::clause_signature_vars_subset;
use crate::clause_arena::ClauseArena;
use crate::literal::Literal;

impl Subsumer {
    // ---------------------------------------------------------------
    // Marking (CaDiCaL: mark/unmark with signed polarity)
    // ---------------------------------------------------------------

    /// Mark all literals of a clause. Each variable's mark slot stores
    /// `lit.0 + 1` so that polarity can be checked in O(1).
    #[inline]
    pub(super) fn mark_clause(&mut self, lits: &[Literal]) {
        for &lit in lits {
            let v = lit.variable().index();
            if v < self.marks.len() {
                self.marks[v] = lit.0 + 1;
            }
        }
    }

    /// Unmark all literals of a clause.
    #[inline]
    pub(super) fn unmark_clause(&mut self, lits: &[Literal]) {
        for &lit in lits {
            let v = lit.variable().index();
            if v < self.marks.len() {
                self.marks[v] = 0;
            }
        }
    }

    /// Check if a literal is marked with its exact polarity.
    /// Returns +1 if same polarity, -1 if opposite polarity, 0 if unmarked.
    #[inline]
    fn marked(&self, lit: Literal) -> i32 {
        let v = lit.variable().index();
        if v >= self.marks.len() {
            return 0;
        }
        let m = self.marks[v];
        if m == 0 {
            return 0;
        }
        // m == lit.0 + 1 means same polarity
        if m == lit.0 + 1 {
            1
        } else {
            -1
        }
    }

    #[inline]
    pub(super) fn literal_nocc(&self, lit: Literal) -> u64 {
        self.noccs.get(lit.index()).copied().unwrap_or(0)
    }

    #[inline]
    pub(super) fn ordered_watch_pair(&self, lit0: Literal, lit1: Literal) -> (Literal, Literal) {
        let key = |lit: Literal| (self.literal_nocc(lit), lit.variable().index());
        if key(lit0) <= key(lit1) {
            (lit0, lit1)
        } else {
            (lit1, lit0)
        }
    }

    #[inline]
    fn process_subsuming_literal(&self, lit: Literal, flipped: &mut i32) -> bool {
        let tmp = self.marked(lit);
        if tmp == 0 {
            return false;
        }
        if tmp > 0 {
            return true;
        }
        if *flipped != 0 {
            return false;
        }
        *flipped = (lit.0 as i32) + 1;
        true
    }

    #[inline]
    pub(super) fn connection_size(&self, lit: Literal, is_binary_irred: bool) -> usize {
        if is_binary_irred {
            self.bins.get(lit.index()).map_or(0, Vec::len)
        } else {
            self.occs.get(lit.index()).map_or(0, Vec::len)
        }
    }

    #[inline]
    pub(super) fn pick_connection_literal(
        &self,
        c_lits: &[Literal],
        is_binary_irred: bool,
    ) -> Literal {
        let mut min_lit = c_lits[0];
        let mut min_size = self.connection_size(min_lit, is_binary_irred);
        let mut min_noccs = self.literal_nocc(min_lit);

        for &lit in &c_lits[1..] {
            let size = self.connection_size(lit, is_binary_irred);
            if size < min_size {
                min_lit = lit;
                min_size = size;
                min_noccs = self.literal_nocc(lit);
                continue;
            }
            if size == min_size {
                let lit_noccs = self.literal_nocc(lit);
                if lit_noccs > min_noccs {
                    min_lit = lit;
                    min_noccs = lit_noccs;
                }
            }
        }

        min_lit
    }

    // ---------------------------------------------------------------
    // Core subsumption check (CaDiCaL subsume.cpp:74-119)
    // ---------------------------------------------------------------

    /// Check if `subsuming` subsumes or can strengthen the (marked) candidate.
    ///
    /// Precondition: candidate clause's literals are marked via `mark_clause`.
    ///
    /// Returns:
    /// - `i32::MIN` if subsumption (all subsuming literals found with correct polarity)
    /// - `0` if neither subsumption nor strengthening
    /// - `(lit.0 + 1) as i32` if strengthening (exactly one opposite-polarity literal).
    ///   +1 offset avoids collision with `Literal(0).0 == 0` and the "no match" sentinel.
    pub(super) fn subsume_check(&mut self, subsuming_lits: &[Literal]) -> i32 {
        self.stats.checks += 1;
        self.round_checks += 1;

        let mut flipped: i32 = 0;
        if subsuming_lits.len() > 2 {
            // CaDiCaL sorts the full clause by noccs before connecting it as a
            // subsumer. AY keeps watched literals in positions [0] and [1], so
            // the physical clause order cannot match that exactly. Compensate by
            // checking the already rare-sorted tail first, then the watched pair
            // in rare-first order. This preserves 2WL invariants while keeping
            // subsume_check close to CaDiCaL's fail-fast literal order.
            for &lit in &subsuming_lits[2..] {
                if !self.process_subsuming_literal(lit, &mut flipped) {
                    return 0;
                }
            }
            let (watch0, watch1) = self.ordered_watch_pair(subsuming_lits[0], subsuming_lits[1]);
            for lit in <[_; 2]>::from((watch0, watch1)) {
                if !self.process_subsuming_literal(lit, &mut flipped) {
                    return 0;
                }
            }
        } else {
            for &lit in subsuming_lits {
                if !self.process_subsuming_literal(lit, &mut flipped) {
                    return 0;
                }
            }
        }
        if flipped == 0 {
            i32::MIN // subsumption
        } else {
            flipped // strengthening: decode as Literal((flipped - 1) as u32)
        }
    }

    // ---------------------------------------------------------------
    // Forward subsumption attempt (CaDiCaL subsume.cpp:184-305)
    // ---------------------------------------------------------------

    /// Try to subsume or strengthen candidate clause `c_idx` using the
    /// one-watch occurrence lists and binary clause table.
    ///
    /// `subsume_dirty`: per-variable dirty bits (true = variable added since last round).
    ///
    /// Returns: `(subsumer_idx_or_none, flipped)` where flipped is as per `subsume_check`.
    pub(super) fn try_to_subsume_clause(
        &mut self,
        c_idx: usize,
        c_lits: &[Literal],
        subsume_dirty: &[bool],
        clauses: &ClauseArena,
    ) -> (Option<usize>, i32) {
        // Mark candidate clause
        self.mark_clause(c_lits);

        // Pre-compute candidate's 64-bit clause signature for bloom-style
        // pre-filtering. For D to subsume or strengthen C, every variable in D
        // must appear as a variable in C (polarity may differ for at most one
        // literal in the strengthening case). The variable-level signature
        // check `clause_signature_vars_subset` filters non-candidates in O(1)
        // before the O(|D|) literal-by-literal `subsume_check`.
        let c_sig = clauses.signature(c_idx);

        let mut found_d: Option<usize> = None;
        let mut flipped: i32 = 0;

        'outer: for &lit in c_lits {
            // Only traverse occ-lists of recently-added variables
            let v = lit.variable().index();
            if v >= subsume_dirty.len() || !subsume_dirty[v] {
                continue;
            }

            // Check both polarities of this variable
            for sign in [lit, lit.negated()] {
                let sign_idx = sign.index();

                // Check binary clauses first (cache-friendly flat array)
                if sign_idx < self.bins.len() {
                    for bi in 0..self.bins[sign_idx].len() {
                        let bin = self.bins[sign_idx][bi];
                        if bin.clause_idx >= clauses.len()
                            || !clauses.is_active(bin.clause_idx)
                            || clauses.is_dead(bin.clause_idx)
                        {
                            continue;
                        }
                        let tmp = self.marked(bin.other);
                        if tmp == 0 {
                            continue;
                        }
                        // Binary clause {sign, other} — check subsumption/strengthening
                        self.stats.checks += 1;
                        self.round_checks += 1;
                        let sign_marked = self.marked(sign);
                        if tmp > 0 {
                            if sign_marked > 0 {
                                flipped = i32::MIN; // both same polarity: subsumption
                            } else if sign_marked < 0 {
                                // sign is opposite polarity → strengthening (+1 offset)
                                // flipped encodes the D literal with opposite polarity
                                flipped = (sign.0 as i32) + 1;
                            } else {
                                continue; // sign not in candidate
                            }
                        } else {
                            // other is opposite polarity (+1 offset)
                            if sign_marked > 0 {
                                flipped = (bin.other.0 as i32) + 1;
                            } else {
                                continue; // tautological resolvent or sign not in candidate
                            }
                        }

                        found_d = Some(bin.clause_idx);
                        break 'outer;
                    }
                }

                // Then check longer clauses via one-watch occurrence lists
                if sign_idx < self.occs.len() {
                    for oi in 0..self.occs[sign_idx].len() {
                        let d_idx = self.occs[sign_idx][oi];
                        if d_idx == c_idx {
                            continue;
                        }
                        if d_idx >= clauses.len()
                            || !clauses.is_active(d_idx)
                            || clauses.is_dead(d_idx)
                        {
                            continue;
                        }
                        let d_lits = clauses.literals(d_idx);
                        if d_lits.len() > c_lits.len() {
                            continue; // D must be <= C in size to subsume C
                        }
                        // 64-bit signature pre-filter: skip D if its variables
                        // are not a subset of C's variables. This avoids the
                        // O(|D|) literal-by-literal subsume_check when the
                        // bloom filter proves non-containment.
                        let d_sig = clauses.signature(d_idx);
                        if !clause_signature_vars_subset(d_sig, c_sig) {
                            continue;
                        }
                        let check = self.subsume_check(d_lits);
                        if check != 0 {
                            flipped = check;
                            found_d = Some(d_idx);
                            break 'outer;
                        }
                    }
                }
            }
        }

        self.unmark_clause(c_lits);

        // Post-condition: marks clean
        debug_assert!(
            c_lits.iter().all(|lit| {
                let v = lit.variable().index();
                v >= self.marks.len() || self.marks[v] == 0
            }),
            "BUG: marks not cleaned after try_to_subsume_clause"
        );

        (found_d, flipped)
    }
}
