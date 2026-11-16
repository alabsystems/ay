// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assertion processing and predicate bitblasting for `BvSolver`.
//!
//! Entry points for processing BV assertions and converting BV predicates
//! (equality, comparisons) into CNF variables.

use super::*;

impl BvSolver<'_> {
    /// Bit-blast an assertion and add clauses
    ///
    /// This processes a single assertion term and generates CNF clauses
    /// for all BV constraints it contains. The assertion is assumed to be true.
    pub fn bitblast_assertion(&mut self, term: TermId) {
        if !self.encoding_complete() {
            return;
        }

        self.process_assertion(term, true);
    }

    /// Bit-blast multiple assertions and return CNF.
    ///
    /// This is the main entry point for eager bit-blasting. It processes
    /// all assertions and returns the resulting CNF clauses.
    ///
    /// Entry, word/row and bounded gate polls observe the original check.
    /// Any observed refusal is sticky and returns NO clauses. Callers must
    /// also require [`BvSolver::encoding_complete`] before result publication.
    pub fn bitblast_all(&mut self, assertions: &[TermId]) -> Vec<CnfClause> {
        if !self.encoding_complete() {
            self.clauses.clear();
            return Vec::new();
        }
        self.count_offset_equalities(assertions);
        for &term in assertions {
            if !self.encoding_complete() {
                self.clauses.clear();
                return Vec::new();
            }
            self.bitblast_assertion(term);
        }
        if !self.encoding_complete() {
            self.clauses.clear();
            return Vec::new();
        }
        self.take_clauses()
    }

    /// The first known raw-interrupt/process-memory cause observed by this
    /// encoding owner, including before or inside [`Self::bitblast_all`].
    /// Readings may since have cleared; the cause and refusal stay recorded.
    /// Opaque callbacks and other owner refusals have no `BlastCut` variant:
    /// `None` is NOT evidence of completion; check [`Self::encoding_complete`].
    pub fn blast_cut(&self) -> Option<BlastCut> {
        self.encoding.blast_cut()
    }

    /// Bit-blast a BV predicate term and return its CNF variable
    ///
    /// This is used to connect Tseitin variables to BV bitblast results (#858).
    /// Unlike `bitblast_assertion`, this does NOT add a unit clause asserting
    /// the predicate - it just returns the CNF variable representing it.
    ///
    /// Returns `Some(lit)` for BV predicates (equality, comparisons), `None` otherwise.
    pub fn bitblast_predicate(&mut self, term: TermId) -> Option<CnfLit> {
        if !self.encoding_complete() {
            return None;
        }

        // Check cache first
        if let Some(&lit) = self.predicate_to_var.get(&term) {
            return Some(lit);
        }

        let data = self.counted_term_data(term)?;

        let result = match data {
            TermData::App(ref sym, ref args) if args.len() == 2 => {
                let name = sym.name();
                match name {
                    "=" => {
                        // Equality between bitvectors — verify both operands
                        // have the same BitVec sort to prevent bitblast_eq
                        // assertion failure on width mismatch (#5602).
                        let a_sort = self.terms.sort(args[0]);
                        let b_sort = self.terms.sort(args[1]);
                        if matches!(a_sort, Sort::BitVec(_)) && a_sort == b_sort {
                            Some(self.bitblast_term_eq(args[0], args[1]))
                        } else {
                            None
                        }
                    }
                    // BV comparison predicates: verify both operands have the
                    // same BitVec sort before bitblasting. Without this guard,
                    // non-BV operands (or width-mismatched operands) cause
                    // assertion failures in bitblast_ult/bitblast_slt. (#5595)
                    "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
                    | "bvsge" => {
                        let a_sort = self.terms.sort(args[0]);
                        let b_sort = self.terms.sort(args[1]);
                        if !matches!(a_sort, Sort::BitVec(_)) || a_sort != b_sort {
                            return None;
                        }
                        let a = self.get_bits(args[0]);
                        let b = self.get_bits(args[1]);
                        match name {
                            "bvult" => Some(self.bitblast_ult(&a, &b)),
                            "bvule" => Some(self.bitblast_ule(&a, &b)),
                            "bvugt" => Some(self.bitblast_ult(&b, &a)),
                            "bvuge" => Some(self.bitblast_ule(&b, &a)),
                            "bvslt" => Some(self.bitblast_slt(&a, &b)),
                            "bvsle" => Some(self.bitblast_sle(&a, &b)),
                            "bvsgt" => Some(self.bitblast_slt(&b, &a)),
                            "bvsge" => Some(self.bitblast_sle(&b, &a)),
                            _ => unreachable!(),
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };

        if !self.encoding_complete() {
            return None;
        }
        // Cache the result
        if let Some(lit) = result {
            if !counted::memory::map(&mut self.predicate_to_var, &self.encoding) {
                return None;
            }
            self.predicate_to_var.insert(term, lit);
        }

        result
    }

    /// Process an assertion.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(crate) fn process_assertion(&mut self, term: TermId, value: bool) {
        stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, || {
            if !self.encoding_complete() {
                return;
            }
            let data = self.terms.get(term).clone();

            match data {
                TermData::Not(inner) => {
                    // Not negates the value
                    self.process_assertion(inner, !value);
                }
                TermData::Ite(_cond, _then_term, _else_term) => {
                    // Bool-sorted ITE: assert (ite c t e) = value
                    // This is equivalent to asserting:
                    //   (c ∧ t = value) ∨ (¬c ∧ e = value)
                    // We encode this by bitblasting the ITE to a CNF literal and asserting it.
                    // Use bitblast_bool on the term itself so the ITE is inserted into
                    // bool_to_var for potential Tseitin-BV connection.
                    let ite_lit = self.bitblast_bool(term);
                    self.add_clause(CnfClause::unit(if value {
                        ite_lit
                    } else {
                        neg_lit(ite_lit)
                    }));
                }
                TermData::App(ref sym, ref args) if sym.name() == "and" && value => {
                    // (and P1 P2 ... Pn) = true: recursively assert all Pi = true (#1536)
                    for &arg in args {
                        self.process_assertion(arg, true);
                    }
                }
                TermData::App(ref sym, _) if sym.name() == "and" && !value => {
                    // (and P1 P2 ... Pn) = false: convert to CNF via bitblast_bool (#1536)
                    let lit = self.bitblast_bool(term);
                    self.add_clause(CnfClause::unit(neg_lit(lit)));
                }
                TermData::App(ref sym, ref args) if sym.name() == "or" && !value => {
                    // (or P1 P2 ... Pn) = false: recursively assert all Pi = false (#1536)
                    for &arg in args {
                        self.process_assertion(arg, false);
                    }
                }
                TermData::App(ref sym, _) if sym.name() == "or" && value => {
                    // (or P1 P2 ... Pn) = true: convert to CNF via bitblast_bool (#1536)
                    let lit = self.bitblast_bool(term);
                    self.add_clause(CnfClause::unit(lit));
                }
                TermData::App(_, ref args) if args.len() == 2 => {
                    // Delegate to bitblast_predicate for all BV predicates (=, bvult,
                    // bvule, bvugt, bvuge, bvslt, bvsle, bvsgt, bvsge). It handles
                    // cache lookup/insertion and returns None for non-BV operations.
                    if let Some(lit) = self.bitblast_predicate(term) {
                        self.add_clause(CnfClause::unit(if value { lit } else { neg_lit(lit) }));
                    }
                }
                _ => {}
            }
        }) // stacker::maybe_grow
    }
}
