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
        self.process_assertion(term, true);
    }

    /// Bit-blast multiple assertions and return CNF.
    ///
    /// This is the main entry point for eager bit-blasting. It processes
    /// all assertions and returns the resulting CNF clauses.
    ///
    /// When an interrupt flag is set via [`BvSolver::set_interrupt`], the loop
    /// checks for interruption every 64 assertions (#8609). If interrupted,
    /// returns the clauses generated so far (partial result). The caller
    /// should check [`BvSolver::is_interrupted`] after this returns to detect
    /// early termination and return `Unknown`.
    ///
    /// The same 64-assertion cadence also polls the process memory ceiling via
    /// [`ay_sys::process_memory_exceeded`]. Eager bit-blasting of a formula over
    /// a byte-addressed `(Array BV64 BV8)` heap can balloon to hundreds of
    /// thousands of CNF variables — enough to blow the `-memory` budget and get
    /// the process OOM-killed mid-blast (a documented worse-than-hang failure).
    /// Breaking out here lets the caller surface a graceful `Unknown` instead.
    /// Like the interrupt path this only ever yields `Unknown` (a partial CNF
    /// is never reported as SAT/UNSAT), so it is sound by the same argument the
    /// codebase already makes for the process-memory ceiling.
    pub fn bitblast_all(&mut self, assertions: &[TermId]) -> Vec<CnfClause> {
        for (i, &term) in assertions.iter().enumerate() {
            // Cooperative interrupt / memory check every 64 assertions (#8609).
            // BV bitblasting can process thousands of assertions for complex
            // formulas. Without this check, set_timeout() and interrupt() are
            // not respected until the entire bitblasting phase completes, and a
            // memory-exploding eager blast OOM-kills the process before any
            // ceiling is observed.
            if i & 63 == 63 && (self.is_interrupted() || ay_sys::process_memory_exceeded()) {
                break;
            }
            self.bitblast_assertion(term);
        }

        self.take_clauses()
    }

    /// Bit-blast a BV predicate term and return its CNF variable
    ///
    /// This is used to connect Tseitin variables to BV bitblast results (#858).
    /// Unlike `bitblast_assertion`, this does NOT add a unit clause asserting
    /// the predicate - it just returns the CNF variable representing it.
    ///
    /// Returns `Some(lit)` for BV predicates (equality, comparisons), `None` otherwise.
    pub fn bitblast_predicate(&mut self, term: TermId) -> Option<CnfLit> {
        // Check cache first
        if let Some(&lit) = self.predicate_to_var.get(&term) {
            return Some(lit);
        }

        let data = self.terms.get(term).clone();

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
                            let a = self.get_bits(args[0]);
                            let b = self.get_bits(args[1]);
                            Some(self.bitblast_eq(&a, &b))
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

        // Cache the result
        if let Some(lit) = result {
            self.predicate_to_var.insert(term, lit);
        }

        result
    }

    /// Process an assertion.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(crate) fn process_assertion(&mut self, term: TermId, value: bool) {
        stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, || {
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
                    self.add_clause(CnfClause::unit(if value { ite_lit } else { -ite_lit }));
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
                    self.add_clause(CnfClause::unit(-lit));
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
                        self.add_clause(CnfClause::unit(if value { lit } else { -lit }));
                    }
                }
                _ => {}
            }
        }) // stacker::maybe_grow
    }
}
