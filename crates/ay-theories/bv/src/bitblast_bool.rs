// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean term bitblasting for `BvSolver`.
//!
//! Handles translating Bool-sorted terms that appear *inside* BV terms
//! (e.g., as ITE conditions, equality operands) into single CNF literals.

use super::*;

impl BvSolver<'_> {
    /// Bit-blast a Bool term into a single CNF literal.
    ///
    /// Used for Boolean conditions appearing *inside* BV terms (e.g., `ite`).
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#4602).
    pub(crate) fn bitblast_bool(&mut self, term: TermId) -> CnfLit {
        stacker::maybe_grow(BV_STACK_RED_ZONE, BV_STACK_SIZE, || {
            if let Some(&lit) = self.bool_to_var.get(&term) {
                return lit;
            }

            let data = self.terms.get(term).clone();

            let lit = match data {
                TermData::Const(Constant::Bool(b)) => {
                    let v = self.fresh_var();
                    self.add_clause(CnfClause::unit(if b { v } else { -v }));
                    v
                }
                TermData::Not(inner) => -self.bitblast_bool(inner),
                TermData::Ite(c, t, e) => {
                    // Track condition for Tseitin-BV linking (#1708)
                    // Bool-sorted ITE conditions must also be linked, not just BV-sorted ITE conditions.
                    // Without this, the condition gets different SAT variables in Tseitin vs BV encoding.
                    self.bv_ite_conditions.insert(c);
                    let c_lit = self.bitblast_bool(c);
                    if debug_bool_ite() {
                        safe_eprintln!(
                            "[bool_ite] Bool ITE term {:?}: cond={:?} -> c_lit={}",
                            term,
                            c,
                            c_lit
                        );
                    }
                    let t_lit = self.bitblast_bool(t);
                    let e_lit = self.bitblast_bool(e);
                    self.mk_mux(t_lit, e_lit, c_lit)
                }
                TermData::App(sym, args) => {
                    if let Some(pred_lit) = self.bitblast_predicate(term) {
                        // NOTE: We rely on the common `self.bool_to_var.insert(term, lit)` at the
                        // end of this function so Tseitin-BV connection works.
                        pred_lit
                    } else {
                        match sym.name() {
                            "and" => {
                                let lits: Vec<CnfLit> =
                                    args.into_iter().map(|a| self.bitblast_bool(a)).collect();
                                self.mk_and_many(&lits)
                            }
                            "or" => {
                                let lits: Vec<CnfLit> =
                                    args.into_iter().map(|a| self.bitblast_bool(a)).collect();
                                self.mk_or_many(&lits)
                            }
                            "xor" => {
                                if args.is_empty() {
                                    // SMT-LIB: (xor) is false.
                                    let f = self.fresh_var();
                                    self.add_clause(CnfClause::unit(-f));
                                    f
                                } else {
                                    // n-ary XOR (left fold)
                                    let mut it = args.into_iter();
                                    let first = it.next().unwrap();
                                    let mut acc = self.bitblast_bool(first);
                                    for a in it {
                                        let next = self.bitblast_bool(a);
                                        acc = self.mk_xor(acc, next);
                                    }
                                    acc
                                }
                            }
                            "=" => {
                                if args.len() < 2 {
                                    // SMT-LIB: (=) and (= x) are true.
                                    let t = self.fresh_var();
                                    self.add_clause(CnfClause::unit(t));
                                    t
                                } else {
                                    let first_sort = self.terms.sort(args[0]);
                                    // Only handle well-sorted equality. Otherwise treat as opaque Bool.
                                    if !args.iter().all(|&t| self.terms.sort(t) == first_sort) {
                                        self.fresh_var()
                                    } else {
                                        match first_sort {
                                            Sort::Bool => {
                                                let first = self.bitblast_bool(args[0]);
                                                let mut eqs: Vec<CnfLit> =
                                                    Vec::with_capacity(args.len() - 1);
                                                for &t in args.iter().skip(1) {
                                                    let next = self.bitblast_bool(t);
                                                    eqs.push(self.mk_xnor(first, next));
                                                }
                                                self.mk_and_many(&eqs)
                                            }
                                            Sort::BitVec(_) => {
                                                let first = self.get_bits(args[0]);
                                                let mut eqs: Vec<CnfLit> =
                                                    Vec::with_capacity(args.len() - 1);
                                                for &t in args.iter().skip(1) {
                                                    let next = self.get_bits(t);
                                                    eqs.push(self.bitblast_eq(&first, &next));
                                                }
                                                self.mk_and_many(&eqs)
                                            }
                                            _ => self.fresh_var(),
                                        }
                                    }
                                }
                            }
                            "distinct" => {
                                if args.len() < 2 {
                                    // SMT-LIB: (distinct) and (distinct x) are true.
                                    let t = self.fresh_var();
                                    self.add_clause(CnfClause::unit(t));
                                    t
                                } else {
                                    let first_sort = self.terms.sort(args[0]);
                                    // Only handle well-sorted distinct. Otherwise treat as opaque Bool.
                                    if !args.iter().all(|&t| self.terms.sort(t) == first_sort) {
                                        self.fresh_var()
                                    } else {
                                        match first_sort {
                                            Sort::Bool => {
                                                let lits: Vec<CnfLit> = args
                                                    .into_iter()
                                                    .map(|a| self.bitblast_bool(a))
                                                    .collect();
                                                let mut pairwise = Vec::new();
                                                for i in 0..lits.len() {
                                                    for j in (i + 1)..lits.len() {
                                                        pairwise
                                                            .push(self.mk_xor(lits[i], lits[j]));
                                                    }
                                                }
                                                self.mk_and_many(&pairwise)
                                            }
                                            Sort::BitVec(_) => {
                                                let bits: Vec<BvBits> = args
                                                    .into_iter()
                                                    .map(|t| self.get_bits(t))
                                                    .collect();
                                                let mut pairwise = Vec::new();
                                                for i in 0..bits.len() {
                                                    for j in (i + 1)..bits.len() {
                                                        let eq =
                                                            self.bitblast_eq(&bits[i], &bits[j]);
                                                        pairwise.push(-eq);
                                                    }
                                                }
                                                self.mk_and_many(&pairwise)
                                            }
                                            _ => self.fresh_var(),
                                        }
                                    }
                                }
                            }
                            "=>" if args.len() == 2 => {
                                let a = self.bitblast_bool(args[0]);
                                let b = self.bitblast_bool(args[1]);
                                self.mk_or(-a, b)
                            }
                            _ => self.fresh_var(),
                        }
                    }
                }
                _ => self.fresh_var(),
            };

            self.bool_to_var.insert(term, lit);
            lit
        }) // stacker::maybe_grow
    }
}
