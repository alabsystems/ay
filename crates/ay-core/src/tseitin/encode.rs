// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tseitin encoding of Boolean operators: AND, OR, EQ, XOR, ITE.

use super::{CnfClause, CnfLit, Tseitin};
use crate::proof::AletheRule;
use crate::term::{Constant, Symbol, TermData, TermId};
use crate::Sort;

impl Tseitin<'_> {
    pub(super) fn encode_inner(&mut self, term_id: TermId, positive: bool) -> CnfLit {
        match self.terms.get(term_id) {
            TermData::Const(Constant::Bool(true)) => {
                // True is a term-backed var forced true. Register var->term
                // (get_var) and annotate the unit with the strict-validated `true`
                // tautology so SAT-proof reconstruction can name it instead of
                // dropping it -> NoUsableHints -> Trust fallback (#verification-route).
                let var = self.get_var(term_id) as i32;
                self.add_clause_with_proof(CnfClause::unit(var), AletheRule::True, term_id);
                if positive {
                    var
                } else {
                    Self::negate(var)
                }
            }
            TermData::Const(Constant::Bool(false)) => {
                // False is a term-backed var forced false. Register var->term and
                // annotate the unit with the strict-validated `false` tautology
                // ([(not false)] is a 0-var tautology) (#verification-route).
                let var = self.get_var(term_id) as i32;
                self.add_clause_with_proof(
                    CnfClause::unit(Self::negate(var)),
                    AletheRule::False,
                    term_id,
                );
                if positive {
                    var
                } else {
                    Self::negate(var)
                }
            }
            TermData::Const(_) => {
                // Non-boolean constants shouldn't appear at Boolean positions
                // Create a variable for theory reasoning
                self.get_literal(term_id, positive)
            }
            TermData::Var(_, _) => {
                // Variables get direct CNF variables
                self.get_literal(term_id, positive)
            }
            TermData::Not(inner) => {
                // not(x) just flips the polarity
                self.encode(*inner, !positive)
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.encode_ite(term_id, *cond, *then_term, *else_term, positive)
            }
            TermData::App(symbol, args) => self.encode_app(term_id, symbol, args, positive),
            TermData::Let(_, _) => {
                // Let bindings should be expanded before Tseitin.
                // If one survives, treat it as an opaque literal rather than crashing.
                self.get_literal(term_id, positive)
            }
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {
                // Quantifiers are treated as opaque theory literals
                // E-matching handles instantiation before we reach this point
                self.get_literal(term_id, positive)
            }
        }
    }

    fn encode_ite(
        &mut self,
        term_id: TermId,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
        positive: bool,
    ) -> CnfLit {
        // Full ITE encoding: v ↔ ite(c, t, e)
        //
        // This is 4 clauses:
        // - v -> ite: (¬v ∨ ¬c ∨ t) ∧ (¬v ∨ c ∨ e)
        // - ite -> v: (¬c ∨ ¬t ∨ v) ∧ (c ∨ ¬e ∨ v)
        //
        // Polarity-aware partial encoding is UNSOUND when the ITE term can be forced
        // false by surrounding constraints (e.g., Boolean equality), because it allows
        // v=false without enforcing ite(c,t,e)=false. This manifested as SAT on UNSAT
        // models in #919 (and model-checker-consumer-derived queries).

        let v = self.get_var(term_id) as i32;

        let c_lit = self.encode(cond, true);
        let t_lit = self.encode(then_term, true);
        let e_lit = self.encode(else_term, true);

        // v -> ite(c, t, e): ite_pos2 and ite_pos1
        self.add_clause_with_proof(
            CnfClause::ternary(Self::negate(c_lit), Self::negate(v), t_lit),
            AletheRule::ItePos2,
            term_id,
        );
        self.add_clause_with_proof(
            CnfClause::ternary(c_lit, Self::negate(v), e_lit),
            AletheRule::ItePos1,
            term_id,
        );

        // ite(c, t, e) -> v: ite_neg2 and ite_neg1
        self.add_clause_with_proof(
            CnfClause::ternary(Self::negate(c_lit), Self::negate(t_lit), v),
            AletheRule::IteNeg2,
            term_id,
        );
        self.add_clause_with_proof(
            CnfClause::ternary(c_lit, Self::negate(e_lit), v),
            AletheRule::IteNeg1,
            term_id,
        );

        // Since encoding is complete, cache both polarities so later encodes
        // don't duplicate clauses under the opposite polarity.
        self.encoded.insert((term_id, true), v);
        self.encoded.insert((term_id, false), Self::negate(v));

        if positive {
            v
        } else {
            Self::negate(v)
        }
    }

    fn encode_app(
        &mut self,
        term_id: TermId,
        symbol: &Symbol,
        args: &[TermId],
        positive: bool,
    ) -> CnfLit {
        match symbol.name() {
            "and" => self.encode_and(term_id, args, positive),
            "or" => self.encode_or(term_id, args, positive),
            "xor" => {
                if args.len() == 2 {
                    self.encode_xor(term_id, args[0], args[1], positive)
                } else {
                    self.get_literal(term_id, positive)
                }
            }
            "=" => {
                if args.len() == 2 {
                    self.encode_eq(term_id, args[0], args[1], positive)
                } else {
                    self.get_literal(term_id, positive)
                }
            }
            "distinct" => self.get_literal(term_id, positive),
            _ => {
                // Theory predicates - create a variable
                self.get_literal(term_id, positive)
            }
        }
    }

    fn encode_and(&mut self, term_id: TermId, args: &[TermId], positive: bool) -> CnfLit {
        if args.is_empty() {
            // empty (and) = true. Register var->term + strict and_neg annotation
            // ([(and)] is the degenerate n=0 and_neg tautology) (#verification-route).
            let var = self.get_var(term_id) as i32;
            self.add_clause_with_proof(CnfClause::unit(var), AletheRule::AndNeg, term_id);
            return if positive { var } else { Self::negate(var) };
        }

        if args.len() == 1 {
            return self.encode(args[0], positive);
        }

        // v ↔ (a1 ∧ a2 ∧ ... ∧ an)
        // v → (a1 ∧ a2 ∧ ... ∧ an): (¬v ∨ a1), (¬v ∨ a2), ..., (¬v ∨ an)
        // (a1 ∧ a2 ∧ ... ∧ an) → v: (¬a1 ∨ ¬a2 ∨ ... ∨ ¬an ∨ v)

        let v = self.get_var(term_id) as i32;

        let arg_lits: Vec<CnfLit> = args.iter().map(|&a| self.encode(a, true)).collect();

        // v → ai for each i: and_pos(i) tautology
        for (i, &a_lit) in arg_lits.iter().enumerate() {
            self.add_clause_with_proof(
                CnfClause::binary(Self::negate(v), a_lit),
                AletheRule::AndPos(i as u32),
                term_id,
            );
        }

        // (a1 ∧ ... ∧ an) → v: and_neg tautology
        let mut clause_lits: Vec<CnfLit> = arg_lits.iter().map(|&l| Self::negate(l)).collect();
        clause_lits.push(v);
        self.add_clause_with_proof(CnfClause::new(clause_lits), AletheRule::AndNeg, term_id);

        if positive {
            v
        } else {
            Self::negate(v)
        }
    }

    fn encode_or(&mut self, term_id: TermId, args: &[TermId], positive: bool) -> CnfLit {
        if args.is_empty() {
            // empty (or) = false. Register var->term + strict or_pos annotation
            // ([(not (or))] is the degenerate or_pos tautology) (#verification-route).
            let var = self.get_var(term_id) as i32;
            self.add_clause_with_proof(
                CnfClause::unit(Self::negate(var)),
                AletheRule::OrPos(0),
                term_id,
            );
            return if positive { var } else { Self::negate(var) };
        }

        if args.len() == 1 {
            return self.encode(args[0], positive);
        }

        // v ↔ (a1 ∨ a2 ∨ ... ∨ an)
        // v → (a1 ∨ a2 ∨ ... ∨ an): (¬v ∨ a1 ∨ a2 ∨ ... ∨ an)
        // (a1 ∨ a2 ∨ ... ∨ an) → v: (¬a1 ∨ v), (¬a2 ∨ v), ..., (¬an ∨ v)

        let v = self.get_var(term_id) as i32;

        let arg_lits: Vec<CnfLit> = args.iter().map(|&a| self.encode(a, true)).collect();

        // v → (a1 ∨ ... ∨ an): or_pos tautology
        let mut clause_lits = vec![Self::negate(v)];
        clause_lits.extend(arg_lits.iter().copied());
        self.add_clause_with_proof(CnfClause::new(clause_lits), AletheRule::OrPos(0), term_id);

        // ai → v for each i: or_neg(i) tautology
        for (i, &a_lit) in arg_lits.iter().enumerate() {
            self.add_clause_with_proof(
                CnfClause::binary(Self::negate(a_lit), v),
                AletheRule::OrNeg,
                term_id,
            );
            let _ = i; // index available for future OrNeg(i) if needed
        }

        if positive {
            v
        } else {
            Self::negate(v)
        }
    }

    fn encode_eq(&mut self, term_id: TermId, lhs: TermId, rhs: TermId, positive: bool) -> CnfLit {
        if matches!(self.terms.sort(lhs), Sort::Bool) {
            // Boolean equality: v ↔ (a ↔ b)
            // Since the clauses use both a and ¬a (and b and ¬b), we must encode
            // both arguments in BOTH polarities to ensure subterms like ITE get
            // their full bidirectional encoding. (#919)

            let v = self.get_var(term_id) as i32;

            let a_lit = self.encode(lhs, true);
            let _ = self.encode(lhs, false);
            let b_lit = self.encode(rhs, true);
            let _ = self.encode(rhs, false);

            // (¬v ∨ ¬a ∨ b): equiv_pos2
            self.add_clause_with_proof(
                CnfClause::ternary(Self::negate(v), Self::negate(a_lit), b_lit),
                AletheRule::EquivPos2,
                term_id,
            );
            // (¬v ∨ a ∨ ¬b): equiv_pos1
            self.add_clause_with_proof(
                CnfClause::ternary(Self::negate(v), a_lit, Self::negate(b_lit)),
                AletheRule::EquivPos1,
                term_id,
            );
            // (a ∨ b ∨ v): equiv_neg2
            self.add_clause_with_proof(
                CnfClause::ternary(a_lit, b_lit, v),
                AletheRule::EquivNeg2,
                term_id,
            );
            // (¬a ∨ ¬b ∨ v): equiv_neg1
            self.add_clause_with_proof(
                CnfClause::ternary(Self::negate(a_lit), Self::negate(b_lit), v),
                AletheRule::EquivNeg1,
                term_id,
            );

            if positive {
                v
            } else {
                Self::negate(v)
            }
        } else {
            // Theory equality - create a variable
            self.get_literal(term_id, positive)
        }
    }

    fn encode_xor(&mut self, term_id: TermId, lhs: TermId, rhs: TermId, positive: bool) -> CnfLit {
        // XOR: v ↔ (a ⊕ b)
        // Since the clauses use both a and ¬a (and b and ¬b), we must encode
        // both arguments in BOTH polarities to ensure subterms like ITE get
        // their full bidirectional encoding. (#919)

        let v = self.get_var(term_id) as i32;

        let a_lit = self.encode(lhs, true);
        let _ = self.encode(lhs, false);
        let b_lit = self.encode(rhs, true);
        let _ = self.encode(rhs, false);

        // (¬v ∨ a ∨ b): xor_pos1
        self.add_clause_with_proof(
            CnfClause::ternary(Self::negate(v), a_lit, b_lit),
            AletheRule::XorPos1,
            term_id,
        );
        // (¬v ∨ ¬a ∨ ¬b): xor_pos2
        self.add_clause_with_proof(
            CnfClause::ternary(Self::negate(v), Self::negate(a_lit), Self::negate(b_lit)),
            AletheRule::XorPos2,
            term_id,
        );
        // (¬a ∨ b ∨ v): xor_neg2
        self.add_clause_with_proof(
            CnfClause::ternary(Self::negate(a_lit), b_lit, v),
            AletheRule::XorNeg2,
            term_id,
        );
        // (a ∨ ¬b ∨ v): xor_neg1
        self.add_clause_with_proof(
            CnfClause::ternary(a_lit, Self::negate(b_lit), v),
            AletheRule::XorNeg1,
            term_id,
        );

        if positive {
            v
        } else {
            Self::negate(v)
        }
    }
}
