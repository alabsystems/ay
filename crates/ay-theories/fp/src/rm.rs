// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rounding modes in the bit-blasted encoding.
//!
//! A rounding-mode operand is either a literal mode, for which every circuit
//! is built exactly as before, or a SYMBOLIC mode, carried as three bits the
//! way z3's `fpa2bv` carries it (`BV_RM_TIES_TO_EVEN` = 0, `..._TIES_TO_AWAY` =
//! 1, `..._TO_POSITIVE` = 2, `..._TO_NEGATIVE` = 3, `..._TO_ZERO` = 4). A
//! symbolic mode's bits are constrained to those five codes, and every
//! mode-dependent choice in a circuit (the rounding increment, the overflow
//! value, the sign of an exact zero) becomes a multiplexer over the five
//! one-hot mode predicates. One circuit therefore covers every mode, where the
//! lane used to solve the formula once per assignment of the modes (`5^k`
//! solves, `theories/fp/rm_expand.rs`, deleted with this encoding).
//!
//! Symbolic modes are declared constants and `ite`s over rounding modes. Any
//! other rounding-mode term (an application of a user function returning a
//! mode) is an encoding gap: the solve answers `unknown`, never a guess.

use ay_core::term::TermData;
use ay_core::{CnfClause, CnfLit, TermId};

use crate::construction::control::{uninterrupted, BuildControl};
use crate::rewriter::rounding_mode_literal;
use crate::{FpSolver, RoundingMode};

/// The five modes in code order: `RM_ORDER[c]` is the mode with code `c`.
pub const RM_ORDER: [RoundingMode; 5] = [
    RoundingMode::RNE,
    RoundingMode::RNA,
    RoundingMode::RTP,
    RoundingMode::RTN,
    RoundingMode::RTZ,
];

fn code(mode: RoundingMode) -> usize {
    match mode {
        RoundingMode::RNE => 0,
        RoundingMode::RNA => 1,
        RoundingMode::RTP => 2,
        RoundingMode::RTN => 3,
        RoundingMode::RTZ => 4,
    }
}

/// The three bits of a symbolic rounding mode (least significant first) and
/// the five one-hot predicates `mode == RM_ORDER[c]` derived from them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RmBits {
    bits: [CnfLit; 3],
    is_mode: [CnfLit; 5],
}

impl RmBits {
    /// The mode these bits denote under a SAT assignment, `None` if the
    /// assignment is incomplete or outside the five codes.
    pub fn decode(&self, value: impl Fn(CnfLit) -> Option<bool>) -> Option<RoundingMode> {
        let mut code = 0usize;
        for (i, &bit) in self.bits.iter().enumerate() {
            if value(bit)? {
                code |= 1 << i;
            }
        }
        RM_ORDER.get(code).copied()
    }

    /// The bits, least significant first.
    pub fn bits(&self) -> [CnfLit; 3] {
        self.bits
    }
}

/// A rounding-mode operand of an FP circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RmOperand {
    /// A literal mode: circuits are specialized to it.
    Literal(RoundingMode),
    /// A symbolic mode: circuits multiplex over its bits.
    Symbolic(RmBits),
}

impl From<RoundingMode> for RmOperand {
    fn from(mode: RoundingMode) -> Self {
        Self::Literal(mode)
    }
}

impl FpSolver<'_> {
    /// The literal `mode == m` for an operand.
    pub(crate) fn rm_is(&mut self, rm: RmOperand, m: RoundingMode) -> CnfLit {
        match rm {
            RmOperand::Literal(mode) => self.const_bool(mode == m),
            RmOperand::Symbolic(bits) => bits.is_mode[code(m)],
        }
    }

    fn const_bool(&mut self, value: bool) -> CnfLit {
        if value {
            self.const_true()
        } else {
            self.const_false()
        }
    }

    fn rm_code_bits(&mut self, rm: RmOperand) -> [CnfLit; 3] {
        match rm {
            RmOperand::Literal(mode) => {
                let c = code(mode);
                [0, 1, 2].map(|i| self.const_bool((c >> i) & 1 == 1))
            }
            RmOperand::Symbolic(bits) => bits.bits,
        }
    }

    /// The literal `a == b` over two rounding-mode operands.
    pub(crate) fn rm_equal(&mut self, a: RmOperand, b: RmOperand) -> CnfLit {
        if let (RmOperand::Literal(x), RmOperand::Literal(y)) = (a, b) {
            return self.const_bool(x == y);
        }
        let (a, b) = (self.rm_code_bits(a), self.rm_code_bits(b));
        self.make_bits_equal(&a, &b)
    }

    /// Mode predicates for three bits already confined to the five codes.
    fn rm_predicates(&mut self, bits: [CnfLit; 3]) -> RmBits {
        let [b0, b1, b2] = bits;
        let low_clear = self.make_and(-b2, -b1);
        let low_set = self.make_and(-b2, b1);
        let is_mode = [
            self.make_and(low_clear, -b0),
            self.make_and(low_clear, b0),
            self.make_and(low_set, -b0),
            self.make_and(low_set, b0),
            b2,
        ];
        RmBits { bits, is_mode }
    }

    /// Three fresh bits confined to the five codes: codes 5, 6 and 7 all have
    /// bit 2 set together with bit 0 or bit 1.
    fn fresh_rm_bits(&mut self) -> RmBits {
        let bits = [self.fresh_var(), self.fresh_var(), self.fresh_var()];
        self.add_clause(CnfClause::new(vec![-bits[2], -bits[1]]));
        self.add_clause(CnfClause::new(vec![-bits[2], -bits[0]]));
        self.rm_predicates(bits)
    }

    /// The operand for a rounding-mode term: a literal, a declared constant's
    /// bits (one set per term, so every occurrence is the same mode), or an
    /// `ite` multiplexing its branches' bits.
    pub(crate) fn rounding_operand_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<RmOperand, C::Error> {
        if let Some(mode) = rounding_mode_literal(self.terms, term) {
            return Ok(RmOperand::Literal(mode));
        }
        if let Some(&bits) = self.rm_terms.get(&term) {
            return Ok(RmOperand::Symbolic(bits));
        }
        if !crate::rewriter::is_rounding_mode_sort(self.terms.sort(term)) {
            self.has_encoding_gap = true;
            let bits = self.fresh_rm_bits();
            self.rm_terms.insert(term, bits);
            return Ok(RmOperand::Symbolic(bits));
        }
        let bits = match self.terms.get(term).clone() {
            TermData::Var(..) => self.fresh_rm_bits(),
            TermData::Ite(c, t, e) => self.rm_ite_with_control(c, t, e, control)?,
            TermData::App(sym, args)
                if args.is_empty() && self.terms.is_declared_function(sym.name()) =>
            {
                self.fresh_rm_bits()
            }
            TermData::App(ay_core::Symbol::Named(name), args)
                if name == "ite" && args.len() == 3 && !self.terms.is_declared_function(&name) =>
            {
                self.rm_ite_with_control(args[0], args[1], args[2], control)?
            }
            _ => {
                tracing::warn!(?term, "rounding-mode term is neither a constant nor an ite");
                self.has_encoding_gap = true;
                self.fresh_rm_bits()
            }
        };
        self.rm_terms.insert(term, bits);
        Ok(RmOperand::Symbolic(bits))
    }

    fn rm_ite_with_control<C: BuildControl>(
        &mut self,
        cond: TermId,
        then_term: TermId,
        else_term: TermId,
        control: &mut C,
    ) -> Result<RmBits, C::Error> {
        let c = self.encode_bool_condition_with_control(cond, control)?;
        let then_rm = self.rounding_operand_with_control(then_term, control)?;
        let else_rm = self.rounding_operand_with_control(else_term, control)?;
        let (t, e) = (self.rm_code_bits(then_rm), self.rm_code_bits(else_rm));
        let bits = [0, 1, 2].map(|i| self.make_ite(c, t[i], e[i]));
        Ok(self.rm_predicates(bits))
    }

    /// `OR over modes m of (mode == m AND choice(m))`: a mode-dependent bit,
    /// built once per mode. A literal mode builds only its own choice.
    pub(crate) fn rm_select(
        &mut self,
        rm: RmOperand,
        mut choice: impl FnMut(&mut Self, RoundingMode) -> CnfLit,
    ) -> CnfLit {
        match rm {
            RmOperand::Literal(mode) => choice(self, mode),
            RmOperand::Symbolic(bits) => {
                let mut result = self.const_false();
                for (i, mode) in RM_ORDER.into_iter().enumerate() {
                    let when = choice(self, mode);
                    let term = self.make_and(bits.is_mode[i], when);
                    result = self.make_or(result, term);
                }
                result
            }
        }
    }

    /// Bit-blast `(= x y)` over two rounding-mode terms.
    pub fn bitblast_rm_eq(&mut self, x: TermId, y: TermId) -> CnfLit {
        uninterrupted(|control| self.bitblast_rm_eq_with_control(x, y, control))
    }

    pub(crate) fn bitblast_rm_eq_with_control<C: BuildControl>(
        &mut self,
        x: TermId,
        y: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        let a = self.rounding_operand_with_control(x, control)?;
        let b = self.rounding_operand_with_control(y, control)?;
        Ok(self.rm_equal(a, b))
    }

    /// The rounding-mode terms given bits so far, with their bits.
    pub fn rm_terms(&self) -> &ay_core::kani_compat::DetHashMap<TermId, RmBits> {
        &self.rm_terms
    }
}

#[cfg(test)]
mod tests;
