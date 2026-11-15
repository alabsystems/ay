// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fresh-only BV conditions: never a permission inherited from a cache.

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{CnfLit, Sort};
use num_bigint::Sign;

use crate::construction::control::BuildControl;
use crate::{FpBuildStage, FpSolver};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConditionNamespace {
    External,
    /// External Tseitin names into which the caller already seeded every
    /// hidden BV predicate it admits (`FpSolver::new_with_seeded_tseitin`).
    /// An unnamed hidden BV atom is one the caller refused, so it keeps the
    /// encoding gap rather than DR-47's fallback circuit.
    SeededExternal,
    ClosedData,
}

impl FpSolver<'_> {
    pub(crate) fn closed_bv_condition_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<Option<CnfLit>, C::Error> {
        if self.condition_namespace != ConditionNamespace::ClosedData
            || self.term_to_cnf.is_some()
            || !self.closed_bv_predicate(term)
        {
            return Ok(None);
        }
        // Complete typed validation precedes the legacy clones and bit cache.
        // Recursive FP ITEs call this same solver, never an independent proxy.
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = self.bitblast_bv_predicate_with_control(term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    fn closed_bv_predicate(&self, term: TermId) -> bool {
        if self.terms.entry_stamp(term).is_none() || self.terms.sort(term) != &Sort::Bool {
            return false;
        }
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return false;
        };
        if !matches!(
            name.as_ref(),
            "=" | "distinct"
                | "bvult"
                | "bvule"
                | "bvugt"
                | "bvuge"
                | "bvslt"
                | "bvsle"
                | "bvsgt"
                | "bvsge"
        ) || args.len() != 2
            || args.iter().any(|&id| self.terms.entry_stamp(id).is_none())
        {
            return false;
        }
        let Sort::BitVec(width) = self.terms.sort(args[0]) else {
            return false;
        };
        (1..=64).contains(&width.width)
            && self.terms.sort(args[0]) == self.terms.sort(args[1])
            && args
                .iter()
                .all(|&id| self.closed_bv_operand(id, width.width))
    }

    fn closed_bv_operand(&self, term: TermId, width: u32) -> bool {
        if self.closed_bv_leaf(term, width) {
            return true;
        }
        let TermData::App(Symbol::Indexed(name, indices), args) = self.terms.get(term) else {
            return false;
        };
        let ([high, low], [word]) = (indices.as_slice(), args.as_slice()) else {
            return false;
        };
        if name.as_ref() != "extract" || low > high || self.terms.entry_stamp(*word).is_none() {
            return false;
        }
        let Sort::BitVec(bits) = self.terms.sort(*word) else {
            return false;
        };
        matches!(bits.width, 32 | 64)
            && *high < bits.width
            && high - low + 1 == width
            && self.closed_bv_leaf(*word, bits.width)
    }

    fn closed_bv_leaf(&self, term: TermId, width: u32) -> bool {
        if self.terms.entry_stamp(term).is_none()
            || !(1..=64).contains(&width)
            || self.terms.sort(term) != &Sort::bitvec(width)
        {
            return false;
        }
        match self.terms.get(term) {
            TermData::Var(..) => true,
            TermData::Const(Constant::BitVec {
                value,
                width: declared,
            }) => {
                *declared == width
                    && value.sign() != Sign::Minus
                    && value.bits() <= u64::from(width)
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests;
