// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Boolean ITE conditions the outer Tseitin walk never reached.
//!
//! A condition that carries a Tseitin variable is linked to it before anything
//! here runs. What reaches these encoders is a predicate buried inside a
//! bitvector or floating-point value — `(ite (= ((_ extract 31 31) x) #b1) …)`
//! inside the operand of an `fp` constructor, which is how a Rust `i32 as f32`
//! cast is lowered — so it has no outer variable to link to. See DR-47 in
//! the development design notes.

use std::collections::BTreeMap;

use ay_core::term::{TermData, TermId, TermStore};
use ay_core::CnfLit;

use crate::closed_data::ConditionNamespace;
use crate::construction::control::BuildControl;
use crate::FpSolver;

impl<'a> FpSolver<'a> {
    /// Create an FP solver over a Tseitin map into which the caller already
    /// SEEDED every hidden BV predicate it admits as an ITE condition.
    ///
    /// Such a caller decides which hidden predicates may get a name: ay-dpll's
    /// `nested_bv_guards` seeds the ones reachable from the original roots and
    /// never one below a quantifier or `let` binder, whose operands mention
    /// bound variables. An unnamed hidden BV atom is therefore one the caller
    /// refused. It keeps the fail-closed encoding gap: DR-47's circuit would
    /// give a bound variable the bits of one free input and so strip the
    /// binder. Every named predicate is linked exactly as with
    /// [`Self::new_with_tseitin`].
    #[must_use]
    pub fn new_with_seeded_tseitin(terms: &'a TermStore, tseitin: &BTreeMap<TermId, u32>) -> Self {
        let mut solver = Self::new_with_tseitin(terms, tseitin);
        solver.condition_namespace = ConditionNamespace::SeededExternal;
        solver
    }
}

impl FpSolver<'_> {
    /// Encode a bitvector relational atom (`=`/`distinct`/`bvult`/… over BV
    /// operands) that is reachable only through a BV/FP value ITE.
    ///
    /// The atom becomes the exact comparator circuit over its operands' bits,
    /// built by [`Self::bitblast_bv_predicate_with_control`], the encoder that
    /// already serves top-level BV atoms on this route. The operands go through
    /// the one `bv_term_bits` cache that top-level BV atoms, `fp` constructors
    /// and `to_fp` arguments also use, so a BV input reached here and elsewhere
    /// is one set of bits: the returned literal is pinned by clauses to the
    /// atom's value under every assignment, which is all an ITE condition
    /// needs. An operand or arity the encoder declines keeps the fail-closed
    /// encoding gap, so no verdict is published from an unconstrained proxy.
    pub(super) fn encode_hidden_bv_condition_with_control<C: BuildControl>(
        &mut self,
        bool_term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        if let Some(lit) = self.bitblast_bv_predicate_with_control(bool_term, control)? {
            return Ok(lit);
        }
        tracing::warn!(
            ?bool_term,
            "ITE condition: BV atom with an unsupported operand — encoding gap"
        );
        self.has_encoding_gap = true;
        Ok(self.fresh_var())
    }

    pub(super) fn encode_bool_condition_gap(
        &mut self,
        bool_term: TermId,
        data: &TermData,
    ) -> CnfLit {
        tracing::warn!(
            ?bool_term,
            ?data,
            "ITE condition: unresolvable — encoding gap"
        );
        self.has_encoding_gap = true;
        self.fresh_var()
    }
}
