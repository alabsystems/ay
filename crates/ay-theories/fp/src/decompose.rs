// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP term decomposition into sign/exponent/significand bitvectors.

mod conditions;

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{CnfLit, Sort};

use crate::closed_data::ConditionNamespace;
use crate::construction::control::{uninterrupted, BuildControl};
use crate::construction::FpBuildStage;

use super::{FpDecomposed, FpPrecision, FpSolver};

impl FpSolver<'_> {
    /// Encode a Bool-sorted term as a CNF literal for use in FP/BV ITE
    /// conditions.
    ///
    /// If the term already carries a Tseitin variable (it appears as a boolean
    /// atom in the outer CNF), we LINK to it — the Tseitin CNF plus the FP
    /// predicate links then constrain it, so no re-encoding is needed. Otherwise
    /// the term is a boolean subformula that the outer Tseitin walk never
    /// reached (e.g. a connective buried inside a bitvector ITE condition); we
    /// bit-blast it directly here. Boolean connectives are gated recursively via
    /// standard Tseitin gate encodings — sound because a fresh proxy variable is
    /// pinned by clauses to the exact boolean function of its (also-encoded)
    /// children. Unrecognized shapes still fail closed via
    /// [`Self::encode_bool_condition_gap`] (sets `has_encoding_gap`, so the
    /// solver returns Unknown rather than a possibly-unsound SAT).
    #[cfg(test)]
    pub(crate) fn encode_bool_condition(&mut self, bool_term: TermId) -> CnfLit {
        uninterrupted(|control| self.encode_bool_condition_with_control(bool_term, control))
    }

    pub(crate) fn encode_bool_condition_with_control<C: BuildControl>(
        &mut self,
        bool_term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        if let Some(cond_lit) = self.linked_condition_lit_with_control(bool_term, control)? {
            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            return Ok(cond_lit);
        }
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = match self.terms.get(bool_term).clone() {
            TermData::Const(Constant::Bool(true)) => self.const_true(),
            TermData::Const(Constant::Bool(false)) => self.const_false(),
            TermData::App(sym, args) => {
                self.encode_bool_app_condition_with_control(bool_term, &sym, &args, control)?
            }
            TermData::Not(inner) => -self.encode_bool_condition_with_control(inner, control)?,
            TermData::Ite(cond, then_term, else_term) => {
                let cond_lit = self.encode_bool_condition_with_control(cond, control)?;
                let then_lit = self.encode_bool_condition_with_control(then_term, control)?;
                let else_lit = self.encode_bool_condition_with_control(else_term, control)?;
                self.make_ite(cond_lit, then_lit, else_lit)
            }
            // A free Boolean input occurring only below a theory atom, so the
            // outer Tseitin walk never assigned it a variable (the
            // `linked_condition_lit` probe above returned `None`). One cached
            // fresh variable per term keeps repeated occurrences correlated —
            // sound (unconstrained input) and complete, unlike the
            // fresh-per-call gap this replaces.
            TermData::Var(..) if matches!(self.terms.sort(bool_term), Sort::Bool) => {
                self.bool_input_lit_with_control(bool_term, control)?
            }
            data => self.encode_bool_condition_gap(bool_term, &data),
        };
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Consistent CNF literal for a free Boolean input term (see the
    /// `TermData::Var` arm of [`Self::encode_bool_condition_with_control`]).
    fn bool_input_lit_with_control<C: BuildControl>(
        &mut self,
        bool_term: TermId,
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        if let Some(&lit) = self.bool_input_lits.get(&bool_term) {
            return Ok(lit);
        }
        let lit = self.fresh_var();
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        self.bool_input_lits.insert(bool_term, lit);
        Ok(lit)
    }

    fn linked_condition_lit_with_control<C: BuildControl>(
        &mut self,
        bool_term: TermId,
        control: &mut C,
    ) -> Result<Option<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let Some(tseitin_var) = self
            .term_to_cnf
            .as_ref()
            .and_then(|mapping| mapping.get(&bool_term).copied())
        else {
            return Ok(None);
        };
        let fp_var = self.fresh_var();
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        self.pending_condition_links
            .push((fp_var as u32, tseitin_var));
        Ok(Some(fp_var))
    }

    fn encode_bool_app_condition_with_control<C: BuildControl>(
        &mut self,
        bool_term: TermId,
        sym: &Symbol,
        args: &[TermId],
        control: &mut C,
    ) -> Result<CnfLit, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        if let Some(lit) = self.closed_bv_condition_with_control(bool_term, control)? {
            return Ok(lit);
        }
        let result = match sym.name() {
            "fp.lt" if args.len() == 2 => {
                self.bitblast_fp_lt_with_control(args[0], args[1], control)?
            }
            "fp.leq" if args.len() == 2 => {
                self.bitblast_fp_le_with_control(args[0], args[1], control)?
            }
            "fp.eq" if args.len() == 2 => {
                self.bitblast_fp_eq_with_control(args[0], args[1], control)?
            }
            "fp.gt" if args.len() == 2 => {
                self.bitblast_fp_gt_with_control(args[0], args[1], control)?
            }
            "fp.geq" if args.len() == 2 => {
                self.bitblast_fp_ge_with_control(args[0], args[1], control)?
            }
            "fp.isNaN" if args.len() == 1 => self.bitblast_is_nan_with_control(args[0], control)?,
            "fp.isZero" if args.len() == 1 => {
                self.bitblast_is_zero_with_control(args[0], control)?
            }
            "fp.isInfinite" if args.len() == 1 => {
                self.bitblast_is_infinite_with_control(args[0], control)?
            }
            "fp.isNormal" if args.len() == 1 => {
                self.bitblast_is_normal_with_control(args[0], control)?
            }
            "fp.isSubnormal" if args.len() == 1 => {
                self.bitblast_is_subnormal_with_control(args[0], control)?
            }
            "fp.isPositive" if args.len() == 1 => {
                self.bitblast_is_positive_with_control(args[0], control)?
            }
            "fp.isNegative" if args.len() == 1 => {
                self.bitblast_is_negative_with_control(args[0], control)?
            }
            "=" if args.len() == 2
                && matches!(self.terms.sort(args[0]), Sort::FloatingPoint(..)) =>
            {
                self.bitblast_fp_structural_eq_with_control(args[0], args[1], control)?
            }
            "=" | "distinct"
                if args.len() == 2
                    && crate::rewriter::is_rounding_mode_sort(self.terms.sort(args[0])) =>
            {
                let equal = self.bitblast_rm_eq_with_control(args[0], args[1], control)?;
                if sym.name() == "=" {
                    equal
                } else {
                    -equal
                }
            }
            // Boolean connectives — a condition subformula the outer Tseitin
            // walk never reached (typically buried inside a BV/FP ITE). Gate
            // recursively; each child goes back through `encode_bool_condition_with_control`
            // (so children that DO have Tseitin vars are linked, not re-blasted).
            "and" => {
                let mut acc = self.const_true();
                for &arg in args {
                    let lit = self.encode_bool_condition_with_control(arg, control)?;
                    acc = self.make_and(acc, lit);
                }
                acc
            }
            "or" => {
                let mut acc = self.const_false();
                for &arg in args {
                    let lit = self.encode_bool_condition_with_control(arg, control)?;
                    acc = self.make_or(acc, lit);
                }
                acc
            }
            "xor" => {
                let mut acc = self.const_false();
                for &arg in args {
                    let lit = self.encode_bool_condition_with_control(arg, control)?;
                    acc = self.make_xor(acc, lit);
                }
                acc
            }
            // Right-associative chained implication: (=> a b c) = (=> a (=> b c)).
            "=>" if args.len() >= 2 => {
                let last = args[args.len() - 1];
                let mut acc = self.encode_bool_condition_with_control(last, control)?;
                for &arg in args[..args.len() - 1].iter().rev() {
                    let a = self.encode_bool_condition_with_control(arg, control)?;
                    acc = self.make_or(-a, acc);
                }
                acc
            }
            // Boolean iff / xor-of-two written as (= a b) / (distinct a b) on
            // Bool-sorted arguments.
            "=" if args.len() == 2 && matches!(self.terms.sort(args[0]), Sort::Bool) => {
                let a = self.encode_bool_condition_with_control(args[0], control)?;
                let b = self.encode_bool_condition_with_control(args[1], control)?;
                self.make_xnor(a, b)
            }
            "distinct" if args.len() == 2 && matches!(self.terms.sort(args[0]), Sort::Bool) => {
                let a = self.encode_bool_condition_with_control(args[0], control)?;
                let b = self.encode_bool_condition_with_control(args[1], control)?;
                self.make_xor(a, b)
            }
            // Name-form Boolean ITE (`App("ite", …)` — the elaborator's usual
            // representation; `TermData::Ite` is handled by the caller's match).
            "ite" if args.len() == 3 && matches!(self.terms.sort(bool_term), Sort::Bool) => {
                let cond = self.encode_bool_condition_with_control(args[0], control)?;
                let then_lit = self.encode_bool_condition_with_control(args[1], control)?;
                let else_lit = self.encode_bool_condition_with_control(args[2], control)?;
                self.make_ite(cond, then_lit, else_lit)
            }
            // Nullary Boolean constant symbol (a `declare-const b Bool` that
            // reaches here as a 0-ary application): same free-input treatment
            // as `TermData::Var` in `encode_bool_condition_with_control`.
            _ if args.is_empty() && matches!(self.terms.sort(bool_term), Sort::Bool) => {
                self.bool_input_lit_with_control(bool_term, control)?
            }
            // A BV relational atom reachable only through a BV/FP value ITE
            // has no Tseitin variable; encode its exact comparator over the
            // shared operand bits (`conditions.rs`, DR-47). A declined operand,
            // or a closed-DATA or caller-seeded namespace, keeps the gap.
            "=" | "distinct" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle"
            | "bvsgt" | "bvsge"
                if args.len() == 2
                    && matches!(self.terms.sort(args[0]), Sort::BitVec(..))
                    && self.condition_namespace == ConditionNamespace::External =>
            {
                self.encode_hidden_bv_condition_with_control(bool_term, control)?
            }
            _ => {
                tracing::warn!(
                    ?bool_term,
                    name = sym.name(),
                    "ITE condition: non-FP App not in Tseitin map — encoding gap"
                );
                self.has_encoding_gap = true;
                self.fresh_var()
            }
        };
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Get or create decomposed FP representation for a term.
    pub fn get_fp(&mut self, term: TermId) -> FpDecomposed {
        uninterrupted(|control| self.get_fp_with_control(term, control))
    }

    pub(crate) fn get_fp_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        if let Some(fp) = self.term_to_fp.get(&term) {
            let fp = fp.clone();
            control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
            return Ok(fp);
        }

        let fp = self.decompose_fp_with_control(term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        self.term_to_fp.insert(term, fp.clone());
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(fp)
    }

    /// Decompose an FP term into sign, exponent, and significand.
    fn decompose_fp_with_control<C: BuildControl>(
        &mut self,
        term: TermId,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let sort = self.terms.sort(term).clone();
        debug_assert!(
            matches!(sort, Sort::FloatingPoint(..)),
            "Expected FloatingPoint sort, got {sort:?}"
        );
        let Sort::FloatingPoint(eb, sb) = sort else {
            tracing::warn!(?term, ?sort, "decompose_fp called on non-FP sort");
            return self.decompose_operation_with_control(control, |solver| {
                solver.fresh_decomposed(FpPrecision::Float32)
            });
        };

        let precision = FpPrecision::from_eb_sb(eb, sb);
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let data = self.terms.get(term).clone();

        let result = match data {
            TermData::App(ref sym, ref args) => {
                self.decompose_fp_app_with_control(term, sym, args, precision, control)?
            }
            TermData::Ite(cond, then_term, else_term) => {
                let cond_lit = self.encode_bool_condition_with_control(cond, control)?;
                let then_fp = self.get_fp_with_control(then_term, control)?;
                let else_fp = self.get_fp_with_control(else_term, control)?;
                self.decompose_operation_with_control(control, |solver| {
                    solver.make_ite_fp(cond_lit, &then_fp, &else_fp, precision)
                })?
            }
            _ => {
                tracing::warn!(
                    ?term,
                    ?data,
                    "FP bit-blasting: non-App/non-Ite FP term, returning unconstrained variables"
                );
                self.decompose_operation_with_control(control, |solver| {
                    solver.fresh_decomposed(precision)
                })?
            }
        };
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }

    /// Bracket an operation whose internal gate loops are not yet cooperative.
    fn decompose_operation_with_control<C: BuildControl, T>(
        &mut self,
        control: &mut C,
        operation: impl FnOnce(&mut Self) -> T,
    ) -> Result<T, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = operation(self);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }

    /// Decompose a function application on FP.
    fn decompose_fp_app_with_control<C: BuildControl>(
        &mut self,
        _term: TermId,
        sym: &Symbol,
        args: &[TermId],
        precision: FpPrecision,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        let result = match sym.name() {
            "fp.zero" | "+zero" => self.decompose_operation_with_control(control, |solver| {
                solver.make_zero(precision, false)
            })?,
            "-zero" => self.decompose_operation_with_control(control, |solver| {
                solver.make_zero(precision, true)
            })?,
            "fp.inf" | "+oo" => self.decompose_operation_with_control(control, |solver| {
                solver.make_infinity(precision, false)
            })?,
            "-oo" => self.decompose_operation_with_control(control, |solver| {
                solver.make_infinity(precision, true)
            })?,
            "fp.nan" | "NaN" => self.decompose_operation_with_control(control, |solver| {
                solver.make_nan_value(precision)
            })?,
            "fp.neg" => {
                let x = self.get_fp_with_control(args[0], control)?;
                self.decompose_operation_with_control(control, |solver| solver.make_neg(&x))?
            }
            "fp.abs" => {
                let x = self.get_fp_with_control(args[0], control)?;
                self.decompose_operation_with_control(control, |solver| solver.make_abs(&x))?
            }
            "fp.add" => {
                let rm = self.rounding_operand_with_control(args[0], control)?;
                let x = self.get_fp_with_control(args[1], control)?;
                let y = self.get_fp_with_control(args[2], control)?;
                self.decompose_operation_with_control(control, |solver| {
                    solver.make_add(&x, &y, rm)
                })?
            }
            "fp.sub" => {
                let rm = self.rounding_operand_with_control(args[0], control)?;
                let x = self.get_fp_with_control(args[1], control)?;
                let y = self.get_fp_with_control(args[2], control)?;
                self.decompose_operation_with_control(control, |solver| {
                    solver.make_sub(&x, &y, rm)
                })?
            }
            "fp.mul" => {
                let rm = self.rounding_operand_with_control(args[0], control)?;
                let x = self.get_fp_with_control(args[1], control)?;
                let y = self.get_fp_with_control(args[2], control)?;
                self.make_mul_with_control(&x, &y, rm, control)?
            }
            "fp.div" => {
                let rm = self.rounding_operand_with_control(args[0], control)?;
                // Dividing by a constant power of two is exact scaling, so the
                // reciprocal multiply is the same value through a circuit an
                // order of magnitude smaller (#fp-div-pow2). The divider is
                // this bit-blaster's most expensive gate by a wide margin, so
                // this is checked before it is built, not after.
                if let Some(result) = self.try_make_div_by_power_of_two_with_control(
                    args[1], args[2], rm, precision, control,
                )? {
                    result
                } else {
                    let x = self.get_fp_with_control(args[1], control)?;
                    let y = self.get_fp_with_control(args[2], control)?;
                    self.make_div_with_control(&x, &y, rm, control)?
                }
            }
            "fp.sqrt" => {
                let rm = self.rounding_operand_with_control(args[0], control)?;
                let x = self.get_fp_with_control(args[1], control)?;
                self.make_sqrt_with_control(&x, rm, control)?
            }
            "fp.fma" => {
                let rm = self.rounding_operand_with_control(args[0], control)?;
                // Z3 PR #9038 / issue #8185: when one multiplicand is a
                // concrete FP zero, fall through to a reduced encoding that
                // avoids the expensive FMA bit-blast circuit.
                let z = self.get_fp_with_control(args[3], control)?;
                if let Some(result) =
                    self.try_make_fma_zero_factor_with_control(args[1], args[2], &z, rm, control)?
                {
                    result
                } else {
                    let x = self.get_fp_with_control(args[1], control)?;
                    let y = self.get_fp_with_control(args[2], control)?;
                    self.make_fma_with_control(&x, &y, &z, rm, control)?
                }
            }
            "fp.roundToIntegral" => {
                let rm = self.rounding_operand_with_control(args[0], control)?;
                let x = self.get_fp_with_control(args[1], control)?;
                self.decompose_operation_with_control(control, |solver| {
                    solver.make_round_to_integral(&x, rm)
                })?
            }
            "__ay_fp_truncating_rem" => {
                self.decompose_truncating_rem_with_control(sym, args, precision, control)?
            }
            "fp.rem" => {
                let x = self.get_fp_with_control(args[0], control)?;
                let y = self.get_fp_with_control(args[1], control)?;
                self.make_rem_with_control(&x, &y, control)?
            }
            "fp.min" => {
                let x = self.get_fp_with_control(args[0], control)?;
                let y = self.get_fp_with_control(args[1], control)?;
                self.decompose_operation_with_control(control, |solver| solver.make_min(&x, &y))?
            }
            "fp.max" => {
                let x = self.get_fp_with_control(args[0], control)?;
                let y = self.get_fp_with_control(args[1], control)?;
                self.decompose_operation_with_control(control, |solver| solver.make_max(&x, &y))?
            }
            // Name-form FP-sorted ITE (`App("ite", …)`); mirrors the
            // `TermData::Ite` arm of `decompose_fp`.
            "ite" if args.len() == 3 => {
                let cond_lit = self.encode_bool_condition_with_control(args[0], control)?;
                let then_fp = self.get_fp_with_control(args[1], control)?;
                let else_fp = self.get_fp_with_control(args[2], control)?;
                self.decompose_operation_with_control(control, |solver| {
                    solver.make_ite_fp(cond_lit, &then_fp, &else_fp, precision)
                })?
            }
            "fp" if args.len() == 3 => {
                self.decompose_fp_constructor_with_control(args, precision, control)?
            }
            "to_fp" => self.decompose_to_fp_with_control(args, precision, control)?,
            "to_fp_unsigned" => {
                self.decompose_to_fp_unsigned_with_control(args, precision, control)?
            }
            other => {
                tracing::warn!(
                    op = other,
                    "FP bit-blasting: unrecognized operation, returning unconstrained variables"
                );
                self.decompose_operation_with_control(control, |solver| {
                    solver.fresh_decomposed(precision)
                })?
            }
        };
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        Ok(result)
    }
}
