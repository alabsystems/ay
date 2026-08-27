// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP term decomposition into sign/exponent/significand bitvectors.

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{CnfLit, Sort};

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
    pub(crate) fn encode_bool_condition(&mut self, bool_term: TermId) -> CnfLit {
        if let Some(cond_lit) = self.linked_condition_lit(bool_term) {
            return cond_lit;
        }

        match self.terms.get(bool_term).clone() {
            TermData::Const(Constant::Bool(true)) => self.const_true(),
            TermData::Const(Constant::Bool(false)) => self.const_false(),
            TermData::App(sym, args) => self.encode_bool_app_condition(bool_term, &sym, &args),
            TermData::Not(inner) => -self.encode_bool_condition(inner),
            TermData::Ite(cond, then_term, else_term) => {
                let cond_lit = self.encode_bool_condition(cond);
                let then_lit = self.encode_bool_condition(then_term);
                let else_lit = self.encode_bool_condition(else_term);
                self.make_ite(cond_lit, then_lit, else_lit)
            }
            // A free Boolean input occurring only below a theory atom, so the
            // outer Tseitin walk never assigned it a variable (the
            // `linked_condition_lit` probe above returned `None`). One cached
            // fresh variable per term keeps repeated occurrences correlated —
            // sound (unconstrained input) and complete, unlike the
            // fresh-per-call gap this replaces.
            TermData::Var(..) if matches!(self.terms.sort(bool_term), Sort::Bool) => {
                self.bool_input_lit(bool_term)
            }
            data => self.encode_bool_condition_gap(bool_term, &data),
        }
    }

    /// Consistent CNF literal for a free Boolean input term (see the
    /// `TermData::Var` arm of [`Self::encode_bool_condition`]).
    fn bool_input_lit(&mut self, bool_term: TermId) -> CnfLit {
        if let Some(&lit) = self.bool_input_lits.get(&bool_term) {
            return lit;
        }
        let lit = self.fresh_var();
        self.bool_input_lits.insert(bool_term, lit);
        lit
    }

    fn linked_condition_lit(&mut self, bool_term: TermId) -> Option<CnfLit> {
        let tseitin_var = self.term_to_cnf.as_ref()?.get(&bool_term).copied()?;
        let fp_var = self.fresh_var();
        self.pending_condition_links
            .push((fp_var as u32, tseitin_var));
        Some(fp_var)
    }

    fn encode_bool_app_condition(
        &mut self,
        bool_term: TermId,
        sym: &Symbol,
        args: &[TermId],
    ) -> CnfLit {
        match sym.name() {
            "fp.lt" if args.len() == 2 => self.bitblast_fp_lt(args[0], args[1]),
            "fp.leq" if args.len() == 2 => self.bitblast_fp_le(args[0], args[1]),
            "fp.eq" if args.len() == 2 => self.bitblast_fp_eq(args[0], args[1]),
            "fp.gt" if args.len() == 2 => self.bitblast_fp_gt(args[0], args[1]),
            "fp.geq" if args.len() == 2 => self.bitblast_fp_ge(args[0], args[1]),
            "fp.isNaN" if args.len() == 1 => self.bitblast_is_nan(args[0]),
            "fp.isZero" if args.len() == 1 => self.bitblast_is_zero(args[0]),
            "fp.isInfinite" if args.len() == 1 => self.bitblast_is_infinite(args[0]),
            "fp.isNormal" if args.len() == 1 => self.bitblast_is_normal(args[0]),
            "fp.isSubnormal" if args.len() == 1 => self.bitblast_is_subnormal(args[0]),
            "fp.isPositive" if args.len() == 1 => self.bitblast_is_positive(args[0]),
            "fp.isNegative" if args.len() == 1 => self.bitblast_is_negative(args[0]),
            "=" if args.len() == 2
                && matches!(self.terms.sort(args[0]), Sort::FloatingPoint(..)) =>
            {
                self.bitblast_fp_structural_eq(args[0], args[1])
            }
            // Boolean connectives — a condition subformula the outer Tseitin
            // walk never reached (typically buried inside a BV/FP ITE). Gate
            // recursively; each child goes back through `encode_bool_condition`
            // (so children that DO have Tseitin vars are linked, not re-blasted).
            "and" => {
                let mut acc = self.const_true();
                for &arg in args {
                    let lit = self.encode_bool_condition(arg);
                    acc = self.make_and(acc, lit);
                }
                acc
            }
            "or" => {
                let mut acc = self.const_false();
                for &arg in args {
                    let lit = self.encode_bool_condition(arg);
                    acc = self.make_or(acc, lit);
                }
                acc
            }
            "xor" => {
                let mut acc = self.const_false();
                for &arg in args {
                    let lit = self.encode_bool_condition(arg);
                    acc = self.make_xor(acc, lit);
                }
                acc
            }
            // Right-associative chained implication: (=> a b c) = (=> a (=> b c)).
            "=>" if args.len() >= 2 => {
                let last = args[args.len() - 1];
                let mut acc = self.encode_bool_condition(last);
                for &arg in args[..args.len() - 1].iter().rev() {
                    let a = self.encode_bool_condition(arg);
                    acc = self.make_or(-a, acc);
                }
                acc
            }
            // Boolean iff / xor-of-two written as (= a b) / (distinct a b) on
            // Bool-sorted arguments.
            "=" if args.len() == 2 && matches!(self.terms.sort(args[0]), Sort::Bool) => {
                let a = self.encode_bool_condition(args[0]);
                let b = self.encode_bool_condition(args[1]);
                self.make_xnor(a, b)
            }
            "distinct" if args.len() == 2 && matches!(self.terms.sort(args[0]), Sort::Bool) => {
                let a = self.encode_bool_condition(args[0]);
                let b = self.encode_bool_condition(args[1]);
                self.make_xor(a, b)
            }
            // Name-form Boolean ITE (`App("ite", …)` — the elaborator's usual
            // representation; `TermData::Ite` is handled by the caller's match).
            "ite" if args.len() == 3 && matches!(self.terms.sort(bool_term), Sort::Bool) => {
                let cond = self.encode_bool_condition(args[0]);
                let then_lit = self.encode_bool_condition(args[1]);
                let else_lit = self.encode_bool_condition(args[2]);
                self.make_ite(cond, then_lit, else_lit)
            }
            // Nullary Boolean constant symbol (a `declare-const b Bool` that
            // reaches here as a 0-ary application): same free-input treatment
            // as `TermData::Var` in `encode_bool_condition`.
            _ if args.is_empty() && matches!(self.terms.sort(bool_term), Sort::Bool) => {
                self.bool_input_lit(bool_term)
            }
            // NOTE: bitvector relational atoms (bvult/bvugt/=/… on BV args) are
            // deliberately NOT handled here. When such a predicate appears only
            // inside an FP/BV ITE condition (not at the outer Bool level) it is
            // not linked into the outer SAT namespace, so we keep the #3586
            // conservative fail-closed (encoding gap → Unknown) rather than risk
            // an unlinked BV condition. FP predicates and boolean connectives
            // over them are fully linked and handled above.
            _ => {
                tracing::warn!(
                    ?bool_term,
                    name = sym.name(),
                    "ITE condition: non-FP App not in Tseitin map — encoding gap"
                );
                self.has_encoding_gap = true;
                self.fresh_var()
            }
        }
    }

    fn encode_bool_condition_gap(&mut self, bool_term: TermId, data: &TermData) -> CnfLit {
        tracing::warn!(
            ?bool_term,
            ?data,
            "ITE condition: unresolvable — encoding gap"
        );
        self.has_encoding_gap = true;
        self.fresh_var()
    }

    /// Get or create decomposed FP representation for a term.
    pub fn get_fp(&mut self, term: TermId) -> FpDecomposed {
        if let Some(fp) = self.term_to_fp.get(&term) {
            return fp.clone();
        }

        let fp = self.decompose_fp(term);
        self.term_to_fp.insert(term, fp.clone());
        fp
    }

    /// Decompose an FP term into sign, exponent, and significand.
    fn decompose_fp(&mut self, term: TermId) -> FpDecomposed {
        let sort = self.terms.sort(term).clone();
        debug_assert!(
            matches!(sort, Sort::FloatingPoint(..)),
            "Expected FloatingPoint sort, got {sort:?}"
        );
        let Sort::FloatingPoint(eb, sb) = sort else {
            tracing::warn!(?term, ?sort, "decompose_fp called on non-FP sort");
            return self.fresh_decomposed(FpPrecision::Float32);
        };

        let precision = FpPrecision::from_eb_sb(eb, sb);
        let data = self.terms.get(term).clone();

        match data {
            TermData::App(ref sym, ref args) => self.decompose_fp_app(term, sym, args, precision),
            TermData::Ite(cond, then_term, else_term) => {
                let cond_lit = self.encode_bool_condition(cond);
                let then_fp = self.get_fp(then_term);
                let else_fp = self.get_fp(else_term);
                self.make_ite_fp(cond_lit, &then_fp, &else_fp, precision)
            }
            _ => {
                tracing::warn!(
                    ?term,
                    ?data,
                    "FP bit-blasting: non-App/non-Ite FP term, returning unconstrained variables"
                );
                self.fresh_decomposed(precision)
            }
        }
    }

    /// Decompose a function application on FP.
    fn decompose_fp_app(
        &mut self,
        _term: TermId,
        sym: &Symbol,
        args: &[TermId],
        precision: FpPrecision,
    ) -> FpDecomposed {
        match sym.name() {
            "fp.zero" | "+zero" => self.make_zero(precision, false),
            "-zero" => self.make_zero(precision, true),
            "fp.inf" | "+oo" => self.make_infinity(precision, false),
            "-oo" => self.make_infinity(precision, true),
            "fp.nan" | "NaN" => self.make_nan_value(precision),
            "fp.neg" => {
                let x = self.get_fp(args[0]);
                self.make_neg(&x)
            }
            "fp.abs" => {
                let x = self.get_fp(args[0]);
                self.make_abs(&x)
            }
            "fp.add" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_add(&x, &y, rm)
            }
            "fp.sub" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_sub(&x, &y, rm)
            }
            "fp.mul" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_mul(&x, &y, rm)
            }
            "fp.div" => {
                let rm = self.get_rounding_mode(args[0]);
                // Dividing by a constant power of two is exact scaling, so the
                // reciprocal multiply is the same value through a circuit an
                // order of magnitude smaller (#fp-div-pow2). The divider is
                // this bit-blaster's most expensive gate by a wide margin, so
                // this is checked before it is built, not after.
                if let Some(result) =
                    self.try_make_div_by_power_of_two(args[1], args[2], rm, precision)
                {
                    return result;
                }
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_div(&x, &y, rm)
            }
            "fp.sqrt" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                self.make_sqrt(&x, rm)
            }
            "fp.fma" => {
                let rm = self.get_rounding_mode(args[0]);
                // Z3 PR #9038 / issue #8185: when one multiplicand is a
                // concrete FP zero, fall through to a reduced encoding that
                // avoids the expensive FMA bit-blast circuit.
                let z = self.get_fp(args[3]);
                if let Some(result) = self.try_make_fma_zero_factor(args[1], args[2], &z, rm) {
                    return result;
                }
                let x = self.get_fp(args[1]);
                let y = self.get_fp(args[2]);
                self.make_fma(&x, &y, &z, rm)
            }
            "fp.roundToIntegral" => {
                let rm = self.get_rounding_mode(args[0]);
                let x = self.get_fp(args[1]);
                self.make_round_to_integral(&x, rm)
            }
            "fp.rem" => {
                let x = self.get_fp(args[0]);
                let y = self.get_fp(args[1]);
                self.make_rem(&x, &y)
            }
            "fp.min" => {
                let x = self.get_fp(args[0]);
                let y = self.get_fp(args[1]);
                self.make_min(&x, &y)
            }
            "fp.max" => {
                let x = self.get_fp(args[0]);
                let y = self.get_fp(args[1]);
                self.make_max(&x, &y)
            }
            // Name-form FP-sorted ITE (`App("ite", …)`); mirrors the
            // `TermData::Ite` arm of `decompose_fp`.
            "ite" if args.len() == 3 => {
                let cond_lit = self.encode_bool_condition(args[0]);
                let then_fp = self.get_fp(args[1]);
                let else_fp = self.get_fp(args[2]);
                self.make_ite_fp(cond_lit, &then_fp, &else_fp, precision)
            }
            "fp" if args.len() == 3 => self.decompose_fp_constructor(args, precision),
            "to_fp" => self.decompose_to_fp(args, precision),
            "to_fp_unsigned" => self.decompose_to_fp_unsigned(args, precision),
            other => {
                tracing::warn!(
                    op = other,
                    "FP bit-blasting: unrecognized operation, returning unconstrained variables"
                );
                self.fresh_decomposed(precision)
            }
        }
    }
}
