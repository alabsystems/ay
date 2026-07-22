// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! FP encoding and SAT bit-blasting for predicate linking.

use ay_core::term::TermData;
use ay_core::{CnfClause, Sort, TermId, Tseitin};
use ay_fp::FpSolver;

use crate::executor_types::Result;

use super::super::super::Executor;
use super::support::FpPredicateResult;
use super::to_real::{build_lra_model_from_fp_to_real, offset_cnf_lit, FpEncoding, FpToRealSite};

impl Executor {
    /// Encode FP assertions via Tseitin + bit-blasting, forcing decomposition
    /// of FP terms that appear in fp.to_real sites.
    ///
    /// Returns the base CNF clauses, metadata for model extraction, and the
    /// total variable count.
    pub(super) fn encode_fp_assertions(
        &mut self,
        fp_assertions: &[TermId],
        sites: &[FpToRealSite],
    ) -> Result<FpEncoding> {
        let mut tseitin = Tseitin::new(&self.ctx.terms);
        for &assertion in fp_assertions {
            tseitin.assert_term(assertion);
        }
        let tseitin_result = ay_core::TseitinResult::new(
            tseitin.all_clauses().to_vec(),
            tseitin.term_to_var().clone(),
            tseitin.var_to_term().clone(),
            0,
            tseitin.num_vars(),
        );

        let mut fp_solver = FpSolver::new_with_tseitin(&self.ctx.terms, tseitin.term_to_var());

        // Force decomposition of FP terms that appear only under fp.to_real (#6241).
        // Without this, these terms wouldn't be in term_to_fp, making model
        // extraction and blocking clauses impossible.
        for site in sites {
            if matches!(self.ctx.terms.sort(site.arg), Sort::FloatingPoint(..)) {
                fp_solver.get_fp(site.arg);
            }
        }

        let mut linking_pairs: Vec<(i32, i32)> = Vec::new();
        for (&tseitin_var, &term) in &tseitin_result.var_to_term {
            match self.bitblast_fp_predicate(&mut fp_solver, term) {
                FpPredicateResult::Bitblasted(fp_lit) => {
                    linking_pairs.push((tseitin_var as i32, fp_lit));
                }
                FpPredicateResult::NotFpPredicate => {}
                FpPredicateResult::Unsupported => {
                    let term_to_fp = fp_solver.term_to_fp().clone();
                    return Ok(FpEncoding {
                        base_clauses: Vec::new(),
                        tseitin_result,
                        term_to_fp,
                        var_offset: 0,
                        total_vars: 0,
                    });
                }
            }
        }

        if fp_solver.has_encoding_gap() {
            tracing::warn!("FP encoding has unresolvable ITE condition — returning Unknown");
            let term_to_fp = fp_solver.term_to_fp().clone();
            return Ok(FpEncoding {
                base_clauses: Vec::new(),
                tseitin_result,
                term_to_fp,
                var_offset: 0,
                total_vars: 0,
            });
        }

        let fp_clauses = fp_solver.take_clauses();
        let condition_links = fp_solver.take_pending_condition_links();
        let fp_num_vars = fp_solver.num_vars();
        let var_offset = tseitin_result.num_vars as i32;
        let term_to_fp = fp_solver.term_to_fp().clone();

        let mut base_clauses = tseitin_result.clauses.clone();
        for clause in fp_clauses {
            let offset_lits: Vec<i32> = clause
                .literals()
                .iter()
                .map(|&lit| offset_cnf_lit(lit, var_offset))
                .collect();
            base_clauses.push(CnfClause::new(offset_lits));
        }
        for (tseitin_lit, fp_lit) in linking_pairs {
            let fp_lit_offset = offset_cnf_lit(fp_lit, var_offset);
            base_clauses.push(CnfClause::binary(-tseitin_lit, fp_lit_offset));
            base_clauses.push(CnfClause::binary(tseitin_lit, -fp_lit_offset));
        }
        for (fp_var, tseitin_var) in condition_links {
            let fp_lit_offset = offset_cnf_lit(fp_var as i32, var_offset);
            let tseitin_lit = tseitin_var as i32;
            base_clauses.push(CnfClause::binary(-tseitin_lit, fp_lit_offset));
            base_clauses.push(CnfClause::binary(tseitin_lit, -fp_lit_offset));
        }

        let total_vars = (tseitin_result.num_vars + fp_num_vars) as usize;

        Ok(FpEncoding {
            base_clauses,
            tseitin_result,
            term_to_fp,
            var_offset,
            total_vars,
        })
    }

    /// Simple one-shot encode+solve for fp.to_real when no sites are found.
    pub(super) fn encode_and_solve_fp_simple(
        &mut self,
        fp_assertions: &[TermId],
        mixed_assertions: &[TermId],
    ) -> Result<crate::executor_types::SolveResult> {
        let encoding = self.encode_fp_assertions(fp_assertions, &[])?;
        let FpEncoding {
            base_clauses,
            tseitin_result,
            term_to_fp,
            var_offset,
            total_vars,
        } = encoding;

        if base_clauses.is_empty() && total_vars == 0 {
            // Encoding failed (unsupported ops)
            return self.solve_and_store_model_full(
                ay_sat::SatResult::Unknown,
                &tseitin_result,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
            );
        }

        let mut solver = ay_sat::Solver::new(total_vars);
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        solver.set_congruence_enabled(false);
        if let Some(seed) = self.random_seed {
            solver.set_random_seed(seed);
        }
        for clause in &base_clauses {
            let lits: Vec<ay_sat::Literal> = clause
                .literals()
                .iter()
                .map(|&lit| crate::cnf_lit_to_sat(lit))
                .collect();
            solver.add_clause(lits);
        }

        let should_stop = self.make_should_stop();
        let result = solver.solve_interruptible(should_stop).into_inner();
        collect_sat_stats!(self, &solver);

        match result {
            ay_sat::SatResult::Sat(ref sat_model) => {
                let fp_model = Self::extract_fp_model_from_bits(
                    sat_model,
                    &term_to_fp,
                    var_offset,
                    &self.ctx.terms,
                );
                let lra_model =
                    build_lra_model_from_fp_to_real(&self.ctx.terms, &fp_model, mixed_assertions);
                let lra = if lra_model.values.is_empty() {
                    None
                } else {
                    Some(lra_model)
                };
                self.solve_and_store_model_full(
                    result,
                    &tseitin_result,
                    None,
                    None,
                    lra,
                    None,
                    None,
                    Some(fp_model),
                    None,
                    None,
                )
            }
            _ => self.solve_and_store_model_full(
                result,
                &tseitin_result,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
            ),
        }
    }

    /// Try to bitblast a term as an FP predicate.
    ///
    /// Returns `Bitblasted(cnf_lit)` if the term is a recognized FP predicate,
    /// `NotFpPredicate` for non-FP terms, or `Unsupported` for unrecognized
    /// `fp.*` predicates that would leave Tseitin variables free (#6189).
    pub(super) fn bitblast_fp_predicate(
        &self,
        fp_solver: &mut FpSolver<'_>,
        term: TermId,
    ) -> FpPredicateResult {
        match self.ctx.terms.get(term) {
            // Use sym.name() to match both Symbol::Named and Symbol::Indexed,
            // consistent with has_unsupported_fp_arithmetic (#3586).
            TermData::App(sym, args) => match sym.name() {
                // Comparison predicates
                "fp.eq" if args.len() == 2 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_fp_eq(args[0], args[1]))
                }
                "fp.lt" if args.len() == 2 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_fp_lt(args[0], args[1]))
                }
                "fp.leq" if args.len() == 2 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_fp_le(args[0], args[1]))
                }
                "fp.gt" if args.len() == 2 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_fp_gt(args[0], args[1]))
                }
                "fp.geq" if args.len() == 2 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_fp_ge(args[0], args[1]))
                }
                // Classification predicates
                "fp.isNaN" if args.len() == 1 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_is_nan(args[0]))
                }
                "fp.isInfinite" if args.len() == 1 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_is_infinite(args[0]))
                }
                "fp.isZero" if args.len() == 1 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_is_zero(args[0]))
                }
                "fp.isNormal" if args.len() == 1 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_is_normal(args[0]))
                }
                "fp.isSubnormal" if args.len() == 1 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_is_subnormal(args[0]))
                }
                "fp.isPositive" if args.len() == 1 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_is_positive(args[0]))
                }
                "fp.isNegative" if args.len() == 1 => {
                    FpPredicateResult::Bitblasted(fp_solver.bitblast_is_negative(args[0]))
                }
                // SMT-LIB structural equality on FP sort: (= x y) where x, y : FloatingPoint
                // Unlike fp.eq (IEEE 754 where NaN != NaN, +0 == -0), structural =
                // is reflexive (NaN = NaN is true) and distinguishes +0 from -0.
                "=" if args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), Sort::FloatingPoint(..)) =>
                {
                    FpPredicateResult::Bitblasted(
                        fp_solver.bitblast_fp_structural_eq(args[0], args[1]),
                    )
                }
                // BV equality: bit-blast in FP solver's variable space.
                // Handles both fp.to_ubv/fp.to_sbv results and BV variables
                // used in to_fp/to_fp_unsigned operations (#3586).
                "=" if args.len() == 2
                    && matches!(self.ctx.terms.sort(args[0]), Sort::BitVec(..)) =>
                {
                    match fp_solver.bitblast_bv_predicate(term) {
                        Some(lit) => FpPredicateResult::Bitblasted(lit),
                        None => FpPredicateResult::Unsupported,
                    }
                }
                // BV distinct may arrive here without being normalized to
                // `not (= ...)`. Link the binary case as negated BV equality,
                // and fail closed for unsupported BV distinct arities (#8870).
                "distinct"
                    if args
                        .iter()
                        .any(|&arg| matches!(self.ctx.terms.sort(arg), Sort::BitVec(..))) =>
                {
                    if args.len() == 2 {
                        match fp_solver.bitblast_bv_predicate(term) {
                            Some(lit) => FpPredicateResult::Bitblasted(lit),
                            None => FpPredicateResult::Unsupported,
                        }
                    } else {
                        FpPredicateResult::Unsupported
                    }
                }
                // BV ordering predicates that occur in QF_BVFP formulas must
                // be linked into the FP bit-blast namespace too. Otherwise the
                // Tseitin Boolean for e.g. `bvule` is unconstrained, allowing
                // false SAT models that violate BV guards (#8870).
                "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
                    if args.len() == 2
                        && matches!(self.ctx.terms.sort(args[0]), Sort::BitVec(..)) =>
                {
                    match fp_solver.bitblast_bv_predicate(term) {
                        Some(lit) => FpPredicateResult::Bitblasted(lit),
                        None => FpPredicateResult::Unsupported,
                    }
                }
                // FP arithmetic operations (fp.add, fp.mul, etc.) are not predicates —
                // they produce FP values, not booleans. They get Tseitin variables but
                // don't need linking clauses (their semantics are in the bit-blasted
                // sub-circuit of their consumer predicate).
                "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.sqrt" | "fp.fma"
                | "fp.roundToIntegral" | "fp.rem" | "fp.abs" | "fp.neg" | "fp.min" | "fp.max"
                | "fp.to_ubv" | "fp.to_sbv" | "fp.to_ieee_bv" | "to_fp" | "to_fp_unsigned" => {
                    FpPredicateResult::NotFpPredicate
                }
                // Unrecognized fp.* name — would leave Tseitin variable free (#6189)
                name if name.starts_with("fp.") => FpPredicateResult::Unsupported,
                _ => FpPredicateResult::NotFpPredicate,
            },
            _ => FpPredicateResult::NotFpPredicate,
        }
    }
}
