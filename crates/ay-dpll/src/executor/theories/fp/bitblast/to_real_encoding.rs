// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete, disposable mixed encodings under their caller's original stop owner.

use ay_core::{CnfClause, Sort, TermId, Tseitin};
use ay_fp::{FpBuildError, FpConstruction, FpSolver};

use crate::executor::Executor;
use crate::executor_types::UnknownOrigin;

use super::super::congruence::{self, PlanLit};
use super::super::namespace::{validate_tseitin_namespace, FpNamespace};
use super::super::stop::FpStop;
use super::super::support::FpPredicateResult;
use super::super::to_real::{FpEncoding, FpToRealSite};
use super::super::to_real_solve::FpRealPhase;
use super::bitblast_fp_predicate_controlled;

#[derive(Debug, thiserror::Error)]
pub(in crate::executor::theories::fp) enum FpRealEncodingError {
    #[error("FP-to-Real encoding stopped: {0:?}")]
    Stopped(UnknownOrigin),
    #[error("unsupported FP predicate")]
    Unsupported,
    #[error("unresolved FP encoding condition")]
    EncodingGap,
}

impl From<UnknownOrigin> for FpRealEncodingError {
    fn from(origin: UnknownOrigin) -> Self {
        Self::Stopped(origin)
    }
}

fn checkpoint(
    stop: &FpStop,
    observe: &impl Fn(FpRealPhase),
    phase: FpRealPhase,
) -> Result<(), UnknownOrigin> {
    stop.check()?;
    observe(phase);
    stop.check()
}

fn append_clause(
    clauses: &mut Vec<CnfClause>,
    literals: impl IntoIterator<Item = i32>,
    stop: &FpStop,
    observe: &impl Fn(FpRealPhase),
) -> Result<(), UnknownOrigin> {
    checkpoint(stop, observe, FpRealPhase::ClauseTransfer)?;
    let mut copied = Vec::new();
    for (index, literal) in literals.into_iter().enumerate() {
        if index % 256 == 0 {
            stop.check()?;
        }
        copied.push(literal);
    }
    stop.check()?;
    clauses.push(CnfClause::new(copied));
    stop.check()
}

impl Executor {
    /// Preserve the mixed lane's exact clause order and semantic refusals.
    ///
    /// Individual Tseitin roots and opaque arithmetic remain bracketed work;
    /// recursive FP/BV construction, divider rows, congruence traversal and
    /// clause copies use the same sticky owner. No partial encoding escapes.
    pub(in crate::executor::theories::fp) fn encode_fp_assertions_controlled(
        &self,
        fp_assertions: &[TermId],
        sites: &[FpToRealSite],
        stop: &FpStop,
        observe: &impl Fn(FpRealPhase),
    ) -> Result<FpEncoding, FpRealEncodingError> {
        checkpoint(stop, observe, FpRealPhase::Tseitin)?;
        let terms = &self.ctx.terms;
        let mut tseitin = Tseitin::new(terms);
        for &assertion in fp_assertions {
            checkpoint(stop, observe, FpRealPhase::Tseitin)?;
            tseitin.assert_term(assertion);
            stop.check()?;
        }
        // Keep binder boundaries from the original mixed roots: the site
        // collector may find fp.to_real below a quantifier, so detached
        // site arguments cannot authorize fresh global predicate names.
        super::super::nested_bv_guards::seed(
            terms,
            fp_assertions
                .iter()
                .copied()
                .chain(self.ctx.assertions.iter().copied()),
            &mut tseitin,
            stop,
            &|| observe(FpRealPhase::Tseitin),
        )?;
        let tseitin_result = tseitin.into_assertion_result();
        validate_tseitin_namespace(tseitin_result.num_vars)
            .map_err(|_| stop.refuse_build_error(FpBuildError::VariableLimit))?;
        stop.check()?;
        let solver = FpSolver::new_with_seeded_tseitin(terms, &tseitin_result.term_to_var);
        stop.check()?;
        let build_error = |error| FpRealEncodingError::Stopped(stop.refuse_build_error(error));
        let mut should_stop =
            |progress| checkpoint(stop, observe, FpRealPhase::Construction(progress)).is_err();
        let mut fp = FpConstruction::new(solver, &mut should_stop).map_err(build_error)?;

        // A term present only below fp.to_real still needs an actual FP cache
        // entry for model extraction and refinement blocking (#6241).
        for site in sites {
            stop.check()?;
            if matches!(terms.sort(site.arg), Sort::FloatingPoint(..)) {
                fp.try_get_fp(site.arg).map_err(build_error)?;
            }
        }
        let mut linking_pairs = Vec::new();
        for (&variable, &term) in &tseitin_result.var_to_term {
            stop.check()?;
            match bitblast_fp_predicate_controlled(terms, &mut fp, term).map_err(build_error)? {
                FpPredicateResult::Bitblasted(lit) => linking_pairs.push((variable as i32, lit)),
                FpPredicateResult::NotFpPredicate => {}
                FpPredicateResult::Unsupported => return Err(FpRealEncodingError::Unsupported),
            }
        }

        let mut scan_check = || {
            checkpoint(stop, observe, FpRealPhase::CongruenceScan)
                .map_err(|_| FpBuildError::Interrupted)
        };
        let foreign = congruence::scan_foreign_controlled(terms, fp_assertions, &mut scan_check)
            .map_err(build_error)?;
        let mut congruence_clauses = Vec::new();
        let mut congruence_incomplete = false;
        if !foreign.is_empty() {
            let mut plan_check = || {
                checkpoint(stop, observe, FpRealPhase::CongruencePlan)
                    .map_err(|_| FpBuildError::Interrupted)
            };
            let plan = congruence::plan_congruence_controlled(
                terms,
                &mut fp,
                &tseitin_result,
                &foreign,
                &mut plan_check,
            )
            .map_err(build_error)?;
            congruence_clauses = plan.clauses;
            // Unlike stateless FP, foreign.unencodable is not an admission
            // condition here: the mixed subproblem decides Real-sorted roots.
            congruence_incomplete = plan.incomplete;
        }
        let encoding = fp.finish().map_err(build_error)?;
        // This mixed lane has always refused *any* actual encoding gap,
        // including one introduced by congruence, not merely a base gap.
        if encoding.has_encoding_gap {
            return Err(FpRealEncodingError::EncodingGap);
        }
        let namespace = FpNamespace::new(tseitin_result.num_vars, encoding.cache.next_var)
            .map_err(|_| stop.refuse_build_error(FpBuildError::VariableLimit))?;
        stop.check()?;
        let mut base_clauses = Vec::new();
        for clause in &tseitin_result.clauses {
            append_clause(
                &mut base_clauses,
                clause.literals().iter().copied(),
                stop,
                observe,
            )?;
        }
        for clause in encoding.clauses {
            append_clause(
                &mut base_clauses,
                clause
                    .literals()
                    .iter()
                    .map(|&lit| namespace.offset_lit(lit)),
                stop,
                observe,
            )?;
        }
        for (tseitin_lit, fp_lit) in linking_pairs {
            let offset = namespace.offset_lit(fp_lit);
            append_clause(&mut base_clauses, [-tseitin_lit, offset], stop, observe)?;
            append_clause(&mut base_clauses, [tseitin_lit, -offset], stop, observe)?;
        }
        // The mixed lane links conditions BEFORE congruence (the stateless
        // lane has a different order). Retain this exact original schedule.
        for (fp_var, tseitin_var) in encoding.pending_condition_links {
            let offset = namespace.offset_lit(fp_var as i32);
            let tseitin_lit = tseitin_var as i32;
            append_clause(&mut base_clauses, [-tseitin_lit, offset], stop, observe)?;
            append_clause(&mut base_clauses, [tseitin_lit, -offset], stop, observe)?;
        }
        for clause in congruence_clauses {
            let literals = clause.into_iter().map(|lit| match lit {
                PlanLit::Fp(lit) => namespace.offset_lit(lit),
                PlanLit::Tseitin(lit) => lit,
            });
            append_clause(&mut base_clauses, literals, stop, observe)?;
        }
        let term_to_fp = encoding.cache.term_to_fp;
        let rm_terms = encoding.cache.rm_terms;
        checkpoint(stop, observe, FpRealPhase::EncodingReady)?;
        Ok(FpEncoding {
            base_clauses,
            tseitin_result,
            term_to_fp,
            rm_terms,
            var_offset: namespace.offset(),
            total_vars: namespace.total_vars() as usize,
            congruence_incomplete,
        })
    }
}

#[cfg(test)]
#[path = "to_real_encoding/tests.rs"]
mod tests;
