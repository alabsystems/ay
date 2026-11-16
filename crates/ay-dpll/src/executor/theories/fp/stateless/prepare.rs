// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A single owning construction covers base predicates and foreign congruence.

use ay_core::{CnfClause, TermId, TermStore, Tseitin, TseitinResult};
use ay_fp::{FpBuildError, FpBuiltEncoding, FpConstruction, FpSolver};

use crate::executor_types::UnknownOrigin;

use super::super::bitblast::bitblast_fp_predicate_controlled;
use super::super::congruence::{self, PlanLit};
use super::super::namespace::{validate_tseitin_namespace, FpNamespace};
use super::super::stop::FpStop;
use super::super::support::FpPredicateResult;
use super::{checkpoint, FpPhase};

pub(super) struct PreparedFp {
    pub(super) tseitin: TseitinResult,
    pub(super) encoding: FpBuiltEncoding,
    pub(super) links: Vec<(i32, i32)>,
    pub(super) congruence: Vec<Vec<PlanLit>>,
    pub(super) congruence_incomplete: bool,
    pub(super) namespace: FpNamespace,
}

pub(super) enum FpPreparationError {
    Stopped(UnknownOrigin),
    Unsupported,
    BaseGap,
}

impl From<UnknownOrigin> for FpPreparationError {
    fn from(origin: UnknownOrigin) -> Self {
        Self::Stopped(origin)
    }
}

fn encode_tseitin(
    terms: &TermStore,
    assertions: &[TermId],
    stop: &FpStop,
    observe: &impl Fn(FpPhase),
) -> Result<TseitinResult, FpPreparationError> {
    checkpoint(stop, observe, FpPhase::Tseitin)?;
    let mut tseitin = Tseitin::new(terms);
    let mut clauses = Vec::new();
    for &assertion in assertions {
        checkpoint(stop, observe, FpPhase::Tseitin)?;
        let encoded = tseitin.encode_assertion(assertion);
        stop.check()?;
        // Keep the existing definition/activation ordering exactly, without
        // separately retaining two unused copies of these clauses.
        for clause in encoded.def_clauses {
            stop.check()?;
            clauses.push(clause);
        }
        clauses.push(CnfClause::unit(encoded.root_lit));
    }
    super::super::nested_bv_guards::seed(
        terms,
        assertions.iter().copied(),
        &mut tseitin,
        stop,
        &|| observe(FpPhase::Tseitin),
    )?;
    for clause in tseitin.take_new_clauses() {
        stop.check()?;
        clauses.push(clause);
    }
    validate_tseitin_namespace(tseitin.num_vars())
        .map_err(|_| stop.refuse_build_error(FpBuildError::VariableLimit))?;
    stop.check()?;
    let term_to_var = tseitin.term_to_var().clone();
    stop.check()?;
    let var_to_term = tseitin.var_to_term().clone();
    stop.check()?;
    Ok(TseitinResult::new(
        clauses,
        term_to_var,
        var_to_term,
        0,
        tseitin.num_vars(),
    ))
}

pub(super) fn prepare(
    terms: &TermStore,
    assertions: &[TermId],
    stop: &FpStop,
    observe: &impl Fn(FpPhase),
) -> Result<PreparedFp, FpPreparationError> {
    let tseitin = encode_tseitin(terms, assertions, stop, observe)?;
    stop.check()?;
    let solver = FpSolver::new_with_seeded_tseitin(terms, &tseitin.term_to_var);
    stop.check()?;
    let build_error = |error| FpPreparationError::Stopped(stop.refuse_build_error(error));
    let mut should_stop = |progress| {
        observe(FpPhase::construction(progress));
        stop.should_stop()
    };
    let mut fp = FpConstruction::new(solver, &mut should_stop).map_err(build_error)?;
    let mut links = Vec::new();
    for (&variable, &term) in &tseitin.var_to_term {
        stop.check()?;
        match bitblast_fp_predicate_controlled(terms, &mut fp, term).map_err(build_error)? {
            FpPredicateResult::Bitblasted(lit) => links.push((variable as i32, lit)),
            FpPredicateResult::NotFpPredicate => {}
            FpPredicateResult::Unsupported => return Err(FpPreparationError::Unsupported),
        }
    }
    let gap_before = fp.try_has_encoding_gap().map_err(build_error)?;
    let mut scan_check = || {
        checkpoint(stop, observe, FpPhase::CongruenceScan).map_err(|_| FpBuildError::Interrupted)
    };
    let foreign = congruence::scan_foreign_controlled(terms, assertions, &mut scan_check)
        .map_err(build_error)?;
    let mut congruence = Vec::new();
    let mut congruence_incomplete = false;
    if !foreign.is_empty() {
        let mut plan_check = || {
            checkpoint(stop, observe, FpPhase::CongruencePlan)
                .map_err(|_| FpBuildError::Interrupted)
        };
        let plan = congruence::plan_congruence_controlled(
            terms,
            &mut fp,
            &tseitin,
            &foreign,
            &mut plan_check,
        )
        .map_err(build_error)?;
        congruence = plan.clauses;
        congruence_incomplete = foreign.unencodable || plan.incomplete;
    }
    // A base gap retains its old unconditional refusal. Only a gap introduced
    // by the congruence pass is a relaxation whose UNSAT may still be admitted.
    if gap_before {
        return Err(FpPreparationError::BaseGap);
    }
    let encoding = fp.finish().map_err(build_error)?;
    congruence_incomplete |= encoding.has_encoding_gap;
    let namespace = FpNamespace::new(tseitin.num_vars, encoding.cache.next_var)
        .map_err(|_| stop.refuse_build_error(FpBuildError::VariableLimit))?;
    stop.check()?;
    Ok(PreparedFp {
        tseitin,
        encoding,
        links,
        congruence,
        congruence_incomplete,
        namespace,
    })
}
