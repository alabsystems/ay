// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only oracle retaining the prior mixed encoder's unrestricted schedule.

use super::*;

pub(super) fn encode(
    executor: &Executor,
    assertions: &[TermId],
    sites: &[FpToRealSite],
) -> (FpEncoding, usize, usize) {
    let terms = &executor.ctx.terms;
    let mut tseitin = Tseitin::new(terms);
    for &root in assertions {
        tseitin.assert_term(root);
    }
    let tseitin_result = tseitin.into_assertion_result();
    let mut fp = FpSolver::new_with_tseitin(terms, &tseitin_result.term_to_var);
    for site in sites {
        if matches!(terms.sort(site.arg), Sort::FloatingPoint(..)) {
            fp.get_fp(site.arg);
        }
    }
    let mut links = Vec::new();
    for (&var, &term) in &tseitin_result.var_to_term {
        match executor.bitblast_fp_predicate(&mut fp, term) {
            FpPredicateResult::Bitblasted(lit) => links.push((var as i32, lit)),
            FpPredicateResult::NotFpPredicate => {}
            FpPredicateResult::Unsupported => return (refused(tseitin_result, &fp), 0, 0),
        }
    }
    let foreign = congruence::scan_foreign(terms, assertions);
    let mut congruence_clauses = Vec::new();
    let mut congruence_incomplete = false;
    if !foreign.is_empty() {
        let plan = congruence::plan_congruence(terms, &mut fp, &tseitin_result, &foreign);
        congruence_clauses = plan.clauses;
        congruence_incomplete = plan.incomplete;
    }
    if fp.has_encoding_gap() {
        return (refused(tseitin_result, &fp), 0, 0);
    }
    let fp_clauses = fp.take_clauses();
    let condition_links = fp.take_pending_condition_links();
    let conditions = condition_links.len();
    let congruences = congruence_clauses.len();
    let total_vars = (tseitin_result.num_vars + fp.num_vars()) as usize;
    let var_offset = tseitin_result.num_vars as i32;
    let shift = |lit| super::super::super::super::to_real::offset_cnf_lit(lit, var_offset);
    let mut base_clauses = tseitin_result.clauses.clone();
    for clause in fp_clauses {
        base_clauses.push(CnfClause::new(
            clause.literals().iter().copied().map(shift).collect(),
        ));
    }
    for (var, lit) in links {
        base_clauses.push(CnfClause::binary(-var, shift(lit)));
        base_clauses.push(CnfClause::binary(var, -shift(lit)));
    }
    for (fp_var, var) in condition_links {
        base_clauses.push(CnfClause::binary(-(var as i32), shift(fp_var as i32)));
        base_clauses.push(CnfClause::binary(var as i32, -shift(fp_var as i32)));
    }
    for clause in congruence_clauses {
        base_clauses.push(CnfClause::new(
            clause
                .into_iter()
                .map(|lit| match lit {
                    PlanLit::Fp(lit) => shift(lit),
                    PlanLit::Tseitin(lit) => lit,
                })
                .collect(),
        ));
    }
    (
        FpEncoding {
            base_clauses,
            tseitin_result,
            term_to_fp: fp.term_to_fp().clone(),
            rm_terms: fp.rm_terms().clone(),
            var_offset,
            total_vars,
            congruence_incomplete,
        },
        conditions,
        congruences,
    )
}

// The old implementation conflated these semantic failures into an empty
// sentinel. Production now returns the corresponding explicit error instead.
fn refused(tseitin_result: ay_core::TseitinResult, fp: &FpSolver<'_>) -> FpEncoding {
    FpEncoding {
        base_clauses: Vec::new(),
        tseitin_result,
        term_to_fp: fp.term_to_fp().clone(),
        rm_terms: fp.rm_terms().clone(),
        var_offset: 0,
        total_vars: 0,
        congruence_incomplete: false,
    }
}

pub(super) fn assert_same(actual: &FpEncoding, expected: &FpEncoding) {
    assert_eq!(actual.base_clauses, expected.base_clauses);
    assert_eq!(actual.var_offset, expected.var_offset);
    assert_eq!(actual.total_vars, expected.total_vars);
    assert_eq!(actual.congruence_incomplete, expected.congruence_incomplete);
    assert_eq!(
        actual.tseitin_result.clauses,
        expected.tseitin_result.clauses
    );
    assert_eq!(
        actual.tseitin_result.term_to_var,
        expected.tseitin_result.term_to_var
    );
    assert_eq!(
        actual.tseitin_result.var_to_term,
        expected.tseitin_result.var_to_term
    );
    assert_eq!(actual.tseitin_result.root, expected.tseitin_result.root);
    assert_eq!(
        actual.tseitin_result.num_vars,
        expected.tseitin_result.num_vars
    );
    assert!(actual.tseitin_result.proof_annotations.is_none());
    assert!(expected.tseitin_result.proof_annotations.is_none());
    assert_eq!(actual.term_to_fp.len(), expected.term_to_fp.len());
    for (term, expected) in &expected.term_to_fp {
        let actual = actual.term_to_fp.get(term).unwrap();
        assert_eq!(actual.sign, expected.sign);
        assert_eq!(actual.exponent, expected.exponent);
        assert_eq!(actual.significand, expected.significand);
        assert_eq!(actual.precision, expected.precision);
    }
}
