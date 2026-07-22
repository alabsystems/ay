// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CNF/Tseitin encoding for check_sat queries.
//!
//! Converts the preprocessed query into a SAT solver instance with
//! Tseitin-encoded clauses, optionally with per-conjunct assumptions
//! for unsat-core extraction.

use ay_core::time::Instant;
use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::{TermId, Tseitin};

use super::super::context::SmtContext;
use super::super::types::SmtResult;
use super::CnfState;
use super::PreparedQuery;
use crate::ChcExpr;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HbHashMap;

impl SmtContext {
    /// Build the CNF encoding for a check_sat query.
    ///
    /// Converts the preprocessed expressions into Tseitin clauses and
    /// populates a fresh SAT solver. When the query has multiple
    /// top-level conjuncts, each gets its own assumption literal for
    /// unsat-core extraction.
    ///
    /// Returns `Err(SmtResult::Unknown)` on budget or timeout exhaustion.
    pub(super) fn build_check_sat_cnf(
        &mut self,
        prepared: &PreparedQuery,
        start: Instant,
        timeout: Option<Duration>,
    ) -> Result<CnfState, SmtResult> {
        let use_assumptions = prepared.top_conjuncts.len() >= 2;

        let (term_to_var, var_to_term, num_vars, sat, assumptions, assumption_map, roots) =
            if use_assumptions {
                let conjunct_terms: Vec<(ChcExpr, TermId)> = prepared
                    .top_conjuncts
                    .iter()
                    .map(|c| (c.clone(), self.convert_expr(c)))
                    .collect();

                // Bail out if conversion budget was exceeded (#2771).
                if self.conversion_budget_exceeded {
                    return Err(SmtResult::Unknown);
                }

                // #6047: Verify all conjunct terms are Bool-sorted. Non-Bool
                // conjuncts arise from ill-typed And/Or expressions where
                // flatten_top_level_and extracted non-Bool leaves before
                // convert_expr could apply sort guards.
                if conjunct_terms
                    .iter()
                    .any(|(_, t)| self.terms.sort(*t) != &ay_core::Sort::Bool)
                {
                    self.conversion_budget_exceeded = true;
                    return Err(SmtResult::Unknown);
                }
                // #5877: Check timeout after expression conversion. For BV-to-Int
                // problems with unrolled transitions (k>=2), convert_expr can exceed
                // the per-query timeout, starving the portfolio of time for PDR.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }

                let mut tseitin = Tseitin::new(&self.terms);

                let mut assumptions: Vec<ay_sat::Literal> =
                    Vec::with_capacity(conjunct_terms.len());
                let mut assumption_map: FxHashMap<ay_sat::Literal, ChcExpr> = FxHashMap::default();

                for (c, c_term) in &conjunct_terms {
                    let cnf_lit = tseitin.encode(*c_term, true);
                    let sat_lit = ay_sat::Literal::from_dimacs(cnf_lit);
                    assumptions.push(sat_lit);
                    assumption_map.insert(sat_lit, c.clone());
                }

                let mut sat = ay_sat::Solver::new(tseitin.num_vars() as usize);
                // #5384: enable clause tracing for UNSAT verification defense.
                sat.enable_clause_trace();
                // Internal CHC queries never consume the UNSAT proof
                // certificate; skip backward LRAT reconstruction on every
                // UNSAT. ClauseTrace clause-ID tracking is unaffected.
                sat.set_unsat_certificate_enabled(false);
                // CHC queries are short-lived and may be replayed under
                // assumptions for UNSAT-core recovery. Keep preprocessing off
                // so BVE/probing/backbone cannot mutate the trace-sensitive
                // clause set before the verifier sees it.
                sat.set_preprocess_enabled(false);
                for clause in tseitin.all_clauses() {
                    let lits: Vec<ay_sat::Literal> = clause
                        .0
                        .iter()
                        .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                        .collect();
                    sat.add_clause(lits);
                }

                // #5877: Check timeout after Tseitin encoding. Large formulas
                // (BV-to-Int at k>=2) can produce huge CNFs that exceed the budget.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }

                let roots: Vec<TermId> = conjunct_terms.iter().map(|(_, t)| *t).collect();
                (
                    tseitin.term_to_var().clone(),
                    tseitin.var_to_term().clone(),
                    tseitin.num_vars(),
                    sat,
                    Some(assumptions),
                    Some(assumption_map),
                    roots,
                )
            } else {
                // Fall back to the legacy "assert root" encoding for non-conjunction queries.
                let term = self.convert_expr(&prepared.normalized);
                if self.conversion_budget_exceeded {
                    return Err(SmtResult::Unknown);
                }
                // #6047: Non-Bool root term → return Unknown.
                if self.terms.sort(term) != &ay_core::Sort::Bool {
                    self.conversion_budget_exceeded = true;
                    return Err(SmtResult::Unknown);
                }
                // #5877: Check timeout after expression conversion.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }
                let tseitin = Tseitin::new(&self.terms);
                let result = tseitin.transform(term);

                // #5877: Check timeout after Tseitin encoding.
                if let Some(t) = timeout {
                    if start.elapsed() >= t {
                        return Err(SmtResult::Unknown);
                    }
                }

                let mut sat = ay_sat::Solver::new(result.num_vars as usize);
                // #5384: enable clause tracing for UNSAT verification defense.
                sat.enable_clause_trace();
                // Internal CHC queries never consume the UNSAT proof
                // certificate; skip backward LRAT reconstruction on every
                // UNSAT. ClauseTrace clause-ID tracking is unaffected.
                sat.set_unsat_certificate_enabled(false);
                // Keep this path aligned with the conjunction encoding above:
                // CHC SAT checks favor stable, replayable clauses over
                // one-shot preprocessing.
                sat.set_preprocess_enabled(false);
                for clause in &result.clauses {
                    let lits: Vec<ay_sat::Literal> = clause
                        .0
                        .iter()
                        .map(|&lit| ay_sat::Literal::from_dimacs(lit))
                        .collect();
                    sat.add_clause(lits);
                }

                (
                    result.term_to_var.clone(),
                    result.var_to_term.clone(),
                    result.num_vars,
                    sat,
                    None,
                    None,
                    vec![term],
                )
            };

        Ok(CnfState {
            term_to_var,
            var_to_term,
            num_vars,
            sat,
            assumptions,
            assumption_map,
            bv_var_offset: 0,
            bv_term_to_bits: HbHashMap::default(),
            roots,
        })
    }
}
