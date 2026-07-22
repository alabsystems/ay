// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) integration tests, split by feature area.

pub(crate) use super::*;
pub(crate) use ay_core::term::Symbol;
pub(crate) use ay_core::{Sort, TheoryLit, Tseitin};
pub(crate) use ay_euf::EufSolver;
pub(crate) use ay_sat::{AssumeResult, SatResult};

mod adapter_forwarding_tests;
mod conflict_explanation;
mod conflict_explanation_lia_arrays;
mod core;
mod incremental;
mod model_equality;
mod model_verification;
mod phase_hints;
mod propagation;
mod sat_warm_state;
mod string_lemma;
mod unsat_core;

/// Convert a ay-sat Literal to DIMACS-style CNF literal
pub(crate) fn sat_lit_to_cnf_lit(lit: Literal) -> CnfLit {
    let var = (lit.variable().id() + 1) as i32;
    if lit.is_positive() {
        var
    } else {
        -var
    }
}

/// High-level SMT solver interface (test-only)
pub(crate) struct SmtSolver {
    /// Term store for all terms
    pub(crate) terms: TermStore,
    /// CNF clauses from Tseitin transformation
    pub(crate) cnf_clauses: Vec<CnfClause>,
    /// Variable mappings
    pub(crate) var_to_term: HashMap<u32, TermId>,
    pub(crate) term_to_var: HashMap<TermId, u32>,
    /// Number of CNF variables
    pub(crate) num_vars: u32,
    /// Assertions as term IDs
    pub(crate) assertions: Vec<TermId>,
}

impl Default for SmtSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtSolver {
    /// Create a new SMT solver
    pub(crate) fn new() -> Self {
        Self {
            terms: TermStore::new(),
            cnf_clauses: Vec::new(),
            var_to_term: HashMap::default(),
            term_to_var: HashMap::default(),
            num_vars: 0,
            assertions: Vec::new(),
        }
    }

    /// Add an assertion
    pub(crate) fn assert(&mut self, term: TermId) {
        self.assertions.push(term);
    }

    /// Solve all assertions (propositional only)
    pub(crate) fn solve_propositional(&mut self) -> SatResult {
        if self.assertions.is_empty() {
            return SatResult::Sat(vec![]);
        }

        // Run Tseitin transformation
        let tseitin = Tseitin::new(&self.terms);
        let result = tseitin.transform_all(&self.assertions);

        // Store mappings
        self.cnf_clauses = result.clauses.clone();
        self.var_to_term = result.var_to_term.iter().map(|(&k, &v)| (k, v)).collect();
        self.term_to_var = result.term_to_var.iter().map(|(&k, &v)| (k, v)).collect();
        self.num_vars = result.num_vars;

        // Create DPLL(T) solver with propositional theory
        let theory = PropositionalTheory;
        let mut dpll = DpllT::from_tseitin(&self.terms, &result, theory);

        dpll.solve().unwrap()
    }
}
