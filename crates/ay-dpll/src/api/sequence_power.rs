// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{Solver, SolverError, Term};
use ay_core::{Sort, Symbol};

impl Solver {
    /// Repeat a String or sequence `count` times, or return empty when count <= 0.
    /// Retains the application for AST inspection. Explicit simplification and
    /// solving lower constant counts where affordable; symbolic powers may
    /// require an incomplete theory lane.
    pub fn try_seq_power(&mut self, sequence: Term, count: Term) -> Result<Term, SolverError> {
        let base = self.resolve_term("seq.power", sequence)?;
        let exponent = self.resolve_term("seq.power", count)?;
        let sort = self.terms().sort(base).clone();
        if !matches!(sort, Sort::String | Sort::Seq(_)) || self.terms().sort(exponent) != &Sort::Int
        {
            return Err(SolverError::SortMismatch {
                operation: "seq.power",
                expected: "String or Seq, Int",
                got: vec![sort, self.terms().sort(exponent).clone()],
            });
        }
        let result =
            self.terms_mut()
                .mk_app_structural(Symbol::named("seq.power"), [base, exponent], sort);
        Ok(self.wrap_term(result))
    }
}
