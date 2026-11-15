// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype declarations of a standalone replay obligation.
//!
//! A replay obligation is a complete SMT-LIB script, so every datatype sort
//! that its predicate parameters, clause constants or formulas mention must be
//! declared in it. Without the declaration no solver parses the script
//! (`unknown sort`), and checked replay of any datatype-sorted Safe model
//! failed closed before it reached a solver.

use super::InvariantModel;
use crate::smt::executor_adapter::{collect_dt_declarations_for_exprs, emit_declare_datatypes};
use crate::{ChcError, ChcExpr, ChcResult, HornClause};

impl InvariantModel {
    /// One simultaneous `declare-datatypes` command for every datatype sort
    /// the obligation of `clause` mentions (empty when it mentions none).
    ///
    /// The definitions are the sorts' own in-memory constructors, gathered by
    /// the executor's bounded collector, which refuses two different
    /// definitions under one name instead of choosing one.
    pub(super) fn replay_datatype_declarations(
        &self,
        clause: &HornClause,
        violation: &ChcExpr,
    ) -> ChcResult<String> {
        let refused = |error| {
            ChcError::Verification(format!("replay obligation datatype declarations: {error}"))
        };
        // Parameters of an interpretation may be dead in its formula and
        // clause constants may occur only under a selector: declare both.
        let variables: Vec<ChcExpr> = clause
            .vars()
            .into_iter()
            .chain(
                self.interpretations
                    .values()
                    .flat_map(|interp| interp.vars.iter().cloned()),
            )
            .map(ChcExpr::var)
            .collect();
        let roots = std::iter::once(violation)
            .chain(self.interpretations.values().map(|interp| &interp.formula))
            .chain(&variables);
        let declarations = collect_dt_declarations_for_exprs(roots).map_err(refused)?;
        emit_declare_datatypes(&declarations).map_err(refused)
    }
}

#[cfg(test)]
mod tests;
