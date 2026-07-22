// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model sampling for invariant discovery.
//!
//! Provides methods to sample diverse models from:
//! - Fact constraints (init regions)
//! - Entry edges (inter-predicate transitions)
//! - Must-summaries (concretely reachable states)
//! - Forward simulation through self-loop transitions

use crate::{ChcExpr, ChcVar};

mod entry_eval;
mod entry_sampling;
mod init;
mod reachable;
#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

fn int_presence_tautology(var: ChcVar) -> ChcExpr {
    let expr = ChcExpr::var(var);
    ChcExpr::or(
        ChcExpr::le(expr.clone(), ChcExpr::int(0)),
        ChcExpr::gt(expr, ChcExpr::int(0)),
    )
}

fn with_int_presence_tautologies(base: ChcExpr, vars: &[ChcVar]) -> ChcExpr {
    let mut conjuncts = Vec::with_capacity(1 + vars.len());
    conjuncts.push(base);
    conjuncts.extend(vars.iter().cloned().map(int_presence_tautology));
    ChcExpr::and_all(conjuncts)
}

fn with_blocking_clauses(base: ChcExpr, blocking_clauses: &[ChcExpr]) -> ChcExpr {
    if blocking_clauses.is_empty() {
        return base;
    }

    let mut conjuncts = Vec::with_capacity(1 + blocking_clauses.len());
    conjuncts.push(base);
    conjuncts.extend(blocking_clauses.iter().cloned());
    ChcExpr::and_all(conjuncts)
}
