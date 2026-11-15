// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{AcyclicNames, BmcSolver, ChcExpr};

/// Preserve the established BMC rewrite order, admitting the result of each
/// stage before another recursive helper or explicit substitution consumes it.
/// The individual pure rewrite implementations are not interruptible here.
pub(super) fn simplify_expression(
    expression: ChcExpr,
    names: &mut AcyclicNames<'_>,
) -> Option<ChcExpr> {
    names.check(&expression)?;
    let expression = BmcSolver::simplify_dt_selector_apps(expression);
    names.check(&expression)?;
    let expression = expression.simplify_array_ops();
    names.check(&expression)?;
    let expression = expression.simplify_constants();
    names.check(&expression)?;
    let expression = BmcSolver::simplify_bv_identities(expression);
    names.check(&expression)?;
    let expression = expression.simplify_constants();
    names.check(&expression)?;
    Some(expression)
}
