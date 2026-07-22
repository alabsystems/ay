// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) fn is_equality_preserved_by_transitions_with_entry(
        &mut self,
        predicate: PredicateId,
        idx_i: usize,
        idx_j: usize,
        entry_constraint: Option<ChcExpr>,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // Get the head expressions for var_i and var_j (post-state values)
            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];

            // Get the body expressions for var_i and var_j (pre-state values)
            // For self-transitions, find the mapping
            if clause.body.predicates.len() != 1 {
                // Hyperedge - check if equality is preserved across predicates
                // For now, be conservative on hyperedges
                continue;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];

            // Check: IF body_i = body_j THEN head_i = head_j
            // Equivalently: body_i = body_j /\ head_i != head_j is UNSAT
            let mut clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Add entry constraint if provided (restricts the domain to reachable states)
            // Need to convert from canonical form to clause-local body variables
            if let Some(ref ec) = entry_constraint {
                // Build map from canonical names to body variable names
                let mut canon_to_body: FxHashMap<String, ChcExpr> = FxHashMap::default();
                for (b_arg, canon) in body_args.iter().zip(canonical_vars.iter()) {
                    canon_to_body.insert(canon.name.clone(), b_arg.clone());
                }
                // Convert entry constraint to use body variable names
                let ec_local = ec.substitute_name_map(&canon_to_body);
                clause_constraint = ChcExpr::and(clause_constraint, ec_local);
            }

            // First, try algebraic check: if head_i and head_j have the same offset
            // from body_i and body_j respectively, equality is preserved.
            // E.g., if head_i = body_i + c and head_j = body_j + c, then body_i=body_j => head_i=head_j
            if let (Some(offset_i), Some(offset_j)) = (
                Self::extract_offset_from_var(head_i, body_i, &clause.body.constraint),
                Self::extract_offset_from_var(head_j, body_j, &clause.body.constraint),
            ) {
                // Check if offsets are equal (or both cases in OR have equal offsets)
                if Self::offsets_always_equal(&offset_i, &offset_j) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Equality algebraically preserved (same offset): {:?} vs {:?}",
                            offset_i,
                            offset_j
                        );
                    }
                    continue;
                }
            }

            let pre_eq = ChcExpr::eq(body_i.clone(), body_j.clone());
            let post_neq = ChcExpr::ne(head_i.clone(), head_j.clone());

            // Query: clause_constraint AND pre_eq AND post_neq
            // If SAT, equality is NOT preserved
            let query = ChcExpr::and(
                ChcExpr::and(clause_constraint, pre_eq.clone()),
                post_neq.clone(),
            );

            self.smt.reset();
            // Use timeout to avoid hanging on complex queries with ITE
            if self.config.verbose && entry_constraint.is_some() {
                safe_eprintln!("PDR: Preservation query: {}", query);
            }
            let result = self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500));
            if self.config.verbose && entry_constraint.is_some() {
                safe_eprintln!(
                    "PDR: Preservation result: {:?}",
                    match &result {
                        SmtResult::Sat(m) => format!("SAT({m:?})"),
                        SmtResult::Unsat => "UNSAT".to_string(),
                        SmtResult::UnsatWithCore(_) => "UNSAT+core".to_string(),
                        SmtResult::UnsatWithFarkas(_) => "UNSAT+farkas".to_string(),
                        SmtResult::Unknown => "UNKNOWN".to_string(),
                    }
                );
            }
            match result {
                SmtResult::Sat(_) => {
                    // Equality is NOT preserved by this transition
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Equality IS preserved by this transition
                    continue;
                }
                SmtResult::Unknown => {
                    // SMT returned Unknown - try case-splitting on OR in constraint
                    // This handles cases like: (or (and A B) (and C D)) which AY's LIA
                    // solver doesn't handle well directly
                    let constraint_for_cases = clause
                        .body
                        .constraint
                        .clone()
                        .unwrap_or(ChcExpr::Bool(true));
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Equality check returned Unknown, trying case-split on: {}",
                            constraint_for_cases
                        );
                    }
                    if let Some(cases) = Self::extract_or_cases(&constraint_for_cases) {
                        if self.config.verbose {
                            safe_eprintln!("PDR: Found {} cases for case-splitting", cases.len());
                        }
                        let mut all_unsat = true;
                        for (i, case) in cases.iter().enumerate() {
                            let case_query = ChcExpr::and(
                                ChcExpr::and(case.clone(), pre_eq.clone()),
                                post_neq.clone(),
                            );
                            if self.config.verbose {
                                safe_eprintln!("PDR: Case {}: {}", i, case);
                            }
                            self.smt.reset();
                            let case_result = self.smt.check_sat_with_timeout(
                                &case_query,
                                std::time::Duration::from_millis(500),
                            );
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Case {} result: {:?}",
                                    i,
                                    match &case_result {
                                        SmtResult::Sat(_) => "SAT",
                                        SmtResult::Unsat => "UNSAT",
                                        SmtResult::UnsatWithCore(_) => "UNSAT+core",
                                        SmtResult::UnsatWithFarkas(_) => "UNSAT+farkas",
                                        SmtResult::Unknown => "UNKNOWN",
                                    }
                                );
                            }
                            match case_result {
                                SmtResult::Sat(_) => {
                                    // One case is SAT - equality not preserved
                                    return false;
                                }
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => {
                                    // This case is UNSAT, continue checking
                                }
                                SmtResult::Unknown => {
                                    // Can't verify this case
                                    all_unsat = false;
                                    break;
                                }
                            }
                        }
                        if all_unsat {
                            // All cases are UNSAT - equality is preserved
                            continue;
                        }
                    }
                    // Can't verify - be conservative
                    return false;
                }
            }
        }

        // All self-loop transitions preserve the equality.
        // But if zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        true
    }

    /// Extract disjuncts from a top-level OR expression, returning them as cases.
    /// If the expression has nested structure like (and (or A B) C), this returns
    /// [(and A C), (and B C)] to enable case-splitting.
    pub(in crate::pdr::solver) fn extract_or_cases(expr: &ChcExpr) -> Option<Vec<ChcExpr>> {
        match expr {
            ChcExpr::Op(ChcOp::Or, args) => {
                // Direct OR at top level
                Some(args.iter().map(|a| (**a).clone()).collect())
            }
            ChcExpr::Op(ChcOp::And, args) => {
                // Look for OR inside AND: (and (or A B) C) -> [(and A C), (and B C)]
                for (i, arg) in args.iter().enumerate() {
                    if let ChcExpr::Op(ChcOp::Or, or_args) = arg.as_ref() {
                        let other_conjuncts: Vec<_> = args
                            .iter()
                            .enumerate()
                            .filter(|(j, _)| *j != i)
                            .map(|(_, a)| (**a).clone())
                            .collect();

                        let cases: Vec<_> = or_args
                            .iter()
                            .map(|or_case| {
                                let mut case_conjuncts = vec![(**or_case).clone()];
                                case_conjuncts.extend(other_conjuncts.clone());
                                if case_conjuncts.len() == 1 {
                                    case_conjuncts.pop().expect("len == 1")
                                } else {
                                    // Build AND chain
                                    let mut result = case_conjuncts.pop().expect("len > 1");
                                    while let Some(c) = case_conjuncts.pop() {
                                        result = ChcExpr::and(c, result);
                                    }
                                    result
                                }
                            })
                            .collect();
                        return Some(cases);
                    }
                }
                None // No OR found in AND
            }
            _ => None,
        }
    }

    /// Extract the offset of head_var from body_var using constraint equalities.
    /// For `head_var = body_var + c`, returns Some(VarOffset::Const(c)).
    /// For OR constraints where each branch has a different offset, returns VarOffset::Cases.
    pub(in crate::pdr::solver) fn extract_offset_from_var(
        head_expr: &ChcExpr,
        body_expr: &ChcExpr,
        constraint: &Option<ChcExpr>,
    ) -> Option<VarOffset> {
        let body_var_name = match body_expr {
            ChcExpr::Var(v) => &v.name,
            _ => return None,
        };
        let head_var_name = match head_expr {
            ChcExpr::Var(v) => &v.name,
            _ => return None,
        };

        // Look for head_var = body_var + c in constraint
        let constraint = constraint.as_ref()?;
        Self::find_offset_in_constraint_recursive(constraint, head_var_name, body_var_name)
    }

    /// Recursively search constraint for offset relationship.
    pub(in crate::pdr::solver) fn find_offset_in_constraint_recursive(
        expr: &ChcExpr,
        head_var: &str,
        body_var: &str,
    ) -> Option<VarOffset> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                // Search conjuncts
                for arg in args {
                    if let Some(offset) =
                        Self::find_offset_in_constraint_recursive(arg, head_var, body_var)
                    {
                        return Some(offset);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Or, args) => {
                // For OR, collect offset from each branch
                let mut offsets = Vec::new();
                for arg in args {
                    if let Some(offset) =
                        Self::find_offset_in_constraint_recursive(arg, head_var, body_var)
                    {
                        match offset {
                            VarOffset::Const(c) => offsets.push(c),
                            VarOffset::Cases(cs) => offsets.extend(cs),
                        }
                    } else {
                        return None; // Can't determine offset in some branch
                    }
                }
                if offsets.is_empty() {
                    None
                } else {
                    Some(VarOffset::Cases(offsets))
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check head_var = body_var + c
                let (lhs, rhs) = (args[0].as_ref(), args[1].as_ref());
                if Self::is_var_expr(lhs, head_var) {
                    if let Some(c) = Self::extract_addition_offset(rhs, body_var) {
                        return Some(VarOffset::Const(c));
                    }
                }
                if Self::is_var_expr(rhs, head_var) {
                    if let Some(c) = Self::extract_addition_offset(lhs, body_var) {
                        return Some(VarOffset::Const(c));
                    }
                }
                None
            }
            _ => None,
        })
    }

    /// Check if two VarOffsets are always equal (both single equal values, or all cases equal)
    pub(in crate::pdr::solver) fn offsets_always_equal(a: &VarOffset, b: &VarOffset) -> bool {
        match (a, b) {
            (VarOffset::Const(x), VarOffset::Const(y)) => x == y,
            (VarOffset::Const(x), VarOffset::Cases(ys)) => ys.iter().all(|y| y == x),
            (VarOffset::Cases(xs), VarOffset::Const(y)) => xs.iter().all(|x| x == y),
            (VarOffset::Cases(xs), VarOffset::Cases(ys)) => {
                // Both have same set of offsets (for corresponding OR branches)
                xs.len() == ys.len() && xs.iter().zip(ys.iter()).all(|(x, y)| x == y)
            }
        }
    }
}
