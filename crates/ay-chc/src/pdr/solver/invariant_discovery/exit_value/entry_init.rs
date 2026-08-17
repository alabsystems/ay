// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Entry-clause initialization for definite exit-value analysis.

use super::PdrSolver;
use crate::{ChcExpr, ChcVar, HornClause};

impl PdrSolver {
    /// Extract init value for a variable at a given index from entry clauses.
    ///
    /// Looks at non-self-loop clauses defining a predicate for direct equality
    /// constraints on the head argument at position `idx`.
    pub(super) fn extract_init_from_entry_clauses(
        entry_clauses: &[&HornClause],
        idx: usize,
        canonical_vars: &[ChcVar],
    ) -> Option<i128> {
        // All entry clauses must agree on the same init value
        let mut init_val: Option<i128> = None;

        for clause in entry_clauses {
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if idx >= head_args.len() || head_args.len() != canonical_vars.len() {
                return None;
            }

            let constraint = clause.body.constraint.as_ref();

            // Case 1: head arg is a constant integer
            if let ChcExpr::Int(v) = &head_args[idx] {
                match init_val {
                    Some(prev) if prev != *v => return None,
                    Some(_) => {}
                    None => init_val = Some(*v),
                }
                continue;
            }

            // Case 2: head arg is a variable with an equality in the constraint
            if let ChcExpr::Var(hv) = &head_args[idx] {
                if let Some(c) = constraint {
                    if let Some(ChcExpr::Int(v)) = Self::find_equality_rhs(c, &hv.name) {
                        match init_val {
                            Some(prev) if prev != v => return None,
                            Some(_) => {}
                            None => init_val = Some(v),
                        }
                        continue;
                    }
                }
                return None;
            }

            return None;
        }

        init_val
    }
}
