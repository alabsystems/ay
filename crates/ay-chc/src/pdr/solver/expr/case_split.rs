// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ITE and OR case-splitting for SMT queries that return Unknown.
//!
//! When the SMT solver returns Unknown on queries with ITE, OR, or disequality
//! structure, these helpers split the query into simpler cases and check each
//! independently. This recovers definitive SAT/UNSAT results from queries that
//! would otherwise stall.

use super::super::PdrSolver;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
#[cfg(test)]
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

#[cfg(test)]
const NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS: u64 = u64::MAX;
#[cfg(test)]
static LAST_CASE_SPLIT_TIMEOUT_MS: AtomicU64 = AtomicU64::new(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS);

#[cfg(test)]
fn record_case_split_timeout_for_tests(timeout: Option<std::time::Duration>) {
    let encoded = match timeout {
        Some(timeout) => u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX - 1),
        None => NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS,
    };
    LAST_CASE_SPLIT_TIMEOUT_MS.store(encoded, Ordering::Relaxed);
}

impl PdrSolver {
    #[cfg(test)]
    pub(in crate::pdr::solver) fn reset_case_split_timeout_observation_for_tests() {
        LAST_CASE_SPLIT_TIMEOUT_MS.store(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS, Ordering::Relaxed);
    }

    /// Extract OR cases from a constraint for case-splitting.
    ///
    /// Given a constraint like `(and guard (or case1 case2))`, this returns
    /// `[(and guard case1), (and guard case2)]` so that we can check each case separately.
    ///
    /// This is a workaround for AY's SMT solver returning Unknown for queries with OR constraints.
    /// By splitting the OR into separate queries, we can often get definitive UNSAT results.
    pub(in crate::pdr) fn extract_or_cases_from_constraint(constraint: &ChcExpr) -> Vec<ChcExpr> {
        // Collect all conjuncts
        let conjuncts = constraint.collect_conjuncts();

        // Find the first OR among the conjuncts
        let mut or_index = None;
        let mut or_branches = Vec::new();
        for (i, conjunct) in conjuncts.iter().enumerate() {
            if let ChcExpr::Op(ChcOp::Or, args) = conjunct {
                or_index = Some(i);
                // Collect all OR branches (handle nested ORs)
                Self::collect_or_branches(args, &mut or_branches);
                break;
            }
        }

        match or_index {
            Some(idx) => {
                // Combine non-OR conjuncts with each OR branch
                let non_or_conjuncts: Vec<_> = conjuncts
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != idx)
                    .map(|(_, c)| c.clone())
                    .collect();

                let mut cases = Vec::new();
                for branch in or_branches {
                    // Build: (and non_or_conjuncts... branch)
                    let mut case_conjuncts = non_or_conjuncts.clone();
                    case_conjuncts.push(branch);
                    cases.push(Self::build_conjunction(&case_conjuncts));
                }
                cases
            }
            None => {
                // No OR found, return the original constraint as a single case
                vec![constraint.clone()]
            }
        }
    }

    /// Collect all branches from an OR expression (handles nested ORs).
    /// Delegated to generalization module.
    pub(in crate::pdr::solver) fn collect_or_branches(
        args: &[Arc<ChcExpr>],
        result: &mut Vec<ChcExpr>,
    ) {
        crate::pdr::generalization::collect_or_branches(args, result);
    }

    /// Split ITE expressions in a constraint into separate cases.
    ///
    /// Given a constraint like:
    ///   (and (= D (ite (<= B F) (+ 1 B) (+ (- 1) B))) ...)
    ///
    /// Returns two cases:
    ///   Case 1: (and (= D (+ 1 B)) (<= B F) ...)
    ///   Case 2: (and (= D (+ (- 1) B)) (not (<= B F)) ...)
    ///
    /// This is essential for verifying invariants through ITE transitions with
    /// parametric constants, where the SMT solver returns Unknown.
    pub(in crate::pdr) fn split_ite_in_constraint(constraint: &ChcExpr) -> Vec<ChcExpr> {
        // Find the first ITE in an equality context
        if let Some((var, cond, then_val, else_val)) = Self::find_ite_equality(constraint) {
            // Create two cases: one for the then-branch, one for the else-branch
            let then_case = Self::substitute_ite_case(constraint, &var, &then_val, &cond, true);
            let else_case = Self::substitute_ite_case(constraint, &var, &else_val, &cond, false);

            vec![then_case, else_case]
        } else {
            vec![constraint.clone()]
        }
    }

    /// Split on the first ITE occurrence anywhere in a boolean formula.
    ///
    /// Returns `(cond, then_case, else_case)` where:
    /// - `then_case` is `expr` with the first `ite(cond, t, e)` replaced by `t`
    /// - `else_case` is `expr` with the first `ite(cond, t, e)` replaced by `e`
    pub(in crate::pdr::solver) fn split_first_ite_anywhere(
        expr: &ChcExpr,
    ) -> Option<(ChcExpr, ChcExpr, ChcExpr)> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => Some((
                args[0].as_ref().clone(),
                args[1].as_ref().clone(),
                args[2].as_ref().clone(),
            )),
            ChcExpr::Op(op, args) => {
                for (i, arg) in args.iter().enumerate() {
                    if let Some((cond, then_sub, else_sub)) = Self::split_first_ite_anywhere(arg) {
                        let mut then_args: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
                        let mut else_args: Vec<Arc<ChcExpr>> = Vec::with_capacity(args.len());
                        for (j, a) in args.iter().enumerate() {
                            if i == j {
                                then_args.push(Arc::new(then_sub.clone()));
                                else_args.push(Arc::new(else_sub.clone()));
                            } else {
                                then_args.push(a.clone());
                                else_args.push(a.clone());
                            }
                        }
                        return Some((
                            cond,
                            ChcExpr::Op(*op, then_args),
                            ChcExpr::Op(*op, else_args),
                        ));
                    }
                }
                None
            }
            _ => None,
        })
    }

    /// If `expr` contains an ITE, split into two guarded cases. Otherwise return `None`.
    pub(in crate::pdr) fn split_ite_cases_anywhere(expr: &ChcExpr) -> Option<[ChcExpr; 2]> {
        let (cond, then_expr, else_expr) = Self::split_first_ite_anywhere(expr)?;
        Some([
            ChcExpr::and(then_expr, cond.clone()),
            ChcExpr::and(else_expr, ChcExpr::not(cond)),
        ])
    }

    /// Run `check_sat` with recursive case-split fallback on `Unknown`.
    ///
    /// Returns `(result, query_used_for_sat)` where `query_used_for_sat` is populated only when
    /// the fallback finds `Sat` using a split query (useful for cube extraction).
    ///
    /// The recursive case-split handles queries with multiple ITEs (e.g., mode-dispatch patterns
    /// like `I = ite(J=1, E+F, E)` combined with arithmetic). When a single split returns Unknown,
    /// we recursively split up to `MAX_ITE_SPLIT_DEPTH` levels.
    pub(in crate::pdr) fn check_sat_with_ite_case_split(
        smt: &mut SmtContext,
        verbose: bool,
        query: &ChcExpr,
    ) -> (SmtResult, Option<ChcExpr>) {
        // Depth limit to prevent exponential blowup.
        // - ITE and disequality splits are binary (2^depth max cases)
        // - OR splits can be wider; we cap branch counts below.
        const MAX_ITE_SPLIT_DEPTH: u8 = 3;

        let (result, sat_query) = Self::check_sat_with_ite_case_split_recursive(
            smt,
            verbose,
            query,
            0,
            MAX_ITE_SPLIT_DEPTH,
        );
        if !matches!(result, SmtResult::Unknown) {
            return (result, sat_query);
        }

        // SOUND UNSAT-ONLY FALLBACK for mixed Boolean / modular-arithmetic
        // queries the LIA core stalls on (e.g. loop parity invariants
        // `acc <=> (count mod 2 == 1)`: the negated bool<->mod-equality coupling
        // `not(b <=> (mod x k = c))` returns Unknown). We (1) eliminate `mod`/`div`
        // into Euclidean quotient/remainder constraints (equisatisfiable), then
        // (2) exhaustively case-split the free Boolean variables, deciding each
        // pure-LIA leaf through the existing diseq/ITE case-split. If EVERY leaf
        // is UNSAT the original is UNSAT (the splits partition the model space and
        // mod-elimination preserves satisfiability). Any SAT/Unknown leaf yields
        // Unknown — we never fabricate SAT, so this only ever strengthens an
        // Unknown into a sound UNSAT.
        if let Some(decided) = Self::decide_bool_mod_unsat(smt, verbose, query) {
            return (decided, None);
        }

        (result, sat_query)
    }

    /// Maximum number of free Boolean variables to exhaustively case-split in
    /// [`Self::decide_bool_mod_unsat`]. 8 vars = 256 leaves worst case; loop
    /// parity/flag invariants have very few Boolean state vars.
    const MAX_BOOL_SPLIT_VARS: usize = 8;

    /// Sound UNSAT-only decision via `mod`/`div` elimination + exhaustive
    /// Boolean case-split. Returns `Some(SmtResult::Unsat)` iff every Boolean
    /// assignment makes the (mod-eliminated) query UNSAT under the diseq/ITE
    /// case-split; otherwise `None` (caller keeps its Unknown). Never returns
    /// SAT — proving SAT here would need a reconstructed model, and the inductive
    /// soundness direction only needs UNSAT.
    fn decide_bool_mod_unsat(
        smt: &mut SmtContext,
        verbose: bool,
        query: &ChcExpr,
    ) -> Option<SmtResult> {
        const MAX_ITE_SPLIT_DEPTH: u8 = 3;
        // Only worth it when the stall-inducing structure is present.
        if !query.contains_mod_or_div() {
            return None;
        }
        let mod_free = query.eliminate_mod();

        fn first_bool_var(e: &ChcExpr) -> Option<ChcVar> {
            e.vars()
                .into_iter()
                .find(|v| matches!(v.sort, ChcSort::Bool))
        }

        // Returns Some(true)=UNSAT-proven, Some(false)=SAT/inconclusive (not all
        // UNSAT), None=budget/var-cap exceeded (treat as inconclusive).
        fn all_leaves_unsat(
            smt: &mut SmtContext,
            verbose: bool,
            e: &ChcExpr,
            depth: usize,
            max_depth: u8,
        ) -> Option<bool> {
            if let ChcExpr::Bool(b) = e {
                return Some(!*b);
            }
            match first_bool_var(e) {
                Some(bv) if depth < PdrSolver::MAX_BOOL_SPLIT_VARS => {
                    for val in [false, true] {
                        let leaf = e
                            .substitute(&[(bv.clone(), ChcExpr::Bool(val))])
                            .simplify_constants();
                        match all_leaves_unsat(smt, verbose, &leaf, depth + 1, max_depth) {
                            Some(true) => {}                   // this leaf UNSAT, keep going
                            Some(false) => return Some(false), // a leaf is SAT/incon
                            None => return None,               // budget exceeded
                        }
                    }
                    Some(true)
                }
                Some(_) => None, // too many bool vars to split exhaustively
                None => {
                    // Pure (mod-free) LIA leaf: diseq/ITE case-split decides it.
                    let (r, _) = PdrSolver::check_sat_with_ite_case_split_recursive(
                        smt, verbose, e, 0, max_depth,
                    );
                    match r {
                        SmtResult::Unsat
                        | SmtResult::UnsatWithCore(_)
                        | SmtResult::UnsatWithFarkas(_) => Some(true),
                        SmtResult::Sat(_) => Some(false),
                        SmtResult::Unknown => None,
                    }
                }
            }
        }

        match all_leaves_unsat(smt, verbose, &mod_free, 0, MAX_ITE_SPLIT_DEPTH) {
            Some(true) => Some(SmtResult::Unsat),
            _ => None,
        }
    }

    /// Recursive helper for ITE case-split. Tracks depth to bound case exploration.
    pub(in crate::pdr::solver) fn check_sat_with_ite_case_split_recursive(
        smt: &mut SmtContext,
        verbose: bool,
        query: &ChcExpr,
        depth: u8,
        max_depth: u8,
    ) -> (SmtResult, Option<ChcExpr>) {
        // Per-call timeout to prevent indefinite hangs (#3237).
        // Without this, callers like is_self_inductive_blocking_uncached can block
        // forever on mod-arithmetic formulas where the LIA solver stalls.
        // If the caller already set a scoped timeout on the SmtContext, respect it;
        // otherwise use a 2-second default (matching the mod-elimination retry timeout).
        const DEFAULT_PER_CALL_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(2);

        #[cfg(test)]
        record_case_split_timeout_for_tests(smt.current_timeout());

        // Engine budget enforcement: once the thread's SMT deadline expires,
        // stop splitting immediately. Without this check the 8-way OR split
        // at depth 3 can issue hundreds of (now pointless) leaf checks.
        if crate::smt::smt_deadline_expired() {
            return (SmtResult::Unknown, None);
        }

        smt.reset();
        let result = if let Some(timeout) = smt.current_timeout() {
            smt.check_sat_with_timeout(query, timeout)
        } else {
            smt.check_sat_with_timeout(query, DEFAULT_PER_CALL_TIMEOUT)
        };
        if !matches!(result, SmtResult::Unknown) {
            return (result, None);
        }

        // Depth limit reached - cannot split further
        if depth >= max_depth {
            return (SmtResult::Unknown, None);
        }

        // Prefer splitting ITEs. If none are present, fall back to:
        // - splitting a single OR under top-level conjuncts (common in CHC encodings)
        // - splitting a single disequality (not (= a b)) into (< a b) / (> a b)
        //
        // These are workarounds for AY's SMT solver returning Unknown on disjunctive
        // and disequality-heavy LIA queries (e.g., `three_dots_moving_2`).
        const MAX_OR_SPLIT_CASES: usize = 8;
        const MAX_DISEQ_SPLIT_CANDIDATES: usize = 4;

        let (split_kind, split_cases) =
            if let Some([then_case, else_case]) = Self::split_ite_cases_anywhere(query) {
                ("ITE", vec![then_case, else_case])
            } else {
                let or_cases = Self::extract_or_cases_from_constraint(query);
                if or_cases.len() > 1 && or_cases.len() <= MAX_OR_SPLIT_CASES {
                    ("OR", or_cases)
                } else {
                    let diseqs = Self::extract_disequalities(query);
                    if diseqs.is_empty() || diseqs.len() > MAX_DISEQ_SPLIT_CANDIDATES {
                        return (SmtResult::Unknown, None);
                    }
                    let (lhs, rhs) = &diseqs[0];
                    (
                        "DISEQ",
                        vec![
                            query.replace_diseq(lhs, rhs, ChcExpr::lt(lhs.clone(), rhs.clone())),
                            query.replace_diseq(lhs, rhs, ChcExpr::gt(lhs.clone(), rhs.clone())),
                        ],
                    )
                }
            };

        if verbose && depth == 0 {
            safe_eprintln!("  SMT returned Unknown; trying {split_kind} case-split");
        }

        let mut any_unknown = false;
        for case_query in split_cases {
            // Recursively check each case with increased depth
            let (case_result, sat_query) = Self::check_sat_with_ite_case_split_recursive(
                smt,
                verbose,
                &case_query,
                depth + 1,
                max_depth,
            );
            match case_result {
                SmtResult::Sat(model) => {
                    return (SmtResult::Sat(model), sat_query.or(Some(case_query)));
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                SmtResult::Unknown => any_unknown = true,
            }
        }

        if any_unknown {
            (SmtResult::Unknown, None)
        } else {
            (SmtResult::Unsat, None)
        }
    }

    /// Find an ITE expression in an equality context: (= var (ite cond then else))
    pub(in crate::pdr::solver) fn find_ite_equality(
        expr: &ChcExpr,
    ) -> Option<(String, ChcExpr, ChcExpr, ChcExpr)> {
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(result) = Self::find_ite_equality(arg) {
                        return Some(result);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check (= var (ite ...))
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if let ChcExpr::Op(ChcOp::Ite, ite_args) = args[1].as_ref() {
                        if ite_args.len() == 3 {
                            return Some((
                                v.name.clone(),
                                ite_args[0].as_ref().clone(),
                                ite_args[1].as_ref().clone(),
                                ite_args[2].as_ref().clone(),
                            ));
                        }
                    }
                }
                // Check (= (ite ...) var)
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if let ChcExpr::Op(ChcOp::Ite, ite_args) = args[0].as_ref() {
                        if ite_args.len() == 3 {
                            return Some((
                                v.name.clone(),
                                ite_args[0].as_ref().clone(),
                                ite_args[1].as_ref().clone(),
                                ite_args[2].as_ref().clone(),
                            ));
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Substitute ITE with a specific branch and add the condition as a conjunct.
    pub(in crate::pdr::solver) fn substitute_ite_case(
        constraint: &ChcExpr,
        var: &str,
        value: &ChcExpr,
        cond: &ChcExpr,
        is_then: bool,
    ) -> ChcExpr {
        // Build the replacement equality: (= var value)
        let value_eq = ChcExpr::eq(
            ChcExpr::Var(ChcVar::new(var.to_string(), ChcSort::Int)),
            value.clone(),
        );

        // Build the condition: cond (for then) or (not cond) (for else)
        let cond_constraint = if is_then {
            cond.clone()
        } else {
            ChcExpr::not(cond.clone())
        };

        // Filter out the original ITE equality and add the new equality + condition
        let new_constraint = Self::replace_ite_equality_with(constraint, var, &value_eq);
        ChcExpr::and(new_constraint, cond_constraint)
    }

    /// Replace the ITE equality for a variable with a new equality.
    pub(in crate::pdr::solver) fn replace_ite_equality_with(
        expr: &ChcExpr,
        var: &str,
        replacement: &ChcExpr,
    ) -> ChcExpr {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|arg| Arc::new(Self::replace_ite_equality_with(arg, var, replacement)))
                    .collect();
                ChcExpr::Op(ChcOp::And, new_args)
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check if this is the ITE equality for the variable
                let is_target = match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::Op(ChcOp::Ite, _)) => v.name == var,
                    (ChcExpr::Op(ChcOp::Ite, _), ChcExpr::Var(v)) => v.name == var,
                    _ => false,
                };
                if is_target {
                    replacement.clone()
                } else {
                    expr.clone()
                }
            }
            _ => expr.clone(),
        })
    }
}
