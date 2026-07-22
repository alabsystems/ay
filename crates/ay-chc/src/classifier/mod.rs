// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Problem classification for adaptive portfolio strategy selection.
//!
//! This module extracts features from CHC problems to classify them
//! and select the best solving strategy. The goal is to predict which
//! engine will work best, budget time accordingly, and return gracefully
//! before external timeouts.
//!
//! # Problem Classes
//!
//! - **Trivial**: <5 clauses, 1 predicate, no cycles -> direct PDR, <0.5s expected
//! - **SimpleLoop**: Single predicate, linear, single transition -> TPA primary
//! - **ComplexLoop**: Single predicate, complex structure -> PDR primary
//! - **MultiPredLinear**: Multiple predicates, linear -> PDR with decomposition
//! - **MultiPredComplex**: Hyperedge structure -> PDR with splits
//!
//! # Reference
//!
//! Part of #1868 - Adaptive portfolio for 30s bounded execution.
//! See the development design notes for full design.

use crate::{pdr::scc::tarjan_scc, ChcExpr, ChcOp, ChcProblem, ChcSort};

/// Extracted features from a CHC problem.
#[derive(Debug, Clone)]
pub(crate) struct ProblemFeatures {
    /// Number of predicates declared
    pub(crate) num_predicates: usize,
    /// Number of clauses
    pub(crate) num_clauses: usize,
    /// Each clause has at most one body predicate
    pub(crate) is_linear: bool,
    /// Only one predicate exists (classic transition system)
    pub(crate) is_single_predicate: bool,
    /// Predicate dependency graph has cycles (SCC analysis)
    pub(crate) has_cycles: bool,
    /// Number of SCCs in the predicate dependency graph
    pub(crate) scc_count: usize,
    /// Size of the largest SCC in the predicate dependency graph
    pub(crate) max_scc_size: usize,
    /// Longest path length in the SCC condensation DAG
    pub(crate) dag_depth: usize,
    /// Any Array sort in predicate signatures
    pub(crate) uses_arrays: bool,
    /// Any Real sort in predicate signatures
    pub(crate) uses_real: bool,
    /// Number of transition clauses (neither facts nor queries)
    pub(crate) num_transitions: usize,
    /// Number of fact clauses (no body predicates, predicate head)
    pub(crate) num_facts: usize,
    /// Number of query clauses (False head)
    pub(crate) num_queries: usize,
    /// Maximum number of distinct variables in a single clause
    pub(crate) max_clause_variables: usize,
    /// Mean number of distinct variables per clause
    pub(crate) mean_clause_variables: f64,
    /// Any arithmetic multiplication term in clause constraints
    pub(crate) has_multiplication: bool,
    /// Any arithmetic mod/div term in clause constraints
    pub(crate) has_mod_div: bool,
    /// Any if-then-else term in clause constraints
    pub(crate) has_ite: bool,
    /// Fraction of transition clauses that are self-loops
    pub(crate) self_loop_ratio: f64,
    /// Maximum predicate arity across all declared predicates
    pub(crate) max_predicate_arity: usize,
    /// All clauses are entry->exit only (queries with no body predicates).
    /// Reference: Golem's `isTrivial()` in TransformationUtils.cc:284-290
    pub(crate) is_entry_exit_only: bool,
    /// Phase-bounded depth: if `Some(depth)`, the problem has a phase counter
    /// argument that monotonically increases across all transitions, making it
    /// safe to solve with BMC at depth `depth` with `acyclic_safe=true`.
    /// Common in model-checker-consumer-generated CHC for phased Rust program execution (#7897).
    pub(crate) phase_bounded_depth: Option<usize>,
    /// Any Datatype sort in predicate signatures.
    ///
    /// When true, the problem uses algebraic datatypes (e.g., `Option<u8>`,
    /// newtype structs). DT problems need SMT-level constructor/selector
    /// reasoning; LIA generalization escalation and k-induction via SingleLoop
    /// are unproductive. Used to skip Kind and cap PDR escalation (#7930).
    pub(crate) uses_datatypes: bool,
    /// CHC-COMP triangle/location first-sample shape: 3-4 predicates, arity
    /// 12, scalar Int or BV32 arguments, and conjunctions of difference-bound
    /// constraints, including the multi-body closure/query rules in the first
    /// smoke samples. This keeps the family out of the generic MultiPredComplex
    /// timeout lane while a dedicated specialist is developed.
    pub(crate) is_triangle_location_diff_bounds: bool,
    /// Classified problem class
    pub(crate) class: ProblemClass,
}

/// Classification of CHC problem structure for strategy selection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProblemClass {
    /// No predicates needed - all clauses are entry->exit only.
    /// This means all queries are facts (no predicate in body).
    /// Solved with single SMT satisfiability check.
    /// Reference: Golem's `isTrivial()` in TransformationUtils.cc:284-290
    EntryExitOnly,
    /// <5 clauses, 1 predicate, no cycles
    /// Expected: <0.5s with any engine
    Trivial,
    /// Single predicate, linear, single transition
    /// Best: TPA (transition power abstraction)
    SimpleLoop,
    /// Single predicate, multiple transitions or non-linear constraints
    /// Best: PDR with generalization
    ComplexLoop,
    /// Multiple predicates, linear (graph structure)
    /// Best: PDR with potential decomposition
    MultiPredLinear,
    /// Multiple predicates, hyperedges (multi-body clauses)
    /// Best: PDR with negated equality splits
    MultiPredComplex,
}

impl std::fmt::Display for ProblemClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EntryExitOnly => write!(f, "EntryExitOnly"),
            Self::Trivial => write!(f, "Trivial"),
            Self::SimpleLoop => write!(f, "SimpleLoop"),
            Self::ComplexLoop => write!(f, "ComplexLoop"),
            Self::MultiPredLinear => write!(f, "MultiPredLinear"),
            Self::MultiPredComplex => write!(f, "MultiPredComplex"),
        }
    }
}

/// Problem classifier for CHC solving strategy selection.
pub(crate) struct ProblemClassifier;

#[derive(Debug, Clone, Copy, Default)]
struct ConstraintFeatures {
    has_multiplication: bool,
    has_mod_div: bool,
    has_ite: bool,
}

impl ConstraintFeatures {
    fn all_set(self) -> bool {
        self.has_multiplication && self.has_mod_div && self.has_ite
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct ClauseFeatures {
    num_transitions: usize,
    num_facts: usize,
    num_queries: usize,
    max_clause_variables: usize,
    mean_clause_variables: f64,
    has_multiplication: bool,
    has_mod_div: bool,
    has_ite: bool,
    self_loop_ratio: f64,
}

#[derive(Debug, Clone, Copy, Default)]
struct DependencyGraphFeatures {
    has_cycles: bool,
    scc_count: usize,
    max_scc_size: usize,
    dag_depth: usize,
}

impl ProblemClassifier {
    /// Classify a CHC problem and extract features.
    ///
    /// This runs in O(|clauses| + |predicates|) time and should complete
    /// in <100ms even for large problems.
    pub(crate) fn classify(problem: &ChcProblem) -> ProblemFeatures {
        let num_predicates = problem.predicates().len();
        let num_clauses = problem.clauses().len();

        // Check linearity: each clause has at most one body predicate
        let is_linear = problem
            .clauses()
            .iter()
            .all(|c| c.body.predicates.len() <= 1);

        let is_single_predicate = num_predicates == 1;

        // Summarize the predicate dependency graph.
        let dependency_graph = Self::analyze_dependency_graph(problem);

        // Check for array/real sorts
        let (uses_arrays, uses_real) = Self::check_sorts(problem);

        // Count clause types and scan clause/constraint-level features.
        let clause_features = Self::analyze_clauses(problem);

        let max_predicate_arity = problem
            .predicates()
            .iter()
            .map(|pred| pred.arity())
            .max()
            .unwrap_or(0);

        // Check for entry-exit-only pattern (Golem's isTrivial)
        let is_entry_exit_only = Self::is_entry_exit_only(problem);

        // Detect phase-bounded problems (#7897)
        let phase_bounded_depth = problem.detect_phase_bounded_depth();

        // Check for datatype sorts in predicate signatures (#7930).
        let uses_datatypes = problem.has_datatype_sorts();

        // Detect CHC-COMP triangle/location diff-bound first samples (#9698).
        let is_triangle_location_diff_bounds =
            Self::is_triangle_location_diff_bounds(problem, uses_arrays, uses_real, uses_datatypes);

        // Determine class
        let class = Self::determine_class(
            num_predicates,
            num_clauses,
            clause_features.num_transitions,
            is_linear,
            is_single_predicate,
            dependency_graph.has_cycles,
            is_entry_exit_only,
            is_triangle_location_diff_bounds,
        );

        ProblemFeatures {
            num_predicates,
            num_clauses,
            is_linear,
            is_single_predicate,
            has_cycles: dependency_graph.has_cycles,
            scc_count: dependency_graph.scc_count,
            max_scc_size: dependency_graph.max_scc_size,
            dag_depth: dependency_graph.dag_depth,
            uses_arrays,
            uses_real,
            num_transitions: clause_features.num_transitions,
            num_facts: clause_features.num_facts,
            num_queries: clause_features.num_queries,
            max_clause_variables: clause_features.max_clause_variables,
            mean_clause_variables: clause_features.mean_clause_variables,
            has_multiplication: clause_features.has_multiplication,
            has_mod_div: clause_features.has_mod_div,
            has_ite: clause_features.has_ite,
            self_loop_ratio: clause_features.self_loop_ratio,
            max_predicate_arity,
            is_entry_exit_only,
            phase_bounded_depth,
            uses_datatypes,
            is_triangle_location_diff_bounds,
            class,
        }
    }

    /// Compute SCC-based dependency graph features.
    fn analyze_dependency_graph(problem: &ChcProblem) -> DependencyGraphFeatures {
        let scc_info = tarjan_scc(problem);
        let scc_count = scc_info.sccs.len();

        if scc_count == 0 {
            return DependencyGraphFeatures::default();
        }

        let dependency_edges = problem.dependency_edges_ignoring_tautological_self_loops();
        let has_cycles =
            Self::dependency_edges_have_cycle(problem.predicates().len(), &dependency_edges);
        let max_scc_size = scc_info
            .sccs
            .iter()
            .map(|scc| scc.predicates.len())
            .max()
            .unwrap_or(0);

        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); scc_count];
        let mut in_degree = vec![0usize; scc_count];

        for (from_pred, to_pred) in dependency_edges {
            let Some(&from_scc) = scc_info.predicate_to_scc.get(&from_pred) else {
                continue;
            };
            let Some(&to_scc) = scc_info.predicate_to_scc.get(&to_pred) else {
                continue;
            };

            if from_scc != to_scc && !adj[from_scc].contains(&to_scc) {
                adj[from_scc].push(to_scc);
                in_degree[to_scc] += 1;
            }
        }

        let mut queue: Vec<_> = (0..scc_count).filter(|i| in_degree[*i] == 0).collect();
        let mut depth = vec![1usize; scc_count];
        let mut dag_depth = 1usize;

        while let Some(scc_idx) = queue.pop() {
            dag_depth = dag_depth.max(depth[scc_idx]);
            for &next in &adj[scc_idx] {
                depth[next] = depth[next].max(depth[scc_idx] + 1);
                in_degree[next] -= 1;
                if in_degree[next] == 0 {
                    queue.push(next);
                }
            }
        }

        DependencyGraphFeatures {
            has_cycles,
            scc_count,
            max_scc_size,
            dag_depth,
        }
    }

    fn dependency_edges_have_cycle(
        num_predicates: usize,
        edges: &[(crate::PredicateId, crate::PredicateId)],
    ) -> bool {
        let mut in_degree = vec![0usize; num_predicates];
        let mut adj: Vec<Vec<crate::PredicateId>> = vec![Vec::new(); num_predicates];

        for &(from, to) in edges {
            adj[from.index()].push(to);
            in_degree[to.index()] += 1;
        }

        let mut queue: Vec<_> = (0..num_predicates)
            .filter(|i| in_degree[*i] == 0)
            .map(|i| crate::PredicateId::new(i as u32))
            .collect();
        let mut visited = 0usize;

        while let Some(node) = queue.pop() {
            visited += 1;
            for &next in &adj[node.index()] {
                in_degree[next.index()] -= 1;
                if in_degree[next.index()] == 0 {
                    queue.push(next);
                }
            }
        }

        visited != num_predicates
    }

    /// Compute clause-level counts and constraint-derived features.
    fn analyze_clauses(problem: &ChcProblem) -> ClauseFeatures {
        let mut num_transitions = 0usize;
        let mut num_facts = 0usize;
        let mut num_queries = 0usize;
        let mut max_clause_variables = 0usize;
        let mut total_clause_variables = 0usize;
        let mut has_multiplication = false;
        let mut has_mod_div = false;
        let mut has_ite = false;
        let mut self_loops = 0usize;

        for clause in problem.clauses() {
            let clause_variables = clause.vars().len();
            max_clause_variables = max_clause_variables.max(clause_variables);
            total_clause_variables += clause_variables;

            if let Some(constraint) = &clause.body.constraint {
                let constraint_features = Self::scan_constraint_features(constraint);
                has_multiplication |= constraint_features.has_multiplication;
                has_mod_div |= constraint_features.has_mod_div;
                has_ite |= constraint_features.has_ite;
            }

            if clause.is_query() {
                num_queries += 1;
            } else if clause.body.predicates.is_empty() {
                num_facts += 1;
            } else {
                num_transitions += 1;
                if let Some(head_pred) = clause.head.predicate_id() {
                    if clause
                        .body
                        .predicates
                        .iter()
                        .any(|(body_pred, _)| *body_pred == head_pred)
                    {
                        self_loops += 1;
                    }
                }
            }
        }

        let num_clauses = problem.clauses().len();
        let mean_clause_variables = if num_clauses == 0 {
            0.0
        } else {
            total_clause_variables as f64 / num_clauses as f64
        };
        let self_loop_ratio = if num_transitions == 0 {
            0.0
        } else {
            self_loops as f64 / num_transitions as f64
        };

        ClauseFeatures {
            num_transitions,
            num_facts,
            num_queries,
            max_clause_variables,
            mean_clause_variables,
            has_multiplication,
            has_mod_div,
            has_ite,
            self_loop_ratio,
        }
    }

    /// Scan a clause constraint for arithmetic and control-flow operators.
    fn scan_constraint_features(expr: &ChcExpr) -> ConstraintFeatures {
        let mut features = ConstraintFeatures::default();
        let mut stack = vec![expr];

        while let Some(current) = stack.pop() {
            match current {
                ChcExpr::Op(op, args) => {
                    match op {
                        ChcOp::Mul => features.has_multiplication = true,
                        ChcOp::Div | ChcOp::Mod => features.has_mod_div = true,
                        ChcOp::Ite => features.has_ite = true,
                        _ => {}
                    }
                    if features.all_set() {
                        break;
                    }
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::ConstArray(_, value) => stack.push(value.as_ref()),
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
        }

        features
    }

    /// Check for array and real sorts in predicate signatures.
    fn check_sorts(problem: &ChcProblem) -> (bool, bool) {
        let mut uses_arrays = false;
        let mut uses_real = false;

        for pred in problem.predicates() {
            for sort in &pred.arg_sorts {
                Self::check_sort_recursive(sort, &mut uses_arrays, &mut uses_real);
            }
        }

        (uses_arrays, uses_real)
    }

    fn check_sort_recursive(sort: &ChcSort, uses_arrays: &mut bool, uses_real: &mut bool) {
        match sort {
            ChcSort::Array(k, v) => {
                *uses_arrays = true;
                Self::check_sort_recursive(k, uses_arrays, uses_real);
                Self::check_sort_recursive(v, uses_arrays, uses_real);
            }
            ChcSort::Real => {
                *uses_real = true;
            }
            ChcSort::Int
            | ChcSort::Bool
            | ChcSort::BitVec(_)
            | ChcSort::Uninterpreted(_)
            | ChcSort::Datatype { .. } => {}
        }
    }

    /// Check if problem has only entry->exit edges (Golem's isTrivial pattern).
    ///
    /// A problem is entry-exit-only if ALL clauses are queries (false head)
    /// with no body predicates. This means there are no intermediate predicates
    /// and the problem reduces to satisfiability checking.
    ///
    /// Reference: Golem's `isTrivial()` in TransformationUtils.cc:284-290
    fn is_entry_exit_only(problem: &ChcProblem) -> bool {
        // Must have at least one clause
        if problem.clauses().is_empty() {
            return false;
        }

        // All clauses must be queries (false head) with no body predicates
        problem.clauses().iter().all(|c| {
            // Must be a query (false head)
            c.is_query() &&
            // Must have no body predicates (only constraints)
            c.body.predicates.is_empty()
        })
    }

    fn is_triangle_location_diff_bounds(
        problem: &ChcProblem,
        uses_arrays: bool,
        uses_real: bool,
        uses_datatypes: bool,
    ) -> bool {
        let predicates = problem.predicates();
        let triangle_predicates: Vec<_> = predicates
            .iter()
            .filter(|pred| pred.arity() == 12)
            .collect();
        if !(3..=6).contains(&triangle_predicates.len())
            || problem.clauses().is_empty()
            || uses_arrays
            || uses_real
            || uses_datatypes
        {
            return false;
        }

        if predicates
            .iter()
            .any(|pred| pred.arity() != 12 && pred.arity() != 0)
        {
            return false;
        }

        let Some(theory) = Self::triangle_location_theory(&triangle_predicates) else {
            return false;
        };

        let mut saw_query = false;
        let mut saw_multi_body_clause = false;
        let mut saw_constraint = false;

        for clause in problem.clauses() {
            saw_query |= clause.is_query()
                || clause
                    .head
                    .predicate_id()
                    .and_then(|id| problem.get_predicate(id))
                    .is_some_and(|pred| pred.arity() == 0);
            saw_multi_body_clause |= clause.body.predicates.len() > 1;

            for (body_pred, args) in &clause.body.predicates {
                let Some(pred) = problem.get_predicate(*body_pred) else {
                    return false;
                };
                if pred.arity() == 0 {
                    if !args.is_empty() {
                        return false;
                    }
                } else if args.len() != 12
                    || args
                        .iter()
                        .any(|arg| !Self::is_triangle_location_term(arg, theory))
                {
                    return false;
                }
            }

            if let Some(constraint) = &clause.body.constraint {
                saw_constraint = true;
                if !Self::is_diff_bound_constraint(constraint, theory) {
                    return false;
                }
            }

            if let crate::ClauseHead::Predicate(head_pred, args) = &clause.head {
                let Some(pred) = problem.get_predicate(*head_pred) else {
                    return false;
                };
                if pred.arity() == 0 {
                    if !args.is_empty() {
                        return false;
                    }
                } else if args.len() != 12
                    || args
                        .iter()
                        .any(|arg| !Self::is_triangle_location_term(arg, theory))
                {
                    return false;
                }
            }
        }

        saw_query && saw_multi_body_clause && saw_constraint
    }

    fn triangle_location_theory(
        predicates: &[&crate::Predicate],
    ) -> Option<TriangleLocationTheory> {
        let mut saw_int = false;
        let mut saw_bv32 = false;

        for pred in predicates {
            for sort in &pred.arg_sorts {
                match sort {
                    ChcSort::Int => saw_int = true,
                    ChcSort::BitVec(32) => saw_bv32 = true,
                    _ => return None,
                }
            }
        }

        match (saw_int, saw_bv32) {
            (true, false) => Some(TriangleLocationTheory::Int),
            (false, true) => Some(TriangleLocationTheory::Bv32),
            _ => None,
        }
    }

    fn is_diff_bound_constraint(expr: &ChcExpr, theory: TriangleLocationTheory) -> bool {
        match expr {
            ChcExpr::Bool(_) => true,
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .all(|arg| Self::is_diff_bound_constraint(arg.as_ref(), theory)),
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                Self::is_diff_bound_atom(args[0].as_ref(), theory)
            }
            _ => Self::is_diff_bound_atom(expr, theory),
        }
    }

    fn is_diff_bound_atom(expr: &ChcExpr, theory: TriangleLocationTheory) -> bool {
        let ChcExpr::Op(op, args) = expr else {
            return false;
        };
        if args.len() != 2 || !Self::is_triangle_location_comparison(*op, theory) {
            return false;
        }

        let Some(mut coeffs) = Self::linear_coefficients(args[0].as_ref(), theory) else {
            return false;
        };
        let Some(rhs_coeffs) = Self::linear_coefficients(args[1].as_ref(), theory) else {
            return false;
        };

        for (var, coeff) in rhs_coeffs {
            Self::add_linear_coeff(&mut coeffs, var, -coeff);
        }
        Self::is_difference_bound_coefficients(&coeffs)
    }

    fn is_triangle_location_comparison(op: ChcOp, theory: TriangleLocationTheory) -> bool {
        match theory {
            TriangleLocationTheory::Int => {
                matches!(
                    op,
                    ChcOp::Eq | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                )
            }
            TriangleLocationTheory::Bv32 => matches!(
                op,
                ChcOp::Eq
                    | ChcOp::BvULt
                    | ChcOp::BvULe
                    | ChcOp::BvUGt
                    | ChcOp::BvUGe
                    | ChcOp::BvSLt
                    | ChcOp::BvSLe
                    | ChcOp::BvSGt
                    | ChcOp::BvSGe
            ),
        }
    }

    fn is_triangle_location_term(expr: &ChcExpr, theory: TriangleLocationTheory) -> bool {
        Self::linear_coefficients(expr, theory).is_some()
    }

    fn linear_coefficients(
        expr: &ChcExpr,
        theory: TriangleLocationTheory,
    ) -> Option<Vec<(crate::ChcVar, i32)>> {
        match expr {
            ChcExpr::Int(_) if theory == TriangleLocationTheory::Int => Some(Vec::new()),
            ChcExpr::BitVec(_, 32) if theory == TriangleLocationTheory::Bv32 => Some(Vec::new()),
            ChcExpr::Var(var) if Self::var_matches_triangle_theory(var, theory) => {
                Some(vec![(var.clone(), 1)])
            }
            ChcExpr::Op(op, args) if Self::is_linear_add_op(*op, theory) => {
                let mut coeffs = Vec::new();
                for arg in args {
                    for (var, coeff) in Self::linear_coefficients(arg.as_ref(), theory)? {
                        Self::add_linear_coeff(&mut coeffs, var, coeff);
                    }
                }
                Some(coeffs)
            }
            ChcExpr::Op(op, args) if Self::is_linear_sub_op(*op, theory) && !args.is_empty() => {
                let mut coeffs = Vec::new();
                for (index, arg) in args.iter().enumerate() {
                    let sign = if index == 0 { 1 } else { -1 };
                    for (var, coeff) in Self::linear_coefficients(arg.as_ref(), theory)? {
                        Self::add_linear_coeff(&mut coeffs, var, sign * coeff);
                    }
                }
                Some(coeffs)
            }
            ChcExpr::Op(ChcOp::Mul, args) if theory == TriangleLocationTheory::Int => {
                Self::int_mul_coefficients(args)
            }
            ChcExpr::Op(ChcOp::BvMul, args) if theory == TriangleLocationTheory::Bv32 => {
                Self::bv32_mul_coefficients(args)
            }
            ChcExpr::Op(op, args) if Self::is_linear_neg_op(*op, theory) && args.len() == 1 => {
                let mut coeffs = Vec::new();
                for (var, coeff) in Self::linear_coefficients(args[0].as_ref(), theory)? {
                    Self::add_linear_coeff(&mut coeffs, var, -coeff);
                }
                Some(coeffs)
            }
            _ => None,
        }
    }

    fn int_mul_coefficients(args: &[std::sync::Arc<ChcExpr>]) -> Option<Vec<(crate::ChcVar, i32)>> {
        let mut scalar = 1i32;
        let mut non_constant: Option<&ChcExpr> = None;

        for arg in args {
            if let Some(value) = arg.as_i64() {
                scalar = scalar.checked_mul(i32::try_from(value).ok()?)?;
            } else if non_constant.replace(arg.as_ref()).is_some() {
                return None;
            }
        }

        let Some(expr) = non_constant else {
            return Some(Vec::new());
        };
        let coeffs = Self::linear_coefficients(expr, TriangleLocationTheory::Int)?;
        Self::scale_coefficients(coeffs, scalar)
    }

    fn bv32_mul_coefficients(
        args: &[std::sync::Arc<ChcExpr>],
    ) -> Option<Vec<(crate::ChcVar, i32)>> {
        let mut scalar = 1i32;
        let mut non_constant: Option<&ChcExpr> = None;

        for arg in args {
            if let Some(value) = Self::bv32_signed_unit(arg.as_ref()) {
                scalar = scalar.checked_mul(value)?;
            } else if non_constant.replace(arg.as_ref()).is_some() {
                return None;
            }
        }

        let Some(expr) = non_constant else {
            return Some(Vec::new());
        };
        let coeffs = Self::linear_coefficients(expr, TriangleLocationTheory::Bv32)?;
        Self::scale_coefficients(coeffs, scalar)
    }

    fn bv32_signed_unit(expr: &ChcExpr) -> Option<i32> {
        let ChcExpr::BitVec(value, 32) = expr else {
            return None;
        };
        match *value {
            0 => Some(0),
            1 => Some(1),
            0xffff_ffff => Some(-1),
            _ => None,
        }
    }

    fn scale_coefficients(
        coeffs: Vec<(crate::ChcVar, i32)>,
        scalar: i32,
    ) -> Option<Vec<(crate::ChcVar, i32)>> {
        if scalar == 0 {
            return Some(Vec::new());
        }
        coeffs
            .into_iter()
            .map(|(var, coeff)| coeff.checked_mul(scalar).map(|scaled| (var, scaled)))
            .collect()
    }

    fn var_matches_triangle_theory(var: &crate::ChcVar, theory: TriangleLocationTheory) -> bool {
        match (&var.sort, theory) {
            (ChcSort::Int, TriangleLocationTheory::Int) => true,
            (ChcSort::BitVec(32), TriangleLocationTheory::Bv32) => true,
            _ => false,
        }
    }

    fn is_linear_add_op(op: ChcOp, theory: TriangleLocationTheory) -> bool {
        matches!(
            (op, theory),
            (ChcOp::Add, TriangleLocationTheory::Int)
                | (ChcOp::BvAdd, TriangleLocationTheory::Bv32)
        )
    }

    fn is_linear_sub_op(op: ChcOp, theory: TriangleLocationTheory) -> bool {
        matches!(
            (op, theory),
            (ChcOp::Sub, TriangleLocationTheory::Int)
                | (ChcOp::BvSub, TriangleLocationTheory::Bv32)
        )
    }

    fn is_linear_neg_op(op: ChcOp, theory: TriangleLocationTheory) -> bool {
        matches!(
            (op, theory),
            (ChcOp::Neg, TriangleLocationTheory::Int)
                | (ChcOp::BvNeg, TriangleLocationTheory::Bv32)
        )
    }

    fn add_linear_coeff(coeffs: &mut Vec<(crate::ChcVar, i32)>, var: crate::ChcVar, coeff: i32) {
        if coeff == 0 {
            return;
        }
        if let Some((_, existing)) = coeffs
            .iter_mut()
            .find(|(existing_var, _)| *existing_var == var)
        {
            *existing += coeff;
            if *existing == 0 {
                coeffs.retain(|(_, retained_coeff)| *retained_coeff != 0);
            }
        } else {
            coeffs.push((var, coeff));
        }
    }

    fn is_difference_bound_coefficients(coeffs: &[(crate::ChcVar, i32)]) -> bool {
        match coeffs {
            [] => true,
            [(_, coeff)] => coeff.abs() == 1,
            [(_, a), (_, b)] => (*a == 1 && *b == -1) || (*a == -1 && *b == 1),
            _ => false,
        }
    }

    /// Determine problem class based on extracted features.
    fn determine_class(
        _num_predicates: usize,
        num_clauses: usize,
        num_transitions: usize,
        is_linear: bool,
        is_single_predicate: bool,
        has_cycles: bool,
        is_entry_exit_only: bool,
        is_triangle_location_diff_bounds: bool,
    ) -> ProblemClass {
        // EntryExitOnly: simplest case - just SAT checking
        // Reference: Golem's isTrivial()
        if is_entry_exit_only {
            return ProblemClass::EntryExitOnly;
        }

        // Single predicate cases
        if is_single_predicate {
            // SimpleLoop: single transition, no branching
            if num_transitions == 1 && is_linear {
                return ProblemClass::SimpleLoop;
            }

            // Trivial: very small problems with predicates and no transition
            // cycle. Keep this after SimpleLoop so syntactically inert
            // self-loop edges ignored for acyclic analysis do not hide the
            // one-transition loop shape used by BV routing (#9587).
            if num_clauses < 5 && !has_cycles {
                return ProblemClass::Trivial;
            }

            // ComplexLoop: multiple transitions or complex structure
            return ProblemClass::ComplexLoop;
        }

        if is_triangle_location_diff_bounds {
            return ProblemClass::MultiPredLinear;
        }

        // Multi-predicate cases
        if is_linear {
            ProblemClass::MultiPredLinear
        } else {
            ProblemClass::MultiPredComplex
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TriangleLocationTheory {
    Int,
    Bv32,
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
