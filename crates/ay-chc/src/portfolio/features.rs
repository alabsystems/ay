// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// WIP infrastructure for learned algorithm selection (#7915). Not yet
// wired into the decision path. Remove this allow when the feature
// extractor is consumed.
#![allow(dead_code)]

//! Extended CHC feature extraction for learned algorithm selection.
//!
//! This module builds on the base `ProblemClassifier` features with
//! portfolio-specific metrics used by the decision tree to predict
//! which engine (PDR, BMC, TPA, LAWI, Kind, DAR, CEGAR, etc.) will
//! solve a given CHC problem fastest.
//!
//! # Feature Categories
//!
//! 1. **Problem size**: predicates, clauses, variables (from classifier)
//! 2. **Clause body complexity**: conjuncts, disjuncts, nesting depth
//! 3. **Theory classification**: pure LIA, pure BV, mixed, arrays, reals
//! 4. **Graph structure**: linear chain, DAG, single-cycle, multi-cycle
//! 5. **Predicate statistics**: arity distribution, argument sort profile
//!
//! # Design
//!
//! `ChcFeatureVector` wraps the existing `ProblemFeatures` and adds
//! portfolio-specific features. The extraction runs in O(|clauses| * |expr_size|)
//! and should complete in <200ms even for large problems.
//!
//! # Reference
//!
//! Part of #7915 - Learned algorithm selection for CHC.
//! SAT-side analog: `ay-sat/src/features.rs` (SATzilla-style features).

use crate::classifier::{ProblemClass, ProblemClassifier, ProblemFeatures};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort};

// ---------------------------------------------------------------------------
// Theory classification
// ---------------------------------------------------------------------------

/// Background theory used in a CHC problem.
///
/// Determines which SMT theory the constraint logic belongs to, which
/// directly affects which engines can handle it efficiently.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TheoryProfile {
    /// Pure linear integer arithmetic (QF_LIA).
    /// Most engines handle this well; TPA and PDR are strongest.
    PureLia,
    /// Pure bitvector arithmetic (QF_BV).
    /// Requires bitblasting; BV-specialized strategies preferred.
    PureBv,
    /// Integer arithmetic with arrays (QF_ALIA / ALIA).
    /// Array-aware engines (PDR with array MBP) needed.
    LiaArrays,
    /// Bitvector with arrays (QF_ABV).
    /// Requires both bitblasting and array reasoning.
    BvArrays,
    /// Mixed integer and bitvector (QF_UFBV or combined).
    /// May need sort-specific decomposition.
    Mixed,
    /// Pure Boolean (propositional, no arithmetic).
    /// Simple; most engines handle this trivially.
    PureBool,
    /// Contains real arithmetic (QF_LRA or mixed).
    Real,
}

impl std::fmt::Display for TheoryProfile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PureLia => write!(f, "PureLIA"),
            Self::PureBv => write!(f, "PureBV"),
            Self::LiaArrays => write!(f, "LIA+Arrays"),
            Self::BvArrays => write!(f, "BV+Arrays"),
            Self::Mixed => write!(f, "Mixed"),
            Self::PureBool => write!(f, "PureBool"),
            Self::Real => write!(f, "Real"),
        }
    }
}

// ---------------------------------------------------------------------------
// Graph structure classification
// ---------------------------------------------------------------------------

/// Predicate dependency graph structure, summarized for engine selection.
///
/// The graph structure strongly predicts which engines will succeed:
/// - Linear chains: TPA, BMC, and Kind excel
/// - DAGs: Decomposition + PDR works well
/// - Single cycles: PDR is strongest
/// - Multi-cycle: PDR with splits, CEGAR as fallback
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GraphStructure {
    /// No predicates (entry-exit-only or trivial).
    Empty,
    /// Single predicate, self-loop only.
    SelfLoop,
    /// Multiple predicates, no cycles (linear or branching chain).
    AcyclicChain,
    /// Multiple predicates forming a DAG with branching.
    AcyclicDag,
    /// Single cycle involving 2+ predicates.
    SingleCycle,
    /// Multiple cycles or complex strongly-connected structure.
    MultiCycle,
}

impl std::fmt::Display for GraphStructure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "Empty"),
            Self::SelfLoop => write!(f, "SelfLoop"),
            Self::AcyclicChain => write!(f, "AcyclicChain"),
            Self::AcyclicDag => write!(f, "AcyclicDag"),
            Self::SingleCycle => write!(f, "SingleCycle"),
            Self::MultiCycle => write!(f, "MultiCycle"),
        }
    }
}

// ---------------------------------------------------------------------------
// Clause body complexity features
// ---------------------------------------------------------------------------

/// Complexity metrics for clause body constraints.
///
/// Measures the structural complexity of the background-theory constraints
/// across all clauses. Higher complexity generally means PDR needs more
/// generalization effort and alternative engines (CEGAR, TPA) may be better.
#[derive(Debug, Clone, Default)]
pub(crate) struct BodyComplexity {
    /// Maximum number of top-level conjuncts in any clause constraint.
    pub(crate) max_conjuncts: usize,
    /// Mean number of top-level conjuncts across clause constraints.
    pub(crate) mean_conjuncts: f64,
    /// Maximum number of top-level disjuncts in any clause constraint.
    pub(crate) max_disjuncts: usize,
    /// Mean number of top-level disjuncts across clause constraints.
    pub(crate) mean_disjuncts: f64,
    /// Maximum AST depth across all clause constraints.
    pub(crate) max_constraint_depth: usize,
    /// Mean AST depth across all clause constraints.
    pub(crate) mean_constraint_depth: f64,
    /// Maximum number of AST nodes in a single clause constraint.
    pub(crate) max_constraint_size: usize,
    /// Total number of AST nodes across all clause constraints.
    pub(crate) total_constraint_nodes: usize,
}

// ---------------------------------------------------------------------------
// Arithmetic profile features
// ---------------------------------------------------------------------------

/// Arithmetic complexity metrics extracted from clause constraints.
///
/// Captures the magnitude and structure of integer constants and arithmetic
/// operations. Problems with large coefficients or high multiplication degree
/// are harder for PDR generalization and may benefit from CEGAR or TPA.
///
/// Part of #7915 - Learned algorithm selection.
#[derive(Debug, Clone, Default)]
pub(crate) struct ArithmeticProfile {
    /// Minimum absolute value of integer constants across all constraints.
    /// 0 if no integer constants found.
    pub(crate) coeff_min_abs: u128,
    /// Maximum absolute value of integer constants across all constraints.
    pub(crate) coeff_max_abs: u128,
    /// Mean absolute value of integer constants.
    pub(crate) coeff_mean_abs: f64,
    /// L1 norm (sum of absolute values) of integer constants.
    pub(crate) coeff_l1_norm: u128,
    /// Maximum multiplication degree (depth of nested Mul operations).
    /// 0 = no multiplication, 1 = linear multiplication, 2+ = polynomial.
    pub(crate) max_mul_degree: usize,
    /// Number of distinct integer constants across all constraints.
    pub(crate) num_distinct_constants: usize,
}

// ---------------------------------------------------------------------------
// Transition structure features
// ---------------------------------------------------------------------------

/// Transition structure metrics extracted from clause analysis.
///
/// Captures how variables evolve across transitions, which directly affects
/// which engines can find invariants efficiently. Counter patterns are easy
/// for TPA/Kind; resets break monotonicity assumptions.
///
/// Part of #7915 - Learned algorithm selection.
#[derive(Debug, Clone, Default)]
pub(crate) struct TransitionProfile {
    /// Number of transitions that reset a variable to a constant (x' = c).
    /// Resets break monotonicity and make BMC more effective than induction.
    pub(crate) reset_count: usize,
    /// Fraction of transitions where at least one variable only increases.
    /// High monotonicity fraction favors Kind and k-induction approaches.
    pub(crate) monotone_inc_ratio: f64,
    /// Fraction of transitions where at least one variable only decreases.
    pub(crate) monotone_dec_ratio: f64,
}

// ---------------------------------------------------------------------------
// Invariant shape hint features
// ---------------------------------------------------------------------------

/// Invariant shape hints derived from constraint structure.
///
/// These features approximate the shape of the invariant needed to prove
/// the property, without running any solver. Problems with many relational
/// comparisons need octagonal or polyhedral invariants; disjunctive guards
/// need disjunctive invariants.
///
/// Part of #7915 - Learned algorithm selection.
#[derive(Debug, Clone, Default)]
pub(crate) struct InvariantShapeHints {
    /// Number of relational comparisons between two distinct variables
    /// (e.g., x < y, x >= z). Indicates octagon/polyhedra need.
    pub(crate) num_relational_comparisons: usize,
    /// Maximum number of top-level disjunctive branches in any guard.
    /// High values indicate the invariant may need to be disjunctive.
    pub(crate) max_guard_disjuncts: usize,
    /// Total number of equality comparisons (x = c or x = y).
    /// High equality counts suggest template-based approaches may work.
    pub(crate) num_equality_comparisons: usize,
}

// ---------------------------------------------------------------------------
// Full CHC feature vector
// ---------------------------------------------------------------------------

/// Complete feature vector for CHC algorithm selection.
///
/// Combines the base `ProblemFeatures` (from the classifier) with
/// portfolio-specific features for engine prediction. The decision
/// tree or scoring function uses these to pick the best engine order.
#[derive(Debug, Clone)]
pub(crate) struct ChcFeatureVector {
    // --- Base features (delegated to ProblemClassifier) ---
    /// Base problem classification and structural features.
    pub(crate) base: ProblemFeatures,

    // --- Theory features ---
    /// Classified background theory.
    pub(crate) theory: TheoryProfile,
    /// Whether any predicate uses bitvector-sorted arguments.
    pub(crate) has_bv_args: bool,
    /// Whether any predicate uses integer-sorted arguments.
    pub(crate) has_int_args: bool,
    /// Whether any predicate uses real-sorted arguments.
    pub(crate) has_real_args: bool,
    /// Whether any predicate uses boolean-sorted arguments.
    pub(crate) has_bool_args: bool,
    /// Whether any predicate uses datatype-sorted arguments.
    pub(crate) has_dt_args: bool,
    /// Whether any predicate uses uninterpreted-sort arguments.
    pub(crate) has_uninterpreted_args: bool,

    // --- Clause body complexity ---
    /// Constraint complexity metrics.
    pub(crate) body_complexity: BodyComplexity,

    // --- Graph structure ---
    /// Classified predicate dependency graph structure.
    pub(crate) graph_structure: GraphStructure,
    /// Number of cyclic SCCs (SCCs with more than one member or self-loop).
    pub(crate) num_cyclic_sccs: usize,
    /// Total number of edges in predicate dependency graph.
    pub(crate) num_dependency_edges: usize,

    // --- Predicate statistics ---
    /// Mean predicate arity.
    pub(crate) mean_predicate_arity: f64,
    /// Sum of all predicate arities (total parameter space).
    pub(crate) total_predicate_arity: usize,
    /// Number of predicates with arity 0 (propositional predicates).
    pub(crate) num_nullary_predicates: usize,
    /// Fraction of Int-sorted predicate arguments (across all predicates).
    pub(crate) frac_int_args: f64,
    /// Fraction of Real-sorted predicate arguments.
    pub(crate) frac_real_args: f64,
    /// Fraction of BV-sorted predicate arguments.
    pub(crate) frac_bv_args: f64,
    /// Fraction of Bool-sorted predicate arguments.
    pub(crate) frac_bool_args: f64,
    /// Fraction of Array-sorted predicate arguments.
    pub(crate) frac_array_args: f64,
    /// Maximum number of Array-sorted parameters in any single predicate (#8660).
    /// When >= 2, PDR invariant synthesis becomes very expensive because the
    /// search space grows combinatorially with unconstrained array terms.
    pub(crate) max_array_params: usize,

    // --- Nonlinearity ---
    /// Route-facing number of non-linear clauses (more than one body predicate).
    /// Classifier-recognized triangle/location closure rules keep their
    /// `max_body_predicates` width but are zeroed here so they use the
    /// triangle/location diff-bound route signal instead of the generic
    /// nonlinear leaf.
    pub(crate) num_nonlinear_clauses: usize,
    /// Maximum number of body predicates in any clause.
    pub(crate) max_body_predicates: usize,

    // --- Graph topology (extended, #7915) ---
    /// Maximum out-degree (number of successors) of any predicate in the
    /// dependency graph.
    pub(crate) max_out_degree: usize,
    /// Maximum in-degree (number of predecessors) of any predicate in the
    /// dependency graph.
    pub(crate) max_in_degree: usize,
    /// Width of the widest level in the DAG condensation (BFS layers).
    pub(crate) dag_width: usize,

    // --- Arithmetic profile (#7915) ---
    /// Coefficient magnitude and multiplication degree statistics.
    pub(crate) arithmetic: ArithmeticProfile,

    // --- Transition structure (#7915) ---
    /// Variable evolution patterns across transitions.
    pub(crate) transitions: TransitionProfile,

    // --- Invariant shape hints (#7915) ---
    /// Constraint-derived invariant shape indicators.
    pub(crate) invariant_hints: InvariantShapeHints,
}

impl ChcFeatureVector {
    /// Convenience: delegate to `base.class`.
    pub(crate) fn class(&self) -> ProblemClass {
        self.base.class
    }
}

// ---------------------------------------------------------------------------
// Internal helper structs
// ---------------------------------------------------------------------------

/// Sort presence flags collected from predicate signatures.
struct SortProfile {
    has_int: bool,
    has_bv: bool,
    has_bool: bool,
    has_array: bool,
    has_real: bool,
    has_dt: bool,
    has_uninterpreted: bool,
}

/// Aggregate predicate arity and sort distribution statistics.
struct PredicateStats {
    mean_arity: f64,
    total_arity: usize,
    num_nullary: usize,
    frac_int: f64,
    frac_real: f64,
    frac_bv: f64,
    frac_bool: f64,
    frac_array: f64,
    max_array_params: usize,
}

// ---------------------------------------------------------------------------
// Feature extraction
// ---------------------------------------------------------------------------

/// CHC feature extractor for learned algorithm selection.
///
/// Computes all features needed by the portfolio decision tree in a
/// small number of passes over the problem. Runs in O(|clauses| * max_expr_size)
/// and should complete in <200ms for typical CHC-COMP benchmarks.
pub(crate) struct ChcFeatureExtractor;

impl ChcFeatureExtractor {
    /// Extract the full feature vector from a CHC problem.
    ///
    /// This is the main entry point. It computes the base classifier features
    /// first, then adds portfolio-specific features on top.
    pub(crate) fn extract(problem: &ChcProblem) -> ChcFeatureVector {
        // Phase 1: Base classification (reuses existing classifier)
        let base = ProblemClassifier::classify(problem);

        // Phase 2: Theory classification from predicate sorts + constraint ops
        let (sort_profile, theory) = Self::classify_theory(problem, &base);

        // Phase 3: Clause body complexity
        let body_complexity = Self::analyze_body_complexity(problem);

        // Phase 4: Graph structure classification
        let graph_structure = Self::classify_graph_structure(&base);
        let num_cyclic_sccs = Self::count_cyclic_sccs(problem);
        let dep_edges = problem.dependency_edges();
        let num_dependency_edges = dep_edges.len();

        // Phase 5: Predicate statistics
        let predicate_stats = Self::compute_predicate_stats(problem);

        // Phase 6: Nonlinearity
        let (num_nonlinear_clauses, max_body_predicates) =
            Self::compute_nonlinearity(problem, &base);

        // Phase 7: Extended graph topology (#7915)
        let (max_out_degree, max_in_degree) =
            Self::compute_degree_stats(&dep_edges, base.num_predicates);
        let dag_width = Self::compute_dag_width(problem, &base);

        // Phase 8: Arithmetic profile (#7915)
        let arithmetic = Self::analyze_arithmetic_profile(problem);

        // Phase 9: Transition structure (#7915)
        let transitions = Self::analyze_transition_structure(problem);

        // Phase 10: Invariant shape hints (#7915)
        let invariant_hints = Self::analyze_invariant_shape(problem);

        ChcFeatureVector {
            base,
            theory,
            has_bv_args: sort_profile.has_bv,
            has_int_args: sort_profile.has_int,
            has_real_args: sort_profile.has_real,
            has_bool_args: sort_profile.has_bool,
            has_dt_args: sort_profile.has_dt,
            has_uninterpreted_args: sort_profile.has_uninterpreted,
            body_complexity,
            graph_structure,
            num_cyclic_sccs,
            num_dependency_edges,
            mean_predicate_arity: predicate_stats.mean_arity,
            total_predicate_arity: predicate_stats.total_arity,
            num_nullary_predicates: predicate_stats.num_nullary,
            frac_int_args: predicate_stats.frac_int,
            frac_real_args: predicate_stats.frac_real,
            frac_bv_args: predicate_stats.frac_bv,
            frac_bool_args: predicate_stats.frac_bool,
            frac_array_args: predicate_stats.frac_array,
            max_array_params: predicate_stats.max_array_params,
            num_nonlinear_clauses,
            max_body_predicates,
            max_out_degree,
            max_in_degree,
            dag_width,
            arithmetic,
            transitions,
            invariant_hints,
        }
    }

    // ----- Theory classification -----

    fn classify_theory(
        problem: &ChcProblem,
        base: &ProblemFeatures,
    ) -> (SortProfile, TheoryProfile) {
        let mut profile = SortProfile {
            has_int: false,
            has_bv: false,
            has_bool: false,
            has_array: base.uses_arrays,
            has_real: base.uses_real,
            has_dt: false,
            has_uninterpreted: false,
        };

        // Scan predicate argument sorts
        for pred in problem.predicates() {
            for sort in &pred.arg_sorts {
                Self::scan_sort(sort, &mut profile);
            }
        }

        // Also scan constraint expressions for BV/array operators
        // (constraints may use BV ops even if predicates are pure Int)
        let has_bv_constraints = problem.clauses().iter().any(|c| {
            c.body
                .constraint
                .as_ref()
                .is_some_and(|expr| Self::expr_has_bv_ops(expr))
        });
        if has_bv_constraints {
            profile.has_bv = true;
        }

        let theory = Self::determine_theory_profile(&profile, base);
        (profile, theory)
    }

    fn scan_sort(sort: &ChcSort, profile: &mut SortProfile) {
        match sort {
            ChcSort::Int => profile.has_int = true,
            ChcSort::Bool => profile.has_bool = true,
            ChcSort::Real => profile.has_real = true,
            ChcSort::BitVec(_) => profile.has_bv = true,
            ChcSort::Array(k, v) => {
                profile.has_array = true;
                Self::scan_sort(k, profile);
                Self::scan_sort(v, profile);
            }
            ChcSort::Datatype { constructors, .. } => {
                profile.has_dt = true;
                // Recurse into constructor field sorts to detect BV/Int/Real
                // fields inside DTs (#8419). Without this, a DT+BV problem
                // like Option<BitVec(8)> would be classified as non-BV,
                // causing wrong engine routing and missing BV preprocessing.
                for ctor in constructors.iter() {
                    for sel in &ctor.selectors {
                        Self::scan_sort(&sel.sort, profile);
                    }
                }
            }
            ChcSort::Uninterpreted(_) => profile.has_uninterpreted = true,
        }
    }

    fn determine_theory_profile(profile: &SortProfile, base: &ProblemFeatures) -> TheoryProfile {
        if profile.has_real {
            return TheoryProfile::Real;
        }

        let has_arithmetic = profile.has_int || base.has_multiplication || base.has_mod_div;

        match (has_arithmetic, profile.has_bv, profile.has_array) {
            (false, false, false) => TheoryProfile::PureBool,
            (true, false, false) => TheoryProfile::PureLia,
            (false, true, false) => TheoryProfile::PureBv,
            (true, false, true) => TheoryProfile::LiaArrays,
            (false, true, true) | (_, true, true) => TheoryProfile::BvArrays,
            (true, true, false) => TheoryProfile::Mixed,
            // Fallback: if we have arrays but no arithmetic or BV,
            // treat as LIA+Arrays (arrays usually imply some indexing theory)
            (false, false, true) => TheoryProfile::LiaArrays,
        }
    }

    /// Check if an expression tree contains any bitvector operations.
    fn expr_has_bv_ops(expr: &ChcExpr) -> bool {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            match current {
                ChcExpr::BitVec(_, _) => return true,
                ChcExpr::Var(v) if matches!(v.sort, ChcSort::BitVec(_)) => return true,
                ChcExpr::Op(op, args) => {
                    if Self::is_bv_op(op) {
                        return true;
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
                ChcExpr::ConstArray(_, val) => stack.push(val.as_ref()),
                _ => {}
            }
        }
        false
    }

    fn is_bv_op(op: &ChcOp) -> bool {
        matches!(
            op,
            ChcOp::BvAdd
                | ChcOp::BvSub
                | ChcOp::BvMul
                | ChcOp::BvUDiv
                | ChcOp::BvURem
                | ChcOp::BvSDiv
                | ChcOp::BvSRem
                | ChcOp::BvSMod
                | ChcOp::BvAnd
                | ChcOp::BvOr
                | ChcOp::BvXor
                | ChcOp::BvNand
                | ChcOp::BvNor
                | ChcOp::BvXnor
                | ChcOp::BvNot
                | ChcOp::BvNeg
                | ChcOp::BvShl
                | ChcOp::BvLShr
                | ChcOp::BvAShr
                | ChcOp::BvULt
                | ChcOp::BvULe
                | ChcOp::BvUGt
                | ChcOp::BvUGe
                | ChcOp::BvSLt
                | ChcOp::BvSLe
                | ChcOp::BvSGt
                | ChcOp::BvSGe
                | ChcOp::BvComp
                | ChcOp::BvConcat
                | ChcOp::Bv2Nat
                | ChcOp::BvExtract(_, _)
                | ChcOp::BvZeroExtend(_)
                | ChcOp::BvSignExtend(_)
                | ChcOp::BvRotateLeft(_)
                | ChcOp::BvRotateRight(_)
                | ChcOp::BvRepeat(_)
                | ChcOp::Int2Bv(_)
        )
    }

    // ----- Body complexity analysis -----

    fn analyze_body_complexity(problem: &ChcProblem) -> BodyComplexity {
        let clauses_with_constraints: Vec<_> = problem
            .clauses()
            .iter()
            .filter_map(|c| c.body.constraint.as_ref())
            .collect();

        if clauses_with_constraints.is_empty() {
            return BodyComplexity::default();
        }

        let n = clauses_with_constraints.len();
        let mut max_conjuncts = 0usize;
        let mut total_conjuncts = 0usize;
        let mut max_disjuncts = 0usize;
        let mut total_disjuncts = 0usize;
        let mut max_depth = 0usize;
        let mut total_depth = 0usize;
        let mut max_size = 0usize;
        let mut total_nodes = 0usize;

        for constraint in &clauses_with_constraints {
            let conj = Self::count_top_level_ops(constraint, &ChcOp::And);
            max_conjuncts = max_conjuncts.max(conj);
            total_conjuncts += conj;

            let disj = Self::count_top_level_ops(constraint, &ChcOp::Or);
            max_disjuncts = max_disjuncts.max(disj);
            total_disjuncts += disj;

            let (depth, size) = Self::measure_expr(constraint);
            max_depth = max_depth.max(depth);
            total_depth += depth;
            max_size = max_size.max(size);
            total_nodes += size;
        }

        BodyComplexity {
            max_conjuncts,
            mean_conjuncts: total_conjuncts as f64 / n as f64,
            max_disjuncts,
            mean_disjuncts: total_disjuncts as f64 / n as f64,
            max_constraint_depth: max_depth,
            mean_constraint_depth: total_depth as f64 / n as f64,
            max_constraint_size: max_size,
            total_constraint_nodes: total_nodes,
        }
    }

    /// Count top-level occurrences of a specific operator.
    ///
    /// For `And`, this counts the number of conjuncts at the top level
    /// (recursing into nested `And` but not into other operators).
    /// A single non-And expression has 1 conjunct.
    fn count_top_level_ops(expr: &ChcExpr, target_op: &ChcOp) -> usize {
        match expr {
            ChcExpr::Op(op, args) if op == target_op => args
                .iter()
                .map(|a| Self::count_top_level_ops(a.as_ref(), target_op))
                .sum(),
            _ => 1,
        }
    }

    /// Measure the depth and node count of an expression tree.
    ///
    /// Uses an iterative approach to avoid stack overflow on deep trees.
    fn measure_expr(expr: &ChcExpr) -> (usize, usize) {
        // (expression, current_depth)
        let mut stack: Vec<(&ChcExpr, usize)> = vec![(expr, 1)];
        let mut max_depth = 0usize;
        let mut node_count = 0usize;

        while let Some((current, depth)) = stack.pop() {
            node_count += 1;
            max_depth = max_depth.max(depth);

            match current {
                ChcExpr::Op(_, args) => {
                    for arg in args {
                        stack.push((arg.as_ref(), depth + 1));
                    }
                }
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        stack.push((arg.as_ref(), depth + 1));
                    }
                }
                ChcExpr::ConstArray(_, val) => {
                    stack.push((val.as_ref(), depth + 1));
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
        }

        (max_depth, node_count)
    }

    // ----- Graph structure classification -----

    fn classify_graph_structure(base: &ProblemFeatures) -> GraphStructure {
        if base.num_predicates == 0 {
            return GraphStructure::Empty;
        }

        if base.is_single_predicate {
            return GraphStructure::SelfLoop;
        }

        if !base.has_cycles {
            // Acyclic: chain vs DAG
            // A chain is a path where each node has at most one successor and predecessor.
            // In our condensation, if all SCCs are singletons and the max in-degree is 1,
            // it is a chain. For simplicity, check if dag_depth == scc_count (linear chain).
            if base.dag_depth >= base.scc_count && base.scc_count > 0 {
                return GraphStructure::AcyclicChain;
            }
            return GraphStructure::AcyclicDag;
        }

        // Cyclic: check number of cyclic SCCs
        // We use max_scc_size as a proxy: if only one SCC has size > 1,
        // it is likely a single cycle.
        if base.scc_count == 1 {
            return GraphStructure::SingleCycle;
        }

        // Multiple SCCs with at least one cyclic: could be single or multi.
        // If max_scc_size > 1 and there are acyclic SCCs too, the cyclic part
        // is a single cycle unless multiple SCCs are cyclic.
        // For the most accurate count, we defer to num_cyclic_sccs (computed separately).
        // Here we use a heuristic based on available base features.
        if base.max_scc_size > 1 && base.scc_count <= 3 {
            // Few SCCs with one large cyclic component
            GraphStructure::SingleCycle
        } else {
            GraphStructure::MultiCycle
        }
    }

    /// Count the number of cyclic SCCs using Tarjan's SCC analysis.
    fn count_cyclic_sccs(problem: &ChcProblem) -> usize {
        let scc_info = crate::pdr::scc::tarjan_scc(problem);
        scc_info.sccs.iter().filter(|scc| scc.is_cyclic).count()
    }

    // ----- Predicate statistics -----

    fn compute_predicate_stats(problem: &ChcProblem) -> PredicateStats {
        let predicates = problem.predicates();

        if predicates.is_empty() {
            return PredicateStats {
                mean_arity: 0.0,
                total_arity: 0,
                num_nullary: 0,
                frac_int: 0.0,
                frac_real: 0.0,
                frac_bv: 0.0,
                frac_bool: 0.0,
                frac_array: 0.0,
                max_array_params: 0,
            };
        }

        let total_arity: usize = predicates.iter().map(|p| p.arity()).sum();
        let num_nullary = predicates.iter().filter(|p| p.arity() == 0).count();
        let mean_arity = total_arity as f64 / predicates.len() as f64;

        // Count sorts across all predicate arguments
        let mut int_count = 0usize;
        let mut real_count = 0usize;
        let mut bv_count = 0usize;
        let mut bool_count = 0usize;
        let mut array_count = 0usize;
        // #8660: Track max Array-sorted params per predicate for portfolio routing
        let mut max_array_params = 0usize;

        for pred in predicates {
            let mut pred_array_count = 0usize;
            for sort in &pred.arg_sorts {
                match sort {
                    ChcSort::Int => int_count += 1,
                    ChcSort::Real => real_count += 1,
                    ChcSort::BitVec(_) => bv_count += 1,
                    ChcSort::Bool => bool_count += 1,
                    ChcSort::Array(_, _) => {
                        array_count += 1;
                        pred_array_count += 1;
                    }
                    ChcSort::Uninterpreted(_) | ChcSort::Datatype { .. } => {}
                }
            }
            max_array_params = max_array_params.max(pred_array_count);
        }

        let total = if total_arity == 0 { 1 } else { total_arity };

        PredicateStats {
            mean_arity,
            total_arity,
            num_nullary,
            frac_int: int_count as f64 / total as f64,
            frac_real: real_count as f64 / total as f64,
            frac_bv: bv_count as f64 / total as f64,
            frac_bool: bool_count as f64 / total as f64,
            frac_array: array_count as f64 / total as f64,
            max_array_params,
        }
    }

    // ----- Nonlinearity -----

    fn compute_nonlinearity(problem: &ChcProblem, base: &ProblemFeatures) -> (usize, usize) {
        let mut num_nonlinear = 0usize;
        let mut max_body_preds = 0usize;

        for clause in problem.clauses() {
            let body_pred_count = clause.body.predicates.len();
            max_body_preds = max_body_preds.max(body_pred_count);
            if body_pred_count > 1 {
                num_nonlinear += 1;
            }
        }

        if base.is_triangle_location_diff_bounds {
            // Triangle/location closure rules are syntactically multi-body, but
            // the classifier has already recognized their difference-bound
            // location form and routed them out of generic MultiPredComplex.
            // Keep the width observable while preventing learned selection from
            // preempting that route signal with the generic nonlinear CEGAR leaf.
            num_nonlinear = 0;
        }

        (num_nonlinear, max_body_preds)
    }

    // ----- Extended graph topology (#7915) -----

    /// Compute max in-degree and max out-degree from dependency edges.
    fn compute_degree_stats(
        edges: &[(crate::PredicateId, crate::PredicateId)],
        num_predicates: usize,
    ) -> (usize, usize) {
        if num_predicates == 0 || edges.is_empty() {
            return (0, 0);
        }
        let mut out_degree = vec![0usize; num_predicates];
        let mut in_degree = vec![0usize; num_predicates];
        for &(from, to) in edges {
            if from.index() < num_predicates {
                out_degree[from.index()] += 1;
            }
            if to.index() < num_predicates {
                in_degree[to.index()] += 1;
            }
        }
        let max_out = out_degree.iter().copied().max().unwrap_or(0);
        let max_in = in_degree.iter().copied().max().unwrap_or(0);
        (max_out, max_in)
    }

    /// Compute the DAG width (maximum number of nodes at any BFS level).
    ///
    /// Uses the SCC condensation DAG and performs a BFS from all roots
    /// (nodes with in-degree 0). The width is the max level population.
    fn compute_dag_width(problem: &ChcProblem, base: &ProblemFeatures) -> usize {
        if base.num_predicates <= 1 {
            return base.num_predicates;
        }
        let scc_info = crate::pdr::scc::tarjan_scc(problem);
        let scc_count = scc_info.sccs.len();
        if scc_count == 0 {
            return 0;
        }

        // Build condensation DAG adjacency + in-degrees
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); scc_count];
        let mut in_deg = vec![0usize; scc_count];
        for (from_pred, to_pred) in problem.dependency_edges() {
            let Some(&from_scc) = scc_info.predicate_to_scc.get(&from_pred) else {
                continue;
            };
            let Some(&to_scc) = scc_info.predicate_to_scc.get(&to_pred) else {
                continue;
            };
            if from_scc != to_scc && !adj[from_scc].contains(&to_scc) {
                adj[from_scc].push(to_scc);
                in_deg[to_scc] += 1;
            }
        }

        // BFS by levels from all roots
        let mut current_level: Vec<usize> = (0..scc_count).filter(|i| in_deg[*i] == 0).collect();
        let mut max_width = current_level.len();

        while !current_level.is_empty() {
            let mut next_level = Vec::new();
            for &node in &current_level {
                for &succ in &adj[node] {
                    in_deg[succ] -= 1;
                    if in_deg[succ] == 0 {
                        next_level.push(succ);
                    }
                }
            }
            if !next_level.is_empty() {
                max_width = max_width.max(next_level.len());
            }
            current_level = next_level;
        }

        max_width
    }

    // ----- Arithmetic profile (#7915) -----

    /// Analyze integer constant magnitudes and multiplication degree.
    fn analyze_arithmetic_profile(problem: &ChcProblem) -> ArithmeticProfile {
        let mut constants: Vec<u128> = Vec::new();
        let mut max_mul_degree = 0usize;

        for clause in problem.clauses() {
            if let Some(constraint) = &clause.body.constraint {
                Self::collect_arithmetic_features(constraint, &mut constants, &mut max_mul_degree);
            }
        }

        if constants.is_empty() {
            return ArithmeticProfile::default();
        }

        let num_distinct = {
            let mut sorted = constants.clone();
            sorted.sort_unstable();
            sorted.dedup();
            sorted.len()
        };
        let l1_norm: u128 = constants.iter().sum();
        let mean = l1_norm as f64 / constants.len() as f64;
        let min_abs = constants.iter().copied().min().unwrap_or(0);
        let max_abs = constants.iter().copied().max().unwrap_or(0);

        ArithmeticProfile {
            coeff_min_abs: min_abs,
            coeff_max_abs: max_abs,
            coeff_mean_abs: mean,
            coeff_l1_norm: l1_norm,
            max_mul_degree,
            num_distinct_constants: num_distinct,
        }
    }

    /// Walk an expression tree collecting integer constant absolute values
    /// and tracking the maximum multiplication nesting depth.
    fn collect_arithmetic_features(
        expr: &ChcExpr,
        constants: &mut Vec<u128>,
        max_mul_degree: &mut usize,
    ) {
        // (expr, current_mul_depth)
        let mut stack: Vec<(&ChcExpr, usize)> = vec![(expr, 0)];
        while let Some((current, mul_depth)) = stack.pop() {
            match current {
                ChcExpr::Int(n) => {
                    constants.push(n.unsigned_abs());
                }
                ChcExpr::Op(op, args) => {
                    let next_mul_depth = if matches!(op, ChcOp::Mul) {
                        let d = mul_depth + 1;
                        *max_mul_degree = (*max_mul_degree).max(d);
                        d
                    } else {
                        0
                    };
                    for arg in args {
                        stack.push((arg.as_ref(), next_mul_depth));
                    }
                }
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        stack.push((arg.as_ref(), 0));
                    }
                }
                ChcExpr::ConstArray(_, val) => stack.push((val.as_ref(), 0)),
                _ => {}
            }
        }
    }

    // ----- Transition structure (#7915) -----

    /// Analyze transition clauses for reset and monotonicity patterns.
    fn analyze_transition_structure(problem: &ChcProblem) -> TransitionProfile {
        let mut reset_count = 0usize;
        let mut monotone_inc_count = 0usize;
        let mut monotone_dec_count = 0usize;
        let mut total_transitions = 0usize;

        for clause in problem.clauses() {
            // A transition has at least one body predicate and a predicate head
            if clause.body.predicates.is_empty() || clause.is_query() {
                continue;
            }
            total_transitions += 1;

            if let Some(constraint) = &clause.body.constraint {
                let (has_reset, has_inc, has_dec) =
                    Self::classify_transition_constraint(constraint);
                if has_reset {
                    reset_count += 1;
                }
                if has_inc {
                    monotone_inc_count += 1;
                }
                if has_dec {
                    monotone_dec_count += 1;
                }
            }
        }

        let denom = if total_transitions == 0 {
            1
        } else {
            total_transitions
        };
        TransitionProfile {
            reset_count,
            monotone_inc_ratio: monotone_inc_count as f64 / denom as f64,
            monotone_dec_ratio: monotone_dec_count as f64 / denom as f64,
        }
    }

    /// Classify a transition constraint for reset/monotonicity patterns.
    ///
    /// Returns (has_reset, has_monotone_inc, has_monotone_dec).
    /// A "reset" is an equality where one side is a constant (x' = 0).
    /// "Monotone inc" is detected from x' = x + c where c > 0.
    /// "Monotone dec" is detected from x' = x - c where c > 0.
    ///
    /// This is a lightweight syntactic check, not a full abstract interpretation.
    fn classify_transition_constraint(expr: &ChcExpr) -> (bool, bool, bool) {
        let mut has_reset = false;
        let mut has_inc = false;
        let mut has_dec = false;
        let mut stack = vec![expr];

        while let Some(current) = stack.pop() {
            match current {
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    // Check for reset: x = constant
                    let lhs_is_const = matches!(args[0].as_ref(), ChcExpr::Int(_));
                    let rhs_is_const = matches!(args[1].as_ref(), ChcExpr::Int(_));
                    if (lhs_is_const && !rhs_is_const) || (!lhs_is_const && rhs_is_const) {
                        has_reset = true;
                    }
                    // Check for increment: x = y + c
                    if let ChcExpr::Op(ChcOp::Add, add_args) = args[1].as_ref() {
                        if add_args.len() == 2 {
                            if let ChcExpr::Int(c) = add_args[1].as_ref() {
                                if *c > 0 {
                                    has_inc = true;
                                } else if *c < 0 {
                                    has_dec = true;
                                }
                            }
                        }
                    }
                    if let ChcExpr::Op(ChcOp::Sub, sub_args) = args[1].as_ref() {
                        if sub_args.len() == 2 {
                            if let ChcExpr::Int(c) = sub_args[1].as_ref() {
                                if *c > 0 {
                                    has_dec = true;
                                }
                            }
                        }
                    }
                }
                ChcExpr::Op(_, args) => {
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::ConstArray(_, val) => stack.push(val.as_ref()),
                _ => {}
            }
        }

        (has_reset, has_inc, has_dec)
    }

    // ----- Invariant shape hints (#7915) -----

    /// Analyze constraint structure for invariant shape indicators.
    fn analyze_invariant_shape(problem: &ChcProblem) -> InvariantShapeHints {
        let mut num_relational = 0usize;
        let mut max_guard_disjuncts = 0usize;
        let mut num_equality = 0usize;

        for clause in problem.clauses() {
            if let Some(constraint) = &clause.body.constraint {
                Self::collect_invariant_hints(
                    constraint,
                    &mut num_relational,
                    &mut max_guard_disjuncts,
                    &mut num_equality,
                );
            }
        }

        InvariantShapeHints {
            num_relational_comparisons: num_relational,
            max_guard_disjuncts,
            num_equality_comparisons: num_equality,
        }
    }

    /// Walk a constraint collecting relational comparison and disjunction counts.
    fn collect_invariant_hints(
        expr: &ChcExpr,
        num_relational: &mut usize,
        max_disjuncts: &mut usize,
        num_equality: &mut usize,
    ) {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            match current {
                ChcExpr::Op(op, args) => {
                    match op {
                        ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                            // Check if both sides reference variables (relational)
                            if args.len() == 2
                                && Self::contains_var(&args[0])
                                && Self::contains_var(&args[1])
                            => {
                                *num_relational += 1;
                            }
                        ChcOp::Eq => {
                            *num_equality += 1;
                        }
                        ChcOp::Or => {
                            // Count top-level disjuncts
                            let count = Self::count_top_level_ops(current, &ChcOp::Or);
                            *max_disjuncts = (*max_disjuncts).max(count);
                        }
                        _ => {}
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
                ChcExpr::ConstArray(_, val) => stack.push(val.as_ref()),
                _ => {}
            }
        }
    }

    /// Check if an expression subtree contains any variable reference.
    fn contains_var(expr: &ChcExpr) -> bool {
        let mut stack = vec![expr];
        while let Some(current) = stack.pop() {
            match current {
                ChcExpr::Var(_) => return true,
                ChcExpr::Op(_, args) => {
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        stack.push(arg.as_ref());
                    }
                }
                ChcExpr::ConstArray(_, val) => stack.push(val.as_ref()),
                _ => {}
            }
        }
        false
    }
}

impl std::fmt::Display for ChcFeatureVector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "ChcFeatures(class={}, theory={}, graph={}, preds={}, clauses={}, \
             max_arity={}, mean_arity={:.1}, body_depth={}, body_conjuncts={}, \
             nonlinear={}, bv={}, real={}, arrays={}, max_array_params={}, cycles={}, \
             coeff_max={}, mul_degree={}, resets={}, \
             relational_cmp={}, guard_disj={})",
            self.base.class,
            self.theory,
            self.graph_structure,
            self.base.num_predicates,
            self.base.num_clauses,
            self.base.max_predicate_arity,
            self.mean_predicate_arity,
            self.body_complexity.max_constraint_depth,
            self.body_complexity.max_conjuncts,
            self.num_nonlinear_clauses,
            self.has_bv_args,
            self.has_real_args,
            self.base.uses_arrays,
            self.max_array_params,
            self.base.has_cycles,
            self.arithmetic.coeff_max_abs,
            self.arithmetic.max_mul_degree,
            self.transitions.reset_count,
            self.invariant_hints.num_relational_comparisons,
            self.invariant_hints.max_guard_disjuncts,
        )
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcVar, ClauseBody, ClauseHead, HornClause};

    fn simple_loop_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        // x = 0 => Inv(x)
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));

        // Inv(x) /\ x < 10 => Inv(x + 1)
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));

        // Inv(x) /\ x >= 10 => false
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
            ),
            ClauseHead::False,
        ));

        problem
    }

    fn triangle_location_feature_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let pred_sorts = vec![ChcSort::Int; 12];
        let lturn = problem.declare_predicate("lturn", pred_sorts.clone());
        let step_lturn = problem.declare_predicate("step_lturn", pred_sorts.clone());
        let combined_lturn = problem.declare_predicate("combined_lturn", pred_sorts);
        let marker = problem.declare_predicate("CHC_COMP_FALSE", Vec::new());
        let vars: Vec<_> = (0..16)
            .map(|index| ChcVar::new(format!("x{index}"), ChcSort::Int))
            .collect();

        let var = |index: usize| ChcExpr::var(vars[index].clone());
        let args = || (0..12).map(var).collect::<Vec<_>>();
        let rotated_args = |a: usize, b: usize, c: usize| {
            vec![
                var(8),
                var(0),
                var(1),
                var(2),
                var(3),
                var(4),
                var(5),
                var(6),
                var(a),
                var(b),
                var(c),
                var(7),
            ]
        };
        let diff_ge_zero = |left: usize, right: usize| {
            ChcExpr::ge(ChcExpr::sub(var(left), var(right)), ChcExpr::int(0))
        };
        let closure_equalities = || {
            ChcExpr::and_all([
                ChcExpr::eq(var(12), var(8)),
                ChcExpr::eq(var(13), var(8)),
                ChcExpr::eq(var(14), var(8)),
            ])
        };

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and_all([
                diff_ge_zero(5, 10),
                diff_ge_zero(5, 8),
                diff_ge_zero(6, 1),
            ])),
            ClauseHead::Predicate(lturn, args()),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and_all([
                diff_ge_zero(5, 1),
                diff_ge_zero(6, 10),
                diff_ge_zero(1, 9),
            ])),
            ClauseHead::Predicate(step_lturn, args()),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(lturn, args())], Some(ChcExpr::Bool(true))),
            ClauseHead::Predicate(combined_lturn, args()),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(step_lturn, args())], Some(ChcExpr::Bool(true))),
            ClauseHead::Predicate(combined_lturn, args()),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![
                    (combined_lturn, rotated_args(12, 9, 11)),
                    (step_lturn, rotated_args(13, 10, 9)),
                    (combined_lturn, rotated_args(14, 11, 10)),
                ],
                Some(closure_equalities()),
            ),
            ClauseHead::Predicate(lturn, rotated_args(11, 10, 9)),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![
                    (combined_lturn, rotated_args(8, 11, 13)),
                    (step_lturn, rotated_args(15, 11, 10)),
                    (combined_lturn, rotated_args(14, 11, 10)),
                    (combined_lturn, rotated_args(8, 15, 11)),
                    (step_lturn, rotated_args(8, 10, 11)),
                ],
                Some(closure_equalities()),
            ),
            ClauseHead::Predicate(step_lturn, rotated_args(8, 11, 10)),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![
                    (combined_lturn, rotated_args(12, 9, 11)),
                    (step_lturn, rotated_args(11, 9, 10)),
                    (combined_lturn, rotated_args(13, 10, 9)),
                    (combined_lturn, rotated_args(14, 11, 10)),
                ],
                Some(closure_equalities()),
            ),
            ClauseHead::Predicate(marker, Vec::new()),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(marker, Vec::new())], None),
            ClauseHead::False,
        ));

        problem
    }

    #[test]
    fn test_simple_loop_features() {
        let problem = simple_loop_problem();
        let features = ChcFeatureExtractor::extract(&problem);

        assert_eq!(features.class(), ProblemClass::SimpleLoop);
        assert_eq!(features.theory, TheoryProfile::PureLia);
        assert_eq!(features.graph_structure, GraphStructure::SelfLoop);
        assert_eq!(features.base.num_predicates, 1);
        assert_eq!(features.base.num_clauses, 3);
        assert!(features.has_int_args);
        assert!(!features.has_bv_args);
        assert_eq!(features.num_nonlinear_clauses, 0);
        assert_eq!(features.max_body_predicates, 1);
        assert_eq!(features.num_cyclic_sccs, 1); // self-loop is cyclic
        assert_eq!(features.total_predicate_arity, 1);
    }

    #[test]
    fn test_bv_features() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(32)]);
        let x = ChcVar::new("x", ChcSort::BitVec(32));

        // x = 0 => Inv(x)
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 32))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));

        // Inv(x) => false
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], None),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);

        assert_eq!(features.theory, TheoryProfile::PureBv);
        assert!(features.has_bv_args);
        assert!(!features.has_int_args);
        assert_eq!(features.frac_bv_args, 1.0);
        assert_eq!(features.frac_int_args, 0.0);
    }

    #[test]
    fn test_entry_exit_features() {
        let mut problem = ChcProblem::new();
        let x = ChcVar::new("x", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and(
                ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
                ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(3)),
            )),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);

        assert_eq!(features.class(), ProblemClass::EntryExitOnly);
        assert_eq!(features.graph_structure, GraphStructure::Empty);
        assert_eq!(features.base.num_predicates, 0);
        assert_eq!(features.num_dependency_edges, 0);
    }

    #[test]
    fn test_body_complexity() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        // Clause with complex constraint: (x > 0) /\ (y > 0) /\ (x + y < 100)
        let constraint = ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::and(
                ChcExpr::gt(ChcExpr::var(y.clone()), ChcExpr::int(0)),
                ChcExpr::lt(
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y)),
                    ChcExpr::int(100),
                ),
            ),
        );

        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], Some(constraint)),
            ClauseHead::False,
        ));

        // Add a fact so the problem is valid
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::int(0)]),
        ));

        let features = ChcFeatureExtractor::extract(&problem);

        // The constraint has 3 top-level conjuncts (flattened And)
        assert_eq!(features.body_complexity.max_conjuncts, 3);
        assert!(features.body_complexity.max_constraint_depth >= 3);
        assert!(features.body_complexity.max_constraint_size >= 7);
    }

    #[test]
    fn test_multi_pred_chain_features() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Int]);
        let r = problem.declare_predicate("R", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(x.clone())])],
                None,
            ),
            ClauseHead::Predicate(r, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(r, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);

        assert_eq!(features.class(), ProblemClass::MultiPredLinear);
        assert_eq!(features.theory, TheoryProfile::PureLia);
        assert_eq!(features.graph_structure, GraphStructure::AcyclicChain);
        assert_eq!(features.base.num_predicates, 3);
        assert!(!features.base.has_cycles);
        assert_eq!(features.num_cyclic_sccs, 0);
        assert_eq!(features.num_nonlinear_clauses, 0);
        assert!(features.base.dag_depth >= 3);
        assert_eq!(features.base.max_predicate_arity, 2);
        assert_eq!(features.total_predicate_arity, 4);
    }

    #[test]
    fn test_cyclic_features() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(
                q,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![ChcExpr::var(y.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(20))),
            ),
            ClauseHead::Predicate(p, vec![ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1))]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(15))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);

        assert_eq!(features.class(), ProblemClass::MultiPredLinear);
        assert!(features.base.has_cycles);
        assert_eq!(features.graph_structure, GraphStructure::SingleCycle);
        assert_eq!(features.num_cyclic_sccs, 1);
    }

    #[test]
    fn test_nonlinear_clause_count() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let r = problem.declare_predicate("R", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
        ));
        // Non-linear: P(x) /\ Q(y) => R(x + y)
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![
                    (p, vec![ChcExpr::var(x.clone())]),
                    (q, vec![ChcExpr::var(y.clone())]),
                ],
                None,
            ),
            ClauseHead::Predicate(
                r,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y))],
            ),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(r, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
            ),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        assert_eq!(features.num_nonlinear_clauses, 1);
        assert_eq!(features.max_body_predicates, 2);
        assert!(!features.base.is_linear);
    }

    #[test]
    fn test_triangle_location_feature_route_signal_keeps_width_observable() {
        let problem = triangle_location_feature_problem();
        let features = ChcFeatureExtractor::extract(&problem);

        assert!(features.base.is_triangle_location_diff_bounds);
        assert_eq!(features.class(), ProblemClass::MultiPredLinear);
        assert!(!features.base.is_linear);
        assert_eq!(features.max_body_predicates, 5);
        assert_eq!(features.num_nonlinear_clauses, 0);
    }

    #[test]
    fn test_predicate_sort_fractions() {
        let mut problem = ChcProblem::new();
        let _inv = problem.declare_predicate(
            "Inv",
            vec![
                ChcSort::Int,
                ChcSort::Int,
                ChcSort::Bool,
                ChcSort::BitVec(32),
            ],
        );

        let x = ChcVar::new("x", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        assert_eq!(features.total_predicate_arity, 4);
        assert!((features.frac_int_args - 0.5).abs() < 1e-10);
        assert!((features.frac_bool_args - 0.25).abs() < 1e-10);
        assert!((features.frac_bv_args - 0.25).abs() < 1e-10);
        assert_eq!(features.theory, TheoryProfile::Mixed);
    }

    #[test]
    fn test_mixed_lia_lra_features_preserve_real_sort_profile() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Real, ChcSort::Real]);

        let r = ChcVar::new("r", ChcSort::Real);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(r), ChcExpr::Real(0, 1))),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        assert_eq!(features.theory, TheoryProfile::Real);
        assert!(features.has_int_args);
        assert!(features.has_real_args);
        assert!((features.frac_int_args - (1.0 / 3.0)).abs() < 1e-10);
        assert!((features.frac_real_args - (2.0 / 3.0)).abs() < 1e-10);
    }

    /// #8419: DT+BV theory classification must detect BV inside DT constructors.
    #[test]
    fn test_dt_bv_theory_classification() {
        use crate::{ChcDtConstructor, ChcDtSelector};
        use std::sync::Arc;

        let dt_sort = ChcSort::Datatype {
            name: "OptionBV8".to_string(),
            constructors: Arc::new(vec![
                ChcDtConstructor {
                    name: "None".to_string(),
                    selectors: vec![],
                },
                ChcDtConstructor {
                    name: "Some".to_string(),
                    selectors: vec![ChcDtSelector {
                        name: "val".to_string(),
                        sort: ChcSort::BitVec(8),
                    }],
                },
            ]),
        };

        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![dt_sort]);

        let x = ChcVar::new("x", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
            ClauseHead::False,
        ));

        let features = ChcFeatureExtractor::extract(&problem);
        assert!(features.has_dt_args, "should detect DT args");
        assert!(
            features.has_bv_args,
            "should detect BV inside DT constructors"
        );
        assert!(
            features.theory == TheoryProfile::PureBv || features.theory == TheoryProfile::Mixed,
            "DT containing BV(8) should classify as BV or Mixed, got {:?}",
            features.theory
        );
    }

    #[test]
    fn test_display() {
        let problem = simple_loop_problem();
        let features = ChcFeatureExtractor::extract(&problem);
        let display = format!("{features}");
        assert!(display.contains("SimpleLoop"));
        assert!(display.contains("PureLIA"));
        assert!(display.contains("SelfLoop"));
    }
}
