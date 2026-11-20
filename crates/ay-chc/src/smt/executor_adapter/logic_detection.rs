// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic detection and sort-to-SMT-LIB conversion helpers for the executor adapter.

use crate::{
    ChcDtConstructor, ChcError, ChcExpr, ChcProblem, ChcResult, ChcSort, ChcVar, ClauseHead,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

#[cfg(test)]
mod admission_tests;
#[cfg(test)]
mod sort_scan_tests;
mod variable_sorts;

pub(super) const MAX_DT_DECLARATIONS: usize = 256;
pub(super) const MAX_DT_CONSTRUCTORS: usize = 4_096;
pub(super) const MAX_DT_SELECTORS: usize = 16_384;
const MAX_DT_SORT_NODES: usize = 32_768;
/// Distinct expression nodes (pointer identity) one executor query may carry.
///
/// Workstream D bridge item D-1 (CHC-COMP 2026, the development design notes at `9598c4206`
/// §4.1): the admission walks below are pointer-memoised, so this caps UNIQUE
/// nodes. It used to cap the TREE expansion, which refused every IMC k-query
/// of the wide `oral_messages` systems at k = 1 (a 168 k–280 k-node let tree
/// that is a small DAG) although the executor decides it in ~23 ms.
pub(super) const MAX_DT_EXPR_NODES: usize = 131_072;
pub(super) const MAX_DT_NESTING_DEPTH: usize = 512;
/// Tree expansion (occurrences, sharing unfolded) of an admitted executor
/// query.
///
/// The executor's script printers other than the Search-lane DAG printer
/// (`InvariantModel::expr_to_smtlib` on the Verification lane, in the
/// DAG-printer fallback, and in the PDR/persistent/ADT executor backends)
/// follow the tree, not the DAG. This separate cap keeps them bounded. It is
/// enforced by the single-query executor admission
/// ([`collect_dt_declarations_for_expr_sized`] and its wrapper) only: the
/// multi-root walk behind problem validation and the UF surface
/// ([`collect_dt_declarations_for_exprs`]) prints nothing and stays
/// DAG-linear end to end (WP-F, `problem_validate_is_linear_on_shared_constraints`).
pub(super) const MAX_EXECUTOR_TREE_NODES: usize = 4_194_304;
const MAX_DT_NAME_BYTES: usize = 1024 * 1024;
const MAX_DT_DEFINITION_COMPARE_WORK: usize = 131_072;
const MAX_DT_DECLARATION_BYTES: usize = 8 * 1024 * 1024;
pub(super) const MAX_EXECUTOR_EXPR_ROOTS: usize = MAX_DT_EXPR_NODES;
pub(super) const MAX_EXECUTOR_UF_DECLARATIONS: usize = 4_096;
pub(super) const MAX_EXECUTOR_UF_APPLICATIONS: usize = 16_384;
pub(super) const MAX_EXECUTOR_SURFACE_NAME_BYTES: usize = MAX_DT_NAME_BYTES;
const MAX_EXECUTOR_UF_ARGUMENT_OCCURRENCES: usize = MAX_DT_EXPR_NODES;
/// Complete query-local UF observation script, including declarations and
/// equality assertions. Keep generated replay text inside the same envelope as
/// executor-bound datatype declaration text.
pub(super) const MAX_EXECUTOR_UF_ALIAS_EMITTED_BYTES: usize = MAX_DT_DECLARATION_BYTES;
/// Aggregate expression-node visits performed while serializing UF observation
/// aliases. A nested UF chain contributes each prefix again, so this must be a
/// separate cap from the original expression-DAG admission.
pub(super) const MAX_EXECUTOR_UF_ALIAS_EMIT_WORK: usize = MAX_DT_EXPR_NODES;

/// Limits of one admission walk.
///
/// An executor query is admitted against [`EXECUTOR_QUERY_LIMITS`]: those caps
/// bound what one executor script may carry. A whole-problem scan
/// ([`collect_uninterpreted_function_declarations_for_problem`], behind
/// `ChcProblem::validate`, PDR initialisation and the BMC executor sessions)
/// serializes nothing. It walks a problem the parser already holds in memory,
/// linearly, so its caps only bound work proportional to that input and are
/// [`PROBLEM_SCAN_LIMITS`]. Charging a whole problem against one query's caps
/// refused every CHC-COMP 2026 BV `ssh-simplified` task (147 k to 497 k
/// argument roots plus constraint nodes against 131,072), so `validate` failed
/// and PDR, the Spacer lane and the BMC executor lanes never ran on them.
#[derive(Clone, Copy, Debug)]
pub(super) struct WalkLimits {
    /// Expression roots, and expression nodes charged per walk.
    pub(super) expr_nodes: usize,
    /// Name bytes hashed or compared (variable, sort, constructor, selector).
    pub(super) name_bytes: usize,
    /// Sort nodes visited; each distinct variable name pays at least one.
    pub(super) sort_nodes: usize,
    /// Repeated-variable sort comparisons.
    pub(super) compare_work: usize,
}

pub(super) const EXECUTOR_QUERY_LIMITS: WalkLimits = WalkLimits {
    expr_nodes: MAX_DT_EXPR_NODES,
    name_bytes: MAX_DT_NAME_BYTES,
    sort_nodes: MAX_DT_SORT_NODES,
    compare_work: MAX_DT_DEFINITION_COMPARE_WORK,
};

/// How much larger a whole-problem scan may be than one executor query: the
/// executor's tree-node ceiling, the largest expression it admits at all,
/// over one query's distinct-node cap (32).
const PROBLEM_SCAN_SCALE: usize = MAX_EXECUTOR_TREE_NODES / MAX_DT_EXPR_NODES;

/// Every per-walk cap of [`EXECUTOR_QUERY_LIMITS`], scaled by
/// [`PROBLEM_SCAN_SCALE`]. The definition-comparison and datatype-count caps
/// stay per query: they grow with datatype definitions, not problem size.
pub(super) const PROBLEM_SCAN_LIMITS: WalkLimits = WalkLimits {
    expr_nodes: MAX_DT_EXPR_NODES * PROBLEM_SCAN_SCALE,
    name_bytes: MAX_DT_NAME_BYTES * PROBLEM_SCAN_SCALE,
    sort_nodes: MAX_DT_SORT_NODES * PROBLEM_SCAN_SCALE,
    compare_work: MAX_DT_DEFINITION_COMPARE_WORK * PROBLEM_SCAN_SCALE,
};

/// A fail-closed reason for declining executor-bound datatype declarations.
#[derive(Debug, thiserror::Error)]
pub(crate) enum DatatypeDeclarationError {
    #[error("datatype declaration resource limit exceeded: {0}")]
    ResourceLimit(&'static str),
    #[error("datatype sort '{0}' has conflicting in-memory definitions")]
    ConflictingDefinition(String),
    #[error("datatype sort '{0}' has no constructors")]
    EmptyDatatype(String),
}

/// A non-datatype uninterpreted function used by an executor-bound expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct UninterpretedFunctionDeclaration {
    pub(crate) name: String,
    pub(crate) return_sort: ChcSort,
    pub(crate) argument_sorts: Vec<ChcSort>,
}

/// Collect unique datatype declarations from a set of variables.
///
/// The returned declarations are deduplicated and sorted by datatype name so
/// the replay bytes do not depend on variable or hash-table traversal order.
/// Collection is iterative and bounded: executor dispatch fails closed rather
/// than recursing or allocating without limit on a hostile in-memory term.
#[cfg(test)]
pub(super) fn collect_dt_declarations(
    vars: &[ChcVar],
) -> Result<Vec<(&str, &[ChcDtConstructor])>, DatatypeDeclarationError> {
    let mut collector = DatatypeDeclarationCollector::default();
    for var in vars {
        collector.visit_variable(var)?;
    }
    Ok(collector.finish())
}

/// Collect unique datatype declarations from free variables and expression-local
/// constructor/selector/tester terms.
pub(crate) fn collect_dt_declarations_for_expr<'a>(
    vars: &'a [ChcVar],
    expr: &'a ChcExpr,
) -> Result<Vec<(&'a str, &'a [ChcDtConstructor])>, DatatypeDeclarationError> {
    collect_dt_declarations_for_expr_sized(vars, expr).map(|(declarations, _)| declarations)
}

/// Sizes an admission walk measured (bridge item D-1 board counters).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ExprAdmissionSizes {
    /// Distinct nodes (pointer identity).
    pub(crate) unique_nodes: usize,
    /// Tree expansion.
    pub(crate) tree_nodes: usize,
}

/// [`collect_dt_declarations_for_expr`] that also reports the admitted sizes.
pub(crate) fn collect_dt_declarations_for_expr_sized<'a>(
    vars: &'a [ChcVar],
    expr: &'a ChcExpr,
) -> Result<(Vec<(&'a str, &'a [ChcDtConstructor])>, ExprAdmissionSizes), DatatypeDeclarationError>
{
    let mut collector = DatatypeDeclarationCollector::default();
    for var in vars {
        collector.visit_variable(var)?;
    }
    collector.visit_expr(expr)?;
    let sizes = collector.sizes();
    if sizes.tree_nodes > MAX_EXECUTOR_TREE_NODES {
        return Err(DatatypeDeclarationError::ResourceLimit(
            "executor expression tree nodes",
        ));
    }
    Ok((collector.finish(), sizes))
}

#[derive(Clone, Copy, Debug)]
struct ExprMemo {
    /// Longest path below the node, in edges.
    height: u32,
    /// Tree expansion, saturated at `MAX_EXECUTOR_TREE_NODES + 1`.
    tree: u64,
}

/// Tree size at or below which the admission walk and the sort scans run as
/// plain tree walks, without the pointer memo / visited set of bridge item
/// D-1. Those structures exist for DAG-shared queries whose TREE is large
/// (the wide `oral_messages` IMC k-queries, 10^5..10^8 tree nodes); on the
/// small queries that dominate the query stream (PDR, Houdini, the persistent
/// executor contexts: hundreds of nodes) their hashing is pure overhead —
/// measured on lustre `metros_4_e2_968_e3_931`, where it pushed the Houdini
/// prepass past its 10 s route budget (sat 16.9 s -> 33.8 s, 3/3 paired).
/// Below this size a plain walk has the same depth, the same tree size and,
/// as the tree has at most this many occurrences, cannot reach the
/// unique-node cap either; per-occurrence name charging is batch 3's
/// behaviour for shared leaves (WP-F charges a leaf per DAG edge).
const DAG_WALK_MIN_TREE_NODES: usize = 4_096;

/// Tree expansion of `root` when it is at most `limit` nodes, else `None`.
/// A plain counting walk (no hashing) that stops as soon as the count
/// passes `limit`, so its cost is bounded by `limit` whatever the DAG.
fn bounded_tree_size(root: &ChcExpr, limit: usize) -> Option<usize> {
    let mut stack = vec![root];
    let mut nodes = 1usize;
    while let Some(node) = stack.pop() {
        let children = expr_children(node);
        nodes = nodes.saturating_add(children.len());
        if nodes > limit {
            return None;
        }
        stack.extend(children.iter().map(AsRef::as_ref));
    }
    Some(nodes)
}

/// Pointer identity of an expression node. Every walk here borrows its
/// roots for the whole walk, so addresses are stable and unique.
pub(super) fn expr_key(expr: &ChcExpr) -> usize {
    std::ptr::from_ref(expr) as usize
}

/// Semantic children used by metadata, sort and resource inspection only.
/// A lambda's closed body is code and its captures are the environment; both
/// count here. Free-variable substitution continues to use expr::dag::children.
#[derive(Clone, Copy)]
pub(super) struct ExprChildren<'a> {
    body: Option<&'a Arc<ChcExpr>>,
    arguments: &'a [Arc<ChcExpr>],
}

impl<'a> ExprChildren<'a> {
    pub(super) fn len(self) -> usize {
        self.arguments.len() + usize::from(self.body.is_some())
    }

    fn get(self, index: usize) -> Option<&'a Arc<ChcExpr>> {
        match (self.body, index) {
            (Some(body), 0) => Some(body),
            (Some(_), index) => self.arguments.get(index - 1),
            (None, index) => self.arguments.get(index),
        }
    }

    pub(super) fn iter(self) -> impl DoubleEndedIterator<Item = &'a Arc<ChcExpr>> {
        self.body.into_iter().chain(self.arguments.iter())
    }
}

pub(super) fn expr_children(expr: &ChcExpr) -> ExprChildren<'_> {
    let (body, arguments) = match expr {
        ChcExpr::ArrayLambda(lambda) => (Some(lambda.body()), lambda.captures()),
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            (None, args.as_slice())
        }
        ChcExpr::ConstArray(_, value) => (None, std::slice::from_ref(value)),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => (None, &[][..]),
    };
    ExprChildren { body, arguments }
}

pub(crate) fn collect_dt_declarations_for_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
) -> Result<Vec<(&'a str, &'a [ChcDtConstructor])>, DatatypeDeclarationError> {
    collect_dt_declarations_for_exprs_within(exprs, EXECUTOR_QUERY_LIMITS)
}

fn collect_dt_declarations_for_exprs_within<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    limits: WalkLimits,
) -> Result<Vec<(&'a str, &'a [ChcDtConstructor])>, DatatypeDeclarationError> {
    let mut collector = DatatypeDeclarationCollector::new(limits);
    let mut root_count = 0usize;
    for expr in exprs {
        root_count = bounded_add(
            root_count,
            1,
            limits.expr_nodes,
            "executor expression roots",
        )?;
        collector.visit_expr(expr)?;
    }
    Ok(collector.finish())
}

struct DatatypeDeclarationCollector<'a> {
    limits: WalkLimits,
    definitions: FxHashMap<&'a str, &'a [ChcDtConstructor]>,
    checked_variable_sorts: FxHashMap<&'a str, &'a ChcSort>,
    checked_definition_pairs: FxHashSet<(&'a str, usize, usize, usize, usize)>,
    expanded_definition_instances: FxHashSet<(usize, usize)>,
    sort_nodes: usize,
    /// Distinct expression nodes visited (capped by `limits.expr_nodes`).
    expr_nodes: usize,
    /// Tree expansion of every visited root (saturating just above
    /// `MAX_EXECUTOR_TREE_NODES`; enforced by the single-query admission).
    tree_nodes: usize,
    /// Completed nodes: pointer -> (height, tree size).
    expr_memo: FxHashMap<usize, ExprMemo>,
    constructors: usize,
    selectors: usize,
    expanded_constructors: usize,
    expanded_selectors: usize,
    name_bytes: usize,
    definition_compare_work: usize,
    variable_sort_compare_work: usize,
}

impl Default for DatatypeDeclarationCollector<'_> {
    fn default() -> Self {
        Self::new(EXECUTOR_QUERY_LIMITS)
    }
}

impl<'a> DatatypeDeclarationCollector<'a> {
    fn new(limits: WalkLimits) -> Self {
        Self {
            limits,
            definitions: FxHashMap::default(),
            checked_variable_sorts: FxHashMap::default(),
            checked_definition_pairs: FxHashSet::default(),
            expanded_definition_instances: FxHashSet::default(),
            sort_nodes: 0,
            expr_nodes: 0,
            tree_nodes: 0,
            expr_memo: FxHashMap::default(),
            constructors: 0,
            selectors: 0,
            expanded_constructors: 0,
            expanded_selectors: 0,
            name_bytes: 0,
            definition_compare_work: 0,
            variable_sort_compare_work: 0,
        }
    }

    fn charge_name_bytes(&mut self, bytes: usize) -> Result<(), DatatypeDeclarationError> {
        self.name_bytes = bounded_add(
            self.name_bytes,
            bytes,
            self.limits.name_bytes,
            "executor surface name bytes",
        )?;
        Ok(())
    }

    fn visit_variable(&mut self, variable: &'a ChcVar) -> Result<(), DatatypeDeclarationError> {
        // Name hashing/comparison remains charged for EVERY visited variable
        // node, even a hit (the expression walk visits each distinct node
        // once, so a variable node shared by pointer is charged once).
        // Different clauses may use one name with different sorts.
        self.charge_name_bytes(variable.name.len())?;
        if let Some(previous) = self.checked_variable_sorts.get(variable.name.as_str()) {
            if variable_sorts::same_metadata_shape(
                previous,
                &variable.sort,
                &mut self.variable_sort_compare_work,
                &mut self.name_bytes,
                self.limits,
            )? {
                return Ok(());
            }
        }
        self.visit_sort(&variable.sort)?;
        // Each new entry has paid at least one sort node, so the unchanged
        // aggregate sort-node cap also bounds this borrowed table's size.
        self.checked_variable_sorts
            .entry(variable.name.as_str())
            .or_insert(&variable.sort);
        Ok(())
    }

    fn definition_matches(
        &mut self,
        name: &'a str,
        previous: &'a [ChcDtConstructor],
        current: &'a [ChcDtConstructor],
    ) -> Result<bool, DatatypeDeclarationError> {
        if std::ptr::eq(previous.as_ptr(), current.as_ptr()) && previous.len() == current.len() {
            return Ok(true);
        }
        let pair = (
            name,
            previous.as_ptr() as usize,
            previous.len(),
            current.as_ptr() as usize,
            current.len(),
        );
        if self.checked_definition_pairs.contains(&pair) {
            return Ok(true);
        }
        if !datatype_definitions_equivalent_bounded(
            previous,
            current,
            &mut self.definition_compare_work,
        )? {
            return Ok(false);
        }
        // This memo records ONLY a completed emitted-signature comparison.
        // visit_sort still expands every distinct metadata allocation below.
        // Borrowed input remains live throughout this collector's lifetime.
        if self.checked_definition_pairs.len() >= self.limits.sort_nodes {
            return Err(DatatypeDeclarationError::ResourceLimit(
                "datatype comparison memo entries",
            ));
        }
        self.checked_definition_pairs.insert(pair);
        Ok(true)
    }

    fn visit_sort(&mut self, root: &'a ChcSort) -> Result<(), DatatypeDeclarationError> {
        let mut stack = vec![(root, 0usize)];
        while let Some((sort, depth)) = stack.pop() {
            if depth > MAX_DT_NESTING_DEPTH {
                return Err(DatatypeDeclarationError::ResourceLimit(
                    "datatype sort nesting depth",
                ));
            }
            self.sort_nodes = bounded_add(
                self.sort_nodes,
                1,
                self.limits.sort_nodes,
                "datatype sort nodes",
            )?;

            match sort {
                ChcSort::Datatype { name, constructors } => {
                    self.name_bytes = bounded_add(
                        self.name_bytes,
                        name.len(),
                        self.limits.name_bytes,
                        "datatype name bytes",
                    )?;
                    if let Some(previous) = self.definitions.get(name.as_str()).copied() {
                        if !self.definition_matches(name, previous, constructors)? {
                            return Err(DatatypeDeclarationError::ConflictingDefinition(
                                name.clone(),
                            ));
                        }
                    } else {
                        if constructors.is_empty() {
                            return Err(DatatypeDeclarationError::EmptyDatatype(name.clone()));
                        }
                        if self.definitions.len() >= MAX_DT_DECLARATIONS {
                            return Err(DatatypeDeclarationError::ResourceLimit(
                                "datatype definitions",
                            ));
                        }
                        self.constructors = bounded_add(
                            self.constructors,
                            constructors.len(),
                            MAX_DT_CONSTRUCTORS,
                            "datatype constructors",
                        )?;
                        let selector_count = constructors
                            .iter()
                            .try_fold(0usize, |count, constructor| {
                                count.checked_add(constructor.selectors.len())
                            })
                            .ok_or(DatatypeDeclarationError::ResourceLimit(
                                "datatype selectors",
                            ))?;
                        self.selectors = bounded_add(
                            self.selectors,
                            selector_count,
                            MAX_DT_SELECTORS,
                            "datatype selectors",
                        )?;
                        self.definitions
                            .insert(name.as_str(), constructors.as_slice());
                    }

                    // Distinct finite-resolution snapshots of a recursive
                    // datatype can carry additional nested definitions. Walk
                    // each metadata allocation once so a conflicting nested
                    // definition cannot be hidden behind a same-signature
                    // outer sort or make output depend on variable order.
                    let instance_key = (constructors.node_addr() as usize, constructors.len());
                    if !self.expanded_definition_instances.insert(instance_key) {
                        continue;
                    }
                    self.expanded_constructors = bounded_add(
                        self.expanded_constructors,
                        constructors.len(),
                        MAX_DT_CONSTRUCTORS,
                        "datatype metadata constructors",
                    )?;
                    let expanded_selector_count = constructors
                        .iter()
                        .try_fold(0usize, |count, constructor| {
                            count.checked_add(constructor.selectors.len())
                        })
                        .ok_or(DatatypeDeclarationError::ResourceLimit(
                            "datatype metadata selectors",
                        ))?;
                    self.expanded_selectors = bounded_add(
                        self.expanded_selectors,
                        expanded_selector_count,
                        MAX_DT_SELECTORS,
                        "datatype metadata selectors",
                    )?;
                    for constructor in constructors.iter() {
                        self.name_bytes = bounded_add(
                            self.name_bytes,
                            constructor.name.len(),
                            self.limits.name_bytes,
                            "datatype name bytes",
                        )?;
                        for selector in &constructor.selectors {
                            self.name_bytes = bounded_add(
                                self.name_bytes,
                                selector.name.len(),
                                self.limits.name_bytes,
                                "datatype name bytes",
                            )?;
                        }
                    }
                    // Reverse pushes preserve source order for deterministic
                    // resource-limit behavior. Final declarations are sorted.
                    for selector in constructors
                        .iter()
                        .rev()
                        .flat_map(|constructor| constructor.selectors.iter().rev())
                    {
                        stack.push((&selector.sort, depth + 1));
                    }
                }
                ChcSort::Array(key, value) => {
                    stack.push((value.as_ref(), depth + 1));
                    stack.push((key.as_ref(), depth + 1));
                }
                ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
                ChcSort::Uninterpreted(name) => {
                    self.name_bytes = bounded_add(
                        self.name_bytes,
                        name.len(),
                        self.limits.name_bytes,
                        "datatype name bytes",
                    )?;
                }
            }
        }
        Ok(())
    }

    /// Admit one root. Pointer-memoised (bridge item D-1; WP-F's DAG-linear
    /// admission): each distinct node is visited and charged once against
    /// `limits.expr_nodes`; the nesting depth stays exact (a shared node met
    /// again is charged at its deeper occurrence through its memoised
    /// height); the root's tree expansion is accumulated (saturating) for the
    /// single-query executor admission's `MAX_EXECUTOR_TREE_NODES` check.
    fn visit_expr(&mut self, root: &'a ChcExpr) -> Result<(), DatatypeDeclarationError> {
        if let Some(memo) = self.expr_memo.get(&expr_key(root)) {
            let tree = memo.tree;
            self.charge_tree(tree);
            return Ok(());
        }
        if let Some(tree) = bounded_tree_size(root, DAG_WALK_MIN_TREE_NODES) {
            // Small tree: one `enter_expr` per occurrence, pre-order
            // left-to-right like the memoised walk, depth exact.
            let mut stack: Vec<(&'a ChcExpr, usize)> = vec![(root, 0)];
            while let Some((node, depth)) = stack.pop() {
                self.enter_expr(node, depth)?;
                stack.extend(
                    expr_children(node)
                        .iter()
                        .rev()
                        .map(|child| (child.as_ref(), depth + 1)),
                );
            }
            self.charge_tree(u64::try_from(tree).unwrap_or(u64::MAX));
            return Ok(());
        }
        self.enter_expr(root, 0)?;
        let mut stack: Vec<(&'a ChcExpr, usize)> = vec![(root, 0)];
        while let Some(top) = stack.last_mut() {
            let node: &'a ChcExpr = top.0;
            let children = expr_children(node);
            if top.1 < children.len() {
                let Some(child) = children.get(top.1) else {
                    return Err(DatatypeDeclarationError::ResourceLimit(
                        "semantic child position",
                    ));
                };
                let child: &'a ChcExpr = child.as_ref();
                top.1 += 1;
                // The stack is the path root..parent, so the child sits at
                // depth `stack.len()`.
                let depth = stack.len();
                if let Some(memo) = self.expr_memo.get(&expr_key(child)) {
                    if depth.saturating_add(memo.height as usize) > MAX_DT_NESTING_DEPTH {
                        return Err(DatatypeDeclarationError::ResourceLimit(
                            "datatype expression nesting depth",
                        ));
                    }
                    continue;
                }
                self.enter_expr(child, depth)?;
                stack.push((child, 0));
            } else {
                stack.pop();
                self.leave_expr(node, children);
            }
        }
        let tree = self
            .expr_memo
            .get(&expr_key(root))
            .map_or(1, |memo| memo.tree);
        self.charge_tree(tree);
        Ok(())
    }

    /// First visit of a distinct node: depth and unique-node caps, then the
    /// node's own name/sort charges.
    fn enter_expr(
        &mut self,
        expr: &'a ChcExpr,
        depth: usize,
    ) -> Result<(), DatatypeDeclarationError> {
        if depth > MAX_DT_NESTING_DEPTH {
            return Err(DatatypeDeclarationError::ResourceLimit(
                "datatype expression nesting depth",
            ));
        }
        self.expr_nodes = bounded_add(
            self.expr_nodes,
            1,
            self.limits.expr_nodes,
            "datatype expression nodes",
        )?;
        match expr {
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Op(_, _) => {}
            ChcExpr::IsTesterMarker(name) | ChcExpr::PredicateApp(name, _, _) => {
                self.charge_name_bytes(name.len())?;
            }
            ChcExpr::Var(var) => self.visit_variable(var)?,
            ChcExpr::FuncApp(name, sort, _) => {
                self.charge_name_bytes(name.len())?;
                self.visit_sort(sort)?;
            }
            ChcExpr::ConstArrayMarker(sort) | ChcExpr::ConstArray(sort, _) => {
                self.visit_sort(sort)?;
            }
            ChcExpr::ArrayLambda(lambda) => {
                self.visit_variable(lambda.binder())?;
                for formal in lambda.formals() {
                    self.visit_variable(formal)?;
                }
            }
        }
        Ok(())
    }

    /// Post-order completion: every child is memoised, so height and tree
    /// size are final.
    fn leave_expr(&mut self, expr: &'a ChcExpr, children: ExprChildren<'a>) {
        let mut height = 0u32;
        let mut tree = 1u64;
        for child in children.iter() {
            if let Some(memo) = self.expr_memo.get(&expr_key(child)) {
                height = height.max(memo.height.saturating_add(1));
                tree = tree.saturating_add(memo.tree);
            }
        }
        // Saturate just above the cap: the exact value past it is never read.
        let tree = tree.min(MAX_EXECUTOR_TREE_NODES as u64 + 1);
        self.expr_memo
            .insert(expr_key(expr), ExprMemo { height, tree });
    }

    /// Accumulate a visited root's tree expansion, saturating just above
    /// `MAX_EXECUTOR_TREE_NODES` (the exact value past it is never read).
    /// Never fails: only the single-query executor admission enforces the
    /// cap (see [`MAX_EXECUTOR_TREE_NODES`]).
    fn charge_tree(&mut self, tree: u64) {
        let tree = usize::try_from(tree).unwrap_or(usize::MAX);
        self.tree_nodes = self
            .tree_nodes
            .saturating_add(tree)
            .min(MAX_EXECUTOR_TREE_NODES + 1);
    }

    fn sizes(&self) -> ExprAdmissionSizes {
        ExprAdmissionSizes {
            unique_nodes: self.expr_nodes,
            tree_nodes: self.tree_nodes,
        }
    }

    fn finish(self) -> Vec<(&'a str, &'a [ChcDtConstructor])> {
        let mut declarations: Vec<_> = self.definitions.into_iter().collect();
        declarations.sort_by(|left, right| left.0.cmp(right.0));
        declarations
    }
}

/// Compare datatype definitions by their emitted SMT signature, not by the
/// recursively embedded metadata carried by `ChcSort::Datatype`.  Parsed
/// mutually recursive sorts intentionally contain finite-resolution snapshots
/// of one another, so derived structural equality is both semantically wrong
/// and an unbounded recursive pre-gate.  Datatype sort identity on the SMT
/// surface is its name; arrays are compared iteratively down to those names.
fn datatype_definitions_equivalent_bounded(
    left: &[ChcDtConstructor],
    right: &[ChcDtConstructor],
    work: &mut usize,
) -> Result<bool, DatatypeDeclarationError> {
    *work = bounded_add(
        *work,
        left.len().max(right.len()),
        MAX_DT_DEFINITION_COMPARE_WORK,
        "datatype definition comparison",
    )?;
    if left.len() != right.len() || left.len() > MAX_DT_CONSTRUCTORS {
        return Ok(false);
    }

    for (left_constructor, right_constructor) in left.iter().zip(right) {
        *work = bounded_add(
            *work,
            left_constructor
                .name
                .len()
                .max(right_constructor.name.len()),
            MAX_DT_DEFINITION_COMPARE_WORK,
            "datatype definition comparison",
        )?;
        if left_constructor.name != right_constructor.name
            || left_constructor.selectors.len() != right_constructor.selectors.len()
        {
            return Ok(false);
        }
        for (left_selector, right_selector) in left_constructor
            .selectors
            .iter()
            .zip(&right_constructor.selectors)
        {
            *work = bounded_add(
                *work,
                left_selector.name.len().max(right_selector.name.len()),
                MAX_DT_DEFINITION_COMPARE_WORK,
                "datatype definition comparison",
            )?;
            if left_selector.name != right_selector.name
                || !datatype_sorts_equivalent_bounded(
                    &left_selector.sort,
                    &right_selector.sort,
                    work,
                )?
            {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn datatype_sorts_equivalent_bounded(
    left: &ChcSort,
    right: &ChcSort,
    work: &mut usize,
) -> Result<bool, DatatypeDeclarationError> {
    let mut stack = vec![(left, right, 0usize)];
    while let Some((left, right, depth)) = stack.pop() {
        if depth > MAX_DT_NESTING_DEPTH {
            return Err(DatatypeDeclarationError::ResourceLimit(
                "datatype definition comparison depth",
            ));
        }
        *work = bounded_add(
            *work,
            1,
            MAX_DT_DEFINITION_COMPARE_WORK,
            "datatype definition comparison",
        )?;
        match (left, right) {
            (ChcSort::Bool, ChcSort::Bool)
            | (ChcSort::Int, ChcSort::Int)
            | (ChcSort::Real, ChcSort::Real) => {}
            (ChcSort::BitVec(left), ChcSort::BitVec(right)) if left == right => {}
            (ChcSort::Array(left_key, left_value), ChcSort::Array(right_key, right_value)) => {
                stack.push((left_value, right_value, depth + 1));
                stack.push((left_key, right_key, depth + 1));
            }
            (
                ChcSort::Datatype { name: left, .. } | ChcSort::Uninterpreted(left),
                ChcSort::Datatype { name: right, .. } | ChcSort::Uninterpreted(right),
            ) if left == right => {}
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn bounded_add(
    current: usize,
    increment: usize,
    limit: usize,
    resource: &'static str,
) -> Result<usize, DatatypeDeclarationError> {
    current
        .checked_add(increment)
        .filter(|total| *total <= limit)
        .ok_or(DatatypeDeclarationError::ResourceLimit(resource))
}

fn push_dt_text(output: &mut String, text: &str) -> Result<(), DatatypeDeclarationError> {
    let new_len = output
        .len()
        .checked_add(text.len())
        .filter(|length| *length <= MAX_DT_DECLARATION_BYTES)
        .ok_or(DatatypeDeclarationError::ResourceLimit(
            "datatype declaration bytes",
        ))?;
    output.reserve(new_len - output.len());
    output.push_str(text);
    Ok(())
}

fn validate_emitted_sort(
    root: &ChcSort,
    sort_nodes: &mut usize,
    name_bytes: &mut usize,
) -> Result<(), DatatypeDeclarationError> {
    let mut stack = vec![(root, 0usize)];
    while let Some((sort, depth)) = stack.pop() {
        if depth > MAX_DT_NESTING_DEPTH {
            return Err(DatatypeDeclarationError::ResourceLimit(
                "datatype sort nesting depth",
            ));
        }
        *sort_nodes = bounded_add(*sort_nodes, 1, MAX_DT_SORT_NODES, "datatype sort nodes")?;
        match sort {
            ChcSort::Array(key, value) => {
                stack.push((value.as_ref(), depth + 1));
                stack.push((key.as_ref(), depth + 1));
            }
            ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } => {
                *name_bytes = bounded_add(
                    *name_bytes,
                    name.len(),
                    MAX_DT_NAME_BYTES,
                    "datatype name bytes",
                )?;
            }
            ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
        }
    }
    Ok(())
}

/// Emit one deterministic, simultaneous SMT-LIB datatype declaration.
///
/// A sequence of `declare-datatype` commands cannot refer forward to a nested
/// datatype (and cannot express mutual recursion). `declare-datatypes` binds
/// every sort head before any constructor body is checked, which is the
/// standard SMT-LIB representation for both cases.
pub(crate) fn emit_declare_datatypes(
    declarations: &[(&str, &[ChcDtConstructor])],
) -> Result<String, DatatypeDeclarationError> {
    if declarations.is_empty() {
        return Ok(String::new());
    }
    if declarations.len() > MAX_DT_DECLARATIONS {
        return Err(DatatypeDeclarationError::ResourceLimit(
            "datatype definitions",
        ));
    }

    // Admit every caller-provided byte and sort surface before cloning,
    // sorting, comparing, quoting, or recursively formatting it.
    let mut constructor_count = 0usize;
    let mut selector_count = 0usize;
    let mut sort_nodes = 0usize;
    let mut name_bytes = 0usize;
    for (name, constructors) in declarations {
        name_bytes = bounded_add(
            name_bytes,
            name.len(),
            MAX_DT_NAME_BYTES,
            "datatype name bytes",
        )?;
        if constructors.is_empty() {
            return Err(DatatypeDeclarationError::EmptyDatatype((*name).to_string()));
        }
        constructor_count = bounded_add(
            constructor_count,
            constructors.len(),
            MAX_DT_CONSTRUCTORS,
            "datatype constructors",
        )?;
        for constructor in *constructors {
            name_bytes = bounded_add(
                name_bytes,
                constructor.name.len(),
                MAX_DT_NAME_BYTES,
                "datatype name bytes",
            )?;
            selector_count = bounded_add(
                selector_count,
                constructor.selectors.len(),
                MAX_DT_SELECTORS,
                "datatype selectors",
            )?;
            for selector in &constructor.selectors {
                name_bytes = bounded_add(
                    name_bytes,
                    selector.name.len(),
                    MAX_DT_NAME_BYTES,
                    "datatype name bytes",
                )?;
                validate_emitted_sort(&selector.sort, &mut sort_nodes, &mut name_bytes)?;
            }
        }
    }

    let mut canonical = declarations.to_vec();
    canonical.sort_by(|left, right| left.0.cmp(right.0));
    let mut unique = Vec::with_capacity(canonical.len());
    let mut definition_compare_work = 0usize;
    for declaration in canonical {
        if let Some(previous) = unique.last() {
            let previous: &(&str, &[ChcDtConstructor]) = previous;
            if previous.0 == declaration.0 {
                if !std::ptr::eq(previous.1.as_ptr(), declaration.1.as_ptr())
                    && !datatype_definitions_equivalent_bounded(
                        previous.1,
                        declaration.1,
                        &mut definition_compare_work,
                    )?
                {
                    return Err(DatatypeDeclarationError::ConflictingDefinition(
                        declaration.0.to_string(),
                    ));
                }
                continue;
            }
        }
        unique.push(declaration);
    }

    let mut output = String::with_capacity(256);
    push_dt_text(&mut output, "(declare-datatypes (")?;
    for (index, (name, _)) in unique.iter().enumerate() {
        if index != 0 {
            push_dt_text(&mut output, " ")?;
        }
        push_dt_text(&mut output, "(")?;
        push_dt_text(&mut output, &quote_symbol(name))?;
        push_dt_text(&mut output, " 0)")?;
    }
    push_dt_text(&mut output, ") (")?;
    for (datatype_index, (_, constructors)) in unique.iter().enumerate() {
        if datatype_index != 0 {
            push_dt_text(&mut output, " ")?;
        }
        push_dt_text(&mut output, "(")?;
        for (constructor_index, constructor) in constructors.iter().enumerate() {
            if constructor_index != 0 {
                push_dt_text(&mut output, " ")?;
            }
            push_dt_text(&mut output, "(")?;
            push_dt_text(&mut output, &quote_symbol(&constructor.name))?;
            for selector in &constructor.selectors {
                push_dt_text(&mut output, " (")?;
                push_dt_text(&mut output, &quote_symbol(&selector.name))?;
                push_dt_text(&mut output, " ")?;
                push_dt_text(&mut output, &sort_to_smtlib(&selector.sort))?;
                push_dt_text(&mut output, ")")?;
            }
            push_dt_text(&mut output, ")")?;
        }
        push_dt_text(&mut output, ")")?;
    }
    push_dt_text(&mut output, "))\n")?;
    Ok(output)
}

/// Emit a `(declare-datatype Name ((ctor1 (sel1 Sort1) ...) ...))` command.
#[cfg(test)]
pub(crate) fn emit_declare_datatype(name: &str, ctors: &[ChcDtConstructor]) -> String {
    let mut s = String::new();
    s.push_str(&format!("(declare-datatype {} (", quote_symbol(name)));
    for ctor in ctors {
        s.push('(');
        s.push_str(&quote_symbol(&ctor.name));
        for sel in &ctor.selectors {
            s.push_str(&format!(
                " ({} {})",
                quote_symbol(&sel.name),
                sort_to_smtlib(&sel.sort)
            ));
        }
        s.push(')');
    }
    s.push_str("))\n");
    s
}

/// Collect ordinary uninterpreted-function declarations needed to reparse an
/// executor-bound expression.
///
/// `ChcExpr::FuncApp` also represents datatype constructors/selectors/testers
/// and the three arithmetic conversion builtins.  Those are already declared
/// by `declare-datatype` or by the active logic and must not be redeclared.
/// Ordinary UFs, however, have no other declaration source because a CHC
/// expression retains the typed application rather than its original command.
///
/// SMT-LIB does not overload ordinary user functions.  If an in-memory caller
/// constructs two signatures with one name, reject the executor dispatch
/// rather than serializing a parse-order-dependent script.
pub(crate) fn collect_uninterpreted_function_declarations(
    expr: &ChcExpr,
) -> ChcResult<Vec<UninterpretedFunctionDeclaration>> {
    collect_uninterpreted_function_declarations_for_exprs(std::iter::once(expr))
}

/// Collect each distinct syntactic application of an ordinary UF.
///
/// The returned terms are the finite observation points for SAT-model
/// extraction.  Datatype functions and arithmetic conversion builtins are
/// excluded by reusing the declaration collector's classification rather than
/// duplicating a name-based approximation here.
#[cfg(test)]
pub(crate) fn collect_uninterpreted_function_applications(
    expr: &ChcExpr,
) -> ChcResult<Vec<ChcExpr>> {
    collect_uninterpreted_function_applications_for_exprs(std::iter::once(expr))
}

/// Collect each distinct ordinary-UF application across multiple expressions.
pub(crate) fn collect_uninterpreted_function_applications_for_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
) -> ChcResult<Vec<ChcExpr>> {
    Ok(collect_uninterpreted_function_surface(exprs, EXECUTOR_QUERY_LIMITS)?.applications)
}

struct UninterpretedFunctionSurface {
    declarations: Vec<UninterpretedFunctionDeclaration>,
    applications: Vec<ChcExpr>,
}

fn executor_resource_limit(resource: &str) -> ChcError {
    ChcError::Internal(format!(
        "executor expression resource limit exceeded: {resource}"
    ))
}

fn bounded_executor_expr_roots<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    max_roots: usize,
) -> ChcResult<Vec<&'a ChcExpr>> {
    let mut roots = Vec::new();
    for expr in exprs {
        if roots.len() >= max_roots {
            return Err(executor_resource_limit("expression roots"));
        }
        roots.push(expr);
    }
    Ok(roots)
}

fn push_bounded_executor_expr_root<'a>(
    roots: &mut Vec<&'a ChcExpr>,
    expr: &'a ChcExpr,
    max_roots: usize,
) -> ChcResult<()> {
    if roots.len() >= max_roots {
        return Err(executor_resource_limit("expression roots"));
    }
    roots.push(expr);
    Ok(())
}

fn collect_uninterpreted_function_surface<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    limits: WalkLimits,
) -> ChcResult<UninterpretedFunctionSurface> {
    let max_nodes = limits.expr_nodes;
    let exprs = bounded_executor_expr_roots(exprs, max_nodes)?;

    // One collector owns the caps for the complete expression set.  Calling a
    // fresh collector per root would let a large CHC problem multiply every
    // node/name/datatype limit by its clause count.
    let datatype_declarations =
        collect_dt_declarations_for_exprs_within(exprs.iter().copied(), limits)
            .map_err(|error| ChcError::Internal(error.to_string()))?;
    let mut datatype_constructors: FxHashSet<&str> = FxHashSet::default();
    let mut datatype_selectors: FxHashSet<&str> = FxHashSet::default();
    for (_, constructors) in datatype_declarations {
        for constructor in constructors {
            datatype_constructors.insert(constructor.name.as_str());
            datatype_selectors.extend(
                constructor
                    .selectors
                    .iter()
                    .map(|selector| selector.name.as_str()),
            );
        }
    }

    let mut declarations = Vec::new();
    let mut applications = Vec::new();
    let mut seen_applications = FxHashSet::default();
    let mut signatures: FxHashMap<String, (ChcSort, Vec<ChcSort>)> = FxHashMap::default();
    let mut stack: Vec<_> = exprs.into_iter().map(|expr| (expr, false)).collect();
    let mut expr_nodes = 0usize;
    let mut ordinary_application_occurrences = 0usize;
    let mut uf_argument_occurrences = 0usize;
    // DAG-linear admission (WP-F): a shared inner node is expanded once.
    // Its UF declaration/signature/application-occurrence charges were
    // already recorded at the first visit (`signatures`/`seen_applications`
    // are idempotent), so a repeat visit is skipped before it can inflate
    // any of this loop's resource counters by its tree-occurrence count.
    // This is the "original expression-DAG admission" the alias-emission
    // budget above is deliberately kept separate from. (Workstream D bridge
    // item D-1 needs exactly this: unique-node charging of shared subterms.)
    let mut seen: FxHashSet<(*const ChcExpr, bool)> = FxHashSet::default();
    while let Some((current, bound_body)) = stack.pop() {
        if expr_children(current).len() != 0
            && !seen.insert((std::ptr::from_ref::<ChcExpr>(current), bound_body))
        {
            continue;
        }
        expr_nodes = expr_nodes
            .checked_add(1)
            .filter(|nodes| *nodes <= max_nodes)
            .ok_or_else(|| executor_resource_limit("expression nodes"))?;
        match current {
            ChcExpr::FuncApp(name, return_sort, args) => {
                let pending = stack
                    .len()
                    .checked_add(args.len())
                    .ok_or_else(|| executor_resource_limit("pending expression nodes"))?;
                if expr_nodes
                    .checked_add(pending)
                    .is_none_or(|nodes| nodes > max_nodes)
                {
                    return Err(executor_resource_limit("expression nodes"));
                }
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), bound_body)));
                let datatype_tester = name
                    .strip_prefix("is-")
                    .is_some_and(|constructor| datatype_constructors.contains(constructor));
                if matches!(name.as_str(), "to_real" | "to_int" | "is_int")
                    || datatype_constructors.contains(name.as_str())
                    || datatype_selectors.contains(name.as_str())
                    || datatype_tester
                {
                    continue;
                }

                ordinary_application_occurrences = ordinary_application_occurrences
                    .checked_add(1)
                    .filter(|count| *count <= MAX_EXECUTOR_UF_APPLICATIONS)
                    .ok_or_else(|| executor_resource_limit("UF application occurrences"))?;
                uf_argument_occurrences = uf_argument_occurrences
                    .checked_add(args.len())
                    .filter(|count| *count <= MAX_EXECUTOR_UF_ARGUMENT_OCCURRENCES)
                    .ok_or_else(|| executor_resource_limit("UF argument occurrences"))?;

                let argument_sorts: Vec<ChcSort> = args.iter().map(|arg| arg.sort()).collect();
                if let Some((previous_return, previous_arguments)) = signatures.get(name) {
                    if previous_return != return_sort || previous_arguments != &argument_sorts {
                        return Err(ChcError::Internal(format!(
                            "uninterpreted function '{name}' has conflicting signatures"
                        )));
                    }
                } else {
                    if declarations.len() >= MAX_EXECUTOR_UF_DECLARATIONS {
                        return Err(executor_resource_limit("UF declarations"));
                    }
                    signatures.insert(name.clone(), (return_sort.clone(), argument_sorts.clone()));
                    declarations.push(UninterpretedFunctionDeclaration {
                        name: name.clone(),
                        return_sort: return_sort.clone(),
                        argument_sorts,
                    });
                }

                if !bound_body && seen_applications.insert((*current).clone()) {
                    applications.push((*current).clone());
                }
            }
            ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
                let pending = stack
                    .len()
                    .checked_add(args.len())
                    .ok_or_else(|| executor_resource_limit("pending expression nodes"))?;
                if expr_nodes
                    .checked_add(pending)
                    .is_none_or(|nodes| nodes > max_nodes)
                {
                    return Err(executor_resource_limit("expression nodes"));
                }
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), bound_body)));
            }
            ChcExpr::ConstArray(_, value) => {
                if expr_nodes
                    .checked_add(stack.len())
                    .and_then(|nodes| nodes.checked_add(1))
                    .is_none_or(|nodes| nodes > max_nodes)
                {
                    return Err(executor_resource_limit("expression nodes"));
                }
                stack.push((value.as_ref(), bound_body));
            }
            ChcExpr::ArrayLambda(lambda) => {
                let pending = stack
                    .len()
                    .checked_add(lambda.captures().len())
                    .and_then(|count| count.checked_add(1))
                    .ok_or_else(|| executor_resource_limit("pending expression nodes"))?;
                if expr_nodes
                    .checked_add(pending)
                    .is_none_or(|nodes| nodes > max_nodes)
                {
                    return Err(executor_resource_limit("expression nodes"));
                }
                // Captures are evaluated in their enclosing scope. The closed
                // body contains private binders and must never yield a global
                // observation alias such as alias = f(private_index).
                stack.extend(
                    lambda
                        .captures()
                        .iter()
                        .rev()
                        .map(|arg| (arg.as_ref(), bound_body)),
                );
                stack.push((lambda.body().as_ref(), true));
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

    // Declaration order is part of replay/transcript bytes. Keep it canonical
    // even when callers supply expressions from a hash-backed problem surface.
    declarations.sort_by(|left, right| {
        left.name
            .cmp(&right.name)
            .then_with(|| left.return_sort.cmp(&right.return_sort))
            .then_with(|| left.argument_sorts.cmp(&right.argument_sorts))
    });
    Ok(UninterpretedFunctionSurface {
        declarations,
        applications,
    })
}

/// Collect one globally consistent ordinary-UF signature table for several
/// expressions that will share an SMT-LIB declaration scope.
pub(crate) fn collect_uninterpreted_function_declarations_for_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
) -> ChcResult<Vec<UninterpretedFunctionDeclaration>> {
    Ok(collect_uninterpreted_function_surface(exprs, EXECUTOR_QUERY_LIMITS)?.declarations)
}

/// Whether a predicate argument can contribute to the UF or datatype surface.
/// A literal, or a variable of a scalar sort (Bool, Int, Real, BitVec), has
/// no function application, no datatype and no sort to declare, so the
/// whole-problem scan skips it rather than charging it as a root. The test
/// reads only the root sort: every other sort is scanned, and charged, by the
/// collector, which owns the caps on walking sort metadata.
fn predicate_argument_has_surface(argument: &ChcExpr) -> bool {
    match argument {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => false,
        ChcExpr::Var(var) => !matches!(
            var.sort,
            ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_)
        ),
        _ => true,
    }
}

/// Collect ordinary UFs from every expression owned by a CHC problem.
///
/// This is the declaration source for executor sessions that serialize an
/// unbounded sequence of derived expressions (BMC/PDR).  Scanning the complete
/// problem up front also rejects a typed caller that reused one ordinary name
/// with conflicting signatures in disjoint clauses.
pub(crate) fn collect_uninterpreted_function_declarations_for_problem(
    problem: &ChcProblem,
) -> ChcResult<Vec<UninterpretedFunctionDeclaration>> {
    let max_roots = PROBLEM_SCAN_LIMITS.expr_nodes;
    let mut exprs = Vec::new();
    for clause in problem.source_clauses() {
        if let Some(constraint) = &clause.body.constraint {
            push_bounded_executor_expr_root(&mut exprs, constraint, max_roots)?;
        }
        let head_arguments = match &clause.head {
            ClauseHead::Predicate(_, args) => args.as_slice(),
            ClauseHead::False => &[],
        };
        for argument in clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter())
            .chain(head_arguments)
            .filter(|argument| predicate_argument_has_surface(argument))
        {
            push_bounded_executor_expr_root(&mut exprs, argument, max_roots)?;
        }
    }
    Ok(collect_uninterpreted_function_surface(exprs, PROBLEM_SCAN_LIMITS)?.declarations)
}

/// Emit one ordinary UF declaration for an executor-generated SMT-LIB script.
pub(crate) fn emit_declare_uninterpreted_function(
    declaration: &UninterpretedFunctionDeclaration,
) -> String {
    let arguments = declaration
        .argument_sorts
        .iter()
        .map(sort_to_smtlib)
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "(declare-fun {} ({arguments}) {})\n",
        quote_symbol(&declaration.name),
        sort_to_smtlib(&declaration.return_sort)
    )
}

/// Detect the SMT-LIB logic string based on the sorts used in the formula.
pub(crate) fn detect_logic(vars: &[ChcVar], expr: &ChcExpr) -> &'static str {
    let expr_features = expr.scan_features();
    let mut has_array = vars.iter().any(|v| sort_contains_array(&v.sort))
        || expr.contains_array_ops()
        || expr_sort_has(expr, sort_contains_array);
    // Check sorts including nested array element/index sorts (#7024) and
    // recursively nested DT selector fields (#7016). Cycle guards prevent
    // self-recursive datatypes from recursing forever.
    let has_bv = vars.iter().any(|v| sort_contains_bv(&v.sort))
        || expr_features.has_bv
        || expr_sort_has(expr, sort_contains_bv);
    let has_int =
        vars.iter().any(|v| sort_contains_int(&v.sort)) || expr_sort_has(expr, sort_contains_int);
    let has_real =
        vars.iter().any(|v| sort_contains_real(&v.sort)) || expr_sort_has(expr, sort_contains_real);
    let has_dt = vars.iter().any(|v| sort_contains_dt(&v.sort))
        || expr_features.has_dt
        || expr_sort_has(expr, sort_contains_dt);
    let has_uf = collect_uninterpreted_function_declarations(expr)
        .is_ok_and(|declarations| !declarations.is_empty());
    let has_nonlinear_mul = expr.contains_nonlinear_mul();
    if has_dt {
        has_array |= vars.iter().any(|v| sort_contains_array(&v.sort))
            || expr_sort_has(expr, sort_contains_array);
    }

    // BITVECTORS MIXED WITH INT/REAL MUST NOT TAKE A BV-ONLY FAMILY NAME.
    //
    // Every QF_*BV and _DT_*BV label routes the query to an eager bit-blast
    // pipeline that carries no integer or real theory.  Let the executor's
    // content-driven `ALL` route select its conservative BV/arithmetic lane;
    // it keeps independent BV and arithmetic constraints soundly separated
    // and fails closed when conversion operators couple the theories.
    //
    // Datatypes make this combination stricter: the executor has no combined
    // DT+BV+arithmetic solver.  Use one of its explicitly recognized,
    // fail-closed combined tokens so dispatch returns `unknown` instead of
    // selecting either `_DT_AUFBV` (drops arithmetic) or `_DT_AUFLI*` (drops
    // bit-vector semantics).  The non-DT case can use content-driven `ALL`,
    // which selects the existing independent/coupled BV-arithmetic lanes.
    if has_bv && (has_int || has_real) {
        if has_dt {
            return if has_real {
                "QF_AUFBVLIRA"
            } else {
                "QF_AUFBVLIA"
            };
        }
        return "ALL";
    }

    if has_dt {
        return match (has_array, has_bv, has_int, has_real) {
            (_, true, _, _) => "_DT_AUFBV",
            (true, _, _, true) => "_DT_AUFLIRA",
            (true, _, _, _) | (_, _, true, _) => "_DT_AUFLIA",
            (_, _, _, true) => "_DT_AUFLRA",
            _ => "QF_DT",
        };
    }

    if has_nonlinear_mul && !has_bv {
        match (has_array, has_int, has_real) {
            (true, true, true) => return "QF_AUFNIRA",
            (true, true, false) => return "QF_AUFNIA",
            (true, false, true) => return "QF_AUFNRA",
            (false, true, true) => {
                return if has_uf { "QF_UFNIRA" } else { "QF_NIRA" };
            }
            (false, true, false) => {
                return if has_uf { "QF_UFNIA" } else { "QF_NIA" };
            }
            (false, false, true) => {
                return if has_uf { "QF_UFNRA" } else { "QF_NRA" };
            }
            _ => {}
        }
    }

    // BITVECTORS MIXED WITH INT/REAL MUST NOT TAKE A BV-FAMILY NAME.
    //
    // Every QF_*BV label routes the query to the eager bit-blast pipeline, which
    // carries no integer theory, so Int-sorted variables come back with NO
    // assignment. Model completion fills them with the sort default (0), and
    // validation then correctly reports the original Int assertion violated —
    // the solve degrades to `unknown (:reason-unknown incomplete)` rather than
    // `sat`. `has_int` was previously a don't-care in both BV arms, which is
    // exactly how a formula full of Int arithmetic acquired a BV logic name.
    //
    // MEASURED: an identical five-line query is `unknown` + MODEL-UNCONFIRMED
    // under QF_AUFBV and `sat` under ALL. Across one workspace this produced
    // ~59,896 MODEL-UNCONFIRMED events.
    //
    // SOUNDNESS: `ALL` only WIDENS the admissible theory set; it never changes a
    // formula's models, so it cannot turn a violation into UNSAT. It can only
    // let a query be decided that was previously abandoned.
    if has_bv && (has_int || has_real) {
        return "ALL";
    }

    match (has_array, has_bv, has_int, has_real) {
        (true, true, _, _) => "QF_AUFBV",
        (true, _, true, true) => "QF_AUFLIRA",
        (true, _, _, true) => "QF_AUFLRA",
        (true, _, true, _) => "QF_AUFLIA",
        (true, _, _, _) => "QF_AX",
        (false, true, _, _) => "QF_UFBV",
        // Real-sorted terms must never be advertised as integer arithmetic.
        // The executor has no dedicated QF_UFLIRA category, so mixed Int/Real
        // uses its supported AUFLIRA combined route even without arrays.
        (false, false, true, true) => "QF_AUFLIRA",
        (false, false, false, true) => "QF_UFLRA",
        _ => "QF_AUFLIA",
    }
}

/// Whether any variable, function result or const-array key sort in `expr`
/// satisfies `pred`. A plain tree walk while the walk stays within
/// `DAG_WALK_MIN_TREE_NODES` visits (no allocation beyond the stack; this runs
/// up to six times per executor query in `detect_logic`), else the DAG walk
/// that visits each distinct node once (bridge item D-1). Same answer either
/// way: the predicate only reads node sorts.
fn expr_sort_has(expr: &ChcExpr, pred: fn(&ChcSort) -> bool) -> bool {
    let mut stack = vec![expr];
    let mut budget = DAG_WALK_MIN_TREE_NODES;
    while let Some(node) = stack.pop() {
        if budget == 0 {
            return expr_sort_has_dag(expr, pred);
        }
        budget -= 1;
        if node_sort_has(node, pred) {
            return true;
        }
        stack.extend(expr_children(node).iter().map(AsRef::as_ref));
    }
    false
}

/// [`expr_sort_has`] over the DAG: each distinct node (pointer identity) once.
fn expr_sort_has_dag(expr: &ChcExpr, pred: fn(&ChcSort) -> bool) -> bool {
    let mut visited: FxHashSet<usize> = FxHashSet::default();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if !visited.insert(expr_key(node)) {
            continue;
        }
        if node_sort_has(node, pred) {
            return true;
        }
        stack.extend(expr_children(node).iter().map(AsRef::as_ref));
    }
    false
}

/// The node's own sort-bearing field satisfies `pred`.
fn node_sort_has(node: &ChcExpr, pred: fn(&ChcSort) -> bool) -> bool {
    match node {
        ChcExpr::Var(var) => pred(&var.sort),
        ChcExpr::FuncApp(_, sort, _) | ChcExpr::ConstArrayMarker(sort) => pred(sort),
        ChcExpr::ConstArray(key_sort, _) => pred(key_sort),
        ChcExpr::ArrayLambda(lambda) => pred(&lambda.sort()),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Op(_, _)
        | ChcExpr::PredicateApp(_, _, _)
        | ChcExpr::IsTesterMarker(_) => false,
    }
}

/// Check if a sort (recursively) contains Int (#7024).
fn sort_contains_int(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::Int => true,
            ChcSort::Array(idx, elem) => go(idx, seen) || go(elem, seen),
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Check if a sort (recursively) contains Real (#7024).
fn sort_contains_real(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::Real => true,
            ChcSort::Array(idx, elem) => go(idx, seen) || go(elem, seen),
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Check if a sort (recursively) contains BitVec (#7024).
fn sort_contains_bv(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::BitVec(_) => true,
            ChcSort::Array(idx, elem) => go(idx, seen) || go(elem, seen),
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Check if a sort (recursively) contains datatypes (#7016).
fn sort_contains_dt(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Datatype { .. } => true,
        ChcSort::Array(idx, elem) => sort_contains_dt(idx) || sort_contains_dt(elem),
        _ => false,
    }
}

/// Check if a sort (recursively) contains arrays.
fn sort_contains_array(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::Array(_, _) => true,
            ChcSort::Datatype { name, constructors } => {
                if !seen.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|sel| go(&sel.sort, seen))
            }
            _ => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

/// Convert ChcSort to SMT-LIB sort string.
pub(crate) fn sort_to_smtlib(sort: &ChcSort) -> String {
    match sort {
        ChcSort::Bool => "Bool".to_string(),
        ChcSort::Int => "Int".to_string(),
        ChcSort::Real => "Real".to_string(),
        ChcSort::BitVec(w) => format!("(_ BitVec {w})"),
        ChcSort::Array(k, v) => format!("(Array {} {})", sort_to_smtlib(k), sort_to_smtlib(v)),
        ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } => quote_symbol(name),
    }
}

/// Quote an SMT-LIB symbol if it contains special characters.
///
/// Delegates to `ay_core::quote_symbol` for correct handling of reserved
/// words (true, false, let, assert, ...) and pipe/backslash sanitization.
pub(crate) fn quote_symbol(name: &str) -> String {
    ay_core::quote_symbol(name)
}
