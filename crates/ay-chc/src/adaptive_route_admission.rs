// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, cooperative surface admission for synchronous adaptive routes.

use crate::{CancellationToken, ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseHead};
use ay_core::{kani_compat::DetHashMap as HashMap, time::Instant};

#[derive(Clone, Copy)]
pub(super) struct RouteSurfaceCaps {
    pub max_clauses: usize,
    pub max_predicates: usize,
    pub max_predicate_arity: usize,
    pub max_actions: usize,
    pub max_datatype_defs: usize,
    pub max_datatype_members: usize,
    pub max_body_atoms_per_clause: usize,
    pub max_total_body_atoms: usize,
    pub max_expr_nodes_per_clause: usize,
    pub max_total_expr_nodes: usize,
    pub max_expr_depth: usize,
    pub max_total_sort_nodes: usize,
    pub max_sort_depth: usize,
    pub max_variable_occurrences_per_clause: usize,
    pub max_array_selects: usize,
    pub max_const_key_rewrite_visits: usize,
    pub max_total_name_bytes: usize,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct RouteSurfaceStats {
    pub total_body_atoms: usize,
    pub total_expr_nodes: usize,
    pub total_sort_nodes: usize,
    pub datatype_members: usize,
    pub datatype_sort_occurrences: usize,
    pub datatype_metadata_name_bytes: usize,
    pub array_selects: usize,
    pub projected_const_key_rewrite_visits: usize,
    pub total_name_bytes: usize,
    pub projected_dt_flatten_max_arity: usize,
    pub projected_dt_flatten_arg_occurrences: usize,
    pub projected_dt_flatten_term_columns: usize,
    pub projected_dt_flatten_work: usize,
    pub projected_dt_flatten_max_occurrence_width: usize,
    pub projected_dt_flatten_expr_clone_work: usize,
    pub projected_dt_flatten_generated_name_bytes: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum RouteAdmissionFailure {
    Cap(String),
    Cancelled,
    Deadline,
}

#[derive(Clone, Copy)]
pub(super) struct DtFlattenProjectionCaps {
    pub max_predicate_arity: usize,
    pub max_total_predicate_arg_occurrences: usize,
    pub max_total_term_columns: usize,
    pub max_expansion_work: usize,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct DtFlattenProjectionStats {
    pub max_predicate_arity: usize,
    pub total_predicate_arg_occurrences: usize,
    pub total_term_columns: usize,
    pub expansion_work: usize,
    pub max_occurrence_width: usize,
    /// Constructor-driven rewrite work which scalar column width does not
    /// represent.  In particular, a multi-constructor enum with only nullary
    /// constructors has width one, but selector fallback/backtranslation still
    /// builds one tester/ITE link and one shallow subject clone for every
    /// non-zero constructor and scans the complete constructor table.
    pub constructor_rewrite_work: usize,
}

#[derive(Clone, Copy)]
pub(super) struct DtFlattenFanoutCaps {
    pub max_expr_clone_work: usize,
    pub max_generated_name_bytes: usize,
    /// Fixed punctuation/index bytes introduced per visited expression or sort
    /// component (`_vNN_`, `_disc`, `_unit`, tester prefixes, and separators).
    pub generated_name_overhead_per_node: usize,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct DtFlattenFanoutStats {
    pub expr_clone_work: usize,
    pub generated_name_bytes: usize,
}

fn check_boundary(
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Result<(), RouteAdmissionFailure> {
    if cancellation.is_cancelled() {
        Err(RouteAdmissionFailure::Cancelled)
    } else if Instant::now() >= deadline {
        Err(RouteAdmissionFailure::Deadline)
    } else {
        Ok(())
    }
}

fn cap_failure(label: &str, actual: usize, cap: usize) -> RouteAdmissionFailure {
    RouteAdmissionFailure::Cap(format!("{label} {actual} > cap {cap}"))
}

/// Admit a fixed number of full [`ChcProblem`] clones under an existing route
/// surface envelope.
///
/// Cloning repeats every owned vector, string, sort, and expression-root
/// allocation represented by [`RouteSurfaceCaps`]. The ordinary cooperative
/// scanner first enforces the existing per-item/depth limits. This function
/// then charges every aggregate surface by the exact fanout, making the same
/// route envelope a bound across all simultaneously owned clones without
/// adding a second heuristic limit.
pub(super) fn admit_problem_clone_fanout(
    problem: &ChcProblem,
    caps: RouteSurfaceCaps,
    clone_count: usize,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Result<RouteSurfaceStats, RouteAdmissionFailure> {
    if clone_count == 0 {
        return Err(RouteAdmissionFailure::Cap(
            "problem clone fanout must be nonzero".to_string(),
        ));
    }
    let stats = scan_problem_surface(problem, caps, cancellation, deadline)?;
    check_clone_fanout(
        "cloned clauses",
        problem.clauses().len(),
        clone_count,
        caps.max_clauses,
    )?;
    check_clone_fanout(
        "cloned predicates",
        problem.predicates().len(),
        clone_count,
        caps.max_predicates,
    )?;
    check_clone_fanout(
        "cloned action declarations",
        problem.action_names().len(),
        clone_count,
        caps.max_actions,
    )?;
    check_clone_fanout(
        "cloned datatype definitions",
        problem.datatype_defs().len(),
        clone_count,
        caps.max_datatype_defs,
    )?;
    check_clone_fanout(
        "cloned datatype constructors/selectors",
        stats.datatype_members,
        clone_count,
        caps.max_datatype_members,
    )?;
    check_clone_fanout(
        "cloned body predicate atoms",
        stats.total_body_atoms,
        clone_count,
        caps.max_total_body_atoms,
    )?;
    check_clone_fanout(
        "cloned expression nodes",
        stats.total_expr_nodes,
        clone_count,
        caps.max_total_expr_nodes,
    )?;
    check_clone_fanout(
        "cloned sort nodes",
        stats.total_sort_nodes,
        clone_count,
        caps.max_total_sort_nodes,
    )?;
    check_clone_fanout(
        "cloned array select/key occurrences",
        stats.array_selects,
        clone_count,
        caps.max_array_selects,
    )?;

    // `ChcProblem` owns each predicate name both in its declaration vector and
    // as a key in `predicate_names`; the surface scan charges the declaration
    // copy. Add exactly the second map-owned copy before applying the fanout.
    let predicate_map_name_bytes = problem.predicates().iter().try_fold(
        0usize,
        |total, predicate| -> Result<usize, RouteAdmissionFailure> {
            total.checked_add(predicate.name.len()).ok_or_else(|| {
                cap_failure(
                    "cloned surface name bytes",
                    usize::MAX,
                    caps.max_total_name_bytes,
                )
            })
        },
    )?;
    let cloned_name_bytes = stats
        .total_name_bytes
        .checked_add(predicate_map_name_bytes)
        .ok_or_else(|| {
            cap_failure(
                "cloned surface name bytes",
                usize::MAX,
                caps.max_total_name_bytes,
            )
        })?;
    check_clone_fanout(
        "cloned surface name bytes",
        cloned_name_bytes,
        clone_count,
        caps.max_total_name_bytes,
    )?;
    check_boundary(cancellation, deadline)?;
    Ok(stats)
}

fn check_clone_fanout(
    label: &str,
    per_clone: usize,
    clone_count: usize,
    cap: usize,
) -> Result<(), RouteAdmissionFailure> {
    let total = per_clone
        .checked_mul(clone_count)
        .ok_or_else(|| cap_failure(label, usize::MAX, cap))?;
    if total > cap {
        return Err(cap_failure(label, total, cap));
    }
    Ok(())
}

/// Work performed by `ChcExpr::clone` at one root, excluding descendants
/// retained behind `Arc`.  Tester construction clones its subject into a new
/// `Arc`; cloning an application also copies its direct child-Arc vector, so a
/// fixed one-unit charge would undercount wide opaque enum subjects.
fn shallow_expr_clone_work(expr: &ChcExpr, cap: usize) -> Result<usize, RouteAdmissionFailure> {
    let direct_entries = match expr {
        ChcExpr::Op(_, arguments)
        | ChcExpr::PredicateApp(_, _, arguments)
        | ChcExpr::FuncApp(_, _, arguments) => arguments.len(),
        ChcExpr::ConstArray(_, _) => 1,
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => 0,
    };
    1usize.checked_add(direct_entries).ok_or_else(|| {
        cap_failure(
            "projected datatype constructor subject clone work",
            usize::MAX,
            cap,
        )
    })
}

enum DtProjectionFrame<'a> {
    Visit {
        sort: &'a ChcSort,
        /// Cost of a shallow clone of the expression currently carrying this
        /// sort.  A generated selector application has one root and one direct
        /// Arc entry, independent of the size of its shared descendant.
        subject_clone_work: usize,
    },
    FinishDatatype {
        name: &'a str,
        single_constructor: bool,
        columns_before: usize,
    },
}

#[derive(Clone, Copy)]
struct FlattenedSortProjection {
    columns: usize,
    constructor_rewrite_work: usize,
}

struct DtProjectionMeter<'a> {
    caps: DtFlattenProjectionCaps,
    cancellation: &'a CancellationToken,
    deadline: Instant,
    expansion_work: usize,
}

impl DtProjectionMeter<'_> {
    fn charge_work(&mut self, amount: usize) -> Result<(), RouteAdmissionFailure> {
        self.expansion_work = self.expansion_work.checked_add(amount).ok_or_else(|| {
            cap_failure(
                "projected datatype flatten expansion work",
                usize::MAX,
                self.caps.max_expansion_work,
            )
        })?;
        if self.expansion_work > self.caps.max_expansion_work {
            return Err(cap_failure(
                "projected datatype flatten expansion work",
                self.expansion_work,
                self.caps.max_expansion_work,
            ));
        }
        if self.expansion_work & 0xff == 0 {
            check_boundary(self.cancellation, self.deadline)?;
        }
        Ok(())
    }

    /// Count the scalar columns produced by `DtFlattener::flatten_sort`
    /// without constructing them.
    ///
    /// The explicit enter/finish stack mirrors the transform's same-datatype
    /// recursion cutoff and its single-constructor unit fallback. Shared
    /// datatype metadata is deliberately NOT memoized: the transform expands
    /// every selector occurrence, so memoizing a compact binary datatype DAG
    /// here would undercount its exponential output.
    fn flattened_sort_width(
        &mut self,
        root: &ChcSort,
        column_cap: usize,
        root_subject_clone_work: usize,
    ) -> Result<FlattenedSortProjection, RouteAdmissionFailure> {
        let recursion_limit = crate::transform::dt_flatten_recursion_limit();
        let mut columns = 0usize;
        let mut constructor_rewrite_work = 0usize;
        let mut datatype_depths: HashMap<&str, usize> = HashMap::default();
        let mut stack = vec![DtProjectionFrame::Visit {
            sort: root,
            subject_clone_work: root_subject_clone_work,
        }];
        while let Some(frame) = stack.pop() {
            self.charge_work(1)?;
            match frame {
                DtProjectionFrame::Visit {
                    sort,
                    subject_clone_work,
                } => match sort {
                    ChcSort::Datatype { name, constructors } => {
                        let occurrence = datatype_depths.get(name.as_str()).copied().unwrap_or(0);
                        if occurrence >= recursion_limit {
                            continue;
                        }
                        datatype_depths.insert(name.as_str(), occurrence + 1);
                        // `flatten_dt_expr` scans the constructor table even
                        // when every constructor is nullary.  Opaque values and
                        // backtranslation additionally build one tester and one
                        // ITE node for every constructor after the first, and
                        // clone the current subject root into each tester. Count
                        // all three surfaces here; scalar-column width alone is
                        // one for such enums and would otherwise miss the fanout.
                        let table_work = constructors.len();
                        let tester_count = constructors.len().saturating_sub(1);
                        let tester_ite_work = tester_count.checked_mul(2).ok_or_else(|| {
                            cap_failure(
                                "projected datatype constructor rewrite work",
                                usize::MAX,
                                self.caps.max_expansion_work,
                            )
                        })?;
                        let subject_clone_work = tester_count
                            .checked_mul(subject_clone_work)
                            .ok_or_else(|| {
                                cap_failure(
                                    "projected datatype constructor rewrite work",
                                    usize::MAX,
                                    self.caps.max_expansion_work,
                                )
                            })?;
                        let occurrence_work = table_work
                            .checked_add(tester_ite_work)
                            .and_then(|work| work.checked_add(subject_clone_work))
                            .ok_or_else(|| {
                                cap_failure(
                                    "projected datatype constructor rewrite work",
                                    usize::MAX,
                                    self.caps.max_expansion_work,
                                )
                            })?;
                        constructor_rewrite_work = constructor_rewrite_work
                            .checked_add(occurrence_work)
                            .ok_or_else(|| {
                                cap_failure(
                                    "projected datatype constructor rewrite work",
                                    usize::MAX,
                                    self.caps.max_expansion_work,
                                )
                            })?;
                        self.charge_work(occurrence_work)?;
                        let single_constructor = constructors.len() == 1;
                        let columns_before = columns;
                        stack.push(DtProjectionFrame::FinishDatatype {
                            name,
                            single_constructor,
                            columns_before,
                        });
                        if single_constructor {
                            for selector in constructors[0].selectors.iter().rev() {
                                stack.push(DtProjectionFrame::Visit {
                                    sort: &selector.sort,
                                    subject_clone_work: 2,
                                });
                            }
                        } else {
                            Self::add_columns(&mut columns, 1, column_cap)?;
                            for selector in constructors
                                .iter()
                                .rev()
                                .flat_map(|constructor| constructor.selectors.iter().rev())
                            {
                                stack.push(DtProjectionFrame::Visit {
                                    sort: &selector.sort,
                                    subject_clone_work: 2,
                                });
                            }
                        }
                    }
                    ChcSort::Uninterpreted(name)
                        if datatype_depths.get(name.as_str()).copied().unwrap_or(0)
                            >= recursion_limit => {}
                    // DtFlattener treats arrays and all scalar/opaque sorts as
                    // one column; it does not flatten a datatype nested inside
                    // an array sort.
                    ChcSort::Array(_, _)
                    | ChcSort::Bool
                    | ChcSort::Int
                    | ChcSort::Real
                    | ChcSort::BitVec(_)
                    | ChcSort::Uninterpreted(_) => {
                        Self::add_columns(&mut columns, 1, column_cap)?;
                    }
                },
                DtProjectionFrame::FinishDatatype {
                    name,
                    single_constructor,
                    columns_before,
                } => {
                    if single_constructor && columns == columns_before {
                        // A unit constructor, or one whose every recursive
                        // child hit the cutoff, is represented by one Bool.
                        Self::add_columns(&mut columns, 1, column_cap)?;
                    }
                    let Some(depth) = datatype_depths.get_mut(name) else {
                        return Err(RouteAdmissionFailure::Cap(
                            "datatype projection stack lost its active definition".to_string(),
                        ));
                    };
                    *depth = depth.saturating_sub(1);
                    if *depth == 0 {
                        datatype_depths.remove(name);
                    }
                }
            }
        }
        check_boundary(self.cancellation, self.deadline)?;
        Ok(FlattenedSortProjection {
            columns,
            constructor_rewrite_work,
        })
    }

    fn add_columns(
        columns: &mut usize,
        amount: usize,
        cap: usize,
    ) -> Result<(), RouteAdmissionFailure> {
        *columns = columns
            .checked_add(amount)
            .ok_or_else(|| cap_failure("projected datatype flatten columns", usize::MAX, cap))?;
        if *columns > cap {
            return Err(cap_failure(
                "projected datatype flatten columns",
                *columns,
                cap,
            ));
        }
        Ok(())
    }

    fn predicate_arities(
        &mut self,
        problem: &ChcProblem,
        stats: &mut DtFlattenProjectionStats,
    ) -> Result<Vec<usize>, RouteAdmissionFailure> {
        let mut projected_arities = Vec::with_capacity(problem.predicates().len());
        for predicate in problem.predicates() {
            check_boundary(self.cancellation, self.deadline)?;
            let mut projected_arity = 0usize;
            for sort in &predicate.arg_sorts {
                let projection = if matches!(sort, ChcSort::Datatype { .. }) {
                    self.flattened_sort_width(sort, self.caps.max_predicate_arity, 1)?
                } else {
                    FlattenedSortProjection {
                        columns: 1,
                        constructor_rewrite_work: 0,
                    }
                };
                let width = projection.columns;
                stats.constructor_rewrite_work = stats
                    .constructor_rewrite_work
                    .checked_add(projection.constructor_rewrite_work)
                    .ok_or_else(|| {
                        cap_failure(
                            "projected datatype constructor rewrite work",
                            usize::MAX,
                            self.caps.max_expansion_work,
                        )
                    })?;
                stats.max_occurrence_width = stats.max_occurrence_width.max(width);
                projected_arity = projected_arity.checked_add(width).ok_or_else(|| {
                    cap_failure(
                        "projected datatype-flattened predicate arity",
                        usize::MAX,
                        self.caps.max_predicate_arity,
                    )
                })?;
                if projected_arity > self.caps.max_predicate_arity {
                    return Err(cap_failure(
                        "projected datatype-flattened predicate arity",
                        projected_arity,
                        self.caps.max_predicate_arity,
                    ));
                }
            }
            stats.max_predicate_arity = stats.max_predicate_arity.max(projected_arity);
            projected_arities.push(projected_arity);
        }
        Ok(projected_arities)
    }

    fn charge_predicate_occurrence(
        &self,
        predicate_index: usize,
        location: &str,
        projected_arities: &[usize],
        stats: &mut DtFlattenProjectionStats,
    ) -> Result<(), RouteAdmissionFailure> {
        let projected = projected_arities.get(predicate_index).ok_or_else(|| {
            RouteAdmissionFailure::Cap(format!(
                "{location} predicate {predicate_index} is outside the declaration table"
            ))
        })?;
        stats.total_predicate_arg_occurrences = stats
            .total_predicate_arg_occurrences
            .checked_add(*projected)
            .ok_or_else(|| {
                cap_failure(
                    "projected datatype-flattened predicate argument occurrences",
                    usize::MAX,
                    self.caps.max_total_predicate_arg_occurrences,
                )
            })?;
        if stats.total_predicate_arg_occurrences > self.caps.max_total_predicate_arg_occurrences {
            return Err(cap_failure(
                "projected datatype-flattened predicate argument occurrences",
                stats.total_predicate_arg_occurrences,
                self.caps.max_total_predicate_arg_occurrences,
            ));
        }
        Ok(())
    }

    /// Recover a borrowed datatype result sort without calling
    /// [`ChcExpr::sort`], which clones every traversed sort.
    ///
    /// `select` is the important case: an array-valued carrier may itself be a
    /// `select`, `store`, or `ite`, so follow the same sort-propagation rules as
    /// `ChcExpr::sort` while counting how many array value layers must be
    /// removed. Every step is charged to the projection work budget so hostile
    /// nested terms cannot turn this admission check into unbounded work.
    fn datatype_result_sort<'expr>(
        &mut self,
        root: &'expr ChcExpr,
    ) -> Result<Option<&'expr ChcSort>, RouteAdmissionFailure> {
        let mut current = root;
        let mut array_layers = 0usize;

        loop {
            self.charge_work(1)?;
            match current {
                ChcExpr::Var(variable) => {
                    return self.datatype_sort_after_array_layers(&variable.sort, array_layers);
                }
                ChcExpr::FuncApp(_, sort, _) => {
                    return self.datatype_sort_after_array_layers(sort, array_layers);
                }
                ChcExpr::ConstArray(_, value) if array_layers > 0 => {
                    array_layers -= 1;
                    current = value.as_ref();
                }
                ChcExpr::Op(ChcOp::Select, arguments) => {
                    let Some(array) = arguments.first() else {
                        return Ok(None);
                    };
                    array_layers = array_layers.checked_add(1).ok_or_else(|| {
                        cap_failure(
                            "projected datatype result-sort array depth",
                            usize::MAX,
                            self.caps.max_expansion_work,
                        )
                    })?;
                    current = array.as_ref();
                }
                ChcExpr::Op(ChcOp::Ite, arguments) => {
                    let Some(then_branch) = arguments.get(1) else {
                        return Ok(None);
                    };
                    current = then_branch.as_ref();
                }
                // These operations inherit their result sort from the first
                // argument (or use it as the malformed-input fallback) in
                // `ChcExpr::sort`. Following it is conservative for malformed
                // terms and exact for well-sorted terms.
                ChcExpr::Op(
                    ChcOp::Add
                    | ChcOp::Sub
                    | ChcOp::Mul
                    | ChcOp::Div
                    | ChcOp::Mod
                    | ChcOp::Neg
                    | ChcOp::Store
                    | ChcOp::BvAdd
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
                    | ChcOp::BvConcat
                    | ChcOp::BvZeroExtend(_)
                    | ChcOp::BvSignExtend(_)
                    | ChcOp::BvRotateLeft(_)
                    | ChcOp::BvRotateRight(_)
                    | ChcOp::BvRepeat(_),
                    arguments,
                ) => {
                    let Some(first) = arguments.first() else {
                        return Ok(None);
                    };
                    current = first.as_ref();
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::PredicateApp(_, _, _)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_)
                | ChcExpr::ConstArray(_, _)
                | ChcExpr::Op(
                    ChcOp::Not
                    | ChcOp::And
                    | ChcOp::Or
                    | ChcOp::Implies
                    | ChcOp::Iff
                    | ChcOp::Eq
                    | ChcOp::Ne
                    | ChcOp::Lt
                    | ChcOp::Le
                    | ChcOp::Gt
                    | ChcOp::Ge
                    | ChcOp::BvULt
                    | ChcOp::BvULe
                    | ChcOp::BvUGt
                    | ChcOp::BvUGe
                    | ChcOp::BvSLt
                    | ChcOp::BvSLe
                    | ChcOp::BvSGt
                    | ChcOp::BvSGe
                    | ChcOp::BvComp
                    | ChcOp::Bv2Nat
                    | ChcOp::BvExtract(_, _)
                    | ChcOp::Int2Bv(_),
                    _,
                ) => return Ok(None),
            }
        }
    }

    fn datatype_sort_after_array_layers<'sort>(
        &mut self,
        mut sort: &'sort ChcSort,
        mut array_layers: usize,
    ) -> Result<Option<&'sort ChcSort>, RouteAdmissionFailure> {
        while array_layers > 0 {
            self.charge_work(1)?;
            let ChcSort::Array(_, value_sort) = sort else {
                return Ok(None);
            };
            sort = value_sort.as_ref();
            array_layers -= 1;
        }
        Ok(matches!(sort, ChcSort::Datatype { .. }).then_some(sort))
    }

    fn charge_expression_projection(
        &mut self,
        root: &ChcExpr,
        stats: &mut DtFlattenProjectionStats,
    ) -> Result<(), RouteAdmissionFailure> {
        let mut expression_stack = vec![root];
        while let Some(expr) = expression_stack.pop() {
            self.charge_work(1)?;
            match expr {
                ChcExpr::FuncApp(_, _, arguments) => {
                    expression_stack.extend(arguments.iter().map(AsRef::as_ref));
                }
                ChcExpr::Op(_, arguments) | ChcExpr::PredicateApp(_, _, arguments) => {
                    expression_stack.extend(arguments.iter().map(AsRef::as_ref));
                }
                ChcExpr::ConstArray(_, value) => {
                    expression_stack.push(value.as_ref());
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
            let projected_sort = self.datatype_result_sort(expr)?;
            if let Some(sort) = projected_sort {
                let remaining = self
                    .caps
                    .max_total_term_columns
                    .saturating_sub(stats.total_term_columns);
                let projection = self.flattened_sort_width(
                    sort,
                    remaining,
                    shallow_expr_clone_work(expr, self.caps.max_expansion_work)?,
                )?;
                let width = projection.columns;
                stats.max_occurrence_width = stats.max_occurrence_width.max(width);
                stats.constructor_rewrite_work = stats
                    .constructor_rewrite_work
                    .checked_add(projection.constructor_rewrite_work)
                    .ok_or_else(|| {
                        cap_failure(
                            "projected datatype constructor rewrite work",
                            usize::MAX,
                            self.caps.max_expansion_work,
                        )
                    })?;
                stats.total_term_columns =
                    stats.total_term_columns.checked_add(width).ok_or_else(|| {
                        cap_failure(
                            "projected datatype-flattened term columns",
                            usize::MAX,
                            self.caps.max_total_term_columns,
                        )
                    })?;
            }
        }
        Ok(())
    }

    fn charge_clause_projection(
        &mut self,
        clause: &crate::HornClause,
        projected_arities: &[usize],
        stats: &mut DtFlattenProjectionStats,
    ) -> Result<(), RouteAdmissionFailure> {
        check_boundary(self.cancellation, self.deadline)?;
        for (predicate, _) in &clause.body.predicates {
            self.charge_predicate_occurrence(predicate.index(), "body", projected_arities, stats)?;
        }
        if let ClauseHead::Predicate(predicate, _) = &clause.head {
            self.charge_predicate_occurrence(predicate.index(), "head", projected_arities, stats)?;
        }
        for root in clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, arguments)| arguments.iter())
            .chain(clause.body.constraint.iter())
            .chain(match &clause.head {
                ClauseHead::Predicate(_, arguments) => arguments.as_slice(),
                ClauseHead::False => &[],
            })
        {
            self.charge_expression_projection(root, stats)?;
        }
        Ok(())
    }

    fn charge_datatype_definitions(
        &mut self,
        problem: &ChcProblem,
    ) -> Result<(), RouteAdmissionFailure> {
        for constructors in problem.datatype_defs().values() {
            self.charge_work(constructors.len())?;
            for (_, selectors) in constructors {
                self.charge_work(selectors.len())?;
                for (_, sort) in selectors {
                    let _ = self.flattened_sort_width(sort, self.caps.max_expansion_work, 0)?;
                }
            }
        }
        Ok(())
    }
}

fn charge_name_bytes(
    stats: &mut RouteSurfaceStats,
    caps: RouteSurfaceCaps,
    bytes: usize,
) -> Result<(), RouteAdmissionFailure> {
    stats.total_name_bytes = stats.total_name_bytes.checked_add(bytes).ok_or_else(|| {
        cap_failure(
            "total surface name bytes",
            usize::MAX,
            caps.max_total_name_bytes,
        )
    })?;
    if stats.total_name_bytes > caps.max_total_name_bytes {
        return Err(cap_failure(
            "total surface name bytes",
            stats.total_name_bytes,
            caps.max_total_name_bytes,
        ));
    }
    Ok(())
}

fn charge_datatype_metadata_name_bytes(
    stats: &mut RouteSurfaceStats,
    caps: RouteSurfaceCaps,
    bytes: usize,
) -> Result<(), RouteAdmissionFailure> {
    charge_name_bytes(stats, caps, bytes)?;
    stats.datatype_metadata_name_bytes = stats
        .datatype_metadata_name_bytes
        .checked_add(bytes)
        .ok_or_else(|| {
            cap_failure(
                "datatype metadata name bytes",
                usize::MAX,
                caps.max_total_name_bytes,
            )
        })?;
    Ok(())
}

/// Iteratively scans every sort reachable from the admitted surface.
///
/// `ChcSort::Array` owns its children through `Box`, so cloning a typed problem
/// recursively clones that shape. Datatype selector metadata is `Arc`-shared,
/// but transforms recursively inspect it. Keep both shapes below fixed depth
/// and work caps before either deterministic route clones the problem.
struct SortSurface<'a> {
    caps: RouteSurfaceCaps,
    cancellation: &'a CancellationToken,
    deadline: Instant,
    /// Highest entry depth at which shared datatype metadata was expanded.
    /// Re-expanding at an equal or shallower depth cannot expose a deeper
    /// descendant; a deeper occurrence is scanned again so the depth cap
    /// remains exact.
    expanded_datatypes: HashMap<usize, usize>,
}

impl SortSurface<'_> {
    fn scan_sort(
        &mut self,
        sort: &ChcSort,
        stats: &mut RouteSurfaceStats,
        label: &str,
    ) -> Result<(), RouteAdmissionFailure> {
        let mut stack = vec![(sort, 1usize)];
        while let Some((current, depth)) = stack.pop() {
            if stats.total_sort_nodes & 0xff == 0 {
                check_boundary(self.cancellation, self.deadline)?;
            }
            if depth > self.caps.max_sort_depth {
                return Err(cap_failure(
                    &format!("{label} sort depth"),
                    depth,
                    self.caps.max_sort_depth,
                ));
            }
            stats.total_sort_nodes = stats.total_sort_nodes.checked_add(1).ok_or_else(|| {
                cap_failure(
                    "total sort nodes",
                    usize::MAX,
                    self.caps.max_total_sort_nodes,
                )
            })?;
            if stats.total_sort_nodes > self.caps.max_total_sort_nodes {
                return Err(cap_failure(
                    "total sort nodes",
                    stats.total_sort_nodes,
                    self.caps.max_total_sort_nodes,
                ));
            }

            match current {
                ChcSort::Array(key, value) => {
                    self.push_sort_child(value, depth, &mut stack, label)?;
                    self.push_sort_child(key, depth, &mut stack, label)?;
                }
                ChcSort::Datatype { name, constructors } => {
                    stats.datatype_sort_occurrences = stats
                        .datatype_sort_occurrences
                        .checked_add(1)
                        .ok_or_else(|| {
                            cap_failure(
                                "datatype sort occurrences",
                                usize::MAX,
                                self.caps.max_total_sort_nodes,
                            )
                        })?;
                    charge_name_bytes(stats, self.caps, name.len())?;
                    let metadata_id = std::sync::Arc::as_ptr(constructors) as usize;
                    if self
                        .expanded_datatypes
                        .get(&metadata_id)
                        .is_some_and(|seen_depth| *seen_depth >= depth)
                    {
                        continue;
                    }
                    self.expanded_datatypes.insert(metadata_id, depth);
                    self.add_datatype_members(constructors.len(), stats)?;
                    for constructor in constructors.iter().rev() {
                        check_boundary(self.cancellation, self.deadline)?;
                        charge_datatype_metadata_name_bytes(
                            stats,
                            self.caps,
                            constructor.name.len(),
                        )?;
                        self.add_datatype_members(constructor.selectors.len(), stats)?;
                        for (selector_index, selector) in
                            constructor.selectors.iter().rev().enumerate()
                        {
                            if selector_index & 0xff == 0 {
                                check_boundary(self.cancellation, self.deadline)?;
                            }
                            charge_datatype_metadata_name_bytes(
                                stats,
                                self.caps,
                                selector.name.len(),
                            )?;
                            self.push_sort_child(&selector.sort, depth, &mut stack, label)?;
                        }
                    }
                }
                ChcSort::Uninterpreted(name) => {
                    charge_name_bytes(stats, self.caps, name.len())?;
                }
                ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
            }
        }
        Ok(())
    }

    fn push_sort_child<'a>(
        &self,
        child: &'a ChcSort,
        parent_depth: usize,
        stack: &mut Vec<(&'a ChcSort, usize)>,
        label: &str,
    ) -> Result<(), RouteAdmissionFailure> {
        let child_depth = parent_depth
            .checked_add(1)
            .ok_or_else(|| cap_failure("sort depth", usize::MAX, self.caps.max_sort_depth))?;
        // Check before scheduling the child: a hostile deeply nested typed
        // sort never grows the explicit work stack beyond the admitted depth.
        if child_depth > self.caps.max_sort_depth {
            return Err(cap_failure(
                &format!("{label} sort depth"),
                child_depth,
                self.caps.max_sort_depth,
            ));
        }
        stack.push((child, child_depth));
        Ok(())
    }

    fn add_datatype_members(
        &self,
        count: usize,
        stats: &mut RouteSurfaceStats,
    ) -> Result<(), RouteAdmissionFailure> {
        stats.datatype_members = stats.datatype_members.checked_add(count).ok_or_else(|| {
            cap_failure(
                "datatype constructors/selectors",
                usize::MAX,
                self.caps.max_datatype_members,
            )
        })?;
        if stats.datatype_members > self.caps.max_datatype_members {
            return Err(cap_failure(
                "datatype constructors/selectors",
                stats.datatype_members,
                self.caps.max_datatype_members,
            ));
        }
        Ok(())
    }
}

struct ClauseSurface<'a> {
    caps: RouteSurfaceCaps,
    cancellation: &'a CancellationToken,
    deadline: Instant,
    clause_index: usize,
    clause_nodes: usize,
    variable_occurrences: usize,
}

impl ClauseSurface<'_> {
    fn scan_expr(
        &mut self,
        expr: &ChcExpr,
        stats: &mut RouteSurfaceStats,
        sort_surface: &mut SortSurface<'_>,
    ) -> Result<(), RouteAdmissionFailure> {
        let mut stack = vec![(expr, 1usize)];
        while let Some((current, depth)) = stack.pop() {
            if self.clause_nodes & 0xff == 0 {
                check_boundary(self.cancellation, self.deadline)?;
            }
            if depth > self.caps.max_expr_depth {
                return Err(cap_failure(
                    &format!("clause {} expression depth", self.clause_index),
                    depth,
                    self.caps.max_expr_depth,
                ));
            }
            self.clause_nodes = self.clause_nodes.checked_add(1).ok_or_else(|| {
                cap_failure(
                    "per-clause expression nodes",
                    usize::MAX,
                    self.caps.max_expr_nodes_per_clause,
                )
            })?;
            if self.clause_nodes > self.caps.max_expr_nodes_per_clause {
                return Err(cap_failure(
                    &format!("clause {} expression nodes", self.clause_index),
                    self.clause_nodes,
                    self.caps.max_expr_nodes_per_clause,
                ));
            }
            stats.total_expr_nodes = stats.total_expr_nodes.checked_add(1).ok_or_else(|| {
                cap_failure(
                    "total expression nodes",
                    usize::MAX,
                    self.caps.max_total_expr_nodes,
                )
            })?;
            if stats.total_expr_nodes > self.caps.max_total_expr_nodes {
                return Err(cap_failure(
                    "total expression nodes",
                    stats.total_expr_nodes,
                    self.caps.max_total_expr_nodes,
                ));
            }

            match current {
                ChcExpr::Var(var) => {
                    charge_name_bytes(stats, self.caps, var.name.len())?;
                    self.variable_occurrences =
                        self.variable_occurrences.checked_add(1).ok_or_else(|| {
                            cap_failure(
                                "per-clause variable occurrences",
                                usize::MAX,
                                self.caps.max_variable_occurrences_per_clause,
                            )
                        })?;
                    if self.variable_occurrences > self.caps.max_variable_occurrences_per_clause {
                        return Err(cap_failure(
                            &format!("clause {} variable occurrences", self.clause_index),
                            self.variable_occurrences,
                            self.caps.max_variable_occurrences_per_clause,
                        ));
                    }
                    sort_surface.scan_sort(&var.sort, stats, "clause variable")?;
                }
                ChcExpr::Op(op, args) => {
                    if matches!(op, ChcOp::Select) {
                        stats.array_selects =
                            stats.array_selects.checked_add(1).ok_or_else(|| {
                                cap_failure(
                                    "array select/key occurrences",
                                    usize::MAX,
                                    self.caps.max_array_selects,
                                )
                            })?;
                        if stats.array_selects > self.caps.max_array_selects {
                            return Err(cap_failure(
                                "array select/key occurrences",
                                stats.array_selects,
                                self.caps.max_array_selects,
                            ));
                        }
                    }
                    self.push_children(
                        args.iter().map(|arg| arg.as_ref()),
                        depth,
                        &mut stack,
                        stats,
                    )?;
                }
                ChcExpr::PredicateApp(name, _, args) => {
                    charge_name_bytes(stats, self.caps, name.len())?;
                    self.push_children(
                        args.iter().map(|arg| arg.as_ref()),
                        depth,
                        &mut stack,
                        stats,
                    )?;
                }
                ChcExpr::FuncApp(name, return_sort, args) => {
                    charge_name_bytes(stats, self.caps, name.len())?;
                    sort_surface.scan_sort(return_sort, stats, "clause function return")?;
                    self.push_children(
                        args.iter().map(|arg| arg.as_ref()),
                        depth,
                        &mut stack,
                        stats,
                    )?;
                }
                ChcExpr::ConstArray(key_sort, value) => {
                    sort_surface.scan_sort(key_sort, stats, "clause constant-array key")?;
                    self.push_children(std::iter::once(value.as_ref()), depth, &mut stack, stats)?;
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _) => {}
                ChcExpr::IsTesterMarker(name) => {
                    charge_name_bytes(stats, self.caps, name.len())?;
                }
                ChcExpr::ConstArrayMarker(key_sort) => {
                    sort_surface.scan_sort(key_sort, stats, "clause constant-array marker")?;
                }
            }
        }
        Ok(())
    }

    fn push_children<'a>(
        &self,
        children: impl Iterator<Item = &'a ChcExpr>,
        parent_depth: usize,
        stack: &mut Vec<(&'a ChcExpr, usize)>,
        stats: &RouteSurfaceStats,
    ) -> Result<(), RouteAdmissionFailure> {
        for child in children {
            if stack.len() & 0xff == 0 {
                check_boundary(self.cancellation, self.deadline)?;
            }
            let child_depth = parent_depth.checked_add(1).ok_or_else(|| {
                cap_failure("expression depth", usize::MAX, self.caps.max_expr_depth)
            })?;
            if child_depth > self.caps.max_expr_depth {
                return Err(cap_failure(
                    &format!("clause {} expression depth", self.clause_index),
                    child_depth,
                    self.caps.max_expr_depth,
                ));
            }
            let pending = stack.len().checked_add(1).ok_or_else(|| {
                cap_failure(
                    "pending expression nodes",
                    usize::MAX,
                    self.caps.max_expr_nodes_per_clause,
                )
            })?;
            if self
                .clause_nodes
                .checked_add(pending)
                .is_none_or(|nodes| nodes > self.caps.max_expr_nodes_per_clause)
            {
                return Err(cap_failure(
                    &format!("clause {} expression nodes", self.clause_index),
                    self.caps.max_expr_nodes_per_clause.saturating_add(1),
                    self.caps.max_expr_nodes_per_clause,
                ));
            }
            if stats
                .total_expr_nodes
                .checked_add(pending)
                .is_none_or(|nodes| nodes > self.caps.max_total_expr_nodes)
            {
                return Err(cap_failure(
                    "total expression nodes",
                    self.caps.max_total_expr_nodes.saturating_add(1),
                    self.caps.max_total_expr_nodes,
                ));
            }
            stack.push((child, child_depth));
        }
        Ok(())
    }
}

pub(super) fn scan_problem_surface(
    problem: &ChcProblem,
    caps: RouteSurfaceCaps,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Result<RouteSurfaceStats, RouteAdmissionFailure> {
    let mut stats = RouteSurfaceStats::default();
    let mut sort_surface = SortSurface {
        caps,
        cancellation,
        deadline,
        expanded_datatypes: HashMap::default(),
    };
    scan_predicate_surface_into(
        problem,
        caps,
        cancellation,
        deadline,
        &mut sort_surface,
        &mut stats,
    )?;
    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        check_boundary(cancellation, deadline)?;
        let clause_body_atoms = clause.body.predicates.len();
        if clause_body_atoms > caps.max_body_atoms_per_clause {
            return Err(cap_failure(
                &format!("clause {clause_index} body predicate atoms"),
                clause_body_atoms,
                caps.max_body_atoms_per_clause,
            ));
        }
        stats.total_body_atoms = stats
            .total_body_atoms
            .checked_add(clause_body_atoms)
            .ok_or_else(|| {
                cap_failure(
                    "total body predicate atoms",
                    usize::MAX,
                    caps.max_total_body_atoms,
                )
            })?;
        if stats.total_body_atoms > caps.max_total_body_atoms {
            return Err(cap_failure(
                "total body predicate atoms",
                stats.total_body_atoms,
                caps.max_total_body_atoms,
            ));
        }

        let mut surface = ClauseSurface {
            caps,
            cancellation,
            deadline,
            clause_index,
            clause_nodes: 0,
            variable_occurrences: 0,
        };
        for (_, args) in &clause.body.predicates {
            for arg in args {
                surface.scan_expr(arg, &mut stats, &mut sort_surface)?;
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            surface.scan_expr(constraint, &mut stats, &mut sort_surface)?;
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                surface.scan_expr(arg, &mut stats, &mut sort_surface)?;
            }
        }
    }
    stats.projected_const_key_rewrite_visits = stats
        .total_expr_nodes
        .checked_mul(stats.array_selects)
        .ok_or_else(|| {
            cap_failure(
                "projected const-key scalarization node/key visits",
                usize::MAX,
                caps.max_const_key_rewrite_visits,
            )
        })?;
    if stats.projected_const_key_rewrite_visits > caps.max_const_key_rewrite_visits {
        return Err(cap_failure(
            "projected const-key scalarization node/key visits",
            stats.projected_const_key_rewrite_visits,
            caps.max_const_key_rewrite_visits,
        ));
    }
    check_boundary(cancellation, deadline)?;
    Ok(stats)
}

/// Bound the work and output that datatype flattening would perform on a
/// surface which already passed [`scan_problem_surface`].
///
/// In particular, an `Arc`-shared datatype DAG can be linear in its stored
/// metadata while expanding to exponentially many scalar columns. The surface
/// scanner deduplicates that metadata for input accounting; this projection
/// intentionally follows every selector occurrence, exactly where the
/// synchronous flattener would duplicate it.
pub(super) fn admit_dt_flatten_projection(
    problem: &ChcProblem,
    caps: DtFlattenProjectionCaps,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Result<DtFlattenProjectionStats, RouteAdmissionFailure> {
    check_boundary(cancellation, deadline)?;
    let mut meter = DtProjectionMeter {
        caps,
        cancellation,
        deadline,
        expansion_work: 0,
    };
    let mut stats = DtFlattenProjectionStats::default();
    let projected_arities = meter.predicate_arities(problem, &mut stats)?;
    for clause in problem.clauses() {
        meter.charge_clause_projection(clause, &projected_arities, &mut stats)?;
    }

    // `DtFlattener` performs a recursive truncation pre-scan over every
    // declared definition, including unused prelude declarations. Walking
    // each selector from an empty datatype path can unfold one occurrence more
    // than the transform's virtual root and is therefore a safe overestimate.
    meter.charge_datatype_definitions(problem)?;

    check_boundary(cancellation, deadline)?;
    stats.expansion_work = meter.expansion_work;
    Ok(stats)
}

/// Bound allocation fanout that column counts alone do not capture.
///
/// `DtFlattener` clones an ITE condition and selector/tester subject once per
/// flattened column, and constructs one concatenated component name per
/// column. Multiplying the already-admitted input surfaces by the maximum
/// exact occurrence width is conservative for both operations. Structural
/// punctuation introduced by the transform is charged per admitted expression
/// and sort node before applying the same width multiplier. Shared datatype
/// metadata names are additionally crossed with every datatype sort occurrence:
/// the input stores those names once behind `Arc`, while the transform embeds
/// them into fresh clause-local component/tester names for every occurrence.
/// Constructor-table scans, tester/ITE nodes, and the shallow subject clones
/// stored below those testers are metered separately by the projection pass;
/// this avoids hiding a wide nullary enum behind scalar width one.
pub(super) fn admit_dt_flatten_fanout(
    surface: &RouteSurfaceStats,
    projection: &DtFlattenProjectionStats,
    caps: DtFlattenFanoutCaps,
) -> Result<DtFlattenFanoutStats, RouteAdmissionFailure> {
    let width = projection.max_occurrence_width.max(1);
    let expr_clone_work = surface
        .total_expr_nodes
        .checked_mul(width)
        .and_then(|work| work.checked_add(projection.constructor_rewrite_work))
        .ok_or_else(|| {
            cap_failure(
                "projected datatype-flatten expression clone work",
                usize::MAX,
                caps.max_expr_clone_work,
            )
        })?;
    if expr_clone_work > caps.max_expr_clone_work {
        return Err(cap_failure(
            "projected datatype-flatten expression clone work",
            expr_clone_work,
            caps.max_expr_clone_work,
        ));
    }

    let metadata_name_replay_bytes = surface
        .datatype_metadata_name_bytes
        .checked_mul(surface.datatype_sort_occurrences)
        .ok_or_else(|| {
            cap_failure(
                "projected datatype-flatten generated name bytes",
                usize::MAX,
                caps.max_generated_name_bytes,
            )
        })?;
    let structural_nodes = surface
        .total_expr_nodes
        .checked_add(surface.total_sort_nodes)
        .ok_or_else(|| {
            cap_failure(
                "projected datatype-flatten generated name bytes",
                usize::MAX,
                caps.max_generated_name_bytes,
            )
        })?;
    let structural_name_bytes = structural_nodes
        .checked_mul(caps.generated_name_overhead_per_node)
        .ok_or_else(|| {
            cap_failure(
                "projected datatype-flatten generated name bytes",
                usize::MAX,
                caps.max_generated_name_bytes,
            )
        })?;
    let name_basis = surface
        .total_name_bytes
        .checked_add(metadata_name_replay_bytes)
        .and_then(|bytes| bytes.checked_add(structural_name_bytes))
        .ok_or_else(|| {
            cap_failure(
                "projected datatype-flatten generated name bytes",
                usize::MAX,
                caps.max_generated_name_bytes,
            )
        })?;
    let generated_name_bytes = name_basis.checked_mul(width).ok_or_else(|| {
        cap_failure(
            "projected datatype-flatten generated name bytes",
            usize::MAX,
            caps.max_generated_name_bytes,
        )
    })?;
    if generated_name_bytes > caps.max_generated_name_bytes {
        return Err(cap_failure(
            "projected datatype-flatten generated name bytes",
            generated_name_bytes,
            caps.max_generated_name_bytes,
        ));
    }

    Ok(DtFlattenFanoutStats {
        expr_clone_work,
        generated_name_bytes,
    })
}

pub(super) fn scan_predicate_surface(
    problem: &ChcProblem,
    caps: RouteSurfaceCaps,
    cancellation: &CancellationToken,
    deadline: Instant,
) -> Result<(), RouteAdmissionFailure> {
    let mut stats = RouteSurfaceStats::default();
    let mut sort_surface = SortSurface {
        caps,
        cancellation,
        deadline,
        expanded_datatypes: HashMap::default(),
    };
    scan_predicate_surface_into(
        problem,
        caps,
        cancellation,
        deadline,
        &mut sort_surface,
        &mut stats,
    )
}

fn scan_predicate_surface_into(
    problem: &ChcProblem,
    caps: RouteSurfaceCaps,
    cancellation: &CancellationToken,
    deadline: Instant,
    sort_surface: &mut SortSurface<'_>,
    stats: &mut RouteSurfaceStats,
) -> Result<(), RouteAdmissionFailure> {
    check_boundary(cancellation, deadline)?;
    if problem.clauses().len() > caps.max_clauses {
        return Err(cap_failure(
            "clauses",
            problem.clauses().len(),
            caps.max_clauses,
        ));
    }
    if problem.predicates().len() > caps.max_predicates {
        return Err(cap_failure(
            "predicates",
            problem.predicates().len(),
            caps.max_predicates,
        ));
    }
    if problem.action_names().len() > caps.max_actions {
        return Err(cap_failure(
            "action declarations",
            problem.action_names().len(),
            caps.max_actions,
        ));
    }
    if problem.datatype_defs().len() > caps.max_datatype_defs {
        return Err(cap_failure(
            "datatype definitions",
            problem.datatype_defs().len(),
            caps.max_datatype_defs,
        ));
    }
    let mut max_arity = 0usize;
    for predicate in problem.predicates() {
        check_boundary(cancellation, deadline)?;
        charge_name_bytes(stats, caps, predicate.name.len())?;
        max_arity = max_arity.max(predicate.arity());
        if max_arity > caps.max_predicate_arity {
            return Err(cap_failure(
                "max_predicate_arity",
                max_arity,
                caps.max_predicate_arity,
            ));
        }
        for sort in &predicate.arg_sorts {
            sort_surface.scan_sort(sort, stats, "predicate argument")?;
        }
    }
    for action_name in problem.action_names() {
        check_boundary(cancellation, deadline)?;
        charge_name_bytes(stats, caps, action_name.len())?;
    }
    for (datatype_name, constructors) in problem.datatype_defs() {
        check_boundary(cancellation, deadline)?;
        charge_name_bytes(stats, caps, datatype_name.len())?;
        sort_surface.add_datatype_members(constructors.len(), stats)?;
        for (constructor_name, selectors) in constructors {
            check_boundary(cancellation, deadline)?;
            charge_datatype_metadata_name_bytes(stats, caps, constructor_name.len())?;
            sort_surface.add_datatype_members(selectors.len(), stats)?;
            for (selector_name, sort) in selectors {
                charge_datatype_metadata_name_bytes(stats, caps, selector_name.len())?;
                sort_surface.scan_sort(sort, stats, "datatype selector")?;
            }
        }
    }
    check_boundary(cancellation, deadline)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcDtConstructor, ChcDtSelector, ChcVar, ClauseBody, HornClause};
    use std::sync::Arc;
    use std::time::Duration;

    fn caps() -> RouteSurfaceCaps {
        RouteSurfaceCaps {
            max_clauses: 8,
            max_predicates: 8,
            max_predicate_arity: 8,
            max_actions: 8,
            max_datatype_defs: 8,
            max_datatype_members: 32,
            max_body_atoms_per_clause: 2,
            max_total_body_atoms: 4,
            max_expr_nodes_per_clause: 64,
            max_total_expr_nodes: 128,
            max_expr_depth: 8,
            max_total_sort_nodes: 128,
            max_sort_depth: 8,
            max_variable_occurrences_per_clause: 32,
            max_array_selects: 1,
            max_const_key_rewrite_visits: 128,
            max_total_name_bytes: 128,
        }
    }

    fn repeated_body_problem(body_atoms: usize) -> ChcProblem {
        let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![array_sort.clone()]);
        let array = ChcVar::new("a", array_sort);
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(
                (0..body_atoms)
                    .map(|_| (predicate, vec![ChcExpr::var(array.clone())]))
                    .collect(),
            ),
            ClauseHead::False,
        ));
        problem
    }

    fn compact_binary_datatype(depth: usize) -> ChcSort {
        let mut child = ChcSort::Int;
        for level in 1..=depth {
            child = ChcSort::Datatype {
                name: format!("BinaryDt{level}"),
                constructors: Arc::new(vec![ChcDtConstructor {
                    name: format!("mk-BinaryDt{level}"),
                    selectors: vec![
                        ChcDtSelector {
                            name: "left".to_string(),
                            sort: child.clone(),
                        },
                        ChcDtSelector {
                            name: "right".to_string(),
                            sort: child.clone(),
                        },
                    ],
                }]),
            };
        }
        child
    }

    fn nullary_enum(constructor_count: usize) -> ChcSort {
        ChcSort::Datatype {
            name: "NullaryEnum".to_string(),
            constructors: Arc::new(
                (0..constructor_count)
                    .map(|index| ChcDtConstructor {
                        name: format!("Nullary{index}"),
                        selectors: Vec::new(),
                    })
                    .collect(),
            ),
        }
    }

    fn projection_caps(max_arity: usize, max_work: usize) -> DtFlattenProjectionCaps {
        DtFlattenProjectionCaps {
            max_predicate_arity: max_arity,
            max_total_predicate_arg_occurrences: 128,
            max_total_term_columns: 128,
            max_expansion_work: max_work,
        }
    }

    fn nested_array_datatype_read(
        datatype: &ChcSort,
        stem: &str,
        store_key: i128,
        outer_key: i128,
        inner_key: i128,
    ) -> ChcExpr {
        let inner_array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(datatype.clone()));
        let outer_array_sort =
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(inner_array_sort.clone()));
        let guarded_array = ChcExpr::ite(
            ChcExpr::var(ChcVar::new(format!("{stem}_guard"), ChcSort::Bool)),
            ChcExpr::var(ChcVar::new(
                format!("{stem}_then"),
                outer_array_sort.clone(),
            )),
            ChcExpr::var(ChcVar::new(format!("{stem}_else"), outer_array_sort)),
        );
        let stored_array = ChcExpr::store(
            guarded_array,
            ChcExpr::int(store_key),
            ChcExpr::var(ChcVar::new(format!("{stem}_replacement"), inner_array_sort)),
        );
        ChcExpr::select(
            ChcExpr::select(stored_array, ChcExpr::int(outer_key)),
            ChcExpr::int(inner_key),
        )
    }

    fn fanout_caps(
        max_expr_clone_work: usize,
        max_generated_name_bytes: usize,
        generated_name_overhead_per_node: usize,
    ) -> DtFlattenFanoutCaps {
        DtFlattenFanoutCaps {
            max_expr_clone_work,
            max_generated_name_bytes,
            generated_name_overhead_per_node,
        }
    }

    #[test]
    fn compact_datatype_dag_projection_accepts_boundary_and_rejects_exponential_plus_one() {
        let mut exact = ChcProblem::new();
        exact.declare_predicate("P", vec![compact_binary_datatype(3)]);
        let stats = admit_dt_flatten_projection(
            &exact,
            projection_caps(8, 1_000),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("three shared binary levels flatten to exactly eight columns");
        assert_eq!(stats.max_predicate_arity, 8);
        assert_eq!(stats.max_occurrence_width, 8);

        let mut too_wide = ChcProblem::new();
        too_wide.declare_predicate("P", vec![compact_binary_datatype(4)]);
        let failure = admit_dt_flatten_projection(
            &too_wide,
            projection_caps(8, 1_000),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("four compact binary levels expand to sixteen columns and must be rejected");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("projected datatype flatten columns 9 > cap 8")
        ));
    }

    #[test]
    fn datatype_projection_charges_select_results_at_exact_term_boundary() {
        let datatype = compact_binary_datatype(3);
        let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(datatype.clone()));
        let array = ChcVar::new("array", array_sort.clone());
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![array_sort]);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::int(0)),
                ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::int(1)),
            )),
            ClauseHead::Predicate(predicate, vec![ChcExpr::var(array)]),
        ));

        let mut exact_caps = projection_caps(8, 10_000);
        exact_caps.max_total_term_columns = 16;
        let stats = admit_dt_flatten_projection(
            &problem,
            exact_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("two eight-column select results exactly at the term cap must be admitted");
        assert_eq!(stats.total_term_columns, 16);
        assert_eq!(stats.max_occurrence_width, 8);

        let mut below_caps = exact_caps;
        below_caps.max_total_term_columns = 15;
        let failure = admit_dt_flatten_projection(
            &problem,
            below_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("the second derived select result must fail one column past the cap");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("projected datatype flatten columns 8 > cap 7")
        ));
    }

    #[test]
    fn datatype_projection_rejects_repeated_nested_select_store_ite_amplification() {
        let datatype = compact_binary_datatype(4);
        let inner_array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(datatype.clone()));
        let outer_array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(inner_array_sort));
        let head_array = ChcVar::new("head_array", outer_array_sort.clone());
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![outer_array_sort]);
        let equalities = (0..4)
            .map(|index| {
                ChcExpr::eq(
                    nested_array_datatype_read(
                        &datatype,
                        &format!("left_{index}"),
                        100 + index,
                        200 + index,
                        300 + index,
                    ),
                    nested_array_datatype_read(
                        &datatype,
                        &format!("right_{index}"),
                        400 + index,
                        500 + index,
                        600 + index,
                    ),
                )
            })
            .collect();
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and_vec(equalities)),
            ClauseHead::Predicate(predicate, vec![ChcExpr::var(head_array)]),
        ));

        let mut exact_caps = projection_caps(32, 20_000);
        exact_caps.max_total_term_columns = 128;
        let stats = admit_dt_flatten_projection(
            &problem,
            exact_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("eight derived sixteen-column reads exactly at the cap must be admitted");
        assert_eq!(stats.total_term_columns, 128);
        assert_eq!(stats.max_occurrence_width, 16);

        let mut below_caps = exact_caps;
        below_caps.max_total_term_columns = 127;
        let failure = admit_dt_flatten_projection(
            &problem,
            below_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("repeated nested datatype reads must not bypass the projection cap");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("projected datatype flatten columns 16 > cap 15")
        ));
    }

    #[test]
    fn datatype_projection_enforces_work_cancellation_and_deadline_boundaries() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("P", vec![compact_binary_datatype(5)]);

        let work_failure = admit_dt_flatten_projection(
            &problem,
            projection_caps(64, 10),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("projected traversal must stop at its work cap before materializing columns");
        assert!(matches!(
            work_failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("projected datatype flatten expansion work 11 > cap 10")
        ));

        let cancelled = CancellationToken::new();
        cancelled.cancel();
        assert_eq!(
            admit_dt_flatten_projection(
                &problem,
                projection_caps(64, 1_000),
                &cancelled,
                Instant::now() + Duration::from_secs(1),
            ),
            Err(RouteAdmissionFailure::Cancelled)
        );
        assert_eq!(
            admit_dt_flatten_projection(
                &problem,
                projection_caps(64, 1_000),
                &CancellationToken::new(),
                Instant::now(),
            ),
            Err(RouteAdmissionFailure::Deadline)
        );
    }

    #[test]
    fn datatype_fanout_accepts_exact_boundaries_and_rejects_plus_one() {
        let surface = RouteSurfaceStats {
            total_expr_nodes: 7,
            total_sort_nodes: 3,
            total_name_bytes: 5,
            ..RouteSurfaceStats::default()
        };
        let projection = DtFlattenProjectionStats {
            max_occurrence_width: 4,
            ..DtFlattenProjectionStats::default()
        };

        // Clone work is 7 * 4 = 28. Generated-name bytes are
        // (5 + (7 + 3) * 2) * 4 = 100.
        let exact = admit_dt_flatten_fanout(&surface, &projection, fanout_caps(28, 100, 2))
            .expect("fanout exactly at both caps must be admitted");
        assert_eq!(exact.expr_clone_work, 28);
        assert_eq!(exact.generated_name_bytes, 100);

        let clone_failure = admit_dt_flatten_fanout(&surface, &projection, fanout_caps(27, 100, 2))
            .expect_err("one clone-work unit above the cap must fail closed");
        assert!(matches!(
            clone_failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten expression clone work 28 > cap 27")
        ));

        let name_failure = admit_dt_flatten_fanout(&surface, &projection, fanout_caps(28, 99, 2))
            .expect_err("one generated name byte above the cap must fail closed");
        assert!(matches!(
            name_failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten generated name bytes 100 > cap 99")
        ));
    }

    #[test]
    fn repeated_nullary_enum_constructor_fanout_has_exact_boundary() {
        let datatype = nullary_enum(4);
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![datatype.clone(), datatype.clone()]);
        for clause_index in 0..2 {
            problem.add_clause(HornClause::new(
                ClauseBody::empty(),
                ClauseHead::Predicate(
                    predicate,
                    vec![
                        ChcExpr::FuncApp(
                            format!("opaque-left{clause_index}"),
                            datatype.clone(),
                            Vec::new(),
                        ),
                        ChcExpr::FuncApp(
                            format!("opaque-right{clause_index}"),
                            datatype.clone(),
                            Vec::new(),
                        ),
                    ],
                ),
            ));
        }

        let mut surface_caps = caps();
        surface_caps.max_total_name_bytes = 4_096;
        let surface = scan_problem_surface(
            &problem,
            surface_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the repeated four-constructor enum surface must be admitted");
        assert_eq!(surface.total_expr_nodes, 4);

        let projection = admit_dt_flatten_projection(
            &problem,
            projection_caps(8, 1_000),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the width-one nullary enum projection must be admitted");
        assert_eq!(projection.max_occurrence_width, 1);
        assert_eq!(projection.total_term_columns, 4);
        // Each of six sort occurrences (two declaration arguments plus four
        // clause subjects) scans four constructors, emits three tester/ITE
        // links, and shallow-clones its one-node subject three times:
        // 4 + 2 * 3 + 1 * 3 = 13 units per occurrence.
        assert_eq!(projection.constructor_rewrite_work, 78);

        let exact = admit_dt_flatten_fanout(&surface, &projection, fanout_caps(82, usize::MAX, 0))
            .expect(
                "four base nodes plus seventy-eight constructor units exactly at the cap must pass",
            );
        assert_eq!(exact.expr_clone_work, 82);

        let failure =
            admit_dt_flatten_fanout(&surface, &projection, fanout_caps(81, usize::MAX, 0))
                .expect_err("repeated nullary constructors must not bypass the clone-work cap");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten expression clone work 82 > cap 81")
        ));
    }

    #[test]
    fn wide_nullary_enum_subject_charges_direct_arc_vector_clones_exactly() {
        let datatype = nullary_enum(4);
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![datatype.clone()]);
        let wide_subject = ChcExpr::FuncApp(
            "opaque-enum".to_string(),
            datatype,
            (0..5).map(|_| Arc::new(ChcExpr::Bool(true))).collect(),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::empty(),
            ClauseHead::Predicate(predicate, vec![wide_subject]),
        ));

        let surface = scan_problem_surface(
            &problem,
            caps(),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the wide opaque enum subject must fit the input surface caps");
        assert_eq!(surface.total_expr_nodes, 6);

        let projection = admit_dt_flatten_projection(
            &problem,
            projection_caps(8, 1_000),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the wide width-one enum projection must be admitted");
        // Predicate plan: 4 table + 6 tester/ITE + 3 one-node variable
        // clones = 13. Clause subject: the same 10 table/tester units plus
        // 3 * (one FuncApp root + five direct Arc entries) = 28.
        assert_eq!(projection.constructor_rewrite_work, 41);

        let exact = admit_dt_flatten_fanout(&surface, &projection, fanout_caps(47, usize::MAX, 0))
            .expect("six base nodes plus forty-one constructor units at the cap must pass");
        assert_eq!(exact.expr_clone_work, 47);
        let failure =
            admit_dt_flatten_fanout(&surface, &projection, fanout_caps(46, usize::MAX, 0))
                .expect_err("one wide-root vector clone unit over the cap must fail closed");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten expression clone work 47 > cap 46")
        ));
    }

    #[test]
    fn datatype_metadata_name_replay_accepts_exact_boundary_and_rejects_plus_one() {
        let surface = RouteSurfaceStats {
            total_expr_nodes: 2,
            total_sort_nodes: 1,
            total_name_bytes: 5,
            datatype_sort_occurrences: 3,
            datatype_metadata_name_bytes: 7,
            ..RouteSurfaceStats::default()
        };
        let projection = DtFlattenProjectionStats {
            max_occurrence_width: 2,
            ..DtFlattenProjectionStats::default()
        };

        // Clone work is 2 * 2 = 4. Generated-name bytes are
        // (5 + 7 * 3 + (2 + 1) * 2) * 2 = 64.
        let exact = admit_dt_flatten_fanout(&surface, &projection, fanout_caps(4, 64, 2))
            .expect("shared metadata name replay exactly at the cap must be admitted");
        assert_eq!(exact.generated_name_bytes, 64);

        let failure = admit_dt_flatten_fanout(&surface, &projection, fanout_caps(4, 63, 2))
            .expect_err("one shared metadata replay byte above the cap must fail closed");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten generated name bytes 64 > cap 63")
        ));
    }

    #[test]
    fn shared_datatype_metadata_names_are_charged_for_every_sort_occurrence() {
        let selector_name = "selector_segment_".repeat(8);
        let constructor_name = "make-Shared";
        let datatype = ChcSort::Datatype {
            name: "Shared".to_string(),
            constructors: Arc::new(vec![ChcDtConstructor {
                name: constructor_name.to_string(),
                selectors: vec![ChcDtSelector {
                    name: selector_name.clone(),
                    sort: ChcSort::Int,
                }],
            }]),
        };
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![datatype.clone()]);
        for index in 0..3 {
            problem.add_clause(HornClause::new(
                ClauseBody::empty(),
                ClauseHead::Predicate(
                    predicate,
                    vec![ChcExpr::var(ChcVar::new(
                        format!("value{index}"),
                        datatype.clone(),
                    ))],
                ),
            ));
        }

        let mut surface_caps = caps();
        surface_caps.max_total_name_bytes = 4_096;
        let surface = scan_problem_surface(
            &problem,
            surface_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the small shared datatype surface must be measurable");
        assert_eq!(surface.datatype_sort_occurrences, 4);
        assert_eq!(
            surface.datatype_metadata_name_bytes,
            constructor_name.len() + selector_name.len()
        );

        let projection = admit_dt_flatten_projection(
            &problem,
            projection_caps(8, 1_000),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the one-column shared datatype projection must be admitted");
        assert_eq!(projection.max_occurrence_width, 1);
        let expected = surface.total_name_bytes
            + surface.datatype_metadata_name_bytes * surface.datatype_sort_occurrences;
        let exact =
            admit_dt_flatten_fanout(&surface, &projection, fanout_caps(usize::MAX, expected, 0))
                .expect("the exact shared-name amplification boundary must be admitted");
        assert_eq!(exact.generated_name_bytes, expected);
        let failure = admit_dt_flatten_fanout(
            &surface,
            &projection,
            fanout_caps(usize::MAX, expected - 1, 0),
        )
        .expect_err("one shared-name byte above the boundary must fail closed");
        assert!(matches!(failure, RouteAdmissionFailure::Cap(_)));
    }

    #[test]
    fn datatype_fanout_arithmetic_overflow_fails_closed() {
        let width_one = DtFlattenProjectionStats {
            max_occurrence_width: 1,
            ..DtFlattenProjectionStats::default()
        };
        let width_two = DtFlattenProjectionStats {
            max_occurrence_width: 2,
            ..DtFlattenProjectionStats::default()
        };
        let clone_overflow = RouteSurfaceStats {
            total_expr_nodes: usize::MAX,
            ..RouteSurfaceStats::default()
        };
        admit_dt_flatten_fanout(
            &clone_overflow,
            &width_one,
            fanout_caps(usize::MAX, usize::MAX, 0),
        )
        .expect("a maximum-sized clone meter at width one must remain representable");
        let failure = admit_dt_flatten_fanout(
            &clone_overflow,
            &width_two,
            fanout_caps(usize::MAX, usize::MAX, 0),
        )
        .expect_err("overflowing expression clone work must fail closed");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten expression clone work")
        ));

        let name_overflow = RouteSurfaceStats {
            total_name_bytes: usize::MAX,
            ..RouteSurfaceStats::default()
        };
        admit_dt_flatten_fanout(
            &name_overflow,
            &width_one,
            fanout_caps(usize::MAX, usize::MAX, 0),
        )
        .expect("a maximum-sized generated-name meter at width one must remain representable");
        let failure = admit_dt_flatten_fanout(
            &name_overflow,
            &width_two,
            fanout_caps(usize::MAX, usize::MAX, 0),
        )
        .expect_err("overflowing generated name bytes must fail closed");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten generated name bytes")
        ));

        let metadata_overflow = RouteSurfaceStats {
            datatype_sort_occurrences: 2,
            datatype_metadata_name_bytes: usize::MAX,
            ..RouteSurfaceStats::default()
        };
        let exact_metadata = RouteSurfaceStats {
            datatype_sort_occurrences: 1,
            datatype_metadata_name_bytes: usize::MAX,
            ..RouteSurfaceStats::default()
        };
        admit_dt_flatten_fanout(
            &exact_metadata,
            &width_one,
            fanout_caps(usize::MAX, usize::MAX, 0),
        )
        .expect("a maximum-sized metadata-name meter at one occurrence is representable");
        let failure = admit_dt_flatten_fanout(
            &metadata_overflow,
            &width_one,
            fanout_caps(usize::MAX, usize::MAX, 0),
        )
        .expect_err("overflowing shared metadata-name replay must fail closed");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("datatype-flatten generated name bytes")
        ));
    }

    #[test]
    fn body_predicate_atom_cap_fails_closed_before_transform() {
        let problem = repeated_body_problem(3);
        let failure = scan_problem_surface(
            &problem,
            caps(),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("three body atoms must exceed the two-atom cap");
        assert!(
            matches!(failure, RouteAdmissionFailure::Cap(reason) if reason.contains("body predicate atoms 3 > cap 2"))
        );
    }

    #[test]
    fn admission_observes_cancellation_and_expired_deadline() {
        let problem = repeated_body_problem(1);
        let cancellation = CancellationToken::new();
        cancellation.cancel();
        assert_eq!(
            scan_problem_surface(
                &problem,
                caps(),
                &cancellation,
                Instant::now() + Duration::from_secs(1),
            ),
            Err(RouteAdmissionFailure::Cancelled)
        );
        assert_eq!(
            scan_problem_surface(&problem, caps(), &CancellationToken::new(), Instant::now(),),
            Err(RouteAdmissionFailure::Deadline)
        );
    }

    #[test]
    fn problem_clone_fanout_admission_enforces_aggregate_and_boundaries() {
        let problem = repeated_body_problem(2);
        let mut exact = caps();
        exact.max_total_body_atoms = 4;
        let stats = admit_problem_clone_fanout(
            &problem,
            exact,
            2,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("two two-atom clauses exactly meet the aggregate cap");
        assert_eq!(stats.total_body_atoms, 2);

        let mut below = exact;
        below.max_total_body_atoms = 3;
        let failure = admit_problem_clone_fanout(
            &problem,
            below,
            2,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("two copies must fail one atom past the aggregate cap");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("cloned body predicate atoms 4 > cap 3")
        ));

        let cancelled = CancellationToken::new();
        cancelled.cancel();
        assert_eq!(
            admit_problem_clone_fanout(
                &problem,
                exact,
                2,
                &cancelled,
                Instant::now() + Duration::from_secs(1),
            ),
            Err(RouteAdmissionFailure::Cancelled)
        );
        assert_eq!(
            admit_problem_clone_fanout(
                &problem,
                exact,
                2,
                &CancellationToken::new(),
                Instant::now(),
            ),
            Err(RouteAdmissionFailure::Deadline)
        );
    }

    #[test]
    fn array_select_count_bounds_key_collection_before_clone() {
        let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let mut problem = ChcProblem::new();
        let predicate = problem.declare_predicate("P", vec![array_sort.clone()]);
        let array = ChcVar::new("a", array_sort);
        let two_selects = ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::int(0)),
            ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::int(1)),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(two_selects),
            ClauseHead::Predicate(predicate, vec![ChcExpr::var(array)]),
        ));
        let failure = scan_problem_surface(
            &problem,
            caps(),
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("two key occurrences must exceed the one-key cap");
        assert!(
            matches!(failure, RouteAdmissionFailure::Cap(reason) if reason.contains("array select/key occurrences 2 > cap 1"))
        );
    }

    #[test]
    fn const_key_rewrite_projection_accepts_exact_boundary_and_rejects_plus_one() {
        let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
        let array = ChcVar::new("a", array_sort.clone());
        let next_array = ChcVar::new("next", array_sort);
        let store_equality = ChcExpr::eq(
            ChcExpr::var(next_array),
            ChcExpr::store(
                ChcExpr::var(array.clone()),
                ChcExpr::int(0),
                ChcExpr::int(12),
            ),
        );
        let constraint = ChcExpr::and(
            store_equality,
            ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::int(0)),
                    ChcExpr::int(10),
                ),
                ChcExpr::eq(
                    ChcExpr::select(ChcExpr::var(array), ChcExpr::int(1)),
                    ChcExpr::int(11),
                ),
            ),
        );
        let problem = constraint_problem(constraint);
        let mut generous = caps();
        generous.max_array_selects = 2;
        generous.max_expr_nodes_per_clause = 32;
        generous.max_total_expr_nodes = 32;
        generous.max_variable_occurrences_per_clause = 8;
        generous.max_const_key_rewrite_visits = usize::MAX;
        let measured = scan_problem_surface(
            &problem,
            generous,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("the small two-key expression must be measurable");
        assert_eq!(measured.array_selects, 2);
        assert!(measured.projected_const_key_rewrite_visits > 1);

        let mut exact = generous;
        exact.max_const_key_rewrite_visits = measured.projected_const_key_rewrite_visits;
        scan_problem_surface(
            &problem,
            exact,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("a node/key product exactly at the cap must be admitted");

        let mut below = exact;
        below.max_const_key_rewrite_visits -= 1;
        let failure = scan_problem_surface(
            &problem,
            below,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("one projected node/key visit above the cap must fail closed");
        assert!(matches!(
            failure,
            RouteAdmissionFailure::Cap(reason)
                if reason.contains("projected const-key scalarization node/key visits")
        ));
    }

    fn unary_expr_depth(depth: usize) -> ChcExpr {
        assert!(depth > 0);
        // Use an uninterpreted unary application rather than nested `not`.
        // `ChcProblem::add_clause` simplifies constant expressions and double
        // negations, which would collapse the intended hostile surface before
        // the admission scanner sees it.
        let mut expr = ChcExpr::var(ChcVar::new("leaf", ChcSort::Bool));
        for _ in 1..depth {
            expr = ChcExpr::FuncApp(
                "f".to_string(),
                ChcSort::Bool,
                vec![std::sync::Arc::new(expr)],
            );
        }
        expr
    }

    fn constraint_problem(constraint: ChcExpr) -> ChcProblem {
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(constraint),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    fn expression_depth_cap_accepts_exact_boundary_and_rejects_plus_one() {
        let mut depth_caps = caps();
        depth_caps.max_expr_depth = 4;
        scan_problem_surface(
            &constraint_problem(unary_expr_depth(4)),
            depth_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("an expression exactly at the depth cap must be admitted");

        let failure = scan_problem_surface(
            &constraint_problem(unary_expr_depth(5)),
            depth_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("an expression one level beyond the depth cap must fail closed");
        assert!(
            matches!(failure, RouteAdmissionFailure::Cap(reason) if reason.contains("expression depth 5 > cap 4"))
        );
    }

    fn nested_array_sort(depth: usize) -> ChcSort {
        assert!(depth > 0);
        let mut sort = ChcSort::Int;
        for _ in 1..depth {
            sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(sort));
        }
        sort
    }

    #[test]
    fn sort_depth_cap_accepts_exact_boundary_and_rejects_plus_one() {
        let mut depth_caps = caps();
        depth_caps.max_sort_depth = 4;
        let mut exact = ChcProblem::new();
        exact.declare_predicate("P", vec![nested_array_sort(4)]);
        scan_predicate_surface(
            &exact,
            depth_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("a predicate sort exactly at the depth cap must be admitted");

        let mut too_deep = ChcProblem::new();
        too_deep.declare_predicate("P", vec![nested_array_sort(5)]);
        let failure = scan_predicate_surface(
            &too_deep,
            depth_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("a predicate sort one level beyond the cap must fail closed");
        assert!(
            matches!(failure, RouteAdmissionFailure::Cap(reason) if reason.contains("sort depth 5 > cap 4"))
        );
    }

    #[test]
    fn sort_depth_scan_covers_expression_and_datatype_sort_carriers() {
        let mut depth_caps = caps();
        depth_caps.max_sort_depth = 4;
        let deep = nested_array_sort(5);
        let deadline = || Instant::now() + Duration::from_secs(1);

        // Structurally identical equality operands are folded to `true` when a
        // clause is inserted. Keep the carriers distinct so they reach the
        // scanner while retaining the same deeply nested sort.
        let left_variable = ChcVar::new("left", deep.clone());
        let right_variable = ChcVar::new("right", deep.clone());
        let variable_problem = constraint_problem(ChcExpr::eq(
            ChcExpr::var(left_variable),
            ChcExpr::var(right_variable),
        ));
        assert!(matches!(
            scan_problem_surface(
                &variable_problem,
                depth_caps,
                &CancellationToken::new(),
                deadline(),
            ),
            Err(RouteAdmissionFailure::Cap(reason)) if reason.contains("variable sort depth")
        ));

        let left_function = ChcExpr::FuncApp("f".to_string(), deep.clone(), Vec::new());
        let right_function = ChcExpr::FuncApp("g".to_string(), deep.clone(), Vec::new());
        let function_problem = constraint_problem(ChcExpr::eq(left_function, right_function));
        assert!(matches!(
            scan_problem_surface(
                &function_problem,
                depth_caps,
                &CancellationToken::new(),
                deadline(),
            ),
            Err(RouteAdmissionFailure::Cap(reason)) if reason.contains("function return sort depth")
        ));

        let left_constant_array =
            ChcExpr::ConstArray(deep.clone(), std::sync::Arc::new(ChcExpr::Int(0)));
        let right_constant_array =
            ChcExpr::ConstArray(deep.clone(), std::sync::Arc::new(ChcExpr::Int(1)));
        let constant_array_problem =
            constraint_problem(ChcExpr::eq(left_constant_array, right_constant_array));
        assert!(matches!(
            scan_problem_surface(
                &constant_array_problem,
                depth_caps,
                &CancellationToken::new(),
                deadline(),
            ),
            Err(RouteAdmissionFailure::Cap(reason)) if reason.contains("constant-array key sort depth")
        ));

        let mut datatype_problem = ChcProblem::new();
        datatype_problem.add_datatype_def(
            "D".to_string(),
            vec![("mk-D".to_string(), vec![("deep".to_string(), deep)])],
        );
        assert!(matches!(
            scan_predicate_surface(
                &datatype_problem,
                depth_caps,
                &CancellationToken::new(),
                deadline(),
            ),
            Err(RouteAdmissionFailure::Cap(reason)) if reason.contains("datatype selector sort depth")
        ));
    }

    #[test]
    fn aggregate_name_byte_cap_accepts_exact_boundary_and_rejects_plus_one() {
        let predicate_name = "p".repeat(32);
        let mut problem = ChcProblem::new();
        problem.declare_predicate(&predicate_name, vec![]);

        let mut exact_caps = caps();
        exact_caps.max_total_name_bytes = predicate_name.len();
        let stats = scan_problem_surface(
            &problem,
            exact_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect("an aggregate name surface exactly at the byte cap must be admitted");
        assert_eq!(stats.total_name_bytes, exact_caps.max_total_name_bytes);

        let mut below_caps = exact_caps;
        below_caps.max_total_name_bytes -= 1;
        let failure = scan_problem_surface(
            &problem,
            below_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("one byte beyond the aggregate name cap must fail closed");
        assert!(
            matches!(failure, RouteAdmissionFailure::Cap(reason) if reason.contains("total surface name bytes 32 > cap 31"))
        );
    }

    #[test]
    fn one_large_expression_symbol_cannot_bypass_small_node_caps() {
        const SYMBOL_BYTES: usize = 4 * 1024;
        let symbol = "v".repeat(SYMBOL_BYTES);
        let problem = constraint_problem(ChcExpr::var(ChcVar::new(symbol, ChcSort::Bool)));
        let mut name_caps = caps();
        name_caps.max_total_name_bytes = SYMBOL_BYTES - 1;

        let failure = scan_problem_surface(
            &problem,
            name_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("a single oversized variable name must be rejected before problem clone");
        assert!(
            matches!(failure, RouteAdmissionFailure::Cap(reason) if reason.contains("total surface name bytes 4096 > cap 4095"))
        );
    }

    #[test]
    fn one_large_action_declaration_cannot_bypass_surface_caps() {
        const SYMBOL_BYTES: usize = 4 * 1024;
        let mut problem = ChcProblem::new();
        problem.declare_action("a".repeat(SYMBOL_BYTES));
        let mut name_caps = caps();
        name_caps.max_total_name_bytes = SYMBOL_BYTES - 1;

        let failure = scan_predicate_surface(
            &problem,
            name_caps,
            &CancellationToken::new(),
            Instant::now() + Duration::from_secs(1),
        )
        .expect_err("an oversized action name must be rejected before problem clone");
        assert!(
            matches!(failure, RouteAdmissionFailure::Cap(reason) if reason.contains("total surface name bytes 4096 > cap 4095"))
        );
    }
}
