// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Logic detection and sort-to-SMT-LIB conversion helpers for the executor adapter.

use crate::{
    ChcDtConstructor, ChcError, ChcExpr, ChcProblem, ChcResult, ChcSort, ChcVar, ClauseHead,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

pub(super) const MAX_DT_DECLARATIONS: usize = 256;
pub(super) const MAX_DT_CONSTRUCTORS: usize = 4_096;
pub(super) const MAX_DT_SELECTORS: usize = 16_384;
const MAX_DT_SORT_NODES: usize = 32_768;
pub(super) const MAX_DT_EXPR_NODES: usize = 131_072;
const MAX_DT_NESTING_DEPTH: usize = 512;
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
        collector.charge_name_bytes(var.name.len())?;
        collector.visit_sort(&var.sort)?;
    }
    Ok(collector.finish())
}

/// Collect unique datatype declarations from free variables and expression-local
/// constructor/selector/tester terms.
pub(crate) fn collect_dt_declarations_for_expr<'a>(
    vars: &'a [ChcVar],
    expr: &'a ChcExpr,
) -> Result<Vec<(&'a str, &'a [ChcDtConstructor])>, DatatypeDeclarationError> {
    let mut collector = DatatypeDeclarationCollector::default();
    for var in vars {
        collector.charge_name_bytes(var.name.len())?;
        collector.visit_sort(&var.sort)?;
    }
    collector.visit_expr(expr)?;
    Ok(collector.finish())
}

pub(crate) fn collect_dt_declarations_for_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
) -> Result<Vec<(&'a str, &'a [ChcDtConstructor])>, DatatypeDeclarationError> {
    let mut collector = DatatypeDeclarationCollector::default();
    let mut root_count = 0usize;
    for expr in exprs {
        root_count = bounded_add(
            root_count,
            1,
            MAX_EXECUTOR_EXPR_ROOTS,
            "executor expression roots",
        )?;
        collector.visit_expr(expr)?;
    }
    Ok(collector.finish())
}

#[derive(Default)]
struct DatatypeDeclarationCollector<'a> {
    definitions: FxHashMap<&'a str, &'a [ChcDtConstructor]>,
    expanded_definition_instances: FxHashSet<(usize, usize)>,
    sort_nodes: usize,
    expr_nodes: usize,
    constructors: usize,
    selectors: usize,
    expanded_constructors: usize,
    expanded_selectors: usize,
    name_bytes: usize,
    definition_compare_work: usize,
}

impl<'a> DatatypeDeclarationCollector<'a> {
    fn charge_name_bytes(&mut self, bytes: usize) -> Result<(), DatatypeDeclarationError> {
        self.name_bytes = bounded_add(
            self.name_bytes,
            bytes,
            MAX_DT_NAME_BYTES,
            "executor surface name bytes",
        )?;
        Ok(())
    }

    fn visit_sort(&mut self, root: &'a ChcSort) -> Result<(), DatatypeDeclarationError> {
        let mut stack = vec![(root, 0usize)];
        while let Some((sort, depth)) = stack.pop() {
            if depth > MAX_DT_NESTING_DEPTH {
                return Err(DatatypeDeclarationError::ResourceLimit(
                    "datatype sort nesting depth",
                ));
            }
            self.sort_nodes =
                bounded_add(self.sort_nodes, 1, MAX_DT_SORT_NODES, "datatype sort nodes")?;

            match sort {
                ChcSort::Datatype { name, constructors } => {
                    self.name_bytes = bounded_add(
                        self.name_bytes,
                        name.len(),
                        MAX_DT_NAME_BYTES,
                        "datatype name bytes",
                    )?;
                    if let Some(previous) = self.definitions.get(name.as_str()) {
                        if !std::ptr::eq(previous.as_ptr(), constructors.as_ptr())
                            && !datatype_definitions_equivalent_bounded(
                                previous,
                                constructors,
                                &mut self.definition_compare_work,
                            )?
                        {
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
                    let instance_key = (constructors.as_ptr() as usize, constructors.len());
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
                            MAX_DT_NAME_BYTES,
                            "datatype name bytes",
                        )?;
                        for selector in &constructor.selectors {
                            self.name_bytes = bounded_add(
                                self.name_bytes,
                                selector.name.len(),
                                MAX_DT_NAME_BYTES,
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
                        MAX_DT_NAME_BYTES,
                        "datatype name bytes",
                    )?;
                }
            }
        }
        Ok(())
    }

    fn visit_expr(&mut self, root: &'a ChcExpr) -> Result<(), DatatypeDeclarationError> {
        self.expr_nodes = bounded_add(
            self.expr_nodes,
            1,
            MAX_DT_EXPR_NODES,
            "datatype expression nodes",
        )?;
        let mut stack = vec![(root, 0usize)];
        while let Some((expr, depth)) = stack.pop() {
            if depth > MAX_DT_NESTING_DEPTH {
                return Err(DatatypeDeclarationError::ResourceLimit(
                    "datatype expression nesting depth",
                ));
            }
            match expr {
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _) => {}
                ChcExpr::IsTesterMarker(name) => self.charge_name_bytes(name.len())?,
                ChcExpr::Var(var) => {
                    self.charge_name_bytes(var.name.len())?;
                    self.visit_sort(&var.sort)?;
                }
                ChcExpr::Op(_, args) => {
                    self.expr_nodes = bounded_add(
                        self.expr_nodes,
                        args.len(),
                        MAX_DT_EXPR_NODES,
                        "datatype expression nodes",
                    )?;
                    stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
                }
                ChcExpr::PredicateApp(name, _, args) => {
                    self.charge_name_bytes(name.len())?;
                    self.expr_nodes = bounded_add(
                        self.expr_nodes,
                        args.len(),
                        MAX_DT_EXPR_NODES,
                        "datatype expression nodes",
                    )?;
                    stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
                }
                ChcExpr::FuncApp(name, sort, args) => {
                    self.charge_name_bytes(name.len())?;
                    self.visit_sort(sort)?;
                    self.expr_nodes = bounded_add(
                        self.expr_nodes,
                        args.len(),
                        MAX_DT_EXPR_NODES,
                        "datatype expression nodes",
                    )?;
                    stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
                }
                ChcExpr::ConstArrayMarker(sort) => self.visit_sort(sort)?,
                ChcExpr::ConstArray(key_sort, value) => {
                    self.visit_sort(key_sort)?;
                    self.expr_nodes = bounded_add(
                        self.expr_nodes,
                        1,
                        MAX_DT_EXPR_NODES,
                        "datatype expression nodes",
                    )?;
                    stack.push((value.as_ref(), depth + 1));
                }
            }
        }
        Ok(())
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
    Ok(collect_uninterpreted_function_surface(exprs)?.applications)
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
) -> ChcResult<Vec<&'a ChcExpr>> {
    let mut roots = Vec::new();
    for expr in exprs {
        if roots.len() >= MAX_EXECUTOR_EXPR_ROOTS {
            return Err(executor_resource_limit("expression roots"));
        }
        roots.push(expr);
    }
    Ok(roots)
}

fn push_bounded_executor_expr_root<'a>(
    roots: &mut Vec<&'a ChcExpr>,
    expr: &'a ChcExpr,
) -> ChcResult<()> {
    if roots.len() >= MAX_EXECUTOR_EXPR_ROOTS {
        return Err(executor_resource_limit("expression roots"));
    }
    roots.push(expr);
    Ok(())
}

fn collect_uninterpreted_function_surface<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
) -> ChcResult<UninterpretedFunctionSurface> {
    let exprs = bounded_executor_expr_roots(exprs)?;

    // One collector owns the caps for the complete expression set.  Calling a
    // fresh collector per root would let a large CHC problem multiply every
    // node/name/datatype limit by its clause count.
    let datatype_declarations = collect_dt_declarations_for_exprs(exprs.iter().copied())
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
    let mut stack = exprs;
    let mut expr_nodes = 0usize;
    let mut ordinary_application_occurrences = 0usize;
    let mut uf_argument_occurrences = 0usize;
    while let Some(current) = stack.pop() {
        expr_nodes = expr_nodes
            .checked_add(1)
            .filter(|nodes| *nodes <= MAX_DT_EXPR_NODES)
            .ok_or_else(|| executor_resource_limit("expression nodes"))?;
        match current {
            ChcExpr::FuncApp(name, return_sort, args) => {
                let pending = stack
                    .len()
                    .checked_add(args.len())
                    .ok_or_else(|| executor_resource_limit("pending expression nodes"))?;
                if expr_nodes
                    .checked_add(pending)
                    .is_none_or(|nodes| nodes > MAX_DT_EXPR_NODES)
                {
                    return Err(executor_resource_limit("expression nodes"));
                }
                stack.extend(args.iter().rev().map(AsRef::as_ref));
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

                if seen_applications.insert((*current).clone()) {
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
                    .is_none_or(|nodes| nodes > MAX_DT_EXPR_NODES)
                {
                    return Err(executor_resource_limit("expression nodes"));
                }
                stack.extend(args.iter().rev().map(AsRef::as_ref));
            }
            ChcExpr::ConstArray(_, value) => {
                if expr_nodes
                    .checked_add(stack.len())
                    .and_then(|nodes| nodes.checked_add(1))
                    .is_none_or(|nodes| nodes > MAX_DT_EXPR_NODES)
                {
                    return Err(executor_resource_limit("expression nodes"));
                }
                stack.push(value.as_ref());
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
    Ok(collect_uninterpreted_function_surface(exprs)?.declarations)
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
    let mut exprs = Vec::new();
    for clause in problem.clauses() {
        if let Some(constraint) = &clause.body.constraint {
            push_bounded_executor_expr_root(&mut exprs, constraint)?;
        }
        for argument in clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter())
        {
            push_bounded_executor_expr_root(&mut exprs, argument)?;
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for argument in args {
                push_bounded_executor_expr_root(&mut exprs, argument)?;
            }
        }
    }
    collect_uninterpreted_function_declarations_for_exprs(exprs)
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

fn expr_sort_has(expr: &ChcExpr, pred: fn(&ChcSort) -> bool) -> bool {
    match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => false,
        ChcExpr::Var(var) => pred(&var.sort),
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
            args.iter().any(|arg| expr_sort_has(arg, pred))
        }
        ChcExpr::FuncApp(_, sort, args) => {
            pred(sort) || args.iter().any(|arg| expr_sort_has(arg, pred))
        }
        ChcExpr::ConstArrayMarker(sort) => pred(sort),
        ChcExpr::IsTesterMarker(_) => false,
        ChcExpr::ConstArray(key_sort, value) => pred(key_sort) || expr_sort_has(value, pred),
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
