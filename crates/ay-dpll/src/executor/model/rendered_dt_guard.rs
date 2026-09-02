// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource and exact-fragment guards for rendered datatype values.

use std::cell::RefCell;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::Sort;

use crate::executor::Executor;

#[cfg(test)]
pub(super) use super::rendered_dt_limits::rendered_sexp_within_limits;
use super::rendered_dt_limits::{
    SchemaSourceBudget, MAX_RENDERED_DT_BYTES, MAX_RENDERED_DT_DEPTH, MAX_RENDERED_DT_NODES,
};

/// A bounded snapshot of the datatype schema plus exact-fragment results.
///
/// Building this once per completion/gate view avoids multiplying a linear
/// registry scan by every datatype-valued application or array cell. An
/// oversized/duplicate registry produces an invalid guard and all queries fail
/// closed.
pub(super) struct RenderedDatatypeGuard {
    schemas: Option<HashMap<String, DatatypeSchema>>,
    #[cfg(test)]
    exact_by_sort: RefCell<HashMap<Sort, bool>>,
    exact_array_cell_by_sort: RefCell<HashMap<Sort, bool>>,
}

struct DatatypeSchema {
    constructors: Vec<GuardConstructor>,
    render_safe: bool,
}

struct GuardConstructor {
    internal: String,
    surface: String,
    field_sorts: Vec<Sort>,
}

impl RenderedDatatypeGuard {
    pub(super) fn new(exec: &Executor) -> Self {
        let mut schemas = HashMap::default();
        let mut nodes = 0usize;
        let mut source_budget = SchemaSourceBudget::new();
        for (name, constructors) in exec.ctx.datatype_iter() {
            if !source_budget.charge_identifier(name) {
                return Self::invalid();
            }
            nodes += 1;
            if nodes > MAX_RENDERED_DT_NODES {
                return Self::invalid();
            }
            nodes = match nodes.checked_add(constructors.len()) {
                Some(total) if total <= MAX_RENDERED_DT_NODES => total,
                _ => return Self::invalid(),
            };
            let mut guarded_constructors = Vec::with_capacity(constructors.len());
            // Carrier names are not emitted in constructor values and may
            // legitimately require quoting (the target ABI contains a space).
            // Constructor heads are emitted raw and must remain bare-safe.
            let mut render_safe = true;
            for constructor in constructors {
                let surface = exec.dt_surface(constructor);
                if !source_budget.charge_identifier(constructor)
                    || !source_budget.charge_identifier(surface)
                {
                    return Self::invalid();
                }
                let Some(fields) = exec.ctx.constructor_selector_info(constructor) else {
                    return Self::invalid();
                };
                nodes = match nodes.checked_add(fields.len()) {
                    Some(total) if total <= MAX_RENDERED_DT_NODES => total,
                    _ => return Self::invalid(),
                };
                for (field, sort) in fields {
                    if !source_budget.charge_identifier(field) || !source_budget.charge_sort(sort) {
                        return Self::invalid();
                    }
                }
                let surface = surface.to_string();
                render_safe &= ay_core::quote_symbol(&surface) == surface;
                guarded_constructors.push(GuardConstructor {
                    internal: constructor.clone(),
                    surface,
                    field_sorts: fields.iter().map(|(_, sort)| sort.clone()).collect(),
                });
            }
            if schemas
                .insert(
                    name.to_string(),
                    DatatypeSchema {
                        constructors: guarded_constructors,
                        render_safe,
                    },
                )
                .is_some()
            {
                return Self::invalid();
            }
        }
        Self {
            schemas: Some(schemas),
            #[cfg(test)]
            exact_by_sort: RefCell::new(HashMap::default()),
            exact_array_cell_by_sort: RefCell::new(HashMap::default()),
        }
    }

    fn invalid() -> Self {
        Self {
            schemas: None,
            #[cfg(test)]
            exact_by_sort: RefCell::new(HashMap::default()),
            exact_array_cell_by_sort: RefCell::new(HashMap::default()),
        }
    }

    pub(super) fn is_bounded(&self) -> bool {
        self.schemas.is_some()
    }

    pub(super) fn datatype_name<'a>(&self, sort: &'a Sort) -> Option<&'a str> {
        let schemas = self.schemas.as_ref()?;
        match sort {
            Sort::Uninterpreted(name) if name.len() <= 256 && schemas.contains_key(name) => {
                Some(name)
            }
            _ => None,
        }
    }

    /// Whether `sort` names a datatype this guard holds a bounded schema for.
    ///
    /// This is the CONSTRUCTION eligibility bar (#dt-opaque-app-model):
    /// total-DT construction produces typed [`ay_model_check::ModelValue`]s
    /// that the strict oracles and the independent gate evaluate directly, so
    /// it needs a bounded registered schema but NOT the exact rendered
    /// round-trip fragment. Requiring the test-only scalar rendered-exactness
    /// predicate here (as the original
    /// opaque-lane landing did) silently excluded every datatype with a scalar
    /// payload field (e.g. `Cons(hd: Int, tl: List)`): construction bailed
    /// entirely, other completion passes still committed structured values for
    /// sibling cells, and the independent gate — comparing an opaque carrier
    /// against a structured value — had to fail the whole SAT verdict closed.
    /// Rendering-dependent consumers (`exact_datatype_cell_completions`, the
    /// rendered-value parsers) each re-check `is_exact` per value themselves.
    pub(super) fn is_registered(&self, sort: &Sort) -> bool {
        self.datatype_name(sort).is_some()
    }

    #[cfg(test)]
    pub(super) fn is_exact(&self, sort: &Sort) -> bool {
        if self.datatype_name(sort).is_none() {
            return false;
        }
        if let Some(exact) = self.exact_by_sort.borrow().get(sort) {
            return *exact;
        }
        let exact = self.compute_exact(sort, false);
        self.exact_by_sort.borrow_mut().insert(sort.clone(), exact);
        exact
    }

    /// Whether one already-rendered, size-bounded array cell can be parsed
    /// exactly into this datatype. This keeps the ordinary opaque-completion
    /// fragment unchanged while admitting integer payloads at the array-model
    /// consumer boundary: unlike schema-driven completion, this path has the
    /// concrete rendered integer in hand and the global S-expression byte/node
    /// limits bound its `BigInt` parse.
    pub(super) fn is_exact_array_cell(&self, sort: &Sort) -> bool {
        if self.datatype_name(sort).is_none() {
            return false;
        }
        if let Some(exact) = self.exact_array_cell_by_sort.borrow().get(sort) {
            return *exact;
        }
        let exact = self.compute_exact(sort, true);
        self.exact_array_cell_by_sort
            .borrow_mut()
            .insert(sort.clone(), exact);
        exact
    }

    pub(super) fn constructor<'a>(
        &'a self,
        sort: &Sort,
        token: &str,
    ) -> Option<(&'a str, &'a [Sort])> {
        let name = self.datatype_name(sort)?;
        self.schemas
            .as_ref()?
            .get(name)?
            .constructors
            .iter()
            .find(|constructor| constructor.internal == token || constructor.surface == token)
            .map(|constructor| {
                (
                    constructor.internal.as_str(),
                    constructor.field_sorts.as_slice(),
                )
            })
    }

    fn compute_exact(&self, sort: &Sort, allow_bounded_int: bool) -> bool {
        let Some(schemas) = self.schemas.as_ref() else {
            return false;
        };
        let Some(root) = self.datatype_name(sort) else {
            return false;
        };
        let mut stack = vec![(root.to_string(), 0usize)];
        let mut seen = HashSet::default();
        let mut nodes = 0usize;
        let mut static_render_bytes = 0usize;
        while let Some((name, depth)) = stack.pop() {
            if depth > MAX_RENDERED_DT_DEPTH {
                return false;
            }
            if !seen.insert(name.clone()) {
                continue;
            }
            nodes += 1;
            if nodes > MAX_RENDERED_DT_NODES {
                return false;
            }
            let Some(schema) = schemas.get(&name) else {
                return false;
            };
            if !schema.render_safe {
                return false;
            }
            let mut datatype_child_constructors = 0usize;
            for constructor in &schema.constructors {
                let Some(has_datatype_child) = check_constructor(
                    schemas,
                    constructor,
                    depth,
                    allow_bounded_int,
                    &mut stack,
                    &mut nodes,
                    &mut static_render_bytes,
                ) else {
                    return false;
                };
                if has_datatype_child {
                    datatype_child_constructors += 1;
                    if datatype_child_constructors > 1 {
                        return false;
                    }
                }
            }
        }
        true
    }
}

/// Check one constructor in the linear, bounded exact-rendering fragment.
/// Returns whether it has its datatype child (at most one).
fn check_constructor(
    schemas: &HashMap<String, DatatypeSchema>,
    constructor: &GuardConstructor,
    depth: usize,
    allow_bounded_int: bool,
    stack: &mut Vec<(String, usize)>,
    nodes: &mut usize,
    static_render_bytes: &mut usize,
) -> Option<bool> {
    *nodes = nodes.checked_add(1)?;
    if *nodes > MAX_RENDERED_DT_NODES {
        return None;
    }
    let mut datatype_fields = 0usize;
    for field_sort in &constructor.field_sorts {
        *nodes = nodes.checked_add(1)?;
        if *nodes > MAX_RENDERED_DT_NODES {
            return None;
        }
        match field_sort {
            Sort::Bool => {}
            // An integer sort has no schema-level width bound, so it stays out
            // of ordinary opaque completion. At the array-cell consumer the
            // concrete rendered value is already protected by
            // `rendered_sexp_within_limits`, making its exact `BigInt` parse
            // bounded without granting schema-driven synthesis authority.
            Sort::Int if allow_bounded_int => {}
            Sort::BitVec(bitvec) => {
                if bitvec.width > 256 {
                    return None;
                }
                let width = usize::try_from(bitvec.width).ok()?;
                let bytes = if width % 4 == 0 {
                    width / 4 + 2
                } else {
                    width + 2
                };
                *static_render_bytes = static_render_bytes.checked_add(bytes)?;
                if *static_render_bytes > MAX_RENDERED_DT_BYTES {
                    return None;
                }
            }
            Sort::Array(array) if allow_bounded_int => {
                check_concrete_array_sort(
                    &array.index_sort,
                    &array.element_sort,
                    nodes,
                    static_render_bytes,
                )?;
            }
            Sort::Uninterpreted(field_name) => {
                if !schemas.contains_key(field_name) {
                    return None;
                }
                datatype_fields += 1;
                stack.push((field_name.clone(), depth + 1));
            }
            // Inline schemas, unbounded scalar payloads, and structured theory
            // sorts are outside this narrowly budgeted eager-completion lane.
            _ => return None,
        }
        if datatype_fields > 1 {
            return None;
        }
    }
    Some(datatype_fields == 1)
}

/// The concrete array-cell reader currently supports scalar finite-map keys
/// and values only. Arbitrarily large numerals and strings remain bounded by
/// the enclosing rendered S-expression limit; bitvectors additionally carry a
/// schema-level width cap.
fn check_concrete_array_sort(
    index_sort: &Sort,
    element_sort: &Sort,
    nodes: &mut usize,
    static_render_bytes: &mut usize,
) -> Option<()> {
    for sort in [index_sort, element_sort] {
        *nodes = nodes.checked_add(1)?;
        if *nodes > MAX_RENDERED_DT_NODES {
            return None;
        }
        match sort {
            Sort::Bool | Sort::Int | Sort::Real | Sort::String => {}
            Sort::BitVec(bitvec) if bitvec.width <= 256 => {
                let width = usize::try_from(bitvec.width).ok()?;
                let bytes = if width % 4 == 0 {
                    width / 4 + 2
                } else {
                    width + 2
                };
                *static_render_bytes = static_render_bytes.checked_add(bytes)?;
                if *static_render_bytes > MAX_RENDERED_DT_BYTES {
                    return None;
                }
            }
            _ => return None,
        }
    }
    Some(())
}

impl Executor {
    /// Whether every reachable field of this registered datatype has an exact
    /// gate/printer round trip today. This is intentionally narrower than the
    /// set of inhabited SMT sorts: unsupported renderers make opaque completion
    /// fail closed rather than silently changing representation.
    #[cfg(test)]
    pub(in crate::executor) fn datatype_value_is_exactly_roundtrippable(
        &self,
        sort: &Sort,
    ) -> bool {
        RenderedDatatypeGuard::new(self).is_exact(sort)
    }
}
