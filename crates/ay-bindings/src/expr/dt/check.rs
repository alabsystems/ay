// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Bounded signature checks, not validation of arbitrary expression bodies.
//!
//! Invariant for [`SortInner::DatatypeRef`]: a reference is resolved only
//! against the receiver's enclosing declarations, never against the
//! argument's sort, and never against a bare `Uninterpreted` name. Outside a
//! declaration of its name a reference is not a sort of its own, and a sort
//! that contains such a dangling reference is the same sort as nothing, not
//! even itself. Two datatype sorts are the same sort only when they are
//! structurally equal under that rule; a name alone never identifies a
//! datatype at this layer.
//!
//! Name-based identification happens once, at the solver carrier, under this
//! invariant: every datatype descriptor that reaches the carrier is
//! structurally equal to the registered definition of its name, and a name
//! has exactly one definition per program. [`authenticate_definitions`]
//! enforces it wherever descriptors enter a registry
//! (`AYProgram::try_declare_datatype`, `AYProgram::try_declare_const`) and
//! again at the native lowering, which resolves descriptors by name.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::sort::{DatatypeConstructor, DatatypeSort, Sort, SortInner};
use crate::SortError;

use super::Expr;

/// Whether two term sorts are the same sort: derived equality first (the
/// scalar fast path charges nothing), then the declaration-scoped structural
/// comparison, so equal declarations spelled with different unfoldings agree
/// while a sort containing a dangling reference agrees with nothing.
pub(crate) fn same_sorts(operation: &'static str, a: &Sort, b: &Sort) -> Result<bool, SortError> {
    if a == b {
        return Ok(a.dangling_datatype_ref().is_none());
    }
    Check::new(operation).same_sort(a, b)
}

/// Registered datatype definitions, keyed by name. Every entry is a closed
/// `SortInner::Datatype`: each reference inside it resolves to a declaration
/// inside it, so the entry means the same datatype in every position.
pub(crate) type Definitions = BTreeMap<String, Sort>;

/// What [`authenticate_definitions`] does with a datatype definition, nested
/// inside the sort it walks, whose name is registered nowhere.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Unregistered {
    /// Refuse it: the lowering, where every name must already be registered.
    Refuse,
    /// Collect it as a definition in its own right: the program registry,
    /// which then declares it before the definition that nests it.
    Register,
}

/// Authenticate every datatype definition in `sort` against `definitions`
/// and return the definitions to register, in dependency order (a nested
/// definition before the one nesting it, `sort` itself last when it is a
/// datatype that is not registered yet).
///
/// Each datatype node is well-formed (`Check::datatype`) and, in order:
/// a node named like an enclosing declaration must be structurally equal to
/// that declaration (an honest unfolding; anything else is shadowing); a node
/// whose name is registered must equal the registered definition; a node
/// whose name was collected earlier in this walk must equal that definition;
/// any other node is refused or collected per `unregistered`. A collected
/// definition must be closed on its own: a reference from inside it to a
/// datatype enclosing it (mutual recursion between separately declared
/// datatypes) is refused, as is a reference that no declaration encloses.
/// `sort` itself, when it is an unregistered datatype, is always collected.
pub(crate) fn authenticate_definitions<'a>(
    operation: &'static str,
    sort: &'a Sort,
    definitions: &'a Definitions,
    unregistered: Unregistered,
) -> Result<Vec<&'a Sort>, SortError> {
    Check::new(operation).definitions(sort, definitions, unregistered)
}

/// A conservative admission budget shared by all checks and folds in one call.
/// Nodes, scheduled edges, and inspected name bytes consume units. Individual
/// allocation/hash operations and destruction are not a wall-clock bound.
pub(super) const CHECK_LIMIT: usize = 32_768;

pub(super) struct Check {
    operation: &'static str,
    remaining: usize,
    refused: bool,
}

impl Check {
    pub(super) fn new(operation: &'static str) -> Self {
        Self {
            operation,
            remaining: CHECK_LIMIT,
            refused: false,
        }
    }

    pub(super) fn error(&self, actual: &'static str) -> SortError {
        SortError::Mismatch {
            operation: self.operation,
            expected: "bounded, unambiguous matching datatype signatures",
            actual: actual.to_owned(),
        }
    }

    /// Budget units still available in this attempt.
    #[cfg(test)]
    pub(super) fn remaining(&self) -> usize {
        self.remaining
    }

    pub(super) fn charge(&mut self, units: usize) -> Result<(), SortError> {
        if self.refused {
            return Err(self.error("datatype signature check budget exceeded"));
        }
        let Some(remaining) = self.remaining.checked_sub(units) else {
            self.refused = true;
            return Err(self.error("datatype signature check budget exceeded"));
        };
        self.remaining = remaining;
        Ok(())
    }

    pub(super) fn names_equal(&mut self, a: &str, b: &str) -> Result<bool, SortError> {
        self.charge(a.len())?;
        self.charge(b.len())?;
        Ok(a == b)
    }

    /// Authenticate names/ambiguity in this descriptor, not recursively in every
    /// field's datatype. Cross-constructor selector overloading is permitted.
    pub(super) fn datatype<'a>(
        &mut self,
        sort: &'a Sort,
        name: &str,
    ) -> Result<&'a DatatypeSort, SortError> {
        self.charge(1)?;
        let dt = sort
            .datatype_sort()
            .ok_or_else(|| self.error("receiver/result is not a datatype"))?;
        if !self.names_equal(&dt.name, name)? || dt.constructors.is_empty() {
            return Err(self.error("datatype name mismatch or empty constructor declaration"));
        }
        let mut constructors = HashSet::new();
        for ctor in &dt.constructors {
            self.charge(1)?;
            self.charge(ctor.name.len())?;
            if !constructors.insert(ctor.name.as_str()) {
                return Err(self.error("duplicate constructor name"));
            }
            let mut fields = HashSet::new();
            for field in &ctor.fields {
                self.charge(1)?;
                self.charge(field.name.len())?;
                if !fields.insert(field.name.as_str()) {
                    return Err(self.error("duplicate field name within a constructor"));
                }
            }
        }
        Ok(dt)
    }

    pub(super) fn constructor<'a>(
        &mut self,
        sort: &'a Sort,
        datatype_name: &str,
        constructor_name: &str,
        args: &[Expr],
    ) -> Result<&'a DatatypeConstructor, SortError> {
        let dt = self.datatype(sort, datatype_name)?;
        let ctor = self.named_constructor(dt, constructor_name)?;
        if ctor.fields.len() != args.len() {
            return Err(self.error("constructor argument count differs from its declaration"));
        }
        for (field, arg) in ctor.fields.iter().zip(args) {
            if !self.same_field_sort(sort, &field.sort, &arg.sort)? {
                return Err(self.error("recorded argument, branch, or result sort mismatch"));
            }
        }
        Ok(ctor)
    }

    pub(super) fn named_constructor<'a>(
        &mut self,
        dt: &'a DatatypeSort,
        name: &str,
    ) -> Result<&'a DatatypeConstructor, SortError> {
        for ctor in &dt.constructors {
            self.charge(1)?;
            if self.names_equal(&ctor.name, name)? {
                return Ok(ctor);
            }
        }
        Err(self.error("constructor is not declared in the datatype"))
    }

    /// Return the positional field index for a struct. An enum is authenticated
    /// by signature, but deliberately has no constant-folding index.
    pub(super) fn selector(
        &mut self,
        sort: &Sort,
        datatype_name: &str,
        selector_name: &str,
        result_sort: &Sort,
    ) -> Result<Option<usize>, SortError> {
        let dt = self.datatype(sort, datatype_name)?;
        let mut matched = None;
        for ctor in &dt.constructors {
            for (index, field) in ctor.fields.iter().enumerate() {
                self.charge(1)?;
                if self.names_equal(&field.name, selector_name)?
                    && self.same_field_sort(sort, &field.sort, result_sort)?
                {
                    matched = Some(index);
                }
            }
        }
        let index =
            matched.ok_or_else(|| self.error("selector/result signature is not declared"))?;
        Ok((dt.constructors.len() == 1).then_some(index))
    }

    pub(super) fn require_same_sort(&mut self, a: &Sort, b: &Sort) -> Result<(), SortError> {
        if !self.same_sort(a, b)? {
            return Err(self.error("recorded argument, branch, or result sort mismatch"));
        }
        Ok(())
    }

    /// Structural equality without recursive derived `Eq` or DAG re-walking.
    /// Pointer identity under one scope proves structural identity, not that
    /// the shared node is closed; it does not certify a schema. Both sorts
    /// stand outside any datatype declaration, so a
    /// [`SortInner::DatatypeRef`] that no datatype inside them encloses makes
    /// its sort unequal to everything, including itself.
    pub(super) fn same_sort(&mut self, a: &Sort, b: &Sort) -> Result<bool, SortError> {
        let mut scopes = Scopes::default();
        self.same_sort_in(&mut scopes, (a, None), (b, None))
    }

    /// Compare a field sort of the datatype declaration `declaration` against
    /// a sort that stands outside any declaration. A datatype reference in the
    /// field resolves to `declaration` (or to a datatype nested around it) and
    /// is then compared structurally, so `Datatype(N)` matches a ref to `N`
    /// only when it is that declaration; `Uninterpreted(N)` never does.
    fn same_field_sort(
        &mut self,
        declaration: &Sort,
        field: &Sort,
        other: &Sort,
    ) -> Result<bool, SortError> {
        let mut scopes = Scopes::default();
        let scope = scopes.enter(declaration, None)?;
        self.same_sort_in(&mut scopes, (field, Some(scope)), (other, None))
    }

    fn same_sort_in<'a>(
        &mut self,
        scopes: &mut Scopes<'a>,
        a: (&'a Sort, Option<usize>),
        b: (&'a Sort, Option<usize>),
    ) -> Result<bool, SortError> {
        let mut pending = vec![(a, b)];
        let mut seen = HashSet::new();
        self.charge(1)?;
        while let Some((a, b)) = pending.pop() {
            let Some((a, a_scope)) = self.resolve(scopes, a)? else {
                return Ok(false);
            };
            let Some((b, b_scope)) = self.resolve(scopes, b)? else {
                return Ok(false);
            };
            let a_sort = a;
            let b_sort = b;
            let a = a.inner();
            let b = b.inner();
            let key = (
                std::ptr::from_ref(a),
                a_scope,
                std::ptr::from_ref(b),
                b_scope,
            );
            if !seen.insert(key) {
                continue;
            }
            if std::ptr::eq(a, b) && a_scope == b_scope {
                // One node under one scope chain is structurally identical to
                // itself; it is the same sort only when it is closed there.
                if !self.closed_in(scopes, a_sort, a_scope)? {
                    return Ok(false);
                }
                continue;
            }
            match (a, b) {
                (SortInner::Bool, SortInner::Bool)
                | (SortInner::Int, SortInner::Int)
                | (SortInner::Real, SortInner::Real)
                | (SortInner::String, SortInner::String)
                | (SortInner::RegLan, SortInner::RegLan) => {}
                (SortInner::BitVec(a), SortInner::BitVec(b)) if a.width == b.width => {}
                (SortInner::FloatingPoint(a, b), SortInner::FloatingPoint(c, d))
                    if a == c && b == d => {}
                (SortInner::Uninterpreted(a), SortInner::Uninterpreted(b)) => {
                    if !self.names_equal(a, b)? {
                        return Ok(false);
                    }
                }
                (SortInner::Array(a), SortInner::Array(b)) => {
                    self.charge(2)?;
                    pending.push(((&a.element_sort, a_scope), (&b.element_sort, b_scope)));
                    pending.push(((&a.index_sort, a_scope), (&b.index_sort, b_scope)));
                }
                (SortInner::Seq(a), SortInner::Seq(b)) => {
                    self.charge(1)?;
                    pending.push(((a, a_scope), (b, b_scope)));
                }
                (SortInner::Datatype(a), SortInner::Datatype(b)) => {
                    let a_inner = scopes.enter(a_sort, a_scope)?;
                    let b_inner = scopes.enter(b_sort, b_scope)?;
                    if !self.enqueue_fields(a, b, (Some(a_inner), Some(b_inner)), &mut pending)? {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    /// Whether every datatype reference inside `sort`, read under `scope`,
    /// names an enclosing declaration. One unit per node.
    fn closed_in<'a>(
        &mut self,
        scopes: &mut Scopes<'a>,
        sort: &'a Sort,
        scope: Option<usize>,
    ) -> Result<bool, SortError> {
        let mut pending = vec![(sort, scope)];
        let mut seen = HashSet::new();
        while let Some((sort, scope)) = pending.pop() {
            self.charge(1)?;
            if !seen.insert((std::ptr::from_ref(sort.inner()), scope)) {
                continue;
            }
            match sort.inner() {
                SortInner::DatatypeRef(_) => {
                    if self.resolve(scopes, (sort, scope))?.is_none() {
                        return Ok(false);
                    }
                }
                SortInner::Datatype(dt) => {
                    let inner = scopes.enter(sort, scope)?;
                    for field in dt.constructors.iter().flat_map(|ctor| &ctor.fields) {
                        pending.push((&field.sort, Some(inner)));
                    }
                }
                SortInner::Array(array) => {
                    pending.push((&array.element_sort, scope));
                    pending.push((&array.index_sort, scope));
                }
                SortInner::Seq(element) => pending.push((element, scope)),
                _ => {}
            }
        }
        Ok(true)
    }

    /// The nearest scope in the chain starting at `scope` whose declaration
    /// is named `name`.
    fn enclosing(
        &mut self,
        scopes: &Scopes<'_>,
        scope: Option<usize>,
        name: &str,
    ) -> Result<Option<usize>, SortError> {
        let mut cursor = scope;
        while let Some(id) = cursor {
            self.charge(1)?;
            if self.names_equal(scopes.nodes[id].name, name)? {
                return Ok(Some(id));
            }
            cursor = scopes.nodes[id].parent;
        }
        Ok(None)
    }

    /// Whether the datatype node `sort`, read under `scope`, is the closed
    /// definition `definition`. A shared node is that definition outright:
    /// a closed definition means the same datatype under every scope.
    fn same_definition<'a>(
        &mut self,
        scopes: &mut Scopes<'a>,
        (sort, scope): (&'a Sort, Option<usize>),
        definition: &'a Sort,
    ) -> Result<bool, SortError> {
        if std::ptr::eq(sort.inner(), definition.inner()) {
            return Ok(true);
        }
        self.same_sort_in(scopes, (sort, scope), (definition, None))
    }

    /// See [`authenticate_definitions`].
    fn definitions<'a>(
        &mut self,
        sort: &'a Sort,
        definitions: &'a Definitions,
        unregistered: Unregistered,
    ) -> Result<Vec<&'a Sort>, SortError> {
        enum Step<'a> {
            Visit(&'a Sort, Option<usize>),
            Collect(&'a Sort),
        }
        let root = sort.datatype_sort().map(|dt| dt.name.as_str());
        let mut scopes = Scopes::default();
        let mut collected: Vec<&'a Sort> = Vec::new();
        let mut pending: HashMap<&'a str, &'a Sort> = HashMap::new();
        let mut seen = HashSet::new();
        let mut stack = vec![Step::Visit(sort, None)];
        while let Some(step) = stack.pop() {
            let (sort, scope) = match step {
                Step::Collect(sort) => {
                    if let Some(dt) = sort.datatype_sort() {
                        pending.insert(dt.name.as_str(), sort);
                    }
                    collected.push(sort);
                    continue;
                }
                Step::Visit(sort, scope) => (sort, scope),
            };
            self.charge(1)?;
            if !seen.insert((std::ptr::from_ref(sort.inner()), scope)) {
                continue;
            }
            let outer = scope.map(|id| scopes.nodes[id].name);
            match sort.inner() {
                SortInner::DatatypeRef(name) => {
                    if self.resolve(&scopes, (sort, scope))?.is_none() {
                        return Err(self.definition_error(match outer {
                            Some(outer) => format!(
                                "datatype reference `{name}` in the declaration of `{outer}` \
                                 names no enclosing datatype"
                            ),
                            None => format!(
                                "datatype reference `{name}` outside any declaration of `{name}`"
                            ),
                        }));
                    }
                }
                SortInner::Datatype(dt) => {
                    let name = dt.name.as_str();
                    self.datatype(sort, name)?;
                    if let Some(id) = self.enclosing(&scopes, scope, name)? {
                        let (declaration, parent) =
                            (scopes.nodes[id].declaration, scopes.nodes[id].parent);
                        if !self.same_sort_in(&mut scopes, (sort, scope), (declaration, parent))? {
                            return Err(self.definition_error(format!(
                                "conflicting datatype definitions under one name: `{name}` \
                                 nested inside `{name}` differs from the enclosing definition"
                            )));
                        }
                        continue;
                    }
                    if let Some(definition) = definitions.get(name) {
                        if !self.same_definition(&mut scopes, (sort, scope), definition)? {
                            return Err(self.definition_error(match outer {
                                Some(outer) => format!(
                                    "conflicting datatype definitions under one name: `{name}` \
                                     (nested inside `{outer}`) differs from the declared `{name}`"
                                ),
                                None => format!(
                                    "conflicting datatype definitions under one name: `{name}`"
                                ),
                            }));
                        }
                        continue;
                    }
                    if let Some(&definition) = pending.get(name) {
                        if !self.same_definition(&mut scopes, (sort, scope), definition)? {
                            return Err(self.definition_error(format!(
                                "conflicting datatype definitions under one name: `{name}` \
                                 is defined twice inside `{}`",
                                root.unwrap_or(name)
                            )));
                        }
                        continue;
                    }
                    if scope.is_some() && unregistered == Unregistered::Refuse {
                        return Err(self.definition_error(format!(
                            "datatype `{name}` (nested inside `{}`) is not declared; \
                             declare `{name}` first",
                            outer.unwrap_or(name)
                        )));
                    }
                    if let Some(reference) = sort.dangling_datatype_ref() {
                        return Err(self.definition_error(match outer {
                            Some(outer) => format!(
                                "datatype `{name}` nested inside `{outer}` refers to `{reference}` \
                                 outside itself: mutual recursion between separately declared \
                                 datatypes is not supported"
                            ),
                            None => format!(
                                "datatype reference `{reference}` in the declaration of `{name}` \
                                 names no enclosing datatype"
                            ),
                        }));
                    }
                    let inner = scopes.enter(sort, scope)?;
                    stack.push(Step::Collect(sort));
                    for field in dt.constructors.iter().flat_map(|ctor| &ctor.fields) {
                        stack.push(Step::Visit(&field.sort, Some(inner)));
                    }
                }
                SortInner::Array(array) => {
                    stack.push(Step::Visit(&array.element_sort, scope));
                    stack.push(Step::Visit(&array.index_sort, scope));
                }
                SortInner::Seq(element) => stack.push(Step::Visit(element, scope)),
                _ => {}
            }
        }
        Ok(collected)
    }

    fn definition_error(&self, actual: String) -> SortError {
        SortError::Mismatch {
            operation: self.operation,
            expected: "one closed datatype definition per name",
            actual,
        }
    }

    /// Replace a datatype reference by the enclosing declaration it names,
    /// together with that declaration's own enclosing scope. `None` when no
    /// enclosing declaration has the name.
    #[allow(clippy::type_complexity)]
    fn resolve<'a>(
        &mut self,
        scopes: &Scopes<'a>,
        (sort, scope): (&'a Sort, Option<usize>),
    ) -> Result<Option<(&'a Sort, Option<usize>)>, SortError> {
        let SortInner::DatatypeRef(name) = sort.inner() else {
            return Ok(Some((sort, scope)));
        };
        let mut cursor = scope;
        while let Some(id) = cursor {
            self.charge(1)?;
            let node = &scopes.nodes[id];
            if self.names_equal(node.name, name)? {
                return Ok(Some((node.declaration, node.parent)));
            }
            cursor = node.parent;
        }
        Ok(None)
    }

    #[allow(clippy::type_complexity)]
    fn enqueue_fields<'a>(
        &mut self,
        a: &'a DatatypeSort,
        b: &'a DatatypeSort,
        (a_scope, b_scope): (Option<usize>, Option<usize>),
        pending: &mut Vec<((&'a Sort, Option<usize>), (&'a Sort, Option<usize>))>,
    ) -> Result<bool, SortError> {
        if !self.names_equal(&a.name, &b.name)? || a.constructors.len() != b.constructors.len() {
            return Ok(false);
        }
        for (a, b) in a.constructors.iter().zip(&b.constructors) {
            self.charge(1)?;
            if !self.names_equal(&a.name, &b.name)? || a.fields.len() != b.fields.len() {
                return Ok(false);
            }
            for (a, b) in a.fields.iter().zip(&b.fields) {
                self.charge(1)?;
                if !self.names_equal(&a.name, &b.name)? {
                    return Ok(false);
                }
                pending.push(((&a.sort, a_scope), (&b.sort, b_scope)));
            }
        }
        Ok(true)
    }
}

/// An enclosing datatype declaration against which a datatype reference
/// resolves.
struct ScopeNode<'a> {
    declaration: &'a Sort,
    name: &'a str,
    parent: Option<usize>,
}

/// Scope chains interned by (declaration node, parent scope): re-entering a
/// declaration through one of its own references yields the same scope, so
/// the `seen` pairs repeat and a recursive comparison terminates.
#[derive(Default)]
struct Scopes<'a> {
    nodes: Vec<ScopeNode<'a>>,
    interned: HashMap<(*const SortInner, Option<usize>), usize>,
}

impl<'a> Scopes<'a> {
    fn enter(&mut self, declaration: &'a Sort, parent: Option<usize>) -> Result<usize, SortError> {
        let SortInner::Datatype(dt) = declaration.inner() else {
            return Err(SortError::Mismatch {
                operation: "datatype_scope",
                expected: "a datatype declaration",
                actual: "a non-datatype sort".to_owned(),
            });
        };
        let key = (std::ptr::from_ref(declaration.inner()), parent);
        if let Some(&id) = self.interned.get(&key) {
            return Ok(id);
        }
        self.nodes.push(ScopeNode {
            declaration,
            name: &dt.name,
            parent,
        });
        let id = self.nodes.len() - 1;
        self.interned.insert(key, id);
        Ok(id)
    }
}
