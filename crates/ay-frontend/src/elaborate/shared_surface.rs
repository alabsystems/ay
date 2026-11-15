// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Attempt-scoped sharing of exact closed source through the ordinary elaborator.

use std::cell::Cell;
use std::marker::PhantomData;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{Sort, TermId};

use crate::command::{Constant, ParsedSort, Term};

use super::{Context, ElaborateError, SourceContextStamp};

/// Resource envelope for one exact-source elaboration attempt.
#[derive(Clone, Copy, Debug)]
pub struct SharedSurfaceLimits {
    /// Maximum number of exactly distinct source subtrees.
    pub distinct_nodes: usize,
    /// Maximum input nesting depth, with the root at zero.
    pub depth: usize,
    /// Maximum source visits in each traversal/elaboration phase.
    pub node_visits: usize,
    /// Maximum inspected source-token bytes in each phase.
    pub token_visits: usize,
}

// Constant-size policy identity. Option commands already advance the private
// elaboration revision, including inert/same-value/alias writes; never compare
// or clone their arbitrarily large scalar payloads at a source-node lookup.
#[derive(Clone, Copy, Eq, PartialEq)]
struct Policy {
    flags: [bool; 7],
    compliant_at_start: Option<bool>,
}

impl Policy {
    fn of(context: &Context) -> Self {
        Self {
            flags: [
                context.numeral_as_real,
                context.int_real_coercions,
                context.strict_logic_compliance,
                context.enforce_logic_sort_signatures,
                context.z3_mode,
                context.lenient_sort_coercions,
                context.multivar_lambda_curry_allowed,
            ],
            compliant_at_start: context.z3_smtlib2_compliant_at_start,
        }
    }
}

fn outside_command_window(context: &Context) -> bool {
    context.skip_journal.is_none() && context.label_journal.is_none()
}

/// Canonical results for one immutable source tree and source/term universe.
///
/// This is a provenance lookup, not proof or assertion authority. Canonical
/// equality never establishes source equality. The source borrow prevents its
/// addresses from being reused while this batch exists; context and arena
/// checks additionally retire it after declarations, pop/reset, rollback,
/// replacement, fresh allocation or checker-visible metadata changes.
pub struct SharedSurfaceElaboration<'source> {
    locations: HashMap<usize, usize>,
    canonical: Vec<TermId>,
    context: SourceContextStamp,
    elaboration_revision: u64,
    policy: Policy,
    terms: TermStoreSnapshotStamp,
    metadata: u64,
    fresh: u32,
    reads_array: bool,
    marker: PhantomData<&'source Term>,
}

impl SharedSurfaceElaboration<'_> {
    fn current(&self, context: &Context) -> bool {
        context.shared_surface.0.is_none()
            && outside_command_window(context)
            && self.policy == Policy::of(context)
            && self.context == context.source_context_stamp()
            && self.elaboration_revision == context.elaboration_revision
            && self.terms.is_append_only_prefix_of(&context.terms)
            && self.metadata == context.terms.checker_visible_metadata_generation()
            && self.fresh == context.terms.var_counter()
    }

    /// Number of exactly distinct source subtrees, including leaves.
    pub fn len(&self) -> usize {
        self.canonical.len()
    }

    /// Whether the batch contains no source nodes.
    pub fn is_empty(&self) -> bool {
        self.canonical.is_empty()
    }

    /// Whether the actual source contains a `select` application.
    pub fn reads_array(&self) -> bool {
        self.reads_array
    }

    /// Exact-source node identity, only while the originating context is live.
    pub fn node_index(&self, context: &Context, source: &Term) -> Option<usize> {
        self.current(context).then_some(())?;
        self.locations
            .get(&(source as *const Term as usize))
            .copied()
    }

    /// Result obtained by the ordinary elaborator for this exact source node.
    pub fn canonical(&self, context: &Context, source: &Term) -> Option<TermId> {
        self.canonical
            .get(self.node_index(context, source)?)
            .copied()
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
enum Head {
    Symbol(String),
    Bool(bool),
    Binary(String),
    Hexadecimal(String),
    App(String),
    Indexed(String, Vec<String>),
    ConstArray(String, String),
}

#[derive(Eq, Hash, PartialEq)]
struct Key(Head, Vec<usize>);

#[derive(Clone, Copy, Default)]
struct Work {
    nodes: usize,
    tokens: usize,
    failed: bool,
}

struct Active {
    locations: HashMap<usize, usize>,
    canonical: Vec<Option<TermId>>,
    local: Vec<usize>,
    context: SourceContextStamp,
    elaboration_revision: u64,
    policy: Policy,
    terms: TermStoreSnapshotStamp,
    metadata: u64,
    fresh: u32,
    limits: SharedSurfaceLimits,
    work: Cell<Work>,
}

impl Active {
    fn current(&self, context: &Context) -> bool {
        outside_command_window(context)
            && self.policy == Policy::of(context)
            && self.context == context.source_context_stamp()
            && self.elaboration_revision == context.elaboration_revision
            && self.terms.is_append_only_prefix_of(&context.terms)
            && self.metadata == context.terms.checker_visible_metadata_generation()
            && self.fresh == context.terms.var_counter()
            && !self.work.get().failed
    }

    fn charge(&self, nodes: usize, tokens: usize) -> bool {
        let old = self.work.get();
        let next = old
            .nodes
            .checked_add(nodes)
            .zip(old.tokens.checked_add(tokens));
        let Some((nodes, tokens)) = next else {
            self.work.set(Work {
                failed: true,
                ..old
            });
            return false;
        };
        let failed =
            old.failed || nodes > self.limits.node_visits || tokens > self.limits.token_visits;
        self.work.set(Work {
            nodes,
            tokens,
            failed,
        });
        !failed
    }
}

/// A cloned Context never inherits a live attempt or its source addresses.
#[derive(Default)]
pub(super) struct Slot(Option<Active>);

impl Clone for Slot {
    fn clone(&self) -> Self {
        Self::default()
    }
}

#[derive(Clone, Copy)]
pub(super) enum Lookup {
    Inactive,
    Hit(TermId),
    Miss(usize),
}

fn refused() -> ElaborateError {
    ElaborateError::Unsupported("shared source elaboration left its exact bounded context".into())
}

impl Context {
    /// Elaborate a closed source DAG using the existing recursive dispatcher.
    ///
    /// Only exact source syntax shares work. Definitions, adopted macros,
    /// binders, lets and annotations are refused before activation. Every
    /// successful head retains ordinary declaration/type checking, including
    /// skipped-branch validation. Failure returns no reusable partial batch.
    pub fn elaborate_shared_surface<'source>(
        &mut self,
        source: &'source Term,
        limits: SharedSurfaceLimits,
        stopped: impl FnMut(&Context) -> bool,
    ) -> Option<SharedSurfaceElaboration<'source>> {
        self.elaborate_shared_surface_with_array_requirement(source, limits, stopped, false)
    }

    /// As `elaborate_shared_surface`, but require a source `select` occurrence
    /// before activating ordinary elaboration in the live context. A caller
    /// declining non-read source must not populate untaken array branches just
    /// to discover that it has no read to reconstruct.
    ///
    /// The existing bounded syntax builder computes this descriptor once. The
    /// requirement grants no proof/assertion authority and changes no limits.
    pub fn elaborate_shared_surface_reading_array<'source>(
        &mut self,
        source: &'source Term,
        limits: SharedSurfaceLimits,
        stopped: impl FnMut(&Context) -> bool,
    ) -> Option<SharedSurfaceElaboration<'source>> {
        self.elaborate_shared_surface_with_array_requirement(source, limits, stopped, true)
    }

    fn elaborate_shared_surface_with_array_requirement<'source>(
        &mut self,
        source: &'source Term,
        limits: SharedSurfaceLimits,
        mut stopped: impl FnMut(&Context) -> bool,
        require_array_read: bool,
    ) -> Option<SharedSurfaceElaboration<'source>> {
        if self.shared_surface.0.is_some() || !outside_command_window(self) || stopped(self) {
            return None;
        }
        let mut builder = Builder::new(self, limits);
        builder.visit(source, 0, &mut stopped)?;
        let Builder {
            locations,
            representatives,
            local,
            reads_array,
            ..
        } = builder;
        // Retain the syntax-only decline before installing the active slot or
        // creating ANY canonical subterm (including a dead ITE branch).
        if require_array_read && !reads_array {
            return None;
        }
        let count = representatives.len();
        self.shared_surface.0 = Some(Active {
            locations,
            canonical: vec![None; count],
            local,
            context: self.source_context_stamp(),
            elaboration_revision: self.elaboration_revision,
            policy: Policy::of(self),
            terms: self.terms.snapshot_stamp(),
            metadata: self.terms.checker_visible_metadata_generation(),
            fresh: self.terms.var_counter(),
            limits,
            work: Cell::new(Work::default()),
        });
        // The guard retires the temporary pointer index on errors and unwinds.
        struct Guard<'a>(&'a mut Context);
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                self.0.shared_surface.0 = None;
            }
        }
        let guard = Guard(self);
        // Children precede parents. Each ordinary dispatch sees already checked
        // canonical children; no typed application or source placeholder is built
        // by this owner. Syntax-sensitive paths still run in the dispatcher.
        for representative in representatives {
            if stopped(guard.0) {
                return None;
            }
            let _ = guard.0.elaborate_surface_subterm(representative)?;
        }
        if stopped(guard.0) || !guard.0.shared_surface.0.as_ref()?.current(guard.0) {
            return None;
        }
        let active = guard.0.shared_surface.0.take()?;
        let canonical = active.canonical.into_iter().collect::<Option<Vec<_>>>()?;
        Some(SharedSurfaceElaboration {
            locations: active.locations,
            canonical,
            context: active.context,
            elaboration_revision: active.elaboration_revision,
            policy: active.policy,
            terms: guard.0.terms.snapshot_stamp(),
            metadata: active.metadata,
            fresh: active.fresh,
            reads_array,
            marker: PhantomData,
        })
    }

    pub(super) fn shared_surface_lookup(
        &self,
        source: &Term,
        closed: bool,
    ) -> Result<Lookup, ElaborateError> {
        let Some(active) = self.shared_surface.0.as_ref() else {
            return Ok(Lookup::Inactive);
        };
        if !closed || !active.current(self) || !active.charge(1, 0) {
            return Err(refused());
        }
        let Some(&index) = active.locations.get(&(source as *const Term as usize)) else {
            // A syntax-sensitive helper may create a different temporary AST.
            // It cannot borrow an original node's authority or escape metering.
            return Err(refused());
        };
        if let Some(term) = active.canonical[index] {
            return Ok(Lookup::Hit(term));
        }
        if !active.charge(0, active.local[index]) {
            return Err(refused());
        }
        Ok(Lookup::Miss(index))
    }

    pub(super) fn shared_surface_record(
        &mut self,
        index: usize,
        term: TermId,
    ) -> Result<(), ElaborateError> {
        let current = self
            .shared_surface
            .0
            .as_ref()
            .is_some_and(|active| active.current(self));
        if !current {
            return Err(refused());
        }
        let active = self.shared_surface.0.as_mut().ok_or_else(refused)?;
        let slot = active.canonical.get_mut(index).ok_or_else(refused)?;
        *slot = Some(term);
        Ok(())
    }

    /// The skipped branch was independently checked by the ordinary dispatcher
    /// before its parent. Reuse that exact-source result here; this avoids the
    /// label/name/type scans and scratch clone, while the existing ITE join
    /// still checks the two branch sorts. The admitted grammar has no labels,
    /// binders or definitions whose skipped-source side effects matter.
    pub(super) fn shared_surface_skipped_sort(
        &self,
        source: &Term,
    ) -> Result<Option<Sort>, ElaborateError> {
        match self.shared_surface_lookup(source, true)? {
            Lookup::Inactive => Ok(None),
            Lookup::Hit(term) => Ok(Some(self.terms.sort(term).clone())),
            Lookup::Miss(_) => Err(refused()),
        }
    }

    pub(super) fn shared_connective_scan(&self, name: &str, args: &[Term]) -> bool {
        let Some(active) = self.shared_surface.0.as_ref() else {
            return true;
        };
        let mut pending: Vec<_> = args.iter().collect();
        while let Some(source) = pending.pop() {
            let tokens = if let Term::App(head, _) = source {
                head.len()
            } else {
                0
            };
            // This metering pass plus the existing gatherer's source/edge walks.
            if !active.charge(8, tokens.saturating_mul(8)) {
                return false;
            }
            if let Term::App(head, children) = source {
                if head == name {
                    pending.extend(children);
                }
            }
        }
        true
    }
}

struct Builder<'context, 'source> {
    context: &'context Context,
    limits: SharedSurfaceLimits,
    keys: HashMap<Key, usize>,
    locations: HashMap<usize, usize>,
    representatives: Vec<&'source Term>,
    local: Vec<usize>,
    input: Work,
    reads_array: bool,
}

impl<'context, 'source> Builder<'context, 'source> {
    fn new(context: &'context Context, limits: SharedSurfaceLimits) -> Self {
        Self {
            context,
            limits,
            keys: HashMap::default(),
            locations: HashMap::default(),
            representatives: Vec::new(),
            local: Vec::new(),
            input: Work::default(),
            reads_array: false,
        }
    }

    fn visit(
        &mut self,
        source: &'source Term,
        depth: usize,
        stopped: &mut impl FnMut(&Context) -> bool,
    ) -> Option<(usize, usize, usize)> {
        if self.input.nodes.is_multiple_of(1024) && stopped(self.context) {
            return None;
        }
        self.input.nodes = self.input.nodes.checked_add(1)?;
        if self.input.nodes > self.limits.node_visits || depth > self.limits.depth {
            return None;
        }
        let (head, local, children) = shape(source, self.context)?;
        self.input.tokens = self.input.tokens.checked_add(local)?;
        if self.input.tokens > self.limits.token_visits {
            return None;
        }
        self.reads_array |= matches!(source, Term::App(name, _) if name == "select");
        let (mut nodes, mut tokens) = (1usize, local);
        let mut ids = Vec::with_capacity(children.len());
        for child in children {
            let (id, child_nodes, child_tokens) = self.visit(child, depth + 1, stopped)?;
            ids.push(id);
            nodes = nodes.checked_add(child_nodes)?;
            tokens = tokens.checked_add(child_tokens)?;
        }
        let key = Key(head, ids);
        let index = if let Some(&index) = self.keys.get(&key) {
            index
        } else {
            if self.keys.len() >= self.limits.distinct_nodes {
                return None;
            }
            let index = self.keys.len();
            self.keys.insert(key, index);
            self.representatives.push(source);
            self.local.push(local);
            index
        };
        let pointer = source as *const Term as usize;
        self.locations.insert(pointer, index);
        Some((index, nodes, tokens))
    }
}

fn shape<'source>(
    source: &'source Term,
    context: &Context,
) -> Option<(Head, usize, &'source [Term])> {
    let macro_name = match source {
        Term::Symbol(name) if name.len() <= 4096 => Some(name.as_str()),
        Term::App(name, _) if name.len() <= 64 => Some(name.as_str()),
        Term::QualifiedApp(identifier, _, _) if identifier.as_symbol() == Some("const") => {
            Some("const")
        }
        _ => None,
    };
    if macro_name.is_some_and(|name| {
        context.is_defined_fun(name) || context.adopted_macro_interp(name).is_some()
    }) {
        return None;
    }
    Some(match source {
        Term::Symbol(name) if name.len() <= 4096 => (Head::Symbol(name.clone()), name.len(), &[]),
        Term::Const(Constant::True) => (Head::Bool(true), 5, &[]),
        Term::Const(Constant::False) => (Head::Bool(false), 5, &[]),
        Term::Const(Constant::Binary(text)) if text.len() <= 130 => {
            (Head::Binary(text.clone()), text.len(), &[])
        }
        Term::Const(Constant::Hexadecimal(text)) if text.len() <= 130 => {
            (Head::Hexadecimal(text.clone()), text.len(), &[])
        }
        Term::App(name, args) if name.len() <= 64 && args.len() <= 128 => (
            Head::App(name.clone()),
            name.len().checked_add(args.len())?.checked_add(2)?,
            args,
        ),
        Term::IndexedApp(name, indices, args)
            if name.len() <= 64 && indices.len() <= 2 && args.len() <= 1 =>
        {
            let indices = indices
                .iter()
                .map(|i| i.as_numeral().filter(|n| n.len() <= 3).map(str::to_owned))
                .collect::<Option<Vec<_>>>()?;
            let bytes = indices
                .iter()
                .try_fold(name.len().checked_add(8)?, |sum, index| {
                    sum.checked_add(index.len().checked_add(1)?)
                })?;
            (Head::Indexed(name.clone(), indices), bytes, args)
        }
        Term::QualifiedApp(identifier, ParsedSort::Parameterized(array, sorts), args)
            if identifier.as_symbol() == Some("const")
                && args.len() == 1
                && array == "Array"
                && sorts.len() == 2 =>
        {
            let widths = sorts
                .iter()
                .map(|sort| {
                    let ParsedSort::Indexed(name, indices) = sort else {
                        return None;
                    };
                    if name != "BitVec" || indices.len() != 1 {
                        return None;
                    }
                    let value = indices[0].as_numeral()?;
                    (value.len() <= 3 && value.parse::<u32>().is_ok_and(|n| (1..=128).contains(&n)))
                        .then(|| value.to_owned())
                })
                .collect::<Option<Vec<_>>>()?;
            (
                Head::ConstArray(widths[0].clone(), widths[1].clone()),
                64,
                args,
            )
        }
        _ => return None,
    })
}

#[cfg(test)]
#[path = "shared_surface_tests.rs"]
mod tests;
