// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope-stable source identity for checked quantified-model certificates.
//!
//! Core applications currently retain only [`Symbol`] spellings.  A spelling
//! is not enough to distinguish an ordinary uninterpreted declaration from a
//! built-in, definition, datatype member, or solver-internal symbol.  This
//! module supplies the independent, positive frontend half of that proof.  It
//! deliberately does not grant SAT authority by itself.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermData, TermId};

use super::{Context, SymbolInfo};

/// Maximum number of distinct reachable terms accepted by the source-binding
/// checker.
const MAX_PROJECTION_BINDING_TERMS: usize = 10_000_000;
/// Small post-solve consumers may request a hard preflight before invoking
/// declaration checks whose legacy lookup walks the live signature table.
const MAX_BOUNDED_PROJECTION_DECLARATIONS: usize = 16_384;
const MAX_BOUNDED_PROJECTION_IDENTITY_BYTES: usize = 256;

/// Opaque, stable identity of one source declaration.
///
/// Cloning this value preserves the declaration identity.  Fresh declarations
/// always receive a fresh allocation, so a scoped declaration that is popped
/// and later redeclared cannot alias its predecessor even when its spelling and
/// signature are identical.
#[derive(Clone)]
pub struct DeclarationId(Arc<DeclarationMarker>);

#[derive(Debug)]
struct DeclarationMarker;

impl DeclarationId {
    pub(super) fn fresh() -> Self {
        Self(Arc::new(DeclarationMarker))
    }
}

impl PartialEq for DeclarationId {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for DeclarationId {}

impl Hash for DeclarationId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Arc::as_ptr(&self.0), state);
    }
}

impl fmt::Debug for DeclarationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("DeclarationId(<opaque>)")
    }
}

/// Positive semantic classification of a declared symbol.
///
/// Projection certificates may select only [`Self::Uninterpreted`].  Every
/// other variant has semantics fixed somewhere outside a free total-function
/// interpretation and must therefore be rejected by the binding checker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DeclarationKind {
    /// An ordinary free constant or total uninterpreted function.
    Uninterpreted,
    /// A problem-level `define-fun`, `define-fun-rec`, or `define-funs-rec`.
    Defined,
    /// A declared function currently adopted as a definitional macro.
    AdoptedDefinition,
    /// A datatype constructor.
    DatatypeConstructor,
    /// A datatype selector.
    DatatypeSelector,
    /// A datatype tester.
    DatatypeTester,
    /// A declaration-activated or otherwise theory-interpreted symbol.
    Theory,
    /// A symbol introduced for solver implementation purposes.
    SolverInternal,
}

/// Identity of one independently mutable frontend context.
///
/// `Clone` intentionally mints a new identity.  [`Context`] derives `Clone` for
/// independent re-discharge, but evidence created for the original context may
/// never authorize its clone merely because their initial term stores match.
#[derive(Debug)]
pub(super) struct ContextIdentity(Arc<ContextMarker>);

#[derive(Debug)]
struct ContextMarker;

impl ContextIdentity {
    pub(super) fn fresh() -> Self {
        Self(Arc::new(ContextMarker))
    }

    pub(super) fn stamp(&self, revision: u64) -> SourceContextStamp {
        SourceContextStamp {
            identity: Arc::clone(&self.0),
            revision,
        }
    }
}

impl Clone for ContextIdentity {
    fn clone(&self) -> Self {
        Self::fresh()
    }
}

/// Opaque snapshot of a frontend context and its source-binding revision.
///
/// The fields are private so downstream candidate producers cannot fabricate a
/// matching scope epoch.  Cloning a stamp preserves the captured snapshot; it
/// does not mint a new context identity.
#[derive(Clone)]
pub struct SourceContextStamp {
    identity: Arc<ContextMarker>,
    revision: u64,
}

impl PartialEq for SourceContextStamp {
    fn eq(&self, other: &Self) -> bool {
        self.revision == other.revision && Arc::ptr_eq(&self.identity, &other.identity)
    }
}

impl Eq for SourceContextStamp {}

impl Hash for SourceContextStamp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Arc::as_ptr(&self.identity), state);
        self.revision.hash(state);
    }
}

impl fmt::Debug for SourceContextStamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SourceContextStamp")
            .field("identity", &"<opaque>")
            .field("revision", &self.revision)
            .finish()
    }
}

impl SourceContextStamp {
    /// Whether two stamps belong to the same independently mutable frontend
    /// context, ignoring their source revisions.
    ///
    /// Declaration handles use this narrower comparison so unrelated later
    /// declarations do not invalidate a still-live handle, while a cloned or
    /// reset context can never authenticate an identity minted elsewhere.
    #[must_use]
    pub fn is_same_context(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.identity, &other.identity)
    }
}

/// Untrusted request to bind one core application head to an ordinary free
/// frontend declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectionBindingRequest {
    /// Exact core symbol used by every selected application.
    pub symbol: Symbol,
    /// Complete parameter signature, in application order.
    pub parameter_sorts: Vec<Sort>,
    /// Declared result sort.
    pub result_sort: Sort,
}

/// One positively checked free-function declaration binding.
///
/// Fields are private; values can only be obtained through
/// [`Context::check_projection_bindings`].
#[derive(Debug)]
pub struct CheckedProjectionBinding {
    stamp: SourceContextStamp,
    symbol: Symbol,
    declaration_id: DeclarationId,
    parameter_sorts: Vec<Sort>,
    result_sort: Sort,
}

impl CheckedProjectionBinding {
    /// Context/scope stamp captured by the declaration checker.
    #[must_use]
    pub fn source_context_stamp(&self) -> &SourceContextStamp {
        &self.stamp
    }

    /// Exact checked core symbol.
    #[must_use]
    pub fn symbol(&self) -> &Symbol {
        &self.symbol
    }

    /// Stable identity of the live source declaration.
    #[must_use]
    pub fn declaration_id(&self) -> &DeclarationId {
        &self.declaration_id
    }

    /// Complete checked parameter signature.
    #[must_use]
    pub fn parameter_sorts(&self) -> &[Sort] {
        &self.parameter_sorts
    }

    /// Checked result sort.
    #[must_use]
    pub fn result_sort(&self) -> &Sort {
        &self.result_sort
    }
}

/// Opaque evidence that every requested projection head is an exact, live,
/// ordinary uninterpreted-function declaration in one frozen source context.
///
/// This type intentionally does not implement `Clone`.  It is only the source
/// half of quantified-SAT authority and must be combined with independently
/// checked projection semantics and an authored-query permit.
#[derive(Debug)]
pub struct CheckedProjectionBindings {
    stamp: SourceContextStamp,
    roots: Vec<TermId>,
    checked_term_count: usize,
    frozen_terms: Vec<FrozenTerm>,
    bindings: Vec<CheckedProjectionBinding>,
}

#[derive(Debug)]
struct FrozenTerm {
    id: TermId,
    data: TermData,
    sort: Sort,
}

impl CheckedProjectionBindings {
    /// Context/scope stamp captured by the checker.
    #[must_use]
    pub fn source_context_stamp(&self) -> &SourceContextStamp {
        &self.stamp
    }

    /// Exact ordered root vector bound to this evidence.
    pub fn roots(&self) -> &[TermId] {
        &self.roots
    }

    /// Term-store length when the evidence was checked.
    ///
    /// This is lifecycle metadata, not a digest; currentness is established by
    /// the complete frozen reachable-term comparison.
    #[must_use]
    pub fn checked_term_count(&self) -> usize {
        self.checked_term_count
    }

    /// Positively checked declaration bindings in request order.
    #[must_use]
    pub fn bindings(&self) -> &[CheckedProjectionBinding] {
        &self.bindings
    }
}

/// Typed, fail-closed rejection from the positive source-binding checker.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ProjectionBindingRejection {
    /// A root or reachable child does not exist in the supplied term store.
    #[error("projection source binding references invalid term {term:?}")]
    InvalidTermId {
        /// Invalid term identifier.
        term: TermId,
    },
    /// A request used an indexed or future core symbol variant.
    #[error("projection source binding does not support symbol {symbol:?}")]
    UnsupportedSymbol {
        /// Unsupported symbol.
        symbol: Symbol,
    },
    /// Two requests selected the same core symbol.
    #[error("projection source binding contains duplicate request for {symbol:?}")]
    DuplicateRequest {
        /// Repeated symbol.
        symbol: Symbol,
    },
    /// No live frontend declaration has the selected core identity.
    #[error("projection symbol {symbol:?} has no live source declaration")]
    UnknownDeclaration {
        /// Unbound core symbol.
        symbol: Symbol,
    },
    /// More than one live binding has the selected core identity.
    #[error("projection symbol {symbol:?} has an ambiguous source declaration")]
    AmbiguousDeclaration {
        /// Ambiguous core symbol.
        symbol: Symbol,
    },
    /// The binding is an overload, alias, or solver-internal surface binding.
    #[error("projection symbol {symbol:?} is not an ordinary primary declaration")]
    NonOrdinaryBinding {
        /// Ineligible core symbol.
        symbol: Symbol,
    },
    /// The selected declaration is not a free uninterpreted function.
    #[error("projection symbol {symbol:?} has ineligible declaration kind {kind:?}")]
    NonFreeDeclaration {
        /// Ineligible core symbol.
        symbol: Symbol,
        /// Positive effective declaration kind.
        kind: DeclarationKind,
    },
    /// A selected declaration or occurrence has a different complete signature.
    #[error("projection symbol {symbol:?} does not match its requested signature")]
    SignatureMismatch {
        /// Mismatched core symbol.
        symbol: Symbol,
    },
    /// A live function declaration occurred without a corresponding request.
    #[error("live declaration {symbol:?} occurs outside the projection binding requests")]
    UnselectedDeclarationOccurrence {
        /// Unselected application head.
        symbol: Symbol,
    },
    /// A requested function did not occur in the frozen roots.
    #[error("projection binding request for {symbol:?} is unused")]
    UnusedRequest {
        /// Unused requested symbol.
        symbol: Symbol,
    },
    /// A future core term variant is outside this checker's audited fragment.
    #[error("projection source binding encountered unsupported term {term:?}")]
    UnsupportedTermNode {
        /// Unsupported reachable term.
        term: TermId,
    },
    /// The bounded checker exhausted its work allowance.
    #[error("projection source binding exceeded its resource limit")]
    ResourceLimit,
    /// The caller's deadline, interrupt, or resource monitor requested a stop.
    #[error("projection source binding was stopped")]
    Stopped,
}

impl Context {
    /// Whether every live declaration lookup fits the bounded projection
    /// envelope. Call this before repeated exact-identity authentication in a
    /// post-solve path that cannot charge arbitrary frontend inventory scans.
    #[must_use]
    pub fn bounded_projection_declaration_inventory_size(&self) -> Option<usize> {
        let mut count = 0usize;
        for (surface, info) in self
            .symbol_iter()
            .take(MAX_BOUNDED_PROJECTION_DECLARATIONS + 1)
        {
            count = count.checked_add(1)?;
            if count > MAX_BOUNDED_PROJECTION_DECLARATIONS
                || surface.len() > MAX_BOUNDED_PROJECTION_IDENTITY_BYTES
                || self.symbol_identity_name(surface, info).len()
                    > MAX_BOUNDED_PROJECTION_IDENTITY_BYTES
            {
                return None;
            }
        }
        Some(count)
    }

    /// Capture the current opaque source context/scope stamp.
    #[must_use]
    pub fn source_context_stamp(&self) -> SourceContextStamp {
        self.context_identity.stamp(self.source_revision)
    }

    /// Return the effective kind of one currently live declaration identity.
    ///
    /// An adopted definitional macro overrides its declaration's original
    /// [`DeclarationKind::Uninterpreted`] classification while the adopting
    /// assertion remains live.
    #[must_use]
    pub fn effective_declaration_kind(
        &self,
        declaration_id: &DeclarationId,
    ) -> Option<DeclarationKind> {
        if self
            .adopted_macro_declaration_ids
            .values()
            .any(|adopted| adopted == declaration_id)
        {
            return Some(DeclarationKind::AdoptedDefinition);
        }
        self.symbol_iter().find_map(|(_, info)| {
            (info.declaration_id() == declaration_id).then_some(info.declaration_kind())
        })
    }

    /// Positively bind selected core symbols to exact live ordinary free-UF
    /// declarations and freeze the complete reachable source snapshot.
    pub fn check_projection_bindings(
        &self,
        roots: &[TermId],
        requests: &[ProjectionBindingRequest],
    ) -> Result<CheckedProjectionBindings, ProjectionBindingRejection> {
        self.check_projection_bindings_with_stop(roots, requests, || false)
    }

    /// Positively bind one exact core symbol/signature to a live, ordinary,
    /// free uninterpreted-function declaration.
    ///
    /// Unlike [`Self::check_projection_bindings`], this checks declaration
    /// identity and kind only; it does not claim occurrence coverage for a
    /// root set. Consumers must independently prove that every occurrence they
    /// reinterpret matches this checked binding. The returned value is opaque,
    /// non-`Clone`, and bound to the current source/scope epoch.
    pub fn check_projection_declaration(
        &self,
        request: &ProjectionBindingRequest,
    ) -> Result<CheckedProjectionBinding, ProjectionBindingRejection> {
        self.check_projection_declaration_request(request)
    }

    /// Cancellation-aware form of [`Self::check_projection_bindings`].
    ///
    /// The callback is polled throughout request validation and reachable-term
    /// freezing so an authored solve's deadline, interrupt, and memory envelope
    /// remain enforceable while source evidence is constructed.
    pub fn check_projection_bindings_with_stop(
        &self,
        roots: &[TermId],
        requests: &[ProjectionBindingRequest],
        mut should_stop: impl FnMut() -> bool,
    ) -> Result<CheckedProjectionBindings, ProjectionBindingRejection> {
        if should_stop() {
            return Err(ProjectionBindingRejection::Stopped);
        }
        if requests.len() > MAX_PROJECTION_BINDING_TERMS
            || roots.len() > MAX_PROJECTION_BINDING_TERMS
        {
            return Err(ProjectionBindingRejection::ResourceLimit);
        }
        let mut requested = HashMap::default();
        let mut checked_bindings = Vec::with_capacity(requests.len());
        for (index, request) in requests.iter().enumerate() {
            if should_stop() {
                return Err(ProjectionBindingRejection::Stopped);
            }
            if requested.insert(request.symbol.clone(), index).is_some() {
                return Err(ProjectionBindingRejection::DuplicateRequest {
                    symbol: request.symbol.clone(),
                });
            }
            checked_bindings.push(self.check_projection_declaration_request(request)?);
        }

        let mut frozen_terms = Vec::new();
        let mut seen = HashSet::default();
        let mut uses = vec![0usize; requests.len()];
        let mut stack = roots.to_vec();
        while let Some(term) = stack.pop() {
            if should_stop() {
                return Err(ProjectionBindingRejection::Stopped);
            }
            if term.index() >= self.terms.len() {
                return Err(ProjectionBindingRejection::InvalidTermId { term });
            }
            if !seen.insert(term) {
                continue;
            }
            if seen.len() > MAX_PROJECTION_BINDING_TERMS {
                return Err(ProjectionBindingRejection::ResourceLimit);
            }
            let data = self.terms.get(term).clone();
            let sort = self.terms.sort(term).clone();
            if should_stop() {
                return Err(ProjectionBindingRejection::Stopped);
            }
            match &data {
                TermData::App(symbol, args) => {
                    let selected = requested.get(symbol).copied();
                    if let Some(index) = selected {
                        let request = &requests[index];
                        if args.len() != request.parameter_sorts.len()
                            || sort != request.result_sort
                        {
                            return Err(ProjectionBindingRejection::SignatureMismatch {
                                symbol: symbol.clone(),
                            });
                        }
                        uses[index] = uses[index].saturating_add(1);
                    } else if self.has_live_function_declaration_for_symbol(symbol) {
                        return Err(
                            ProjectionBindingRejection::UnselectedDeclarationOccurrence {
                                symbol: symbol.clone(),
                            },
                        );
                    }
                    for (argument_index, &argument) in args.iter().enumerate() {
                        if should_stop() {
                            return Err(ProjectionBindingRejection::Stopped);
                        }
                        if argument.index() >= self.terms.len() {
                            return Err(ProjectionBindingRejection::InvalidTermId {
                                term: argument,
                            });
                        }
                        if let Some(index) = selected {
                            let request = &requests[index];
                            if self.terms.sort(argument) != &request.parameter_sorts[argument_index]
                            {
                                return Err(ProjectionBindingRejection::SignatureMismatch {
                                    symbol: symbol.clone(),
                                });
                            }
                        }
                        stack.push(argument);
                    }
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                TermData::Let(bindings, body) => {
                    for (_, value) in bindings {
                        if should_stop() {
                            return Err(ProjectionBindingRejection::Stopped);
                        }
                        stack.push(*value);
                    }
                    stack.push(*body);
                }
                TermData::Not(child) => stack.push(*child),
                TermData::Ite(condition, then_term, else_term) => {
                    stack.extend([*condition, *then_term, *else_term]);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    for trigger in triggers {
                        for &trigger_term in trigger {
                            if should_stop() {
                                return Err(ProjectionBindingRejection::Stopped);
                            }
                            stack.push(trigger_term);
                        }
                    }
                }
                _ => {
                    return Err(ProjectionBindingRejection::UnsupportedTermNode { term });
                }
            }
            frozen_terms.push(FrozenTerm {
                id: term,
                data,
                sort,
            });
        }
        for (index, use_count) in uses.iter().enumerate() {
            if should_stop() {
                return Err(ProjectionBindingRejection::Stopped);
            }
            if *use_count == 0 {
                return Err(ProjectionBindingRejection::UnusedRequest {
                    symbol: requests[index].symbol.clone(),
                });
            }
        }

        Ok(CheckedProjectionBindings {
            stamp: self.source_context_stamp(),
            roots: roots.to_vec(),
            checked_term_count: self.terms.len(),
            frozen_terms,
            bindings: checked_bindings,
        })
    }

    /// Whether checked source bindings still describe this exact context,
    /// scope, declaration environment, root vector, and reachable term graph.
    #[must_use]
    pub fn projection_bindings_still_current(
        &self,
        checked: &CheckedProjectionBindings,
        roots: &[TermId],
    ) -> bool {
        if checked.stamp != self.source_context_stamp() || checked.roots != roots {
            return false;
        }
        if !checked.frozen_terms.iter().all(|frozen| {
            frozen.id.index() < self.terms.len()
                && self.terms.get(frozen.id) == &frozen.data
                && self.terms.sort(frozen.id) == &frozen.sort
        }) {
            return false;
        }
        checked
            .bindings
            .iter()
            .all(|binding| self.projection_binding_still_current(binding))
    }

    /// Whether one positively checked projection declaration still names the
    /// same live declaration, kind, signature, and source/scope epoch.
    #[must_use]
    pub fn projection_binding_still_current(&self, binding: &CheckedProjectionBinding) -> bool {
        if binding.stamp != self.source_context_stamp() {
            return false;
        }
        let Symbol::Named(name) = &binding.symbol else {
            return false;
        };
        let Ok((surface, info)) = self.resolve_exact_live_identity(name, &binding.symbol) else {
            return false;
        };
        self.is_direct_ordinary_source_binding(surface, info, name)
            && info.declaration_id() == &binding.declaration_id
            && info.arg_sorts == binding.parameter_sorts
            && info.sort == binding.result_sort
            && self.effective_declaration_kind(info.declaration_id())
                == Some(DeclarationKind::Uninterpreted)
    }

    fn check_projection_declaration_request(
        &self,
        request: &ProjectionBindingRequest,
    ) -> Result<CheckedProjectionBinding, ProjectionBindingRejection> {
        let Symbol::Named(name) = &request.symbol else {
            return Err(ProjectionBindingRejection::UnsupportedSymbol {
                symbol: request.symbol.clone(),
            });
        };
        let (surface, info) = self.resolve_exact_live_identity(name, &request.symbol)?;
        let Some(kind) = self.effective_declaration_kind(info.declaration_id()) else {
            // Construction and currentness must use the same positive live-kind
            // predicate. Falling back to the stored kind here could mint a
            // binding which `projection_binding_still_current` rejects
            // immediately because the declaration identity is no longer in the
            // effective live inventory.
            return Err(ProjectionBindingRejection::NonOrdinaryBinding {
                symbol: request.symbol.clone(),
            });
        };
        if kind != DeclarationKind::Uninterpreted {
            return Err(ProjectionBindingRejection::NonFreeDeclaration {
                symbol: request.symbol.clone(),
                kind,
            });
        }
        if !self.is_direct_ordinary_source_binding(surface, info, name) {
            return Err(ProjectionBindingRejection::NonOrdinaryBinding {
                symbol: request.symbol.clone(),
            });
        }
        if info.arg_sorts != request.parameter_sorts || info.sort != request.result_sort {
            return Err(ProjectionBindingRejection::SignatureMismatch {
                symbol: request.symbol.clone(),
            });
        }
        Ok(CheckedProjectionBinding {
            stamp: self.source_context_stamp(),
            symbol: request.symbol.clone(),
            declaration_id: info.declaration_id().clone(),
            parameter_sorts: request.parameter_sorts.clone(),
            result_sort: request.result_sort.clone(),
        })
    }

    /// Whether `info` is the one direct source declaration that owns the exact
    /// core identity `identity`.
    ///
    /// A private core identity is permitted here: builtin-colliding source
    /// declarations intentionally receive one so their applications cannot be
    /// confused with interpreted operators. Native aliases use the same
    /// `internal_name` mechanism, so the private binding-origin bit is
    /// load-bearing; overload and solver-internal surface gates remain separate.
    fn is_direct_ordinary_source_binding(
        &self,
        surface: &str,
        info: &SymbolInfo,
        identity: &str,
    ) -> bool {
        // `is_completion_eligible_declaration`, NOT `is_direct_source_declaration`:
        // a native-API `declare_const`/`declare_fun` allocates its term in the
        // same operation that records its metadata, so it carries the same
        // "this is the source program's own free declaration" guarantee a
        // parsed `(declare-fun ...)` does — that is the documented point of
        // `SymbolBindingOrigin::NativeApiDeclaration`. Excluding it here made
        // every projection-binding consumer (the const-interp /
        // finite-table SAT certificates among them) decline outright for
        // API-route embedders: deductive-checks's guarded-broadcast refutation queries
        // pin a plain `declare-const` head, hit `NonOrdinaryBinding`, and a
        // genuinely SAT counterexample surfaced as
        // `Unknown (quantifier-unhandled)`. `Other` origins (aliases,
        // definitions, caller-supplied-term registrations, solver internals)
        // stay excluded, and the liveness, kind, overload, internal-symbol and
        // signature gates above and below are untouched.
        info.is_completion_eligible_declaration()
            && self.symbol_identity_name(surface, info) == identity
            && !self.overloaded_symbols.contains_key(surface)
            && !self.internal_symbols.contains(surface)
    }

    fn resolve_exact_live_identity<'a>(
        &'a self,
        identity: &str,
        symbol: &Symbol,
    ) -> Result<(&'a str, &'a SymbolInfo), ProjectionBindingRejection> {
        let mut matches = self
            .symbol_iter()
            .filter(|(surface, info)| self.symbol_identity_name(surface, info) == identity);
        let Some((surface, info)) = matches.next() else {
            return Err(ProjectionBindingRejection::UnknownDeclaration {
                symbol: symbol.clone(),
            });
        };
        if matches.next().is_some() {
            return Err(ProjectionBindingRejection::AmbiguousDeclaration {
                symbol: symbol.clone(),
            });
        }
        Ok((surface.as_str(), info))
    }

    fn has_live_function_declaration_for_symbol(&self, symbol: &Symbol) -> bool {
        let Symbol::Named(identity) = symbol else {
            return false;
        };
        self.symbol_iter().any(|(surface, info)| {
            !info.arg_sorts.is_empty() && self.symbol_identity_name(surface, info) == identity
        })
    }
}
