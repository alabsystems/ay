// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term and function declaration handles.

use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use ay_core::term::TermEntryStamp;
use ay_core::{Sort, TermId};
use ay_frontend::{DeclarationId, DeclarationKind, SourceContextStamp};

static NEXT_TERM_ARENA_STAMP: AtomicU64 = AtomicU64::new(1);

/// Opaque identity of one native solver's current term arena.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct TermArenaStamp(u64);

impl TermArenaStamp {
    #[allow(clippy::panic, deprecated)]
    pub(crate) fn fresh() -> Self {
        // `fetch_update`, not `try_update`: same closure-CAS loop, stable
        // since 1.45 — see the twin note in ay-core/src/term/mod.rs.
        let stamp = NEXT_TERM_ARENA_STAMP
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
                current.checked_add(1)
            })
            .unwrap_or_else(|_| panic!("native solver term-arena identity space exhausted"));
        Self(stamp)
    }
}

impl std::fmt::Debug for TermArenaStamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("TermArenaStamp(<opaque>)")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TermAuthority {
    /// A raw numeric ID with no evidence about its originating arena or entry.
    Unauthenticated,
    /// Exact solver-incarnation and term-entry birth identity.
    Authenticated {
        arena: TermArenaStamp,
        entry: TermEntryStamp,
    },
}

/// An authenticated handle to one exact term in one solver incarnation.
///
/// Numeric [`TermId`] values are reusable after a full reset or a speculative
/// suffix rollback. Equality and hashing therefore include opaque arena and
/// entry-birth authority, and every solver operation validates that authority
/// before indexing its term store.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Term {
    id: TermId,
    authority: TermAuthority,
}

impl Term {
    /// Get the underlying term ID.
    ///
    /// The numeric ID is for diagnostics and compatibility serialization only;
    /// it is not a complete term identity and can be reused by another solver
    /// or after reset. Compare [`Term`] values themselves when identity matters.
    pub fn id(self) -> TermId {
        self.id
    }

    /// Create an unauthenticated term from a raw numeric ID.
    ///
    /// This preserves source compatibility for adapters that need to carry an
    /// opaque number, but the result is deliberately rejected by every solver
    /// operation. Only a solver/context that owns a trusted raw-handle table can
    /// reconstitute an authenticated term. This method can therefore never turn
    /// an arbitrary or stale integer into declaration or assertion authority.
    #[must_use]
    pub fn from_raw(raw: u32) -> Self {
        Self {
            id: TermId(raw),
            authority: TermAuthority::Unauthenticated,
        }
    }

    /// Extract the raw u32 handle from a Term.
    ///
    /// This intentionally strips identity authority. Passing the number back to
    /// [`Self::from_raw`] does not recreate an authenticated handle.
    #[must_use]
    pub fn to_raw(self) -> u32 {
        self.id.0
    }

    pub(crate) fn authenticated(id: TermId, arena: TermArenaStamp, entry: TermEntryStamp) -> Self {
        Self {
            id,
            authority: TermAuthority::Authenticated { arena, entry },
        }
    }

    pub(crate) fn authenticates(self, arena: TermArenaStamp, entry: TermEntryStamp) -> bool {
        self.authority == TermAuthority::Authenticated { arena, entry }
    }
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Term").field(&self.id).finish()
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Term({})", self.id)
    }
}

/// Exact frontend authority carried by a native declaration handle.
///
/// The core spelling is deliberately kept on [`FuncDecl`] for term building;
/// this separate opaque capability prevents that spelling and a matching
/// signature from authenticating a declaration reincarnated after reset.
#[derive(Debug, Clone)]
pub(crate) struct FrontendFuncDeclIdentity {
    context_stamp: SourceContextStamp,
    declaration_id: DeclarationId,
    declaration_kind: DeclarationKind,
}

impl PartialEq for FrontendFuncDeclIdentity {
    fn eq(&self, other: &Self) -> bool {
        self.context_stamp.is_same_context(&other.context_stamp)
            && self.declaration_id == other.declaration_id
            && self.declaration_kind == other.declaration_kind
    }
}

impl Eq for FrontendFuncDeclIdentity {}

impl Hash for FrontendFuncDeclIdentity {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Declaration ids are allocation-unique. Context clones deliberately
        // retain those ids but compare unequal above; sharing a hash bucket in
        // that rare case is valid and avoids hashing the stamp's revision.
        self.declaration_id.hash(state);
        self.declaration_kind.hash(state);
    }
}

impl FrontendFuncDeclIdentity {
    pub(crate) fn new(
        context_stamp: SourceContextStamp,
        declaration_id: DeclarationId,
        declaration_kind: DeclarationKind,
    ) -> Self {
        Self {
            context_stamp,
            declaration_id,
            declaration_kind,
        }
    }

    pub(crate) fn context_stamp(&self) -> &SourceContextStamp {
        &self.context_stamp
    }

    pub(crate) fn declaration_id(&self) -> &DeclarationId {
        &self.declaration_id
    }

    pub(crate) fn declaration_kind(&self) -> DeclarationKind {
        self.declaration_kind
    }
}

/// Unforgeable identity of one explicit native inline definition.
#[derive(Clone)]
pub(crate) struct NativeDefinitionIdentity(Arc<NativeDefinitionMarker>);

#[derive(Debug)]
struct NativeDefinitionMarker;

impl NativeDefinitionIdentity {
    pub(crate) fn fresh() -> Self {
        Self(Arc::new(NativeDefinitionMarker))
    }
}

impl PartialEq for NativeDefinitionIdentity {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for NativeDefinitionIdentity {}

impl Hash for NativeDefinitionIdentity {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Arc::as_ptr(&self.0), state);
    }
}

impl std::fmt::Debug for NativeDefinitionIdentity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NativeDefinitionIdentity(<opaque>)")
    }
}

/// Exact, non-forgeable authority associated with an authenticated function
/// handle. Public synthetic handles intentionally carry no such value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum FuncDeclIdentity {
    Frontend(FrontendFuncDeclIdentity),
    NativeDefinition(NativeDefinitionIdentity),
}

/// A declared function (n-arity) that can be applied to arguments.
///
/// For 0-arity functions (constants), use `Solver::declare_const` instead.
/// For higher arity functions, use `Solver::declare_fun` to create a `FuncDecl`,
/// then `Solver::apply` to create application terms.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncDecl {
    /// Caller-visible function name.
    pub(crate) name: String,
    /// Exact symbol identity stored in core application terms.
    ///
    /// This differs from `name` for user declarations whose spelling also
    /// names an interpreted builtin.  Keeping the two identities separate is
    /// what prevents a native UF such as `rem` or `=` from acquiring builtin
    /// semantics in downstream solvers and proof checkers.
    pub(crate) core_name: String,
    /// Argument sorts (domain)
    pub(crate) domain: Vec<Sort>,
    /// Return sort (range)
    pub(crate) range: Sort,
    /// Exact declaration authority. `None` is reserved for synthetic builtin
    /// and model handles and can never authenticate a user/native declaration.
    pub(crate) identity: Option<FuncDeclIdentity>,
}

impl FuncDecl {
    /// Create a new function declaration.
    ///
    /// Used by FFI layers to construct synthetic func_decl handles for
    /// built-in operators and model constant declarations. Synthetic handles
    /// carry no declaration authority: matching a user/native declaration's
    /// spelling and signature is never enough to pass [`crate::api::Solver`]
    /// handle authentication.
    #[must_use]
    pub fn new(name: String, domain: Vec<Sort>, range: Sort) -> Self {
        let core_name = name.clone();
        Self {
            name,
            core_name,
            domain,
            range,
            identity: None,
        }
    }

    /// Construct a handle bound to one exact live frontend declaration.
    pub(crate) fn with_frontend_identity(
        name: String,
        core_name: String,
        domain: Vec<Sort>,
        range: Sort,
        identity: FrontendFuncDeclIdentity,
    ) -> Self {
        Self {
            name,
            core_name,
            domain,
            range,
            identity: Some(FuncDeclIdentity::Frontend(identity)),
        }
    }

    /// Construct a handle bound to one exact native inline definition.
    pub(crate) fn with_native_definition_identity(
        name: String,
        domain: Vec<Sort>,
        range: Sort,
        identity: NativeDefinitionIdentity,
    ) -> Self {
        Self {
            core_name: name.clone(),
            name,
            domain,
            range,
            identity: Some(FuncDeclIdentity::NativeDefinition(identity)),
        }
    }

    /// Exact symbol identity to place in a core application.
    pub(crate) fn core_name(&self) -> &str {
        &self.core_name
    }

    /// Exact core identity retained in application terms.
    ///
    /// This read-only adapter hook lets compatibility layers recover the
    /// authenticated declaration handle for an inspected application. The
    /// returned spelling is not declaration authority by itself.
    #[doc(hidden)]
    #[must_use]
    pub fn declaration_identity_name(&self) -> &str {
        &self.core_name
    }

    /// Whether this handle carries declaration authority rather than describing
    /// a synthetic builtin/model operator.
    #[doc(hidden)]
    #[must_use]
    pub fn has_declaration_authority(&self) -> bool {
        self.identity.is_some()
    }

    /// Preserve this declaration's identity while replacing a polymorphic or
    /// adapter-facing signature with its concrete instance.
    ///
    /// This is an internal compatibility hook. `Solver::try_apply` still
    /// authenticates the resulting signature against the registered
    /// declaration.
    #[doc(hidden)]
    #[must_use]
    pub fn with_instantiated_signature(&self, domain: Vec<Sort>, range: Sort) -> Self {
        Self {
            name: self.name.clone(),
            core_name: self.core_name.clone(),
            domain,
            range,
            identity: self.identity.clone(),
        }
    }

    /// Get the function name
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the function arity (number of arguments)
    #[must_use]
    pub fn arity(&self) -> usize {
        self.domain.len()
    }

    /// Get the domain sorts
    #[must_use]
    pub fn domain(&self) -> &[Sort] {
        &self.domain
    }

    /// Get the range sort
    #[must_use]
    pub fn range(&self) -> &Sort {
        &self.range
    }
}

impl std::fmt::Display for FuncDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.domain.is_empty() {
            // 0-arity: name : range
            write!(f, "{} : {}", self.name, self.range)
        } else {
            // n-arity: name : (domain1, domain2, ...) -> range
            write!(f, "{} : (", self.name)?;
            for (i, sort) in self.domain.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{sort}")?;
            }
            write!(f, ") -> {}", self.range)
        }
    }
}
