// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `elaborate/mod.rs`; inherent method paths stay unchanged.

impl SymbolInfo {
    /// Stable identity of the declaration behind this binding.
    #[must_use]
    pub fn declaration_id(&self) -> &DeclarationId {
        &self.declaration_id
    }

    /// Positive origin kind of this declaration.
    ///
    /// Use [`Context::effective_declaration_kind`] when an adopted
    /// definitional macro must be distinguished from its free origin.
    #[must_use]
    pub fn declaration_kind(&self) -> DeclarationKind {
        self.declaration_kind
    }

    /// Whether this binding was installed directly by a source
    /// `declare-const`/`declare-fun`, rather than by an alias, definition,
    /// datatype/theory registration, or solver-internal API.
    ///
    /// This predicate is only producer-side provenance. It is not sufficient
    /// projection authority without the frontend's exact identity, kind,
    /// signature, overload, and scope-epoch checks.
    #[must_use]
    pub fn is_direct_source_declaration(&self) -> bool {
        self.binding_origin == SymbolBindingOrigin::DirectSourceDeclaration
    }

    /// Whether an unconstrained declaration with this binding may receive a
    /// canonical default value during quantified-output model completion.
    ///
    /// Parsed source declarations qualify, and so do native-API declarations
    /// that allocated their term atomically: both carry the guarantee that
    /// the symbol is the source program's own free declaration. `Other`
    /// origins (aliases, definitions, caller-supplied-term registrations,
    /// solver internals) stay excluded — completing those would either leak
    /// internal bookkeeping into user models or reward a forged registration.
    #[must_use]
    pub fn is_completion_eligible_declaration(&self) -> bool {
        matches!(
            self.binding_origin,
            SymbolBindingOrigin::DirectSourceDeclaration
                | SymbolBindingOrigin::NativeApiDeclaration
        )
    }
}
