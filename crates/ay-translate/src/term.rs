// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term translation trait.

use std::hash::Hash;

use ay_dpll::api::Term;

use crate::TranslationTermHost;

/// Trait for translating consumer expression types to ay terms.
pub trait TermTranslator {
    /// The consumer's expression type.
    type Expr;
    /// The key type used to identify variables in the context.
    type VarKey: Eq + Hash;
    /// Error type for translation failures.
    type Error;
    /// Translate a consumer expression to a ay term.
    fn translate<H: TranslationTermHost<Self::VarKey>>(
        &self,
        ctx: &mut H,
        expr: &Self::Expr,
    ) -> Result<Term, Self::Error>;
}
