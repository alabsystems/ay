// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact datatype-selector identity checks used by array model completion.

use ay_core::term::Symbol;
use ay_core::TermId;

use super::Executor;

impl Executor {
    /// Whether `name` is a selector of some declared datatype constructor.
    pub(super) fn is_datatype_selector_symbol(&self, name: &str) -> bool {
        self.ctx
            .ctor_selectors_iter()
            .any(|(_, selectors)| selectors.iter().any(|selector| selector == name))
    }

    pub(super) fn is_exact_datatype_selector_application(
        &self,
        symbol: &Symbol,
        args: &[TermId],
        result: TermId,
    ) -> bool {
        matches!(symbol, Symbol::Named(_))
            && self
                .ctx
                .exact_datatype_member_info(symbol.name())
                .is_some_and(|info| {
                    info.declaration_kind() == ay_frontend::DeclarationKind::DatatypeSelector
                        && info.arg_sorts.len() == args.len()
                        && info
                            .arg_sorts
                            .iter()
                            .zip(args)
                            .all(|(expected, &actual)| expected == self.ctx.terms.sort(actual))
                        && &info.sort == self.ctx.terms.sort(result)
                })
    }
}
