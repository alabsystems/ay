// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact producer scope for opaque datatype model completion.

use ay_core::term::Symbol;
use ay_core::{Sort, TermId};

use super::dt_construct_budget::MAX_OPAQUE_DT_APP_ARGS;
use super::rendered_dt_guard::RenderedDatatypeGuard;
use super::rendered_dt_limits::SchemaSourceBudget;
use crate::executor::Executor;

impl Executor {
    /// Conservative borrowed work for classifying one datatype-result
    /// application. Direct UF metadata is included because a successful
    /// projection check clones both the request and checked binding.
    pub(super) fn opaque_application_signature_work(
        &self,
        symbol: &Symbol,
        args: &[TermId],
        result: TermId,
    ) -> Option<usize> {
        if args.len() > MAX_OPAQUE_DT_APP_ARGS
            || !matches!(symbol, Symbol::Named(_))
            || (symbol.name() != "select"
                && ay_frontend::is_canonical_theory_operator_identity(symbol.name()))
        {
            return None;
        }
        let mut budget = SchemaSourceBudget::new();
        if !budget.charge_identifier(symbol.name())
            || !budget.charge_sort(self.ctx.terms.sort(result))
            || args
                .iter()
                .any(|&arg| !budget.charge_sort(self.ctx.terms.sort(arg)))
        {
            return None;
        }
        if matches!(symbol, Symbol::Named(_))
            && symbol.name() != "select"
            && !ay_frontend::is_canonical_theory_operator_identity(symbol.name())
        {
            if let Some(info) = self.ctx.symbol_info_by_identity(symbol.name()) {
                if !budget.charge_sort(&info.sort)
                    || info.arg_sorts.iter().any(|sort| !budget.charge_sort(sort))
                {
                    return None;
                }
            }
        }
        budget.work()
    }

    /// Whether this exact application is an ordinary declared UF eligible for
    /// opaque datatype completion. Canonical theory identities and indexed
    /// symbols are never ordinary declarations, even if malformed low-level
    /// state attempts to give them declaration metadata.
    #[cfg(test)]
    pub(super) fn dt_completion_ordinary_uf_application(
        &self,
        symbol: &Symbol,
        args: &[TermId],
        result: TermId,
    ) -> bool {
        let guard = RenderedDatatypeGuard::new(self);
        self.dt_completion_ordinary_uf_application_guarded(&guard, symbol, args, result)
    }

    pub(super) fn dt_completion_ordinary_uf_application_guarded(
        &self,
        guard: &RenderedDatatypeGuard,
        symbol: &Symbol,
        args: &[TermId],
        result: TermId,
    ) -> bool {
        let result_sort = self.ctx.terms.sort(result);
        if !matches!(symbol, Symbol::Named(_))
            || args.is_empty()
            || args.len() > MAX_OPAQUE_DT_APP_ARGS
            || ay_frontend::is_canonical_theory_operator_identity(symbol.name())
            || !self.opaque_uf_signature_within_limits(symbol, args, result_sort)
            || !guard.is_exact(result_sort)
        {
            return false;
        }
        let request = ay_frontend::ProjectionBindingRequest {
            symbol: symbol.clone(),
            parameter_sorts: args
                .iter()
                .map(|&arg| self.ctx.terms.sort(arg).clone())
                .collect(),
            result_sort: result_sort.clone(),
        };
        self.ctx.check_projection_declaration(&request).is_ok()
    }

    /// Bound both the occurrence signature and the exact live declaration
    /// before recursive sort equality or any request-owned clones.
    fn opaque_uf_signature_within_limits(
        &self,
        symbol: &Symbol,
        args: &[TermId],
        result_sort: &Sort,
    ) -> bool {
        let mut budget = SchemaSourceBudget::new();
        if !budget.charge_identifier(symbol.name())
            || !budget.charge_sort(result_sort)
            || args
                .iter()
                .any(|&arg| !budget.charge_sort(self.ctx.terms.sort(arg)))
        {
            return false;
        }
        let Some(info) = self.ctx.symbol_info_by_identity(symbol.name()) else {
            return false;
        };
        info.arg_sorts.len() <= MAX_OPAQUE_DT_APP_ARGS
            && budget.charge_sort(&info.sort)
            && info.arg_sorts.iter().all(|sort| budget.charge_sort(sort))
    }

    /// Whether this is the exact canonical array-select shape whose element is
    /// the result: `(select : (Array I E) I -> E)`. A same-spelled declared UF
    /// has a private core identity and is handled only by the ordinary-UF arm.
    #[cfg(test)]
    pub(super) fn dt_completion_array_select_application(
        &self,
        symbol: &Symbol,
        args: &[TermId],
        result: TermId,
    ) -> bool {
        let guard = RenderedDatatypeGuard::new(self);
        self.dt_completion_array_select_application_guarded(&guard, symbol, args, result)
    }

    pub(super) fn dt_completion_array_select_application_guarded(
        &self,
        guard: &RenderedDatatypeGuard,
        symbol: &Symbol,
        args: &[TermId],
        result: TermId,
    ) -> bool {
        if symbol.name() != "select"
            || !matches!(symbol, Symbol::Named(_))
            || args.len() != 2
            || !self.opaque_select_signature_within_limits(args, result)
        {
            return false;
        }
        let canonical_binding_is_coherent =
            self.ctx
                .symbol_info_by_identity("select")
                .is_none_or(|info| {
                    self.ctx.effective_declaration_kind(info.declaration_id())
                        == Some(ay_frontend::DeclarationKind::Theory)
                });
        canonical_binding_is_coherent
            && guard.is_exact(self.ctx.terms.sort(result))
            && matches!(self.ctx.terms.sort(args[0]), Sort::Array(array_sort)
                if &array_sort.index_sort == self.ctx.terms.sort(args[1])
                    && &array_sort.element_sort == self.ctx.terms.sort(result))
    }

    /// Bound borrowed array/index/result descriptors before recursive `Sort`
    /// equality evaluates the exact canonical select signature.
    fn opaque_select_signature_within_limits(&self, args: &[TermId], result: TermId) -> bool {
        let mut budget = SchemaSourceBudget::new();
        budget.charge_identifier("select")
            && budget.charge_sort(self.ctx.terms.sort(result))
            && budget.charge_sort(self.ctx.terms.sort(args[0]))
            && budget.charge_sort(self.ctx.terms.sort(args[1]))
    }
}
