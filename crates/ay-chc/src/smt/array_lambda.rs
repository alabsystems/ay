// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Capture values are converted outside the fresh binder's conversion scope.

use super::{context::SmtContext, convert_dag::ConvertCx};
use crate::expr::ChcArrayLambda;
use ay_core::TermId;

impl SmtContext {
    pub(super) fn convert_array_lambda(
        &mut self,
        lambda: &ChcArrayLambda,
        outer: &mut ConvertCx,
    ) -> TermId {
        if !lambda.captures_are_well_typed() {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        }
        let values = self.convert_children(lambda.captures(), outer);
        if self.conversion_budget_exceeded {
            return self.terms.mk_bool(true);
        }
        if values
            .iter()
            .zip(lambda.formals())
            .any(|(value, formal)| self.terms.sort(*value) != &Self::convert_sort(&formal.sort))
        {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        }
        let Ok(prefix) = lambda.conversion_prefix() else {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        };
        let sort = Self::convert_sort(&lambda.binder().sort);
        let binder = self.terms.mk_fresh_var(&prefix, sort);
        let mut bindings: ay_core::kani_compat::DetHashMap<_, _> =
            lambda.formals().iter().cloned().zip(values).collect();
        bindings.insert(lambda.binder().clone(), binder);
        // A fresh memo prevents a shared template from reusing terms from a
        // different binder/capture environment. The global resource budget is
        // deliberately retained across this scope boundary.
        let mut inner = ConvertCx::scoped(bindings);
        let body = self.convert_child(lambda.body(), &mut inner);
        if self.conversion_budget_exceeded {
            return self.terms.mk_bool(true);
        }
        let crate::ChcSort::Array(_, value_sort) = lambda.sort() else {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        };
        if self.terms.sort(body) != &Self::convert_sort(&value_sort) {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        }
        self.terms.mk_lambda_array(binder, body)
    }
}
