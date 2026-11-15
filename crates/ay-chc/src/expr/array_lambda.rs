// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed closure conversion for array lambdas. The body is closed over private
//! formal variables; only capture values are ordinary rewriting children.
//! See Minamide, Morrisett and Harper, *Typed Closure Conversion*, POPL 1996,
//! https://www.cs.cmu.edu/~rwh/papers/closures/popl96.pdf.

mod analysis;

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap;

use super::{ChcExpr, ChcSort, ChcVar};
use crate::{ChcError, ChcResult};

/// An immutable closed array-lambda template and its ordered environment.
///
/// Construction is checked. Generic rewrites change only `captures`, preserving
/// the binder and formal variables inside `body`. Consequently substitution of
/// a free variable can never capture the lambda's bound index.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ChcArrayLambda {
    binder: ChcVar,
    formals: Vec<ChcVar>,
    body: Arc<ChcExpr>,
    captures: Vec<Arc<ChcExpr>>,
    value_sort: ChcSort,
    function_symbols: std::collections::BTreeSet<String>,
}

impl ChcExpr {
    /// Close a well-typed single-binder body over all of its free variables.
    /// Incomplete or over-budget discovery is an error, never a closedness claim.
    pub fn array_lambda(binder: ChcVar, body: Self) -> ChcResult<Self> {
        analysis::validate_sort(&binder.sort)?;
        analysis::validate_rendering_bound(&body)?;
        let value_sort = analysis::validate_matrix(&body)?;
        let mut free = analysis::free_variables(&body)?;
        free.retain(|variable| variable != &binder);

        // Variables are all abstracted below. Only function/relation symbols
        // remain in the template's term namespace. Capture expressions are
        // evaluated outside the parallel let, even when their names coincide.
        let symbols = analysis::function_symbols(&body)?;
        let mut prefix = "ay!lambda!".to_owned();
        while symbols.iter().any(|name| name.starts_with(&prefix)) {
            prefix.push('!');
        }
        let private_binder = ChcVar::new(format!("{prefix}index"), binder.sort.clone());
        let formals: Vec<_> = free
            .iter()
            .enumerate()
            .map(|(index, variable)| {
                ChcVar::new(format!("{prefix}capture{index}"), variable.sort.clone())
            })
            .collect();
        let mut replacements = vec![(binder, Arc::new(Self::Var(private_binder.clone())))];
        replacements.extend(
            free.iter().cloned().zip(
                formals
                    .iter()
                    .cloned()
                    .map(|variable| Arc::new(Self::Var(variable))),
            ),
        );
        let map: DetHashMap<_, _> = replacements
            .iter()
            .map(|(variable, value)| (variable, Arc::clone(value)))
            .collect();
        let closed = Self::substitute_let_shared(&Arc::new(body), &map);
        let permitted: std::collections::BTreeSet<_> = formals
            .iter()
            .chain(std::iter::once(&private_binder))
            .cloned()
            .collect();
        if analysis::free_variables(&closed)?
            .iter()
            .any(|variable| !permitted.contains(variable))
        {
            return Err(ChcError::Verification(
                "array lambda closure conversion left an unbound variable".into(),
            ));
        }
        Ok(Self::ArrayLambda(Box::new(ChcArrayLambda {
            binder: private_binder,
            formals,
            body: closed,
            captures: free
                .into_iter()
                .map(|variable| Arc::new(Self::Var(variable)))
                .collect(),
            value_sort,
            function_symbols: symbols,
        })))
    }
}

impl ChcArrayLambda {
    /// The private bound array index.
    pub fn binder(&self) -> &ChcVar {
        &self.binder
    }

    /// Private environment slots, in capture order.
    pub fn formals(&self) -> &[ChcVar] {
        &self.formals
    }

    /// The immutable, closed lambda matrix.
    pub fn body(&self) -> &Arc<ChcExpr> {
        &self.body
    }

    /// Free expression values supplied to the private slots.
    pub fn captures(&self) -> &[Arc<ChcExpr>] {
        &self.captures
    }

    /// Borrow the checked result sort without cloning potentially large metadata.
    pub(crate) fn value_sort(&self) -> &ChcSort {
        &self.value_sort
    }

    /// The array sort induced by index and result types.
    pub fn sort(&self) -> ChcSort {
        ChcSort::Array(
            Box::new(self.binder.sort.clone()),
            Box::new(self.value_sort.clone()),
        )
    }

    /// Rewrites may change capture expressions, including their sorts. The
    /// strict validators and converters reject a sort-changing substitution;
    /// retaining an old capture would silently discard the requested rewrite.
    pub(crate) fn with_captures(&self, captures: Vec<Arc<ChcExpr>>) -> Box<Self> {
        Box::new(Self {
            captures,
            ..self.clone()
        })
    }

    pub(crate) fn code_uses_prefix(&self, prefix: &str) -> bool {
        self.function_symbols
            .iter()
            .any(|name| name.starts_with(prefix))
    }

    pub(crate) fn conversion_prefix(&self) -> ChcResult<String> {
        let expression = ChcExpr::ArrayLambda(Box::new(self.clone()));
        let symbols = analysis::function_symbols(&expression)?;
        let mut prefix = "ay!lambda!index".to_owned();
        while symbols.iter().any(|name| name.starts_with(&prefix)) {
            prefix.push('!');
        }
        Ok(prefix)
    }

    pub(crate) fn captures_are_well_typed(&self) -> bool {
        self.captures.len() == self.formals.len()
            && self
                .captures
                .iter()
                .zip(&self.formals)
                .all(|(value, formal)| value.sort() == formal.sort)
    }

    /// Instantiate only the private formals. Input captures and the index are
    /// inserted simultaneously, so their free variables cannot be captured.
    pub(crate) fn instantiate(&self, index: ChcExpr) -> Option<ChcExpr> {
        if index.sort() != self.binder.sort || !self.captures_are_well_typed() {
            return None;
        }
        let mut replacements = vec![(&self.binder, Arc::new(index))];
        replacements.extend(self.formals.iter().zip(self.captures.iter().cloned()));
        let map = replacements.into_iter().collect();
        let value = ChcExpr::substitute_let_shared(&self.body, &map);
        Some(Arc::try_unwrap(value).unwrap_or_else(|value| (*value).clone()))
    }

    /// Leave a harmless shell while ChcExpr's iterative destructor owns both
    /// the template body and the environment's children.
    pub(crate) fn take_children_for_drop(&mut self) -> Vec<Arc<ChcExpr>> {
        let mut children = std::mem::take(&mut self.captures);
        children.push(std::mem::replace(
            &mut self.body,
            Arc::new(ChcExpr::Bool(false)),
        ));
        children
    }

    /// Captures are parallel let RHSs, outside both their own bindings and the
    /// lambda. `body` is rendered in a separate binder-local serializer scope.
    pub(crate) fn render(&self, captures: &[String], body: &str) -> String {
        let sort = crate::smt::executor_adapter::sort_to_smtlib(&self.binder.sort);
        let lambda = format!("(lambda (({} {sort})) {body})", self.binder.name);
        if captures.is_empty() {
            return lambda;
        }
        let bindings = self
            .formals
            .iter()
            .zip(captures)
            .map(|(formal, value)| format!("({} {value})", formal.name))
            .collect::<Vec<_>>()
            .join(" ");
        format!("(let ({bindings}) {lambda})")
    }
}

#[cfg(test)]
mod tests;
