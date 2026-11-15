// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact local declaration membership; values and SAT authority live elsewhere.

use super::*;

pub(in crate::quantified::counterexample) struct Binding<'a> {
    pub(in crate::quantified::counterexample) occurrence: usize,
    pub(in crate::quantified::counterexample) variable: &'a ChcVar,
    pub(in crate::quantified::counterexample) symbol: String,
}

pub(in crate::quantified::counterexample) struct Rendered<'a> {
    pub(in crate::quantified::counterexample) obligation: String,
    pub(in crate::quantified::counterexample) bindings: Vec<Binding<'a>>,
    /// Exact byte interval emitted for the complete ordered ordinary-function
    /// registry. Concrete replay replaces only this segment, never occurrences
    /// of a name or a declaration-looking substring in arbitrary source text.
    pub(in crate::quantified::counterexample) function_declarations: std::ops::Range<usize>,
}

pub(super) fn retain<'a>(
    obligation: String,
    scopes: Vec<Scope<'a>>,
    function_declarations: std::ops::Range<usize>,
    control: &SourceControl<'_>,
) -> Result<Rendered<'a>> {
    let mut count = 0usize;
    for scope in &scopes {
        control.charge(1).ok_or_else(refused)?;
        count = count
            .checked_add(scope.variables.len())
            .ok_or_else(refused)?;
    }
    control
        .bytes(
            count
                .checked_mul(std::mem::size_of::<Binding<'_>>())
                .ok_or_else(refused)?,
        )
        .ok_or_else(refused)?;
    let mut bindings = Vec::new();
    bindings.try_reserve_exact(count).map_err(|_| refused())?;
    for (occurrence, scope) in scopes.into_iter().enumerate() {
        for (variable, symbol) in scope.variables {
            control.charge(1).ok_or_else(refused)?;
            // Transfer the already charged fresh spelling, never regenerate
            // it from a model or clone it separately for the manifest.
            bindings.push(Binding {
                occurrence,
                variable,
                symbol,
            });
        }
    }
    Ok(Rendered {
        obligation,
        bindings,
        function_declarations,
    })
}

#[cfg(test)]
mod tests;
