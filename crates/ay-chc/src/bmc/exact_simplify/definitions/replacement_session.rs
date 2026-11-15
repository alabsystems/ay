// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One immutable replacement-map admission per definitional round.
//!
//! Only admission is reused, never a substitution result. Inputs and expanded
//! outputs retain the existing independent depth/occurrence checks. The map and
//! control owner stay borrowed throughout the round; there is no transferable
//! token or cache keyed by an address. Legacy pure transforms remain unchanged
//! and are not made allocation- or latency-bounded by these checks.

use crate::bmc::AcyclicNames;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap;

enum Admission {
    Unchecked,
    Admitted,
    Pending,
}

pub(super) struct ReplacementSession<'map, 'owner, 'control> {
    substitutions: &'map DetHashMap<String, ChcExpr>,
    names: &'owner mut AcyclicNames<'control>,
    admission: Admission,
}

impl<'map, 'owner, 'control> ReplacementSession<'map, 'owner, 'control> {
    pub(super) fn new(
        substitutions: &'map DetHashMap<String, ChcExpr>,
        names: &'owner mut AcyclicNames<'control>,
    ) -> Self {
        Self {
            substitutions,
            names,
            admission: Admission::Unchecked,
        }
    }

    pub(super) fn substitute(&mut self, expression: &ChcExpr) -> Option<ChcExpr> {
        let substitutions = self.substitutions;
        let needs_admission = matches!(self.admission, Admission::Unchecked);
        let result = self.with_names(|names| {
            // Preserve the legacy first-input-before-RHS refusal order. Empty
            // rounds never admit the map, and early false still ends the round.
            names.check(expression)?;
            if needs_admission {
                for replacement in substitutions.values() {
                    names.check(replacement)?;
                }
            }
            let result = expression.substitute_name_map(substitutions);
            names.check(&result)?;
            Some(result)
        })?;
        self.admission = Admission::Admitted;
        Some(result)
    }

    /// Borrow the same control for unchanged surrounding round operations.
    /// Refusal or a caught panic (including one in a pure transform) cannot
    /// restore this session's admission or rearm its control owner.
    pub(super) fn with_names<T>(
        &mut self,
        operation: impl FnOnce(&mut AcyclicNames<'control>) -> Option<T>,
    ) -> Option<T> {
        let previous = std::mem::replace(&mut self.admission, Admission::Pending);
        if matches!(previous, Admission::Pending) {
            return self.names.refuse();
        }
        let result = operation(self.names)?;
        self.admission = previous;
        Some(result)
    }
}

impl Drop for ReplacementSession<'_, '_, '_> {
    fn drop(&mut self) {
        if matches!(self.admission, Admission::Pending) {
            let _ = self.names.refuse::<()>();
        }
    }
}

#[cfg(test)]
mod tests;
