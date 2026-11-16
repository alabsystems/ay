// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

static CHECKABLE_RULE_NAMES: &[&str] = &ay_core::CHECKABLE_ALETHE_RULES;

/// A rule name canonicalized against the pinned checker's wire vocabulary.
///
/// The private field makes an unchecked wire-rule spelling unrepresentable
/// outside this module. Canonicalization borrows the static table entry, so
/// carrying a checked name requires neither an allocation nor a lifetime.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct CheckableRule(&'static str);

impl CheckableRule {
    pub(super) fn new(name: &str) -> Option<Self> {
        let index = CHECKABLE_RULE_NAMES.binary_search(&name).ok()?;
        Some(Self(CHECKABLE_RULE_NAMES[index]))
    }

    pub(super) fn or_hole(name: &str) -> Self {
        Self::new(name).unwrap_or_else(|| {
            Self::new(ay_core::UNPROVED_STEP_RULE)
                .expect("the pinned checker vocabulary must contain the canonical hole")
        })
    }

    pub(super) const fn as_str(self) -> &'static str {
        self.0
    }
}

impl fmt::Display for CheckableRule {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.0)
    }
}

#[cfg(test)]
#[path = "wire_rule_tests.rs"]
mod tests;
