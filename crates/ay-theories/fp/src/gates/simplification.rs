// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Literal identities shared with the BV gate construction strategy.
//!
//! Only the solver's canonical constant caches establish constant values. Their
//! unit clauses must remain in the same CNF namespace after `take_clauses` or
//! cache import, as required by the existing incremental-cache contract. Reset
//! clears both caches before restarting variable numbering. No input assignment,
//! arbitrary unit clause, or numeric literal spelling is treated as a constant.

use super::{CnfLit, FpSolver};

impl FpSolver<'_> {
    pub(crate) fn known_literal_value(&self, lit: CnfLit) -> Option<bool> {
        if self.cached_false == Some(lit) || self.cached_true == Some(-lit) {
            Some(false)
        } else if self.cached_true == Some(lit) || self.cached_false == Some(-lit) {
            Some(true)
        } else {
            None
        }
    }

    pub(super) fn simplify_and(&mut self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        if a == b {
            return Some(a);
        }
        if a == -b {
            return Some(self.const_false());
        }
        match (self.known_literal_value(a), self.known_literal_value(b)) {
            (Some(false), _) => Some(a),
            (_, Some(false)) => Some(b),
            (Some(true), _) => Some(b),
            (_, Some(true)) => Some(a),
            _ => None,
        }
    }

    pub(super) fn simplify_or(&mut self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        if a == b {
            return Some(a);
        }
        if a == -b {
            return Some(self.const_true());
        }
        match (self.known_literal_value(a), self.known_literal_value(b)) {
            (Some(true), _) => Some(a),
            (_, Some(true)) => Some(b),
            (Some(false), _) => Some(b),
            (_, Some(false)) => Some(a),
            _ => None,
        }
    }

    pub(super) fn simplify_xor(&mut self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        if a == b {
            return Some(self.const_false());
        }
        if a == -b {
            return Some(self.const_true());
        }
        match (self.known_literal_value(a), self.known_literal_value(b)) {
            (Some(false), _) => Some(b),
            (_, Some(false)) => Some(a),
            (Some(true), _) => Some(-b),
            (_, Some(true)) => Some(-a),
            _ => None,
        }
    }

    pub(super) fn simplify_ite(
        &mut self,
        cond: CnfLit,
        then_val: CnfLit,
        else_val: CnfLit,
    ) -> Option<CnfLit> {
        if then_val == else_val {
            return Some(then_val);
        }
        if let Some(value) = self.known_literal_value(cond) {
            return Some(if value { then_val } else { else_val });
        }
        if then_val == -else_val {
            return Some(self.make_xor(cond, else_val));
        }
        match (
            self.known_literal_value(then_val),
            self.known_literal_value(else_val),
        ) {
            (Some(true), _) => return Some(self.make_or(cond, else_val)),
            (Some(false), _) => return Some(self.make_and(-cond, else_val)),
            (_, Some(true)) => return Some(self.make_or(-cond, then_val)),
            (_, Some(false)) => return Some(self.make_and(cond, then_val)),
            _ => {}
        }
        if cond == then_val {
            Some(self.make_or(cond, else_val))
        } else if cond == -then_val {
            Some(self.make_and(-cond, else_val))
        } else if cond == else_val {
            Some(self.make_and(cond, then_val))
        } else if cond == -else_val {
            Some(self.make_or(-cond, then_val))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests;
