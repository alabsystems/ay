// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Local Boolean-gate simplifications.

use super::*;

impl BvSolver<'_> {
    pub(super) fn normalize_commutative_gate_key(a: CnfLit, b: CnfLit) -> (CnfLit, CnfLit) {
        if a < b {
            (a, b)
        } else {
            (b, a)
        }
    }

    pub(super) fn and_children_of(&self, lit: CnfLit) -> Option<(CnfLit, CnfLit)> {
        // `checked_abs` is `abs` on every literal; `i32::MIN` is no variable's
        // literal, so it has no AND children.
        self.and_children.get(&lit.checked_abs()?).copied()
    }

    pub(super) fn simplify_and_level1(&mut self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        if a == b {
            return Some(a);
        }
        if a == neg_lit(b) {
            return Some(self.fresh_false());
        }
        if self.is_known_true(a) {
            return Some(b);
        }
        if self.is_known_true(b) {
            return Some(a);
        }
        if self.is_known_false(a) {
            return Some(a);
        }
        if self.is_known_false(b) {
            return Some(b);
        }
        None
    }

    pub(super) fn split_common_complement(
        left: (CnfLit, CnfLit),
        right: (CnfLit, CnfLit),
    ) -> Option<CnfLit> {
        let (a, b) = left;
        let (c, d) = right;

        if a == c && b == neg_lit(d) {
            return Some(a);
        }
        if a == d && b == neg_lit(c) {
            return Some(a);
        }
        if b == c && a == neg_lit(d) {
            return Some(b);
        }
        if b == d && a == neg_lit(c) {
            return Some(b);
        }
        None
    }

    pub(super) fn simplify_xor_split_ands(&self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        let a_children = self.and_children_of(a)?;
        let b_children = self.and_children_of(b)?;
        let common = Self::split_common_complement(a_children, b_children)?;

        if (a < 0) == (b < 0) {
            Some(common)
        } else {
            Some(neg_lit(common))
        }
    }

    pub(super) fn simplify_xor_with_and_child(
        &mut self,
        and_lit: CnfLit,
        other: CnfLit,
    ) -> Option<CnfLit> {
        let (x, y) = self.and_children_of(and_lit)?;
        let and_is_negated = and_lit < 0;

        if other == x {
            return Some(if and_is_negated {
                self.mk_or(neg_lit(x), y)
            } else {
                self.mk_and(x, neg_lit(y))
            });
        }
        if other == y {
            return Some(if and_is_negated {
                self.mk_or(x, neg_lit(y))
            } else {
                self.mk_and(neg_lit(x), y)
            });
        }
        if other == neg_lit(x) {
            return Some(if and_is_negated {
                self.mk_and(x, neg_lit(y))
            } else {
                self.mk_or(neg_lit(x), y)
            });
        }
        if other == neg_lit(y) {
            return Some(if and_is_negated {
                self.mk_and(neg_lit(x), y)
            } else {
                self.mk_or(x, neg_lit(y))
            });
        }

        None
    }
}
