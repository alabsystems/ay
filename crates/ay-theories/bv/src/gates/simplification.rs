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
        self.and_children.get(&lit.abs()).copied()
    }

    pub(super) fn simplify_and_level1(&mut self, a: CnfLit, b: CnfLit) -> Option<CnfLit> {
        if a == b {
            return Some(a);
        }
        if a == -b {
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

        if a == c && b == -d {
            return Some(a);
        }
        if a == d && b == -c {
            return Some(a);
        }
        if b == c && a == -d {
            return Some(b);
        }
        if b == d && a == -c {
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
            Some(-common)
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
                self.mk_or(-x, y)
            } else {
                self.mk_and(x, -y)
            });
        }
        if other == y {
            return Some(if and_is_negated {
                self.mk_or(x, -y)
            } else {
                self.mk_and(-x, y)
            });
        }
        if other == -x {
            return Some(if and_is_negated {
                self.mk_and(x, -y)
            } else {
                self.mk_or(-x, y)
            });
        }
        if other == -y {
            return Some(if and_is_negated {
                self.mk_and(-x, y)
            } else {
                self.mk_or(x, -y)
            });
        }

        None
    }
}
