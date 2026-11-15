// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reapply identical writes through checked read-over-write and congruence.

use super::*;

impl Circuit<'_, '_, '_> {
    pub(super) fn common_write(
        &mut self,
        a: &Write,
        b: &Write,
        key: &str,
        equality: Equality,
    ) -> Option<Equality> {
        if a.key != b.key
            || a.value.equality.left != b.value.equality.left
            || equality.left != format!("(select {} {key})", a.inner)
            || equality.right != format!("(select {} {key})", b.inner)
        {
            return None;
        }
        let left = self.read_over_write(a, key)?;
        let right = self.read_over_write(b, key)?;
        let condition = format!("(= {} {key})", a.index.text);
        let condition = self.proof.equality(&condition, &condition, "refl", &[])?;
        let value = &a.value.equality.left;
        let value = self.proof.equality(value, value, "refl", &[])?;
        let middle = self
            .proof
            .congruence("ite", &[condition, value, equality])?;
        let result = self.proof.chain(left, middle)?;
        let reverse = self
            .proof
            .equality(&right.right, &right.left, "symm", &[&right.step])?;
        self.proof.chain(result, reverse)
    }
}
