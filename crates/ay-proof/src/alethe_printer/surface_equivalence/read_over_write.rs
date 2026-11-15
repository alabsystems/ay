// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored read-over-write against the element it reads.
//!
//! Preprocessing folds `(select (store a i e) i)` to `e`, so the canonical term
//! states `e` where the problem file wrote the read. Carcara's `arrays_idx`
//! concludes exactly `(= (select (store a i1 e1) i2) e2)` when `i1`/`i2` and
//! `e1`/`e2` are one parsed term each (`checker/rules/arrays.rs`,
//! `arrays::idx`), so the equality is one stock step. When the stored element
//! is itself re-spelled against the canonical text, the element's own derived
//! equality is appended with `trans`.
//!
//! Only the SAME index is admitted. A read at a different index needs
//! `arrays_row` and a proved index disequality, which this schema never
//! claims, so it declines and the caller keeps its existing refusal.

use super::super::surface_literal::same_printed_term;
use super::super::*;
use super::{CanonicalNode, Derivation};

impl AlethePrinter<'_> {
    pub(super) fn read_over_write_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        let Some(read) = split_application(surface, "select") else {
            return false;
        };
        let [array, read_index] = read.as_slice() else {
            return false;
        };
        let Some(write) = split_application(array, "store") else {
            return false;
        };
        let [_, write_index, element] = write.as_slice() else {
            return false;
        };
        if !same_printed_term(write_index, read_index) {
            return false;
        }
        let canonical_text = canonical.text;
        if same_printed_term(element, canonical_text) {
            derivation.steps.push(format!(
                "(step {id} (cl (= {surface} {canonical_text})) :rule arrays_idx)"
            ));
            return true;
        }
        let leg = format!("{id}.re");
        if !self.derive_printed_equivalence(&leg, element, canonical, depth + 1, derivation) {
            return false;
        }
        derivation.steps.push(format!(
            "(step {id}.ri (cl (= {surface} {element})) :rule arrays_idx)"
        ));
        derivation.steps.push(format!(
            "(step {id} (cl (= {surface} {canonical_text})) :rule trans :premises ({id}.ri {leg}))"
        ));
        true
    }
}
