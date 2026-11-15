// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored negations elaboration eliminated from a canonical literal.
//!
//! `(not (not E))` becomes `E'` and `(not (distinct a b))` becomes `(= a b)`
//! (#screened-surface-gaps). An authored universal keeps its own spelling
//! inside `forall_inst`, so without a derived equality the confined-instance
//! pass declines and every later consumer (the `or` that clausifies the
//! instance) prints the authored literal against a canonical clause and is
//! holed. MEASURED at 938ec0327: `(=> (not (bvuge i 5)) ..)` and
//! `(=> .. (not (distinct (g i) 1)))` each published `unsat` with one `hole`
//! at that `or`. The same equality serves the authored-`assume` bridge
//! (`authored_assume/document_canonical.rs`) and the quantified `and_pos`
//! projection under `bind` (`surface_and_pos/quantified_body.rs`). A negated
//! conjunction is a disjunctive connective ([`super::flattened_clause`]).
//!
//! Each schema is stock pinned-carcara rules over the exact printed text:
//!
//! * `(not (not X))`: `not_simplify` concludes `(= (not (not X)) X)`
//!   (`checker/rules/simplification.rs`), then `trans` onto the canonical
//!   term's own derived equality when `X` is re-spelled;
//! * `(not (distinct a b))`: `distinct_elim` under `cong` over `not`, then the
//!   double negation above.
//!
//! The caller admits these schemas only after every established schema
//! declined the whole pair, so every equality printed before this module
//! existed is still printed byte-for-byte. Any other shape declines.

use super::super::*;
use super::{CanonicalNode, Derivation, SchemaTier};

impl AlethePrinter<'_> {
    /// One of the two negation schemas, or `false` with `derivation`
    /// unchanged (always, on a first attempt).
    pub(super) fn negation_form_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        if derivation.tier != SchemaTier::Extended {
            return false;
        }
        let Some(negated) = split_application(surface, "not") else {
            return false;
        };
        let [operand] = negated.as_slice() else {
            return false;
        };
        let checkpoint = derivation.steps.len();
        let derived = if let Some(inner) = split_application(operand, "not") {
            match inner.as_slice() {
                [core] => self
                    .double_negation_equivalence(id, surface, core, canonical, depth, derivation),
                _ => false,
            }
        } else if let Some(sides) = split_application(operand, "distinct") {
            let distinct = Distinct {
                text: operand,
                sides: &sides,
            };
            self.negated_distinct_equivalence(id, surface, distinct, canonical, depth, derivation)
        } else {
            false
        };
        if !derived {
            derivation.steps.truncate(checkpoint);
        }
        derived
    }

    /// `(= surface canonical)` for `surface = (not (not core))`.
    fn double_negation_equivalence(
        &self,
        id: &str,
        surface: &str,
        core: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        let canonical_text = canonical.text;
        if core == canonical_text {
            derivation.steps.push(format!(
                "(step {id} (cl (= {surface} {canonical_text})) :rule not_simplify)"
            ));
            return true;
        }
        let leg = format!("{id}.nr");
        if !self.derive_printed_equivalence(&leg, core, canonical, depth + 1, derivation) {
            return false;
        }
        derivation.steps.push(format!(
            "(step {id}.nn (cl (= {surface} {core})) :rule not_simplify)"
        ));
        derivation.steps.push(format!(
            "(step {id} (cl (= {surface} {canonical_text})) :rule trans :premises ({id}.nn {leg}))"
        ));
        true
    }

    /// `(= surface canonical)` for `surface = (not (distinct left right))`.
    fn negated_distinct_equivalence(
        &self,
        id: &str,
        surface: &str,
        Distinct {
            text: distinct,
            sides,
        }: Distinct<'_>,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        let [left, right] = sides else {
            return false;
        };
        let eliminated = format!("(not (= {left} {right}))");
        let doubled = format!("(not {eliminated})");
        let leg = format!("{id}.dn");
        if !self.double_negation_equivalence(
            &leg,
            &doubled,
            &format!("(= {left} {right})"),
            canonical,
            depth + 1,
            derivation,
        ) {
            return false;
        }
        let canonical_text = canonical.text;
        derivation.steps.push(format!(
            "(step {id}.de (cl (= {distinct} {eliminated})) :rule distinct_elim)"
        ));
        derivation.steps.push(format!(
            "(step {id}.dc (cl (= {surface} {doubled})) :rule cong :premises ({id}.de))"
        ));
        derivation.steps.push(format!(
            "(step {id} (cl (= {surface} {canonical_text})) :rule trans :premises ({id}.dc {leg}))"
        ));
        true
    }
}

/// An authored `(distinct ..)`: its exact printed text and its operands.
#[derive(Clone, Copy)]
struct Distinct<'a> {
    text: &'a str,
    sides: &'a [String],
}

#[cfg(test)]
mod tests;
