// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact elimination of one top-level negated pointwise array equality.
//!
//! This producer records syntax-to-syntax provenance only.  Result mapping
//! independently replays the equivalence and validates the retained model
//! before any SAT authority is minted.

use ay_core::term::TermEntryStamp;
use ay_core::{Sort, TermData, TermId};

use super::{Executor, QuantifierProcessingResult};
use crate::ematching::contains_quantifier;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ExactArrayNegationRecord {
    pub(super) assertion_index: usize,
    pub(super) original: TermId,
    pub(super) original_entry: TermEntryStamp,
    pub(super) rewritten: TermId,
    pub(super) rewritten_entry: TermEntryStamp,
}

/// Producer provenance for an exact whole-window rewrite.
///
/// The record is deliberately not authority.  Its consumer must prove exact
/// one-to-one coverage, replay the canonical replacement, and validate the
/// final installed model against `rewritten_assertions`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::executor) struct ExactArrayNegationEvidence {
    pub(super) original_assertions: Box<[TermId]>,
    pub(super) rewritten_assertions: Box<[TermId]>,
    pub(super) record: ExactArrayNegationRecord,
}

impl Executor {
    /// Freeze the authored/synthesized-term boundary, then try the sole exact
    /// infinite-domain quantifier rewrite.
    ///
    /// The watermark is fixed before any witness synthesis (Skolemization,
    /// diagonal instances, MBQI/CEGQI model values).  Later invented values
    /// therefore cannot discharge a `no_mbqi` Hilbert-`choose` obligation.
    /// The rewrite is producer provenance only: result mapping independently
    /// replays it and validates the retained model before granting SAT.
    pub(super) fn begin_quantifier_synthesis_or_exact_array_negation(
        &mut self,
    ) -> Option<QuantifierProcessingResult> {
        self.ctx.terms.set_synthesis_watermark();
        self.rewrite_exact_top_level_array_negation()
            .map(QuantifierProcessingResult::exact_array_negation)
    }

    /// Rewrite exactly one direct assertion
    /// `not (forall ((i I)) (= (select a i) (select b i)))` to `not (= a b)`.
    ///
    /// Array extensionality makes the two formulas equivalent.  The whole
    /// vector is adopted only when this is the sole quantified root, so no
    /// partial transformation can masquerade as complete quantifier coverage.
    pub(in crate::executor) fn rewrite_exact_top_level_array_negation(
        &mut self,
    ) -> Option<ExactArrayNegationEvidence> {
        let original_assertions = self.ctx.assertions.clone();
        let mut quantified = original_assertions
            .iter()
            .copied()
            .enumerate()
            .filter(|(_, root)| contains_quantifier(&self.ctx.terms, *root));
        let (assertion_index, original) = quantified.next()?;
        if quantified.next().is_some() {
            return None;
        }

        let original_entry = self.ctx.terms.entry_stamp(original)?;
        let (lhs, rhs) = self.exact_top_level_array_negation_operands(original)?;
        if original_assertions
            .iter()
            .copied()
            .enumerate()
            .any(|(index, root)| {
                index != assertion_index && self.is_direct_array_equality(root, lhs, rhs)
            })
        {
            // The SAT-only lane must not replace the existing authenticated
            // Skolem/proof route for an immediately contradictory query.
            return None;
        }
        let equality = self.ctx.terms.mk_eq(lhs, rhs);
        let rewritten = self.ctx.terms.mk_not(equality);
        let rewritten_entry = self.ctx.terms.entry_stamp(rewritten)?;
        let mut rewritten_assertions = original_assertions.clone();
        rewritten_assertions[assertion_index] = rewritten;
        self.ctx.assertions = rewritten_assertions.clone();

        Some(ExactArrayNegationEvidence {
            original_assertions: original_assertions.into_boxed_slice(),
            rewritten_assertions: rewritten_assertions.into_boxed_slice(),
            record: ExactArrayNegationRecord {
                assertion_index,
                original,
                original_entry,
                rewritten,
                rewritten_entry,
            },
        })
    }

    /// Independently reproduce the one admitted equivalence from `root`.
    pub(in crate::executor) fn replay_exact_top_level_array_negation(
        &mut self,
        root: TermId,
    ) -> Option<TermId> {
        let (lhs, rhs) = self.exact_top_level_array_negation_operands(root)?;
        let equality = self.ctx.terms.mk_eq(lhs, rhs);
        Some(self.ctx.terms.mk_not(equality))
    }

    fn exact_top_level_array_negation_operands(&self, root: TermId) -> Option<(TermId, TermId)> {
        let TermData::Not(quantifier) = self.ctx.terms.get(root) else {
            return None;
        };
        let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(*quantifier).clone() else {
            return None;
        };
        if vars.len() != 1 || !triggers.is_empty() || contains_quantifier(&self.ctx.terms, body) {
            return None;
        }

        let (binder, binder_sort) = &vars[0];
        // Keep the model check on a carrier with an uncovered point. For a
        // finite index sort, two differently normalized array interpretations
        // can still be extensionally equal once their explicit stores cover
        // the whole domain. The current array evaluator's normalized-default
        // mismatch is therefore authoritative only for this proven-infinite
        // target carrier.
        if binder_sort != &Sort::Int {
            return None;
        }
        let bound = [binder.clone()];
        let (lhs, rhs) = self.select_eq_at_binder(body, binder, &bound)?;
        let Sort::Array(array_sort) = self.ctx.terms.sort(lhs) else {
            return None;
        };
        if array_sort.index_sort != *binder_sort
            || self.ctx.terms.sort(rhs) != self.ctx.terms.sort(lhs)
        {
            return None;
        }
        Some((lhs, rhs))
    }

    fn is_direct_array_equality(&self, root: TermId, lhs: TermId, rhs: TermId) -> bool {
        matches!(
            self.ctx.terms.get(root),
            TermData::App(symbol, args)
                if symbol.name() == "="
                    && args.len() == 2
                    && ((args[0] == lhs && args[1] == rhs)
                        || (args[0] == rhs && args[1] == lhs))
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;

    fn load_assertions(source: &str) -> Executor {
        let commands = parse(source).expect("fixture parses");
        let mut executor = Executor::new();
        let output = executor.execute_all(&commands).expect("fixture executes");
        assert!(output.is_empty(), "fixture must not contain check-sat");
        executor
    }

    const DECLARATIONS: &str = r#"
        (set-logic ALIA)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const c (Array Int Int))
        (declare-const ba (Array Bool Int))
        (declare-const bb (Array Bool Int))
        (declare-const p Bool)
    "#;

    #[test]
    fn exact_direct_root_rewrites_one_slot_and_preserves_ground_siblings() {
        let mut executor = load_assertions(&format!(
            "{DECLARATIONS}
             (assert p)
             (assert (not (forall ((i Int)) (= (select a i) (select b i)))))"
        ));
        let original = executor.ctx.assertions.clone();
        let evidence = executor
            .rewrite_exact_top_level_array_negation()
            .expect("exact direct root rewrites");

        assert_eq!(evidence.record.assertion_index, 1);
        assert_eq!(evidence.original_assertions.as_ref(), original);
        assert_eq!(
            executor.ctx.assertions,
            evidence.rewritten_assertions.as_ref()
        );
        assert_eq!(executor.ctx.assertions[0], original[0]);
        assert!(executor
            .ctx
            .assertions
            .iter()
            .all(|&root| !contains_quantifier(&executor.ctx.terms, root)));
        assert_eq!(
            executor.replay_exact_top_level_array_negation(evidence.record.original),
            Some(evidence.record.rewritten)
        );
    }

    #[test]
    fn producer_declines_nested_multiple_and_noncanonical_shapes_without_rewriting() {
        let cases = [
            // The forall is nested below a disjunction, not the assertion root.
            "(assert (or p (not (forall ((i Int)) (= (select a i) (select b i))))))",
            // More than one quantified root makes whole-window coverage partial.
            "(assert (not (forall ((i Int)) (= (select a i) (select b i)))))
             (assert (not (forall ((i Int)) (= (select b i) (select c i)))))",
            // Multiple binders are outside the exact theorem.
            "(assert (not (forall ((i Int) (j Int))
                (= (select a i) (select b j)))))",
            // Trigger-bearing syntax is intentionally outside the narrow source.
            "(assert (not (forall ((i Int))
                (! (= (select a i) (select b i)) :pattern ((select a i))))))",
            // The matrix is not a pointwise select equality.
            "(assert (not (forall ((i Int)) (= i i))))",
            // The select indices are not exactly the binder.
            "(assert (not (forall ((i Int))
                (= (select a (+ i 1)) (select b (+ i 1))))))",
            // An array operand depends on the binder.
            "(assert (not (forall ((i Int))
                (= (select (ite (= i 0) a b) i) (select c i)))))",
            // A nested quantifier in the matrix must fail closed.
            "(assert (not (forall ((i Int))
                (and (= (select a i) (select b i))
                     (forall ((j Int)) (= (select b j) (select c j)))))))",
            // Preserve the existing authored-proof route for direct conflict.
            "(assert (not (forall ((i Int)) (= (select a i) (select b i)))))
             (assert (= a b))",
            // Finite carriers are outside the checked-model theorem. These two
            // differently normalized Bool arrays are extensionally identical:
            // both map false to 0 and true to 1.
            "(assert (= ba (store ((as const (Array Bool Int)) 0) true 1)))
             (assert (= bb (store ((as const (Array Bool Int)) 1) false 0)))
             (assert (not (forall ((i Bool))
                (= (select ba i) (select bb i)))))",
        ];

        for case in cases {
            let mut executor = load_assertions(&format!("{DECLARATIONS}\n{case}"));
            let before = executor.ctx.assertions.clone();
            assert!(
                executor.rewrite_exact_top_level_array_negation().is_none(),
                "unexpected rewrite for {case}"
            );
            assert_eq!(
                executor.ctx.assertions, before,
                "assertions changed for {case}"
            );
        }
    }
}
