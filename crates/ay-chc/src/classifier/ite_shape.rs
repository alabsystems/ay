// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `ite` signal of the acyclic BV proof-lane gates.
//!
//! [`ProblemFeatures::has_ite`] scans clause constraints only, but the parser
//! inlines a defining equality `(= v (ite c a b))` into the predicate argument
//! `v` feeds. An `ite` an encoder writes in a constraint therefore usually
//! reaches the classifier as a predicate argument, and the gates that read
//! `has_ite` as "this BV problem is `ite`-shaped" never saw it. MODEL_CHECKER_CONSUMER ask
//! 2026-10-14-acyclic-8bit-ite-chain: a 27-predicate acyclic 8-bit query
//! whose method value is a 13-deep `ite` chain (27 predicates and DAG depth 25
//! are under the size half of the gate) skipped the pre-algebraic acyclic BV
//! probe, whose collapsed BV-native candidate decides it in milliseconds, and
//! waited on the algebraic pre-strategy and the later exact-BvToInt probe:
//! seconds, and minutes while the algebraic validator was exponential in the
//! chain's depth.
//!
//! The predicate-argument signal is kept apart from `has_ite` on purpose: the
//! LIA Kind budgets that also read `has_ite` were tuned on its constraint-only
//! meaning, and they are not BV proof lanes.

use super::{ProblemClassifier, ProblemFeatures};
use crate::{ChcExpr, ChcOp, ChcProblem, ClauseHead};

impl ProblemClassifier {
    /// Whether any predicate argument of any clause, head or body, contains an
    /// `ite`. One DAG-linear walk per argument.
    pub(super) fn predicate_args_have_ite(problem: &ChcProblem) -> bool {
        problem.clauses().iter().any(|clause| {
            let head_args: &[ChcExpr] = match &clause.head {
                ClauseHead::Predicate(_, args) => args,
                ClauseHead::False => &[],
            };
            head_args
                .iter()
                .chain(clause.body.predicates.iter().flat_map(|(_, args)| args))
                .any(|arg| {
                    !crate::expr::dag::all_distinct(arg, |node| {
                        !matches!(node, ChcExpr::Op(ChcOp::Ite, _))
                    })
                })
        })
    }
}

impl ProblemFeatures {
    /// The size-or-`ite` half shared by the acyclic BV proof-lane gates: the
    /// pre-algebraic acyclic BV probe, the collapsed BV-native candidate and
    /// the exact native preference. An `ite` counts wherever the parser left
    /// it, constraint or predicate argument.
    pub(crate) fn acyclic_bv_proof_scale_or_ite(&self) -> bool {
        self.num_predicates >= 32
            || self.dag_depth >= 32
            || self.has_ite
            || self.has_ite_in_predicate_args
    }
}

#[cfg(test)]
mod tests {
    use crate::classifier::{ProblemClassifier, ProblemFeatures};
    use crate::ChcParser;

    /// A three-relation acyclic 8-bit chain, `p0 -> p1 -> err`: far below
    /// the size half of the gate, so only an `ite` can open it.
    fn classify(transition_constraint: &str) -> ProblemFeatures {
        let source = format!(
            "(set-logic HORN)\n\
             (declare-var x (_ BitVec 8))\n(declare-var y (_ BitVec 8))\n\
             (declare-var o (_ BitVec 8))\n\
             (declare-rel p0 ((_ BitVec 8) (_ BitVec 8)))\n\
             (declare-rel p1 ((_ BitVec 8) (_ BitVec 8)))\n(declare-rel err ())\n\
             (rule (=> true (p0 x y)))\n\
             (rule (=> (and (p0 x y) {transition_constraint}) (p1 x o)))\n\
             (rule (=> (and (p1 x y) (not (= y x))) err))\n(query err)\n"
        );
        let problem = ChcParser::parse(&source).expect("chain parses");
        ProblemClassifier::classify(&problem)
    }

    /// The defining equality of `o` is inlined into `p1`'s argument, so the
    /// constraint scan misses the `ite` and the predicate-argument scan finds it.
    #[test]
    fn an_inlined_ite_opens_the_acyclic_bv_gate() {
        let features = classify("(= o (ite (bvule x #x05) x #x05))");
        assert!(
            !features.has_ite,
            "the parser moved the ite out of the constraint"
        );
        assert!(features.has_ite_in_predicate_args);
        assert!(features.acyclic_bv_proof_scale_or_ite());
    }

    /// Negative twin: the same chain with an `ite`-free update stays below the
    /// gate.
    #[test]
    fn an_ite_free_small_chain_stays_below_the_acyclic_bv_gate() {
        let features = classify("(= o (bvadd x #x01))");
        assert!(!features.has_ite);
        assert!(!features.has_ite_in_predicate_args);
        assert!(!features.acyclic_bv_proof_scale_or_ite());
    }

    /// An `ite` in a guard stays in the constraint and counts through
    /// `has_ite`, as before.
    #[test]
    fn a_guard_ite_still_counts_through_has_ite() {
        let features = classify("(= (ite (bvule x #x05) x y) #x03) (= o x)");
        assert!(features.has_ite);
        assert!(!features.has_ite_in_predicate_args);
        assert!(features.acyclic_bv_proof_scale_or_ite());
    }
}
