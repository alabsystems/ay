// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic witnesses for structural Z3 5.1.0 SMT parser tokens.
//!
//! Structural tokens use a clean contradiction against a satisfiable baseline.
//! Attribute tokens additionally query the authored assertion and compare
//! against the same formula without the attribute. This prevents a parser that
//! merely ignores an annotation from receiving parity credit.

pub(super) struct SemanticWitness {
    pub(super) candidate: &'static str,
    pub(super) baseline: &'static str,
}

const SAT_BASELINE: &str = "(set-logic ALL)\n(check-sat)\n(exit)\n";

const SEMANTIC_INPUTS: [(&str, SemanticWitness); 12] = [
    (
        ":no-pattern",
        SemanticWitness {
            candidate: "(set-option :interactive-mode true)\n(declare-fun f (Int) Int)\n(assert (forall ((x Int)) (! false :no-pattern (f x))))\n(get-assertions)\n(check-sat)\n(exit)\n",
            baseline: "(set-option :interactive-mode true)\n(declare-fun f (Int) Int)\n(assert (forall ((x Int)) false))\n(get-assertions)\n(check-sat)\n(exit)\n",
        },
    ),
    (
        ":qid",
        SemanticWitness {
            candidate: "(set-option :interactive-mode true)\n(assert (forall ((x Int)) (! false :qid owner-qid)))\n(get-assertions)\n(check-sat)\n(exit)\n",
            baseline: "(set-option :interactive-mode true)\n(assert (forall ((x Int)) false))\n(get-assertions)\n(check-sat)\n(exit)\n",
        },
    ),
    (
        ":skolemid",
        SemanticWitness {
            candidate: "(set-option :interactive-mode true)\n(assert (forall ((x Int)) (! false :skolemid owner-skid)))\n(get-assertions)\n(check-sat)\n(exit)\n",
            baseline: "(set-option :interactive-mode true)\n(assert (forall ((x Int)) false))\n(get-assertions)\n(check-sat)\n(exit)\n",
        },
    ),
    (
        ":weight",
        SemanticWitness {
            candidate: "(set-option :interactive-mode true)\n(assert (forall ((x Int)) (! false :weight 7)))\n(get-assertions)\n(check-sat)\n(exit)\n",
            baseline: "(set-option :interactive-mode true)\n(assert (forall ((x Int)) false))\n(get-assertions)\n(check-sat)\n(exit)\n",
        },
    ),
    (
        "_",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(assert (= (_ bv1 1) (_ bv0 1)))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
    (
        "case",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(declare-datatype Bit ((zero) (one)))\n(declare-const b Bit)\n(assert (= (match b (case zero false) (case one false)) true))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
    (
        "exists",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(assert (exists ((x Int)) false))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
    (
        "forall",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(assert (forall ((x Int)) false))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
    (
        "let",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(assert (let ((x false)) x))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
    (
        "match",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(declare-datatype Bit ((zero) (one)))\n(declare-const b Bit)\n(assert (= (match b ((zero false) (one false))) true))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
    (
        "not",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(assert (not true))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
    (
        "par",
        SemanticWitness {
            candidate: "(set-logic ALL)\n(declare-datatypes ((Box 1)) ((par (T) ((box (value T))))))\n(declare-const b (Box Int))\n(assert (not (= (value b) (value b))))\n(check-sat)\n(exit)\n",
            baseline: SAT_BASELINE,
        },
    ),
];

pub(super) fn semantic_witness(owner: &str) -> Option<&'static SemanticWitness> {
    SEMANTIC_INPUTS
        .iter()
        .find_map(|(name, witness)| (*name == owner).then_some(witness))
}

pub(super) fn semantic_owner_names() -> impl Iterator<Item = &'static str> {
    SEMANTIC_INPUTS.iter().map(|(name, _)| *name)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_parser_token_table_is_closed_sorted_and_unique() {
        assert_eq!(SEMANTIC_INPUTS.len(), 12);
        assert!(SEMANTIC_INPUTS.windows(2).all(|pair| pair[0].0 < pair[1].0));
        assert_eq!(semantic_owner_names().count(), 12);
    }

    #[test]
    fn every_candidate_is_distinct_and_exercises_its_owner() {
        for (owner, witness) in &SEMANTIC_INPUTS {
            assert!(
                witness.candidate.contains(owner),
                "candidate does not contain {owner}"
            );
            assert!(witness.candidate.contains("(check-sat)"), "{owner}");
            assert!(witness.baseline.contains("(check-sat)"), "{owner}");
            assert_ne!(witness.candidate, witness.baseline, "{owner}");
            assert!(semantic_witness(owner).is_some(), "{owner}");
        }
        for (index, (_, witness)) in SEMANTIC_INPUTS.iter().enumerate() {
            for (_, other_witness) in SEMANTIC_INPUTS.iter().skip(index + 1) {
                assert_ne!(
                    witness.candidate, other_witness.candidate,
                    "duplicate candidate input"
                );
            }
        }
    }
}
