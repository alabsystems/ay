// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{FarkasAnnotation, Sort, TermId};

use super::{
    spend_or_unit, spend_provenance_or, spend_quant_chain, spend_tautology, OrTautologyPlan,
    OrUnitPlan, QuantInstanceChain, TautRoute, Volume, MAX_EMITTED_VECTOR_ENTRIES,
};
use crate::executor::proof_trust_surgery_ite::ProvenanceFarkasLemma;
use crate::executor::proof_trust_surgery_provenance_or::{
    ProvenanceOrAndConflictPlan, ProvenanceOrAndRefutation, ProvenanceOrPlan,
};
use crate::executor::Executor;

#[test]
fn repeated_identical_or_units_spend_each_triangular_chain() {
    let mut executor = Executor::new();
    let disjuncts: Vec<_> = (0..64)
        .map(|index| {
            executor
                .ctx
                .terms
                .mk_var(format!("or_unit_volume_{index}"), Sort::Bool)
        })
        .collect();
    let eliminations = disjuncts[..63]
        .iter()
        .copied()
        .map(|literal| (literal, literal))
        .collect();
    let plan = OrUnitPlan {
        orig: disjuncts[63],
        disjuncts,
        eliminations,
    };
    let per_plan = 64 * 65 / 2 + 64;
    let accepted = MAX_EMITTED_VECTOR_ENTRIES / per_plan;
    let mut volume = Volume { used: 0 };
    for _ in 0..accepted {
        assert!(spend_or_unit(&mut volume, &plan));
    }
    assert!(!spend_or_unit(&mut volume, &plan));
}

#[test]
fn tautology_derivations_share_one_output_budget() {
    let mut executor = Executor::new();
    let eq = executor.ctx.terms.mk_bool(true);
    let neg = executor.ctx.terms.mk_bool(false);
    let term = executor.ctx.terms.mk_var("tautology_volume", Sort::Bool);
    let plan = OrTautologyPlan {
        term,
        eq,
        route: TautRoute::Plain {
            negs: vec![neg; 200],
        },
    };
    let mut volume = Volume { used: 0 };
    for _ in 0..6 {
        assert!(spend_tautology(&mut volume, &plan));
    }
    assert!(!spend_tautology(&mut volume, &plan));
}

#[test]
fn quant_guard_chain_charges_every_shrinking_clause() {
    let mut executor = Executor::new();
    let atom = executor.ctx.terms.mk_bool(true);
    let chain = QuantInstanceChain {
        values: Vec::new(),
        phi: atom,
        guard: Some((atom, vec![atom; 64])),
        body_lit: atom,
        target: atom,
    };
    let mut volume = Volume { used: 0 };
    assert!(spend_quant_chain(&mut volume, &chain));
    assert_eq!(volume.used, 4 + 3 + (65 * 66 / 2) + 2 * 64 + 3);
}

#[test]
fn malformed_or_unit_shape_is_declined() {
    let plan = OrUnitPlan {
        orig: TermId(0),
        disjuncts: vec![TermId(1), TermId(2)],
        eliminations: Vec::new(),
    };
    assert!(!spend_or_unit(&mut Volume { used: 0 }, &plan));
}

#[test]
fn conjunctive_or_charges_every_generated_clause_and_argument() {
    let refutation = |disjunct, conjunct, support| ProvenanceOrAndRefutation {
        disjunct: TermId(disjunct),
        conjunct: TermId(conjunct),
        index: 0,
        lemma: ProvenanceFarkasLemma {
            clause: vec![TermId(conjunct + 10), TermId(support + 10)],
            farkas: FarkasAnnotation::from_ints(&[1, 1]),
            supports: vec![TermId(support)],
        },
    };
    let plan = ProvenanceOrPlan::ConjunctiveConflict(ProvenanceOrAndConflictPlan {
        goal: TermId(1),
        orig: TermId(2),
        disjuncts: vec![TermId(3), TermId(4)],
        authored_sources: vec![TermId(2), TermId(7), TermId(8)],
        refutations: vec![refutation(3, 5, 7), refutation(4, 6, 8)],
    });
    let mut volume = Volume { used: 0 };
    assert!(spend_provenance_or(&mut volume, &plan));
    assert_eq!(volume.used, 25);
}
