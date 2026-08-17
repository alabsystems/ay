// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_metered_premise_authentication_reports_dynamic_edges_and_bytes() {
    let mut terms = TermStore::new();
    let leaves: Vec<TermId> = (0..128)
        .map(|index| terms.mk_var(format!("metered_leaf_{index}"), Sort::Bool))
        .collect();
    let authored = terms.mk_app(Symbol::named("and"), leaves.clone(), Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(leaves[127], None);

    let mut reported_work = 0_usize;
    let mut reported_bytes = 0_usize;
    let authenticated = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[authored],
        &mut |work, bytes| {
            reported_work += work;
            reported_bytes += bytes;
            true
        },
    )
    .expect("a nested authored conjunct should authenticate within an unbounded envelope");

    assert_eq!(authenticated.step_count(), 1);
    assert!(reported_work >= leaves.len());
    assert!(reported_bytes >= leaves.len() * size_of::<TermId>());
}

#[test]
fn test_metered_premise_authentication_can_stop_on_dynamic_edge_payload() {
    let mut terms = TermStore::new();
    let leaves: Vec<TermId> = (0..256)
        .map(|index| terms.mk_var(format!("metered_cutoff_leaf_{index}"), Sort::Bool))
        .collect();
    let authored = terms.mk_app(Symbol::named("and"), leaves.clone(), Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(leaves[255], None);

    let edge_payload = leaves.len() * size_of::<TermId>();
    let mut saw_edge_payload = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[authored],
        &mut |_, bytes| {
            if bytes >= edge_payload {
                saw_edge_payload = true;
                false
            } else {
                true
            }
        },
    )
    .expect_err("the caller must be able to stop before accepting a large edge payload");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(saw_edge_payload);
}

#[test]
fn test_metered_premise_authentication_debits_private_bv_replay_budget() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("metered_bv16", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), vec![value, value], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let clause = vec![equality, negated];
    assert!(crate::bv_bitblast_requires_proof_producer(&terms, &clause));

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", clause, TheoryLemmaKind::BvBitBlast);
    let mut saw_private_budget = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if work
                == usize::try_from(crate::MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA)
                    .expect("published work fits usize")
                && bytes == crate::MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
            {
                saw_private_budget = true;
                false
            } else {
                true
            }
        },
    )
    .expect_err("the aggregate envelope must be debited before private BV replay");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(saw_private_budget);
}

#[test]
fn test_bv_classifier_meter_is_debited_before_budget_classification() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("metered_bv_classifier", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), vec![value, value], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let clause = vec![equality, negated];

    // Nine proof-producing lemmas exceed the private replay aggregate cap. A callback rejecting
    // the classifier debit must observe ResourceLimit before unmetered classification reports it.
    let mut proof = Proof::new();
    for _ in 0..9 {
        proof.add_theory_lemma_with_kind("BV", clause.clone(), TheoryLemmaKind::BvBitBlast);
    }
    let authentication_stats =
        meter_authentication_payload(&proof, &terms, None, None, None, Some(&[]), &mut |_, _| {
            true
        })
        .expect("small payload census should fit usize");
    let classifier_charge =
        proof_producing_bv_classifier_charge(&proof, authentication_stats.aggregate)
            .expect("small classifier charge should fit usize");
    assert!(classifier_charge.0 > 0);
    assert!(classifier_charge.1 > 0);

    let mut saw_classifier_charge = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if (work, bytes) == classifier_charge {
                saw_classifier_charge = true;
                false
            } else {
                true
            }
        },
    )
    .expect_err("classification must not run before its caller-owned debit");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(saw_classifier_charge);
}

#[test]
fn test_semantic_meter_charges_repeated_edge_matching_quadratically() {
    let step = ProofStep::Step {
        rule: AletheRule::AndNeg,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    let payload = PayloadStats {
        work: 257,
        bytes: 4096,
        unfolded_work: 257,
        order_assignments: 0,
    };
    let (work, bytes) = semantic_validator_charge(&step, payload, SemanticChargeClass::General)
        .expect("small checked products should fit usize");
    assert!(work >= 257 * 257);
    assert!(bytes >= payload.bytes);
}

/// The resolution route is accounted by `binary_resolution_charge` /
/// `chain_resolution_charge`, never by the generic recursive product: those
/// validators compare decoded literals by `TermId` and never recurse into a
/// literal's arguments.
///
/// The measured consequence of the product estimate: on
/// `QF_AX/storecomm/storecomm_t1_np_nf_ai_00020_001.cvc` a 153-literal
/// `th_resolution` was pre-charged 7,783,776 work, and such steps consumed
/// 343,825,101 of the 350,000,000 envelope before one more was refused.
#[test]
fn resolution_route_defers_to_the_dedicated_resolution_accountants() {
    let mut terms = TermStore::new();
    let atom = terms.mk_var("resolution_route_atom", Sort::Bool);
    let payload = PayloadStats {
        work: 6_638,
        bytes: 91_442,
        unfolded_work: 1_165,
        order_assignments: 0,
    };

    for step in [
        ProofStep::Resolution {
            clause: vec![atom],
            pivot: atom,
            clause1: ProofId(0),
            clause2: ProofId(1),
        },
        ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![atom],
            premises: vec![ProofId(0), ProofId(1)],
            args: Vec::new(),
        },
        ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: vec![atom],
            premises: vec![ProofId(0), ProofId(1), ProofId(2)],
            args: Vec::new(),
        },
    ] {
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::ResolutionRoute
        );
        assert_eq!(
            semantic_validator_charge(&step, payload, SemanticChargeClass::ResolutionRoute),
            Ok((0, 0))
        );
    }

    // The exemption is only sound because leading-not decoding is now paid by
    // the dedicated accountants: both must strictly increase with the step's
    // unfolded literal payload.
    let flat = binary_resolution_charge(4, 4, 4, 0).expect("charge fits usize");
    let deep = binary_resolution_charge(4, 4, 4, 1_000).expect("charge fits usize");
    assert_eq!(deep.0, flat.0 + 4_000);

    // The binary precharge now covers only the GUARANTEED decode+sort of the
    // three clauses (linear-log in `left + right + conclusion`) plus the
    // leading-not decode term. The pivot SEARCH — formerly the `input*(total+1)`
    // scan precharged here — is decided by
    // `checker::resolution::argfree_binary_resolution_metered`, which finds the
    // pivot in O(total) on the clean case and debits any exhaustive fallback
    // trial-by-trial. So the precharge no longer carries the width term. The
    // measured step that used to exhaust the byte envelope is 23 + 23 -> 304.
    let (measured_work, measured_bytes) =
        binary_resolution_charge(23, 23, 304, 0).expect("charge fits usize");
    let total = 23 + 23 + 304;
    assert_eq!(measured_bytes, total * 4 * size_of::<(TermId, bool)>());
    assert!(measured_bytes < 12 * 1024);
    assert_eq!(
        measured_work,
        sort_comparison_bound(23).unwrap() * 2
            + sort_comparison_bound(304).unwrap()
            // The fourth sort bound covers the argument-directed resolvent sort.
            + sort_comparison_bound(total).unwrap()
    );
    // Parity: the precharge still grows with the clause widths (via the sort
    // bounds and decoded-set bytes), so a wider binary resolution still consumes
    // more budget even before its metered search runs.
    let wider = binary_resolution_charge(24, 23, 304, 0).expect("charge fits usize");
    assert!(wider.0 > measured_work && wider.1 > measured_bytes);

    let derived: Vec<Option<Vec<TermId>>> = vec![Some(vec![atom, atom]); 4];
    let premises = vec![ProofId(0), ProofId(1), ProofId(2), ProofId(3)];
    let flat_chain =
        chain_resolution_charge(&premises, &derived, 2, false, 0).expect("charge fits usize");
    let deep_chain =
        chain_resolution_charge(&premises, &derived, 2, false, 1_000).expect("charge fits usize");
    assert_eq!(deep_chain.0, flat_chain.0 + (4 * 4 + 256 + 1) * 1_000);
}

/// The EUF identity/congruence family (`refl`/`symm`/`trans`/`cong`/
/// `eq_transitive`/`eq_congruent`/`eq_congruent_pred`, as Alethe steps AND as
/// the `Euf*` theory lemmas) routes to `EufIdentityRoute`, not `General`. Their
/// strict validators compare terms by `TermId` identity and never descend into
/// argument subterms, so their charge must be linear in the step's reachable
/// DAG, not quadratic in the tree-unfolded payload.
#[test]
fn euf_identity_family_routes_to_the_dag_bounded_class() {
    let terms = TermStore::new();
    let step_rules = [
        AletheRule::Refl,
        AletheRule::Symm,
        AletheRule::Trans,
        AletheRule::Cong,
        AletheRule::EqTransitive,
        AletheRule::EqCongruent,
        AletheRule::EqCongruentPred,
    ];
    for rule in step_rules {
        let label = format!("{rule:?}");
        let step = ProofStep::Step {
            rule,
            clause: Vec::new(),
            premises: Vec::new(),
            args: Vec::new(),
        };
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::EufIdentityRoute,
            "{label} must use the DAG-bounded EUF identity route"
        );
    }
    let lemma_kinds = [
        TheoryLemmaKind::EufReflexive,
        TheoryLemmaKind::EufTransitive,
        TheoryLemmaKind::EufCongruent,
        TheoryLemmaKind::EufCongruentPred,
    ];
    for kind in lemma_kinds {
        let step = ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: Vec::new(),
            farkas: None,
            kind,
            lia: None,
        };
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::EufIdentityRoute,
            "{kind:?} must use the DAG-bounded EUF identity route"
        );
    }
}

/// SOUNDNESS-PRESERVING SPEEDUP: an EUF identity step whose argument atoms are
/// deep and internally shared (huge tree-unfolded payload) but whose reachable
/// DAG is small must be charged LINEAR in the DAG, not the square of the
/// unfolded payload. This is exactly the `storecomm` shape whose old `General`
/// `unfolded_work^2` charge exhausted the 350M envelope and withheld a correctly
/// decided UNSAT as `unknown`.
#[test]
fn euf_identity_charge_is_linear_in_dag_not_unfolded_square() {
    let step = ProofStep::Step {
        rule: AletheRule::EqCongruent,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    // A 40-deep internally-shared store-chain argument: small DAG, enormous
    // tree-unfolded payload.
    let deep_atom = PayloadStats {
        work: 512,
        bytes: 8_192,
        unfolded_work: 20_000,
        order_assignments: 0,
    };
    let (work, bytes) =
        semantic_validator_charge(&step, deep_atom, SemanticChargeClass::EufIdentityRoute)
            .expect("linear EUF charge fits usize");
    // Charge is exactly the linear DAG multiple, and CRUCIALLY far below the
    // old unfolded^2 (= 4e8) that used to exhaust the 350M work envelope.
    assert_eq!(work, deep_atom.work * EUF_IDENTITY_WORK_FACTOR);
    assert_eq!(bytes, deep_atom.bytes * EUF_IDENTITY_BYTE_FACTOR);
    assert!(
        work < deep_atom.unfolded_work * deep_atom.unfolded_work,
        "the whole point: the DAG charge must be far below the unfolded square"
    );
    assert!(work < 350_000_000);
}

/// PARITY: the route is not a blanket exemption. A genuinely wide EUF step (large
/// reachable DAG) still grows its charge and can still exhaust the envelope, so
/// the validator's real linear work stays paid.
#[test]
fn euf_identity_charge_still_grows_with_dag_work() {
    let step = ProofStep::Step {
        rule: AletheRule::Trans,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    let narrow = PayloadStats {
        work: 1_000,
        bytes: 1_000,
        unfolded_work: 1,
        order_assignments: 0,
    };
    let wide = PayloadStats {
        work: 1_000_000,
        bytes: 1_000_000,
        unfolded_work: 1,
        order_assignments: 0,
    };
    let (nw, _) = semantic_validator_charge(&step, narrow, SemanticChargeClass::EufIdentityRoute)
        .expect("fits usize");
    let (ww, _) = semantic_validator_charge(&step, wide, SemanticChargeClass::EufIdentityRoute)
        .expect("fits usize");
    assert!(ww > nw, "charge must grow with the step's real DAG work");
    // A 50M-node DAG step is genuinely large and still consumes budget.
    let huge = PayloadStats {
        work: 50_000_000,
        bytes: 1,
        unfolded_work: 1,
        order_assignments: 0,
    };
    let (hw, _) = semantic_validator_charge(&step, huge, SemanticChargeClass::EufIdentityRoute)
        .expect("fits usize");
    assert!(
        hw > 350_000_000,
        "a genuinely huge EUF DAG payload must still exhaust the envelope: {hw}"
    );
}
