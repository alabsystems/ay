// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{FpOp, Proof, ProofStep, TheoryLemmaKind};

use super::super::{recognize_fp_classification, validate_fp_classification, FpVal};
use super::*;
use crate::{check_proof_strict, re_check_bundle_strict, SerializableProofBundle};

struct Fixture {
    terms: TermStore,
    x: TermId,
    y: TermId,
    nx: TermId,
    ny: TermId,
    eq: TermId,
    clause: [TermId; 3],
    assertions: [TermId; 3],
}

impl Fixture {
    fn new(eb: u32, sb: u32, reverse: bool) -> Self {
        let mut terms = TermStore::new();
        let sort = Sort::FloatingPoint(eb, sb);
        let x = terms.mk_var("nan_x", sort.clone());
        let y = terms.mk_var("nan_y", sort);
        let nx = terms.mk_app(Symbol::named("fp.isNaN"), [x], Sort::Bool);
        let ny = terms.mk_app(Symbol::named("fp.isNaN"), [y], Sort::Bool);
        let eq = terms.mk_app(
            Symbol::named("="),
            if reverse { [y, x] } else { [x, y] },
            Sort::Bool,
        );
        let clause = [terms.mk_not(nx), terms.mk_not(ny), eq];
        let assertions = [nx, ny, terms.mk_not(eq)];
        Self {
            terms,
            x,
            y,
            nx,
            ny,
            eq,
            clause,
            assertions,
        }
    }

    fn proof(&self) -> Proof {
        let mut proof = Proof::new();
        let nx = proof.add_assume(self.assertions[0], None);
        let ny = proof.add_assume(self.assertions[1], None);
        let neq = proof.add_assume(self.assertions[2], None);
        let theorem = proof.add_theory_lemma_with_kind(
            "fp",
            self.clause.to_vec(),
            TheoryLemmaKind::FpClassification {
                operation: FpOp::IsNaN,
            },
        );
        let one = proof.add_resolution(vec![self.clause[1], self.eq], self.nx, theorem, nx);
        let equality = proof.add_resolution(vec![self.eq], self.ny, one, ny);
        proof.add_resolution(vec![], self.eq, equality, neq);
        proof
    }

    fn bundle(&self) -> SerializableProofBundle {
        SerializableProofBundle::from_proof(&self.proof(), &self.terms, self.assertions.to_vec())
    }
}

#[test]
fn registered_heads_cannot_authorize_nan_refutation() {
    for name in ["fp.isNaN", "="] {
        let mut fixture = Fixture::new(8, 24, false);
        let proof = fixture.proof();
        assert!(check_proof_strict(&proof, &fixture.terms).is_ok());
        fixture.terms.register_declared_function(name);
        assert!(!in_store(&fixture.terms, ProofId(0), &fixture.clause).unwrap());
        assert!(check_proof_strict(&proof, &fixture.terms).is_err());
    }
}

#[test]
fn nan_identity_fp16_fp32_fp64_permutations_and_closed_offline_proofs() {
    for (eb, sb) in [(5, 11), (8, 24), (11, 53)] {
        for reverse in [false, true] {
            let fixture = Fixture::new(eb, sb, reverse);
            for order in [
                [0, 1, 2],
                [0, 2, 1],
                [1, 0, 2],
                [1, 2, 0],
                [2, 0, 1],
                [2, 1, 0],
            ] {
                let clause = order.map(|i| fixture.clause[i]);
                assert!(in_store(&fixture.terms, ProofId(0), &clause).unwrap());
                assert!(validate_fp_classification(&fixture.terms, ProofId(0), &clause).is_ok());
            }
            let proof = fixture.proof();
            let quality = check_proof_strict(&proof, &fixture.terms).unwrap();
            assert_eq!(quality.trust_count, 0);
            assert_eq!(quality.resolution_count, 3);
            let bytes = serde_json::to_vec(&fixture.bundle()).unwrap();
            let restored: SerializableProofBundle = serde_json::from_slice(&bytes).unwrap();
            let checked = re_check_bundle_strict(&restored).unwrap();
            assert_eq!(checked.assume_terms, fixture.assertions.to_vec());
            assert_eq!(checked.quality.trust_count, 0);
            // All three authored roots are used; the structural equality is
            // derived by checked theory+resolution, never installed as Assume.
            assert!(!proof.steps.iter().any(|step| matches!(
                step, ProofStep::Assume(term) if *term == fixture.eq
            )));
        }
    }
}

#[test]
fn nan_identity_requires_exact_antecedents_endpoints_polarities_and_arity() {
    let mut fixture = Fixture::new(8, 24, false);
    let z = fixture.terms.mk_var("nan_z", Sort::FloatingPoint(8, 24));
    let xz = fixture
        .terms
        .mk_app(Symbol::named("="), [fixture.x, z], Sort::Bool);
    let [not_x, not_y, eq] = fixture.clause;
    for clause in [
        vec![not_x, eq],
        vec![not_x, not_y, eq, fixture.terms.false_term()],
        vec![not_x, not_x, eq],
        vec![fixture.nx, not_y, eq],
        vec![not_x, not_y, fixture.assertions[2]],
        vec![not_x, not_y, xz],
    ] {
        assert!(!in_store(&fixture.terms, ProofId(0), &clause).unwrap());
        assert!(!recognize_fp_classification(&fixture.terms, &clause));
    }
    let missing = [not_x, not_y, TermId(u32::MAX)];
    assert!(matches!(
        in_store(&fixture.terms, ProofId(0), &missing),
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
}

#[test]
fn nan_identity_does_not_alias_indexed_names_ieee_equality_or_other_classes() {
    for op in [
        Symbol::indexed("fp.isNaN", vec![0]),
        Symbol::named("fp.isZero"),
        Symbol::named("fp.isInfinite"),
        Symbol::named("fp.isNaN_extra"),
    ] {
        let mut fixture = Fixture::new(8, 24, false);
        let px = fixture.terms.mk_app(op.clone(), [fixture.x], Sort::Bool);
        let py = fixture.terms.mk_app(op, [fixture.y], Sort::Bool);
        let clause = [
            fixture.terms.mk_not(px),
            fixture.terms.mk_not(py),
            fixture.eq,
        ];
        assert!(!in_store(&fixture.terms, ProofId(0), &clause).unwrap());
        assert!(!recognize_fp_classification(&fixture.terms, &clause));
    }
    for op in [Symbol::indexed("=", vec![0]), Symbol::named("fp.eq")] {
        let mut fixture = Fixture::new(8, 24, false);
        let equality = fixture.terms.mk_app(op, [fixture.x, fixture.y], Sort::Bool);
        let clause = [fixture.clause[0], fixture.clause[1], equality];
        assert!(!in_store(&fixture.terms, ProofId(0), &clause).unwrap());
        assert!(!recognize_fp_classification(&fixture.terms, &clause));
    }
}

#[test]
fn nan_identity_malformed_sorts_and_snapshot_signatures_never_gain_authority() {
    let fixture = Fixture::new(8, 24, false);
    // The helper handles bad local sorts without recursive sort comparisons.
    // Full snapshot replay additionally checks global format limits/signatures.
    for bad in [
        Sort::Int,
        Sort::FloatingPoint(8, 23),
        Sort::FloatingPoint(1, 24),
    ] {
        let mut bundle = fixture.bundle();
        bundle.term_entries[fixture.y.index()].1 = bad;
        let terms = TermStore::from_entries(
            bundle.term_entries.clone(),
            bundle.true_term,
            bundle.false_term,
            bundle.var_counter,
        );
        assert!(!in_store(&terms, ProofId(0), &fixture.clause).unwrap());
        assert!(re_check_bundle_strict(&bundle).is_err());
    }
    for term in [fixture.nx, fixture.clause[0], fixture.eq] {
        let mut bundle = fixture.bundle();
        bundle.term_entries[term.index()].1 = Sort::Int;
        assert!(re_check_bundle_strict(&bundle).is_err());
    }
    for (eb, sb) in [(1, 24), (8, 1), (65, 24), (8, (1 << 20) + 1)] {
        let mut bundle = fixture.bundle();
        bundle.term_entries[fixture.x.index()].1 = Sort::FloatingPoint(eb, sb);
        bundle.term_entries[fixture.y.index()].1 = Sort::FloatingPoint(eb, sb);
        assert!(re_check_bundle_strict(&bundle).is_err());
    }
    let mut bad_descendant = fixture.bundle();
    bad_descendant.term_entries[fixture.x.index()].0 =
        TermData::App(Symbol::named("fp.neg"), vec![TermId(u32::MAX)]);
    let shallow = TermStore::from_entries(
        bad_descendant.term_entries.clone(),
        bad_descendant.true_term,
        bad_descendant.false_term,
        bad_descendant.var_counter,
    );
    // The exact theorem treats FP-valued endpoints as opaque. The complete
    // bundle's preceding global graph check must still reject this bad child.
    assert!(in_store(&shallow, ProofId(0), &fixture.clause).unwrap());
    assert!(re_check_bundle_strict(&bad_descendant).is_err());
}

#[test]
fn nan_identity_offline_proof_rejects_changed_premises_and_forged_derived_assume() {
    let fixture = Fixture::new(8, 24, false);
    for removed in 0..3 {
        let mut bundle = fixture.bundle();
        bundle.obligation_assertions.remove(removed);
        assert!(re_check_bundle_strict(&bundle).is_err());
        let mut bundle = fixture.bundle();
        bundle.steps[removed] = ProofStep::Assume(fixture.terms.true_term());
        assert!(re_check_bundle_strict(&bundle).is_err());
    }
    let mut forged = fixture.bundle();
    // Step 5 is the derived equality, and is reachable from the empty clause.
    forged.steps[5] = ProofStep::Assume(fixture.eq);
    assert!(re_check_bundle_strict(&forged).is_err());
    let mut changed = fixture.bundle();
    changed.term_entries[fixture.eq.index()].0 =
        TermData::App(Symbol::named("fp.eq"), vec![fixture.x, fixture.y]);
    assert!(re_check_bundle_strict(&changed).is_err());
}

#[test]
fn nan_identity_small_format_truth_is_independent_of_syntactic_recognition() {
    // The existing exact value evaluator is independent of the new matcher.
    // Exhaust all 1024 pairs, including distinct NaN payloads and signs.
    let fixture = Fixture::new(2, 3, false);
    assert!(in_store(&fixture.terms, ProofId(0), &fixture.clause).unwrap());
    let mut distinct_nan_pairs = 0;
    for a in 0..32 {
        for b in 0..32 {
            let x = FpVal::from_bits(a, 2, 3);
            let y = FpVal::from_bits(b, 2, 3);
            assert!(!x.is_nan() || !y.is_nan() || x.structural_eq(&y));
            if x.is_nan() && y.is_nan() {
                assert!(!x.fp_eq(&y));
                distinct_nan_pairs += usize::from(a != b);
            }
        }
    }
    assert!(distinct_nan_pairs > 0);
    let plus_zero = FpVal::from_bits(0, 2, 3);
    let minus_zero = FpVal::from_bits(16, 2, 3);
    assert!(plus_zero.is_zero() && minus_zero.is_zero());
    assert!(!plus_zero.structural_eq(&minus_zero));
    let plus_inf = FpVal::from_bits(12, 2, 3);
    let minus_inf = FpVal::from_bits(28, 2, 3);
    assert!(plus_inf.is_infinite() && minus_inf.is_infinite());
    assert!(!plus_inf.structural_eq(&minus_inf));
}
