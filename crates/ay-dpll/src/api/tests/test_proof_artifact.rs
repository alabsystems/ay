// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the consumer-facing proof artifact API (#6354).
//!
//! Verifies that `export_last_unsat_artifact` returns correct quality metrics
//! and restricted-rule-subset compatibility flags for pure Boolean, QF_UF, and arithmetic cases.

use crate::api::proofs::strict_verdict_from_result;
use crate::api::*;
use ay_core::{AletheRule, ProofStep, Symbol, TheoryLemmaKind};

#[test]
fn finite_enum_artifact_is_native_strict_and_explicitly_holey_on_alethe_wire() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfDt);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-datatype Unit ((u0) (u1) (u2)))
            (declare-const p0 Unit)
            (declare-const p1 Unit)
            (declare-const p2 Unit)
            (declare-const p3 Unit)
            (assert (not (= p0 p1)))
            (assert (not (= p0 p2)))
            (assert (not (= p0 p3)))
            (assert (not (= p1 p2)))
            (assert (not (= p1 p3)))
            (assert (not (= p2 p3)))
            "#,
        )
        .expect("parse direct finite-enum clique");

    assert!(solver.check_sat().is_unsat());
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("direct finite-enum clique must export its authenticated surface");
    assert!(
        artifact.alethe.contains(":rule hole"),
        "{}",
        artifact.alethe
    );
    assert!(
        !artifact.alethe.contains(":rule dt_enum_pigeonhole"),
        "{}",
        artifact.alethe
    );
    assert!(artifact.quality.is_complete(), "{}", artifact.quality);
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));
    assert!(!artifact.restricted_rule_subset);
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(())
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Err(ProofAcceptanceError::NotRestrictedRuleSubset)
    );

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("native finite-enum proof must remain offline-recheckable");
    let checked = re_check_bundle_strict(&bundle).expect("strictly recheck native bundle");
    assert_eq!(checked.assume_terms.len(), 6);
}

#[test]
fn surface_less_finite_enum_declines_alethe_but_exports_native_bundle() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfDt);
    solver.set_produce_proofs(true);
    let mut deep_true = "true".to_string();
    for _ in 0..300 {
        deep_true = format!("(not {deep_true})");
    }
    let script = format!(
        "(declare-datatype Unit ((u0) (u1) (u2)))\n\
         (declare-const p0 Unit)\n\
         (declare-const p1 Unit)\n\
         (declare-const p2 Unit)\n\
         (declare-const p3 Unit)\n\
         (assert {deep_true})\n\
         (assert (distinct p0 p1))\n\
         (assert (not (= p0 p2)))\n\
         (assert (not (= p0 p3)))\n\
         (assert (not (= p1 p2)))\n\
         (assert (not (= p1 p3)))\n\
         (assert (not (= p2 p3)))\n"
    );
    solver
        .parse_smtlib2(&script)
        .expect("parse surface-less finite-enum clique");

    assert!(solver.check_sat().is_unsat());
    assert!(solver.export_last_proof_alethe().is_none());
    assert!(solver.export_last_unsat_artifact().is_none());
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("sealed native authority does not depend on an Alethe surface");
    let checked = re_check_bundle_strict(&bundle).expect("strictly recheck surface-less bundle");
    assert_eq!(checked.assume_terms.len(), 6);
}

/// A native API assertion of literal `false` is already an empty-clause
/// obligation. It must still publish a concrete, strictly checked artifact;
/// consumers must not have to synthesize proof metadata for this fast path.
#[test]
fn artifact_literal_false_is_present_and_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);

    let false_term = solver.bool_const(false);
    solver.assert_term(false_term);

    assert!(solver.check_sat().is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("literal false UNSAT must publish a proof artifact");
    assert!(!artifact.alethe.is_empty(), "Alethe text must be non-empty");
    assert!(
        artifact.quality.is_complete(),
        "literal false proof must have zero trust/hole: {}",
        artifact.quality,
    );
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "literal false artifact must pass strict checking: {:?}",
        artifact.strict_verdict,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// pure Boolean contradiction: p AND NOT p.
/// The proof should be trust-free and restricted-rule-subset.
#[test]
fn artifact_qf_bool_accepts_strict_and_restricted_subset() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(!artifact.alethe.is_empty(), "Alethe text must be non-empty");
    assert!(
        artifact.quality.is_complete(),
        "pure Boolean proof must have zero trust/hole: {}",
        artifact.quality,
    );
    assert!(
        artifact.restricted_rule_subset,
        "pure Boolean proof must be restricted-rule-subset: {}",
        artifact.quality,
    );
    assert!(
        artifact
            .lrat_certificate
            .as_ref()
            .is_some_and(|bytes| !bytes.is_empty()),
        "pure Boolean artifact should carry non-empty LRAT bytes",
    );
    assert!(
        artifact.farkas_certificates.is_empty(),
        "pure Boolean proof should not export Farkas certificates",
    );
    match &artifact.strict_verdict {
        StrictProofVerdict::Verified(quality) => {
            assert!(
                quality.is_complete(),
                "pure Boolean strict proof must remain complete: {quality}",
            );
        }
        StrictProofVerdict::Rejected(reason) => {
            panic!("pure Boolean proof must pass strict validation, got: {reason}");
        }
    }
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "pure Boolean artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Ok(()),
        "pure Boolean artifact should be acceptable in restricted-rule-subset mode",
    );
}

/// DEDUCTIVE_CHECKS's zero-arity spec-function path registers the function as a Bool
/// constant, asserts its exact body definition at base scope, and checks the
/// caller's negated postcondition in a pushed scope. The refutation must be
/// reconstructed from those authored roots; a synthetic `trust` leaf is not a
/// certificate for the definition-to-result implication.
#[test]
fn zero_arity_bool_spec_definition_in_push_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);

    let spec_value = solver.declare_const("crate::m::f", Sort::Bool);
    let result = solver.declare_const("target::result", Sort::Bool);

    // `f() -> bool { true }` and the caller's return-value binding.
    solver.assert_term(spec_value);
    let result_is_spec = solver.eq(result, spec_value);
    solver.assert_term(result_is_spec);

    solver.push();
    let negated_postcondition = solver.not(result);
    solver.assert_term(negated_postcondition);

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "Bool spec-definition implication must publish certified UNSAT, got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("strict Bool definition proof artifact");
    assert!(
        matches!(artifact.strict_verdict, StrictProofVerdict::Verified(ref q) if q.is_complete()),
        "strict checker rejected Bool definition proof: {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
}

/// End-to-end SerializableProofBundle round-trip: a LIA contradiction
/// `x = 0 /\ x < 0` is solved to UNSAT, exported as a portable bundle,
/// round-tripped through JSON, and re-checked OFFLINE via
/// [`ay_proof::re_check_bundle_strict`] — with NO solver run and no access to the
/// producer's term store. This is the genuinely-external proof re-check: the
/// verdict rests on a checked proof object, not on re-running the solver.
///
/// Also asserts the proof's `assume` axiom set equals the bundle's
/// `obligation_assertions`, so a consumer can soundly bind the proof to the
/// obligation it discharges.
#[test]
fn bundle_export_roundtrip_offline_recheck_lia() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let eq0 = solver.eq(x, zero);
    let lt0 = solver.lt(x, zero);
    solver.assert_term(eq0);
    solver.assert_term(lt0);

    assert!(
        solver.check_sat().is_unsat(),
        "x = 0 /\\ x < 0 must be UNSAT"
    );

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("bundle must be present after UNSAT");
    assert_eq!(bundle.schema, PROOF_BUNDLE_SCHEMA);
    assert!(!bundle.steps.is_empty(), "bundle must carry proof steps");
    assert!(
        !bundle.term_entries.is_empty(),
        "bundle must carry the term snapshot"
    );

    // Round-trip the bundle through JSON, exactly as a certificate would embed it.
    let json = serde_json::to_string(&bundle).expect("bundle serializes to JSON");
    let restored: SerializableProofBundle =
        serde_json::from_str(&json).expect("bundle deserializes from JSON");

    // OFFLINE strict re-check: rebuild a checker-only store + proof and validate,
    // with no solver and no producer term store.
    let recheck = re_check_bundle_strict(&restored)
        .expect("offline strict re-check must accept the embedded proof");
    assert!(
        recheck.quality.is_complete(),
        "the LIA refutation must be trust/hole-free under strict re-check: {}",
        recheck.quality,
    );

    // The proof's assume axioms must equal the asserted obligation (set-equal),
    // so the offline check is genuinely about THIS obligation and nothing else.
    use std::collections::BTreeSet;
    let assume_set: BTreeSet<u32> = recheck.assume_terms.iter().map(|t| t.0).collect();
    let oblig_set: BTreeSet<u32> = restored.obligation_assertions.iter().map(|t| t.0).collect();
    assert_eq!(
        assume_set, oblig_set,
        "proof assume axioms must match the bundle obligation assertions \
         (assume={assume_set:?}, obligation={oblig_set:?})"
    );
}

#[test]
fn assuming_unsat_artifact_and_bundle_use_the_complete_authored_scope() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("assuming_bundle_p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    assert!(solver.check_sat_assuming(&[not_p]).is_unsat());

    let strict = solver
        .last_strict_proof_quality()
        .expect("proof must be available")
        .expect("the temporary authored assumption must be in strict scope");
    assert!(strict.is_complete());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after assumption-based UNSAT");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("bundle must be present after assumption-based UNSAT");
    assert!(bundle.obligation_assertions.contains(&p.id()));
    assert!(bundle.obligation_assertions.contains(&not_p.id()));
    let recheck = re_check_bundle_strict(&bundle)
        .expect("offline checking must authenticate the temporary assumption");
    assert!(recheck.quality.is_complete());

    use std::collections::BTreeSet;
    let assume_set: BTreeSet<u32> = recheck.assume_terms.iter().map(|term| term.0).collect();
    let obligation_set: BTreeSet<u32> = bundle
        .obligation_assertions
        .iter()
        .map(|term| term.0)
        .collect();
    assert_eq!(assume_set, obligation_set);
}

#[test]
fn assuming_rounding_mode_domain_axioms_remain_certified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);

    let rm_sort = Sort::Uninterpreted("RoundingMode".to_string());
    let modes: Vec<Term> = (0..6)
        .map(|index| solver.declare_const(&format!("proof_rm_{index}"), rm_sort.clone()))
        .collect();
    let six_distinct = solver.distinct(&modes);
    assert!(solver.check_sat_assuming(&[six_distinct]).is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("RM assumption proof must be available");
    assert!(
        matches!(artifact.strict_verdict, StrictProofVerdict::Verified(ref quality)
            if quality.is_complete()),
        "generated RM domain coverage must remain a certified lemma: {:?}",
        artifact.strict_verdict
    );

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("RM assumption bundle must be available");
    let recheck = re_check_bundle_strict(&bundle)
        .expect("offline checking must accept certified RM coverage");
    assert!(recheck.quality.is_complete());
    assert_eq!(bundle.obligation_assertions, vec![six_distinct.id()]);
    assert_eq!(recheck.assume_terms, vec![six_distinct.id()]);
}

/// A datatype-valued store disequality must be discharged through a
/// provenance-bound array-extensionality schema and remain independently
/// checkable after export.
/// Storing the value already present at an index leaves the array unchanged, so
/// the asserted disequality is UNSAT. The equality is built as a raw core term
/// because the public frontend correctly simplifies this identity eagerly;
/// this regression targets the late executor lane used by internally generated
/// array terms after frontend elaboration.
#[test]
fn bundle_export_rechecks_datatype_array_extensionality() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-datatype D ((left) (right)))
            (declare-const base (Array Int D))
            (declare-const i Int)
            "#,
        )
        .expect("datatype-array declarations must parse");

    let base = solver
        .executor
        .context()
        .symbol_info_by_identity("base")
        .and_then(|info| info.term)
        .expect("base must be declared");
    let index = solver
        .executor
        .context()
        .symbol_info_by_identity("i")
        .and_then(|info| info.term)
        .expect("index must be declared");
    let left = solver
        .executor
        .context()
        .symbol_info_by_identity("left")
        .and_then(|info| info.term)
        .expect("left constructor must have a term");
    let terms = &mut solver.executor.context_mut().terms;
    let array_sort = terms.sort(base).clone();
    let element_sort = terms.sort(left).clone();
    let selected = terms.mk_app(Symbol::named("select"), vec![base, index], element_sort);
    let selected_is_left = terms.mk_app(Symbol::named("="), vec![selected, left], Sort::Bool);
    let stored = terms.mk_app(Symbol::named("store"), vec![base, index, left], array_sort);
    let arrays_equal = terms.mk_app(Symbol::named("="), vec![stored, base], Sort::Bool);
    let arrays_disequal = terms.mk_not(arrays_equal);
    solver.assert_term(solver.wrap_term(selected_is_left));
    solver.assert_term(solver.wrap_term(arrays_disequal));

    assert!(
        solver.check_sat().is_unsat(),
        "storing the existing cell value cannot change an array"
    );
    let proof = solver
        .executor
        .last_proof()
        .expect("proof must be present after UNSAT");
    let terms = solver.executor.terms();
    let introductions: Vec<(TermId, TermId, TermId)> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ArrayExtDiffIntro,
                clause,
                premises,
                args,
            } if clause.is_empty() && premises.is_empty() => match args.as_slice() {
                [witness, array_a, array_b] => Some((*witness, *array_a, *array_b)),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let certified_extensionality_is_present = proof.steps.iter().any(|step| {
        let ProofStep::TheoryLemma {
            clause,
            kind: TheoryLemmaKind::ArrayExtensionality,
            ..
        } = step
        else {
            return false;
        };
        let raw_is_bound = ay_proof::recognize_array_extensionality_chain(terms, clause)
            .is_some_and(|bindings| {
                bindings.iter().all(|&(array_a, array_b, witness)| {
                    introductions
                        .iter()
                        .any(|&(introduced_witness, introduced_a, introduced_b)| {
                            witness == introduced_witness
                                && ((array_a == introduced_a && array_b == introduced_b)
                                    || (array_a == introduced_b && array_b == introduced_a))
                        })
                })
            });
        raw_is_bound
            || introductions.iter().any(|&(witness, array_a, array_b)| {
                ay_proof::recognize_folded_array_extensionality(
                    terms, clause, array_a, array_b, witness,
                )
            })
    });
    let extensionality_debug: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArrayExtensionality,
                ..
            } => Some((
                clause
                    .iter()
                    .map(|&term| render_term_canonical(terms, term))
                    .collect::<Vec<_>>(),
                ay_proof::recognize_array_extensionality_chain(terms, clause),
                introductions
                    .iter()
                    .map(|&(witness, array_a, array_b)| {
                        ay_proof::recognize_folded_array_extensionality(
                            terms, clause, array_a, array_b, witness,
                        )
                    })
                    .collect::<Vec<_>>(),
            )),
            _ => None,
        })
        .collect();
    let assume_debug: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(render_term_canonical(terms, *term)),
            _ => None,
        })
        .collect();
    assert!(
        certified_extensionality_is_present,
        "the exported proof must contain a provenance-bound \
         array-extensionality lemma; extensionality={extensionality_debug:#?}; \
         introductions={introductions:#?}; assumes={assume_debug:#?}",
    );

    assert!(matches!(
        solver
            .executor
            .try_export_last_proof_alethe_for_problem_scope(),
        Some(Err(
            ay_proof::AlethePrintError::UnsupportedArrayExtensionality { .. }
        ))
    ));

    let (strict_checks_before, strict_steps_before) =
        solver.executor.strict_check_counters_for_test();
    let proof_steps = proof.steps.len() as u64;
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");
    assert_eq!(
        solver.executor.strict_check_counters_for_test().0 - strict_checks_before,
        1,
        "artifact fallback must reuse its boundary strict verdict"
    );
    assert_eq!(
        solver.executor.strict_check_counters_for_test().1 - strict_steps_before,
        proof_steps,
        "artifact fallback must walk the native proof exactly once"
    );
    assert_eq!(artifact.alethe.matches(":rule hole").count(), 1);
    assert_eq!(
        artifact
            .alethe
            .matches("(define-fun __ay_ext_diff!")
            .count(),
        1
    );
    assert!(
        !artifact.alethe.contains(":rule arrays_ext")
            && !artifact.alethe.contains(":rule extensionality")
            && !artifact.alethe.contains(":rule array_ext_diff_intro"),
        "{}",
        artifact.alethe
    );
    let final_step = artifact
        .alethe
        .lines()
        .rev()
        .find(|line| line.starts_with("(step "))
        .expect("diagnostic must retain its closing proof step");
    assert!(
        final_step.contains("(cl)") && final_step.contains(":rule resolution"),
        "final proof step is not the expected empty-clause resolution: {final_step}\n{}",
        artifact.alethe,
    );
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(quality)
            if quality.is_complete()),
        "array-extensionality proof must be strict-verified: {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert_eq!(
        artifact.quality.hole_count, 0,
        "native proof quality must not inherit the presentation-only hole"
    );
    assert!(!artifact.restricted_rule_subset);
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Err(ProofAcceptanceError::NotRestrictedRuleSubset)
    );

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("bundle must be present after UNSAT");
    let json = serde_json::to_string(&bundle).expect("bundle serializes to JSON");
    let restored: SerializableProofBundle =
        serde_json::from_str(&json).expect("bundle deserializes from JSON");
    let recheck = re_check_bundle_strict(&restored)
        .expect("offline strict re-check must accept array extensionality");
    assert!(
        recheck.quality.is_complete(),
        "offline array-extensionality proof must be trust/hole-free: {}",
        recheck.quality,
    );
    use std::collections::BTreeSet;
    let assume_set: BTreeSet<u32> = recheck.assume_terms.iter().map(|term| term.0).collect();
    let obligation_set: BTreeSet<u32> = restored
        .obligation_assertions
        .iter()
        .map(|term| term.0)
        .collect();
    assert_eq!(
        assume_set, obligation_set,
        "offline proof assumptions must equal the serialized obligation"
    );
}

/// Datatype declarations are part of the serialized proof obligation. Without
/// them an offline checker cannot distinguish a valid constructor-disjointness
/// lemma from the same syntactic clause over unrelated uninterpreted symbols.
#[test]
fn bundle_export_rechecks_datatype_declaration_context() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-datatype D ((left) (right)))
            (declare-const value D)
            (assert (= value left))
            (assert (= value right))
            "#,
        )
        .expect("datatype disjointness fixture must parse");

    assert!(solver.check_sat().is_unsat());
    let proof = solver
        .executor
        .last_proof()
        .expect("proof must be present after UNSAT");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeDistinct,
                ..
            }
        )),
        "fixture must exercise strict datatype constructor disjointness"
    );
    let strict = solver
        .last_strict_proof_quality()
        .expect("strict verdict must be available")
        .expect("live strict check must receive datatype declarations");
    assert!(strict.is_complete());

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("bundle must be present after UNSAT");
    assert_eq!(
        bundle.datatype_declarations,
        vec![(
            "D".to_string(),
            vec!["left".to_string(), "right".to_string()]
        )]
    );
    let json = serde_json::to_string(&bundle).expect("bundle serializes to JSON");
    let restored: SerializableProofBundle =
        serde_json::from_str(&json).expect("bundle deserializes from JSON");
    let recheck = re_check_bundle_strict(&restored)
        .expect("offline strict re-check must use serialized datatype declarations");
    assert!(recheck.quality.is_complete());
}

/// Simple QF_UF contradiction: a=b, b=c, NOT(a=c).
/// The proof should be trust-free and restricted-rule-subset.
///
/// Uses `parse_smtlib2` to declare an uninterpreted sort, since the Rust API
/// does not yet expose `declare_sort`.
#[test]
fn artifact_qf_uf_accepts_strict_and_restricted_subset() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    solver
        .parse_smtlib2(
            r#"
            (declare-sort U 0)
            (declare-fun a () U)
            (declare-fun b () U)
            (declare-fun c () U)
            (assert (= a b))
            (assert (= b c))
            (assert (not (= a c)))
            "#,
        )
        .expect("SMT-LIB2 parsing should succeed");

    assert!(solver.check_sat().is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(!artifact.alethe.is_empty(), "Alethe text must be non-empty");
    assert!(
        artifact.quality.is_complete(),
        "QF_UF proof must have zero trust/hole: {}",
        artifact.quality,
    );
    assert!(
        artifact.restricted_rule_subset,
        "simple QF_UF proof must be restricted-rule-subset: {}",
        artifact.quality,
    );
    assert!(
        matches!(
            &artifact.strict_verdict,
            StrictProofVerdict::Verified(quality) if quality.is_complete()
        ),
        "QF_UF proof must export a successful strict verdict: {:?}",
        artifact.strict_verdict,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "QF_UF artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Ok(()),
        "QF_UF artifact should be acceptable in restricted-rule-subset mode",
    );
}

/// Simple QF_LRA contradiction: x > 0 AND x < 0.
///
/// The proof should pass strict checking, but restricted-rule-subset support is currently
/// limited to a strict subset that excludes arithmetic theory lemmas.
#[test]
fn artifact_qf_lra_strict_but_not_restricted_subset() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLra);
    solver.set_produce_proofs(true);

    let x = solver.declare_const("x", Sort::Real);
    let zero = solver.real_const(0.0);
    let gt_term = solver.gt(x, zero);
    solver.assert_term(gt_term);
    let lt_term = solver.lt(x, zero);
    solver.assert_term(lt_term);

    assert!(solver.check_sat().is_unsat());

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");

    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "LRA proof must export a successful strict verdict: {:?}",
        artifact.strict_verdict,
    );
    assert!(
        !artifact.restricted_rule_subset,
        "LRA proof should remain outside the restricted-rule-subset subset",
    );
    assert!(
        artifact
            .lrat_certificate
            .as_ref()
            .is_some_and(|bytes| !bytes.is_empty()),
        "LRA artifact should carry non-empty LRAT bytes",
    );
    assert!(
        !artifact.farkas_certificates.is_empty(),
        "LRA artifact should export Farkas certificates",
    );
    assert!(
        artifact
            .farkas_certificates
            .iter()
            .all(|certificate| !certificate.coefficients.is_empty()),
        "exported Farkas certificates should contain coefficients",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
        "LRA artifact should be acceptable in strict mode",
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Err(ProofAcceptanceError::NotRestrictedRuleSubset),
        "LRA artifact should be rejected in restricted-rule-subset mode",
    );
}

/// SAT result returns None for the proof artifact.
#[test]
fn artifact_sat_returns_none() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    solver.assert_term(p);

    assert_eq!(solver.check_sat(), SolveResult::Sat);

    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "artifact must be None after SAT result"
    );
}

/// Proofs disabled returns None for the proof artifact.
#[test]
fn artifact_proofs_disabled_returns_none() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    // Proofs disabled by default.

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    assert!(
        solver.export_last_unsat_artifact().is_none(),
        "artifact must be None when proofs not enabled"
    );
}

/// Individual proof accessor: export_last_proof_alethe returns non-empty text.
#[test]
fn alethe_export_returns_text() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    let alethe = solver
        .export_last_proof_alethe()
        .expect("Alethe text must be present");
    assert!(!alethe.is_empty());
    // Alethe proofs contain assume and step/resolution commands
    assert!(
        alethe.contains("assume") || alethe.contains("step"),
        "Alethe text should contain proof commands"
    );
}

/// Individual proof accessor: last_proof_quality returns metrics.
#[test]
fn quality_accessor_returns_metrics() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());

    let quality = solver
        .last_proof_quality()
        .expect("quality must be present");
    assert!(quality.total_steps > 0);
    assert!(quality.is_complete());
}

/// Negative regression: a whitelisted rule (AllSimplify) that derives an
/// incorrect clause must be rejected by the strict gate even though the
/// diagnostic quality says "complete" and the rule whitelist accepts it.
///
/// This is the key #6541 regression: before the strict gate, this proof would
/// have been restricted_rule_subset=true because `trust_count == 0`, `hole_count == 0`,
/// and AllSimplify is in the whitelist. Now restricted_rule_subset requires
/// check_proof_strict to succeed, which rejects unvalidated generic rules.
#[test]
fn strict_rejection_is_preserved_on_artifact_boundary() {
    use ay_core::{AletheRule, Proof, Sort as CoreSort, TermStore};
    use ay_proof::{check_proof_strict, check_proof_with_quality};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", CoreSort::Bool);
    let not_x = terms.mk_not(x);

    // Build a bogus proof:
    //   assume x
    //   AllSimplify deriving (not x) — this is semantically wrong
    //   resolution on x to derive empty clause
    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let bogus = proof.add_rule_step(AletheRule::AllSimplify, vec![not_x], Vec::new(), Vec::new());
    proof.add_resolution(vec![], x, h0, bogus);

    // Diagnostic (non-strict) quality should say "complete" —
    // no trust, no hole, the proof derives the empty clause.
    let diag = check_proof_with_quality(&proof, &terms)
        .expect("non-strict check should accept this proof");
    assert!(
        diag.is_complete(),
        "diagnostic quality should be complete (no trust/hole): {diag}"
    );

    // Strict checker rejects: AllSimplify is not semantically validated.
    let strict_error = check_proof_strict(&proof, &terms)
        .expect_err("strict checker must reject bogus AllSimplify");
    let strict_error_text = strict_error.to_string();
    let strict_verdict = strict_verdict_from_result(Err(strict_error));
    assert_eq!(
        strict_verdict,
        StrictProofVerdict::Rejected(strict_error_text),
        "artifact boundary must preserve the strict rejection explanation",
    );
}

/// Regression (#trust bounds-VC gap): a trivially-UNSAT CONJUNCTIVE LIA
/// assertion must export a fully verified proof. Top-level and-flattening
/// asserts the conjuncts separately; their assume steps used to be demoted to
/// unverified `trust` steps ("step t0 uses unverified trust rule"), which
/// fail-closed the strict checker on every guarded bounds VC. The conjuncts
/// are now DERIVED from the asserted conjunction via and_pos + th_resolution.
#[test]
fn conjunctive_lia_unsat_proof_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let i = solver.declare_const("i", Sort::Int);
    let c16 = solver.int_const(16);
    let lt = solver.lt(i, c16);
    let ge = solver.ge(i, c16);
    let conj = solver.and(lt, ge);
    solver.assert_term(conj);
    assert!(solver.check_sat().is_unsat());
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "conjunctive LIA proof must be strict-verified, got {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {} \n{}",
        artifact.quality,
        artifact.alethe,
    );
}

/// TrustVC's open-spec u16 obligation pins a wide bitvector before using its
/// mathematical `bv2nat` value.  The bounded semantic proof lane must propagate
/// that exact source pin before sizing the finite domain, then publish an
/// internally replayable (honestly holey on the bv2nat-incapable Alethe wire)
/// certificate.  A satisfiable boundary near-miss must remain SAT.
#[test]
fn pinned_u16_bv2nat_refutation_is_native_strict_and_sat_near_miss_stays_sat() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const result (_ BitVec 16))
            (declare-const x (_ BitVec 16))
            (assert (= x #x9c40))
            (assert (= x result))
            (assert (<= (* (bv2nat x) 2) 65535))
            "#,
        )
        .expect("parse pinned u16 mathematical-arithmetic obligation");

    assert!(solver.check_sat().is_unsat());
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("native strict bv2nat certificate must be present");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(quality) if quality.is_complete()),
        "pinned bv2nat proof must pass native strict replay: {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(artifact.quality.is_complete(), "{}", artifact.quality);
    assert!(
        artifact.alethe.contains(":rule hole"),
        "the unsupported external bv2nat rule must remain an honest hole: {}",
        artifact.alethe,
    );
    assert!(!artifact.restricted_rule_subset);
    let proof = solver
        .last_proof()
        .expect("UNSAT publishes its native proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvLiaTautology,
            ..
        }
    )));

    #[allow(deprecated)]
    let mut near_miss = Solver::new(Logic::All);
    near_miss.set_produce_proofs(true);
    near_miss
        .parse_smtlib2(
            r#"
            (declare-const x (_ BitVec 16))
            (assert (= x #x9c40))
            (assert (<= (* (bv2nat x) 2) 80000))
            "#,
        )
        .expect("parse satisfiable pinned u16 boundary");
    assert!(
        near_miss.check_sat().is_sat(),
        "x=40000 witnesses the exact mathematical boundary"
    );
}

/// Exact integer system emitted by Trust's rational-clearing bridge:
/// `x <= 2 /\ 2*x >= 7`. The LIA producer must orient and normalize its Farkas
/// coefficients against the authored literals before strict replay.
#[test]
fn rational_clearing_lia_conjunction_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);

    let x = solver.declare_const("x", Sort::Int);
    let two = solver.int_const(2);
    let seven = solver.int_const(7);
    let upper = solver.le(x, two);
    let twice_x = solver.mul(two, x);
    let lower = solver.ge(twice_x, seven);
    let violation = solver.and(upper, lower);
    solver.assert_term(violation);

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "cleared rational system must publish certified UNSAT, got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("strict rational-clearing proof artifact");
    assert!(
        matches!(artifact.strict_verdict, StrictProofVerdict::Verified(ref q) if q.is_complete()),
        "strict checker rejected rational-clearing proof: {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
}

/// Comparison normalization must not become proof authority. The solver may
/// internally rewrite `>=`/`>` into swapped `<=`/`<` terms, but a rebuilt
/// complementary-literal refutation must still assume the exact authored
/// conjunction and remain offline-checkable against that obligation.
#[test]
fn normalized_complementary_conjunction_uses_authored_bundle_premise() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const x Int)
            (assert (and (>= x 0) (not (> x 10)) (> x 10)))
            "#,
        )
        .expect("comparison-normalization fixture must parse");

    assert!(solver.check_sat().is_unsat());
    let authored = solver.executor.proof_original_problem_assertions();
    assert_eq!(authored.len(), 1, "fixture has one authored assertion");

    let proof = solver
        .last_proof()
        .expect("proof must be present after UNSAT");
    let assumed: Vec<_> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect();
    assert_eq!(
        assumed, authored,
        "the refutation must assume the authored conjunction, not its normalized derivative"
    );

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");
    assert!(
        matches!(
            artifact.strict_verdict,
            StrictProofVerdict::Verified(ref quality) if quality.is_complete()
        ),
        "authored-root refutation must pass strict checking: {:?}",
        artifact.strict_verdict
    );

    let bundle = solver
        .export_last_unsat_bundle()
        .expect("bundle must be present after UNSAT");
    let recheck = re_check_bundle_strict(&bundle)
        .expect("offline checking must authenticate the authored conjunction");
    assert_eq!(recheck.assume_terms, authored);
}

/// Regression (#trust slice-bounds gap, second export hole): preprocessing
/// variable substitution rewrites a conjunct under a conjunct equality
/// (`(<= n5 i)` under `(= len n5)` becomes `(<= len i)`), so the SAT-level
/// unit matches no conjunct exactly and used to surface as an unverified
/// `trust` step. The export now bridges it: derive the original conjunct and
/// the equality via and_pos, then a Farkas-certified LIA lemma
/// `(cl (not E) (not C) substituted)` resolved to the unit.
#[test]
fn substituted_conjunct_unsat_proof_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let i = solver.declare_const("i", Sort::Int);
    let len = solver.declare_const("len", Sort::Int);
    let n4 = solver.declare_const("n4", Sort::Int);
    let n5 = solver.declare_const("n5", Sort::Int);
    let b3 = solver.declare_const("b3", Sort::Bool);
    let b6 = solver.declare_const("b6", Sort::Bool);
    let lt_i_n4 = solver.lt(i, n4);
    let lt_i_n5 = solver.lt(i, n5);
    let lt_i_len = solver.lt(i, len);
    let ge_i_n5 = solver.ge(i, n5);
    let eq_n4 = solver.eq(n4, len);
    let eq_n5 = solver.eq(n5, len);
    let eq_b3 = solver.eq(b3, lt_i_n4);
    let eq_b6 = solver.eq(b6, lt_i_n5);
    let conj = solver.and_many(&[eq_n4, eq_b3, lt_i_len, eq_n5, eq_b6, ge_i_n5]);
    solver.assert_term(conj);
    assert!(solver.check_sat().is_unsat());
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("artifact must be present after UNSAT");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "substituted-conjunct proof must be strict-verified, got {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {} \n{}",
        artifact.quality,
        artifact.alethe,
    );
}

/// Regression (#trust slice-bounds gap, cross-root substitution): the exact
/// guarded-slice-index VC shape — nested conjunctions asserted as MULTIPLE
/// roots, with a conjunct rewritten under an equality conjunct from a
/// DIFFERENT root by preprocessing variable substitution. The substituted
/// SAT-level unit is derived via and_pos chains from both roots, `cong`
/// (substitution IS congruence), and an orientation-aware equiv_pos1/2
/// tautology — never an unverified trust step.
#[test]
fn cross_root_substituted_conjunct_proof_is_strict_verified() {
    #[allow(deprecated)]
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_proofs(true);
    let i = solver.declare_const("i", Sort::Int);
    let len = solver.declare_const("samples__slice_len", Sort::Int);
    let n4 = solver.declare_const("_4", Sort::Int);
    let n5 = solver.declare_const("_5", Sort::Int);
    let b3 = solver.declare_const("_3", Sort::Bool);
    let b6 = solver.declare_const("_6", Sort::Bool);
    let eq4 = solver.eq(n4, len);
    let lt_i_n4 = solver.lt(i, n4);
    let eq3 = solver.eq(b3, lt_i_n4);
    let lt_i_len = solver.lt(i, len);
    let eq5 = solver.eq(n5, len);
    let lt_i_n5 = solver.lt(i, n5);
    let eq6 = solver.eq(b6, lt_i_n5);
    let ge_i_n5 = solver.ge(i, n5);
    let inner3 = solver.and_many(&[eq5, eq6, ge_i_n5]);
    let inner2 = solver.and_many(&[eq4, eq3, inner3]);
    let inner1 = solver.and_many(&[lt_i_len, inner2]);
    let outer = solver.and_many(&[eq4, eq3, inner1]);
    solver.assert_term(outer);
    assert!(solver.check_sat().is_unsat());
    let artifact = solver.export_last_unsat_artifact().expect("artifact");
    assert!(
        matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
        "cross-root substituted-conjunct proof must be strict-verified, got {:?}\n{}",
        artifact.strict_verdict,
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {} \n{}",
        artifact.quality,
        artifact.alethe,
    );
}

/// Assert the shared post-conditions of a store-permutation refutation.
///
/// The PLAIN-checker call is the load-bearing one. `artifact.strict_verdict`
/// is NOT enough on its own: `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also reports `Verified` when the deferred-trust RESCUE
/// re-discharges an unverified leaf, so it cannot distinguish "the step was
/// checked" from "the step was tolerated". `check_proof_strict_with_datatypes`
/// is the same call `mint_unsat_certificate` makes BEFORE any rescue, and it
/// runs `validate_array_store_permutation`'s full re-derivation: one common
/// base array, equal chain lengths, pairwise-distinct index terms, equal
/// `(index, value)` multisets, and one `(= i_p i_q)` literal per index pair.
fn assert_store_permutation_refutation_is_plainly_checked(solver: &Solver) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the store-permutation \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the array rule, not something else. Read
    // the proof IR, not the printed text: Carcara has no `store_permutation`
    // rule, so the WIRE name is an honest `hole` while AY's own checker
    // validates the kind.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArrayStorePermutation,
                ..
            }
        )),
        "refutation must contain a checker-validated store_permutation lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the QF_AX `storecomm` shape): a STORE
/// COMMUTATION refutation — `i != j` plus a negated equality between two store
/// chains that write the same `(index, value)` pairs in the other order — must
/// export a strictly verified, trust-free proof.
///
/// The eager array lane closes this by level-0 propagation, so no clause-level
/// conflict reaches the SAT trace, `derive_empty_via_level0_rup` declines with
/// `RupNoConflict`, and the reconstruction closes on the whole-problem `trust`
/// fallback. Discharging that clause IS re-proving the problem, so the
/// deferred-trust rescue cannot save it — it re-enters the budgeted
/// `reconfirms_unsat_within` DPLL re-solve, which is where this family burns
/// its time — and the mandatory certification gate publishes `unknown` for a
/// correct `unsat`.
///
/// CORE TRACKING IS PART OF THE FIXTURE, NOT DECORATION. Measured with
/// entry/gate/commit instrumentation on
/// `replace_with_exact_authored_store_permutation_refutation`: the same two
/// assertions WITHOUT `:named` labels and `produce-unsat-cores` never reach
/// the pass at all. On that path the reconstruction ALREADY hands the strict
/// checker a trust-free five-step `ArrayStorePermutation` refutation (two
/// assumes, the lemma, two `th_resolution` steps), the checker accepts it, and
/// the new pass early-returns on its first line — so a fixture without core
/// tracking pins the PRE-EXISTING producer and says nothing about this one.
/// With core tracking the reconstruction instead closes on the whole-problem
/// `trust` step, the strict checker rejects with `step t0 uses unverified
/// trust rule`, and the new pass fires and commits its candidate. One `:named`
/// label plus core production is enough to route the shape there.
#[test]
fn qfax_store_permutation_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAx);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort I 0)
            (declare-sort E 0)
            (declare-const arr (Array I E))
            (declare-const i I)
            (declare-const j I)
            (declare-const x E)
            (declare-const y E)
            (assert (! (distinct i j) :named neq))
            (assert (! (not (= (store (store arr i x) j y)
                               (store (store arr j y) i x))) :named goal))
            "#,
        )
        .expect("store-commutation fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "store commutation under distinct indices is UNSAT (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_store_permutation_refutation_is_plainly_checked(&solver);
}

/// The n-ary arm of the same pass: a THREE-index store chain, whose refutation
/// needs all three authored index disequalities in the lemma clause and a
/// three-link resolution chain to strip them. Instrumented, this reaches the
/// pass with `premises=3` and commits a 9-step candidate, so it exercises the
/// premise-collection, shrink, and resolution-chain loops that the two-index
/// fixture leaves at their trivial size.
#[test]
fn qfax_store_permutation_three_index_chain_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAx);
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort I 0)
            (declare-sort E 0)
            (declare-const arr (Array I E))
            (declare-const i I)
            (declare-const j I)
            (declare-const k I)
            (declare-const x E)
            (declare-const y E)
            (declare-const z E)
            (assert (! (distinct i j) :named nij))
            (assert (! (distinct j k) :named njk))
            (assert (! (distinct i k) :named nik))
            (assert (! (not (= (store (store (store arr i x) j y) k z)
                               (store (store (store arr k z) j y) i x))) :named goal))
            "#,
        )
        .expect("three-index store-permutation fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a three-index store permutation under pairwise-distinct indices is \
         UNSAT (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_store_permutation_refutation_is_plainly_checked(&solver);
}

/// Shared assertion for the two refutation families closed by
/// `replace_with_exact_authored_equality_chain_refutation`'s BV lane and by
/// `replace_with_exact_authored_congruence_refutation`.
///
/// Asserting `artifact.strict_verdict` alone would NOT distinguish "checked"
/// from "tolerated": `strict_verdict_with_deferred_trust` (`api/proofs.rs`)
/// also returns `Verified` from its two RESCUE arms — the whole-problem
/// executor re-solve and the BV re-translation. So this runs the PLAIN
/// `check_proof_strict_with_datatypes` over the exported proof, pins that the
/// accepted step is the expected checker-validated kind, and requires the
/// artifact to be trust- and hole-free.
fn assert_refutation_is_plainly_checked(solver: &Solver, expected: TheoryLemmaKind, what: &str) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the {what} refutation, \
                 got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the rule we claim, not something else.
    // Read the proof IR rather than the printed text: the WIRE rule name can
    // be an honest `hole` where Carcara has no counterpart, while AY's own
    // checker validates the kind.
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if *kind == expected)),
        "the {what} refutation must contain a checker-validated {expected:?} \
         lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0): two authored equalities sharing an opaque
/// endpoint and pinning it to two DIFFERENT BV constants must export a
/// strictly verified, trust-free proof.
///
/// `(select a i)` is opaque to both the array and the bitvector lane, so the
/// only fact the refutation needs is that `#x05` and `#x06` differ. AY computed
/// `unsat` here (z3 5.0.0 agrees) but could not certify it: the sole endpoint
/// refuter reachable from `replace_with_exact_authored_equality_chain_refutation`
/// was the INTEGER divisibility recognizer, which declines on BV constants, so
/// the reconstruction fell through to the whole-problem `trust` closer and the
/// mandatory publication gate degraded the verdict to `unknown`.
#[test]
fn qfabv_shared_endpoint_bv_constant_mismatch_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const i (_ BitVec 8))
            (assert (= (select a i) #x05))
            (assert (= (select a i) #x06))
            "#,
        )
        .expect("shared-endpoint BV fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "one array cell cannot hold both #x05 and #x06 (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(&solver, TheoryLemmaKind::BvBitBlast, "shared-endpoint");
}

/// The same endpoint lane over a term the BV theory could in principle
/// evaluate but the refutation does not need to: `(bvudiv x #x03)` is held
/// OPAQUE and only the constant mismatch is re-derived. This is the arm that
/// matters for operators outside the strict checker's bit-blast fragment —
/// `bvudiv` has no gate in the proof-producing kernel, so a refutation that
/// tried to blast it could not be checked at all.
#[test]
fn qfbv_shared_endpoint_over_opaque_udiv_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfBv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const x (_ BitVec 8))
            (assert (= (bvudiv x #x03) #x02))
            (assert (= (bvudiv x #x03) #x03))
            "#,
        )
        .expect("opaque-udiv fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "x/3 cannot be both #x02 and #x03 (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(&solver, TheoryLemmaKind::BvBitBlast, "opaque-udiv");
}

/// Regression (#trust-count→0): `x = y` plus `f(x) != f(y)` must export a
/// strictly verified, trust-free CONGRUENCE proof.
///
/// The EUF lane closes this by level-0 propagation, so no clause-level conflict
/// reaches the SAT trace and the reconstruction falls through to the
/// whole-problem `trust` closer. Discharging that clause IS re-proving the
/// problem, so the deferred-trust rescue cannot help and the gate correctly
/// refused ("step t1 uses unverified trust rule").
#[test]
fn qfufbv_unary_congruence_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfUfbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= x y))
            (assert (not (= (f x) (f y))))
            "#,
        )
        .expect("unary congruence fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "congruence forbids f(x) != f(y) when x = y (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(&solver, TheoryLemmaKind::EufCongruent, "congruence");
}

/// The n-ary arm of the same pass: a BINARY function needs a premise literal
/// for EVERY argument position, so this exercises the premise-collection and
/// resolution-chain loops the unary fixture leaves at their trivial size. The
/// strict `EufCongruent` validator requires exactly one negated-equality
/// premise per position, each connecting that position's two arguments.
#[test]
fn qfufbv_binary_congruence_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfUfbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun g ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
            (declare-const x1 (_ BitVec 8))
            (declare-const x2 (_ BitVec 8))
            (declare-const y1 (_ BitVec 8))
            (declare-const y2 (_ BitVec 8))
            (assert (= x1 y1))
            (assert (= x2 y2))
            (assert (not (= (g x1 x2) (g y1 y2))))
            "#,
        )
        .expect("binary congruence fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "congruence forbids g(x1,x2) != g(y1,y2) when the arguments agree \
         pairwise (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::EufCongruent,
        "binary congruence",
    );
}

/// Assert the shared post-conditions of an exact-IEEE-754 FP refutation.
///
/// The PLAIN-checker call is the load-bearing one, for the same reason as
/// [`assert_store_permutation_refutation_is_plainly_checked`]:
/// `artifact.strict_verdict` alone cannot distinguish "the step was CHECKED"
/// from "the step was TOLERATED", because `strict_verdict_with_deferred_trust`
/// also returns `Verified` from its rescue arms.
/// `check_proof_strict_with_datatypes` is the call `mint_unsat_certificate`
/// makes BEFORE any rescue, and it runs `validate_fp_ground_eval`'s full
/// re-derivation: the clause's own ground bindings are substituted in, and the
/// result is evaluated by an independent correctly-rounded exact
/// integer/rational IEEE-754 kernel over EVERY assignment of the residual
/// variables.
fn assert_fp_ground_eval_refutation_is_plainly_checked(solver: &Solver) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the exact-IEEE-754 \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the exact-evaluation rule. Read the proof
    // IR, not the printed text: Carcara has no `fp_ground_eval` rule, so the
    // WIRE name is an honest `hole` while AY's own checker validates the kind.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::FpGroundEval,
                ..
            }
        )),
        "refutation must contain a checker-validated fp_ground_eval lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#fp-ground-cert): a GROUND floating-point refutation whose only
/// content is ARITHMETIC — `0 + 0 = 0` under `roundNearestTiesToEven` — must
/// export a strictly verified, trust-free proof.
///
/// `FpClassification` cannot reach this: its bounded evaluator implements the
/// sign/class/comparison fragment only and fails closed on EVERY FP arithmetic
/// operator, so the one-literal refutation carried `TheoryLemmaKind::Generic`,
/// the strict checker rejected it with "step t1 uses unsupported theory lemma
/// kind Generic in strict mode", and the mandatory certification gate published
/// `unknown` for a correct `unsat` (z3 5.0.0 agrees it is `unsat`).
#[test]
fn qffp_ground_arithmetic_refutation_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfFp);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (assert (not (fp.eq (fp.add RNE (_ +zero 8 24) (_ +zero 8 24))
                                (_ +zero 8 24))))
            "#,
        )
        .expect("ground FP arithmetic fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "denying 0 + 0 = 0 in Float32 is UNSAT (z3 5.0.0 agrees), got \
         {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_fp_ground_eval_refutation_is_plainly_checked(&solver);
}

/// The CONVERSION arm of the same lane: `((_ to_fp 8 24) RNE bv)` reads its
/// bitvector operand as a SIGNED integer, so the 32-bit all-ones pattern is
/// `-1.0f`, not `2^32 - 1`. The checker re-derives that with its own exact
/// two's-complement decode and correctly-rounded conversion.
#[test]
fn qffp_signed_bitvector_conversion_refutation_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfFp);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (assert (not (fp.eq
                ((_ to_fp 8 24) RNE #b11111111111111111111111111111111)
                (fp #b1 #b01111111 #b00000000000000000000000))))
            "#,
        )
        .expect("signed BV-to-FP fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "the signed 32-bit all-ones pattern converts to -1.0f (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_fp_ground_eval_refutation_is_plainly_checked(&solver);
}

/// The SUBSTITUTION arm: the clause's own `(not (= v ground))` literals bind
/// the variables, and only after that is the residual literal ground. Nothing
/// in this input is a closed formula — `x` and `y` are Float32 variables, far
/// too wide to enumerate — so this fixture fails if the binding step is
/// removed, while the two above do not.
#[test]
fn qffp_bound_variable_refutation_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfFp);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const x (_ FloatingPoint 8 24))
            (declare-const y (_ FloatingPoint 8 24))
            (assert (= x (fp #b0 #b01111111 #b00000000000000000000000)))
            (assert (= y (fp #b0 #b10000000 #b00000000000000000000000)))
            (assert (fp.eq x y))
            "#,
        )
        .expect("bound-variable FP fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "x = 1.0 and y = 2.0 cannot be fp.eq (z3 5.0.0 agrees), got \
         {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_fp_ground_eval_refutation_is_plainly_checked(&solver);
}

/// Assert the shared post-conditions of a string-length arithmetic refutation.
///
/// The PLAIN-checker call is the load-bearing one. `artifact.strict_verdict`
/// is NOT enough on its own: `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also reports `Verified` when the deferred-trust RESCUE
/// re-discharges an unverified leaf, so it cannot distinguish "the step was
/// checked" from "the step was tolerated". `check_proof_strict_with_datatypes`
/// is the same call `mint_unsat_certificate` makes BEFORE any rescue, and it
/// runs `validate_string_length_lemma`'s full re-derivation of every length
/// identity plus the Farkas / integer-divisibility re-verification of the
/// arithmetic closure.
fn assert_string_length_refutation_is_plainly_checked(solver: &Solver) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the string-length \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the string-length rule, not something
    // else. Read the proof IR, not the printed text: Carcara has no
    // `string_length_lemma` rule, so the WIRE name is an honest `hole` while
    // AY's own checker validates the kind.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::StringLengthLemma,
                ..
            }
        )),
        "refutation must contain a checker-validated string_length_lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the QF_SLIA length-coherence shape): a concat
/// whose operands are pinned to more characters than the concatenation holds
/// must export a strictly verified, trust-free proof.
///
/// `(= (str.++ x y) "abc")` with `(= (str.len x) 2)` and `(= (str.len y) 2)`
/// is UNSAT — z3 5.0.0 agrees — because the concatenation is three characters
/// long while its operands are pinned to four between them. The CEGAR string
/// lane decides this outside the SAT trace, so no clause-level conflict reaches
/// the proof, the reconstruction closes on the whole-problem `trust` fallback,
/// and mandatory certification degraded a correct `unsat` to `unknown`.
///
/// The refutation is a RATIONAL one: `3 = len(x) + len(y)` with `len(x) = 2`
/// and `len(y) = 2` is already infeasible over the rationals, so it closes with
/// an `LraFarkas` certificate over the checker-validated length identities.
#[test]
fn qfslia_concat_length_coherence_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (declare-fun y () String)
            (assert (= (str.++ x y) "abc"))
            (assert (= (str.len x) 2))
            (assert (= (str.len y) 2))
            "#,
        )
        .expect("concat length-coherence fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a three-character concat whose operands are pinned to four characters \
         is UNSAT (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_length_refutation_is_plainly_checked(&solver);
}

/// The containment arm of the same pass: the bound
/// `str.contains(x, y) -> len(y) <= len(x)` is what makes `(str.contains x y)`
/// with `(= (str.len x) 0)` and `(> (str.len y) 0)` UNSAT — z3 5.0.0 agrees.
/// It exercises the root-conditioned `(or (not PRED) (<= ...))` derivation
/// (lemma + `or` clausification + resolution against the authored predicate)
/// rather than the equality one.
#[test]
fn qfslia_containment_length_bound_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (declare-fun y () String)
            (assert (str.contains x y))
            (assert (= (str.len x) 0))
            (assert (> (str.len y) 0))
            "#,
        )
        .expect("containment length-bound fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "an empty container cannot contain a non-empty string; UNSAT \
         (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_length_refutation_is_plainly_checked(&solver);
}

/// The INTEGER arm of the same pass, which a rational certificate provably
/// cannot reach: `(= (str.++ x x) "aba")` pins `2*len(x) = 3`, which is
/// perfectly satisfiable over the rationals (`len(x) = 3/2`) and infeasible
/// only over the integers. z3 5.0.0 answers `unsat`.
///
/// The Farkas closure therefore declines and the refutation goes through
/// `eq_transitive` — whose validator re-derives the connecting path itself —
/// to the single equality `3 = len(x) + len(x)`, whose negation the strict
/// `Divisibility` validator accepts by re-running "gcd 2 does not divide 3".
#[test]
fn qfs_word_equation_parity_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= (str.++ x x) "aba"))
            "#,
        )
        .expect("word-equation parity fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a doubled word cannot have odd length; UNSAT (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_length_refutation_is_plainly_checked(&solver);

    // The integer arm specifically: the closure is the divisibility lemma, not
    // a rational Farkas certificate (which cannot exist for `2*len(x) = 3`).
    let proof = solver.last_proof().expect("UNSAT publishes its proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::LiaGeneric,
                lia: Some(ay_core::LiaAnnotation::Divisibility),
                ..
            }
        )),
        "the parity refutation must close on the integer-divisibility lemma",
    );
}

/// Assert the shared post-conditions of a universal-instantiation refutation.
///
/// The PLAIN-checker call is the load-bearing one. `artifact.strict_verdict`
/// is NOT enough on its own: `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also reports `Verified` when the deferred-trust RESCUE
/// re-discharges an unverified leaf, so it cannot distinguish "the step was
/// checked" from "the step was tolerated". `check_proof_strict_with_datatypes`
/// is the same call `mint_unsat_certificate` makes BEFORE any rescue, and it
/// runs `validate_forall_inst`'s full re-derivation: binder/argument arity and
/// sorts, groundness of every argument with respect to the source binders, and
/// the exact simultaneous capture-safe substitution.
fn assert_forall_inst_refutation_is_plainly_checked(solver: &Solver) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the forall_inst \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the universal-instantiation rule, not
    // something else. Read the proof IR rather than the printed text.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )),
        "refutation must contain a checker-validated forall_inst step:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the universal-instantiation shape): a `forall`
/// whose quantifier-free body has an authored ground COUNTEREXAMPLE must
/// export a strictly verified, trust-free proof.
///
/// The instance is produced inside the quantifier lane by E-matching, so no
/// clause-level conflict reaches the SAT trace, the level-0 RUP replay
/// declines, and the reconstruction closes on the whole-problem `trust`
/// fallback. Measured on the pre-fix head, the rejected proof was literally
/// three steps — `(assume (not I))`, a `Generic` theory lemma asserting the
/// bare instance `(cl I)`, and one resolution — and `(cl I)` is NOT a theory
/// tautology (it holds only under the authored `forall`), so the deferred
/// trust rescue could not discharge it either:
///
/// ```text
/// strict UNSAT proof validation failed: step t1 uses unsupported theory
/// lemma kind Generic in strict mode; deferred-trust discharge failed: a
/// collected trust clause is not a standalone theory tautology AND the
/// authored assertions could not be independently re-solved as UNSAT
/// ```
///
/// z3 5.0.0 answers `unsat`; so does AY, and now it can say why.
#[test]
fn forall_instantiation_ground_counterexample_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::Lia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun P (Int) Bool)
            (assert (forall ((x Int)) (P x)))
            (assert (not (P 0)))
            "#,
        )
        .expect("universal-instantiation fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a universal with an authored ground counterexample is UNSAT \
         (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_forall_inst_refutation_is_plainly_checked(&solver);
}

/// The MULTI-BINDER arm of the same pass: two binders instantiated
/// SIMULTANEOUSLY from a pattern-annotated axiom, where the ground
/// counterexample fixes `x := a` and `y := b` independently.
///
/// This exercises the part of the certificate a single-binder fixture cannot:
/// `validate_forall_inst` checks the positional argument vector against the
/// binder list and re-derives the SIMULTANEOUS substitution, so an emitted
/// `:args` in the wrong order — or one value short — is rejected there rather
/// than silently accepted.
#[test]
fn multi_binder_forall_instantiation_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::Auflia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort S 0)
            (declare-fun f (S) S)
            (declare-fun g (S) S)
            (declare-fun p (S S) Bool)
            (declare-const a S)
            (declare-const b S)
            (assert (forall ((x S) (y S))
                (! (p (f x) (g y)) :pattern ((f x) (g y)))))
            (assert (not (p (f a) (g b))))
            "#,
        )
        .expect("multi-binder fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a two-binder universal with an authored ground counterexample is \
         UNSAT (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_forall_inst_refutation_is_plainly_checked(&solver);
}

/// Assert the shared post-conditions of a refutation whose theory lemma was
/// only recognizable after its doubly-negated literal was collapsed.
///
/// The PLAIN-checker call is the load-bearing assertion. `artifact.strict_verdict`
/// would NOT distinguish "the step was checked" from "the step was tolerated":
/// `strict_verdict_with_deferred_trust` (`api/proofs.rs`) also returns
/// `Verified` from its RESCUE arms. `check_proof_strict_with_datatypes` is the
/// call `mint_unsat_certificate` makes BEFORE any rescue, and it runs
/// `ay-proof`'s full read-over-write re-derivation from the clause alone.
fn assert_row_refutation_is_plainly_checked(solver: &Solver, expected: TheoryLemmaKind) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the collapsed read-over-write \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the array rule the CHECKER'S OWN
    // classifier chose, not a producer-side label.
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if *kind == expected)),
        "refutation must carry a checker-validated {expected:?} lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the double-negation blind spot): the ROW1
/// conflict under an index-equality premise must export a strictly verified,
/// trust-free proof.
///
/// `(= i j)` plus `(not (= (select (store a i v) j) v))` is UNSAT — z3 5.0.0
/// agrees — and AY computes that verdict. The theory conflict is recorded as
/// the negation of each conflicting literal, so refuting the AUTHORED negation
/// `(not (= v (select ...)))` produces the raw term
/// `(not (not (= v (select ...))))`: `mk_not` does not fold the pair. The
/// resulting clause IS `read_over_write_pos` under an index-equality premise,
/// and `ay-proof`'s `matches_row1_conditional` validates exactly that schema —
/// but only after seeing an EQUALITY literal, and `flatten_clause_literals`
/// flattens a unit `or` and nothing else. So `recognize_array_theory_lemma`
/// answered `None`, the lemma kept the `Generic` kind, and mandatory
/// certification degraded a correct `unsat` to `unknown` with
/// `step t2 uses unsupported theory lemma kind Generic in strict mode`.
///
/// The fix collapses `(not (not X))` to `X` — the SAME proposition — and hands
/// the rewritten clause to the checker's own classifier. Nothing in the
/// certification gate changed.
#[test]
fn row1_under_index_equality_premise_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAx);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const a (Array Int Int))
            (declare-const i Int)
            (declare-const j Int)
            (declare-const v Int)
            (assert (= i j))
            (assert (not (= (select (store a i v) j) v)))
            "#,
        )
        .expect("ROW1-under-premise fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "select(store(a,i,v),j) = v when i = j, so asserting the negation is \
         UNSAT (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_row_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    );
}

/// The chain arm of the same blind spot: reading a CONST-ARRAY through an
/// array-equality premise. `I = ((as const (Array Int Int)) 7)` plus
/// `(not (= (select I k) 7))` is UNSAT — z3 5.0.0 agrees.
///
/// Its conflict clause is
/// `(cl (not (= I (const-array 7))) (not (not (= 7 (select I k)))))`, which the
/// checker's matcher accepts as `ArrayRowChain` once the doubly-negated literal
/// is collapsed. Instrumented on the pristine base this reported
/// `dn=true before=None after=Some(ArrayRowChain)` — the matcher accepts the
/// collapsed clause and rejects the raw one. This pins the SECOND kind the one
/// normalization unlocks, so a regression that only restored the two-literal
/// ROW1 case would still fail here.
#[test]
fn const_array_read_under_equality_premise_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const I (Array Int Int))
            (declare-const k Int)
            (assert (= I ((as const (Array Int Int)) 7)))
            (assert (not (= (select I k) 7)))
            "#,
        )
        .expect("const-array read fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "select(const(7), k) = 7 for every k, so asserting != 7 is UNSAT \
         (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_row_refutation_is_plainly_checked(&solver, TheoryLemmaKind::ArrayRowChain);
}

/// Assert the shared post-conditions of a congruence VALUE-CONFLICT refutation.
///
/// The PLAIN-checker call is the load-bearing one, for the same reason it is in
/// [`assert_store_permutation_refutation_is_plainly_checked`]:
/// `artifact.strict_verdict` alone cannot distinguish "the step was checked"
/// from "the step was tolerated", because `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also returns `Verified` from its RESCUE arms.
/// `check_proof_strict_with_datatypes` is the same call `mint_unsat_certificate`
/// makes BEFORE any rescue, and it runs `validate_euf_congruent`'s full
/// re-derivation (both sides applications of the SAME symbol with the SAME
/// arity, exactly one premise equality per argument position connecting
/// `f_args[i]` to `g_args[i]`) and the arithmetic validator's independent
/// replay of the Farkas certificate against the exact clause.
fn assert_congruence_value_refutation_is_plainly_checked(solver: &Solver) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the congruence value-conflict \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the steps it accepted are the two primitive rules the `Generic`
    // label was standing in for, not something else. Read the proof IR rather
    // than the printed text.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::EufCongruent,
                ..
            }
        )),
        "refutation must contain a checker-validated eq_congruent lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric,
                farkas: Some(_),
                ..
            }
        )),
        "refutation must close the value conflict with a certificate-bearing \
         arithmetic lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the UFLIA carrier-projection shape): two values
/// for the SAME function symbol at arguments an authored equality identifies is
/// UNSAT — z3 5.0.0 agrees — and must export a strictly verified, trust-free
/// proof.
///
/// The EUF lane closes this by congruence closure and reports the conflict as
/// ONE clause over the three authored literals, labelled `Generic` (`euf.rs`:
/// "All derived array consequences ... remain honest Generic lemmas until an
/// explicit primitive proof expansion is available"). Strict mode has no
/// validator for `Generic`; discharging that clause IS re-proving the problem,
/// so the deferred-trust rescue reports `a collected trust clause is not a
/// standalone theory tautology`, and the mandatory publication gate turned a
/// correct `unsat` into `unknown`.
#[test]
fn uflia_congruence_value_conflict_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort MR 0)
            (declare-const bx MR)
            (declare-const by MR)
            (declare-fun cur (MR) Int)
            (assert (= (cur bx) 1))
            (assert (= (cur by) 2))
            (assert (= bx by))
            "#,
        )
        .expect("carrier-projection fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "bx = by forces cur(bx) = cur(by), contradicting 1 = 2 (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_congruence_value_refutation_is_plainly_checked(&solver);
}

/// The n-ary arm of the same pass: a BINARY function symbol whose second
/// argument is shared. That position has no authored equality to draw on, so it
/// exercises the reflexivity arm of the congruence-premise loop —
/// `validate_euf_congruent` demands one premise per argument position even when
/// the arguments are syntactically identical, so a missing premise would be a
/// hard rejection rather than a silently smaller clause.
#[test]
fn uflia_congruence_value_conflict_with_shared_argument_is_strict_verified() {
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort MR 0)
            (declare-const p MR)
            (declare-const q MR)
            (declare-const r MR)
            (declare-fun g (MR MR) Int)
            (assert (= (g p r) 7))
            (assert (= (g q r) 9))
            (assert (= p q))
            "#,
        )
        .expect("shared-argument congruence fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "p = q forces g(p, r) = g(q, r), contradicting 7 = 9 (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_congruence_value_refutation_is_plainly_checked(&solver);
}

/// The falsifiable near-miss, pinned so the pass cannot be widened into a
/// schema that accepts more than it derives. WITHOUT the argument equality the
/// same two value assertions are SATISFIABLE — z3 5.0.0 returns `sat` — so no
/// congruence lemma may ever be built for them.
#[test]
fn uflia_congruence_value_conflict_without_argument_equality_is_sat() {
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort MR 0)
            (declare-const bx MR)
            (declare-const by MR)
            (declare-fun cur (MR) Int)
            (assert (= (cur bx) 1))
            (assert (= (cur by) 2))
            "#,
        )
        .expect("near-miss fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_sat(),
        "two values at DISTINCT arguments are satisfiable (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
}
/// Regression (#trust-count→0): a ROW2 read-over-write whose index
/// DISEQUALITY is not authored but derived from two authored constants must
/// export a strictly verified, trust-free proof.
///
/// `i = #x05`, `j = #x06`, `(select a j) = #xAA` and
/// `(select (store a i v) j) = #xBB` is UNSAT (z3 5.0.0 agrees: `unsat`), and
/// AY computes that verdict. `replace_with_exact_authored_array_row2_refutation`
/// declines because the problem authors no `(not (= i j))` premise, so the
/// reconstruction fell through to the whole-problem `trust` closer and the
/// mandatory publication gate degraded the verdict to `unknown`.
#[test]
fn qfabv_row2_derived_index_disequality_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const i (_ BitVec 8))
            (declare-const j (_ BitVec 8))
            (declare-const v (_ BitVec 8))
            (assert (= i #x05))
            (assert (= j #x06))
            (assert (= (select a j) #xAA))
            (assert (= (select (store a i v) j) #xBB))
            "#,
        )
        .expect("ROW2 derived-disequality fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a write at #x05 cannot change the cell at #x06 (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
        "ROW2 derived-index-disequality",
    );
}

/// Regression (#trust-count→0): a ROW1 read-over-write reached through an
/// authored ARRAY equality must export a strictly verified, trust-free proof.
///
/// `mem2 = store(mem, p+0, #x10)` with `(select mem2 (bvadd p #x00)) = #x20` is
/// UNSAT (z3 5.0.0 agrees: `unsat`). The read names `mem2`, not the store term,
/// so the refutation needs a congruence lift onto the store before ROW1 applies.
#[test]
fn qfabv_row1_through_authored_array_equality_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const p (_ BitVec 8))
            (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
            (assert (= mem2 (store mem (bvadd p #x00) #x10)))
            (assert (= (select mem2 (bvadd p #x00)) #x20))
            "#,
        )
        .expect("ROW1 array-equality fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "the cell just written with #x10 cannot read back #x20 (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
        "ROW1 through an authored array equality",
    );
}

/// Regression (#trust-count→0): a ROW1 read-over-write whose index EQUALITY is
/// derived from two authored constants must export a strictly verified,
/// trust-free proof.
///
/// `p0 = #x10`, `p1 = #x10`, `mem2 = store(mem, p0, #xAA)` and
/// `(select mem2 p1) = #xBB` is UNSAT (z3 5.0.0 agrees: `unsat`). The problem
/// authors no `(= p0 p1)` premise; it is reached by transitivity through the
/// shared constant.
#[test]
fn qfabv_row1_derived_index_equality_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const p0 (_ BitVec 8))
            (declare-const p1 (_ BitVec 8))
            (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
            (assert (= p0 #x10))
            (assert (= p1 #x10))
            (assert (= mem2 (store mem p0 #xAA)))
            (assert (= (select mem2 p1) #xBB))
            "#,
        )
        .expect("ROW1 derived-index-equality fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "p0 and p1 are both #x10, so the write of #xAA is what p1 reads \
         (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
        "ROW1 derived-index-equality",
    );
}

/// Regression (#trust-count→0): a congruence conflict closed by an AUTHORED
/// disequality — rather than by a ground value mismatch — must export a
/// strictly verified, trust-free proof.
///
/// `x = #x05`, `f(x) = #xAA` and `f(#x05) != #xAA` is UNSAT (z3 5.0.0 agrees:
/// `unsat`). Neither existing arm of
/// `replace_with_exact_authored_congruence_refutation` fires: ARM A needs the
/// refuting disequality to be BETWEEN the two congruent applications, and ARM B
/// needs BOTH of them pinned to values by authored equalities.
#[test]
fn qfufbv_congruence_against_authored_disequality_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfUfbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
            (declare-const x (_ BitVec 8))
            (assert (= x #x05))
            (assert (= (f x) #xAA))
            (assert (not (= (f #x05) #xAA)))
            "#,
        )
        .expect("congruence-against-authored-disequality fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "f(x) and f(#x05) are the same application when x is #x05 (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::EufCongruent,
        "congruence against an authored disequality",
    );
}

/// Regression (#trust-count→0): a read-over-write CHAIN spanning three SSA
/// array equalities must export a strictly verified, trust-free proof.
///
/// `mem1 = store(mem0, #x00, #x01)`, `mem2 = store(mem1, #x01, #x02)`,
/// `mem3 = store(mem2, #x02, #x03)` and `(select mem3 #x01) = #xFF` is UNSAT
/// (z3 5.0.0 agrees: `unsat`). Closing it needs a WALK: ROW2 past the `#x02`
/// write, then ROW1 at the `#x01` write, with a congruence lift onto each SSA
/// array name in between — one ROW step is not enough.
#[test]
fn qfabv_row_chain_walk_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-const mem0 (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const mem1 (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const mem2 (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const mem3 (Array (_ BitVec 8) (_ BitVec 8)))
            (assert (= mem1 (store mem0 #x00 #x01)))
            (assert (= mem2 (store mem1 #x01 #x02)))
            (assert (= mem3 (store mem2 #x02 #x03)))
            (assert (= (select mem3 #x01) #xFF))
            "#,
        )
        .expect("SSA store-chain fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "cell #x01 holds #x02 after the chain, not #xFF (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
        "read-over-write chain walk",
    );
}

/// Regression (#trust-count→0): a value conflict between two NESTED congruent
/// applications must export a strictly verified, trust-free proof.
///
/// `x = y`, `f(select(a, x)) = #xAA` and `f(select(a, y)) = #xBB` is UNSAT
/// (z3 5.0.0 agrees: `unsat`). No argument position of the two `f`
/// applications carries an authored equality — `(select a x)` and
/// `(select a y)` are themselves only congruent — so the refutation needs one
/// `eq_congruent` per level.
#[test]
fn qfaufbv_nested_congruence_value_conflict_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfAufbv);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
            (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
            (declare-const x (_ BitVec 8))
            (declare-const y (_ BitVec 8))
            (assert (= x y))
            (assert (= (f (select a x)) #xAA))
            (assert (= (f (select a y)) #xBB))
            "#,
        )
        .expect("nested-congruence fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "f of the same cell cannot be both #xAA and #xBB (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_refutation_is_plainly_checked(
        &solver,
        TheoryLemmaKind::EufCongruent,
        "nested congruence value conflict",
    );
}

/// Assert the shared post-conditions of a refutation whose equality chain
/// needed a ground INSTANCE of an authored `forall`
/// (`replace_with_exact_authored_forall_inst_equality_refutation`).
///
/// The PLAIN-checker call is the load-bearing one. `artifact.strict_verdict`
/// is NOT enough on its own: `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also reports `Verified` when the deferred-trust RESCUE
/// re-discharges an unverified leaf, so it cannot distinguish "the step was
/// checked" from "the step was tolerated". `check_proof_strict_with_datatypes`
/// is the same call `mint_unsat_certificate` makes BEFORE any rescue, and it
/// runs `validate_forall_inst`'s full re-derivation of the substitution plus
/// `validate_euf_transitive`'s BFS for a genuine path between the conclusion
/// equality's two endpoints.
fn assert_forall_inst_equality_refutation_is_plainly_checked(solver: &Solver) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the instantiated-equality \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the steps it accepted are the universal instantiation and the
    // transitivity chain, not something else. Read the proof IR, not the
    // printed text.
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )),
        "refutation must instantiate the authored forall with `forall_inst`:\n{}",
        artifact.alethe,
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqTransitive,
                ..
            }
        )),
        "refutation must close through a checked transitivity chain:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the deductive-checks left-inverse family), ARM 1 —
/// SHARED ENDPOINT. The authored `forall` instance `(= (Unbox (Box c)) c)`
/// and the authored pin `(= (Unbox (Box c)) d)` share an endpoint, so
/// `eq_transitive` yields `(= c d)`, which the authored `distinct` refutes.
///
/// Before this pass AY computed `unsat` and published `unknown`:
/// `strict UNSAT proof validation failed: step t4 uses unverified trust rule`.
/// `replace_with_exact_authored_forall_inst_refutation` cannot reach it — that
/// lane needs an authored `(not I)` root that is the EXACT complement of the
/// instantiated body, and here the instance is an equality that has to be
/// COMPOSED with the other roots before anything contradicts.
///
/// THE BITVECTOR ELEMENT SORT IS PART OF THE FIXTURE, NOT DECORATION. The
/// same shape over an uninterpreted element sort never reaches this pass: the
/// ordinary reconstruction already derives the instance through the proof
/// tracker's `add_forall_instantiated_assertion` and closes it with a checked
/// `eq_transitive`, so the strict checker accepts and the pass early-returns
/// on its first line. On the BV32 signature — the shape deductive-checks actually
/// emits — the reconstruction closes on the whole-problem `trust` step
/// instead, which is where this pass fires.
///
/// z3 5.0.0: unsat.
#[test]
fn forall_instance_shared_endpoint_refutation_is_strict_verified() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort Poly 0)
            (declare-const c (_ BitVec 32))
            (declare-const d (_ BitVec 32))
            (declare-fun Box_i32 ((_ BitVec 32)) Poly)
            (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
            (assert (forall ((x (_ BitVec 32))) (= (Unbox_i32 (Box_i32 x)) x)))
            (assert (distinct c d))
            (assert (= (Unbox_i32 (Box_i32 c)) d))
            "#,
        )
        .expect("left-inverse image-disagreement fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "z3 5.0.0 decides this unsat; got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_forall_inst_equality_refutation_is_plainly_checked(&solver);
}

/// NEAR-MISS twin of ARM 1, one token different: the authored pin AGREES with
/// the axiom (`(= (Unbox (Box c)) c)`), so the chain the arm can build ends at
/// `(= c c)` and the authored `distinct c d` refutes nothing.
///
/// This is what stops the arm from being a rubber stamp. A producer that
/// fabricated the endpoint equality instead of deriving it would turn this
/// SATISFIABLE problem into `unsat`. Stated over an uninterpreted element sort
/// because the pinned oracle does not decide the BV32 twin's SAT direction
/// inside a 280 s budget; the pass is sort-agnostic, so the schema contrast is
/// the same one.
///
/// z3 5.0.0: sat.
#[test]
fn forall_instance_shared_endpoint_agreeing_pin_is_not_unsat() {
    let mut solver = Solver::new(Logic::Uf);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort E 0)
            (declare-sort Poly 0)
            (declare-const c E)
            (declare-const d E)
            (declare-fun Box (E) Poly)
            (declare-fun Unbox (Poly) E)
            (assert (forall ((x E)) (= (Unbox (Box x)) x)))
            (assert (distinct c d))
            (assert (= (Unbox (Box c)) c))
            "#,
        )
        .expect("near-miss fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        !verdict.is_unsat(),
        "an agreeing pin is satisfiable (z3 5.0.0: sat); refuting it would mean \
         the endpoint equality was fabricated rather than derived, got {verdict:?}",
    );
}

/// Regression (#trust-count→0, the deductive-checks left-inverse family), ARM 2 —
/// CONGRUENCE BRIDGE. Two instances of the authored `forall`,
/// `(= (Unbox (Box a)) a)` and `(= (Unbox (Box b)) b)`, are joined by a
/// congruence unit built from the authored `(= (Box a) (Box b))` — the same
/// `derive_authored_congruence_unit` the ground lane uses — and the three-edge
/// chain yields `(= a b)`, refuted by the authored `distinct`.
///
/// z3 5.0.0: unsat.
#[test]
fn forall_instance_congruence_bridge_refutation_is_strict_verified() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort Poly 0)
            (declare-const a (_ BitVec 32))
            (declare-const b (_ BitVec 32))
            (declare-fun Box_i32 ((_ BitVec 32)) Poly)
            (declare-fun Unbox_i32 (Poly) (_ BitVec 32))
            (assert (forall ((x (_ BitVec 32))) (= (Unbox_i32 (Box_i32 x)) x)))
            (assert (distinct a b))
            (assert (= (Box_i32 a) (Box_i32 b)))
            "#,
        )
        .expect("left-inverse non-injectivity fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "z3 5.0.0 decides this unsat; got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_forall_inst_equality_refutation_is_plainly_checked(&solver);
}

/// NEAR-MISS twin of ARM 2, one token different: the authored equality pins
/// `(= (Box a) (Wrap b))`, whose two sides are applications of DIFFERENT
/// heads, so no congruence bridges the two instances and the chain never
/// reaches `(= a b)`.
///
/// Sort rationale as in the ARM 1 near-miss above.
///
/// z3 5.0.0: sat.
#[test]
fn forall_instance_congruence_bridge_distinct_heads_is_not_unsat() {
    let mut solver = Solver::new(Logic::Uf);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-sort E 0)
            (declare-sort Poly 0)
            (declare-const a E)
            (declare-const b E)
            (declare-fun Box (E) Poly)
            (declare-fun Wrap (E) Poly)
            (declare-fun Unbox (Poly) E)
            (assert (forall ((x E)) (= (Unbox (Box x)) x)))
            (assert (distinct a b))
            (assert (= (Box a) (Wrap b)))
            "#,
        )
        .expect("near-miss fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        !verdict.is_unsat(),
        "two different heads cannot be bridged by congruence, so this is \
         satisfiable (z3 5.0.0: sat), got {verdict:?}",
    );
}

/// Assert the shared post-conditions of a UNIVERSAL-INSTANTIATION refutation
/// whose instance is refuted by the REST of the authored problem rather than
/// by being the literal complement of one authored root.
///
/// The PLAIN-checker call is the load-bearing one, for the same reason it is
/// in [`assert_forall_inst_refutation_is_plainly_checked`]:
/// `artifact.strict_verdict` alone cannot distinguish "the step was checked"
/// from "the step was tolerated", because `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also returns `Verified` from its RESCUE arms.
/// `check_proof_strict_with_datatypes` is the same call
/// `mint_unsat_certificate` makes BEFORE any rescue, and it runs
/// `validate_forall_inst`'s full re-derivation (binder/argument arity and
/// sorts, argument groundness, and the EXACT simultaneous capture-safe
/// substitution) plus the Boolean and arithmetic validators for every other
/// step of the rebuilt refutation.
fn assert_forall_inst_conflict_refutation_is_plainly_checked(solver: &Solver) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the forall_inst \
                 conflict refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                ..
            }
        )),
        "refutation must contain a checker-validated forall_inst step:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0): a `forall` instance that complements NO
/// authored root, and conflicts with the ground assertions only through a
/// Farkas combination, must export a strictly verified, trust-free proof.
///
/// This is the fixture of the pre-existing
/// `api::tests::test_core::test_uflia_ground_unsat_with_referenced_forall_axiom_2829`,
/// which asserts only the VERDICT. Instantiating the axiom at `x := i` gives
/// `(= (double i) (+ i i))`, which complements no authored root; it conflicts
/// with `(>= i 0)`, `(= i_prime (double i))` and `(not (>= i_prime 0))`
/// TOGETHER, and only arithmetically, over the opaque atom `(double i)`. The
/// conflict is admitted only after `try_lra_farkas_reconstruction` (the same
/// LRA solver the checker's `la_generic` validator replays) returns an actual
/// certificate for the exact clause. z3 5.0.0 answers `unsat`.
///
/// NON-VACUOUS, measured: with the pass's call site removed this test fails at
/// its first assertion with `step t5 uses unverified trust rule`.
#[test]
fn arithmetic_forall_instantiation_bound_conflict_is_strict_verified() {
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun double (Int) Int)
            (declare-const i Int)
            (declare-const i_prime Int)
            (assert (>= i 0))
            (assert (< i 10))
            (assert (= i_prime (double i)))
            (assert (not (>= i_prime 0)))
            (assert (forall ((x Int))
                (! (= (double x) (+ x x)) :pattern ((double x)))))
            "#,
        )
        .expect("arithmetic instantiation fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "i >= 0 and double(i) = i + i force i_prime >= 0 (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_forall_inst_conflict_refutation_is_plainly_checked(&solver);
}

/// The falsifiable near-miss, pinned so the pass cannot be widened into a
/// schema that accepts more than it derives. WITHOUT `(>= i 0)` the very same
/// axiom and chain are SATISFIABLE — a negative `i` gives a negative
/// `i_prime = i + i` — and z3 5.0.0 returns `sat`. The Farkas search finds no
/// certificate for any premise subset, so no candidate is ever built and no
/// refutation is ever published.
///
/// The assertion is `!is_unsat()` rather than `is_sat()` DELIBERATELY, and the
/// difference is measured, not assumed: on this head AY answers `unknown` here
/// with `QuantifierEmatchingExistsIncomplete`. That incompleteness is
/// pre-existing, lives in the quantifier lane, and is untouched by this commit
/// — a proof-step derivation cannot reach it, because no verdict is ever
/// computed to certify. What this test pins is the property this pass could
/// actually violate: a satisfiable problem must never come back `unsat`.
#[test]
fn arithmetic_forall_instantiation_consistent_bound_is_sat() {
    let mut solver = Solver::new(Logic::Uflia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun double (Int) Int)
            (declare-const i Int)
            (declare-const i_prime Int)
            (assert (< i 10))
            (assert (= i_prime (double i)))
            (assert (not (>= i_prime 0)))
            (assert (forall ((x Int))
                (! (= (double x) (+ x x)) :pattern ((double x)))))
            "#,
        )
        .expect("consistent-bound near-miss fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        !verdict.is_unsat(),
        "a negative i makes i_prime = i + i negative, so this is SATISFIABLE \
         (z3 5.0.0 agrees) and no refutation may ever be built for it, \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
}

/// Regression (#trust-count→0, the datatype equality-closure family): a
/// refutation whose whole content is EQUALITY REASONING over the authored roots
/// must export a strictly verified proof, not degrade to `unknown`.
///
/// `(and (= red c1) (= c1 c2))` together with `(= blue c2)` chains `red` to
/// `blue` through two variables. The congruence closure / datatype solver closes
/// this internally and publishes the conflict as ONE `Generic` (trust) clause —
/// typically the bare negation of the authored conjunction — which carries no
/// argument, so strict mode must reject it, discharging it is re-proving the
/// problem, and the mandatory publication gate turned a correct `unsat` into
/// `unknown`.
///
/// `replace_with_exact_authored_equality_closure_refutation` rebuilds the
/// derivation instead: `and_pos` projections for the conjuncts, `eq_transitive`
/// for the chain, and a registry-backed `DatatypeDistinct` lemma to refute
/// `(= red blue)`. Every one of those has an independent strict validator in
/// `ay-proof`, so the certificate is CHECKED rather than tolerated.
#[test]
fn datatype_equality_chain_distinct_constructors_is_strict_verified() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-datatypes ((Colour 0)) (((red) (blue) (green))))
            (declare-const c1 Colour)
            (declare-const c2 Colour)
            (assert (and (= red c1) (= c1 c2)))
            (assert (= blue c2))
            "#,
        )
        .expect("datatype equality-chain fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "red = c1 = c2 = blue is UNSAT for distinct constructors (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    // The assertion that matters: the PLAIN strict checker accepts it. The
    // artifact's own verdict would not distinguish "checked" from "tolerated",
    // because `strict_verdict_with_deferred_trust` also reports `Verified` from
    // its two RESCUE arms.
    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the equality-closure \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeDistinct,
                ..
            }
        )),
        "the refutation must close on a registry-validated dt_distinct lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqTransitive,
                ..
            }
        )),
        "the chain red = c1 = c2 = blue must be stated as eq_transitive:\n{}",
        artifact.alethe,
    );
}

/// The CONGRUENCE arm of the same pass, and the arm that closes on an authored
/// DISEQUALITY rather than on constructor distinctness.
///
/// `result = Accept(claimed)` and `actual = claimed` force
/// `result = Accept(actual)`, contradicting the second assertion. The rebuilt
/// derivation therefore needs `eq_congruent` (to lift `actual = claimed` through
/// the constructor) as well as `eq_transitive`, both independently re-validated
/// by `ay-proof`: `validate_euf_congruent` re-checks that the two conclusion
/// sides apply the SAME symbol at the SAME arity and that premise `i` links
/// argument position `i`, so a mis-built congruence is rejected there and the
/// pass leaves the proof — and the `unknown` — exactly as it found them.
#[test]
fn datatype_constructor_congruence_closure_is_strict_verified() {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-datatypes ((Verdict 0)) (((Reject) (Accept (objv (_ BitVec 8))))))
            (declare-const result Verdict)
            (declare-const actual (_ BitVec 8))
            (declare-const claimed (_ BitVec 8))
            (assert (= result (Accept claimed)))
            (assert (not (= result (Accept actual))))
            (assert (= actual claimed))
            "#,
        )
        .expect("constructor-congruence fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "actual = claimed forces Accept(actual) = Accept(claimed) = result, so \
         the fixture is UNSAT (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );

    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the congruence-closure \
                 refutation, got {error}\n{}",
                artifact.alethe,
            )
        });

    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqCongruent,
                ..
            }
        )),
        "lifting actual = claimed through the constructor must be stated as \
         eq_congruent:\n{}",
        artifact.alethe,
    );
}

/// Assert the shared post-conditions of a refutation this round's string
/// passes rebuild, and that the step the checker accepted carries `kind`.
///
/// The PLAIN-checker call is the load-bearing one. `artifact.strict_verdict`
/// is NOT enough on its own: `strict_verdict_with_deferred_trust`
/// (`api/proofs.rs`) also reports `Verified` when the deferred-trust RESCUE
/// re-discharges an unverified leaf, so it cannot distinguish "the step was
/// checked" from "the step was tolerated". `check_proof_strict_with_datatypes`
/// is the same call `mint_unsat_certificate` makes BEFORE any rescue, and it
/// runs each new validator's full independent re-derivation.
fn assert_string_refutation_carries_kind(solver: &Solver, kind: TheoryLemmaKind) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("a certified UNSAT must publish a proof artifact");
    let proof = solver
        .last_proof()
        .expect("a certified UNSAT publishes its proof");

    solver
        .executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap_or_else(|error| {
            panic!(
                "the PLAIN strict checker must accept the refutation, got \
                 {error}\n{}",
                artifact.alethe,
            )
        });

    // ...and the step it accepted is the expected rule, not something else.
    // Read the proof IR, not the printed text: Carcara has no rule for these
    // internal certificates, so the WIRE name is an honest `hole` while AY's
    // own checker validates the kind.
    assert!(
        proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::TheoryLemma { kind: k, .. } if *k == kind)),
        "refutation must contain a checker-validated {kind:?} lemma:\n{}",
        artifact.alethe,
    );
    assert!(
        artifact.quality.is_complete(),
        "proof must have zero trust/hole steps: {}\n{}",
        artifact.quality,
        artifact.alethe,
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(()),
    );
}

/// Regression (#trust-count→0, the extended-function reduction shape):
/// `(= x "hello")` propagated into `(= (str.substr x 1 3) "abc")` leaves a
/// GROUND claim — `str.substr("hello", 1, 3)` is `"ell"`, not `"abc"` — so the
/// problem is UNSAT and z3 5.0.0 agrees. AY computed that every time and
/// published `unknown`, because the reduction happens outside the SAT trace and
/// the reconstruction closed on the whole-problem `trust` fallback.
///
/// The rebuilt refutation transports the authored literal across the ground
/// binding with `eq_congruent` / `eq_congruent_pred` (whose validators re-derive
/// the per-argument matching themselves) and closes on `StringGroundEval`, whose
/// INDEPENDENT evaluator re-decides `str.substr("hello", 1, 3)`.
#[test]
fn qfslia_substr_ground_substitution_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= x "hello"))
            (assert (= (str.substr x 1 3) "abc"))
            "#,
        )
        .expect("substr reduction fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "str.substr(\"hello\", 1, 3) is \"ell\", not \"abc\"; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundEval);
}

/// The same pass over `str.indexof`: `str.indexof("abcab", "b", 0)` is the
/// LEFTMOST occurrence, `1`, not `4`. z3 5.0.0 answers `unsat`.
#[test]
fn qfslia_indexof_ground_substitution_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= x "abcab"))
            (assert (= (str.indexof x "b" 0) 4))
            "#,
        )
        .expect("indexof reduction fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "the leftmost \"b\" in \"abcab\" is at index 1, not 4; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundEval);
}

/// The same pass over `str.replace`, which rewrites only the FIRST occurrence:
/// `str.replace("abcab", "b", "z")` is `"azcab"`, not `"abcaz"`. z3 5.0.0
/// answers `unsat`.
#[test]
fn qfslia_replace_ground_substitution_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= x "abcab"))
            (assert (= (str.replace x "b" "z") "abcaz"))
            "#,
        )
        .expect("replace reduction fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "str.replace rewrites only the first occurrence; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundEval);
}

/// Regression (#trust-count→0, the self-containment shape): every word contains
/// itself, so `(not (str.contains x x))` is UNSAT for any `x`. z3 5.0.0 agrees.
/// The refutation states that theorem as `StringContainmentIdentity`, whose
/// validator re-checks that the two argument positions hold the SAME term.
#[test]
fn qfs_self_containment_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (not (str.contains x x)))
            "#,
        )
        .expect("self-containment fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "a word contains itself; UNSAT (z3 5.0.0 agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringContainmentIdentity);
}

/// Regression (#trust-count→0, the ground-factor shape): `"c"` does not occur
/// in `"ab"`, so no value of `x` makes `x ++ "c"` a factor of `"ab"` and
/// `(str.contains "ab" (str.++ x "c"))` is UNSAT. z3 5.0.0 agrees.
#[test]
fn qfs_ground_factor_conflict_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (str.contains "ab" (str.++ x "c")))
            "#,
        )
        .expect("ground-factor fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "\"c\" is not a factor of \"ab\"; UNSAT (z3 5.0.0 agrees), got \
         {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundFactorConflict);
}

/// The boundary-block arm of the same kind: the last character of `x ++ "b"` is
/// `"b"`, so `(str.suffixof "c" (str.++ x "b"))` is UNSAT. z3 5.0.0 agrees.
/// This exercises the prefix/suffix schema (pattern no longer than the ground
/// boundary block) rather than the factor scan.
#[test]
fn qfs_ground_suffix_conflict_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (str.suffixof "c" (str.++ x "b")))
            "#,
        )
        .expect("ground-suffix fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "the last character of x ++ \"b\" is \"b\"; UNSAT (z3 5.0.0 agrees), \
         got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringGroundFactorConflict);
}

/// Regression (#trust-count→0, the cancellation shape): `str.++` cancels on the
/// right in the free monoid, so `x ++ "c" = y ++ "c"` forces `x = y` and the
/// added `(not (= x y))` is UNSAT. z3 5.0.0 agrees. The refutation states the
/// cancellation as `StringConcatCancellation`, whose validator re-derives the
/// shared operand run and both residuals from the clause alone.
#[test]
fn qfslia_concat_cancellation_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfSlia);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (declare-fun y () String)
            (assert (= (str.len x) (str.len y)))
            (assert (= (str.++ x "c") (str.++ y "c")))
            (assert (not (= x y)))
            "#,
        )
        .expect("concat cancellation fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "str.++ cancels on the right; UNSAT (z3 5.0.0 agrees), got \
         {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::StringConcatCancellation);
}

/// Regression (#trust-count→0, the regex length-bound shape): `x ++ x = "aaaa"`
/// pins `2*len(x) = 4`, i.e. `len(x) = 2`, while
/// `x` in `((_ re.loop 3 5) (str.to_re "a"))` pins `len(x) >= 3`. z3 5.0.0
/// answers `unsat`.
///
/// The bound joins the existing length-arithmetic pool as a
/// `RegexLengthLowerBound` clause, whose validator recomputes the regex's
/// minimum word length compositionally, and the pool closes on a rational
/// `LraFarkas` certificate.
#[test]
fn qfs_regex_length_lower_bound_unsat_proof_is_strict_verified() {
    let mut solver = Solver::new(Logic::QfS);
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            r#"
            (declare-fun x () String)
            (assert (= (str.++ x x) "aaaa"))
            (assert (str.in_re x ((_ re.loop 3 5) (str.to_re "a"))))
            "#,
        )
        .expect("regex length-bound fixture must parse");

    let verdict = solver.check_sat();
    assert!(
        verdict.is_unsat(),
        "len(x) = 2 contradicts the regex's minimum length 3; UNSAT (z3 5.0.0 \
         agrees), got {verdict:?} / {:?}",
        solver.unknown_reason(),
    );
    assert_string_refutation_carries_kind(&solver, TheoryLemmaKind::RegexLengthLowerBound);
}

/// Best-effort proof collection is a diagnostic surface, not an authority
/// demand. The mandatory UNSAT-certification funnel may publish this genuine
/// nonlinear refutation while retaining the trust-bearing proof so consumers
/// can verify that their own strict-trust policy still rejects that artifact.
/// An explicit artifact request remains covered separately by the fail-closed
/// proof-required tests above.
#[test]
fn best_effort_api_retains_trust_bearing_proof_without_overriding_certified_unsat() {
    let mut solver = Solver::try_new(Logic::QfNia).expect("QF_NIA solver");
    solver.set_best_effort_produce_proofs(1_000_000);

    let x = solver.declare_const("best_effort_nia_x", Sort::Int);
    let x_sq = solver.try_mul(x, x).expect("x * x");
    let two = solver.int_const(2);
    let eq = solver.try_eq(x_sq, two).expect("x * x = 2");
    solver.assert_term(eq);

    let verdict = solver.check_sat_with_details();
    assert!(
        verdict.result.result().is_unsat(),
        "the independently certified nonlinear refutation must publish as UNSAT; got {:?}",
        verdict.result.result()
    );
    let quality = solver
        .last_proof_quality()
        .expect("best-effort collection must retain this diagnostic proof");
    assert!(
        !quality.is_complete(),
        "fixture drift: expected a trust-bearing diagnostic proof, got {quality:?}"
    );
    assert!(
        solver
            .last_strict_proof_quality()
            .expect("retained proof must expose a strict verdict")
            .is_err(),
        "strict checking must still reject the trust-bearing diagnostic proof"
    );
}
