// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-source publication/state tests. No SMT decision procedure is invoked.

#![cfg(test)]

use super::*;
use crate::executor_types::SolveResult;
use ay_core::{ProofStep, Sort as CoreSort, TermId};
use ay_frontend::parse;
use num_rational::BigRational;

mod control_flow;
mod declined_lowering;

const SQUARE: &str = "(declare-const x Real) (assert (< (* x x) 0.0))";

fn load(source: &str) -> Box<Executor> {
    let commands = parse(&format!(
        "(set-option :produce-proofs true) \
         (set-option :check-proofs-strict true) (set-logic ALL) {source}"
    ))
    .expect("source fixture parses");
    let mut executor = Box::new(Executor::new());
    executor
        .execute_all(&commands)
        .expect("install source only");
    executor
}

fn open(executor: &mut Executor, assumptions: &[TermId]) {
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(assumptions);
    executor.last_assumptions = Some(assumptions.to_vec());
}

fn prepare(executor: &mut Executor, assumptions: &[TermId]) -> PreparedStrictNativeNraSosBundle {
    executor
        .prepare_strict_native_nra_sos_bundle(assumptions)
        .expect("live bounded preparation")
        .expect("analytic SOS source")
}

fn install(executor: &mut Executor, assumptions: &[TermId]) {
    let prepared = prepare(executor, assumptions);
    let scope = executor
        .authenticate_unsat_query_scope(assumptions, true)
        .expect("exact publication scope");
    let checked = prepared.bind(scope, executor).expect("same-query binding");
    executor.last_unsat_certificate = Some(UnsatCertificate(
        UnsatCertificateKind::StrictNativeNraSosBundle(checked),
    ));
    // The fixture injects only the provisional decision; SOS search, source
    // authentication, native reconstruction/replay and binding are production.
    executor.last_result = Some(SolveResult::unsat());
}

fn sealed() -> Box<Executor> {
    let mut executor = load(SQUARE);
    open(&mut executor, &[]);
    install(&mut executor, &[]);
    executor
}

fn has_current_bundle(executor: &Executor) -> bool {
    executor.last_proof.as_ref().is_some_and(|proof| {
        executor
            .strict_native_nra_sos_bundle_for_proof(proof)
            .is_some()
    })
}

#[test]
fn native_bundle_is_strict_and_alethe_renders_its_checked_lowering() {
    let mut executor = sealed();
    let certificate = executor.last_unsat_certificate.as_ref().unwrap();
    assert!(certificate.strict_proof_verified());
    assert!(!certificate.independently_verified());
    assert!(matches!(
        &certificate.0,
        UnsatCertificateKind::StrictNativeNraSosBundle(_)
    ));
    let proof = executor.last_proof.as_ref().unwrap();
    let bundle = executor
        .strict_native_nra_sos_bundle_for_proof(proof)
        .unwrap();
    let checked = ay_proof::re_check_bundle_strict(bundle).expect("independent native replay");
    assert!(checked.quality.is_complete());
    assert_eq!(checked.assume_terms, bundle.obligation_assertions);
    assert_eq!(checked.quality.hole_count, 0);
    assert!(!executor.proof_has_known_wire_gap(proof));
    assert!(!executor.unsat_proof_terminal_trust_detected());
    let text = ay_proof::try_export_alethe(proof, &executor.ctx.terms).unwrap();
    assert_eq!(text.matches(":rule hole").count(), 0, "{text}");
    assert!(text.contains(":rule la_mult_neg"), "{text}");
    assert!(!text.contains(":rule nra_sos"));
    assert!(!text.contains(":rule trust"));
    assert!(executor
        .decline_trust_bearing_unsat_under_strict_proofs(SolveResult::unsat())
        .is_unsat());
}

#[test]
fn the_common_mint_reconstructs_source_evidence_without_a_pending_solver_proof() {
    let mut executor = load(SQUARE);
    open(&mut executor, &[]);
    executor.last_result = Some(SolveResult::unsat());
    assert!(executor.last_proof.is_none());
    assert!(executor.last_unsat_certificate.is_none());
    let certificate = executor
        .mint_unsat_certificate(&[])
        .expect("the common mint must independently prove the exact source");
    assert!(matches!(
        &certificate.0,
        UnsatCertificateKind::StrictNativeNraSosBundle(_)
    ));
    assert!(certificate.strict_proof_verified());
    assert!(!certificate.independently_verified());
    executor.last_unsat_certificate = Some(certificate);
    assert!(has_current_bundle(&executor));
    assert!(executor
        .decline_trust_bearing_unsat_under_strict_proofs(SolveResult::unsat())
        .is_unsat());
}

#[test]
fn a_satisfiable_authored_query_cannot_borrow_an_unsat_working_set() {
    let mut executor = load("(declare-const x Real) (assert (<= (* x x) 0.0))");
    let x = executor.ctx.symbol_info("x").unwrap().term.unwrap();
    let zero = executor
        .ctx
        .terms
        .mk_rational(BigRational::from_integer(0.into()));
    let square = executor.ctx.terms.mk_mul(vec![x, x]);
    let negative = executor.ctx.terms.mk_lt(square, zero);
    open(&mut executor, &[]);
    let authored = executor
        .unsat_query_epoch
        .as_ref()
        .unwrap()
        .assertions
        .clone();
    executor.ctx.assertions = vec![negative];
    assert_ne!(executor.ctx.assertions, authored);
    assert!(executor
        .prepare_strict_native_nra_sos_bundle(&[])
        .unwrap()
        .is_none());
    assert!(executor.last_unsat_certificate.is_none());
    assert!(!executor.has_strict_native_nra_sos_bundle_state());
}

#[test]
fn exact_authored_unsat_does_not_require_the_rewritten_working_roots() {
    let mut executor = load(SQUARE);
    open(&mut executor, &[]);
    let authored = executor
        .unsat_query_epoch
        .as_ref()
        .unwrap()
        .assertions
        .clone();
    executor.ctx.assertions = vec![executor.ctx.terms.true_term()];
    install(&mut executor, &[]);
    let proof = executor.last_proof.as_ref().unwrap();
    assert_eq!(
        executor
            .strict_native_nra_sos_bundle_for_proof(proof)
            .unwrap()
            .obligation_assertions,
        authored
    );
}

#[test]
fn surface_shadowing_does_not_turn_an_uninterpreted_product_into_a_square() {
    let mut executor = load(
        "(declare-fun * (Real Real) Real) (declare-const x Real) \
         (assert (< (* x x) 0.0))",
    );
    let info = executor.ctx.symbol_info("*").expect("source declaration");
    assert_ne!(executor.ctx.symbol_identity_name("*", info), "*");
    open(&mut executor, &[]);
    assert!(executor
        .prepare_strict_native_nra_sos_bundle(&[])
        .unwrap()
        .is_none());
    assert!(!executor.has_strict_native_nra_sos_bundle_state());
}

#[test]
fn canonical_operator_ownership_and_forged_aliases_cannot_authorize_sos() {
    for name in ["+", "-", "*", "=", "<", "<=", ">", ">=", "not"] {
        let mut executor = load(SQUARE);
        let owner = executor
            .ctx
            .terms
            .mk_fresh_var("forged_operator", CoreSort::Real);
        executor
            .ctx
            .register_symbol(name.to_owned(), owner, CoreSort::Real);
        open(&mut executor, &[]);
        assert!(
            executor
                .prepare_strict_native_nra_sos_bundle(&[])
                .unwrap()
                .is_none(),
            "{name}"
        );
        assert!(!executor.has_strict_native_nra_sos_bundle_state());
    }
    let mut executor = load(SQUARE);
    // The public alias API itself refuses this attack; do not invent an
    // inaccessible SymbolInfo mutation just to bypass the frontend boundary.
    assert!(executor
        .ctx
        .register_native_function_alias(
            "apparently_ordinary".to_owned(),
            "*".to_owned(),
            vec![CoreSort::Real, CoreSort::Real],
            CoreSort::Real,
        )
        .is_err());
    open(&mut executor, &[]);
    assert!(prepare(&mut executor, &[])
        .bind(
            executor.authenticate_unsat_query_scope(&[], true).unwrap(),
            &mut executor,
        )
        .is_some());
}

#[test]
fn prepared_evidence_is_bound_to_one_query_epoch_and_one_executor() {
    let mut same = load(SQUARE);
    open(&mut same, &[]);
    let prepared = prepare(&mut same, &[]);
    let scope = same.authenticate_unsat_query_scope(&[], true).unwrap();
    assert!(prepared.bind(scope, &mut same).is_some());
    for foreign_executor in [false, true] {
        let mut original = load(SQUARE);
        open(&mut original, &[]);
        let prepared = prepare(&mut original, &[]);
        let mut target = if foreign_executor {
            load(SQUARE)
        } else {
            original
        };
        open(&mut target, &[]);
        let scope = target.authenticate_unsat_query_scope(&[], true).unwrap();
        assert!(prepared.bind(scope, &mut target).is_none());
        assert!(!target.has_strict_native_nra_sos_bundle_state());
    }
}

fn assumed_fixture() -> (Box<Executor>, Vec<TermId>) {
    let mut executor = load("(declare-const x Real) (assert (>= x 1.0))");
    let x = executor.ctx.symbol_info("x").unwrap().term.unwrap();
    let zero = executor
        .ctx
        .terms
        .mk_rational(BigRational::from_integer(0.into()));
    let two = executor
        .ctx
        .terms
        .mk_rational(BigRational::from_integer(2.into()));
    let upper = executor.ctx.terms.mk_le(x, zero);
    let extra = executor.ctx.terms.mk_le(x, two);
    let assumptions = vec![upper, extra];
    open(&mut executor, &assumptions);
    (executor, assumptions)
}

#[test]
fn supplied_assumptions_must_match_the_ordered_bound_partition() {
    let (mut executor, assumptions) = assumed_fixture();
    for supplied in [
        vec![],
        vec![assumptions[0]],
        vec![assumptions[1], assumptions[0]],
    ] {
        let rejected = executor.prepare_strict_native_nra_sos_bundle(&supplied);
        assert!(!matches!(rejected, Ok(Some(_))));
        assert!(!executor.has_strict_native_nra_sos_bundle_state());
    }
    install(&mut executor, &assumptions);
    assert!(has_current_bundle(&executor));
}

#[test]
fn moving_a_root_between_source_partitions_cannot_reuse_prepared_evidence() {
    let (mut executor, assumptions) = assumed_fixture();
    let original_roots = executor
        .ctx
        .assertions
        .iter()
        .chain(&assumptions)
        .copied()
        .collect::<Vec<_>>();
    let prepared = prepare(&mut executor, &assumptions);
    executor.ctx.assertions.push(assumptions[0]);
    open(&mut executor, &assumptions[1..]);
    let current_roots = executor
        .ctx
        .assertions
        .iter()
        .chain(&assumptions[1..])
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(
        original_roots, current_roots,
        "flattened roots alone are insufficient"
    );
    let scope = executor
        .authenticate_unsat_query_scope(&assumptions[1..], true)
        .unwrap();
    assert!(prepared.bind(scope, &mut executor).is_none());
}

#[test]
fn consumed_certificate_keeps_current_export_but_not_changed_solver_assumptions() {
    let (mut executor, assumptions) = assumed_fixture();
    install(&mut executor, &assumptions);
    assert!(executor
        .take_unsat_certificate()
        .unwrap()
        .strict_proof_verified());
    assert!(has_current_bundle(&executor));
    executor.last_assumptions = Some(vec![assumptions[1], assumptions[0]]);
    assert!(executor.has_strict_native_nra_sos_bundle_state());
    assert!(!has_current_bundle(&executor));
}

#[test]
fn arena_append_metadata_and_replacement_each_retire_sealed_authority() {
    for mutation in 0..3 {
        let mut executor = sealed();
        match mutation {
            0 => {
                executor.ctx.terms.mk_var("late", CoreSort::Real);
            }
            1 => {
                let stamp = executor.ctx.terms.snapshot_stamp();
                executor.ctx.terms.mark_to_real_shadowed();
                assert_eq!(executor.ctx.terms.snapshot_stamp(), stamp);
            }
            _ => {
                executor.ctx.terms = executor.ctx.terms.clone();
            }
        }
        // Presence stays visible so an exporter must not fall through to a
        // generic fresh bundle merely because sealed currentness now fails.
        assert!(executor.has_strict_native_nra_sos_bundle_state());
        assert!(!has_current_bundle(&executor));
        assert!(executor.take_unsat_certificate().is_none());
    }
}

#[test]
fn rollback_generation_retires_identical_retained_term_contents() {
    let mut executor = sealed();
    let entries = executor.ctx.terms.entries_snapshot();
    let checkpoint = executor.ctx.terms.rollback_checkpoint();
    // No scratch handle escapes or is retained by the proof/state.
    executor
        .ctx
        .terms
        .mk_var("discarded_scratch", CoreSort::Real);
    executor.ctx.terms.rollback_to(checkpoint);
    assert_eq!(executor.ctx.terms.entries_snapshot(), entries);
    assert!(!has_current_bundle(&executor));
    assert!(executor.take_unsat_certificate().is_none());
}

/// A checked native SOS theorem the Alethe lowering declines (its product
/// multiplies a `Real` and an `Int` factor), so it keeps a real wire gap:
/// `(x-1)(n-1) + (-x)(n-1) + 2(n-1) + (-n) = -1`.
fn declined_native_sos_step(executor: &mut Executor) -> ProofStep {
    use ay_core::{NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, Symbol};
    let terms = &mut executor.ctx.terms;
    let x = terms.mk_var("declined_sos_real", CoreSort::Real);
    let n = terms.mk_var("declined_sos_int", CoreSort::Int);
    let [real_zero, real_one] =
        [0u8, 1u8].map(|value| terms.mk_rational(BigRational::from_integer(value.into())));
    let [int_zero, int_one] = [0u8, 1u8].map(|value| terms.mk_int(value.into()));
    let mut compare =
        |left, right| terms.mk_app(Symbol::named("<="), [left, right], CoreSort::Bool);
    let sources = [
        compare(real_one, x),
        compare(x, real_zero),
        compare(int_one, n),
        compare(n, int_zero),
    ];
    let clause = sources.into_iter().map(|s| terms.mk_not(s)).collect();
    let rational = |value: i64| NraSosRational {
        numerator: value.into(),
        denominator: 1.into(),
    };
    let term = |origin, value| NraSosTerm {
        origin,
        multiplier: rational(value),
    };
    let product = |left, right| NraSosOrigin::Product { left, right };
    let literal = |position| NraSosOrigin::ClauseLiteral { position };
    ProofStep::NraSos {
        clause,
        certificate: NraSosCertificate {
            basis: vec![vec![]],
            gram: vec![vec![rational(0)]],
            terms: vec![
                term(product(0, 2), 1),
                term(product(1, 2), 1),
                term(literal(2), 2),
                term(literal(3), 1),
            ],
            rhs: rational(-1),
        },
    }
}

#[test]
fn even_a_valid_extra_empty_derivation_cannot_inherit_the_wire_gap_exception() {
    let mut executor = sealed();
    // The sealed square itself now lowers to checked Alethe, so the extra
    // derivation carries the gap: a valid native theorem the lowering declines.
    assert!(!executor.proof_has_known_wire_gap(executor.last_proof.as_ref().unwrap()));
    let declined = declined_native_sos_step(&mut executor);
    let proof = executor.last_proof.as_mut().unwrap();
    let extra = proof.steps.last().unwrap().clone();
    assert!(matches!(&extra, ProofStep::Resolution { clause, .. } if clause.is_empty()));
    proof.steps.insert(proof.steps.len() - 1, declined);
    proof.steps.push(extra);
    let proof = executor.last_proof.as_ref().unwrap();
    assert!(executor.proof_has_known_wire_gap(proof));
    assert!(executor
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    assert!(!has_current_bundle(&executor));
    assert!(executor
        .decline_trust_bearing_unsat_under_strict_proofs(SolveResult::unsat())
        .is_unknown());
    assert!(executor.last_unsat_certificate.is_none());
}

#[test]
fn new_source_declarations_and_new_public_queries_revoke_export_state() {
    for change_source in [false, true] {
        let mut executor = sealed();
        if change_source {
            executor
                .execute_all(&parse("(declare-const later Real)").unwrap())
                .unwrap();
        } else {
            open(&mut executor, &[]);
        }
        assert!(!has_current_bundle(&executor));
        assert!(executor.take_unsat_certificate().is_none());
    }
}
