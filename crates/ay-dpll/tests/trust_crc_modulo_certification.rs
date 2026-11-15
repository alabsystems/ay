// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trust's actual CRC summary must carry a checked proof through both public
//! entry points. The SMT fixtures are byte-exact shared-exporter output; the
//! native builder uses the same unsigned bounds and Rust-remainder ITE.

use ay_dpll::api::{
    re_check_bundle_strict, re_check_bundle_strict_with_cancellation, Logic, ProofCheckError,
    SerializableProofBundle, Solver, Sort, StrictProofVerdict, Term,
};
use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::authenticate_bv_lia_unsat_query;
use ntest::timeout;

const ORIGINAL: &str = include_str!("fixtures/trust_crc_modulo/original.smt2");
const WRONG_ZERO: &str = include_str!("fixtures/trust_crc_modulo/wrong-zero.smt2");
const OPPOSITE_ARM: &str = include_str!("fixtures/trust_crc_modulo/opposite-arm.smt2");
const RANGE: &str = include_str!("fixtures/trust_crc_modulo/plain-range.smt2");

#[test]
#[timeout(60_000)]
fn crc_source_queries_authenticate_before_solver_dispatch() {
    let mut mismatches = Vec::new();
    for (name, problem, unsat) in [
        ("original", ORIGINAL, true),
        ("range", RANGE, true),
        ("wrong-zero", WRONG_ZERO, false),
        ("opposite-arm", OPPOSITE_ARM, false),
    ] {
        assert_eq!(problem.matches("(check-sat)").count(), 1);
        let commands = parse(&problem.replace("(check-sat)", "")).expect("source parses");
        let mut executor = Executor::new();
        assert!(executor
            .execute_all(&commands)
            .expect("install source")
            .is_empty());
        let context = executor.context();
        let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(5);
        let result =
            authenticate_bv_lia_unsat_query(&context.terms, &context.assertions, Some(deadline));
        if result.is_ok() != unsat {
            mismatches.push(format!("{name}: {result:?}"));
            for term in context.terms.term_ids() {
                println!("{name} {term:?}: {:?}", context.terms.get(term));
            }
        }
    }
    assert!(mismatches.is_empty(), "{mismatches:?}");
}

fn parsed_verdict(problem: &str, expected: &str) {
    let script = format!(
        "(set-option :produce-proofs true)\n\
         (set-option :check-proofs-strict true)\n\
         (set-option :timeout 5000)\n{problem}"
    );
    let commands = parse(&script).expect("captured problem parses");
    let mut executor = Executor::new();
    let output = executor.execute_all(&commands).expect("problem executes");
    assert_eq!(
        output,
        [expected],
        "unknown reason: {:?}; retained proof: {:?}",
        executor.unknown_reason(),
        executor.last_proof(),
    );
    if expected == "unsat" {
        let proof = executor.last_proof().expect("proof retained");
        let quality = ay_proof::check_proof_strict(proof, executor.terms())
            .expect("strict checker accepts the full proof");
        assert!(quality.is_complete(), "{quality}");
        assert_eq!(quality.trust_count, 0);
    }
}

#[test]
#[timeout(60_000)]
fn parsed_actual_crc_summary_certifies() {
    parsed_verdict(ORIGINAL, "unsat");
}

#[test]
#[timeout(60_000)]
fn parsed_binary_remainder_domain_certifies() {
    parsed_verdict(RANGE, "unsat");
}

#[test]
#[timeout(60_000)]
fn parsed_false_summaries_remain_satisfiable() {
    parsed_verdict(WRONG_ZERO, "sat");
    parsed_verdict(OPPOSITE_ARM, "sat");
}

#[test]
#[timeout(60_000)]
fn parsed_assumption_checks_preserve_remainder_proofs_and_sat_controls() {
    for (problem, verdict) in [(RANGE, "unsat"), (WRONG_ZERO, "sat"), (OPPOSITE_ARM, "sat")] {
        let problem = problem.replace(
            "(check-sat)",
            "(declare-const crc_assumption Bool)\n(check-sat-assuming (crc_assumption))",
        );
        parsed_verdict(&problem, verdict);
    }
}

#[derive(Clone, Copy)]
enum Claim {
    Actual,
    WrongZero,
    OppositeArm,
}

fn push_u32_bounds(solver: &mut Solver, conjuncts: &mut Vec<Term>, value: Term) {
    let zero = solver.int_const(0);
    let maximum = solver.int_const(4_294_967_295_i64);
    conjuncts.push(solver.le(zero, value));
    conjuncts.push(solver.le(value, maximum));
}

fn native_crc(solver: &mut Solver, claim: Claim) {
    let out = solver.declare_const("__trust_u__0", Sort::Int);
    let selected = solver.declare_const("__trust_u__2", Sort::Int);
    let crc = solver.declare_const("__trust_u_crc", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let polynomial = solver.int_const(3_988_292_384_i64);
    let nonnegative = solver.ge(crc, zero);
    let positive_mod = solver.modulo(crc, two);
    let negated_crc = solver.neg(crc);
    let negative_mod = solver.modulo(negated_crc, two);
    let negative_rem = solver.neg(negative_mod);
    let rem = solver.ite(nonnegative, positive_mod, negative_rem);
    let even = solver.eq(rem, zero);
    let odd = solver.eq(rem, one);
    let selected_zero = solver.eq(selected, zero);
    let selected_polynomial = solver.eq(selected, polynomial);
    let even_arm = solver.implies(even, selected_zero);
    let not_even = solver.not(even);
    let odd_arm = solver.implies(not_even, selected_polynomial);
    let linked = solver.eq(out, selected);
    let out_zero = solver.eq(out, zero);
    let out_polynomial = solver.eq(out, polynomial);
    let summary = match claim {
        Claim::WrongZero => out_zero,
        Claim::Actual | Claim::OppositeArm => {
            let (even_value, odd_value) = match claim {
                Claim::Actual => (out_zero, out_polynomial),
                _ => (out_polynomial, out_zero),
            };
            let even_result = solver.and(even, even_value);
            let odd_result = solver.and(odd, odd_value);
            solver.or(even_result, odd_result)
        }
    };
    let violated = solver.not(summary);
    let mut conjuncts = Vec::new();
    for value in [selected, out, selected, out] {
        push_u32_bounds(solver, &mut conjuncts, value);
    }
    if !matches!(claim, Claim::WrongZero) {
        push_u32_bounds(solver, &mut conjuncts, out);
    }
    conjuncts.extend([even_arm, odd_arm]);
    push_u32_bounds(solver, &mut conjuncts, crc);
    conjuncts.extend([linked, violated]);
    let problem = solver.and_many(&conjuncts);
    solver
        .try_assert_named(problem, "crc-summary")
        .expect("assert");
}

fn replay_original_bundle(solver: &Solver, bundle: SerializableProofBundle) {
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("native artifact");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(quality) if quality.is_complete() && quality.trust_count == 0
    ));
    let json = serde_json::to_vec(&bundle).expect("serialize native bundle");
    let reread: SerializableProofBundle = serde_json::from_slice(&json).expect("reread bundle");
    let replay = re_check_bundle_strict(&reread).expect("independent offline source replay");
    assert!(replay.quality.is_complete());
    assert_eq!(replay.quality.trust_count, 0);
    assert!(matches!(
        re_check_bundle_strict_with_cancellation(&reread, &mut || false),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut missing_source = reread.clone();
    missing_source.obligation_assertions.clear();
    assert!(re_check_bundle_strict(&missing_source).is_err());
    let mut truncated_proof = reread;
    truncated_proof.steps.pop().expect("nonempty proof");
    assert!(re_check_bundle_strict(&truncated_proof).is_err());
}

#[test]
#[timeout(60_000)]
fn parsed_actual_crc_bundle_binds_exact_source() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(ORIGINAL)
        .expect("exact source");
    assert!(solver.check_sat().was_unsat_strictly_verified());
    let bundle = solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .expect("exact source bundle");
    replay_original_bundle(&solver, bundle);
    solver.try_reset().expect("reset source epoch");
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
    solver.parse_smtlib2(WRONG_ZERO).expect("new SAT epoch");
    assert!(solver.check_sat().is_sat());
    assert!(solver.export_last_unsat_bundle().is_none());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
}

#[test]
#[timeout(60_000)]
fn native_actual_crc_summary_certifies() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    native_crc(&mut solver, Claim::Actual);
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "expected UNSAT: {:?}, {:?}, {:?}",
        details.result.result(),
        details.unknown_reason,
        details.executor_error,
    );
    assert!(details.result.was_unsat_strictly_verified());
    assert!(details.verification.unsat_proof_available);
    assert_eq!(details.verification.unsat_proof_checker_failures, 0);
    assert_eq!(solver.try_get_unsat_core().expect("core"), ["crc-summary"]);
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("native source bundle");
    replay_original_bundle(&solver, bundle);
}

#[test]
#[timeout(60_000)]
fn native_false_summaries_remain_satisfiable() {
    for claim in [Claim::WrongZero, Claim::OppositeArm] {
        let mut solver = Solver::try_new(Logic::All).expect("solver");
        solver.set_produce_proofs(true);
        solver.set_produce_unsat_cores(true);
        native_crc(&mut solver, claim);
        let details = solver.check_sat_with_details();
        assert!(details.result.is_sat(), "{:?}", details.unknown_reason);
        let model = solver.model_map().expect("SAT model");
        let crc = model["__trust_u_crc"].as_int().expect("integer CRC");
        let out = model["__trust_u__0"].as_int().expect("integer result");
        let expected = if crc % 2 == 0.into() {
            0
        } else {
            3_988_292_384_i64
        };
        assert_eq!(out, &expected.into(), "model satisfies the actual summary");
        if matches!(claim, Claim::WrongZero) {
            assert_ne!(out, &0.into(), "model violates the false zero claim");
        }
    }
}

#[test]
#[timeout(60_000)]
fn an_assumption_dependent_mod_proof_cannot_outlive_its_source() {
    let mut solver = Solver::try_new(Logic::QfNia).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":produce-unsat-assumptions", "true")
        .expect("assumption core option");
    let enabled = solver.declare_const("mod_enabled", Sort::Bool);
    let disabled = solver.not(enabled);
    let x = solver.declare_const("mod_source", Sort::Int);
    let two = solver.int_const(2);
    let remainder = solver.modulo(x, two);
    let impossible = solver.eq(remainder, two);
    let guarded = solver.implies(enabled, impossible);
    solver.try_assert_term(guarded).expect("guarded source");
    let result = solver.check_sat_assuming_with_details(&[enabled]);
    assert!(
        result.solve.result.was_unsat_strictly_verified(),
        "{:?}",
        result.solve.unknown_reason
    );
    assert_eq!(result.unsat_assumptions, Some(vec![enabled]));
    assert_eq!(solver.unsat_assumptions(), Some(vec![enabled]));
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("assumption-bound native proof");
    replay_original_bundle(&solver, bundle.clone());
    assert_eq!(bundle.obligation_assertions, [guarded.id(), enabled.id()]);
    let mut missing_assumption = bundle;
    assert_eq!(
        missing_assumption.obligation_assertions.pop(),
        Some(enabled.id())
    );
    assert!(re_check_bundle_strict(&missing_assumption).is_err());
    for assumptions in [vec![disabled], vec![]] {
        assert!(solver.check_sat_assuming(&assumptions).is_sat());
        assert!(solver.export_last_unsat_bundle().is_none());
        assert!(solver.unsat_assumptions().is_none());
    }
}
