// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Production parse/solve controls, with no manually installed consequences.
//! These are authored expectations; runtime qualification is recorded apart.

use super::*;
use crate::executor::model::EvalValue;
use ay_core::{ProofId, Symbol};
use ay_frontend::{parse, Command};
use num_bigint::BigInt;
use std::time::Duration;

// Kept with the crate because public exports intentionally omit benchmarks/.
// Byte-identical to benchmarks/smt/model_checker_consumer_chc/native_wide_array_diamond_sat.smt2.
const WIDE: &str = include_str!("tests/native_wide_array_diamond_sat.smt2");

fn execute(executor: &mut Executor, source: &str) -> Vec<String> {
    executor.execute_all(&parse(source).unwrap()).unwrap()
}

enum ProofDemand {
    Ordinary,
    Required,
}

fn setup(proofs: ProofDemand) -> Executor {
    let mut executor = Executor::new();
    // PER-EXECUTOR term ceiling, not the process footprint. `set_memory_limit`
    // is documented as a process-RSS bound (`crate::memory`), and this whole
    // suite is ONE process: by the time these cases run, roughly 5000 earlier
    // solver tests have left the live footprint around 230 MiB against a peak
    // of ~1.5 GiB, so a 256 MiB process bound is decided by allocator
    // retention this query never caused. Measured: these four flipped to
    // `unknown` in the full `ay-dpll` run while passing in isolation and in
    // their own module (0.06s), with no input difference -- the exact hazard
    // `crate::memory::probe_may_run_under_limit` records. The per-executor
    // ceiling charges only this solve's own term store, so the blow-up guard
    // these cases want survives and the cross-test coupling does not.
    executor.set_term_memory_limit(Some(256 * 1024 * 1024));
    executor.set_timeout(Some(Duration::from_secs(10)));
    if matches!(proofs, ProofDemand::Required) {
        execute(&mut executor, "(set-option :produce-proofs true)");
    }
    let mut found = false;
    for command in parse(WIDE).unwrap() {
        if matches!(command, Command::CheckSat) {
            found = true;
            break;
        }
        executor.execute(&command).unwrap();
    }
    assert!(found, "the retained fixture includes its actual query");
    executor
}

fn assert_installed(executor: &Executor) {
    for key in [
        "smt.abv.guarded_store.definitions",
        "smt.abv.guarded_store.derived_units",
    ] {
        assert!(
            executor
                .last_statistics
                .get_int(key)
                .is_some_and(|count| count > 0),
            "the production route must install checked units: {key}; {:?}",
            executor.last_statistics
        );
    }
}

fn scalar_value(executor: &Executor, term: TermId) -> BigInt {
    match executor.evaluate_term(executor.last_model.as_ref().unwrap(), term) {
        EvalValue::BitVec { value, width: 129 } => value,
        value => panic!("expected an exact BV129 value, got {value:?}"),
    }
}

fn diagnose_unsat_refusal(executor: &Executor, originals: &[TermId]) {
    const LIMIT: usize = 64;
    eprintln!("wide-diamond refusal; each section limited to {LIMIT} items");
    if let Some(proof) = executor.last_proof() {
        eprintln!("last proof: {} steps", proof.steps.len());
        for (index, step) in proof.steps.iter().take(LIMIT).enumerate() {
            eprintln!("proof t{index}: {step:?}");
        }
    } else {
        eprintln!("last proof: absent");
    }
    let records = &executor.propagated_value_provenance;
    eprintln!("retained entries: {}", records.entries.len());
    for (index, entry) in records.entries.iter().take(LIMIT).enumerate() {
        eprintln!(
            "entry {index} stamp={}: {:?} {} -> {:?} {}; source {:?} {}",
            entry.stamp,
            entry.expr,
            executor.format_term(entry.expr),
            entry.value,
            executor.format_term(entry.value),
            entry.source_assertion,
            executor.format_term(entry.source_assertion),
        );
    }
    eprintln!("retained rewrites: {}", records.rewrites.len());
    for (index, rewrite) in records.rewrites.iter().take(LIMIT).enumerate() {
        eprintln!(
            "rewrite {index} stamp={}: {:?} {} -> {:?} {}",
            rewrite.stamp,
            rewrite.before,
            executor.format_term(rewrite.before),
            rewrite.after,
            executor.format_term(rewrite.after),
        );
    }
    eprintln!(
        "retained checked array units: {}",
        records.array_units.len()
    );
    for (index, unit) in records.array_units.iter().take(LIMIT).enumerate() {
        eprintln!(
            "array unit {index}: {:?} {}",
            unit.term(),
            executor.format_term(unit.term()),
        );
    }
    eprintln!("original roots: {}", originals.len());
    for (index, &root) in originals.iter().take(LIMIT).enumerate() {
        eprintln!("original {index}: {root:?} {}", executor.format_term(root));
    }
}

#[test]
fn original_wide_diamond_public_sat_restores_roots_and_distinct_native_values() {
    let mut executor = setup(ProofDemand::Ordinary);
    let originals = executor.ctx.assertions.clone();
    let output = executor.execute(&Command::CheckSat).unwrap();
    assert_eq!(
        output.as_deref(),
        Some("sat"),
        "{:?}",
        executor.last_statistics
    );
    assert_installed(&executor);
    assert_eq!(executor.ctx.assertions, originals);
    assert_eq!(
        executor.proof_original_problem_assertions_slice(),
        originals
    );
    assert!(executor.last_result_is_sat());
    assert!(executor.was_model_validated());
    assert!(executor.last_model.is_some());
    assert!(
        executor.last_sat_certificate.is_none(),
        "text-command publication consumes its sealed SAT capability"
    );

    let x = executor
        .ctx
        .source_constant_for_value("__tree_q_x")
        .unwrap()
        .0;
    let y = executor
        .ctx
        .source_constant_for_value("__tree_q_y")
        .unwrap()
        .0;
    let x_value = scalar_value(&executor, x);
    let y_value = scalar_value(&executor, y);
    let high = BigInt::from(1u8) << 128usize;
    let next = &high + 1u8;
    assert_ne!(x_value, y_value);
    for value in [&x_value, &y_value] {
        assert!(value == &high || value == &next, "full high bits survive");
    }
    for (name, expected) in [("__tree_q_a", &x_value), ("__tree_q_b", &y_value)] {
        let array = executor.ctx.source_constant_for_value(name).unwrap().0;
        let key = executor.ctx.terms.mk_bitvec(7.into(), 8);
        let read =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("select"), [array, key], Sort::bitvec(129));
        assert_eq!(&scalar_value(&executor, read), expected);
    }
    let values = execute(
        &mut executor,
        "(get-value (__tree_q_x __tree_q_y
          (select __tree_q_a (_ bv7 8)) (select __tree_q_b (_ bv7 8))))",
    );
    assert_eq!(values.len(), 1);
    assert!(!values[0].starts_with("(error"), "{values:?}");
    for value in [&x_value, &y_value] {
        let literal = crate::executor_format::format_bitvec(value, 129);
        assert!(values[0].matches(&literal).count() >= 2, "{values:?}");
    }
    assert_eq!(executor.ctx.assertions, originals);
}

#[test]
fn original_wide_diamond_equal_fact_choices_have_a_source_authorized_unsat_proof() {
    let mut executor = setup(ProofDemand::Required);
    // Both first-fact choices force 2^128, contradicting the unchanged original
    // query x != y. No derived store definitions or aliases are asserted here.
    execute(&mut executor, "(assert __tree_ind_1) (assert __tree_ind_4)");
    let originals = executor.ctx.assertions.clone();
    let output = executor.execute(&Command::CheckSat).unwrap();
    if output.as_deref() != Some("unsat") {
        diagnose_unsat_refusal(&executor, &originals);
    }
    assert_eq!(
        output.as_deref(),
        Some("unsat"),
        "{:?}",
        executor.last_statistics
    );
    assert_installed(&executor);
    assert_eq!(executor.ctx.assertions, originals);
    assert_eq!(
        executor.proof_original_problem_assertions_slice(),
        originals
    );
    let proof = executor.last_proof().expect("public UNSAT proof required");
    let quality = ay_proof::check_proof_strict(proof, executor.terms())
        .expect("all structural and BV proof steps must check strictly");
    assert_eq!(quality.trust_count, 0, "{quality}");
    let checked = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        proof,
        executor.terms(),
        None,
        None,
        &originals,
        &mut |_, _| true,
    )
    .expect("derived working roots are not authored assumptions");
    let conclusion = ProofId(u32::try_from(proof.steps.len().checked_sub(1).unwrap()).unwrap());
    assert_eq!(checked.clause(conclusion), Some([].as_slice()));
}

#[test]
fn temporary_assumption_does_not_activate_the_source_only_preprocessing_owner() {
    let mut executor = Executor::new();
    // Per-executor term ceiling; see `setup` for the measured reason.
    executor.set_term_memory_limit(Some(256 * 1024 * 1024));
    executor.set_timeout(Some(Duration::from_secs(10)));
    execute(
        &mut executor,
        "(set-logic ALL)
         (declare-const a (Array (_ BitVec 1) (_ BitVec 129)))
         (declare-const p Bool) (declare-const g Bool) (declare-const h Bool)
         (assert (=> g (= a (store
           ((as const (Array (_ BitVec 1) (_ BitVec 129))) (_ bv0 129))
           (_ bv0 1) (_ bv340282366920938463463374607431768211456 129)))))
         (assert (=> h (= a (store
           ((as const (Array (_ BitVec 1) (_ BitVec 129))) (_ bv0 129))
           (_ bv0 1) (_ bv340282366920938463463374607431768211457 129)))))
         (assert (=> p (or g h)))",
    );
    let originals = executor.ctx.assertions.clone();
    assert_eq!(execute(&mut executor, "(check-sat-assuming (p))"), ["sat"]);
    assert_eq!(executor.ctx.assertions, originals);
    assert_eq!(
        executor
            .last_statistics
            .get_int("smt.abv.guarded_store.derived_units")
            .unwrap_or(0),
        0
    );
    assert!(executor.propagated_value_provenance.array_units.is_empty());
}

#[test]
fn source_owner_refusals_preserve_working_rows_and_query_local_unit_lifecycle() {
    let mut executor = setup(ProofDemand::Required);
    let originals = executor.ctx.assertions.clone();
    let mut source_sets: Vec<_> = originals.iter().map(|&term| vec![term]).collect();
    // A private route without the public original-source snapshot cannot use
    // the positional proof-source fallback to promote newly prepended units.
    executor.proof_problem_assertion_provenance = None;
    assert!(executor
        .prepare_guarded_store_preprocessing(&originals, &mut source_sets)
        .is_none());
    assert_eq!(executor.ctx.assertions, originals);
    assert_eq!(
        source_sets,
        originals.iter().map(|&term| vec![term]).collect::<Vec<_>>()
    );
    assert!(executor.propagated_value_provenance.array_units.is_empty());
    executor.begin_public_solve(false);
    let mut wrong = originals.clone();
    wrong.swap(0, 1);
    assert!(executor
        .prepare_guarded_store_preprocessing(&wrong, &mut source_sets)
        .is_none());
    assert_eq!(executor.ctx.assertions, originals);
    assert!(executor
        .prepare_guarded_store_preprocessing(&originals, &mut source_sets)
        .is_some());
    assert_installed(&executor);
    assert_eq!(
        executor.proof_original_problem_assertions_slice(),
        originals
    );
    assert!(!executor.propagated_value_provenance.array_units.is_empty());
    executor.clear_preprocessing_proof_records();
    assert!(executor.propagated_value_provenance.array_units.is_empty());
}
