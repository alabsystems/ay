// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const ORIGINAL: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/external_codegen_actual_e1_outside_local.smt2"
));

fn prepared(input: &str) -> (Executor, Vec<TermId>) {
    let mut exec = Executor::new();
    for command in parse(input).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            exec.execute_authored(&command).unwrap();
        }
    }
    let surfaces = exec.ctx.assertions_parsed().to_vec();
    let roots = surfaces
        .iter()
        .map(|surface| exec.raw_intern_ground_bv_surface(surface).unwrap())
        .collect();
    (exec, roots)
}

#[test]
fn existing_checked_rules_prove_actual_width_conditional_store_miss() {
    let input = "(set-option :produce-proofs true)\n(set-logic QF_BV)\n\
        (declare-const point (_ BitVec 64))\n\
        (declare-const base (_ BitVec 64))\n\
        (assert (not (bvult (bvsub point base) (_ bv16 64))))\n\
        (assert (= point (bvadd base (_ bv7 64))))\n(check-sat)\n";
    let (mut exec, roots) = prepared(input);
    let TermData::Not(range) = *exec.ctx.terms.get(roots[0]) else {
        panic!("negative outside-range premise");
    };
    let equality = roots[1];
    let disequality = exec.ctx.terms.mk_not_raw(equality);
    let (point, index) = decode_eq_local(&exec.ctx.terms, equality).unwrap();
    let TermData::App(_, range_args) = exec.ctx.terms.get(range).clone() else {
        panic!("range predicate");
    };
    let delta = range_args[0];
    let bound = range_args[1];
    let TermData::App(_, index_args) = exec.ctx.terms.get(index).clone() else {
        panic!("source index");
    };
    let base = index_args[0];
    let offset = index_args[1];
    let image_delta = exec.ctx.terms.mk_app(
        Symbol::named("bvsub"),
        [index, base],
        exec.ctx.terms.sort(point).clone(),
    );
    let joined = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [delta, image_delta], Sort::Bool);
    let evaluated = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [image_delta, offset], Sort::Bool);
    let constant_delta = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [delta, offset], Sort::Bool);
    let closed_range = exec
        .ctx
        .terms
        .mk_app(Symbol::named("bvult"), [offset, bound], Sort::Bool);
    let predicate_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [range, closed_range], Sort::Bool);
    assert!(exec.recognize_bv_bitblast_until_stopped(&[evaluated]));
    assert!(exec.recognize_bv_bitblast_until_stopped(&[closed_range]));
    let not_joined = exec.ctx.terms.mk_not_raw(joined);
    let not_evaluated = exec.ctx.terms.mk_not_raw(evaluated);
    let not_constant_delta = exec.ctx.terms.mk_not_raw(constant_delta);
    let not_closed_range = exec.ctx.terms.mk_not_raw(closed_range);
    let not_predicate_equality = exec.ctx.terms.mk_not_raw(predicate_equality);
    let mut proof = Proof::new();
    let congruent = proof.add_theory_lemma_with_kind(
        "euf",
        vec![disequality, joined],
        TheoryLemmaKind::EufCongruent,
    );
    let arithmetic = proof.add_theory_lemma_with_kind(
        "arith",
        vec![evaluated],
        TheoryLemmaKind::ArithClauseTautology,
    );
    let transitive = proof.add_theory_lemma_with_kind(
        "euf",
        vec![not_joined, not_evaluated, constant_delta],
        TheoryLemmaKind::EufTransitive,
    );
    let transitive = proof.add_resolution(
        vec![not_joined, constant_delta],
        evaluated,
        transitive,
        arithmetic,
    );
    let conditional_delta = proof.add_resolution(
        vec![disequality, constant_delta],
        joined,
        congruent,
        transitive,
    );
    let closed =
        proof.add_theory_lemma_with_kind("bv", vec![closed_range], TheoryLemmaKind::BvBitBlast);
    let predicate = proof.add_theory_lemma_with_kind(
        "euf",
        vec![not_constant_delta, predicate_equality],
        TheoryLemmaKind::EufCongruent,
    );
    let logical = proof.add_rule_step(
        AletheRule::EquivPos1,
        vec![not_predicate_equality, range, not_closed_range],
        Vec::new(),
        Vec::new(),
    );
    let logical = proof.add_resolution(
        vec![not_predicate_equality, range],
        closed_range,
        logical,
        closed,
    );
    let predicate = proof.add_resolution(
        vec![not_constant_delta, range],
        predicate_equality,
        predicate,
        logical,
    );
    let conditional_miss = proof.add_resolution(
        vec![disequality, range],
        constant_delta,
        conditional_delta,
        predicate,
    );
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::Assume(_))));
    let outside = proof.add_assume(roots[0], None);
    let aliases = proof.add_assume(equality, None);
    let range_unit = proof.add_resolution(vec![range], equality, conditional_miss, aliases);
    proof.add_resolution(Vec::new(), range, range_unit, outside);
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    let overrides = exec.proof_export_term_overrides();
    let surfaces = exec.authored_export_surfaces();
    let text = exec
        .in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces(
                &proof,
                &exec.ctx.terms,
                &roots,
                overrides.as_ref(),
                surfaces.channels(),
                None,
            )
        })
        .expect("existing conditional BV guard must have an actual proof export");
    let directory =
        std::env::temp_dir().join(format!("ay-outside-range-preflight-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("guard64.smt2"), input).unwrap();
    std::fs::write(directory.join("guard64.alethe"), &text).unwrap();
    println!(
        "OUTSIDE_RANGE_GUARD64 steps={} bytes={} capture={}",
        proof.steps.len(),
        text.len(),
        directory.display()
    );
    assert!(
        !text.contains(":rule hole") && !text.contains(":rule trust"),
        "a kernel-valid guard still needs a complete actual wire proof"
    );
    let scope = ay_proof::ProblemScope::from_smtlib_source(input);
    ay_proof::check_alethe_document_in_dialect(&text, &scope, ay_proof::AletheDialect::Clean)
        .unwrap();
}

#[test]
fn actual_original_outside_requires_checked_miss_guards() {
    checked_actual_outside(ORIGINAL, "original-outside");
    checked_actual_outside(
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/external_codegen_actual_e1_outside_exit1_local.smt2"
        )),
        "original-outside-exit1",
    );
}

fn checked_actual_outside(input: &str, label: &str) {
    use sha2::{Digest, Sha256};
    let expected = match label {
        "original-outside" => (
            13_335,
            "c4c75dc0ff5380a029f129d7f1760fc25e1d8827b5bcecc26a95992c8279c119",
        ),
        "original-outside-exit1" => (
            16_494,
            "1f84fcb2a9dbbff0840a17282231f5fa0b54d70119c162b6774369ebf3a39af7",
        ),
        _ => panic!("unknown retained original"),
    };
    assert_eq!(input.len(), expected.0);
    assert_eq!(
        format!("{:x}", Sha256::digest(input.as_bytes())),
        expected.1
    );
    let _probe = ay_core::debug_channel::misc_test_override::set(
        ay_core::debug_channel::misc_cli_flags_with(|flags| flags.probe_cert_reject = true),
    );
    let (mut exec, roots) = prepared(input);
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    assert_eq!(roots.len(), 1);
    let candidate = exec.early_ground_closure_memory_candidate(roots[0]);
    assert!(
        candidate.is_some(),
        "the actual original outside-range query needs a source-backed guard bridge"
    );
    let proof = candidate.unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    assert!(proof
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::Assume(term) if *term != roots[0])));
    let overrides = exec.proof_export_term_overrides();
    let surfaces = exec.authored_export_surfaces();
    let text = exec
        .in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces(
                &proof,
                &exec.ctx.terms,
                &roots,
                overrides.as_ref(),
                surfaces.channels(),
                None,
            )
        })
        .expect("actual outside proof must export");
    let empty = ay_core::kani_compat::DetHashMap::default();
    let with_empty_context = exec
        .in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces(
                &proof,
                &exec.ctx.terms,
                &roots,
                Some(&empty),
                surfaces.channels(),
                None,
            )
        })
        .expect("a present unchanged surface context must preserve the complete congruence proof");
    assert_eq!(with_empty_context, text);
    let directory =
        std::env::temp_dir().join(format!("ay-outside-range-preflight-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join(format!("{label}.smt2")), input).unwrap();
    std::fs::write(directory.join(format!("{label}.alethe")), &text).unwrap();
    println!(
        "ACTUAL_OUTSIDE {label} steps={} bytes={} capture={}",
        proof.steps.len(),
        text.len(),
        directory.display()
    );
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn actual_outside_public_entry_preserves_source_export_context() {
    for (label, input) in [
        ("original-outside", ORIGINAL),
        (
            "original-outside-exit1",
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/fixtures/external_codegen_actual_e1_outside_exit1_local.smt2"
            )),
        ),
    ] {
        let mut exec = Executor::new();
        // Match the real CLI's external `--proof` request. The unchanged
        // original asks for models, and contains no produce-proofs option.
        exec.set_produce_proofs(true);
        exec.set_timeout(Some(std::time::Duration::from_secs(30)));
        exec.set_memory_limit(Some(8 * 1024 * 1024 * 1024));
        exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
        for command in parse(input).unwrap() {
            if !matches!(command, Command::CheckSat | Command::Exit) {
                exec.execute_authored(&command).unwrap();
            }
        }
        assert_eq!(
            exec.execute_authored(&Command::CheckSat)
                .unwrap()
                .as_deref(),
            Some("unsat")
        );
        let proof = exec.last_proof().unwrap();
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(proof)
            .unwrap()
            .is_complete());
        let directory =
            std::env::temp_dir().join(format!("ay-outside-range-public-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let overrides = exec.proof_export_term_overrides().unwrap_or_default();
        let mut inventory: Vec<_> = overrides
            .iter()
            .map(|(term, text)| format!("{term}\t{text}\n"))
            .collect();
        inventory.sort();
        std::fs::write(
            directory.join(format!("{label}-actual-overrides.txt")),
            inventory.concat(),
        )
        .unwrap();
        let text = exec.execute_authored(&Command::GetProof).unwrap().unwrap();
        std::fs::write(directory.join(format!("{label}.smt2")), input).unwrap();
        std::fs::write(directory.join(format!("{label}.alethe")), &text).unwrap();
        println!(
            "ACTUAL_OUTSIDE_PUBLIC {label} bytes={} actual_overrides={} capture={}",
            text.len(),
            overrides.len(),
            directory.display()
        );
        assert!(
            !text.starts_with("(error")
                && !text.contains(":rule hole")
                && !text.contains(":rule trust"),
            "{text}"
        );
    }
}
