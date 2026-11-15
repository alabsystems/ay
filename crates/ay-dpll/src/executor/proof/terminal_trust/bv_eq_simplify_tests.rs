// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, Symbol};

fn fixture() -> (Executor, Proof, TermId) {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let x = terms.mk_var("x", Sort::bitvec(64));
    let a = terms.mk_bitvec(0.into(), 64);
    let b = terms.mk_bitvec(1.into(), 64);
    let left = terms.mk_app(Symbol::named("bvadd"), [x, a], Sort::bitvec(64));
    let right = terms.mk_app(Symbol::named("bvadd"), [x, b], Sort::bitvec(64));
    let source = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [source, terms.false_term()], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::EqSimplify, vec![equality], vec![], vec![]);
    (executor, proof, left)
}

#[test]
fn bv_eq_simplify_wire_screen_requires_the_explicit_clean_dialect() {
    let (mut executor, proof, _) = fixture();
    executor.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    assert!(!executor.proof_has_known_wire_gap(&proof));
    executor.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
    assert!(executor.proof_has_known_wire_gap(&proof));
}

#[test]
fn bv_eq_simplify_wire_screen_refuses_a_changed_surface_or_unused_payload() {
    let (mut executor, mut proof, left) = fixture();
    executor.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    let mut overrides = DetHashMap::default();
    overrides.insert(left, "(bvadd y (_ bv0 64))".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    assert!(executor.proof_has_known_wire_gap(&proof));
    executor.last_proof_term_overrides = None;
    let ProofStep::Step { args, .. } = &mut proof.steps[0] else {
        panic!("simplification")
    };
    args.push(left);
    assert!(executor.proof_has_known_wire_gap(&proof));
}

#[test]
fn bv_offset_spines_wire_screen_requires_clean_exact_semantics_and_no_payload() {
    let (mut executor, mut proof, left) = fixture();
    let ProofStep::Step { rule, .. } = &mut proof.steps[0] else {
        panic!("rule")
    };
    *rule = AletheRule::BvOffsetSpinesV1;
    executor.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    assert!(!executor.proof_has_known_wire_gap(&proof));
    executor.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
    assert!(executor.proof_has_known_wire_gap(&proof));
    executor.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    let mut overrides = DetHashMap::default();
    overrides.insert(left, "(bvadd y (_ bv0 64))".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    assert!(executor.proof_has_known_wire_gap(&proof));
    executor.last_proof_term_overrides = None;
    let ProofStep::Step { args, .. } = &mut proof.steps[0] else {
        panic!("rule")
    };
    args.push(left);
    assert!(executor.proof_has_known_wire_gap(&proof));
}

#[test]
fn bv_reconstruct_wire_screen_requires_clean_exact_semantics_and_no_payload() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let x = terms.mk_var("x", Sort::bitvec(8));
    let full = terms.mk_app(
        Symbol::indexed("zero_extend", vec![0]),
        [x],
        Sort::bitvec(8),
    );
    let source = terms.mk_app(Symbol::named("="), [full, x], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::BvReconstructV1, vec![source], vec![], vec![]);
    executor.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    assert!(!executor.proof_has_known_wire_gap(&proof));
    executor.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
    assert!(executor.proof_has_known_wire_gap(&proof));
    executor.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    let mut overrides = DetHashMap::default();
    overrides.insert(x, "y".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    assert!(executor.proof_has_known_wire_gap(&proof));
    executor.last_proof_term_overrides = None;
    let ProofStep::Step { args, .. } = &mut proof.steps[0] else {
        panic!("rule")
    };
    args.push(x);
    assert!(executor.proof_has_known_wire_gap(&proof));
}

#[test]
fn bv_reconstruct_ten_retained_raw_sources_have_one_strict_native_and_exact_wire_proof() {
    let rows: serde_json::Value = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../ay-proof/src/checker/bv_reconstruct/tests/ten-packing-identities.json"
    )))
    .unwrap();
    let rows = rows.as_array().unwrap();
    assert_eq!(rows.len(), 10);
    let mut declarations = String::from("(set-option :produce-proofs true)\n(set-logic QF_BV)\n");
    let mut sources = Vec::new();
    for row in rows {
        let name = row["word"].as_str().unwrap();
        declarations.push_str(&format!("(declare-const {name} (_ BitVec 64))\n"));
        sources.push(row["pure_packing_equality"].as_str().unwrap());
    }
    let script = format!("{declarations}(assert (not (and {})))\n", sources.join(" "));
    let mut exec = Executor::new();
    exec.execute_all(&ay_frontend::parse(&script).unwrap())
        .unwrap();
    let source = exec.ctx.raw_reinternable_parsed_assertions()[0].clone();
    let denied_source = exec
        .raw_intern_ground_bv_surface(&source)
        .expect("existing bounded raw source owner");
    let terms = &mut exec.ctx.terms;
    let TermData::Not(conjunction) = terms.get(denied_source) else {
        panic!("authored negation")
    };
    let conjunction = *conjunction;
    let TermData::App(Symbol::Named(op), args) = terms.get(conjunction) else {
        panic!("and")
    };
    assert_eq!(op, "and");
    let sources = args.clone();
    assert_eq!(sources.len(), 10);
    let denied = terms.mk_not_raw(conjunction);
    assert_eq!(denied, denied_source, "actual raw authored assertion");
    let mut proof = Proof::new();
    let a = proof.add_assume(denied, None);
    let mut units = Vec::new();
    for (index, &source) in sources.iter().enumerate() {
        let mut single = Proof::new();
        let denied_one = terms.mk_not_raw(source);
        let assumed = single.add_assume(denied_one, None);
        let unit = single.add_rule_step(AletheRule::BvReconstructV1, vec![source], vec![], vec![]);
        single.add_resolution(vec![], source, assumed, unit);
        ay_proof::check_proof_strict_with_context(&single, terms, None, None, Some(&[denied_one]))
            .unwrap();
        let wire = ay_proof::with_alethe_dialect(ay_proof::AletheDialect::Clean, || {
            ay_proof::try_export_alethe_with_problem_scope_and_overrides(
                &single,
                terms,
                &[denied_one],
                None,
            )
        })
        .unwrap();
        if let Ok(dir) = std::env::var("AY_BV_RECONSTRUCT_ARTIFACT_DIR") {
            let name = rows[index]["word"].as_str().unwrap();
            let source_text = rows[index]["pure_packing_equality"].as_str().unwrap();
            let problem=format!("(set-logic QF_BV)\n(declare-const {name} (_ BitVec 64))\n(assert (not {source_text}))\n(check-sat)\n");
            let path = std::path::Path::new(&dir);
            std::fs::create_dir_all(path).unwrap();
            let write = |suffix: &str, text: &str| {
                std::fs::write(path.join(format!("original-{index:02}{suffix}.json")),serde_json::to_vec_pretty(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap()
            };
            write("", &wire);
            let original = format!("(cl {})", ay_proof::format_term_alethe(terms, source));
            let truth = terms.false_term();
            let wrong = terms.mk_app(Symbol::named("="), [source, truth], Sort::Bool);
            let replacement = format!("(cl {})", ay_proof::format_term_alethe(terms, wrong));
            assert!(wire.contains(&original));
            write("-wrong-truth", &wire.replacen(&original, &replacement, 1));
        }
        units.push(proof.add_rule_step(AletheRule::BvReconstructV1, vec![source], vec![], vec![]));
    }
    let mut clause = vec![conjunction];
    for &source in &sources {
        clause.push(terms.mk_not_raw(source));
    }
    let mut unit = proof.add_rule_step(AletheRule::AndNeg, clause.clone(), vec![], vec![]);
    for (&source, premise) in sources.iter().zip(units) {
        clause.remove(1);
        unit = proof.add_resolution(clause.clone(), source, unit, premise);
    }
    proof.add_resolution(vec![], conjunction, a, unit);
    let (mut work, mut bytes, mut attempts) = (0usize, 0usize, 0usize);
    ay_proof::check_proof_strict_with_context_and_progress(
        &proof,
        terms,
        None,
        None,
        Some(&[denied]),
        &mut |w, b| {
            work += w;
            bytes += b;
            if (w, b) == (524_288, 16_384) {
                attempts += 1;
            }
            work <= 350_000_000 && bytes <= 1_342_177_280
        },
    )
    .unwrap();
    assert_eq!(attempts, 10);
    let wire = ay_proof::with_alethe_dialect(ay_proof::AletheDialect::Clean, || {
        ay_proof::try_export_alethe_with_problem_scope_and_overrides(&proof, terms, &[denied], None)
    })
    .unwrap();
    assert_eq!(wire.matches(":rule bv_reconstruct_v1").count(), 10);
    if let Ok(dir) = std::env::var("AY_BV_RECONSTRUCT_ARTIFACT_DIR") {
        let problem = format!(
            "{declarations}(assert {})\n(check-sat)\n",
            ay_proof::format_term_alethe(terms, denied)
        );
        let dir = std::path::Path::new(&dir);
        std::fs::write(dir.join("all-ten.json"),serde_json::to_vec_pretty(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":wire})).unwrap()).unwrap();
        std::fs::write(dir.join("aggregate-native.json"),serde_json::to_vec_pretty(&serde_json::json!({"new_rule_attempts":attempts,"proof_steps":proof.steps.len(),"observed_native_work":work,"observed_native_bytes":bytes,"strict_native":true,"raw_source_owner":"raw_intern_ground_bv_surface","no_whole_E1_claim":true})).unwrap()).unwrap();
    }
}
