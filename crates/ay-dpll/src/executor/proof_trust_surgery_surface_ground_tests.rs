// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::Executor;
use ay_core::{Proof, TheoryLemmaKind};

fn process(executor: &mut Executor, source: &str) {
    for command in ay_frontend::parse(source).unwrap() {
        executor.ctx.process_command(&command).unwrap();
    }
}

#[test]
fn complete_memory_sources_rebuild_with_checked_original_assumptions() {
    let fixtures = [
        (
            "cell32",
            include_str!(
                "../../../ay-proof/src/alethe_printer/bv_packed/circuit/memory_fixtures/cell32.smt2"
            ),
        ),
        (
            "cell64",
            include_str!(
                "../../../ay-proof/src/alethe_printer/bv_packed/circuit/memory_fixtures/cell64.smt2"
            ),
        ),
    ];
    for (name, problem) in fixtures {
        let mut executor = Executor::new();
        process(&mut executor, problem);
        let parsed = executor.ctx.assertions_parsed()[0].clone();
        assert!(
            executor.raw_intern_surface(&parsed).is_none(),
            "generic policy stays closed"
        );
        println!(
            "ground source {name}: work={:?}",
            work(&parsed, Some(&executor.ctx))
        );
        let root = executor.raw_intern_ground_bv_surface(&parsed).expect(name);
        let negative = executor.ctx.terms.mk_not_raw(root);
        let mut proof = Proof::new();
        let assume = proof.add_assume(root, None);
        let lemma =
            proof.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(vec![], root, assume, lemma);
        ay_proof::check_proof_strict(&proof, &executor.ctx.terms).unwrap();
        let text = ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
            &proof,
            &executor.ctx.terms,
            &[root],
            None,
            None,
        )
        .unwrap();
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
        let path = std::env::temp_dir().join(format!(
            "ay-ground-source-{name}-{}.json",
            std::process::id()
        ));
        std::fs::write(
            &path,
            serde_json::to_vec(&serde_json::json!({
                "type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":text
            }))
            .unwrap(),
        )
        .unwrap();
        println!("independent replay certificate: {}", path.display());
    }
}

#[test]
fn ground_source_preserves_shadowed_declarations_and_refuses_macro_work() {
    let mut executor = Executor::new();
    process(
        &mut executor,
        "(declare-fun rem ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8)) (declare-const x (_ BitVec 8)) (assert (= (rem x x) x))",
    );
    let parsed = executor.ctx.assertions_parsed()[0].clone();
    let private = executor
        .ctx
        .symbol_info("rem")
        .unwrap()
        .internal_name
        .clone()
        .unwrap();
    assert_ne!(private, "rem");
    let ordinary = executor.raw_intern_surface(&parsed).unwrap();
    let mut pending = vec![ordinary];
    let mut found = false;
    while let Some(term) = pending.pop() {
        if let ay_core::term::TermData::App(ay_core::Symbol::Named(head), _) =
            executor.ctx.terms.get(term)
        {
            found |= head.as_str() == private;
            assert_ne!(head.as_str(), "rem");
        }
        pending.extend(executor.ctx.terms.children(term));
    }
    assert!(
        found,
        "the declared private identity must survive reconstruction"
    );
    assert_eq!(
        executor.raw_intern_ground_bv_surface(&parsed),
        Some(ordinary)
    );
    process(
        &mut executor,
        "(define-fun duplicate ((a (_ BitVec 8))) (_ BitVec 8) (bvadd a a)) (define-fun named () (_ BitVec 8) x)",
    );
    for source in ["(assert (= (duplicate x) x))", "(assert (= named x))"] {
        process(&mut executor, source);
        let parsed = executor.ctx.assertions_parsed().last().unwrap().clone();
        assert!(executor.raw_intern_ground_bv_surface(&parsed).is_none());
    }
}

#[test]
fn ground_source_declines_depth_width_bytes_binders_and_bad_types() {
    let leaf = Term::Const(Constant::True);
    let mut deep = leaf.clone();
    for _ in 0..97 {
        deep = Term::App("not".into(), vec![deep]);
    }
    assert!(work(&deep, None).is_none());
    let broad = Term::App(
        "and".into(),
        vec![Term::App("and".into(), vec![leaf; 128]); 128],
    );
    assert!(work(&broad, None).is_none());
    let text = Term::Symbol("x".repeat(4096));
    let mut heavy = Term::App("and".into(), vec![text; 128]);
    for _ in 0..16 {
        heavy = Term::App("not".into(), vec![heavy]);
    }
    assert!(work(&heavy, None).is_none());
    let mut executor = Executor::new();
    process(&mut executor, "(declare-const x (_ BitVec 8))");
    for source in [
        "(assert (forall ((b Bool)) b))",
        "(assert (! true :named tagged))",
    ] {
        process(&mut executor, source);
        let parsed = executor.ctx.assertions_parsed().last().unwrap().clone();
        assert!(executor.raw_intern_ground_bv_surface(&parsed).is_none());
    }
    let malformed = Term::App("bvadd".into(), vec![Term::Symbol("x".into())]);
    assert!(executor.raw_intern_ground_bv_surface(&malformed).is_none());
    let mistyped = Term::App(
        "bvadd".into(),
        vec![Term::Symbol("x".into()), Term::Const(Constant::True)],
    );
    assert!(executor.raw_intern_ground_bv_surface(&mistyped).is_none());
}
