// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::checker::bv_affine::guarded_mask_identity;
use ay_core::{Proof, TheoryLemmaKind};

#[test]
fn guarded_original_tls_have_native_and_external_proofs() {
    for (name, problem) in [
        (
            "range",
            include_str!("../../../../ay-dpll/tests/fixtures/guarded_range_tls.smt2"),
        ),
        (
            "mask",
            include_str!("../../../../ay-dpll/tests/fixtures/guarded_mask_tls.smt2"),
        ),
    ] {
        publish(name, problem);
    }
}

fn publish(name: &str, problem: &str) {
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(problem).unwrap() {
        context.process_command(&command).unwrap();
    }
    let parsed = context.assertions_parsed()[0].clone();
    let root = super::aggregate_tests::raw_fixture_term(&mut context, &parsed);
    let negated = context.terms.mk_not_raw(root);
    assert!(
        guarded_mask_identity(&context.terms, &[negated], &mut |_, _| true)
            .unwrap()
            .is_some(),
        "{name}"
    );
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "bv",
        vec![negated],
        TheoryLemmaKind::ArithClauseTautology,
    );
    proof.add_resolution(vec![], root, assume, lemma);
    crate::check_proof_strict(&proof, &context.terms).expect("native strict check");
    let text = crate::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &context.terms,
        &[root],
        None,
    )
    .unwrap();
    assert!(
        text.contains(":rule bitblast_equal") || text.contains(":rule bitblast_ult"),
        "{name}: {text}"
    );
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!(
        "ay-guarded-original-{name}-{}.json",
        std::process::id()
    ));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":text})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn guarded_widths_and_both_root_and_equality_orders_publish() {
    for width in [1u32, 9, 32, 64, 128] {
        let maximum = u128::MAX >> (128 - width);
        for range in [false, true] {
            let limit = 1u128 << (width - 1).min(24);
            let zeros = if range {
                maximum ^ (limit - 1)
            } else {
                (1u128 << width.min(3)) - 1
            };
            let keep = maximum ^ zeros;
            let literal = |value| format!("#b{value:0width$b}", width = width as usize);
            for reverse in [false, true] {
                let guard = if range {
                    format!("(bvult x {})", literal(limit))
                } else {
                    format!("(= {} (bvand {} x))", literal(0), literal(zeros))
                };
                let masked = format!("(bvand x {})", literal(keep));
                let negated = if reverse {
                    format!("(not (= {masked} x))")
                } else {
                    format!("(not (= x {masked}))")
                };
                let root = if reverse {
                    format!("(and {negated} {guard})")
                } else {
                    format!("(and {guard} {negated})")
                };
                let problem = format!("(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(assert {root})\n(check-sat)\n");
                publish(&format!("{width}-{range}-{reverse}"), &problem);
            }
        }
    }
}

#[test]
fn guarded_refuses_changed_guards_dropped_premises_overrides_and_budget() {
    use super::{AlethePrinter, DetHashMap, ProofId};
    for (problem, before, after) in [
        (
            include_str!("../../../../ay-dpll/tests/fixtures/guarded_range_tls.smt2"),
            "(_ bv16777216 64)",
            "(_ bv33554432 64)",
        ),
        (
            include_str!("../../../../ay-dpll/tests/fixtures/guarded_mask_tls.smt2"),
            "(_ bv7 64)",
            "(_ bv3 64)",
        ),
    ] {
        for changed in [false, true] {
            let problem = if changed {
                problem.replace(before, after)
            } else {
                problem.into()
            };
            let mut context = ay_frontend::Context::new();
            for command in ay_frontend::parse(&problem).unwrap() {
                context.process_command(&command).unwrap();
            }
            let parsed = context.assertions_parsed()[0].clone();
            let root = super::aggregate_tests::raw_fixture_term(&mut context, &parsed);
            let negated = context.terms.mk_not_raw(root);
            let info = guarded_mask_identity(&context.terms, &[negated], &mut |_, _| true).unwrap();
            assert_eq!(info.is_some(), !changed);
            if let Some(info) = info {
                assert!(
                    guarded_mask_identity(&context.terms, &[negated], &mut |_, _| false).is_err()
                );
                assert!(
                    guarded_mask_identity(&context.terms, &[info.equality], &mut |_, _| true)
                        .unwrap()
                        .is_none()
                );
                assert!(guarded_mask_identity(
                    &context.terms,
                    &[negated, info.guard],
                    &mut |_, _| true
                )
                .unwrap()
                .is_none());
                let mut overrides = DetHashMap::default();
                overrides.insert(info.guard, "true".into());
                assert!(
                    AlethePrinter::new_with_overrides(&context.terms, Some(&overrides))
                        .format_bv_guarded_mask_identity(ProofId(7), &[negated])
                        .is_none()
                );
                let printer =
                    AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(1024));
                assert!(printer
                    .format_bv_guarded_mask_identity(ProofId(7), &[negated])
                    .is_none());
                assert!(printer.work_budget_exhausted());
            }
        }
    }
}
