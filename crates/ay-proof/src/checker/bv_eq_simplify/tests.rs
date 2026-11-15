// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{AletheDialect, CleanOnlySpelling};
use ay_core::{AletheRule, Proof};

mod source_and_oracle;

fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

fn add(terms: &mut TermStore, left: TermId, right: TermId, width: u32) -> TermId {
    terms.mk_app(Symbol::named("bvadd"), [left, right], Sort::bitvec(width))
}

fn claim(terms: &mut TermStore, source: TermId, result: bool) -> TermId {
    let result = if result {
        terms.true_term()
    } else {
        terms.false_term()
    };
    eq(terms, source, result)
}

fn accepted(terms: &TermStore, root: TermId) -> bool {
    validate(terms, ProofId(0), &[root], 0, 0, &mut |_, _| true).is_ok()
}

#[test]
fn exhaustive_small_widths_match_modular_evaluation_in_all_placements() {
    for width in 1..=4 {
        let modulus = 1u128 << width;
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::bitvec(width));
        for a in 0..modulus {
            for b in 0..modulus {
                let expected = a == b;
                for value in 0..modulus {
                    assert_eq!((value + a) % modulus == (value + b) % modulus, expected);
                }
                let a_term = terms.mk_bitvec(a.into(), width);
                let b_term = terms.mk_bitvec(b.into(), width);
                for left_swapped in [false, true] {
                    for right_swapped in [false, true] {
                        let left = if left_swapped {
                            add(&mut terms, a_term, x, width)
                        } else {
                            add(&mut terms, x, a_term, width)
                        };
                        let right = if right_swapped {
                            add(&mut terms, b_term, x, width)
                        } else {
                            add(&mut terms, x, b_term, width)
                        };
                        let source = eq(&mut terms, left, right);
                        let correct = claim(&mut terms, source, expected);
                        let wrong = claim(&mut terms, source, !expected);
                        assert!(accepted(&terms, correct), "width={width} a={a} b={b}");
                        assert!(!accepted(&terms, wrong));
                        let literal_test = eq(&mut terms, a_term, b_term);
                        let cancelled = eq(&mut terms, source, literal_test);
                        assert!(accepted(&terms, cancelled));
                        let reversed = eq(&mut terms, literal_test, source);
                        assert!(accepted(&terms, reversed));
                    }
                }
            }
        }
    }
}

#[test]
fn literal_truth_and_wraparound_keep_the_exact_width() {
    for width in [1, 8, 64, 128] {
        let mut terms = TermStore::new();
        let max = u128::MAX >> (128 - width);
        let x = terms.mk_var("x", Sort::bitvec(width));
        let a = terms.mk_bitvec(max.into(), width);
        let b = terms.mk_bitvec(0.into(), width);
        let left = add(&mut terms, x, a, width);
        let right = add(&mut terms, x, b, width);
        let source = eq(&mut terms, left, right);
        let correct = claim(&mut terms, source, false);
        assert!(accepted(&terms, correct));
        let literal_test = eq(&mut terms, a, b);
        let correct = claim(&mut terms, literal_test, false);
        assert!(accepted(&terms, correct));
        // The public literal constructor canonicalizes the entire integer.
        let wrap = terms.mk_bitvec((num_bigint::BigInt::from(1u8) << width).into(), width);
        let equal_residues = eq(&mut terms, wrap, b);
        let wrong = claim(&mut terms, equal_residues, false);
        assert!(!accepted(&terms, wrong));
        let truth = claim(&mut terms, equal_residues, true);
        assert!(accepted(&terms, truth));
    }
}

#[test]
fn malformed_heads_sorts_widths_and_missing_common_base_fail_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let wide = terms.mk_var("wide", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 8);
    let one = terms.mk_bitvec(1.into(), 8);
    let right = add(&mut terms, x, one, 8);
    let bad = [
        add(&mut terms, y, zero, 8),
        add(&mut terms, wide, zero, 8),
        terms.mk_app(Symbol::named("bvsub"), [x, zero], Sort::bitvec(8)),
        terms.mk_app(
            Symbol::named("__ay_private_bvadd"),
            [x, zero],
            Sort::bitvec(8),
        ),
        terms.mk_app(Symbol::named("|bvadd|"), [x, zero], Sort::bitvec(8)),
        terms.mk_app(Symbol::indexed("bvadd", vec![]), [x, zero], Sort::bitvec(8)),
        terms.mk_app(Symbol::named("bvadd"), [x], Sort::bitvec(8)),
        terms.mk_app(Symbol::named("bvadd"), [x, zero, one], Sort::bitvec(8)),
        terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::Bool),
    ];
    for left in bad {
        let source = eq(&mut terms, left, right);
        let forged = claim(&mut terms, source, false);
        assert!(
            !accepted(&terms, forged),
            "{}",
            crate::format_term_alethe(&terms, forged)
        );
    }
    let source = eq(&mut terms, zero, one);
    let malformed_outer = terms.mk_app(Symbol::named("="), [source, terms.false_term()], Sort::Int);
    assert!(!accepted(&terms, malformed_outer));
    for width in [0, 129] {
        let x = terms.mk_var(format!("x{width}"), Sort::bitvec(width));
        let zero = terms.mk_bitvec(0.into(), width);
        let one = terms.mk_bitvec(1.into(), width);
        let left = add(&mut terms, x, zero, width);
        let right = add(&mut terms, x, one, width);
        let source = eq(&mut terms, left, right);
        let forged = claim(&mut terms, source, false);
        assert!(!accepted(&terms, forged));
    }
}

#[test]
fn failed_attempts_and_cancellation_pay_before_inspecting_terms() {
    let terms = TermStore::new();
    let mut charges = Vec::new();
    assert!(validate(
        &terms,
        ProofId(0),
        &[TermId(u32::MAX)],
        0,
        0,
        &mut |work, bytes| {
            charges.push((work, bytes));
            true
        }
    )
    .is_err());
    assert_eq!(charges, [(WORK, BYTES)]);
    assert!(matches!(
        validate(
            &terms,
            ProofId(0),
            &[TermId(u32::MAX)],
            0,
            0,
            &mut |_, _| false
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut terms = TermStore::new();
    let zero = terms.mk_bitvec(0.into(), 8);
    let one = terms.mk_bitvec(1.into(), 8);
    let source = eq(&mut terms, zero, one);
    let correct = claim(&mut terms, source, false);
    for (premises, arguments) in [(1, 0), (0, 1), (1, 1)] {
        assert!(validate(
            &terms,
            ProofId(0),
            &[correct],
            premises,
            arguments,
            &mut |_, _| true
        )
        .is_err());
    }
}

#[test]
fn a_deep_common_base_stays_opaque_under_the_fixed_reserve() {
    let mut terms = TermStore::new();
    let mut base = terms.mk_var("opaque", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    let one = terms.mk_bitvec(1.into(), 64);
    for _ in 0..4_096 {
        base = terms.mk_app(Symbol::named("bvxor"), [base, one], Sort::bitvec(64));
    }
    let left = add(&mut terms, base, zero, 64);
    let right = add(&mut terms, one, base, 64);
    let source = eq(&mut terms, left, right);
    let correct = claim(&mut terms, source, false);
    let mut charges = Vec::new();
    validate(&terms, ProofId(0), &[correct], 0, 0, &mut |work, bytes| {
        charges.push((work, bytes));
        true
    })
    .expect("only the authenticated common term identity is read");
    assert_eq!(charges, [(WORK, BYTES)]);
}

fn refutation(width: u32) -> (TermStore, Proof, TermId, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(width));
    let max = u128::MAX >> (128 - width);
    let a = terms.mk_bitvec(max.into(), width);
    let b = terms.mk_bitvec(0.into(), width);
    let left = add(&mut terms, x, a, width);
    let right = add(&mut terms, x, b, width);
    let source = eq(&mut terms, left, right);
    let simplified = claim(&mut terms, source, false);
    let not_simplified = terms.mk_not_raw(simplified);
    let not_source = terms.mk_not_raw(source);
    let not_false = terms.mk_not_raw(terms.false_term());
    let mut proof = Proof::new();
    let assumed = proof.add_assume(source, None);
    let simple = proof.add_rule_step(AletheRule::EqSimplify, vec![simplified], vec![], vec![]);
    let equiv = proof.add_rule_step(
        AletheRule::EquivPos2,
        vec![not_simplified, not_source, terms.false_term()],
        vec![],
        vec![],
    );
    let implication = proof.add_resolution(
        vec![not_source, terms.false_term()],
        simplified,
        simple,
        equiv,
    );
    let false_axiom = proof.add_rule_step(AletheRule::False, vec![not_false], vec![], vec![]);
    let guard = proof.add_resolution(
        vec![not_source],
        terms.false_term(),
        implication,
        false_axiom,
    );
    proof.add_resolution(vec![], source, assumed, guard);
    (terms, proof, source, left)
}

#[test]
fn strict_native_and_exact_wire_replay_artifacts_disclose_the_clean_capability() {
    for width in [1, 8, 64, 128] {
        let (terms, proof, source, left) = refutation(width);
        crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[source]))
            .expect("a complete independently checked native refutation");
        assert!(matches!(
            crate::check_proof_strict_with_context_and_progress(
                &proof,
                &terms,
                None,
                None,
                Some(&[source]),
                &mut |work, bytes| (work, bytes) != (WORK, BYTES)
            ),
            Err(ProofCheckError::ResourceLimit)
        ));
        let (text, report) = crate::capture_alethe_dialect_report(|| {
            crate::with_alethe_dialect(AletheDialect::Clean, || {
                crate::try_export_alethe_with_problem_scope_and_overrides(
                    &proof,
                    &terms,
                    &[source],
                    None,
                )
                .expect("exact Clean-dialect export")
            })
        });
        assert!(
            text.contains(":rule eq_simplify") && !text.contains(":rule hole"),
            "{text}"
        );
        assert_eq!(
            report.first_clean_only(),
            Some(CleanOnlySpelling::BvOffsetEqualitySimplify)
        );
        let surface = crate::CarcaraSurface::Supported.with_dialect_report(&report);
        assert!(matches!(
            surface,
            crate::CarcaraSurface::CleanDialect { .. }
        ));
        let (pinned, report) = crate::capture_alethe_dialect_report(|| {
            crate::with_alethe_dialect(AletheDialect::PinnedCarcara, || {
                crate::try_export_alethe_with_problem_scope_and_overrides(
                    &proof,
                    &terms,
                    &[source],
                    None,
                )
                .expect("honest diagnostic hole")
            })
        });
        assert!(pinned.contains(":rule hole") && !pinned.contains(":rule eq_simplify"));
        assert!(report.is_pinned_spelling());
        let mut overrides = ay_core::kani_compat::DetHashMap::default();
        overrides.insert(left, format!("(bvadd y (_ bv0 {width}))"));
        assert!(
            crate::with_alethe_dialect(AletheDialect::Clean, || {
                crate::try_export_alethe_with_problem_scope_and_overrides(
                    &proof,
                    &terms,
                    &[source],
                    Some(&overrides),
                )
            })
            .is_err(),
            "changed source must refuse"
        );
        if let Ok(directory) = std::env::var("AY_BV_EQ_SIMPLIFY_ARTIFACT_DIR") {
            let directory = std::path::Path::new(&directory);
            std::fs::create_dir_all(directory).expect("owned artifact directory");
            let problem = format!("(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(assert {})\n(check-sat)\n", crate::format_term_alethe(&terms, source));
            let cert = serde_json::json!({"type":"alethe_certificate", "version":"1.0", "problem":problem, "proof":text});
            std::fs::write(
                directory.join(format!("native-wire-w{width}.json")),
                serde_json::to_vec_pretty(&cert).unwrap(),
            )
            .expect("exact native-exported certificate");
        }
    }
}

#[test]
fn wire_support_preserves_premise_and_surface_boundaries() {
    let (terms, proof, _, left) = refutation(8);
    let ay_core::ProofStep::Step { clause, .. } = &proof.steps[1] else {
        panic!("simplification")
    };
    let support = |dialect, premises, arguments, overrides| {
        crate::bv_eq_simplify_step_lowering_supported(
            dialect, &terms, clause, premises, arguments, overrides,
        )
    };
    assert!(support(AletheDialect::Clean, 0, 0, None));
    assert!(!support(AletheDialect::PinnedCarcara, 0, 0, None));
    assert!(!support(AletheDialect::Clean, 1, 0, None));
    assert!(!support(AletheDialect::Clean, 0, 1, None));
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(left, "(bvadd y (_ bv0 8))".to_string());
    assert!(!support(AletheDialect::Clean, 0, 0, Some(&overrides)));
    assert_eq!(
        AletheRule::EqSimplify.wire_name(),
        ay_core::UNPROVED_STEP_RULE
    );
}
