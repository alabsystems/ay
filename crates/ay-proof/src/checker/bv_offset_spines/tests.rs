// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{AletheDialect, CleanOnlySpelling};
use ay_core::{AletheRule, Proof, ProofStep};

mod source_and_oracle;

fn eq(t: &mut TermStore, a: TermId, b: TermId) -> TermId {
    t.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}

fn frame(t: &mut TermStore, base: TermId, value: u128, width: u32, kind: u8) -> TermId {
    let c = t.mk_bitvec(value.into(), width);
    let (op, args) = match kind {
        0 => ("bvadd", [base, c]),
        1 => ("bvadd", [c, base]),
        2 => ("bvsub", [base, c]),
        _ => panic!("frame kind"),
    };
    t.mk_app(Symbol::named(op), args, Sort::bitvec(width))
}

fn claim(t: &mut TermStore, source: TermId, expected: bool) -> TermId {
    let truth = if expected {
        t.true_term()
    } else {
        t.false_term()
    };
    eq(t, source, truth)
}

fn accepted(t: &TermStore, root: TermId) -> bool {
    validate(t, ProofId(0), &[root], 0, 0, &mut |_, _| true).is_ok()
}

fn fixture(width: u32) -> (TermStore, TermId, TermId, TermId) {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(width));
    let max = u128::MAX >> (128 - width);
    let left = frame(&mut t, x, max, width, 0);
    let left = frame(&mut t, left, 1, width, 0);
    let source = eq(&mut t, left, x);
    let root = claim(&mut t, source, true);
    (t, source, root, left)
}

/// Derive the source equality's actual polarity with ordinary Boolean rules.
fn derive(t: &mut TermStore, p: &mut Proof, source: TermId, truth: bool) -> (ProofId, TermId) {
    let root = claim(t, source, truth);
    let not_root = t.mk_not_raw(root);
    let result = if truth { source } else { t.mk_not_raw(source) };
    let value = if truth { t.true_term() } else { t.false_term() };
    let complement = t.mk_not_raw(value);
    let simple = p.add_rule_step(AletheRule::BvOffsetSpinesV1, vec![root], vec![], vec![]);
    let (rule, tail) = if truth {
        (AletheRule::EquivPos1, complement)
    } else {
        (AletheRule::EquivPos2, value)
    };
    let logical = p.add_rule_step(rule, vec![not_root, result, tail], vec![], vec![]);
    let implication = p.add_resolution(vec![result, tail], root, simple, logical);
    let constant = p.add_rule_step(
        if truth {
            AletheRule::True
        } else {
            AletheRule::False
        },
        vec![if truth { value } else { complement }],
        vec![],
        vec![],
    );
    let unit = p.add_resolution(vec![result], value, implication, constant);
    (unit, root)
}

fn proof_for(t: &mut TermStore, source: TermId, truth: bool) -> (Proof, TermId, TermId) {
    let denied = if truth { t.mk_not_raw(source) } else { source };
    let mut p = Proof::new();
    let assumed = p.add_assume(denied, None);
    let (unit, root) = derive(t, &mut p, source, truth);
    p.add_resolution(vec![], source, assumed, unit);
    (p, denied, root)
}

fn export(t: &TermStore, p: &Proof, assertions: &[TermId]) -> String {
    let (text, report) = crate::capture_alethe_dialect_report(|| {
        crate::with_alethe_dialect(AletheDialect::Clean, || {
            crate::try_export_alethe_with_problem_scope_and_overrides(p, t, assertions, None)
                .expect("exact new Clean capability")
        })
    });
    assert!(!text.contains(":rule hole"));
    assert_eq!(
        report.first_clean_only(),
        Some(CleanOnlySpelling::BvOffsetSpinesV1)
    );
    text
}

fn artifacts(name: &str, problem: &str, proof: &str, wrong: Option<(&str, &str)>) {
    let Ok(directory) = std::env::var("AY_BV_OFFSET_SPINES_ARTIFACT_DIR") else {
        return;
    };
    let directory = std::path::Path::new(&directory);
    std::fs::create_dir_all(directory).unwrap();
    let write = |suffix: &str, proof: &str| {
        let certificate = serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof});
        std::fs::write(
            directory.join(format!("{name}{suffix}.json")),
            serde_json::to_vec_pretty(&certificate).unwrap(),
        )
        .unwrap();
    };
    write("", proof);
    if let Some((original, forged)) = wrong {
        assert!(proof.contains(original));
        write("-wrong-truth", &proof.replacen(original, forged, 1));
    }
}

#[test]
fn bv_offset_spines_exhaustive_small_widths_match_independent_modular_execution() {
    for width in 1..=4 {
        let modulus = 1u128 << width;
        let mut t = TermStore::new();
        let x = t.mk_var("x", Sort::bitvec(width));
        for a in 0..modulus {
            for b in 0..modulus {
                for c in 0..modulus {
                    for first in 0..3 {
                        for second in 0..3 {
                            let eval = |v, k, op| {
                                if op == 2 {
                                    (v + modulus - k) % modulus
                                } else {
                                    (v + k) % modulus
                                }
                            };
                            let expected = eval(eval(0, a, first), b, second) == c;
                            for value in 0..modulus {
                                assert_eq!(
                                    eval(eval(value, a, first), b, second) == (value + c) % modulus,
                                    expected
                                );
                            }
                            let left = frame(&mut t, x, a, width, first);
                            let left = frame(&mut t, left, b, width, second);
                            let right = frame(&mut t, x, c, width, 0);
                            let source = eq(&mut t, left, right);
                            for truth in [false, true] {
                                let root = claim(&mut t, source, truth);
                                assert_eq!(accepted(&t, root), truth == expected);
                                let value = if truth { t.true_term() } else { t.false_term() };
                                let reversed = eq(&mut t, value, source);
                                assert_eq!(accepted(&t, reversed), truth == expected);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn bv_offset_spines_wrap_zero_and_boundaries_have_strict_wire_proofs() {
    for width in [1, 8, 64, 128] {
        let (mut t, source, root, left) = fixture(width);
        assert!(accepted(&t, root));
        let (p, denied, root) = proof_for(&mut t, source, true);
        crate::check_proof_strict_with_context(&p, &t, None, None, Some(&[denied])).unwrap();
        let text = export(&t, &p, &[denied]);
        let wrong = claim(&mut t, source, false);
        let problem = format!(
            "(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(assert {})\n(check-sat)\n",
            crate::format_term_alethe(&t, denied)
        );
        artifacts(
            &format!("wrap-w{width}"),
            &problem,
            &text,
            Some((
                &crate::format_term_alethe(&t, root),
                &crate::format_term_alethe(&t, wrong),
            )),
        );
        let pinned = crate::with_alethe_dialect(AletheDialect::PinnedCarcara, || {
            crate::try_export_alethe_with_problem_scope_and_overrides(&p, &t, &[denied], None)
                .unwrap()
        });
        assert!(
            pinned.contains(":rule hole") && !pinned.contains(":rule eq_simplify_bv_offset_spines")
        );
        let mut changed = ay_core::kani_compat::DetHashMap::default();
        changed.insert(left, format!("(bvadd y (_ bv1 {width}))"));
        assert!(!crate::bv_offset_spines_step_lowering_supported(
            AletheDialect::Clean,
            &t,
            &[root],
            0,
            0,
            Some(&changed)
        ));
        assert!(crate::with_alethe_dialect(AletheDialect::Clean, || {
            crate::try_export_alethe_with_problem_scope_and_overrides(
                &p,
                &t,
                &[denied],
                Some(&changed),
            )
        })
        .is_err());
        // Independent arbitrary-precision arithmetic, including the 128-bit modulus.
        let modulus = num_bigint::BigInt::from(1u8) << width;
        let max = &modulus - 1u8;
        assert_eq!((&max + 1u8) % &modulus, num_bigint::BigInt::from(0u8));
        let x = t.mk_var("x", Sort::bitvec(width));
        let minus = frame(&mut t, x, 1, width, 2);
        let minus = frame(&mut t, minus, 1, width, 1);
        let source = eq(&mut t, minus, x);
        let subtraction_claim = claim(&mut t, source, true);
        assert!(accepted(&t, subtraction_claim));
    }
}

#[test]
fn bv_offset_spines_frame_work_stop_and_aggregate_attempts_fail_closed() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(128));
    let mut left = x;
    let mut right = x;
    for _ in 0..16 {
        left = frame(&mut t, left, 0, 128, 0);
        right = frame(&mut t, right, 0, 128, 2);
    }
    let source = eq(&mut t, left, right);
    let root = claim(&mut t, source, true);
    let mut inspector = Inspector {
        terms: &t,
        remaining: WORK,
        exhausted: false,
        stopped: false,
        poll: &mut || true,
    };
    assert_eq!(inspector.holds(&[root]), Some(true));
    let maximum_valid_work = WORK - inspector.remaining;
    assert!(maximum_valid_work < 2_048);
    assert!(matches!(
        inspect(&t, &[root], 1, &mut || true),
        Err(ProofCheckError::ResourceLimit)
    ));
    let seventeen = frame(&mut t, left, 0, 128, 0);
    let too_long_source = eq(&mut t, seventeen, right);
    let too_long = claim(&mut t, too_long_source, true);
    assert!(!accepted(&t, too_long));
    let (proof, denied, root) = proof_for(&mut t, source, true);
    crate::check_proof_strict_with_context(&proof, &t, None, None, Some(&[denied])).unwrap();
    let printed = export(&t, &proof, &[denied]);
    let source_text = crate::format_term_alethe(&t, source);
    let over_limit_text = crate::format_term_alethe(&t, too_long_source);
    let problem = format!(
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 128))\n(assert {})\n(check-sat)\n",
        crate::format_term_alethe(&t, denied)
    );
    let wrong_truth = claim(&mut t, source, false);
    artifacts(
        "frames-16",
        &problem,
        &printed,
        Some((
            &crate::format_term_alethe(&t, root),
            &crate::format_term_alethe(&t, wrong_truth),
        )),
    );
    let (invalid, denied17, _) = proof_for(&mut t, too_long_source, true);
    assert!(
        crate::check_proof_strict_with_context(&invalid, &t, None, None, Some(&[denied17]))
            .is_err()
    );
    assert!(crate::with_alethe_dialect(AletheDialect::Clean, || {
        crate::try_export_alethe_with_problem_scope_and_overrides(&invalid, &t, &[denied17], None)
    })
    .is_err());
    // This intentionally invalid wire control is never an accepted export:
    // replace the exact 16-frame term everywhere by its actual 17-frame term.
    artifacts(
        "frames-17",
        &problem.replace(&source_text, &over_limit_text),
        &printed.replace(&source_text, &over_limit_text),
        None,
    );
    if let Ok(directory) = std::env::var("AY_BV_OFFSET_SPINES_ARTIFACT_DIR") {
        std::fs::write(std::path::Path::new(&directory).join("bounded-inspection.json"),
            serde_json::to_vec_pretty(&serde_json::json!({"two_16_frame_spines_metered_units":maximum_valid_work,"prepaid_work":WORK,"prepaid_admission_bytes":BYTES,"private_heap_bytes":0,"frame_17_native_and_export_refused":true})).unwrap()).unwrap();
    }
    for clause in [vec![], vec![TermId(u32::MAX)], vec![root, root]] {
        let mut calls = Vec::new();
        assert!(validate(&t, ProofId(0), &clause, 0, 0, &mut |w, b| {
            calls.push((w, b));
            true
        })
        .is_err());
        assert_eq!(calls.first(), Some(&(WORK, BYTES)));
    }
    assert!(matches!(
        validate(&t, ProofId(0), &[TermId(u32::MAX)], 0, 0, &mut |_, _| false),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut polls = 0;
    assert!(matches!(
        validate(&t, ProofId(0), &[root], 0, 0, &mut |w, b| {
            if (w, b) == (WORK, BYTES) {
                true
            } else {
                polls += 1;
                polls < 3
            }
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    for (premises, args) in [(1, 0), (0, 1), (1, 1)] {
        let mut charges = Vec::new();
        assert!(
            validate(&t, ProofId(0), &[root], premises, args, &mut |w, b| {
                charges.push((w, b));
                true
            })
            .is_err()
        );
        assert_eq!(charges, [(WORK, BYTES)]);
    }
    let mut work = 0;
    let mut bytes = 0;
    for attempt in 0..3 {
        let result = validate(&t, ProofId(0), &[TermId(u32::MAX)], 0, 0, &mut |w, b| {
            work += w;
            bytes += b;
            work <= 2 * WORK && bytes <= 2 * BYTES
        });
        assert!(result.is_err());
        assert_eq!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            attempt == 2
        );
    }
}

#[test]
fn bv_offset_spines_malformed_entries_heads_literals_widths_and_wrong_results_refuse() {
    let (mut t, source, root, _) = fixture(8);
    let x = t.mk_var("x", Sort::bitvec(8));
    let y = t.mk_var("y", Sort::bitvec(8));
    let zero = t.mk_bitvec(0.into(), 8);
    let one = t.mk_bitvec(1.into(), 8);
    let two = t.mk_bitvec(2.into(), 8);
    let bad = [
        frame(&mut t, y, 0, 8, 0),
        frame(&mut t, x, 1, 8, 0),
        t.mk_app(Symbol::named("bvmul"), [x, one], Sort::bitvec(8)),
        t.mk_app(Symbol::named("bvneg"), [x], Sort::bitvec(8)),
        t.mk_app(Symbol::named("bvsub"), [one, x], Sort::bitvec(8)),
        t.mk_app(
            Symbol::named("__ay_private_bvadd"),
            [x, zero],
            Sort::bitvec(8),
        ),
        t.mk_app(Symbol::named("|bvadd|"), [x, zero], Sort::bitvec(8)),
        t.mk_app(Symbol::indexed("bvadd", vec![]), [x, zero], Sort::bitvec(8)),
        t.mk_app(Symbol::named("bvadd"), [], Sort::bitvec(8)),
        t.mk_app(Symbol::named("bvadd"), [x], Sort::bitvec(8)),
        t.mk_app(Symbol::named("bvadd"), [x, zero, one], Sort::bitvec(8)),
        t.mk_app(
            Symbol::named("bvadd"),
            [x, TermId(u32::MAX)],
            Sort::bitvec(8),
        ),
        t.mk_app(Symbol::named("bvadd"), [zero, one], Sort::bitvec(8)),
        t.mk_app(Symbol::named("bvadd"), [x, zero], Sort::Bool),
    ];
    for left in bad {
        let s = eq(&mut t, left, x);
        let q = claim(&mut t, s, true);
        assert!(!accepted(&t, q));
    }
    let wrong_claim = claim(&mut t, source, false);
    assert!(!accepted(&t, wrong_claim));
    let snapshots = [
        (
            one,
            TermData::Const(Constant::BitVec {
                value: (-1).into(),
                width: 8,
            }),
            Sort::bitvec(8),
        ),
        (
            one,
            TermData::Const(Constant::BitVec {
                value: num_bigint::BigInt::from(1u8) << 4096u32,
                width: 8,
            }),
            Sort::bitvec(8),
        ),
        (
            one,
            TermData::Const(Constant::BitVec {
                value: 1.into(),
                width: 64,
            }),
            Sort::bitvec(8),
        ),
        (
            one,
            TermData::Const(Constant::BitVec {
                value: 1.into(),
                width: 8,
            }),
            Sort::bitvec(64),
        ),
        (one, TermData::Const(Constant::Bool(true)), Sort::bitvec(8)),
        (
            root,
            TermData::App(Symbol::named("="), vec![source, t.true_term()]),
            Sort::Int,
        ),
    ];
    for (id, data, sort) in snapshots {
        let mut entries = t.entries_snapshot();
        entries[id.index()] = (data, sort);
        let forged = TermStore::from_entries(
            entries,
            Some(t.true_term()),
            Some(t.false_term()),
            t.var_counter(),
        );
        assert!(!accepted(&forged, root));
    }
    let symbolic = t.mk_app(Symbol::named("bvadd"), [x, y], Sort::bitvec(8));
    let other = frame(&mut t, x, 2, 8, 0);
    let s = eq(&mut t, symbolic, other);
    let q = claim(&mut t, s, true);
    assert!(!accepted(&t, q));
    for width in [0, 129] {
        let base = t.mk_var(format!("w{width}"), Sort::bitvec(width));
        let s = eq(&mut t, base, base);
        let q = claim(&mut t, s, true);
        assert!(!accepted(&t, q));
    }
    // The old immediate rule keeps its grammar and fees.
    assert!(
        super::super::bv_eq_simplify::validate(&t, ProofId(0), &[root], 0, 0, &mut |_, _| true)
            .is_err()
    );
    assert_eq!(super::super::bv_eq_simplify::WORK, 512);
    assert_eq!(super::super::bv_eq_simplify::BYTES, 2048);
    let _ = two;
}

#[test]
fn bv_offset_spines_deep_identical_base_is_borrowed_and_opaque() {
    let mut t = TermStore::new();
    let mut base = t.mk_var("opaque", Sort::bitvec(64));
    let one = t.mk_bitvec(1.into(), 64);
    for _ in 0..4096 {
        base = t.mk_app(Symbol::named("bvxor"), [base, one], Sort::bitvec(64));
    }
    let left = frame(&mut t, base, 1, 64, 2);
    let left = frame(&mut t, left, 1, 64, 1);
    let s = eq(&mut t, left, base);
    let root = claim(&mut t, s, true);
    let before = t.len();
    let mut charges = Vec::new();
    validate(&t, ProofId(0), &[root], 0, 0, &mut |w, b| {
        charges.push((w, b));
        true
    })
    .unwrap();
    assert_eq!(before, t.len());
    assert_eq!(charges[0], (WORK, BYTES));
    assert!(charges[1..].iter().all(|x| *x == (0, 0)));
    assert!(std::mem::size_of::<Inspector<'_, '_>>() <= 128);
}

fn from_plan(t: &mut TermStore, ast: &serde_json::Value) -> TermId {
    if let Some(name) = ast.as_str() {
        return t.mk_var(name, Sort::bitvec(64));
    }
    let a = ast.as_array().expect("retained syntax array");
    if a[0] == "_" {
        let value = a[1]
            .as_str()
            .unwrap()
            .strip_prefix("bv")
            .unwrap()
            .parse::<num_bigint::BigInt>()
            .unwrap();
        let width = a[2].as_str().unwrap().parse().unwrap();
        return t.mk_bitvec(value, width);
    }
    assert_eq!(a.len(), 3);
    assert!(a[0] == "bvadd" || a[0] == "bvsub");
    let left = from_plan(t, &a[1]);
    let right = from_plan(t, &a[2]);
    t.mk_app(
        Symbol::named(a[0].as_str().unwrap()),
        [left, right],
        Sort::bitvec(64),
    )
}

#[test]
fn bv_offset_spines_all_293_retained_identities_have_native_and_exact_wire_proofs() {
    let plan: serde_json::Value =
        serde_json::from_str(include_str!("tests/canonical-plan-obligations.json")).unwrap();
    let rows = plan["normalizations"].as_array().unwrap();
    assert_eq!(rows.len(), 293);
    let mut t = TermStore::new();
    let mut sources = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        let left = from_plan(&mut t, &row["left"]);
        let right = from_plan(&mut t, &row["right"]);
        let source = eq(&mut t, left, right);
        sources.push(source);
        let (p, denied, root) = proof_for(&mut t, source, true);
        crate::check_proof_strict_with_context(&p, &t, None, None, Some(&[denied])).unwrap();
        let text = export(&t, &p, &[denied]);
        let wrong = claim(&mut t, source, false);
        let mut invalid = p.clone();
        let ProofStep::Step { clause, .. } = &mut invalid.steps[1] else {
            panic!("new semantic step")
        };
        *clause = vec![wrong];
        assert!(
            crate::check_proof_strict_with_context(&invalid, &t, None, None, Some(&[denied]))
                .is_err()
        );
        let problem=format!("(set-logic QF_BV)\n(declare-const frame_entry_sp (_ BitVec 64))\n(declare-const frame_exit_0_resume_sp (_ BitVec 64))\n(assert {})\n(check-sat)\n",crate::format_term_alethe(&t,denied));
        artifacts(
            &format!("plan-{index:03}"),
            &problem,
            &text,
            Some((
                &crate::format_term_alethe(&t, root),
                &crate::format_term_alethe(&t, wrong),
            )),
        );
    }
    // One full proof replays every new rule under ONE unchanged aggregate
    // allowance. No standalone-printer or proof partition resets a cap.
    let first = sources[0];
    let last = *sources.last().unwrap();
    // Both source variables belong to this ONE authored assertion. Declaring
    // an unused symbol in text cannot grant an undeclarable proof symbol.
    let conjunction = t.mk_app(Symbol::named("and"), [first, last], Sort::Bool);
    let denied = t.mk_not_raw(conjunction);
    let mut p = Proof::new();
    let assumed = p.add_assume(denied, None);
    let mut units = Vec::new();
    for source in sources {
        units.push(derive(&mut t, &mut p, source, true).0);
    }
    let not_first = t.mk_not_raw(first);
    let not_last = t.mk_not_raw(last);
    let introduction = p.add_rule_step(
        AletheRule::AndNeg,
        vec![conjunction, not_first, not_last],
        vec![],
        vec![],
    );
    let introduction = p.add_resolution(vec![conjunction, not_last], first, units[0], introduction);
    let conjunction_unit = p.add_resolution(
        vec![conjunction],
        last,
        introduction,
        *units.last().unwrap(),
    );
    p.add_resolution(vec![], conjunction, assumed, conjunction_unit);
    let (mut work, mut bytes, mut attempts) = (0usize, 0usize, 0usize);
    crate::check_proof_strict_with_context_and_progress(
        &p,
        &t,
        None,
        None,
        Some(&[denied]),
        &mut |w, b| {
            work = work.checked_add(w).unwrap();
            bytes = bytes.checked_add(b).unwrap();
            if (w, b) == (WORK, BYTES) {
                attempts += 1;
            }
            work <= 350_000_000 && bytes <= 1_342_177_280
        },
    )
    .unwrap();
    assert_eq!(attempts, 293);
    let text = export(&t, &p, &[denied]);
    assert_eq!(
        text.matches(":rule eq_simplify_bv_offset_spines").count(),
        293
    );
    let problem=format!("(set-logic QF_BV)\n(declare-const frame_entry_sp (_ BitVec 64))\n(declare-const frame_exit_0_resume_sp (_ BitVec 64))\n(assert {})\n(check-sat)\n",crate::format_term_alethe(&t,denied));
    artifacts("all-293", &problem, &text, None);
    if let Ok(directory) = std::env::var("AY_BV_OFFSET_SPINES_ARTIFACT_DIR") {
        std::fs::write(std::path::Path::new(&directory).join("aggregate-native.json"),serde_json::to_vec_pretty(&serde_json::json!({"new_rule_attempts":attempts,"proof_steps":p.steps.len(),"observed_native_progress_work":work,"observed_native_progress_bytes":bytes,"strict_native":true,"no_whole_E1_claim":true})).unwrap()).unwrap();
    }
}
