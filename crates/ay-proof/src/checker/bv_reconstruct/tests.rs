// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{AletheDialect, CleanOnlySpelling};
use ay_core::{AletheRule, Proof, ProofStep};

mod source_and_oracle;

fn eq(t: &mut TermStore, a: TermId, b: TermId) -> TermId {
    t.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}
fn app(t: &mut TermStore, name: &str, a: TermId, b: TermId, width: u32) -> TermId {
    t.mk_app(Symbol::named(name), [a, b], Sort::bitvec(width))
}
fn indexed(t: &mut TermStore, name: &str, indices: Vec<u32>, child: TermId, width: u32) -> TermId {
    t.mk_app(Symbol::indexed(name, indices), [child], Sort::bitvec(width))
}
fn piece(t: &mut TermStore, word: TermId, width: u32, low: u32, span: u32) -> TermId {
    let extracted = indexed(t, "extract", vec![low + span - 1, low], word, span);
    let extended = indexed(t, "zero_extend", vec![width - span], extracted, width);
    if low == 0 {
        extended
    } else {
        let amount = t.mk_bitvec(low.into(), width);
        app(t, "bvshl", extended, amount, width)
    }
}
fn packed(
    t: &mut TermStore,
    word: TermId,
    width: u32,
    ranges: &[(u32, u32)],
    reverse: bool,
) -> TermId {
    let mut pieces: Vec<_> = ranges
        .iter()
        .map(|&(low, span)| piece(t, word, width, low, span))
        .collect();
    if reverse {
        pieces.reverse();
    }
    let mut result = pieces[0];
    for p in pieces.into_iter().skip(1) {
        result = app(t, "bvor", result, p, width);
    }
    result
}
fn accepts(t: &TermStore, source: TermId) -> bool {
    validate(t, ProofId(0), &[source], 0, 0, &mut |_, _| true).is_ok()
}
fn proof_for(t: &mut TermStore, source: TermId) -> (Proof, TermId) {
    let denied = t.mk_not_raw(source);
    let mut p = Proof::new();
    let assumed = p.add_assume(denied, None);
    let unit = p.add_rule_step(AletheRule::BvReconstructV1, vec![source], vec![], vec![]);
    p.add_resolution(vec![], source, assumed, unit);
    (p, denied)
}
fn export(t: &TermStore, p: &Proof, assertions: &[TermId]) -> String {
    let (text, report) = crate::capture_alethe_dialect_report(|| {
        crate::with_alethe_dialect(AletheDialect::Clean, || {
            crate::try_export_alethe_with_problem_scope_and_overrides(p, t, assertions, None)
                .unwrap()
        })
    });
    assert!(!text.contains(":rule hole"));
    assert_eq!(
        report.first_clean_only(),
        Some(CleanOnlySpelling::BvReconstructV1)
    );
    text
}
fn artifact(name: &str, problem: &str, proof: &str) {
    if let Ok(dir) = std::env::var("AY_BV_RECONSTRUCT_ARTIFACT_DIR") {
        let dir = std::path::Path::new(&dir);
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(
            dir.join(format!("{name}.json")),
            serde_json::to_vec_pretty(&serde_json::json!({
            "type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof}))
            .unwrap(),
        )
        .unwrap();
    }
}
fn problem(t: &TermStore, denied: TermId, width: u32) -> String {
    format!("(set-logic QF_BV)\n(declare-const x (_ BitVec {width}))\n(declare-const y (_ BitVec {width}))\n(assert {})\n(check-sat)\n",crate::format_term_alethe(t,denied))
}
fn check_and_export(t: &mut TermStore, source: TermId, width: u32, name: &str) {
    let (p, denied) = proof_for(t, source);
    crate::check_proof_strict_with_context(&p, t, None, None, Some(&[denied])).unwrap();
    let text = export(t, &p, &[denied]);
    artifact(name, &problem(t, denied, width), &text);
    // Same source assertion, one changed semantic step; native rejects there.
    let false_term = t.false_term();
    let wrong = eq(t, source, false_term);
    let mut forged = p.clone();
    let ProofStep::Step { clause, .. } = &mut forged.steps[1] else {
        panic!("semantic step")
    };
    *clause = vec![wrong];
    assert!(
        crate::check_proof_strict_with_context(&forged, t, None, None, Some(&[denied])).is_err()
    );
    let original = format!("(cl {})", crate::format_term_alethe(t, source));
    let replacement = format!("(cl {})", crate::format_term_alethe(t, wrong));
    assert!(text.contains(&original));
    artifact(
        &format!("{name}-wrong-truth"),
        &problem(t, denied, width),
        &text.replacen(&original, &replacement, 1),
    );
}

fn causal_refusal(t: &mut TermStore, wrong: TermId, name: &str) {
    assert!(!accepts(t, wrong));
    let x = t.mk_var("x", Sort::bitvec(8));
    let full = piece(t, x, 8, 0, 8);
    let good = eq(t, full, x);
    let (p, denied) = proof_for(t, good);
    crate::check_proof_strict_with_context(&p, t, None, None, Some(&[denied])).unwrap();
    let text = export(t, &p, &[denied]);
    let mut forged = p.clone();
    let ProofStep::Step { clause, .. } = &mut forged.steps[1] else {
        panic!("semantic step")
    };
    *clause = vec![wrong];
    assert!(matches!(
        crate::check_proof_strict_with_context(&forged, t, None, None, Some(&[denied])),
        Err(ProofCheckError::InvalidBvReconstruct { .. })
    ));
    let mut payload = p.clone();
    let ProofStep::Step { premises, .. } = &mut payload.steps[1] else {
        panic!("step")
    };
    premises.push(ProofId(u32::MAX));
    assert!(matches!(
        crate::check_proof_strict_with_context(&payload, t, None, None, Some(&[denied])),
        Err(ProofCheckError::InvalidBvReconstruct { .. })
    ));
    let original = format!("(cl {})", crate::format_term_alethe(t, good));
    let replacement = format!("(cl {})", crate::format_term_alethe(t, wrong));
    artifact(
        name,
        &problem(t, denied, 8),
        &text.replacen(&original, &replacement, 1),
    );
}

#[test]
fn bv_reconstruct_causal_wire_defects_refuse_at_the_new_rule() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(8));
    let y = t.mk_var("y", Sort::bitvec(8));
    let good = packed(&mut t, x, 8, &[(0, 4), (4, 4)], false);
    for (name, ranges) in [
        ("gap", vec![(0, 4)]),
        ("overlap", vec![(0, 4), (0, 4)]),
        ("boundary-gap", vec![(0, 3), (4, 4)]),
    ] {
        let pack = packed(&mut t, x, 8, &ranges, false);
        let wrong = eq(&mut t, pack, x);
        causal_refusal(&mut t, wrong, &format!("causal-{name}"));
    }
    let wrong = eq(&mut t, good, y);
    causal_refusal(&mut t, wrong, "causal-wrong-source");
    let wrong = eq(&mut t, x, good);
    causal_refusal(&mut t, wrong, "causal-reverse-orientation");
    let bad = app(&mut t, "bvand", x, x, 8);
    let wrong = eq(&mut t, bad, x);
    causal_refusal(&mut t, wrong, "causal-wrong-head");
    let low = piece(&mut t, x, 8, 0, 4);
    let amount = t.mk_bitvec(4.into(), 8);
    let wrong_high = app(&mut t, "bvshl", low, amount, 8);
    let bad = app(&mut t, "bvor", low, wrong_high, 8);
    let wrong = eq(&mut t, bad, x);
    causal_refusal(&mut t, wrong, "causal-wrong-shift-source-alignment");
    let amount = t.mk_bitvec(8.into(), 8);
    let bad = app(&mut t, "bvshl", x, amount, 8);
    let wrong = eq(&mut t, bad, x);
    causal_refusal(&mut t, wrong, "causal-shift-width");
    let full = piece(&mut t, x, 8, 0, 8);
    let one = t.mk_bitvec(1.into(), 8);
    let bad = app(&mut t, "bvor", full, one, 8);
    let wrong = eq(&mut t, bad, x);
    causal_refusal(&mut t, wrong, "causal-nonzero-fill");
    let unary = t.mk_app(Symbol::named("bvor"), [full], Sort::bitvec(8));
    let wrong = eq(&mut t, unary, x);
    causal_refusal(&mut t, wrong, "causal-unary-or");
    let mut depth = x;
    for _ in 0..257 {
        depth = indexed(&mut t, "zero_extend", vec![0], depth, 8);
    }
    let wrong = eq(&mut t, depth, x);
    causal_refusal(&mut t, wrong, "native-only-depth-257-zero-extend-0");
    let zero = t.mk_bitvec(0.into(), 8);
    let mut leaves = vec![zero; 1024];
    leaves[0] = x;
    while leaves.len() > 1 {
        leaves = leaves
            .chunks(2)
            .map(|p| app(&mut t, "bvor", p[0], p[1], 8))
            .collect();
    }
    let n2048 = indexed(&mut t, "zero_extend", vec![0], leaves[0], 8);
    let n2049 = indexed(&mut t, "zero_extend", vec![0], n2048, 8);
    let wrong = eq(&mut t, n2049, x);
    causal_refusal(&mut t, wrong, "native-only-nodes-2049-zero-extend-0");
}

#[test]
fn bv_reconstruct_boundaries_exact_surface_and_pinned_refusal() {
    for width in [1, 8, 64, 128] {
        let mut t = TermStore::new();
        let word = t.mk_var("x", Sort::bitvec(width));
        let ranges: Vec<_> = (0..width).map(|low| (low, 1)).collect();
        let pack = packed(&mut t, word, width, &ranges, true);
        let source = eq(&mut t, pack, word);
        check_and_export(&mut t, source, width, &format!("width-{width}"));
        let (p, denied) = proof_for(&mut t, source);
        let pinned = crate::with_alethe_dialect(AletheDialect::PinnedCarcara, || {
            crate::export_alethe(&p, &t)
        });
        assert!(pinned.contains(":rule hole") && !pinned.contains(":rule bv_reconstruct_v1"));
        assert_eq!(
            AletheRule::BvReconstructV1.wire_name(),
            ay_core::UNPROVED_STEP_RULE
        );
        assert!(!crate::bv_reconstruct_step_lowering_supported(
            AletheDialect::PinnedCarcara,
            &t,
            &[source],
            0,
            0,
            None
        ));
        let mut overrides = ay_core::kani_compat::DetHashMap::default();
        overrides.insert(word, "y".into());
        assert!(!crate::bv_reconstruct_step_lowering_supported(
            AletheDialect::Clean,
            &t,
            &[source],
            0,
            0,
            Some(&overrides)
        ));
        assert!(!crate::bv_reconstruct_step_lowering_supported(
            AletheDialect::Clean,
            &t,
            &[source],
            1,
            0,
            None
        ));
        assert!(!crate::bv_reconstruct_step_lowering_supported(
            AletheDialect::Clean,
            &t,
            &[source],
            0,
            1,
            None
        ));
        let _ = denied;
        let full = piece(&mut t, word, width, 0, width);
        let source = eq(&mut t, full, word);
        check_and_export(&mut t, source, width, &format!("whole-extract-{width}"));
        let source = eq(&mut t, word, word);
        assert!(accepts(&t, source));
        check_and_export(&mut t, source, width, &format!("bare-word-{width}"));
    }
}

#[test]
fn bv_reconstruct_node_depth_precharge_stop_and_one_aggregate_bound() {
    assert!(
        std::mem::size_of::<Visit>() * (MAX_DEPTH as usize + 1) + std::mem::size_of::<Inspector>()
            < BYTES
    );
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(8));
    let mut deep = x;
    for _ in 0..256 {
        deep = indexed(&mut t, "zero_extend", vec![0], deep, 8);
    }
    let source = eq(&mut t, deep, x);
    assert!(accepts(&t, source));
    check_and_export(&mut t, source, 8, "depth-256");
    deep = indexed(&mut t, "zero_extend", vec![0], deep, 8);
    let too_deep = eq(&mut t, deep, x);
    assert!(!accepts(&t, too_deep));
    let zero = t.mk_bitvec(0.into(), 8);
    let mut leaves = vec![zero; 1024];
    leaves[0] = x;
    while leaves.len() > 1 {
        leaves = leaves
            .chunks(2)
            .map(|p| app(&mut t, "bvor", p[0], p[1], 8))
            .collect();
    }
    let n2047 = leaves[0];
    let n2048 = indexed(&mut t, "zero_extend", vec![0], n2047, 8);
    let source = eq(&mut t, n2048, x);
    assert!(accepts(&t, source));
    check_and_export(&mut t, source, 8, "nodes-2048");
    let n2049 = indexed(&mut t, "zero_extend", vec![0], n2048, 8);
    let bad = eq(&mut t, n2049, x);
    assert!(!accepts(&t, bad));
    let mut calls = Vec::new();
    assert!(matches!(
        validate(&t, ProofId(0), &[TermId(u32::MAX)], 0, 0, &mut |w, b| {
            calls.push((w, b));
            false
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, [(WORK, BYTES)]);
    assert!(matches!(
        inspect(&t, &[source], 4095, &mut || true),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(matches!(
        validate(&t, ProofId(0), &[source], 0, 0, &mut |w, b| w != 0
            || b != 0),
        Err(ProofCheckError::ResourceLimit)
    ));
    for (premises, args) in [(1, 0), (0, 1)] {
        let mut paid = Vec::new();
        assert!(
            validate(&t, ProofId(0), &[source], premises, args, &mut |w, b| {
                paid.push((w, b));
                true
            })
            .is_err()
        );
        assert_eq!(paid, [(WORK, BYTES)]);
    }
    let mut work = 0;
    let mut bytes = 0;
    let mut accepted = 0;
    for _ in 0..1000 {
        let result = validate(&t, ProofId(0), &[source], 0, 0, &mut |w, b| {
            work += w;
            bytes += b;
            work <= 350_000_000 && bytes <= 1_342_177_280
        });
        if result.is_err() {
            break;
        }
        accepted += 1;
    }
    assert_eq!(accepted, 350_000_000 / WORK);
    assert!(work > 350_000_000);
    assert!(bytes < 1_342_177_280);
}

#[test]
fn bv_reconstruct_wire_visible_node_and_depth_limits_survive_consumer_parsing() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(8));
    let zero = t.mk_bitvec(0.into(), 8);
    let mut deep = x;
    for _ in 0..256 {
        deep = app(&mut t, "bvor", zero, deep, 8);
    }
    let source = eq(&mut t, deep, x);
    assert!(accepts(&t, source));
    check_and_export(&mut t, source, 8, "wire-depth-256");
    let deep = app(&mut t, "bvor", zero, deep, 8);
    let wrong = eq(&mut t, deep, x);
    causal_refusal(&mut t, wrong, "causal-wire-depth-257");
    for (ranges, zeros, expected, name) in [
        (vec![(0, 2), (2, 2), (4, 4)], 1018, true, "wire-nodes-2048"),
        (
            vec![(0, 2), (2, 2), (4, 2), (6, 2)],
            1016,
            false,
            "causal-wire-nodes-2049",
        ),
    ] {
        let pack = packed(&mut t, x, 8, &ranges, false);
        let mut leaves = vec![zero; zeros + 1];
        leaves[0] = pack;
        while leaves.len() > 1 {
            let mut next = Vec::new();
            for p in leaves.chunks(2) {
                next.push(if p.len() == 1 {
                    p[0]
                } else {
                    app(&mut t, "bvor", p[0], p[1], 8)
                });
            }
            leaves = next;
        }
        let source = eq(&mut t, leaves[0], x);
        let mut meter = Inspector {
            terms: &t,
            remaining: WORK,
            exhausted: false,
            stopped: false,
            poll: &mut || true,
            nodes: 0,
        };
        assert_eq!(meter.holds(&[source]).unwrap_or(false), expected);
        assert_eq!(meter.nodes, if expected { 2048 } else { 2049 });
        if let Ok(dir) = std::env::var("AY_BV_RECONSTRUCT_ARTIFACT_DIR") {
            std::fs::write(std::path::Path::new(&dir).join(format!("{name}-inspection.json")),serde_json::to_vec_pretty(&serde_json::json!({"actual_visits":meter.nodes,"metered_units":WORK-meter.remaining,"prepaid_work":WORK,"prepaid_bytes":BYTES,"fixed_stack_slots":MAX_DEPTH as usize+1,"fixed_stack_bytes":std::mem::size_of::<Visit>()*(MAX_DEPTH as usize+1),"max_depth":MAX_DEPTH,"no_private_heap_by_construction":true,"accepted":expected})).unwrap()).unwrap();
        }
        if expected {
            check_and_export(&mut t, source, 8, name);
        } else {
            causal_refusal(&mut t, source, name);
        }
    }
}

#[test]
fn bv_reconstruct_nested_groups_zero_leaves_and_shift_extension_limits() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(8));
    let lo = piece(&mut t, x, 4, 0, 4);
    let a = indexed(&mut t, "extract", vec![5, 4], x, 2);
    let a = indexed(&mut t, "zero_extend", vec![2], a, 4);
    let b = indexed(&mut t, "extract", vec![7, 6], x, 2);
    let b = indexed(&mut t, "zero_extend", vec![2], b, 4);
    let two = t.mk_bitvec(2.into(), 4);
    let b = app(&mut t, "bvshl", b, two, 4);
    let upper = app(&mut t, "bvor", a, b, 4);
    let upper = indexed(&mut t, "zero_extend", vec![4], upper, 8);
    let four = t.mk_bitvec(4.into(), 8);
    let upper = app(&mut t, "bvshl", upper, four, 8);
    let lo = indexed(&mut t, "zero_extend", vec![4], lo, 8);
    let joined = app(&mut t, "bvor", upper, lo, 8);
    let zero = t.mk_bitvec(0.into(), 8);
    let joined = app(&mut t, "bvor", zero, joined, 8);
    let zero = t.mk_bitvec(0.into(), 8);
    let joined = app(&mut t, "bvshl", joined, zero, 8);
    let source = eq(&mut t, joined, x);
    check_and_export(&mut t, source, 8, "nested-groups-zero-shift-fill");
    let mut polls = 0;
    assert!(matches!(
        validate(&t, ProofId(0), &[source], 0, 0, &mut |w, b| {
            if (w, b) == (0, 0) {
                polls += 1;
            }
            polls < 5
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(polls, 5);
}

#[test]
fn bv_reconstruct_malformed_heads_indices_ids_sorts_literals_and_coverage_refuse() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::bitvec(8));
    let y = t.mk_var("y", Sort::bitvec(8));
    let good = packed(&mut t, x, 8, &[(0, 4), (4, 4)], false);
    let source = eq(&mut t, good, x);
    assert!(accepts(&t, source));
    for ranges in [
        vec![(0, 4)],
        vec![(0, 4), (0, 4)],
        vec![(0, 3), (4, 4)],
        vec![(0, 5), (4, 4)],
    ] {
        let pack = packed(&mut t, x, 8, &ranges, false);
        let bad = eq(&mut t, pack, x);
        assert!(!accepts(&t, bad));
    }
    let wrong_base = eq(&mut t, good, y);
    assert!(!accepts(&t, wrong_base));
    let reversed = eq(&mut t, x, good);
    assert!(!accepts(&t, reversed));
    for head in ["bvand", "bvxor", "@bv_reconstruct", "__ay_internal$bvor"] {
        let bad = app(&mut t, head, x, x, 8);
        let bad = eq(&mut t, bad, x);
        assert!(!accepts(&t, bad));
    }
    for indices in [
        vec![],
        vec![7],
        vec![7, 0, 0],
        vec![0, 7],
        vec![8, 0],
        vec![u32::MAX, 0],
    ] {
        let bad = indexed(&mut t, "extract", indices, x, 8);
        let bad = eq(&mut t, bad, x);
        assert!(!accepts(&t, bad));
    }
    for (indices, width) in [
        (vec![], 8),
        (vec![0, 0], 8),
        (vec![1], 8),
        (vec![u32::MAX], 8),
    ] {
        let bad = indexed(&mut t, "zero_extend", indices, x, width);
        let bad = eq(&mut t, bad, x);
        assert!(!accepts(&t, bad));
    }
    for amount in [8u128, 9, 255] {
        let amount = t.mk_bitvec(amount.into(), 8);
        let bad = app(&mut t, "bvshl", x, amount, 8);
        let bad = eq(&mut t, bad, x);
        assert!(!accepts(&t, bad));
    }
    let one = t.mk_bitvec(1.into(), 8);
    let bad = app(&mut t, "bvor", good, one, 8);
    let bad = eq(&mut t, bad, x);
    assert!(!accepts(&t, bad));
    let one = t.mk_bitvec(1.into(), 8);
    let containing = app(&mut t, "bvor", good, one, 8);
    let containing = eq(&mut t, containing, x);
    for (value, actual, sort) in [
        ((-1).into(), 8, Sort::bitvec(8)),
        (num_bigint::BigInt::from(1u8) << 4096u32, 8, Sort::bitvec(8)),
        (0.into(), 7, Sort::bitvec(8)),
        (0.into(), 8, Sort::bitvec(7)),
    ] {
        let mut entries = t.entries_snapshot();
        entries[one.index()] = (
            TermData::Const(Constant::BitVec {
                value,
                width: actual,
            }),
            sort,
        );
        let forged = TermStore::from_entries(
            entries,
            Some(t.true_term()),
            Some(t.false_term()),
            t.var_counter(),
        );
        assert!(!accepts(&forged, containing));
    }
    let bad = t.mk_app(Symbol::named("bvor"), [good], Sort::bitvec(8));
    let bad = eq(&mut t, bad, x);
    assert!(!accepts(&t, bad));
    let wrong = t.mk_app(Symbol::named("bvor"), [good, x, x], Sort::bitvec(8));
    let wrong = eq(&mut t, wrong, x);
    assert!(!accepts(&t, wrong));
    let private = t.mk_app(Symbol::indexed("bvor", vec![]), [good, x], Sort::bitvec(8));
    let bad = eq(&mut t, private, x);
    assert!(!accepts(&t, bad));
    let bad = t.mk_app(Symbol::named("="), [good, x], Sort::bitvec(8));
    assert!(!accepts(&t, bad));
    let invalid = t.mk_app(
        Symbol::named("bvor"),
        [good, TermId(u32::MAX)],
        Sort::bitvec(8),
    );
    let invalid = eq(&mut t, invalid, x);
    assert!(!accepts(&t, invalid));
    let narrow = t.mk_var("n", Sort::bitvec(7));
    let bad = app(&mut t, "bvor", good, narrow, 8);
    let bad = eq(&mut t, bad, x);
    assert!(!accepts(&t, bad));
    for width in [0, 129] {
        let w = t.mk_var("w", Sort::bitvec(width));
        let bad = eq(&mut t, w, w);
        assert!(!accepts(&t, bad));
    }
    for clause in [vec![], vec![source, source], vec![TermId(u32::MAX)]] {
        assert!(validate(&t, ProofId(0), &clause, 0, 0, &mut |_, _| true).is_err());
    }
    // A narrow intermediate shift must not claim bits discarded before extension.
    let lo = piece(&mut t, x, 4, 0, 4);
    let amount = t.mk_bitvec(1.into(), 4);
    let shifted = app(&mut t, "bvshl", lo, amount, 4);
    let extended = indexed(&mut t, "zero_extend", vec![4], shifted, 8);
    let bad = eq(&mut t, extended, x);
    assert!(!accepts(&t, bad));
}

#[test]
fn bv_reconstruct_identical_deep_word_body_is_opaque_and_symmetry_is_ordinary() {
    let mut t = TermStore::new();
    let mut word = t.mk_var("x", Sort::bitvec(8));
    for _ in 0..4096 {
        word = app(&mut t, "bvadd", word, word, 8);
    }
    let full = piece(&mut t, word, 8, 0, 8);
    let source = eq(&mut t, full, word);
    assert!(accepts(&t, source));
    let reverse = eq(&mut t, word, full);
    assert!(!accepts(&t, reverse));
    let denied = t.mk_not_raw(reverse);
    let mut p = Proof::new();
    let a = p.add_assume(denied, None);
    let unit = p.add_rule_step(AletheRule::BvReconstructV1, vec![source], vec![], vec![]);
    let symm = p.add_rule_step(AletheRule::Symm, vec![reverse], vec![unit], vec![]);
    p.add_resolution(vec![], reverse, a, symm);
    // The intrinsic is constant in the opaque body's size. The ordinary
    // framework still charges its existing traversal, which refuses this DAG.
    assert!(matches!(
        crate::check_proof_strict_with_context(&p, &t, None, None, Some(&[denied])),
        Err(ProofCheckError::ResourceLimit)
    ));
    let mut t = TermStore::new();
    let word = t.mk_var("x", Sort::bitvec(8));
    let full = piece(&mut t, word, 8, 0, 8);
    let source = eq(&mut t, full, word);
    let reversed = eq(&mut t, word, full);
    let denied = t.mk_not_raw(reversed);
    let mut p = Proof::new();
    let a = p.add_assume(denied, None);
    let u = p.add_rule_step(AletheRule::BvReconstructV1, vec![source], vec![], vec![]);
    let u = p.add_rule_step(AletheRule::Symm, vec![reversed], vec![u], vec![]);
    p.add_resolution(vec![], reversed, a, u);
    crate::check_proof_strict_with_context(&p, &t, None, None, Some(&[denied])).unwrap();
    artifact(
        "ordinary-symmetry",
        &problem(&t, denied, 8),
        &export(&t, &p, &[denied]),
    );
}
